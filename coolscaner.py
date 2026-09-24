"""Simple USB barcode check-in/check-out system.

Most USB barcode scanners work as a keyboard: they type the barcode and press
Enter. Keep the cursor in the scan box and the item will be selected.

Data is stored locally in a SQLite database (see DATABASE_FILE) and, if
configured, mirrored to a Google Sheet in the background: an "Item Info" tab
(current status), a "History" tab (every check-in/out), a "Bookings" tab
(read-only calendar view), and a "Booking Requests" tab (where staff can type
in new bookings for the app to pick up). See the Google Sheets sync section
below for how the two-way sync is kept safe from race conditions.

Run with --database PATH (or -d PATH) to point the app at a specific database
file instead of the default — handy for testing against a throwaway copy
without touching the live database. See parse_arguments()/DATABASE_FILE below.
"""

import argparse
from datetime import datetime, timedelta
import calendar
import hashlib
from pathlib import Path
import secrets
import shutil
import subprocess
import sys
import threading
import time
import sqlite3
from concurrent.futures import ThreadPoolExecutor
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk

from PIL import Image, ImageTk


if getattr(sys, "frozen", False):
	DATA_DIRECTORY = Path.home() / "Library" / "Application Support" / "EquipmentCheckIn"
	DATA_DIRECTORY.mkdir(parents=True, exist_ok=True)
	_executable_path = Path(sys.executable).resolve()
	_resource_directory = _executable_path.parent.parent / "Resources"
	_pyinstaller_directory = Path(getattr(sys, "_MEIPASS", _resource_directory))
	_credential_candidates = [
		_resource_directory / "google-service-account.json",
		_pyinstaller_directory / "google-service-account.json",
		_executable_path.parent / "google-service-account.json",
		_executable_path.parents[3] / "google-service-account.json",
		DATA_DIRECTORY / "google-service-account.json",
	]
	GOOGLE_CREDENTIALS_FILE = str(next(
		(path for path in _credential_candidates if path.exists()),
		DATA_DIRECTORY / "google-service-account.json",
	))
	_bundled_database_candidates = [
		_resource_directory / "check_in_system.db",
		_pyinstaller_directory / "check_in_system.db",
	]
else:
	DATA_DIRECTORY = Path(__file__).resolve().parent
	GOOGLE_CREDENTIALS_FILE = str(DATA_DIRECTORY / "google-service-account.json")
	_bundled_database_candidates = []

DATABASE_FILE = str(DATA_DIRECTORY / "check_in_system.db")
_DATABASE_SEED_MARKER = DATA_DIRECTORY / ".initial_database_seeded"
if getattr(sys, "frozen", False) and not _DATABASE_SEED_MARKER.exists():
	# Seed a first-run (or earlier empty) packaged installation without
	# overwriting a populated user database on later launches.
	for _bundled_database in _bundled_database_candidates:
		if not _bundled_database.exists():
			continue
		try:
			with sqlite3.connect(DATABASE_FILE) as _database:
				_local_item_count = _database.execute("SELECT COUNT(*) FROM items").fetchone()[0]
		except sqlite3.Error:
			_local_item_count = 0
		if _local_item_count == 0:
			shutil.copy2(_bundled_database, DATABASE_FILE)
		break
	_DATABASE_SEED_MARKER.touch()
BACKUP_DIRECTORY = DATA_DIRECTORY / "database_backups"
MAX_DATABASE_BACKUPS = 10
GOOGLE_SHEETS_ENABLED = True
GOOGLE_SPREADSHEET_ID = "1I5FNNSTbMZuqaNQ66FqcEEUXheIsCdTqWFfs5J_9GDM"
GOOGLE_WORKSHEET_NAME = "Item Info"
GOOGLE_HISTORY_WORKSHEET_NAME = "History"
GOOGLE_BOOKINGS_WORKSHEET_NAME = "Bookings"
GOOGLE_BOOKING_REQUESTS_WORKSHEET_NAME = "Make Bookings"
GOOGLE_SYNC_INTERVAL_MS = 10_000
# How long a barcode is protected from sheet-driven changes after a local
# check-in/out, covering one export cycle plus network latency.
LOCAL_CHANGE_GRACE_SECONDS = (GOOGLE_SYNC_INTERVAL_MS / 1000) * 2
BOOKING_REQUEST_DELETE_GRACE_SECONDS = 5 * 60
# USB scanners in keyboard mode normally send a barcode much faster than a
# person can type.  These values let us distinguish a scanner burst from
# ordinary typing in another field.
SCAN_BURST_GAP_SECONDS = 0.15
SCAN_MAX_AVERAGE_KEY_INTERVAL_SECONDS = 0.05
SCAN_MIN_CHARACTERS = 3


class CheckInSystem:
	"""The whole app: one Tk window wired to a local SQLite database and an
	optional background Google Sheets sync (see the sync_to_google_sheets and
	_import_sheet_* methods for how that two-way sync works).
	"""

	def __init__(self, root: tk.Tk) -> None:
		self.root = root
		self.root.title(f"Equipment Check-In System — {Path(DATABASE_FILE).name}")
		self.root.geometry("900x560")
		self.root.minsize(720, 450)

		self.create_database_backup()
		self.database = sqlite3.connect(DATABASE_FILE, check_same_thread=False)
		self.database.row_factory = sqlite3.Row
		self.create_database()
		# The connection is shared with the background Google Sync thread; serialize access.
		self.db_lock = threading.Lock()

		self.admin_mode = False
		self.selected_barcode: str | None = None
		self.photo_image = None
		self.scan_value = tk.StringVar()
		self.global_scan_buffer = ""
		self.last_scan_key_time = 0.0
		self.scan_burst_started_at = 0.0
		self.scan_capture_widget = None
		self.scan_capture_text = None
		self.item_name = tk.StringVar(value="Scan an item to begin")
		self.item_status = tk.StringVar(value="Ready for scan")
		self.item_category = tk.StringVar(value="")
		self.borrower_name = tk.StringVar()
		self.search_value = tk.StringVar()
		self.multi_scan_enabled = tk.BooleanVar(value=False)
		self.multi_scan_queue: list[str] = []
		self.audit_mode = tk.BooleanVar(value=False)
		self.audit_items_scanned: list[str] = []
		self.audit_total_expected: int = 0
		self.audit_categories: set[str] | None = None
		self.audit_category_label = tk.StringVar(value="All categories")
		self.google_worksheets = {}
		self.last_export_values = None
		self.last_history_export_values = None
		self.last_bookings_export_values = None
		self.google_executor = ThreadPoolExecutor(max_workers=1)
		self.google_sync_running = False
		self.google_import_running = False
		self.booking_requests_setup_done = False
		self.last_booking_item_options = None
		# Barcode -> monotonic time of the last local status change, so the sheet
		# import can't undo a check-in/out with a stale snapshot it read moments before.
		self.recently_changed_barcodes: dict[str, float] = {}
		self.audit_progress = tk.DoubleVar(value=0.0)
		self.audit_status_label = tk.StringVar(value="Progress: 0 / 0")
		self.build_interface()
		self.refresh_items()
		self.update_admin_controls()
		self.root.protocol("WM_DELETE_WINDOW", self.close)
		self.root.after(1_000, self.poll_google_sheet)
		self.root.after(1_500, self.sync_to_google_sheets)
		# Allow scanner bursts to be recognized from any field.  Entry widgets get
		# a first-in-line binding so their existing text can be restored after a
		# confirmed scan instead of retaining the barcode characters.
		self.scan_capture_bindtag = "EquipmentCheckInScanCapture"
		self.root.bind_class(self.scan_capture_bindtag, "<KeyPress>", self._capture_entry_before_keypress)
		self.root.bind_all("<FocusIn>", self._install_scan_capture_binding, add="+")
		self._install_scan_capture_binding()
		self.root.bind_all("<Key>", self._on_global_key_press, add="+")
		self.root.bind_all("<Return>", self._on_global_return_press, add="+")

	def create_database_backup(self) -> None:
		"""Copy the current database to database_backups/ and prune old copies, run once at startup."""
		database_path = Path(DATABASE_FILE)
		if not database_path.exists():
			return

		BACKUP_DIRECTORY.mkdir(exist_ok=True)
		timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
		backup_path = BACKUP_DIRECTORY / f"check_in_system_{timestamp}.db"
		shutil.copy2(database_path, backup_path)

		backups = sorted(
			BACKUP_DIRECTORY.glob("check_in_system_*.db"),
			key=lambda path: path.stat().st_mtime,
			reverse=True,
		)
		for old_backup in backups[MAX_DATABASE_BACKUPS:]:
			old_backup.unlink()

	def export_database(self) -> None:
		"""Admin only: save a standalone copy of the current database wherever the user picks.

		Use this to move a snapshot to another computer for testing — that copy is
		independent, so anything done to it there (including deleting items) can
		never touch the live database this app is actually running against.
		"""
		if not self.admin_mode:
			return
		default_name = f"check_in_system_export_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
		destination = filedialog.asksaveasfilename(
			parent=self.root,
			title="Export database copy",
			defaultextension=".db",
			initialfile=default_name,
			filetypes=[("SQLite database", "*.db"), ("All files", "*.*")],
		)
		if not destination:
			return
		try:
			with self.db_lock:
				self.database.commit()
				shutil.copy2(DATABASE_FILE, destination)
		except OSError as error:
			messagebox.showerror("Export failed", f"Could not export the database:\n{error}", parent=self.root)
			return
		messagebox.showinfo(
			"Database exported",
			f"A copy of the database was saved to:\n{destination}\n\n"
			"This is a standalone snapshot. Point a test copy of the app at this file "
			"(instead of the live one) and nothing you do there — including deleting "
			"items — will affect the main system.",
			parent=self.root,
		)

	def get_google_worksheet(self, worksheet_name: str = GOOGLE_WORKSHEET_NAME):
		"""Return a cached gspread Worksheet handle, opening the spreadsheet/tab on first use."""
		if worksheet_name in self.google_worksheets:
			return self.google_worksheets[worksheet_name]
		from importlib import import_module
		gspread = import_module("gspread")
		client = gspread.service_account(filename=GOOGLE_CREDENTIALS_FILE)
		spreadsheet = client.open_by_key(GOOGLE_SPREADSHEET_ID)
		try:
			worksheet = spreadsheet.worksheet(worksheet_name)
		except gspread.WorksheetNotFound:
			worksheet = spreadsheet.add_worksheet(title=worksheet_name, rows=1000, cols=8)
		self.google_worksheets[worksheet_name] = worksheet
		return worksheet

	def sync_to_google_sheets(self, show_result: bool = True) -> None:
		"""Public entry point: export local data to Sheets on the background executor, skipping if one is already running."""
		if not GOOGLE_SHEETS_ENABLED or not GOOGLE_SPREADSHEET_ID or self.google_sync_running:
			return
		self.google_sync_running = True
		self.google_executor.submit(self._sync_to_google_sheets, show_result)

	def _sync_to_google_sheets(self, show_result: bool = True) -> None:
		"""Runs on the background thread: push items/history/bookings to their sheets, skipping unchanged ones."""
		if not GOOGLE_SHEETS_ENABLED or not GOOGLE_SPREADSHEET_ID:
			if show_result:
				messagebox.showwarning(
					"Google Sheets is not configured",
					"Set GOOGLE_SHEETS_ENABLED to True and add the spreadsheet ID in the app settings.",
					parent=self.root,
				)
			return
		try:
			worksheet = self.get_google_worksheet(GOOGLE_WORKSHEET_NAME)

			rows = self.database.execute(
				"SELECT items.barcode, items.name, items.category, items.unavailable, "
				"items.checked_out_by, items.checked_out_at FROM items "
				"LEFT JOIN categories ON categories.name = items.category COLLATE NOCASE "
				"ORDER BY COALESCE(categories.sort_order, 999999), COALESCE(items.category, '') COLLATE NOCASE, "
				"CASE "
				"WHEN items.unavailable = 1 THEN 2 "
				"WHEN items.checked_out_by IS NOT NULL THEN 1 "
				"ELSE 0 END, items.name COLLATE NOCASE"
			).fetchall()
			values = [["Barcode", "Item", "Category", "Status", "Checked out by", "Checkout time"]]
			for row in rows:
				today_reservation = self.get_reservation(row["barcode"])
				if row["unavailable"]:
					status = "Unavailable"
				elif row["checked_out_by"]:
					status = "Checked out"
				elif today_reservation:
					status = "Reserved"
				else:
					status = "Available"
				values.append([
					row["barcode"], row["name"], row["category"] or "Uncategorized", status,
					row["checked_out_by"] or "", row["checked_out_at"] or "",
				])
			if values != self.last_export_values:
				worksheet.clear()
				worksheet.update(values, "A1")
				from gspread.utils import ValidationConditionType
				worksheet.add_validation(
					"D2:D1000",
					ValidationConditionType.one_of_list,
					["Available", "Unavailable", "Reserved"],
					strict=True,
					showCustomUi=True,
				)
				self.last_export_values = values

			history_worksheet = self.get_google_worksheet(GOOGLE_HISTORY_WORKSHEET_NAME)
			history_rows = self.database.execute(
				"SELECT timestamp, action, barcode, item_name, borrower "
				"FROM checkout_history ORDER BY id DESC"
			).fetchall()
			history_values = [["Time", "Action", "Barcode", "Item", "Borrower"]]
			history_values.extend([
				[row["timestamp"], row["action"], row["barcode"], row["item_name"], row["borrower"] or ""]
				for row in history_rows
			])
			if history_values != self.last_history_export_values:
				history_worksheet.clear()
				history_worksheet.update(history_values, "A1")
				self.last_history_export_values = history_values

			bookings_worksheet = self.get_google_worksheet(GOOGLE_BOOKINGS_WORKSHEET_NAME)
			booking_rows = self.database.execute(
				"SELECT reservations.reserved_date, reservations.barcode, reservations.item_name, "
				"reservations.borrower, reservations.status, items.unavailable, items.checked_out_by "
				"FROM reservations JOIN items ON items.barcode = reservations.barcode "
				"ORDER BY reservations.reserved_date, reservations.item_name"
			).fetchall()
			today = datetime.now().strftime("%Y-%m-%d")
			year, month = datetime.now().year, datetime.now().month
			next_year, next_month = (year + 1, 1) if month == 12 else (year, month + 1)
			month_specs = [(year, month), (next_year, next_month)]
			bookings_by_date = {}
			for booking in booking_rows:
				if booking["status"] == "Pending":
					booking_status = "Pending"
				elif booking["unavailable"]:
					booking_status = "Unavailable"
				elif booking["checked_out_by"]:
					booking_status = "Checked out"
				elif booking["reserved_date"] <= today:
					booking_status = "Reserved"
				else:
					booking_status = "Booked"
				bookings_by_date.setdefault(booking["reserved_date"], []).append(
					f"{booking['item_name']} - {booking['borrower']} ({booking_status})"
				)
			booking_values = []
			calendar_blocks = []
			for block_index, (block_year, block_month) in enumerate(month_specs):
				if block_index:
					booking_values.append([""] * 7)
				start_row = len(booking_values) + 1
				weeks = calendar.monthcalendar(block_year, block_month)
				calendar_blocks.append((start_row, block_year, block_month, weeks))
				booking_values.append([f"Bookings - {calendar.month_name[block_month]} {block_year}"] + [""] * 6)
				booking_values.append(list(calendar.day_name))
				for week in weeks:
					calendar_row = []
					for day in week:
						if not day:
							calendar_row.append("")
							continue
						date_text = f"{block_year:04d}-{block_month:02d}-{day:02d}"
						entries = bookings_by_date.get(date_text, [])
						calendar_row.append(str(day) + ("\n" + "\n".join(entries) if entries else ""))
					booking_values.append(calendar_row)
			if booking_values != self.last_bookings_export_values:
				bookings_worksheet.clear()
				bookings_worksheet.update(booking_values, "A1")
				bookings_worksheet.resize(rows=len(booking_values), cols=7)
				# Collect every cell format into one batch_format call to avoid
				# hitting the Sheets API per-minute write quota.
				cell_formats = []
				for start_row, block_year, block_month, weeks in calendar_blocks:
					cell_formats.append({
						"range": f"A{start_row}:G{start_row}",
						"format": {
							"backgroundColor": {"red": 0.62, "green": 0.77, "blue": 0.99},
							"textFormat": {"bold": True, "fontSize": 14, "foregroundColor": {"red": 0, "green": 0, "blue": 0}},
						},
					})
					cell_formats.append({
						"range": f"A{start_row + 1}:G{start_row + 1}",
						"format": {
							"backgroundColor": {"red": 0.86, "green": 0.91, "blue": 0.98},
							"textFormat": {"bold": True, "foregroundColor": {"red": 0, "green": 0, "blue": 0}},
						},
					})
					body_end = start_row + 1 + len(weeks)
					cell_formats.append({
						"range": f"A{start_row + 2}:G{body_end}",
						"format": {
							"wrapStrategy": "WRAP",
							"verticalAlignment": "TOP",
							"textFormat": {"foregroundColor": {"red": 0, "green": 0, "blue": 0}},
						},
					})
					for row_number, week in enumerate(weeks, start=start_row + 2):
						for column, day in enumerate(week, start=1):
							if day:
								date_text = f"{block_year:04d}-{block_month:02d}-{day:02d}"
								color = {"red": 1, "green": 1, "blue": 1}
								if date_text in bookings_by_date:
									color = {"red": 1, "green": 0.94, "blue": 0.8}
								elif date_text == today:
									color = {"red": 0.62, "green": 0.77, "blue": 0.99}
								cell_formats.append({
									"range": f"{chr(64 + column)}{row_number}",
									"format": {"backgroundColor": color},
								})
				bookings_worksheet.batch_format(cell_formats)
				self.last_bookings_export_values = booking_values
		except (FileNotFoundError, ImportError, OSError) as error:
			self.google_worksheets = {}
			self.last_export_values = None
			self.last_history_export_values = None
			self.last_bookings_export_values = None
			if show_result:
				self.root.after(0, lambda: messagebox.showerror(
					"Google Sheets sync failed", str(error), parent=self.root
				))
			self.google_sync_running = False
			return
		except Exception as error:
			self.google_worksheets = {}
			self.last_export_values = None
			self.last_history_export_values = None
			self.last_bookings_export_values = None
			if show_result:
				self.root.after(0, lambda: messagebox.showerror(
					"Google Sheets sync failed", str(error), parent=self.root
				))
			self.google_sync_running = False
			return
		if show_result:
			self.root.after(0, lambda: messagebox.showinfo(
				"Google Sheets", "Inventory synced successfully.", parent=self.root
			))
		self.google_sync_running = False

	def import_sheet_checkouts(self, show_result: bool = True, require_admin: bool = True) -> None:
		"""Public entry point: pull check-in/out edits made directly in the Item Info sheet, in the background."""
		if require_admin and not self.admin_mode:
			return
		if self.google_import_running:
			return
		self.google_import_running = True
		self.google_executor.submit(self._run_with_import_lock, self._import_sheet_checkouts, show_result)

	def _run_with_import_lock(self, func, *args, **kwargs) -> None:
		"""Run func on the executor thread and always clear the import-running flag afterward, even on error."""
		try:
			func(*args, **kwargs)
		finally:
			self.google_import_running = False

	def _import_sheet_checkouts(self, show_result: bool = True) -> None:
		"""Runs on the background thread: apply Checked-out-by/Status edits from the Item Info sheet to the local DB."""
		try:
			worksheet = self.get_google_worksheet()
			rows = worksheet.get_all_records()
			checked_out_count = 0
			checked_in_count = 0
			availability_count = 0
			changed = False
			skipped_items: list[str] = []
			# Hold the lock for the whole loop so a button click can't interleave
			# with these reads/writes on the shared connection.
			with self.db_lock:
				for sheet_row in rows:
					barcode = str(sheet_row.get("Barcode", "")).strip()
					borrower = str(sheet_row.get("Checked out by", "")).strip()
					status = str(sheet_row.get("Status", "")).strip().lower()
					if not barcode:
						continue
					if self.was_recently_changed_locally(barcode):
						# Skip: this row may be a stale snapshot read before our own
						# export caught the sheet up with a very recent local change.
						continue
					if borrower:
						accounts = self.find_accounts(borrower)
						if len(accounts) != 1:
							skipped_items.append(f"{barcode} (checkout requires one matching account)")
							continue
						borrower = accounts[0]["full_name"]
					item = self.database.execute(
						"SELECT name, unavailable, checked_out_by FROM items WHERE barcode = ?", (barcode,)
					).fetchone()
					if item is None:
						skipped_items.append(f"{barcode} (not found)")
					elif item["checked_out_by"] is None and borrower and self.database.execute(
						"SELECT 1 FROM reservations WHERE barcode = ? AND reserved_date <= ?",
						(barcode, datetime.now().strftime("%Y-%m-%d")),
					).fetchone():
						skipped_items.append(f"{barcode} (use the Check Out button for its reservation)")
					elif item["checked_out_by"] and not borrower:
						self.database.execute(
							"UPDATE items SET checked_out_by = NULL, checked_out_at = NULL, unavailable = 0 "
							"WHERE barcode = ?",
							(barcode,),
						)
						self.record_history(barcode, item["name"], "Checked in", None)
						checked_in_count += 1
						changed = True
					elif item["unavailable"]:
						if status == "available":
							self.database.execute("UPDATE items SET unavailable = 0 WHERE barcode = ?", (barcode,))
							availability_count += 1
							changed = True
						elif borrower:
							skipped_items.append(f"{barcode} (unavailable)")
					elif status == "unavailable":
						if item["checked_out_by"]:
							skipped_items.append(f"{barcode} (checked out)")
						else:
							self.database.execute("UPDATE items SET unavailable = 1 WHERE barcode = ?", (barcode,))
							availability_count += 1
							changed = True
					elif item["checked_out_by"] and not self.names_match(item["checked_out_by"], borrower):
						skipped_items.append(f"{barcode} (already checked out)")
					elif borrower and not item["checked_out_by"]:
						timestamp = datetime.now().strftime("%Y-%m-%d %H:%M")
						self.database.execute(
							"UPDATE items SET checked_out_by = ?, checked_out_at = ? WHERE barcode = ?",
							(borrower, timestamp, barcode),
						)
						self.record_history(barcode, item["name"], "Checked out", borrower)
						checked_out_count += 1
						changed = True
				if changed:
					self.database.commit()
			if changed:
				self.root.after(0, self.refresh_items)
				self._sync_to_google_sheets(show_result=False)
		except Exception as error:
			self.google_worksheets = {}
			if show_result:
				self.root.after(0, lambda: messagebox.showerror(
					"Sheet import failed", str(error), parent=self.root
				))
			return
		message = (
			f"Checked out {checked_out_count} item(s), checked in {checked_in_count} item(s), "
			f"and changed availability for {availability_count} item(s)."
		)
		if skipped_items:
			message += "\nSkipped: " + ", ".join(skipped_items)
		if show_result:
			self.root.after(0, lambda: messagebox.showinfo(
				"Sheet checkouts", message, parent=self.root
			))

	def poll_google_sheet(self) -> None:
		"""Timer loop: every GOOGLE_SYNC_INTERVAL_MS, run one import cycle in the background, then reschedule."""
		if GOOGLE_SHEETS_ENABLED and GOOGLE_SPREADSHEET_ID and not self.google_import_running:
			self.google_import_running = True
			self.google_executor.submit(self._run_with_import_lock, self._run_google_import_cycle)
		self.root.after(GOOGLE_SYNC_INTERVAL_MS, self.poll_google_sheet)

	def _run_google_import_cycle(self) -> None:
		"""One full background sync pass: pull booking requests, then pull checkout/status edits."""
		# Bookings then checkouts, sharing one lock so neither call skips the other.
		self._import_sheet_bookings(show_result=False)
		self._import_sheet_checkouts(show_result=False)

	def import_sheet_bookings(self, show_result: bool = True) -> None:
		"""Public entry point: pull new rows from the Booking Requests sheet, in the background."""
		if self.google_import_running:
			return
		self.google_import_running = True
		self.google_executor.submit(self._run_with_import_lock, self._import_sheet_bookings, show_result)

	def submit_booking_requests(self, requests: list[list[str]], parent: tk.Misc | None = None) -> bool:
		"""Send app-created bookings to Make Bookings for admin approval."""
		if not GOOGLE_SHEETS_ENABLED or not GOOGLE_SPREADSHEET_ID:
			messagebox.showerror(
				"Google Sheets is not configured",
				"The booking request could not be sent to Make Bookings.",
				parent=parent or self.root,
			)
			return False
		self.google_executor.submit(self._submit_booking_requests, requests)
		return True

	def _submit_booking_requests(self, requests: list[list[str]]) -> None:
		"""Append only new pending booking requests to Make Bookings."""
		try:
			worksheet = self.get_google_worksheet(GOOGLE_BOOKING_REQUESTS_WORKSHEET_NAME)
			headers = ["Date", "Barcode", "Reserved for", "Confirm", "Status"]
			values = worksheet.get_all_values()
			if not values or not any(values[0]):
				worksheet.update([headers], "A1")
				values = [headers]

			existing_requests = {
				(tuple(str(cell).strip().casefold() for cell in row[:3]))
				for row in values[1:]
				if len(row) >= 3 and any(cell.strip() for cell in row)
			}
			new_requests = []
			for request in requests:
				request_key = tuple(str(cell).strip().casefold() for cell in request[:3])
				if request_key not in existing_requests:
					new_requests.append(request)
					existing_requests.add(request_key)
			if new_requests:
				data_rows = [
					index + 1
					for index, row in enumerate(values[1:], start=1)
					if any(cell.strip() for cell in row[:3])
					or (len(row) > 4 and row[4].strip())
				]
				next_row = max(data_rows, default=1) + 1
				last_row = next_row + len(new_requests) - 1
				worksheet.update(
					new_requests,
					f"A{next_row}:E{last_row}",
					value_input_option="USER_ENTERED",
				)
			self.root.after(0, lambda: messagebox.showinfo(
				"Booking pending",
				f"{len(new_requests)} booking request(s) were sent to Make Bookings for approval.",
				parent=self.root,
			))
		except Exception as error:
			self.google_worksheets = {}
			self.root.after(0, lambda: messagebox.showerror(
				"Booking request failed", str(error), parent=self.root
			))

	def delete_booking_requests(self, requests: list[tuple[str, str, str]]) -> None:
		"""Remove deleted pending requests from Make Bookings in the background."""
		if requests:
			self.google_executor.submit(self._delete_booking_requests, requests)

	def _delete_booking_requests(self, requests: list[tuple[str, str, str]]) -> None:
		try:
			worksheet = self.get_google_worksheet(GOOGLE_BOOKING_REQUESTS_WORKSHEET_NAME)
			request_keys = {
				tuple(value.strip().casefold() for value in request)
				for request in requests
			}
			rows = worksheet.get_all_values()
			rows_to_delete = []
			for row_number, row in enumerate(rows[1:], start=2):
				row_key = tuple(str(cell).strip().casefold() for cell in row[:3])
				if row_key in request_keys:
					rows_to_delete.append(row_number)
			for row_number in reversed(rows_to_delete):
				worksheet.delete_rows(row_number)
		except Exception as error:
			self.google_worksheets = {}
			self.root.after(0, lambda: messagebox.showerror(
				"Booking request deletion failed", str(error), parent=self.root
			))

	def _import_sheet_bookings(self, show_result: bool = True) -> None:
		"""Runs on the background thread: turn confirmed Booking Requests rows into reservations."""
		try:
			worksheet = self.get_google_worksheet(GOOGLE_BOOKING_REQUESTS_WORKSHEET_NAME)
			headers = ["Date", "Barcode", "Reserved for", "Confirm", "Status"]
			values = worksheet.get_all_values()
			if not values or not any(values[0]):
				worksheet.update([headers], "A1")
			item_options = [
				row["name"] for row in self.database.execute("SELECT name FROM items ORDER BY name").fetchall()
			]
			# Only rewrite validation/formatting when it actually needs to change, since
			# each call is a Sheets API write and this runs every poll cycle otherwise.
			if not self.booking_requests_setup_done or item_options != self.last_booking_item_options:
				from gspread.utils import ValidationConditionType
				worksheet.add_validation(
					"A2:A1000", ValidationConditionType.date_is_valid, [],
					strict=False, showCustomUi=True,
				)
				worksheet.format("A2:A1000", {"numberFormat": {"type": "DATE", "pattern": "yyyy-mm-dd"}})
				if item_options:
					worksheet.add_validation(
						"B2:B1000", ValidationConditionType.one_of_list, item_options,
						strict=False, showCustomUi=True,
					)
				worksheet.add_validation(
					"D2:D1000", ValidationConditionType.boolean, ["TRUE", "FALSE"],
					strict=True, showCustomUi=True,
				)
				self.booking_requests_setup_done = True
				self.last_booking_item_options = item_options
			rows = worksheet.get_all_records()
			output_rows = []
			changed = False
			created_request = False
			# Hold the lock for the whole loop so a button click can't interleave
			# with these reads/writes on the shared connection.
			with self.db_lock:
				for row in rows:
					booking_date = str(row.get("Date", "")).strip()
					barcode = str(row.get("Barcode", "")).strip()
					borrower = str(row.get("Reserved for", "")).strip()
					confirm_value = str(row.get("Confirm", "")).strip()
					confirmed = confirm_value.lower() in {"true", "yes", "1", "x"}
					status = str(row.get("Status", "")).strip()
					if not booking_date and not barcode and not borrower:
						continue
					if not booking_date or not barcode or not borrower:
						status = "Missing Date, Barcode, or Reserved for"
					else:
						accounts = self.find_accounts(borrower)
						if len(accounts) == 0:
							status = "Account not found"
						elif len(accounts) > 1:
							status = "Multiple accounts match"
						else:
							borrower = accounts[0]["full_name"]
						if status == "":
							if not confirmed:
								status = "Pending"
							else:
								try:
									booking_date = datetime.strptime(booking_date, "%Y-%m-%d").strftime("%Y-%m-%d")
								except ValueError:
									status = "Use YYYY-MM-DD"
								else:
									item = self.database.execute(
										"SELECT barcode, name, unavailable, checked_out_by FROM items WHERE barcode = ?", (barcode,)
									).fetchone()
									if item is None:
										item = self.database.execute(
											"SELECT barcode, name, unavailable, checked_out_by FROM items WHERE name = ?", (barcode,)
										).fetchone()
									if item is None:
										status = "Barcode not found"
									elif item["unavailable"]:
										status = "Item unavailable"
									else:
										reservation = self.database.execute(
											"SELECT id, status, borrower FROM reservations "
											"WHERE barcode = ? AND reserved_date = ?",
											(item["barcode"], booking_date),
										).fetchone()
										if reservation is not None:
											if reservation["status"] == "Pending" and self.names_match(reservation["borrower"], borrower):
												self.database.execute(
													"UPDATE reservations SET status = 'Confirmed', borrower = ? WHERE id = ?",
													(borrower, reservation["id"]),
												)
												status = "Created"
												changed = True
												created_request = True
												continue
											status = "Already booked"
										else:
											self.database.execute(
												"INSERT INTO reservations "
												"(barcode, item_name, reserved_date, borrower, created_at, status) "
												"VALUES (?, ?, ?, ?, ?, 'Confirmed')",
												(item["barcode"], item["name"], booking_date, borrower, datetime.now().strftime("%Y-%m-%d %H:%M:%S")),
											)
											status = "Created"
											changed = True
											created_request = True
											continue
						output_rows.append([booking_date, barcode, borrower, confirmed, status])
				if changed:
					self.database.commit()
			if created_request:
				worksheet.batch_clear(["A2:E2000"])
				if output_rows:
					worksheet.update(output_rows, "A2", value_input_option="USER_ENTERED")
			elif output_rows:
				existing_rows = [
					[row[index] if index < len(row) else "" for index in range(5)]
					for row in values[1:]
					if any(cell.strip() for cell in row)
				]
				normalize_row = lambda row: [str(cell).strip().casefold() for cell in row]
				if list(map(normalize_row, output_rows)) != list(map(normalize_row, existing_rows)):
					worksheet.update(output_rows, "A2")
			if changed:
				self.root.after(0, self.refresh_items)
				self.sync_to_google_sheets(show_result=False)
		except Exception as error:
			self.google_worksheets = {}
			if show_result:
				self.root.after(0, lambda: messagebox.showerror(
					"Booking import failed", str(error), parent=self.root
				))

	def create_database(self) -> None:
		"""Create tables on first run and add any columns missing from an older database file."""
		self.database.execute(
			"""CREATE TABLE IF NOT EXISTS items (
				barcode TEXT PRIMARY KEY,
				name TEXT NOT NULL,
				category TEXT,
				checked_out_by TEXT,
				checked_out_at TEXT,
				photo_path TEXT
			)"""
		)
		self.database.execute(
			"CREATE TABLE IF NOT EXISTS categories (name TEXT PRIMARY KEY COLLATE NOCASE, sort_order INTEGER NOT NULL DEFAULT 0)"
		)
		self.database.execute("CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT NOT NULL)")
		self.database.execute(
			"""CREATE TABLE IF NOT EXISTS accounts (
				id INTEGER PRIMARY KEY AUTOINCREMENT,
				full_name TEXT NOT NULL,
				student_id TEXT NOT NULL UNIQUE,
				email TEXT NOT NULL,
				phone TEXT NOT NULL,
				created_at TEXT NOT NULL
			)"""
		)
		self.database.execute(
			"""CREATE TABLE IF NOT EXISTS checkout_history (
				id INTEGER PRIMARY KEY AUTOINCREMENT,
				barcode TEXT NOT NULL,
				item_name TEXT NOT NULL,
				action TEXT NOT NULL,
				borrower TEXT,
				timestamp TEXT NOT NULL
			)"""
		)
		self.database.execute(
			"""CREATE TABLE IF NOT EXISTS reservations (
				id INTEGER PRIMARY KEY AUTOINCREMENT,
				barcode TEXT NOT NULL,
				item_name TEXT NOT NULL,
				reserved_date TEXT NOT NULL,
				borrower TEXT NOT NULL,
				created_at TEXT NOT NULL,
				status TEXT NOT NULL DEFAULT 'Confirmed',
				UNIQUE(barcode, reserved_date)
			)"""
		)
		reservation_columns = {column[1] for column in self.database.execute("PRAGMA table_info(reservations)")}
		if "status" not in reservation_columns:
			self.database.execute(
				"ALTER TABLE reservations ADD COLUMN status TEXT NOT NULL DEFAULT 'Confirmed'"
			)
		columns = {column[1] for column in self.database.execute("PRAGMA table_info(items)")}
		if "photo_path" not in columns:
			self.database.execute("ALTER TABLE items ADD COLUMN photo_path TEXT")
		if "unavailable" not in columns:
			self.database.execute("ALTER TABLE items ADD COLUMN unavailable INTEGER NOT NULL DEFAULT 0")
		if "category" not in columns:
			self.database.execute("ALTER TABLE items ADD COLUMN category TEXT")
		category_columns = {column[1] for column in self.database.execute("PRAGMA table_info(categories)")}
		if "sort_order" not in category_columns:
			self.database.execute("ALTER TABLE categories ADD COLUMN sort_order INTEGER NOT NULL DEFAULT 0")
			# Backfill existing categories (from before priorities existed) alphabetically.
			for index, row in enumerate(
				self.database.execute("SELECT name FROM categories ORDER BY name COLLATE NOCASE").fetchall()
			):
				self.database.execute("UPDATE categories SET sort_order = ? WHERE name = ?", (index, row["name"]))
		self.database.commit()

	def get_categories(self) -> list[str]:
		"""Return the admin-defined categories in priority order (alphabetical as a tiebreaker)."""
		return [
			row["name"]
			for row in self.database.execute(
				"SELECT name FROM categories ORDER BY sort_order, name COLLATE NOCASE"
			).fetchall()
		]

	def add_category_dialog(self, parent: tk.Misc | None = None) -> str | None:
		"""Ask an admin for a category name and save it, after existing categories, for use by all items."""
		if not self.admin_mode:
			return None
		category = simpledialog.askstring("Add category", "Category name:", parent=parent or self.root)
		if category is None:
			return None
		category = category.strip()
		if not category:
			messagebox.showwarning("Category name required", "Enter a category name.", parent=parent or self.root)
			return None
		next_sort_order = self.database.execute(
			"SELECT COALESCE(MAX(sort_order), -1) + 1 AS n FROM categories"
		).fetchone()["n"]
		try:
			self.database.execute(
				"INSERT INTO categories (name, sort_order) VALUES (?, ?)", (category, next_sort_order)
			)
			self.database.commit()
		except sqlite3.IntegrityError:
			messagebox.showwarning("Category already exists", f"{category} is already a category.", parent=parent or self.root)
			return None
		return category

	def move_category(self, name: str, direction: int) -> bool:
		"""Admin only: swap a category's sort priority with its neighbor (direction: -1 = up, +1 = down)."""
		if not self.admin_mode:
			return False
		categories = self.database.execute(
			"SELECT name, sort_order FROM categories ORDER BY sort_order, name COLLATE NOCASE"
		).fetchall()
		names = [row["name"] for row in categories]
		if name not in names:
			return False
		index = names.index(name)
		neighbor_index = index + direction
		if neighbor_index < 0 or neighbor_index >= len(names):
			return False
		current_order = categories[index]["sort_order"]
		neighbor_order = categories[neighbor_index]["sort_order"]
		self.database.execute("UPDATE categories SET sort_order = ? WHERE name = ?", (neighbor_order, name))
		self.database.execute(
			"UPDATE categories SET sort_order = ? WHERE name = ?", (current_order, names[neighbor_index])
		)
		self.database.commit()
		return True

	def category_choices(self) -> list[str]:
		"""Return the dropdown choices, including a clear uncategorized option."""
		return ["Uncategorized", *self.get_categories()]

	def rename_category(self, old_name: str, new_name: str, parent: tk.Misc | None = None) -> bool:
		"""Admin only: rename a category and update every item that uses it. Returns True on success."""
		if not self.admin_mode:
			return False
		try:
			self.database.execute("UPDATE categories SET name = ? WHERE name = ?", (new_name, old_name))
		except sqlite3.IntegrityError:
			messagebox.showwarning(
				"Category already exists", f"{new_name} is already a category.", parent=parent or self.root
			)
			return False
		self.database.execute("UPDATE items SET category = ? WHERE category = ?", (new_name, old_name))
		self.database.commit()
		return True

	def delete_category(self, name: str) -> None:
		"""Admin only: remove a category, leaving any items that used it Uncategorized."""
		if not self.admin_mode:
			return
		self.database.execute("UPDATE items SET category = NULL WHERE category = ?", (name,))
		self.database.execute("DELETE FROM categories WHERE name = ?", (name,))
		self.database.commit()

	def manage_categories_dialog(self) -> None:
		"""Admin only: add, rename, or delete categories, keeping items in sync."""
		if not self.admin_mode:
			return
		dialog = tk.Toplevel(self.root)
		dialog.title("Manage categories")
		dialog.resizable(False, False)
		dialog.transient(self.root)
		dialog.grab_set()
		frame = ttk.Frame(dialog, padding=18)
		frame.grid()

		listbox = tk.Listbox(frame, height=10, width=32, exportselection=False)
		listbox.grid(row=0, column=0, rowspan=7, sticky="ns")
		scrollbar = ttk.Scrollbar(frame, orient="vertical", command=listbox.yview)
		scrollbar.grid(row=0, column=1, rowspan=7, sticky="ns")
		listbox.configure(yscrollcommand=scrollbar.set)

		def reload_list(select_name: str | None = None) -> None:
			listbox.delete(0, tk.END)
			for name in self.get_categories():
				listbox.insert(tk.END, name)
			if select_name and select_name in listbox.get(0, tk.END):
				listbox.selection_set(list(listbox.get(0, tk.END)).index(select_name))

		def selected_category() -> str | None:
			selection = listbox.curselection()
			return listbox.get(selection[0]) if selection else None

		def after_change() -> None:
			self.refresh_items()
			if self.selected_barcode:
				row = self.database.execute(
					"SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)
				).fetchone()
				if row:
					self.show_item(row)
			self.sync_to_google_sheets(show_result=False)

		def add() -> None:
			new_category = self.add_category_dialog(dialog)
			if new_category:
				reload_list(new_category)
				after_change()

		def rename() -> None:
			current = selected_category()
			if not current:
				messagebox.showinfo("Select a category", "Choose a category to rename.", parent=dialog)
				return
			new_name = simpledialog.askstring(
				"Rename category", "New name:", initialvalue=current, parent=dialog
			)
			if new_name is None:
				return
			new_name = new_name.strip()
			if not new_name or new_name == current:
				return
			if self.rename_category(current, new_name, parent=dialog):
				reload_list(new_name)
				after_change()

		def delete() -> None:
			current = selected_category()
			if not current:
				messagebox.showinfo("Select a category", "Choose a category to delete.", parent=dialog)
				return
			count = self.database.execute(
				"SELECT COUNT(*) AS n FROM items WHERE category = ?", (current,)
			).fetchone()["n"]
			message = f"Delete category '{current}'?"
			if count:
				message += f"\n{count} item(s) using it will become Uncategorized."
			if not messagebox.askyesno("Delete category", message, parent=dialog):
				return
			self.delete_category(current)
			reload_list()
			after_change()

		def move_up() -> None:
			current = selected_category()
			if not current:
				messagebox.showinfo("Select a category", "Choose a category to move.", parent=dialog)
				return
			if self.move_category(current, -1):
				reload_list(current)
				after_change()

		def move_down() -> None:
			current = selected_category()
			if not current:
				messagebox.showinfo("Select a category", "Choose a category to move.", parent=dialog)
				return
			if self.move_category(current, 1):
				reload_list(current)
				after_change()

		ttk.Label(frame, text="Priority controls the order categories\nappear in and items are sorted by.", foreground="#555555").grid(
			row=0, column=2, padx=(8, 0), sticky="w"
		)
		ttk.Button(frame, text="Move Up", command=move_up).grid(row=1, column=2, padx=(8, 0), sticky="ew")
		ttk.Button(frame, text="Move Down", command=move_down).grid(row=2, column=2, padx=(8, 0), sticky="ew")
		ttk.Button(frame, text="Add", command=add).grid(row=3, column=2, padx=(8, 0), sticky="ew")
		ttk.Button(frame, text="Rename", command=rename).grid(row=4, column=2, padx=(8, 0), sticky="ew")
		ttk.Button(frame, text="Delete", command=delete).grid(row=5, column=2, padx=(8, 0), sticky="ew")
		ttk.Button(frame, text="Close", command=dialog.destroy).grid(row=6, column=2, padx=(8, 0), sticky="ew")

		reload_list()

	def get_reservation(self, barcode: str, reserved_date: str | None = None):
		"""Return a confirmed reservation for a barcode and date (today by default), or None."""
		reserved_date = reserved_date or datetime.now().strftime("%Y-%m-%d")
		return self.database.execute(
			"SELECT * FROM reservations WHERE barcode = ? AND reserved_date = ? AND status = 'Confirmed'",
			(barcode, reserved_date),
		).fetchone()

	def booking_request_is_recent(self, created_at: str) -> bool:
		"""Return whether a pending booking can still be deleted without admin access."""
		for format_text in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M"):
			try:
				created_time = datetime.strptime(created_at, format_text)
				return (datetime.now() - created_time).total_seconds() <= BOOKING_REQUEST_DELETE_GRACE_SECONDS
			except ValueError:
				continue
		return False

	def names_match(self, first_name: str, second_name: str) -> bool:
		"""Compare borrower names ignoring case/whitespace, so sheet edits don't need exact capitalization."""
		return first_name.strip().casefold() == second_name.strip().casefold()

	def mark_recently_changed(self, barcode: str) -> None:
		"""Record that a barcode changed locally just now, see was_recently_changed_locally."""
		self.recently_changed_barcodes[barcode] = time.monotonic()

	def was_recently_changed_locally(self, barcode: str) -> bool:
		"""True if a barcode was changed locally within the last grace window.

		Used by the sheet import to skip a barcode it just read: that row can be a
		stale snapshot fetched before our own export caught the sheet up with a
		check-in/out that just happened, and blindly applying it would otherwise
		flip the item straight back to its old state.
		"""
		changed_at = self.recently_changed_barcodes.get(barcode)
		return changed_at is not None and (time.monotonic() - changed_at) < LOCAL_CHANGE_GRACE_SECONDS

	def record_history(self, barcode: str, item_name: str, action: str, borrower: str | None) -> None:
		"""Append one row to the local checkout_history table (also mirrored to the History sheet)."""
		self.database.execute(
			"INSERT INTO checkout_history (barcode, item_name, action, borrower, timestamp) VALUES (?, ?, ?, ?, ?)",
			(barcode, item_name, action, borrower, datetime.now().strftime("%Y-%m-%d %H:%M")),
		)

	def hash_password(self, password: str, salt: str | None = None) -> str:
		"""Return 'salt$hash' using PBKDF2-SHA256; a fresh random salt is generated if one isn't given."""
		salt = salt or secrets.token_hex(16)
		password_hash = hashlib.pbkdf2_hmac("sha256", password.encode(), salt.encode(), 200_000).hex()
		return f"{salt}${password_hash}"

	def password_matches(self, password: str, stored_password: str) -> bool:
		"""Check a typed password against a stored 'salt$hash' string using a constant-time comparison."""
		try:
			salt, expected_hash = stored_password.split("$", 1)
		except ValueError:
			return False
		actual_hash = self.hash_password(password, salt).split("$", 1)[1]
		return secrets.compare_digest(actual_hash, expected_hash)
	def update_audit_controls(self) -> None:
		"""Refresh everything that depends on audit_mode."""
		if self.audit_mode.get():
			self.audit_button.configure(text="End Audit")
			self.audit_frame.grid()
		else:
			self.audit_button.configure(text="Start Audit")
			self.audit_frame.grid_remove()
	def update_admin_controls(self) -> None:
		"""Refresh everything that depends on admin_mode: background color, and which buttons are shown/enabled."""
		self.apply_admin_background(self.admin_mode)
		self.admin_status.set("Admin mode" if self.admin_mode else "Normal mode")
		self.admin_button.configure(text="Leave Admin Mode" if self.admin_mode else "Enter Admin Mode")

		# Admin-only controls are hidden entirely in normal mode, not just disabled.
		admin_only_buttons = (
			self.add_button, self.edit_button, self.photo_button,
			self.unavailable_button, self.delete_button, self.history_button,
			self.category_button, self.export_button, self.manage_accounts_button,
		)
		for button in admin_only_buttons:
			if self.admin_mode:
				button.grid()
			else:
				button.grid_remove()

		if self.admin_mode:
			self.add_button.state(["!disabled"])
			self.edit_button.state(["!disabled"] if self.selected_barcode else ["disabled"])
			self.photo_button.state(["!disabled"] if self.selected_barcode else ["disabled"])
			self.unavailable_button.state(["!disabled"] if self.selected_barcode else ["disabled"])
			self.delete_button.state(["!disabled"] if self.selected_barcode else ["disabled"])
			self.history_button.state(["!disabled"])
			self.category_button.state(["!disabled"])
			self.export_button.state(["!disabled"])
			self.manage_accounts_button.state(["!disabled"])
		self.checkout_button.configure(state="normal" if self.selected_barcode else "disabled")
		self.checkin_button.configure(state="normal" if self.selected_barcode else "disabled")
		self.book_button.state(["!disabled"] if self.selected_barcode else ["disabled"])
		if self.selected_barcode:
			row = self.database.execute(
				"SELECT unavailable FROM items WHERE barcode = ?", (self.selected_barcode,)
			).fetchone()
			self.unavailable_button.configure(text="Mark Available" if row and row["unavailable"] else "Mark Unavailable")
	def choose_audit_categories(self) -> tuple[bool, set[str] | None]:
		"""Ask which item categories should be included, or return None for all."""
		category_names = ["Uncategorized", *self.get_categories()]
		dialog = tk.Toplevel(self.root)
		dialog.title("Choose audit categories")
		dialog.resizable(False, False)
		dialog.transient(self.root)
		dialog.grab_set()
		frame = ttk.Frame(dialog, padding=16)
		frame.grid()
		tk.Label(frame, text="Choose the categories to include in this audit:").grid(
			row=0, column=0, sticky="w", pady=(0, 8)
		)
		all_categories = tk.BooleanVar(value=True)
		category_values = {name: tk.BooleanVar(value=True) for name in category_names}
		ttk.Checkbutton(
			frame, text="All categories", variable=all_categories,
		).grid(row=1, column=0, sticky="w")

		category_frame = ttk.Frame(frame)
		category_frame.grid(row=2, column=0, sticky="w", padx=(20, 0), pady=(4, 0))
		for row_number, name in enumerate(category_names):
			ttk.Checkbutton(
				category_frame, text=name, variable=category_values[name],
			).grid(row=row_number, column=0, sticky="w")

		def sync_all_categories() -> None:
			state = "disabled" if all_categories.get() else "normal"
			for child in category_frame.winfo_children():
				child.configure(state=state)

		all_categories.trace_add("write", lambda *_args: sync_all_categories())
		sync_all_categories()
		result: list[tuple[bool, set[str] | None]] = [(False, None)]

		def start_audit() -> None:
			if all_categories.get():
				result[0] = (True, None)
			else:
				selected = {
					name.casefold() for name, value in category_values.items() if value.get()
				}
				if not selected:
					messagebox.showwarning(
						"Choose a category", "Select at least one category or choose All categories.", parent=dialog
					)
					return
				result[0] = (True, selected)
			dialog.destroy()

		ttk.Button(frame, text="Start Audit", command=start_audit).grid(
			row=3, column=0, sticky="e", pady=(12, 0)
		)
		dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
		dialog.wait_window()
		return result[0]

	def audit_item_is_in_scope(self, row: sqlite3.Row) -> bool:
		"""Return whether an item belongs to the categories selected for this audit."""
		if self.audit_categories is None:
			return True
		category = (row["category"] or "Uncategorized").casefold()
		return category in self.audit_categories

	def toggle_audit_mode(self) -> None:
		"""Toggle audit mode on or off."""
		if not self.audit_mode.get():
			accepted, selected_categories = self.choose_audit_categories()
			# A cancelled category dialog leaves audit mode off.
			if not accepted:
				self.audit_categories = None
				return
			self.audit_categories = selected_categories
			self.audit_mode.set(True)
			self.update_audit_controls()
			# Prepare for audit
			self.audit_items_scanned = []
			self.audit_progress.set(0.0)
			rows = self.database.execute("SELECT category FROM items").fetchall()
			self.audit_total_expected = sum(1 for row in rows if self.audit_item_is_in_scope(row))
			if self.audit_categories is None:
				self.audit_category_label.set("All categories")
			else:
				category_labels = {
					"Uncategorized": "Uncategorized",
					**{name.casefold(): name for name in self.get_categories()},
				}
				self.audit_category_label.set(", ".join(
					category_labels.get(category, category) for category in sorted(self.audit_categories)
				))
			self.audit_status_label.configure(text=f"Progress: 0 / {self.audit_total_expected}")
		else:
			self.audit_mode.set(False)
			self.update_audit_controls()
			# Reset audit data when leaving audit mode
			self.audit_items_scanned = []
			self.audit_total_expected = 0
			self.audit_categories = None
			self.audit_category_label.set("All categories")
			self.audit_progress.set(0.0)
			self.audit_status_label.configure(text="Progress: 0 / 0")

	def show_audit_report(self) -> None:
		"""Display a summary of the audit results."""
		scanned_count = len(self.audit_items_scanned)
		total_expected = self.audit_total_expected
		
		message = (
			f"Audit Complete!\n\n"
			f"Items Scanned: {scanned_count}\n"
			f"Total Expected: {total_expected}\n\n"
		)
		
		if total_expected > 0:
			if scanned_count == total_expected:
				message += "✅ All items accounted for!"
			else:
				# Find missing items
				missing_items = []
				cursor = self.database.execute("SELECT barcode, name, category, checked_out_by FROM items")
				for row in cursor:
					if not self.audit_item_is_in_scope(row):
						continue
					if row["barcode"] not in self.audit_items_scanned:
						status = "Checked Out" if row["checked_out_by"] else "Available"
						borrower = f" ({row['checked_out_by']})" if row["checked_out_by"] else ""
						missing_items.append(f"- {row['name']} ({row['barcode']}){borrower} [{status}]")
				
				if len(missing_items) > 0:
					message += f"⚠️ Missing {len(missing_items)} items:\n\n"
					message += "\n".join(missing_items[:20])
					if len(missing_items) > 20:
						message += f"\n... and {len(missing_items) - 20} more."
				
				if scanned_count > total_expected:
					message += f"\n\n❓ Note: You also scanned {scanned_count - total_expected} extra items."
		else:
			message += "No items were found in the database to audit."

		messagebox.showinfo("Audit Report", message)
		
		# Automatically end audit mode
		self.toggle_audit_mode()

	def toggle_admin_mode(self) -> None:
		"""Leave admin mode instantly; entering it requires the stored password (or creating one on first use)."""
		if self.admin_mode:
			self.admin_mode = False
			self.update_admin_controls()
			self.refresh_items()
			return

		stored_password = self.database.execute(
			"SELECT value FROM settings WHERE key = 'admin_password'"
		).fetchone()
		if stored_password is None:
			password = simpledialog.askstring("Set admin password", "Create an admin password:", show="*", parent=self.root)
			if not password:
				return
			confirmation = simpledialog.askstring("Set admin password", "Enter the password again:", show="*", parent=self.root)
			if password != confirmation:
				messagebox.showwarning("Passwords do not match", "The admin password was not saved.", parent=self.root)
				return
			self.database.execute(
				"INSERT INTO settings (key, value) VALUES ('admin_password', ?)",
				(self.hash_password(password),),
			)
			self.database.commit()
		else:
			password = simpledialog.askstring("Admin access", "Enter the admin password:", show="*", parent=self.root)
			if password is None or not self.password_matches(password, stored_password["value"]):
				messagebox.showwarning("Access denied", "That admin password is incorrect.", parent=self.root)
				return

		self.admin_mode = True
		self.update_admin_controls()
		self.refresh_items()

	def apply_admin_background(self, admin: bool) -> None:
		"""Tint the whole window gold in admin mode, or restore the theme's normal background."""
		background = "gold" if admin else self.default_bg
		self.root.configure(bg=background)
		style = ttk.Style(self.root)
		for style_name in ("TFrame", "TLabelframe", "TLabelframe.Label", "TLabel"):
			style.configure(style_name, background=background)

	def show_history(self) -> None:
		"""Open a read-only window listing every checkout_history row, newest first (admin only)."""
		if not self.admin_mode:
			return
		dialog = tk.Toplevel(self.root)
		dialog.title("Checkout History")
		dialog.geometry("760x420")
		dialog.transient(self.root)
		frame = ttk.Frame(dialog, padding=12)
		frame.pack(fill="both", expand=True)
		columns = ("time", "action", "barcode", "item", "borrower")
		table = ttk.Treeview(frame, columns=columns, show="headings")
		headings = {
			"time": "Time", "action": "Action", "barcode": "Barcode",
			"item": "Item", "borrower": "Borrower",
		}
		widths = {"time": 140, "action": 110, "barcode": 140, "item": 190, "borrower": 140}
		for column in columns:
			table.heading(column, text=headings[column])
			table.column(column, width=widths[column], anchor="w")
		rows = self.database.execute(
			"SELECT timestamp, action, barcode, item_name, borrower "
			"FROM checkout_history ORDER BY id DESC"
		).fetchall()
		for row in rows:
			table.insert("", "end", values=(
				row["timestamp"], row["action"], row["barcode"],
				row["item_name"], row["borrower"] or "",
			))
		table.pack(side="left", fill="both", expand=True)
		scrollbar = ttk.Scrollbar(frame, orient="vertical", command=table.yview)
		scrollbar.pack(side="right", fill="y")
		table.configure(yscrollcommand=scrollbar.set)

	def find_accounts(self, name_query: str) -> list[sqlite3.Row]:
		"""Find accounts by student ID, full name, first name, or last name."""
		query = name_query.strip().casefold()
		if not query:
			return []
		matches = []
		for account in self.database.execute(
			"SELECT * FROM accounts ORDER BY full_name COLLATE NOCASE"
		).fetchall():
			name_parts = account["full_name"].split()
			if (
				account["student_id"].casefold() == query
				or
				account["full_name"].casefold() == query
				or (name_parts and name_parts[0].casefold() == query)
				or (name_parts and name_parts[-1].casefold() == query)
			):
				matches.append(account)
		return matches

	def choose_account_dialog(self, accounts: list[sqlite3.Row], parent: tk.Misc) -> sqlite3.Row | None:
		"""Let the borrower choose one account when a name matches multiple people."""
		if len(accounts) == 1:
			return accounts[0]
		dialog = tk.Toplevel(parent)
		dialog.title("Choose account")
		dialog.resizable(False, True)
		dialog.transient(parent)
		dialog.grab_set()
		frame = ttk.Frame(dialog, padding=14)
		frame.grid(sticky="nsew")
		ttk.Label(frame, text="Multiple accounts match that name. Choose the borrower:").grid(
			row=0, column=0, columnspan=2, sticky="w", pady=(0, 8)
		)
		table = ttk.Treeview(frame, columns=("name", "student_id", "email", "phone"), show="headings", height=6)
		for column, heading, width in (
			("name", "Name", 180), ("student_id", "Student ID", 110),
			("email", "Email", 190), ("phone", "Phone", 120),
		):
			table.heading(column, text=heading)
			table.column(column, width=width, anchor="w")
		for account in accounts:
			table.insert("", "end", iid=str(account["id"]), values=(
				account["full_name"], account["student_id"], account["email"], account["phone"],
			))
		table.grid(row=1, column=0, columnspan=2, sticky="nsew")
		result: list[sqlite3.Row | None] = [None]

		def choose() -> None:
			selection = table.selection()
			if not selection:
				messagebox.showwarning("Choose an account", "Select the borrower account first.", parent=dialog)
				return
			result[0] = next(account for account in accounts if str(account["id"]) == selection[0])
			dialog.destroy()

		ttk.Button(frame, text="Use selected account", command=choose).grid(row=2, column=1, sticky="e", pady=(8, 0))
		dialog.bind("<Return>", lambda _event: choose())
		dialog.wait_window()
		return result[0]

	def resolve_borrower_account(self, parent: tk.Misc) -> sqlite3.Row | None:
		"""Resolve the typed borrower to a registered account before checkout."""
		name_query = self.borrower_name.get().strip()
		if not name_query:
			messagebox.showwarning("Name required", "Enter the borrower's first, last, or full name.", parent=parent)
			self.borrower_entry.focus_set()
			return None
		accounts = self.find_accounts(name_query)
		if not accounts:
			messagebox.showwarning(
				"Account required",
				"No account matches that name. Use Sign Up before checking out equipment.",
				parent=parent,
			)
			return None
		account = self.choose_account_dialog(accounts, parent)
		if account:
			self.borrower_name.set(account["full_name"])
		return account

	def signup_dialog(self) -> None:
		"""Create a borrower account available to every checkout station."""
		dialog = tk.Toplevel(self.root)
		dialog.title("Create account")
		dialog.resizable(False, False)
		dialog.transient(self.root)
		dialog.grab_set()
		fields = [("Full name", tk.StringVar()), ("Student ID", tk.StringVar()), ("Email", tk.StringVar()), ("Phone", tk.StringVar())]
		frame = ttk.Frame(dialog, padding=18)
		frame.grid()
		entries = []
		for row_number, (label, value) in enumerate(fields):
			ttk.Label(frame, text=f"{label}:").grid(row=row_number, column=0, sticky="w", padx=(0, 10), pady=4)
			entry = ttk.Entry(frame, textvariable=value, width=34)
			entry.grid(row=row_number, column=1, pady=4)
			entries.append(entry)

		def save() -> None:
			values = [value.get().strip() for _, value in fields]
			if not all(values):
				messagebox.showwarning("Missing information", "Enter a name, student ID, email, and phone number.", parent=dialog)
				return
			try:
				self.database.execute(
					"INSERT INTO accounts (full_name, student_id, email, phone, created_at) VALUES (?, ?, ?, ?, ?)",
					(*values, datetime.now().strftime("%Y-%m-%d %H:%M:%S")),
				)
				self.database.commit()
			except sqlite3.IntegrityError:
				messagebox.showwarning("Student ID already registered", "That student ID already has an account.", parent=dialog)
				return
			dialog.destroy()
			messagebox.showinfo("Account created", f"Account created for {values[0]}.", parent=self.root)

		ttk.Button(frame, text="Create account", command=save).grid(row=len(fields), column=1, sticky="e", pady=(12, 0))
		entries[0].focus_set()

	def manage_accounts_dialog(self) -> None:
		"""Admin-only account list with edit and delete controls."""
		if not self.admin_mode:
			return
		dialog = tk.Toplevel(self.root)
		dialog.title("Manage accounts")
		dialog.geometry("760x380")
		dialog.transient(self.root)
		frame = ttk.Frame(dialog, padding=12)
		frame.pack(fill="both", expand=True)
		columns = ("name", "student_id", "email", "phone")
		table = ttk.Treeview(frame, columns=columns, show="headings", selectmode="browse")
		for column, heading, width in (
			("name", "Name", 180), ("student_id", "Student ID", 120),
			("email", "Email", 220), ("phone", "Phone", 130),
		):
			table.heading(column, text=heading)
			table.column(column, width=width, anchor="w")
		table.pack(fill="both", expand=True)

		def reload_accounts() -> None:
			for row_id in table.get_children():
				table.delete(row_id)
			for account in self.database.execute("SELECT * FROM accounts ORDER BY full_name COLLATE NOCASE").fetchall():
				table.insert("", "end", iid=str(account["id"]), values=(
					account["full_name"], account["student_id"], account["email"], account["phone"],
				))

		def selected_account() -> sqlite3.Row | None:
			selection = table.selection()
			if not selection:
				return None
			return self.database.execute("SELECT * FROM accounts WHERE id = ?", (selection[0],)).fetchone()

		def edit_account() -> None:
			account = selected_account()
			if account is None:
				messagebox.showinfo("Select an account", "Choose an account to edit.", parent=dialog)
				return
			edit_dialog = tk.Toplevel(dialog)
			edit_dialog.title("Edit account")
			edit_dialog.transient(dialog)
			edit_dialog.grab_set()
			fields = [
				("Full name", tk.StringVar(value=account["full_name"])),
				("Student ID", tk.StringVar(value=account["student_id"])),
				("Email", tk.StringVar(value=account["email"])),
				("Phone", tk.StringVar(value=account["phone"])),
			]
			edit_frame = ttk.Frame(edit_dialog, padding=16)
			edit_frame.grid()
			entries = []
			for row_number, (label, value) in enumerate(fields):
				ttk.Label(edit_frame, text=f"{label}:").grid(row=row_number, column=0, sticky="w", padx=(0, 10), pady=4)
				entry = ttk.Entry(edit_frame, textvariable=value, width=34)
				entry.grid(row=row_number, column=1, pady=4)
				entries.append(entry)

			def save_changes() -> None:
				values = [value.get().strip() for _, value in fields]
				if not all(values):
					messagebox.showwarning("Missing information", "All account fields are required.", parent=edit_dialog)
					return
				try:
					self.database.execute(
						"UPDATE accounts SET full_name = ?, student_id = ?, email = ?, phone = ? WHERE id = ?",
						(*values, account["id"]),
					)
					self.database.commit()
				except sqlite3.IntegrityError:
					messagebox.showwarning("Student ID already registered", "That student ID already has an account.", parent=edit_dialog)
					return
				edit_dialog.destroy()
				reload_accounts()

			ttk.Button(edit_frame, text="Save changes", command=save_changes).grid(
				row=len(fields), column=1, sticky="e", pady=(12, 0)
			)
			entries[0].focus_set()

		def delete_account() -> None:
			account = selected_account()
			if account is None:
				messagebox.showinfo("Select an account", "Choose an account to delete.", parent=dialog)
				return
			if not messagebox.askyesno(
				"Delete account",
				f"Delete the account for {account['full_name']}? Existing checkout history will be preserved.",
				parent=dialog,
			):
				return
			self.database.execute("DELETE FROM accounts WHERE id = ?", (account["id"],))
			self.database.commit()
			reload_accounts()

		buttons = ttk.Frame(frame)
		buttons.pack(fill="x", pady=(8, 0))
		ttk.Button(buttons, text="Edit", command=edit_account).pack(side="left")
		ttk.Button(buttons, text="Delete", command=delete_account).pack(side="left", padx=(8, 0))
		ttk.Button(buttons, text="Close", command=dialog.destroy).pack(side="right")
		reload_accounts()

	def build_interface(self) -> None:
		"""Build every widget in the main window: header/admin controls, scan box, multi-scan queue, item details, and the item list."""
		style = ttk.Style(self.root)
		self.default_bg = style.lookup("TFrame", "background") or self.root.cget("bg")
		self.root.columnconfigure(0, weight=1)
		self.root.rowconfigure(2, weight=1)

		header = ttk.Frame(self.root, padding=(20, 18, 20, 8))
		header.grid(row=0, column=0, sticky="ew")
		header.columnconfigure(0, weight=1)
		ttk.Label(header, text="Equipment Check-In System", font=("Segoe UI", 18, "bold")).grid(
			row=0, column=0, sticky="w"
		)
		ttk.Label(header, text="Scan a barcode, then check the item out or back in.").grid(
			row=1, column=0, sticky="w", pady=(4, 0)
		)
		self.admin_status = tk.StringVar(value="Normal mode")
		ttk.Label(header, textvariable=self.admin_status).grid(row=0, column=1, padx=(12, 8))
		self.admin_button = ttk.Button(header, text="Enter Admin Mode", command=self.toggle_admin_mode)
		self.admin_button.grid(row=0, column=2, rowspan=2)
		self.audit_button = ttk.Button(header, text="Inventory Audit", command=self.toggle_audit_mode)
		self.audit_button.grid(row=0, column=3, rowspan=2, padx=(8, 0))
		self.history_button = ttk.Button(
			header, text="Checkout History", command=self.show_history, state="disabled"
		)
		self.history_button.grid(row=0, column=4, rowspan=2, padx=(8, 0))
		self.export_button = ttk.Button(
			header, text="Export Database", command=self.export_database, state="disabled"
		)
		self.export_button.grid(row=0, column=5, rowspan=2, padx=(8, 0))
		self.signup_button = ttk.Button(header, text="Sign Up", command=self.signup_dialog)
		self.signup_button.grid(row=0, column=6, rowspan=2, padx=(8, 0))
		self.manage_accounts_button = ttk.Button(
			header, text="Manage Accounts", command=self.manage_accounts_dialog, state="disabled"
		)
		self.manage_accounts_button.grid(row=0, column=7, rowspan=2, padx=(8, 0))

		scan_frame = ttk.LabelFrame(self.root, text="Scan item", padding=14)
		scan_frame.grid(row=1, column=0, padx=20, pady=8, sticky="ew")
		scan_frame.columnconfigure(0, weight=1)
		self.scan_entry = ttk.Entry(scan_frame, textvariable=self.scan_value, font=("Segoe UI", 14))
		self.scan_entry.grid(row=0, column=0, sticky="ew", padx=(0, 8))
		self.scan_entry.bind("<Return>", self.scan_item)
		ttk.Button(scan_frame, text="Scan / Find", command=self.scan_item).grid(row=0, column=1)
		ttk.Checkbutton(
			scan_frame, text="Multi-scan mode (scan several items, then check them out together)",
			variable=self.multi_scan_enabled, command=self.toggle_multi_scan_mode,
		).grid(row=1, column=0, columnspan=2, sticky="w", pady=(8, 0))

		self.multi_scan_frame = ttk.Frame(scan_frame)
		self.multi_scan_frame.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(8, 0))
		self.multi_scan_frame.columnconfigure(0, weight=1)
		self.multi_scan_table = ttk.Treeview(
			self.multi_scan_frame, columns=("barcode", "name", "status"),
			show="headings", height=5, selectmode="browse",
		)
		for column, heading, width in (
			("barcode", "Barcode", 150), ("name", "Item", 220), ("status", "Status", 110),
		):
			self.multi_scan_table.heading(column, text=heading)
			self.multi_scan_table.column(column, width=width, anchor="w")
		self.multi_scan_table.grid(row=0, column=0, sticky="nsew")
		multi_scan_scrollbar = ttk.Scrollbar(
			self.multi_scan_frame, orient="vertical", command=self.multi_scan_table.yview
		)
		multi_scan_scrollbar.grid(row=0, column=1, sticky="ns")
		self.multi_scan_table.configure(yscrollcommand=multi_scan_scrollbar.set)
		multi_scan_buttons = ttk.Frame(self.multi_scan_frame)
		multi_scan_buttons.grid(row=1, column=0, columnspan=2, sticky="w", pady=(6, 0))
		self.multi_scan_checkout_button = tk.Button(
			multi_scan_buttons, text="Check Out All", command=self.checkout_multi_scan_queue,
			bg="#f4b4b4", fg="#8b0000", activebackground="#e98f8f",
		)
		self.multi_scan_checkout_button.grid(row=0, column=0)
		self.multi_scan_checkin_button = tk.Button(
			multi_scan_buttons, text="Check In All", command=self.checkin_multi_scan_queue,
			bg="#c4f0c4", fg="#006400", activebackground="#a0e0a0",
		)
		self.multi_scan_checkin_button.grid(row=0, column=1, padx=(8, 0))
		ttk.Button(
			multi_scan_buttons, text="Book All", command=self.book_multi_scan_queue,
		).grid(row=0, column=2, padx=(8, 0))
		ttk.Button(
			multi_scan_buttons, text="Remove Selected", command=self.remove_from_multi_scan_queue,
		).grid(row=0, column=3, padx=(8, 0))
		ttk.Button(
			multi_scan_buttons, text="Clear Queue", command=self.clear_multi_scan_queue,
		).grid(row=0, column=4, padx=(8, 0))
		self.multi_scan_frame.grid_remove()

		# Audit Mode Frame
		self.audit_frame = ttk.LabelFrame(self.root, text="Inventory Audit", padding=14)
		self.audit_frame.grid(row=4, column=0, padx=20, pady=8, sticky="ew")
		self.audit_frame.columnconfigure(0, weight=1)
		
		self.audit_progress = tk.DoubleVar(value=0.0)
		self.audit_progress_bar = ttk.Progressbar(self.audit_frame, variable=self.audit_progress, maximum=100)
		self.audit_progress_bar.grid(row=0, column=0, sticky="ew", padx=(0, 8))
		
		self.audit_status_label = ttk.Label(self.audit_frame, text="Progress: 0 / 0")
		self.audit_status_label.grid(row=0, column=1, sticky="w")
		ttk.Label(self.audit_frame, text="Categories:").grid(row=1, column=0, sticky="w", pady=(8, 0))
		ttk.Label(self.audit_frame, textvariable=self.audit_category_label).grid(
			row=1, column=1, sticky="w", pady=(8, 0)
		)

		ttk.Button(self.audit_frame, text="Show Report & End", command=self.show_audit_report).grid(row=2, column=0, columnspan=2, sticky="ew", pady=(8, 0))
		self.audit_frame.grid_remove()

		details = ttk.LabelFrame(self.root, text="Selected item", padding=14)
		details.grid(row=2, column=0, padx=20, pady=8, sticky="new")
		details.columnconfigure(1, weight=1)
		details.columnconfigure(2, minsize=180)
		ttk.Label(details, text="Item:").grid(row=0, column=0, sticky="w", padx=(0, 10))
		ttk.Label(details, textvariable=self.item_name, font=("Segoe UI", 11, "bold")).grid(
			row=0, column=1, sticky="w"
		)
		ttk.Label(details, text="Status:").grid(row=1, column=0, sticky="w", padx=(0, 10), pady=(8, 0))
		ttk.Label(details, textvariable=self.item_status).grid(row=1, column=1, sticky="w", pady=(8, 0))
		ttk.Label(details, text="Category:").grid(row=2, column=0, sticky="w", padx=(0, 10), pady=(8, 0))
		ttk.Label(details, textvariable=self.item_category).grid(row=2, column=1, sticky="w", pady=(8, 0))
		tk.Label(details, text="Borrower name or student ID:").grid(row=3, column=0, sticky="w", padx=(0, 10), pady=(8, 0))
		tk.Label(details, text="Tip: You Can Scan Student ID").grid(row=4, column=0, sticky="w", padx=(0, 10), pady=(8, 0))
		self.borrower_entry = ttk.Entry(details, textvariable=self.borrower_name)
		self.borrower_entry.grid(row=3, column=1, sticky="ew", pady=(8, 0))
		buttons = ttk.Frame(details)
		buttons.grid(row=4, column=1, sticky="w", pady=(12, 0))
		self.checkout_button = tk.Button(
			buttons, text="Check Out", command=self.check_out,
			bg="#f4b4b4", fg="#8b0000", activebackground="#e98f8f",
		)
		self.checkout_button.grid(row=0, column=0, padx=(0, 8))
		self.checkin_button = tk.Button(
			buttons, text="Check In", command=self.check_in,
			bg="#b8e6b8", fg="#145214", activebackground="#91d391",
		)
		self.checkin_button.grid(row=0, column=1)
		self.book_button = ttk.Button(buttons, text="Request Booking", command=self.book_item, state="disabled")
		self.book_button.grid(row=0, column=2, padx=(8, 0))
		self.unavailable_button = ttk.Button(
			buttons, text="Mark Unavailable", command=self.toggle_unavailable, state="disabled"
		)
		self.unavailable_button.grid(row=0, column=3, padx=(8, 0))
		self.photo_preview = ttk.Label(details, text="No photo", anchor="center")
		self.photo_preview.grid(row=0, column=2, rowspan=5, padx=(24, 0), sticky="nsew")
		self.photo_button = ttk.Button(details, text="Add / Change Photo", command=self.choose_photo, state="disabled")
		self.photo_button.grid(row=5, column=2, padx=(24, 0), pady=(8, 0))

		list_frame = ttk.LabelFrame(self.root, text="All items", padding=10)
		list_frame.grid(row=3, column=0, padx=20, pady=(0, 20), sticky="nsew")
		list_frame.columnconfigure(0, weight=1)
		list_frame.rowconfigure(1, weight=1)
		self.root.rowconfigure(3, weight=1)
		search = ttk.Entry(list_frame, textvariable=self.search_value)
		search.grid(row=0, column=0, sticky="ew", padx=(0, 8), pady=(0, 8))
		search.insert(0, "Search barcode or item name")
		search.bind("<FocusIn>", lambda _: search.delete(0, tk.END) if search.get() == "Search barcode or item name" else None)
		search.bind("<KeyRelease>", lambda _: self.refresh_items())
		self.add_button = ttk.Button(list_frame, text="Add item", command=self.add_item_dialog, state="disabled")
		self.add_button.grid(row=0, column=1, pady=(0, 8))
		self.delete_button = ttk.Button(
			list_frame, text="Delete item", command=self.delete_selected_item, state="disabled"
		)
		self.delete_button.grid(row=0, column=2, padx=(8, 0), pady=(0, 8))
		self.edit_button = ttk.Button(
			list_frame, text="Edit item", command=self.edit_item_dialog, state="disabled"
		)
		self.edit_button.grid(row=0, column=3, padx=(8, 0), pady=(0, 8))
		self.category_button = ttk.Button(
			list_frame, text="Manage categories", command=self.manage_categories_dialog, state="disabled"
		)
		self.category_button.grid(row=0, column=4, padx=(8, 0), pady=(0, 8))

		columns = ("barcode", "name", "category", "status", "borrower", "time")
		self.items_table = ttk.Treeview(list_frame, columns=columns, show="headings", selectmode="browse")
		self.items_table.tag_configure("checked_out", background="#ffd9d9", foreground="#9b1c1c")
		self.items_table.tag_configure("available", background="#dff4df", foreground="#176b2c")
		self.items_table.tag_configure("unavailable", background="#e6e6e6", foreground="#555555")
		self.items_table.tag_configure("reserved", background="#fff0cc", foreground="#8a5a00")
		headings = {
			"barcode": "Barcode", "name": "Item", "category": "Category", "status": "Status",
			"borrower": "Borrowed by", "time": "Time",
		}
		widths = {"barcode": 125, "name": 170, "category": 120, "status": 100, "borrower": 135, "time": 125}
		for column in columns:
			self.items_table.heading(column, text=headings[column])
			self.items_table.column(column, width=widths[column], anchor="w")
		self.items_table.grid(row=1, column=0, columnspan=2, sticky="nsew")
		scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=self.items_table.yview)
		scrollbar.grid(row=1, column=2, sticky="ns")
		self.items_table.configure(yscrollcommand=scrollbar.set)
		self.items_table.bind("<<TreeviewSelect>>", self.select_table_item)

	def refresh_items(self) -> None:
		"""Reload the item list, hiding unavailable items outside admin mode.

		Items are grouped by category (in the admin-defined priority order set in
		Manage categories), so a checked-out item stays with its category instead of
		jumping to a separate "checked out" section. Within each category they are
		ordered Available/Reserved first, then Checked out, then Unavailable, then by name.
		"""
		for row_id in self.items_table.get_children():
			self.items_table.delete(row_id)
		search = self.search_value.get().strip()
		if search == "Search barcode or item name":
			search = ""
		where_clause = "WHERE (items.barcode LIKE ? OR items.name LIKE ? OR COALESCE(items.category, '') LIKE ?)"
		if not self.admin_mode:
			where_clause += " AND items.unavailable = 0"
		rows = self.database.execute(
			"SELECT items.* FROM items "
			"LEFT JOIN categories ON categories.name = items.category COLLATE NOCASE "
			+ where_clause + " "
			"ORDER BY COALESCE(categories.sort_order, 999999), COALESCE(items.category, '') COLLATE NOCASE, "
			"CASE "
			"WHEN items.unavailable = 1 THEN 2 "
			"WHEN items.checked_out_by IS NOT NULL THEN 1 "
			"ELSE 0 END, items.name COLLATE NOCASE",
			(f"%{search}%", f"%{search}%", f"%{search}%"),
		).fetchall()
		for row in rows:
			today_reservation = self.get_reservation(row["barcode"])
			if row["unavailable"]:
				status, row_tag = "Unavailable", "unavailable"
			elif row["checked_out_by"]:
				status, row_tag = "Checked out", "checked_out"
			elif today_reservation:
				status, row_tag = "Reserved", "reserved"
			else:
				status, row_tag = "Available", "available"
			self.items_table.insert("", "end", iid=row["barcode"], values=(
				row["barcode"], row["name"], row["category"] or "Uncategorized", status,
				row["checked_out_by"] or "", row["checked_out_at"] or "",
			), tags=(row_tag,))

	def scan_item(self, event_or_barcode: tk.Event | str | None = None, force: bool = False) -> None:
		"""Look up a scanned/typed barcode: add it to the multi-scan queue, or select it for single-item actions."""
		if isinstance(event_or_barcode, tk.Event):
			if hasattr(event_or_barcode.widget, 'get'):
				barcode = event_or_barcode.widget.get().strip()
			else:
				barcode = self.scan_value.get().strip()
		elif isinstance(event_or_barcode, str):
			barcode = event_or_barcode
		else:
			barcode = ""

		if not barcode:
			return

		# Manual Enter presses in the Borrower name or Search fields should keep
		# their ordinary behavior.  A confirmed fast scanner burst passes
		# force=True, so a barcode can still be found from either field.
		focused_widget = self.root.focus_get()
		if not force and isinstance(focused_widget, (tk.Entry, ttk.Entry)) and focused_widget != self.scan_entry:
			return

		row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (barcode,)).fetchone()
		if row is None:
			accounts = self.find_accounts(barcode)
			if len(accounts) == 1:
				self.scan_value.set("")
				self.borrower_name.set(accounts[0]["full_name"])
				self.borrower_entry.focus_set()
				return
			self.clear_selection()
			self.scan_entry.focus_set()
			messagebox.showinfo("Unknown barcode", f"No item is registered for barcode {barcode}.\nUse Add item to register it.")
			return

		# Clear the scan entry box to prepare for the next scan
		self.scan_value.set("")
		self.scan_entry.focus_set()

		if self.audit_mode.get():
			if not self.audit_item_is_in_scope(row):
				self.play_sound("Error")
				return
			if barcode not in self.audit_items_scanned:
				self.audit_items_scanned.append(barcode)
				if self.audit_total_expected > 0:
					progress = (len(self.audit_items_scanned) / self.audit_total_expected) * 100
					self.audit_progress.set(progress)
				self.audit_status_label.config(text=f"Progress: {len(self.audit_items_scanned)} / {self.audit_total_expected}")
				self.play_sound("Tink")
				if row["checked_out_by"]:
					messagebox.showwarning("Item Checked Out", f"Item '{row['name']}' is currently checked out to {row['checked_out_by']}.", parent=self.root)
			else:
				self.play_sound("Error")
			return

		if self.multi_scan_enabled.get():
			self.add_to_multi_scan_queue(row)
			return
		self.show_item(row)

	def _install_scan_capture_binding(self, event: tk.Event | None = None) -> None:
		"""Put the scan snapshot binding ahead of normal text-entry behavior.

		The binding is attached when an Entry gains focus, including entries in
		dialogs that are created after startup.  This lets a confirmed scanner
		burst leave the person's partly typed text exactly as it was.
		"""
		widget = event.widget if event is not None else self.root.focus_get()
		if not isinstance(widget, (tk.Entry, ttk.Entry)):
			return
		tags = widget.bindtags()
		if self.scan_capture_bindtag not in tags:
			widget.bindtags((self.scan_capture_bindtag, *tags))

	def _capture_entry_before_keypress(self, event: tk.Event) -> None:
		"""Snapshot the focused Entry before the first key in a possible scan."""
		char = event.char
		if not char or not char.isprintable():
			return
		now = time.monotonic()
		if now - self.last_scan_key_time > SCAN_BURST_GAP_SECONDS:
			self.scan_capture_widget = event.widget
			self.scan_capture_text = event.widget.get()

	def _clear_scan_capture(self) -> None:
		"""Discard the saved field contents once this input sequence is finished."""
		self.scan_capture_widget = None
		self.scan_capture_text = None

	def _is_fast_scan_burst(self, now: float) -> bool:
		"""Return True only for a recent, scanner-speed sequence of characters."""
		barcode = self.global_scan_buffer.strip()
		if len(barcode) < SCAN_MIN_CHARACTERS:
			return False
		if now - self.last_scan_key_time > SCAN_BURST_GAP_SECONDS:
			return False
		key_intervals = len(self.global_scan_buffer) - 1
		if key_intervals <= 0:
			return False
		average_interval = (self.last_scan_key_time - self.scan_burst_started_at) / key_intervals
		return average_interval <= SCAN_MAX_AVERAGE_KEY_INTERVAL_SECONDS

	def _restore_scan_capture(self) -> None:
		"""Remove a recognized barcode from the field that had focus when it began."""
		widget, text = self.scan_capture_widget, self.scan_capture_text
		if isinstance(widget, (tk.Entry, ttk.Entry)) and text is not None and widget.winfo_exists():
			widget.delete(0, tk.END)
			widget.insert(0, text)
		self._clear_scan_capture()

	def _on_global_key_press(self, event: tk.Event) -> None:
		"""Collect a potential barcode and start a new buffer after a typing pause."""
		char = event.char
		if not char or not char.isprintable():
			return
		now = time.monotonic()
		if now - self.last_scan_key_time > SCAN_BURST_GAP_SECONDS:
			self.global_scan_buffer = char
			self.scan_burst_started_at = now
			if not isinstance(event.widget, (tk.Entry, ttk.Entry)):
				self._clear_scan_capture()
		else:
			self.global_scan_buffer += char
		self.last_scan_key_time = now

	def _on_global_return_press(self, event: tk.Event) -> str | None:
		"""Select a known item when a fast scanner burst ends with Enter.

		A normal Return remains untouched.  This avoids treating a person's quick
		typing as an unknown barcode while still handling keyboard-mode scanners
		from the Borrower name and Search boxes.
		"""
		now = time.monotonic()
		barcode = self.global_scan_buffer.strip()
		fast_scan = self._is_fast_scan_burst(now)
		self.global_scan_buffer = ""
		# A completed sequence must not become the beginning of the next scan.
		self.last_scan_key_time = 0.0
		self.scan_burst_started_at = 0.0

		# The Scan entry's own Return binding has already handled this one.  Just
		# clear the duplicate global buffer so multi-scan mode cannot queue twice.
		if event.widget == self.scan_entry:
			self._clear_scan_capture()
			return None

		if fast_scan and barcode:
			accounts = self.find_accounts(barcode)
			if len(accounts) == 1:
				self._restore_scan_capture()
				self.borrower_name.set(accounts[0]["full_name"])
				return "break"
			item_exists = self.database.execute(
				"SELECT 1 FROM items WHERE barcode = ?", (barcode,)
			).fetchone()
			if item_exists:
				self.scan_item(barcode, force=True)
				self._restore_scan_capture()
				return "break"

		self._clear_scan_capture()
		return None

	def show_item(self, row: sqlite3.Row) -> None:
		"""Update the details panel with the selected item's information."""
		self.selected_barcode = row["barcode"]
		self.item_name.set(row["name"])
		if row["unavailable"]:
			status = "Unavailable"
		elif row["checked_out_by"]:
			status = "Checked out"
		elif self.get_reservation(row["barcode"]):
			status = "Reserved"
		else:
			status = "Available"
		self.item_status.set(status)
		self.item_category.set(row["category"] or "Uncategorized")
		self.borrower_name.set(row["checked_out_by"] or "")
		self.update_photo_preview(row["photo_path"]) if row["photo_path"] else self.photo_preview.configure(image="", text="No photo")
		self.update_admin_controls()

	def toggle_multi_scan_mode(self) -> None:
		"""Show or hide the multi-scan queue panel to match the checkbox."""
		if self.multi_scan_enabled.get():
			self.multi_scan_frame.grid()
		else:
			self.multi_scan_frame.grid_remove()
		self.scan_entry.focus_set()

	def add_to_multi_scan_queue(self, row: sqlite3.Row) -> None:
		"""Queue a scanned item for batch checkout; a duplicate scan just beeps instead of adding twice."""
		barcode = row["barcode"]
		if barcode in self.multi_scan_queue:
			self.root.bell()
			return
		self.multi_scan_queue.append(barcode)
		self.refresh_multi_scan_queue()
		self.play_sound("Tink")

	def refresh_multi_scan_queue(self) -> None:
		"""Redraw the multi-scan queue table from self.multi_scan_queue."""
		for row_id in self.multi_scan_table.get_children():
			self.multi_scan_table.delete(row_id)
		for barcode in self.multi_scan_queue:
			row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (barcode,)).fetchone()
			if row is None:
				continue
			if row["unavailable"]:
				status = "Unavailable"
			elif row["checked_out_by"]:
				status = "Checked out"
			else:
				status = "Available"
			self.multi_scan_table.insert("", "end", iid=barcode, values=(barcode, row["name"], status))

	def remove_from_multi_scan_queue(self) -> None:
		"""Drop the selected queue row(s) without affecting their item's actual status."""
		for barcode in self.multi_scan_table.selection():
			if barcode in self.multi_scan_queue:
				self.multi_scan_queue.remove(barcode)
		self.refresh_multi_scan_queue()

	def clear_multi_scan_queue(self) -> None:
		"""Empty the multi-scan queue."""
		self.multi_scan_queue.clear()
		self.refresh_multi_scan_queue()

	def checkout_multi_scan_queue(self) -> None:
		"""Check out every queued item to one borrower in a single batch, skipping any that aren't available."""
		if not self.multi_scan_queue:
			messagebox.showwarning("Queue is empty", "Scan at least one item before checking out.")
			return
		account = self.resolve_borrower_account(self.root)
		if account is None:
			return
		borrower = account["full_name"]
		timestamp = datetime.now().strftime("%Y-%m-%d %H:%M")
		checked_out: list[str] = []
		skipped: list[str] = []
		with self.db_lock:
			for barcode in list(self.multi_scan_queue):
				try:
					item = self.database.execute(
						"SELECT name, checked_out_by, unavailable FROM items WHERE barcode = ?", (barcode,)
					).fetchone()
					if item is None:
						skipped.append(f"{barcode} (not found)")
						continue
					if item["unavailable"]:
						skipped.append(f"{item['name']} (unavailable)")
						continue
					if item["checked_out_by"]:
						skipped.append(f"{item['name']} (already checked out)")
						continue
					
					self.database.execute(
						"UPDATE items SET checked_out_by = ?, checked_out_at = ? WHERE barcode = ?",
						(borrower, timestamp, barcode),
					)
					self.record_history(barcode, item["name"], "Checked out", borrower)
					self.mark_recently_changed(barcode)
					checked_out.append(item["name"])
				except Exception as e:
					skipped.append(f"Error with {barcode}: {str(e)}")

			self.database.commit()
		self.multi_scan_queue.clear()
		self.refresh_multi_scan_queue()
		self.refresh_items()
		if checked_out:
			self.sync_to_google_sheets(show_result=False)
			self.play_sound("Pop")
		message = f"Checked out {len(checked_out)} item(s) to {borrower}."
		if skipped:
			message += "\nSkipped: " + ", ".join(skipped)
		messagebox.showinfo("Multi-scan checkout", message)

	def checkin_multi_scan_queue(self) -> None:
		"""Check in every queued item in a single batch, skipping any that aren't checked out."""
		if not self.multi_scan_queue:
			messagebox.showwarning("Queue is empty", "Scan at least one item before checking in.")
			return
		checked_in: list[str] = []
		skipped: list[str] = []
		with self.db_lock:
			for barcode in list(self.multi_scan_queue):
				try:
					item = self.database.execute(
						"SELECT name, checked_out_by FROM items WHERE barcode = ?", (barcode,)
					).fetchone()
					if item is None:
						skipped.append(f"{barcode} (not found)")
						continue
					if not item["checked_out_by"]:
						skipped.append(f"{item['name']} (not checked out)")
						continue
					
					update = self.database.execute(
						"UPDATE items SET checked_out_by = NULL, checked_out_at = NULL "
						"WHERE barcode = ? AND checked_out_by IS NOT NULL",
						(barcode,),
					)
					if not update.rowcount:
						skipped.append(f"{item['name']} (check-in failed)")
						continue
					
					self.record_history(barcode, item["name"], "Checked in", None)
					self.mark_recently_changed(barcode)
					self.database.execute(
						"DELETE FROM reservations WHERE barcode = ? AND reserved_date <= ?",
						(barcode, datetime.now().strftime("%Y-%m-%d")),
					)
					checked_in.append(item["name"])
				except Exception as e:
					skipped.append(f"{barcode} (error: {str(e)})")
			self.database.commit()

		message = f"Checked in {len(checked_in)} item(s)."
		if skipped:
			message += "\nSkipped: " + ", ".join(skipped)
		messagebox.showinfo("Multi-scan check-in", message)
		self.clear_multi_scan_queue()
		self.refresh_items()
		if checked_in:
			self.sync_to_google_sheets(show_result=False)
			self.play_sound("Pop")

	def update_photo_preview(self, photo_path: str) -> None:
		"""Update the photo preview with the image at photo_path."""
		try:
			image = Image.open(photo_path)
			image.thumbnail((160*2, 120*2))
			self.photo_image = ImageTk.PhotoImage(image)
			self.photo_preview.configure(image=self.photo_image, text="")
		except (FileNotFoundError, OSError):
			self.photo_preview.configure(image="", text="No photo")

	def choose_photo(self) -> None:
		"""Admin only: pick an image file and attach it to the selected item."""
		if not self.admin_mode or not self.selected_barcode:
			return
		photo_path = filedialog.askopenfilename(
			title="Choose item photo",
			filetypes=[("Image files", "*.png *.jpg *.jpeg *.gif *.bmp"), ("All files", "*.*")],
		)
		if not photo_path:
			return
		self.database.execute("UPDATE items SET photo_path = ? WHERE barcode = ?", (photo_path, self.selected_barcode))
		self.database.commit()
		row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)).fetchone()
		if row:
			self.show_item(row)

	def edit_item_dialog(self) -> None:
		"""Admin only: edit an item's name, category, barcode, or photo."""
		if not self.admin_mode or not self.selected_barcode:
			return
		row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)).fetchone()
		if row is None:
			return

		dialog = tk.Toplevel(self.root)
		dialog.title("Edit item")
		dialog.resizable(False, False)
		dialog.transient(self.root)
		dialog.grab_set()
		barcode = tk.StringVar(value=row["barcode"])
		name = tk.StringVar(value=row["name"])
		category = tk.StringVar(value=row["category"] or "Uncategorized")
		photo_path = tk.StringVar(value=row["photo_path"] or "")
		category_options = self.category_choices()
		if row["category"] and row["category"] not in category_options:
			category_options.append(row["category"])
		frame = ttk.Frame(dialog, padding=18)
		frame.grid()
		ttk.Label(frame, text="Barcode:").grid(row=0, column=0, sticky="w", padx=(0, 8), pady=4)
		ttk.Entry(frame, textvariable=barcode, width=32).grid(row=0, column=1, pady=4)
		ttk.Label(frame, text="Item name:").grid(row=1, column=0, sticky="w", padx=(0, 8), pady=4)
		ttk.Entry(frame, textvariable=name, width=32).grid(row=1, column=1, pady=4)
		ttk.Label(frame, text="Category:").grid(row=2, column=0, sticky="w", padx=(0, 8), pady=4)
		category_menu = ttk.Combobox(
			frame, textvariable=category, values=category_options, state="readonly", width=29
		)
		category_menu.grid(row=2, column=1, pady=4)

		def add_category_from_dialog() -> None:
			new_category = self.add_category_dialog(dialog)
			category_menu.configure(values=self.category_choices())
			if new_category:
				category.set(new_category)

		ttk.Button(frame, text="New category", command=add_category_from_dialog).grid(row=2, column=2, padx=(8, 0))
		tk.Label(frame, text="Photo:").grid(row=3, column=0, sticky="w", padx=(0, 8), pady=4)
		tk.Entry(frame, textvariable=photo_path, width=32, state="readonly").grid(
			row=3, column=1, pady=4
		)

		def choose_existing_photo() -> None:
			selected_path = filedialog.askopenfilename(
				parent=dialog,
				title="Choose item photo",
				filetypes=[("Image files", "*.png *.jpg *.jpeg *.gif *.bmp"), ("All files", "*.*")],
			)
			if selected_path:
				photo_path.set(selected_path)

		ttk.Button(frame, text="Choose photo", command=choose_existing_photo).grid(row=3, column=2, padx=(8, 0))

		def save() -> None:
			barcode_text, name_text = barcode.get().strip(), name.get().strip()
			category_text = category.get().strip()
			category_value = None if category_text == "Uncategorized" else category_text
			if not barcode_text or not name_text:
				messagebox.showwarning("Missing information", "Enter both a barcode and an item name.", parent=dialog)
				return
			try:
				self.database.execute(
					"UPDATE items SET barcode = ?, name = ?, category = ?, photo_path = ? WHERE barcode = ?",
					(barcode_text, name_text, category_value, photo_path.get() or None, self.selected_barcode),
				)
				self.database.commit()
			except sqlite3.IntegrityError:
				messagebox.showwarning("Barcode already exists", "That barcode is already registered.", parent=dialog)
				return
			self.selected_barcode = barcode_text
			dialog.destroy()
			self.refresh_items()
			self.sync_to_google_sheets(show_result=False)
			updated_row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (barcode_text,)).fetchone()
			if updated_row:
				self.show_item(updated_row)

		ttk.Button(frame, text="Save changes", command=save).grid(row=4, column=1, sticky="e", pady=(12, 0))

	def select_table_item(self, _event: tk.Event) -> None:
		"""Show details for whichever row the user clicked in the item list."""
		selected = self.items_table.selection()
		if selected:
			row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (selected[0],)).fetchone()
			if row:
				self.show_item(row)

	def check_out(self) -> None:
		"""Check the selected item out to the typed borrower.

		The read-check-write happens under db_lock and the UPDATE only succeeds if
		the item is still available, so a concurrent background sheet sync can't
		cause this to report success when nothing actually changed.
		"""
		if self.multi_scan_enabled.get():
			self.checkout_multi_scan_queue()
			return

		if not self.selected_barcode:
			messagebox.showwarning("No item selected", "Scan or select an item first.")
			return
		account = self.resolve_borrower_account(self.root)
		if account is None:
			return
		succeeded = False
		borrower = account["full_name"]
		with self.db_lock:
			item = self.database.execute(
				"SELECT name, unavailable FROM items WHERE barcode = ?", (self.selected_barcode,)
			).fetchone()
			if item and item["unavailable"]:
				messagebox.showwarning("Item unavailable", "An admin must mark this item available before checkout.")
				return
			reservation = self.get_reservation(self.selected_barcode)
			if reservation and not self.names_match(reservation["borrower"], self.borrower_name.get()):
				messagebox.showwarning(
					"Item reserved",
					f"This item is reserved today for {reservation['borrower']}.",
				)
				return
			timestamp = datetime.now().strftime("%Y-%m-%d %H:%M")
			update = self.database.execute(
				"UPDATE items SET checked_out_by = ?, checked_out_at = ? WHERE barcode = ? AND checked_out_by IS NULL",
				(borrower, timestamp, self.selected_barcode),
			)
			# Only report success if the row actually changed; a background Google
			# Sheets sync could have checked this item out moments earlier.
			succeeded = bool(item and update.rowcount)
			if succeeded:
				self.record_history(self.selected_barcode, item["name"], "Checked out", borrower)
				self.mark_recently_changed(self.selected_barcode)
			self.database.commit()

		if not succeeded:
			current = self.database.execute(
				"SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)
			).fetchone()
			if current:
				self.show_item(current)
			messagebox.showwarning(
				"Checkout failed",
				"This item was just checked out or changed by someone else. Its current status is now shown.",
			)
			return
		self.finish_action(f"Item checked out to {borrower}.")

	def check_in(self) -> None:
		"""Check the selected item back in, the same race-safe way as check_out."""
		if self.multi_scan_enabled.get():
			self.checkin_multi_scan_queue()
			return

		if not self.selected_barcode:
			messagebox.showwarning("No item selected", "Scan or select an item first.")
			return
		succeeded = False
		with self.db_lock:
			item = self.database.execute(
				"SELECT name, checked_out_by FROM items WHERE barcode = ?", (self.selected_barcode,)
			).fetchone()
			was_checked_out = bool(item and item["checked_out_by"])
			update = self.database.execute(
				"UPDATE items SET checked_out_by = NULL, checked_out_at = NULL "
				"WHERE barcode = ? AND checked_out_by IS NOT NULL",
				(self.selected_barcode,),
			)
			succeeded = bool(was_checked_out and update.rowcount)
			if succeeded:
				self.record_history(self.selected_barcode, item["name"], "Checked in", None)
				self.mark_recently_changed(self.selected_barcode)
				self.database.execute(
					"DELETE FROM reservations WHERE barcode = ? AND reserved_date <= ?",
					(self.selected_barcode, datetime.now().strftime("%Y-%m-%d")),
				)
			self.database.commit()

		if not succeeded:
			current = self.database.execute(
				"SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)
			).fetchone()
			if current:
				self.show_item(current)
			messagebox.showwarning(
				"Check-in failed",
				"This item was already checked in or changed by someone else. Its current status is now shown.",
			)
			return
		self.finish_action("Item checked in and available.")

	def play_sound(self, sound_name: str) -> None:
		"""Play a short confirmation sound; falls back to the plain Tk bell off macOS or if the file is missing."""
		# macOS built-in sound file, falling back to the plain Tk bell elsewhere.
		sound_path = Path("/System/Library/Sounds") / f"{sound_name}.aiff"
		if sys.platform == "darwin" and sound_path.exists():
			try:
				subprocess.Popen(
					["afplay", str(sound_path)],
					stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
				)
				return
			except OSError:
				pass
		self.root.bell()

	def book_item(self) -> None:
		"""Open a calendar dialog to create, edit, or delete a reservation for the selected item."""
		if not self.selected_barcode:
			return
		row = self.database.execute(
			"SELECT name FROM items WHERE barcode = ?", (self.selected_barcode,)
		).fetchone()
		if row is None:
			return
		self.book_items([(self.selected_barcode, row["name"])])

	def book_multi_scan_queue(self) -> None:
		"""Open the same calendar dialog to book every item currently in the multi-scan queue at once."""
		if not self.multi_scan_queue:
			messagebox.showwarning("Queue is empty", "Scan at least one item before booking.")
			return
		items: list[tuple[str, str]] = []
		missing: list[str] = []
		for barcode in self.multi_scan_queue:
			row = self.database.execute("SELECT name FROM items WHERE barcode = ?", (barcode,)).fetchone()
			if row is None:
				missing.append(barcode)
				continue
			items.append((barcode, row["name"]))
		if missing:
			messagebox.showwarning(
				"Some items not found", "Skipping unknown barcode(s): " + ", ".join(missing)
			)
		if items:
			self.book_items(items)

	def book_items(self, items: list[tuple[str, str]]) -> None:
		"""Shared calendar dialog: book one or more items (barcode, name pairs) for one or more days at once."""
		date_dialog = tk.Toplevel(self.root)
		date_dialog.title("Book item" if len(items) == 1 else f"Book {len(items)} items")
		date_dialog.resizable(False, False)
		date_dialog.transient(self.root)
		date_dialog.grab_set()
		frame = ttk.Frame(date_dialog, padding=18)
		frame.grid()
		if len(items) > 1:
			names_preview = ", ".join(name for _, name in items[:5])
			if len(items) > 5:
				names_preview += f", +{len(items) - 5} more"
			ttk.Label(
				frame, text=f"Booking {len(items)} items: {names_preview}", wraplength=320, justify="left"
			).grid(row=6, column=0, columnspan=3, sticky="w", pady=(10, 0))
		today = datetime.now()
		month_year = [today.year, today.month]
		selected_dates: set[str] = {today.strftime("%Y-%m-%d")}
		last_clicked_date = [today.strftime("%Y-%m-%d")]
		borrower = tk.StringVar(value=self.borrower_name.get().strip())
		month_label = tk.StringVar()
		selection_label = tk.StringVar()
		calendar_frame = ttk.Frame(frame)
		calendar_frame.grid(row=1, column=0, columnspan=3, pady=(10, 0))
		barcode_placeholders = ",".join("?" * len(items))
		barcodes = tuple(barcode for barcode, _ in items)

		def existing_bookings_for_selection() -> dict[str, dict[str, sqlite3.Row]]:
			"""date -> {barcode: booking row} for target items already booked that day."""
			if not selected_dates:
				return {}
			date_placeholders = ",".join("?" * len(selected_dates))
			result: dict[str, dict[str, sqlite3.Row]] = {}
			for booking in self.database.execute(
				f"SELECT id, barcode, reserved_date, borrower, status, created_at FROM reservations "
				f"WHERE barcode IN ({barcode_placeholders}) AND reserved_date IN ({date_placeholders})",
				(*barcodes, *selected_dates),
			).fetchall():
				result.setdefault(booking["reserved_date"], {})[booking["barcode"]] = booking
			return result

		def sync_selection_state() -> None:
			bookings = existing_bookings_for_selection()
			total_slots = len(selected_dates) * len(items)
			booked_slots = sum(len(day_map) for day_map in bookings.values())
			borrower_names = {booking["borrower"] for day_map in bookings.values() for booking in day_map.values()}
			if bookings and booked_slots == total_slots and len(borrower_names) == 1:
				borrower.set(next(iter(borrower_names)))
			else:
				borrower.set("")
			delete_button.state(["!disabled"] if bookings else ["disabled"])
			label = f"{len(selected_dates)} day(s)" if len(items) == 1 else f"{len(selected_dates)} day(s) x {len(items)} item(s) selected"
			if bookings:
				label += f" ({booked_slots} already booked)"
			selection_label.set(label)

		def toggle_date(date_text: str, event: "tk.Event | None" = None) -> None:
			shift_held = bool(event and event.state & 0x0001)
			ctrl_held = bool(event and event.state & 0x0004)
			if shift_held:
				start_text, end_text = last_clicked_date[0], date_text
				start = datetime.strptime(start_text, "%Y-%m-%d")
				end = datetime.strptime(end_text, "%Y-%m-%d")
				if start > end:
					start, end = end, start
				selected_dates.clear()
				current = start
				while current <= end:
					selected_dates.add(current.strftime("%Y-%m-%d"))
					current += timedelta(days=1)
			elif ctrl_held:
				if date_text in selected_dates:
					if len(selected_dates) > 1:
						selected_dates.discard(date_text)
				else:
					selected_dates.add(date_text)
				last_clicked_date[0] = date_text
			else:
				selected_dates.clear()
				selected_dates.add(date_text)
				last_clicked_date[0] = date_text
			sync_selection_state()
			build_calendar()

		def build_calendar() -> None:
			for child in calendar_frame.winfo_children():
				child.destroy()
			year, month = month_year
			month_label.set(f"{calendar.month_name[month]} {year}")
			for column, name in enumerate(calendar.day_abbr):
				ttk.Label(calendar_frame, text=name).grid(row=0, column=column, padx=3, pady=3)
			bookings_by_date: dict[str, dict[str, tuple[str, str]]] = {}
			for booking in self.database.execute(
				f"SELECT barcode, reserved_date, borrower, status FROM reservations WHERE barcode IN ({barcode_placeholders})",
				barcodes,
			).fetchall():
				bookings_by_date.setdefault(booking["reserved_date"], {})[booking["barcode"]] = (
					booking["borrower"], booking["status"]
				)
			for row_number, week in enumerate(calendar.monthcalendar(year, month), start=1):
				for column, day in enumerate(week):
					if not day:
						tk.Label(calendar_frame, text="", width=10).grid(row=row_number, column=column, padx=2, pady=2)
						continue
					date_text = f"{year:04d}-{month:02d}-{day:02d}"
					day_bookings = bookings_by_date.get(date_text, {})
					label = str(day)
					if day_bookings:
						if len(items) == 1:
							borrower_name, booking_status = next(iter(day_bookings.values()))
							label += (
								f"\nPending: {borrower_name}" if booking_status == "Pending"
								else f"\n{borrower_name}"
							)
						else:
							label += f"\n{len(day_bookings)}/{len(items)} booked"
					cell_color = (
						"#5b9bf7" if date_text in selected_dates
						else "#fff0cc" if day_bookings else "#ffffff"
					)
					date_cell = tk.Label(
						calendar_frame, text=label, width=10, height=2,
						bg=cell_color, fg="#000000",
						relief="solid" if day_bookings else "flat", borderwidth=1,
					)
					date_cell.grid(row=row_number, column=column, padx=2, pady=2)
					date_cell.bind("<Button-1>", lambda event, value=date_text: toggle_date(value, event))

		def change_month(offset: int) -> None:
				month_year[1] += offset
				if month_year[1] == 0:
					month_year[1], month_year[0] = 12, month_year[0] - 1
				elif month_year[1] == 13:
					month_year[1], month_year[0] = 1, month_year[0] + 1
				build_calendar()

		tk.Button(frame, text="<", command=lambda: change_month(-1)).grid(row=0, column=0)
		ttk.Label(frame, textvariable=month_label, width=22, anchor="center").grid(row=0, column=1)
		tk.Button(frame, text=">", command=lambda: change_month(1)).grid(row=0, column=2)
		ttk.Label(
			frame, text="Click a day to select it. Ctrl+click to add/remove a day, Shift+click to select a range.",
			wraplength=280, justify="left", foreground="#555555",
		).grid(row=2, column=0, columnspan=3, sticky="w", pady=(10, 0))
		ttk.Label(frame, textvariable=selection_label, foreground="#555555").grid(
			row=3, column=0, columnspan=3, sticky="w", pady=(2, 8)
		)
		ttk.Label(frame, text="Reserved for name or student ID:").grid(row=4, column=0, sticky="w", pady=(0, 4))
		borrower_entry = tk.Entry(frame, textvariable=borrower, width=28)
		borrower_entry.grid(row=4, column=1, columnspan=2, sticky="ew", pady=(0, 4))

		def resolve_scanned_booking_account(_event: tk.Event) -> str | None:
			accounts = self.find_accounts(borrower.get().strip())
			if len(accounts) != 1:
				return None
			borrower.set(accounts[0]["full_name"])
			self.global_scan_buffer = ""
			self.last_scan_key_time = 0.0
			self.scan_burst_started_at = 0.0
			self._clear_scan_capture()
			return "break"

		borrower_entry.bind("<Return>", resolve_scanned_booking_account, add="+")

		def refresh_after_change() -> None:
			date_dialog.destroy()
			if self.selected_barcode:
				row = self.database.execute(
					"SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)
				).fetchone()
				if row:
					self.show_item(row)
			self.refresh_items()
			self.sync_to_google_sheets(show_result=False)

		def save_booking() -> None:
			borrower_name = borrower.get().strip()
			if not borrower_name:
				messagebox.showwarning("Account required", "Enter the account name or student ID.", parent=date_dialog)
				return
			accounts = self.find_accounts(borrower_name)
			if not accounts:
				messagebox.showwarning(
					"Account required",
					"No account matches that name or student ID. Use Sign Up first.",
					parent=date_dialog,
				)
				return
			account = self.choose_account_dialog(accounts, date_dialog)
			if account is None:
				return
			borrower_name = account["full_name"]
			borrower.set(borrower_name)
			if not selected_dates:
				return
			existing = existing_bookings_for_selection()
			conflicts = [
				f"{name} on {date_text} (booked for {existing[date_text][barcode]['borrower']})"
				for date_text in sorted(selected_dates)
				for barcode, name in items
				if existing.get(date_text, {}).get(barcode) is not None
				and not self.names_match(existing[date_text][barcode]["borrower"], borrower_name)
			]
			confirmed_bookings = [
				f"{name} on {date_text}"
				for date_text in selected_dates
				for barcode, name in items
				if existing.get(date_text, {}).get(barcode)
				and existing[date_text][barcode]["status"] == "Confirmed"
			]
			if confirmed_bookings and not self.admin_mode:
				messagebox.showwarning(
					"Admin approval required",
					"Confirmed booking(s) can only be changed in admin mode:\n" + "\n".join(confirmed_bookings),
					parent=date_dialog,
				)
				return
			if conflicts:
				preview = "\n".join(conflicts[:10]) + ("\n..." if len(conflicts) > 10 else "")
				if not messagebox.askyesno(
					"Overwrite existing bookings?",
					f"{len(conflicts)} booking(s) will be overwritten:\n{preview}\n\nOverwrite them for {borrower_name}?",
					parent=date_dialog,
				):
					return
			request_rows = [
				[date_text, barcode, borrower_name, "FALSE", "Pending"]
				for date_text in sorted(selected_dates)
				for barcode, _name in items
			]
			created_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
			with self.db_lock:
				for date_text in selected_dates:
					for barcode, name in items:
						if existing.get(date_text, {}).get(barcode):
							self.database.execute(
								"UPDATE reservations SET borrower = ?, created_at = ?, status = 'Pending' "
								"WHERE barcode = ? AND reserved_date = ?",
								(borrower_name, created_at, barcode, date_text),
							)
						else:
							self.database.execute(
								"INSERT INTO reservations "
								"(barcode, item_name, reserved_date, borrower, created_at, status) "
								"VALUES (?, ?, ?, ?, ?, 'Pending')",
								(barcode, name, date_text, borrower_name, created_at),
							)
				self.database.commit()
			if self.submit_booking_requests(request_rows, date_dialog):
				date_dialog.destroy()

		def delete_booking() -> None:
			existing = existing_bookings_for_selection()
			to_delete = [
				(date_text, booking) for date_text, day_map in existing.items() for booking in day_map.values()
			]
			if not to_delete:
				return
			blocked = []
			pending_requests = []
			for date_text, booking in to_delete:
				if booking["status"] == "Confirmed" and not self.admin_mode:
					blocked.append(f"{booking['item_name'] if 'item_name' in booking.keys() else booking['barcode']} on {date_text} (confirmed)")
				elif booking["status"] == "Pending":
					if not self.admin_mode and not self.booking_request_is_recent(booking["created_at"]):
						blocked.append(f"{booking['barcode']} on {date_text} (pending for more than 5 minutes)")
					else:
						pending_requests.append((date_text, booking["barcode"], booking["borrower"]))
			if blocked:
				messagebox.showwarning(
					"Admin approval required",
					"Only bookings requested within the last 5 minutes can be deleted without admin mode:\n"
					+ "\n".join(blocked),
					parent=date_dialog,
				)
				return
			if messagebox.askyesno(
				"Delete Request",
				f"Delete {len(to_delete)} booking(s) across {len(items)} item(s)?",
				parent=date_dialog,
			):
				with self.db_lock:
					for _date_text, booking in to_delete:
						self.database.execute("DELETE FROM reservations WHERE id = ?", (booking["id"],))
					self.database.commit()
				self.delete_booking_requests(pending_requests)
				refresh_after_change()

		delete_button = ttk.Button(frame, text="Delete Request", command=delete_booking, state="disabled")
		delete_button.grid(row=5, column=0, pady=(12, 0))
		ttk.Button(frame, text="Request Booking", command=save_booking).grid(row=5, column=2, pady=(12, 0))
		build_calendar()
		sync_selection_state()

	def toggle_unavailable(self) -> None:
		"""Admin only: mark the selected item unavailable (or available again) for checkout."""
		if not self.admin_mode or not self.selected_barcode:
			return
		row = self.database.execute(
			"SELECT unavailable, checked_out_by FROM items WHERE barcode = ?", (self.selected_barcode,)
		).fetchone()
		if row is None:
			return
		if not row["unavailable"] and row["checked_out_by"]:
			messagebox.showwarning("Item is checked out", "Check the item in before marking it unavailable.")
			return
		self.database.execute(
			"UPDATE items SET unavailable = ? WHERE barcode = ?",
			(0 if row["unavailable"] else 1, self.selected_barcode),
		)
		self.database.commit()
		self.mark_recently_changed(self.selected_barcode)
		updated_row = self.database.execute(
			"SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)
		).fetchone()
		if updated_row:
			self.show_item(updated_row)
		self.refresh_items()
		self.sync_to_google_sheets(show_result=False)

	def finish_action(self, message: str) -> None:
		"""Common tail end of a successful check-in/out: notify, refresh the UI, and sync to Sheets."""
		messagebox.showinfo("Complete", message)
		row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)).fetchone()
		if row:
			self.show_item(row)
		self.borrower_name.set("")
		self.refresh_items()
		self.sync_to_google_sheets(show_result=False)

	def clear_selection(self) -> None:
		"""Reset the details panel to its no-item-selected state."""
		self.selected_barcode = None
		self.item_name.set("Scan an item to begin")
		self.item_status.set("Ready for scan")
		self.item_category.set("")
		self.borrower_name.set("")
		self.checkout_button.configure(state="disabled")
		self.checkin_button.configure(state="disabled")
		self.update_admin_controls()

	def delete_selected_item(self) -> None:
		"""Admin only: permanently remove the selected item and its bookings, after confirmation."""
		if not self.admin_mode or not self.selected_barcode:
			return
		row = self.database.execute(
			"SELECT name, checked_out_by FROM items WHERE barcode = ?", (self.selected_barcode,)
		).fetchone()
		if row is None:
			return
		message = f"Delete {row['name']} ({self.selected_barcode})?"
		if row["checked_out_by"]:
			message += f"\nIt is currently checked out to {row['checked_out_by']}."
		if not messagebox.askyesno("Confirm deletion", message, parent=self.root):
			return
		self.database.execute("DELETE FROM reservations WHERE barcode = ?", (self.selected_barcode,))
		self.database.execute("DELETE FROM items WHERE barcode = ?", (self.selected_barcode,))
		self.database.commit()
		self.clear_selection()
		self.refresh_items()
		self.sync_to_google_sheets(show_result=False)

	def add_item_dialog(self) -> None:
		"""Admin only: register a new item with a barcode, category, and optional photo."""
		if not self.admin_mode:
			return
		dialog = tk.Toplevel(self.root)
		dialog.title("Add item")
		dialog.resizable(False, False)
		dialog.transient(self.root)
		dialog.grab_set()
		barcode = tk.StringVar(value=self.scan_value.get().strip())
		name = tk.StringVar()
		category = tk.StringVar(value="Uncategorized")
		photo_path = tk.StringVar()
		frame = ttk.Frame(dialog, padding=18)
		frame.grid()
		ttk.Label(frame, text="Barcode:").grid(row=0, column=0, sticky="w", padx=(0, 8), pady=4)
		barcode_entry = ttk.Entry(frame, textvariable=barcode, width=32)
		barcode_entry.grid(row=0, column=1, pady=4)
		ttk.Label(frame, text="Item name:").grid(row=1, column=0, sticky="w", padx=(0, 8), pady=4)
		name_entry = ttk.Entry(frame, textvariable=name, width=32)
		name_entry.grid(row=1, column=1, pady=4)
		ttk.Label(frame, text="Category:").grid(row=2, column=0, sticky="w", padx=(0, 8), pady=4)
		category_menu = ttk.Combobox(
			frame, textvariable=category, values=self.category_choices(), state="readonly", width=29
		)
		category_menu.grid(row=2, column=1, pady=4)

		def add_category_from_dialog() -> None:
			new_category = self.add_category_dialog(dialog)
			category_menu.configure(values=self.category_choices())
			if new_category:
				category.set(new_category)

		ttk.Button(frame, text="New category", command=add_category_from_dialog).grid(row=2, column=2, padx=(8, 0))
		tk.Label(frame, text="Photo:").grid(row=3, column=0, sticky="w", padx=(0, 8), pady=4)
		photo_entry = ttk.Entry(frame, textvariable=photo_path, width=32, state="readonly")
		photo_entry.grid(row=3, column=1, sticky="ew", pady=4)

		def choose_new_photo() -> None:
			selected_path = filedialog.askopenfilename(
				parent=dialog,
				title="Choose item photo",
				filetypes=[("Image files", "*.png *.jpg *.jpeg *.gif *.bmp"), ("All files", "*.*")],
			)
			if selected_path:
				photo_path.set(selected_path)

		ttk.Button(frame, text="Choose photo", command=choose_new_photo).grid(row=3, column=2, padx=(8, 0))

		def save() -> None:
			barcode_text, name_text = barcode.get().strip(), name.get().strip()
			category_text = category.get().strip()
			category_value = None if category_text == "Uncategorized" else category_text
			if not barcode_text or not name_text:
				messagebox.showwarning("Missing information", "Enter both a barcode and an item name.", parent=dialog)
				return
			try:
				self.database.execute(
					"INSERT INTO items (barcode, name, category, photo_path) VALUES (?, ?, ?, ?)",
					(barcode_text, name_text, category_value, photo_path.get() or None),
				)
				self.database.commit()
			except sqlite3.IntegrityError:
				messagebox.showwarning("Barcode already exists", "That barcode is already registered.", parent=dialog)
				return
			dialog.destroy()
			self.refresh_items()
			self.sync_to_google_sheets(show_result=False)
			row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (barcode_text,)).fetchone()
			if row:
				self.show_item(row)

		ttk.Button(frame, text="Save item", command=save).grid(row=4, column=1, sticky="e", pady=(12, 0))
		barcode_entry.focus_set()

	def close(self) -> None:
		"""Stop the background sync worker and close the database before the window exits."""
		self.google_executor.shutdown(wait=False, cancel_futures=True)
		self.database.close()
		self.root.destroy()


if __name__ == "__main__":
	parser = argparse.ArgumentParser(description="Equipment Check-In System")
	parser.add_argument(
		"--database", "-d", metavar="PATH",
		help="Path to the SQLite database file to use instead of the default. "
		"Point this at a separate copy (e.g. one made with Export Database) to test "
		"safely on another computer without touching the live database.",
	)
	cli_args = parser.parse_args()
	if cli_args.database:
		DATABASE_FILE = str(Path(cli_args.database).expanduser().resolve())
		Path(DATABASE_FILE).parent.mkdir(parents=True, exist_ok=True)
		BACKUP_DIRECTORY = Path(DATABASE_FILE).parent / "database_backups"

	application = tk.Tk()
	CheckInSystem(application)
	application.mainloop()
