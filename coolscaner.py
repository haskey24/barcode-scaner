"""Simple USB barcode check-in/check-out system.

Most USB barcode scanners work as a keyboard: they type the barcode and press
		smtp_password_entry = ttk.Entry(frame, show="*", width=38)
		smtp_password_entry.grid(row=row, column=1, sticky="ew", pady=3)
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
import base64
from datetime import datetime, timedelta
import calendar
import hashlib
import json
from email.message import EmailMessage
import logging
import os
from pathlib import Path
import re
import secrets
import shutil
import smtplib
import subprocess
import sys
import threading
import time
import sqlite3
from urllib.parse import quote, urlencode, urlsplit
from urllib.request import Request, urlopen
import zipfile
from xml.etree import ElementTree
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
WEB_API_SYNC_INTERVAL_MS = 10_000
SELECTION_CLEAR_DELAY_MS = 3 * 60 * 1000
# How long a barcode is protected from sheet-driven changes after a local
# check-in/out, covering one export cycle plus network latency.
LOCAL_CHANGE_GRACE_SECONDS = (GOOGLE_SYNC_INTERVAL_MS / 1000) * 2
BOOKING_DELETE_GRACE_SECONDS = 5 * 60
NOTIFICATION_KEYRING_SERVICE = "EquipmentCheckIn.Notifications"
# USB scanners in keyboard mode normally send a barcode much faster than a
# person can type.  These values let us distinguish a scanner burst from
# ordinary typing in another field.
SCAN_BURST_GAP_SECONDS = 0.15
SCAN_MAX_AVERAGE_KEY_INTERVAL_SECONDS = 0.05
SCAN_MIN_CHARACTERS = 3
WEB_API_BASE_URL = os.environ.get("EQUIPMENT_CHECKIN_API_URL", "").strip()
WEB_API_EMAIL = os.environ.get("EQUIPMENT_CHECKIN_API_EMAIL", "").strip()
WEB_API_PASSWORD = os.environ.get("EQUIPMENT_CHECKIN_API_PASSWORD", "").strip()
WEB_API_INVENTORY_ID = os.environ.get("EQUIPMENT_CHECKIN_API_INVENTORY_ID", "")


def build_web_service_import_payload(database_path: str | Path) -> dict:
	"""Collect the local SQLite inventory into the payload expected by the hosted API import route."""
	database_path = Path(database_path)
	if not database_path.exists():
		return {"items": [], "borrowers": [], "reservations": [], "history": [], "categories": [], "bell_periods": []}
	payload = {"items": [], "borrowers": [], "reservations": [], "history": [], "categories": [], "bell_periods": []}
	with sqlite3.connect(database_path) as database:
		database.row_factory = sqlite3.Row
		for table_name in ("categories", "items", "borrowers", "reservations", "checkout_history", "bell_periods"):
			try:
				if database.execute(f"SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (table_name,)).fetchone() is None:
					continue
			except sqlite3.DatabaseError:
				continue
		if database.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='categories'").fetchone() is not None:
			for row in database.execute("SELECT name, sort_order FROM categories ORDER BY sort_order, name COLLATE NOCASE").fetchall():
				payload["categories"].append({"name": row["name"], "sort_order": row["sort_order"]})
		if database.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='items'").fetchone() is not None:
			for row in database.execute(
				"SELECT barcode, name, category, unavailable, missing, checked_out_by, checked_out_at, checkout_due_at, checkout_late FROM items ORDER BY name COLLATE NOCASE"
			).fetchall():
				payload["items"].append({
					"barcode": row["barcode"], "name": row["name"], "category": row["category"],
					"unavailable": bool(row["unavailable"]), "missing": bool(row["missing"]),
					"checked_out_by": row["checked_out_by"], "checked_out_at": row["checked_out_at"],
					"checkout_due_at": row["checkout_due_at"], "checkout_late": bool(row["checkout_late"]),
				})
		borrower_table = next((
			table_name for table_name in ("accounts", "borrowers")
			if database.execute(
				"SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (table_name,)
			).fetchone() is not None
		), None)
		if borrower_table:
			for row in database.execute(
				f"SELECT full_name, student_id, email, phone, sms_opt_in FROM {borrower_table} ORDER BY full_name COLLATE NOCASE"
			).fetchall():
				payload["borrowers"].append({
					"full_name": row["full_name"], "student_id": row["student_id"], "email": row["email"] or "",
					"phone": row["phone"] or "", "sms_opt_in": bool(row["sms_opt_in"]),
				})
		if database.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='reservations'").fetchone() is not None:
			for row in database.execute("SELECT barcode, item_name, reserved_date, borrower, created_at, status FROM reservations ORDER BY reserved_date, item_name COLLATE NOCASE").fetchall():
				payload["reservations"].append({
					"barcode": row["barcode"], "item_name": row["item_name"], "reserved_date": row["reserved_date"],
					"borrower": row["borrower"], "created_at": row["created_at"], "status": row["status"],
				})
		if database.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='checkout_history'").fetchone() is not None:
			for row in database.execute("SELECT barcode, item_name, action, borrower, timestamp FROM checkout_history ORDER BY rowid DESC").fetchall():
				payload["history"].append({
					"barcode": row["barcode"], "item_name": row["item_name"], "action": row["action"],
					"borrower": row["borrower"], "timestamp": row["timestamp"],
				})
		if database.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='bell_periods'").fetchone() is not None:
			for row in database.execute("SELECT period_date, period_name, start_time, end_time FROM bell_periods ORDER BY period_date, start_time").fetchall():
				payload["bell_periods"].append({
					"period_date": row["period_date"], "period_name": row["period_name"],
					"start_time": row["start_time"], "end_time": row["end_time"],
				})
	return payload


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
		self.multi_scan_queue: list[str] = []
		self.selection_clear_after_id: str | None = None
		self.item_selection_vars: dict[str, tk.BooleanVar] = {}
		self.item_row_images: list[ImageTk.PhotoImage] = []
		self.item_base_order: list[str] = []
		self.item_row_frames: dict[str, ttk.Frame] = {}
		self.item_row_separators: dict[str, ttk.Separator] = {}
		self.audit_mode = tk.BooleanVar(value=False)
		self.audit_items_scanned: list[str] = []
		self.audit_total_expected: int = 0
		self.audit_categories: set[str] | None = None
		self.audit_category_label = tk.StringVar(value="All categories")
		self.expiration_check_running = False
		self.google_worksheets = {}
		self.last_export_values = None
		self.last_history_export_values = None
		self.last_bookings_export_values = None
		self.google_executor = ThreadPoolExecutor(max_workers=1)
		self.web_api_executor = ThreadPoolExecutor(max_workers=1)
		self.notification_executor = ThreadPoolExecutor(max_workers=2)
		self.google_sync_running = False
		self.google_import_running = False
		self.bell_schedule_import_running = False
		self.bell_schedule_refresh_callback = None
		self.bell_schedule_refresh_callback = None
		self.booking_requests_setup_done = False
		self.last_booking_item_options = None
		# Barcode -> monotonic time of the last local status change, so the sheet
		# import can't undo a check-in/out with a stale snapshot it read moments before.
		self.recently_changed_barcodes: dict[str, float] = {}
		self.audit_progress = tk.DoubleVar(value=0.0)
		self.audit_status_label = tk.StringVar(value="Progress: 0 / 0")
		self.web_api_base_url = WEB_API_BASE_URL
		self.web_api_email = WEB_API_EMAIL
		self.web_api_password = WEB_API_PASSWORD
		self.web_api_inventory_id = WEB_API_INVENTORY_ID
		self.web_api_base_url = self.get_setting("web_api_base_url", self.web_api_base_url)
		self.web_api_email = self.get_setting("web_api_email", self.web_api_email)
		self.web_api_inventory_id = self.get_setting("web_api_inventory_id", self.web_api_inventory_id)
		try:
			self.web_api_password = self.get_notification_secret("web_api_password") or self.web_api_password
		except Exception:
			pass
		self.web_api_token = ""
		self.web_api_sync_running = False
		self.web_api_cycle_running = False
		self.web_api_poll_started = False
		self.web_api_pending_changes: dict[str, dict] = {}
		self.web_api_pending_lock = threading.Lock()
		self.build_interface()
		self.refresh_items()
		self.update_admin_controls()
		self.root.protocol("WM_DELETE_WINDOW", self.close)
		self.root.after(1_000, self.poll_google_sheet)
		if self.web_api_base_url:
			self.root.after(1_500, self.sync_to_web_service)
			self.root.after(3_000, self.poll_web_service)
			self.web_api_poll_started = True
		else:
			self.root.after(1_500, self.sync_to_google_sheets)
		self.root.after(30_000, self.expire_due_checkouts)
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

	def get_bell_schedule_file(self) -> str:
		"""Return the locally downloaded bell schedule file path, if configured."""
		setting = self.database.execute(
			"SELECT value FROM settings WHERE key = 'bell_schedule_file'"
		).fetchone()
		return (setting["value"] if setting else "").strip()

	def get_setting(self, key: str, default: str = "") -> str:
		"""Return a persisted app setting, or a default if it is missing."""
		setting = self.database.execute(
			"SELECT value FROM settings WHERE key = ?",
			(key,),
		).fetchone()
		return setting["value"] if setting else default

	def set_setting(self, key: str, value: str) -> None:
		"""Persist a text value in the app settings table."""
		self.database.execute(
			"INSERT INTO settings (key, value) VALUES (?, ?) "
			"ON CONFLICT(key) DO UPDATE SET value = excluded.value",
			(key, value),
		)
		self.database.commit()

	def set_bell_schedule_file(self, file_path: str) -> None:
		self.database.execute(
			"INSERT INTO settings (key, value) VALUES ('bell_schedule_file', ?) "
			"ON CONFLICT(key) DO UPDATE SET value = excluded.value",
			(file_path.strip(),),
		)
		self.database.commit()

	def _read_downloaded_bell_schedule(self, file_path: str) -> dict:
		"""Convert a downloaded .docx or text schedule into parser-compatible document text."""
		path = Path(file_path)
		if path.suffix.casefold() in {".txt", ".csv"}:
			return {"body": {"content": [{"paragraph": {"elements": [{"textRun": {"content": path.read_text(encoding="utf-8-sig")}}]}}]}}
		if path.suffix.casefold() == ".pdf":
			from importlib import import_module
			reader = import_module("pypdf").PdfReader(str(path))
			text = self._normalize_pdf_schedule_text(
				"\n".join(page.extract_text() or "" for page in reader.pages)
			)
			return {"body": {"content": [{"paragraph": {"elements": [{"textRun": {"content": text}}]}}]}}
		if path.suffix.casefold() != ".docx":
			raise ValueError("Choose a downloaded PDF, Word document (.docx), or text file (.txt/.csv).")
		with zipfile.ZipFile(path) as archive:
			document_xml = archive.read("word/document.xml")
		root = ElementTree.fromstring(document_xml)
		namespace = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"
		lines: list[str] = []
		for child in root.find(f"{namespace}body") or []:
			if child.tag == f"{namespace}tbl":
				rows = child.findall(f"{namespace}tr")
				for row in rows:
					row_cells: list[str] = []
					for cell in row.findall(f"{namespace}tc"):
						cell_text = "".join(node.text or "" for node in cell.iter(f"{namespace}t"))
						if cell_text.strip():
							row_cells.append(cell_text.strip())
					if row_cells:
						lines.append(" ".join(row_cells))
			elif child.tag == f"{namespace}p":
				text = "".join(node.text or "" for node in child.iter(f"{namespace}t"))
				if text.strip():
					lines.append(text.strip())
		text = "\n".join(lines)
		return {"body": {"content": [{"paragraph": {"elements": [{"textRun": {"content": text}}]}}]}}

	def _normalize_pdf_schedule_text(self, text: str) -> str:
		"""Turn PDF table-cell extraction into one logical schedule row per line."""
		text = text.replace("\ufb00", "ff").replace("\xa0", " ")
		text = re.sub(r"\s+", " ", text).strip()
		section_patterns = (
			r"Monday\s+Bell\s+Schedule",
			r"Tuesday\s*-\s*Friday\s+Bell\s+Schedule",
			r"Monday\s*\(\s*Staff\s+Development\s+Day\s*\)\s+Schedule",
			r"Finals\s+Schedule",
			r"Dates:",
			r"1st\s+Semester\s+Finals:",
			r"2nd\s+Semester\s+Finals:",
		)
		for pattern in section_patterns:
			text = re.sub(f"(?i)({pattern})", r"\n\1", text)
		row_pattern = r"(Period\s+\d+|PLC\s+Collaboration|Lunch|Staff\s+Development|Break|Make-ups)"
		text = re.sub(rf"(?i)\s+{row_pattern}\b", r"\n\1", text)
		return "\n".join(line.strip() for line in text.splitlines() if line.strip())

	def _google_doc_text(self, value) -> str:
		"""Recursively collect text-run content from a Google Docs API object."""
		if isinstance(value, dict):
			if "textRun" in value:
				return value["textRun"].get("content", "")
			if "table" in value:
				table_rows = value["table"].get("tableRows", [])
				column_count = max(
					(len(row.get("tableCells", [])) for row in table_rows), default=0
				)
				columns = []
				for column_index in range(column_count):
					columns.append("\n".join(
						self._google_doc_text(row.get("tableCells", [])[column_index])
						for row in table_rows
						if column_index < len(row.get("tableCells", []))
					))
				return "\n".join(columns)
			return "".join(self._google_doc_text(child) for child in value.values())
		if isinstance(value, list):
			return "".join(self._google_doc_text(child) for child in value)
		return ""

	def _parse_formatted_bell_schedule(self, document: dict) -> list[tuple[str, str, str, str]]:
		"""Parse the school-year schedule layout with weekday and special-day sections."""
		lines = [
			re.sub(r"\s+", " ", line.replace("\xa0", " ").replace("–", "-")).strip()
			for line in self._google_doc_text(document).splitlines()
			if line.strip()
		]
		year_match = next(
			(match for line in lines if (match := re.search(r"(20\d{2})\s*-\s*(20\d{2})", line))),
			None,
		)
		if year_match is None:
			raise ValueError("Could not find a school-year heading such as 2026-2027.")
		first_year, second_year = int(year_match.group(1)), int(year_match.group(2))
		sections: dict[str, list[tuple[str, str, str]]] = {}
		special_dates: dict[str, list[tuple[str, str, str]]] = {}
		finals_target_dates: set[str] = set()
		finals_mappings: list[tuple[list[str], list[tuple[list[int], str, str]]]] = []
		current_finals_dates: list[str] = []
		current_finals_period_groups: list[tuple[list[int], str, str]] = []
		current_section: str | None = None
		current_rows: list[tuple[str, str, str]] = []

		def apply_finals_mapping(date_order: list[str], period_groups: list[tuple[list[int], str, str]]) -> None:
			if not date_order or len(period_groups) < 2:
				return
			first_period_group = period_groups[0]
			second_period_group = period_groups[1]
			for day_index, date_text in enumerate(date_order):
				if day_index >= len(first_period_group[0]) or day_index >= len(second_period_group[0]):
					continue
				finals_target_dates.add(date_text)
				special_dates[date_text] = [
					(f"Period {first_period_group[0][day_index]}", first_period_group[1], first_period_group[2]),
					(f"Period {second_period_group[0][day_index]}", second_period_group[1], second_period_group[2]),
				]

		def save_section() -> None:
			if current_section and current_rows:
				sections[current_section] = list(current_rows)

		def date_from_month_day(month_name: str, day_text: str) -> str:
			month = next(
				(index for index, name in enumerate(calendar.month_abbr) if name.casefold() == month_name[:3].casefold()),
				None,
			)
			if month is None:
				raise ValueError(f"Unknown month in Google Doc: {month_name}")
			year = first_year if month >= 9 else second_year
			return f"{year:04d}-{month:02d}-{int(day_text):02d}"

		for index, line in enumerate(lines):
			lower = line.casefold()
			if lower.startswith("monday (staff development day) schedule"):
				save_section()
				current_section, current_rows = "staff", []
				continue
			if lower.startswith("monday bell schedule"):
				save_section()
				current_section, current_rows = "monday", []
				continue
			if re.match(r"tuesday\s*-\s*friday bell schedule", lower):
				save_section()
				current_section, current_rows = "tuesday-friday", []
				continue
			if lower.startswith("finals schedule"):
				save_section()
				current_section, current_rows = "finals", []
				continue
			if current_section is None and re.search(r"^(?:period\s+\d+|plc\b|lunch\b)", line, re.IGNORECASE):
				current_section, current_rows = "monday", []
			if current_section is None and re.search(r"\d{1,2}:\d{2}", line):
				current_section, current_rows = "fallback", []
			if current_section == "staff" and lower.startswith("dates:"):
				for month_name, day_text in re.findall(r"([A-Za-z]+)\.?\s+(\d{1,2})", line):
					special_dates[date_from_month_day(month_name, day_text)] = []
				continue
			if current_section == "finals":
				semester_match = re.match(r"(1st|2nd) Semester Finals:\s*(.*)", line, re.IGNORECASE)
				if semester_match:
					months_and_days = re.findall(r"([A-Za-z]+)\.?\s+(\d{1,2}(?:\s*,\s*\d{1,2})*)", semester_match.group(2))
					semester_dates: list[str] = []
					for month_name, days_text in months_and_days:
						for day_text in re.findall(r"\d+", days_text):
							date_text = date_from_month_day(month_name, day_text)
							semester_dates.append(date_text)
							special_dates.setdefault(date_text, [])
					if current_finals_period_groups and semester_dates:
						finals_mappings.append((list(semester_dates), list(current_finals_period_groups)))
					current_finals_dates = list(semester_dates)
					current_finals_period_groups = []
					continue
				period_group_match = re.fullmatch(r"Period\s+(\d+)\s+(\d+)\s+(\d+)", line, re.IGNORECASE)
				if period_group_match and index + 2 < len(lines):
					period_values = [int(period_group_match.group(1)), int(period_group_match.group(2)), int(period_group_match.group(3))]
					start_time = self.parse_bell_time(lines[index + 1])
					end_time = self.parse_bell_time(lines[index + 2])
					if start_time and end_time:
						current_finals_period_groups.append((period_values, start_time, end_time))
						continue
				if re.match(r"Day\s+\d", line, re.IGNORECASE):
					continue
			if current_section is None:
				continue

			times = re.search(
				r"(?P<start>\d{1,2}:\d{2}(?:\s?[APap]\.?[Mm]\.?)?)\s*(?:-|–|—|to)?\s*(?P<end>\d{1,2}:\d{2}(?:\s?[APap]\.?[Mm]\.?)?)",
				line,
			)
			if times:
				period_name = line[:times.start()].strip()
				start_time = self.parse_bell_time(times.group("start"))
				end_time = self.parse_bell_time(times.group("end"))
				if start_time and end_time and not re.search(r"[APap][Mm]", line) and start_time >= end_time and start_time >= "12:00" and end_time < "12:00":
					end_minutes = int(end_time[0:2]) * 60 + int(end_time[3:5])
					end_time = f"{(12 + (end_minutes // 60)) % 24:02d}:{end_minutes % 60:02d}"
				if period_name and start_time and end_time:
					current_rows.append((period_name, start_time, end_time))
				continue

			period_match = re.fullmatch(r"(?:period\s+\d+|plc\s+collaboration|lunch)", line, re.IGNORECASE)
			if period_match and index + 2 < len(lines):
				first_time = self.parse_bell_time(lines[index + 1])
				second_time = self.parse_bell_time(lines[index + 2])
				if first_time and second_time:
					period_name = line.strip()
					if period_name and first_time < second_time:
						current_rows.append((period_name, first_time, second_time))
					continue
		save_section()
		if current_finals_dates and current_finals_period_groups:
			finals_mappings.append((list(current_finals_dates), list(current_finals_period_groups)))
		for date_order, period_groups in finals_mappings:
			apply_finals_mapping(date_order, period_groups)
		for date_text in list(special_dates):
			if not special_dates[date_text] and date_text not in finals_target_dates:
				special_dates[date_text] = list(sections.get("staff", []))
		parsed_rows: dict[str, list[tuple[str, str, str]]] = {}
		current = datetime(first_year, 9, 1)
		last = datetime(second_year, 6, 30)
		while current <= last:
			if current.strftime("%Y-%m-%d") in special_dates:
				rows_for_date = special_dates[current.strftime("%Y-%m-%d")]
			elif current.weekday() == 0:
				rows_for_date = sections.get("monday", sections.get("fallback", []))
			elif current.weekday() in {1, 2, 3, 4}:
				rows_for_date = sections.get("tuesday-friday", sections.get("fallback", []))
			else:
				rows_for_date = []
			if rows_for_date:
				parsed_rows[current.strftime("%Y-%m-%d")] = rows_for_date
			current += timedelta(days=1)
		# Strip PLC/placeholder rows such as "Period 0" before saving. If a real period starts
		# earlier than the previous row's end, use the previous end; otherwise keep the actual
		# AM/PM value for that period.
		for date_text, date_rows in parsed_rows.items():
			filtered_rows: list[tuple[str, str, str]] = []
			plc_start: str | None = None
			lunch_start: str | None = None
			first_after_lunch = True
			uses_24h_time = any(
				int(start_time[:2]) >= 13 or int(end_time[:2]) >= 13
				for _, start_time, end_time in date_rows
			)
			for period_name, start_time, end_time in date_rows:
				lower_name = period_name.casefold().strip()
				if lower_name.startswith("plc") or re.fullmatch(r"(?:period\s*)?0", lower_name):
					if plc_start is None:
						plc_start = start_time
					continue
				if "lunch" in lower_name:
					lunch_start = start_time
					continue
				if lunch_start is not None and first_after_lunch:
					if not uses_24h_time:
						def add_twelve(value: str) -> str:
							minutes = int(value[0:2]) * 60 + int(value[3:5])
							return f"{(12 + (minutes // 60)) % 24:02d}:{minutes % 60:02d}"
						start_time = lunch_start
						if start_time < "12:00":
							start_time = add_twelve(start_time)
						if end_time < "12:00":
							end_time = add_twelve(end_time)
					else:
						start_time = lunch_start
					first_after_lunch = False
					filtered_rows.append((period_name, start_time, end_time))
					continue
				elif lunch_start is not None and (start_time < "12:00" or end_time < "12:00") and not uses_24h_time:
					def add_twelve(value: str) -> str:
						minutes = int(value[0:2]) * 60 + int(value[3:5])
						return f"{(12 + (minutes // 60)) % 24:02d}:{minutes % 60:02d}"
					if start_time < "12:00":
						start_time = add_twelve(start_time)
					if end_time < "12:00":
						end_time = add_twelve(end_time)
				if start_time >= end_time:
					continue
				filtered_rows.append((period_name, start_time, end_time))
			if filtered_rows:
				if not any(int(row[1][0:2]) >= 12 for row in filtered_rows):
					filtered_rows.sort(key=lambda row: row[1])
				normalized_rows: list[tuple[str, str, str]] = []
				for index, (period_name, start_time, end_time) in enumerate(filtered_rows):
					lower_name = period_name.strip().casefold()
					if start_time >= end_time and not (
						lunch_start is not None and re.fullmatch(r"period\s*5\b", lower_name, flags=re.IGNORECASE)
					):
						continue
					if index == 0 and plc_start is not None and re.fullmatch(r"period\s*1\b", lower_name, flags=re.IGNORECASE):
						actual_start = plc_start
					else:
						actual_start = start_time
					normalized_rows.append((period_name, actual_start, end_time))
				filtered_rows = normalized_rows
			parsed_rows[date_text] = filtered_rows
		return [
			(date_text, period_name, start_time, end_time)
			for date_text, date_rows in parsed_rows.items()
			for period_name, start_time, end_time in date_rows
		]

	def import_bell_schedule_from_file(self, show_result: bool = True) -> None:
		"""Choose and link a downloaded Google Doc export for local bell-schedule imports."""
		if self.bell_schedule_import_running:
			return
		file_path = filedialog.askopenfilename(
			parent=self.root,
			title="Choose downloaded bell schedule",
			filetypes=[
				("Downloaded Google Doc", "*.pdf *.docx *.txt *.csv"),
				("PDF document", "*.pdf"),
				("Word document", "*.docx"),
				("Text files", "*.txt *.csv"),
				("All files", "*.*"),
			],
		)
		if not file_path:
			return
		self.set_bell_schedule_file(file_path)
		self.bell_schedule_import_running = True
		self.google_executor.submit(
			self._run_with_bell_schedule_lock, self._import_bell_schedule_from_file, show_result
		)

	def _run_with_bell_schedule_lock(self, func, *args, **kwargs) -> None:
		"""Run the bell schedule import on the executor thread and always clear its dedicated lock."""
		try:
			func(*args, **kwargs)
		finally:
			self.bell_schedule_import_running = False

	def _import_bell_schedule_from_file(self, show_result: bool = True) -> None:
		"""Import a downloaded schedule without making any network or Google API calls."""
		try:
			file_path = self.get_bell_schedule_file()
			if not file_path or not Path(file_path).exists():
				raise FileNotFoundError("The linked bell schedule download could not be found.")
			document = self._read_downloaded_bell_schedule(file_path)
			parsed_rows = self._parse_formatted_bell_schedule(document)
			if not parsed_rows:
				raise ValueError("The downloaded document did not contain a recognizable bell schedule.")
			with self.db_lock:
				self.database.execute("DELETE FROM bell_periods")
				self.database.executemany(
					"INSERT INTO bell_periods (period_date, period_name, start_time, end_time) VALUES (?, ?, ?, ?)",
					parsed_rows,
				)
				self.database.commit()
			date_count = len({period_date for period_date, _, _, _ in parsed_rows})
			if self.bell_schedule_refresh_callback:
				self.root.after(0, self.bell_schedule_refresh_callback)
			if show_result:
				self.root.after(0, lambda: messagebox.showinfo(
					"Bell schedule imported",
					f"Imported {len(parsed_rows)} period(s) for {date_count} date(s) from the downloaded file.",
					parent=self.root,
				))
		except Exception as error:
			if show_result:
				self.root.after(0, lambda: messagebox.showerror(
					"Bell schedule import failed", str(error), parent=self.root
				))

	def web_api_request(self, method: str, path: str, payload: dict | None = None, headers: dict | None = None) -> tuple[int, dict | None]:
		"""Send a request to the hosted inventory API and return the HTTP status and JSON payload, or a detail string."""
		if not self.web_api_base_url:
			return 0, None
		request_headers = {"Accept": "application/json"}
		if headers:
			request_headers.update(headers)
		if payload is not None:
			request_headers["Content-Type"] = "application/json"
		body = json.dumps(payload).encode("utf-8") if payload is not None else None
		request = Request(f"{self.web_api_base_url.rstrip('/')}{path}", data=body, headers=request_headers, method=method)
		try:
			with urlopen(request, timeout=30) as response:
				text = response.read().decode("utf-8")
				return response.status, json.loads(text) if text else None
		except Exception as error:
			if hasattr(error, "read"):
				try:
					text = error.read().decode("utf-8")
					try:
						details = json.loads(text) if text else {}
					except json.JSONDecodeError:
						details = {"detail": text}
				except Exception:
					details = {"detail": str(error)}
				status_code = getattr(error, "code", 500)
				return status_code, details
			return getattr(error, "code", 500), {"detail": str(error)}

	def ensure_web_api_session(self) -> bool:
		"""Authenticate against the hosted API and capture a token and inventory ID for this desktop app."""
		if not self.web_api_base_url:
			return False
		if self.web_api_token and self.web_api_inventory_id:
			return True
		if not self.web_api_email or not self.web_api_password:
			return False
		status_code, payload = self.web_api_request(
			"POST",
			"/api/auth/login",
			{"email": self.web_api_email, "password": self.web_api_password},
		)
		if status_code != 200 or payload is None:
			return False
		self.web_api_token = payload.get("token", "")
		inventories = payload.get("inventories", [])
		if self.web_api_inventory_id:
			inventory_id = str(self.web_api_inventory_id)
			self.web_api_inventory_id = inventory_id
			return bool(self.web_api_token)
		if inventories:
			self.web_api_inventory_id = str(inventories[0]["id"])
		return bool(self.web_api_token and self.web_api_inventory_id)

	def sync_to_web_service(self, show_result: bool = True) -> None:
		"""Upload the desktop database to the hosted inventory API once when the app first connects to a remote service."""
		if not self.web_api_base_url or self.web_api_sync_running:
			return
		self.web_api_sync_running = True
		try:
			if not self.ensure_web_api_session():
				if show_result:
					self.root.after(0, lambda: messagebox.showwarning(
						"Web service not configured",
						"Set --api-url, --api-email, and --api-password to sync this app to the hosted inventory API.",
						parent=self.root,
					))
				self.web_api_sync_running = False
				return
			payload = build_web_service_import_payload(DATABASE_FILE)
			if not any(payload.values()):
				self.web_api_sync_running = False
				return
			status_code, response = self.web_api_request(
				"POST",
				"/api/import/sqlite",
				payload,
				headers={
					"Authorization": f"Bearer {self.web_api_token}",
					"X-Inventory-ID": str(self.web_api_inventory_id),
				},
			)
			if status_code == 200:
				if show_result:
					self.root.after(0, lambda: messagebox.showinfo(
						"Web service", "Inventory synced to the hosted inventory service.", parent=self.root
					))
			elif status_code == 409:
				borrower_status, borrower_response = self.web_api_request(
					"PUT",
					"/api/borrowers/sync",
					{"borrowers": payload["borrowers"]},
					headers={
						"Authorization": f"Bearer {self.web_api_token}",
						"X-Inventory-ID": str(self.web_api_inventory_id),
					},
				)
				if borrower_status == 200 and show_result:
					self.root.after(0, lambda: messagebox.showinfo(
						"Web service", "Borrower accounts synced to the hosted inventory service.", parent=self.root
					))
				elif show_result:
					detail = borrower_response.get("detail") if isinstance(borrower_response, dict) else str(borrower_response)
					self.root.after(0, lambda: messagebox.showwarning(
						"Borrower sync skipped", detail or f"Hosted service rejected borrower sync (HTTP {borrower_status}).",
						parent=self.root,
					))
			elif show_result:
				detail = response.get("detail") if isinstance(response, dict) else str(response)
				self.root.after(0, lambda: messagebox.showwarning(
					"Web inventory sync skipped",
					detail or f"Hosted inventory rejected the desktop sync (HTTP {status_code}).",
					parent=self.root,
				))
			self.web_api_sync_running = False
		except Exception as error:
			self.web_api_sync_running = False
			if show_result:
				self.root.after(0, lambda: messagebox.showerror(
					"Web inventory sync failed",
					str(error), parent=self.root,
				))

	def queue_web_service_checkout_sync(self, barcode: str) -> None:
		"""Queue one locally committed checkout change for the hosted inventory."""
		if not self.web_api_base_url or not barcode:
			return
		with self.db_lock:
			row = self.database.execute(
				"SELECT checked_out_by, checked_out_at, checkout_due_at FROM items WHERE barcode = ?",
				(barcode,),
			).fetchone()
		if row is None:
			return
		with self.web_api_pending_lock:
			self.web_api_pending_changes[barcode] = {
				"checked_out_by": row["checked_out_by"],
				"checked_out_at": row["checked_out_at"],
				"checkout_due_at": row["checkout_due_at"],
			}
		self.start_web_service_sync_cycle()

	def start_web_service_sync_cycle(self) -> None:
		"""Run one serialized web push/pull cycle without blocking the Tk event loop."""
		if not self.web_api_base_url or self.web_api_cycle_running:
			return
		self.web_api_cycle_running = True
		self.web_api_executor.submit(self.run_web_service_sync_cycle)

	def poll_web_service(self) -> None:
		"""Refresh hosted checkout changes periodically while the desktop app is open."""
		self.start_web_service_sync_cycle()
		self.root.after(WEB_API_SYNC_INTERVAL_MS, self.poll_web_service)

	def authenticated_web_api_request(
		self, method: str, path: str, payload: dict | None = None,
	) -> tuple[int, dict | list | None]:
		if not self.ensure_web_api_session():
			return 401, None
		headers = {
			"Authorization": f"Bearer {self.web_api_token}",
			"X-Inventory-ID": str(self.web_api_inventory_id),
		}
		status_code, response = self.web_api_request(method, path, payload, headers)
		if status_code == 401:
			self.web_api_token = ""
			if self.ensure_web_api_session():
				headers["Authorization"] = f"Bearer {self.web_api_token}"
				status_code, response = self.web_api_request(method, path, payload, headers)
		return status_code, response

	def run_web_service_sync_cycle(self) -> None:
		"""Push pending local changes, then apply the latest hosted checkout state."""
		conflicted_barcodes: set[str] = set()
		try:
			if not self.ensure_web_api_session():
				return
			with self.web_api_pending_lock:
				pending = list(self.web_api_pending_changes.items())
			for barcode, change in pending:
				borrower = change["checked_out_by"]
				if borrower:
					status_code, _response = self.authenticated_web_api_request(
						"POST", f"/api/items/{quote(barcode, safe='')}/checkout",
						{"borrower": borrower, "due_at": change["checkout_due_at"]},
					)
				else:
					status_code, _response = self.authenticated_web_api_request(
						"POST", f"/api/items/{quote(barcode, safe='')}/checkin",
					)
				if status_code == 200 or (status_code == 409 and not borrower):
					with self.web_api_pending_lock:
						if self.web_api_pending_changes.get(barcode) == change:
							self.web_api_pending_changes.pop(barcode, None)
				elif status_code == 409:
					with self.web_api_pending_lock:
						if self.web_api_pending_changes.get(barcode) == change:
							self.web_api_pending_changes.pop(barcode, None)
					conflicted_barcodes.add(barcode)
				elif status_code == 401:
					return

			status_code, remote_items = self.authenticated_web_api_request("GET", "/api/items")
			if status_code == 200 and isinstance(remote_items, list):
				self.root.after(0, self.apply_web_service_item_snapshot, remote_items, conflicted_barcodes)
		except Exception:
			logging.exception("Web service checkout sync failed")
		finally:
			self.web_api_cycle_running = False

	def apply_web_service_item_snapshot(
		self, remote_items: list[dict], conflicted_barcodes: set[str] | None = None,
	) -> None:
		"""Apply hosted checkout fields without overwriting local item metadata."""
		conflicted_barcodes = conflicted_barcodes or set()
		changed = False
		with self.db_lock:
			for remote in remote_items:
				barcode = str(remote.get("barcode", ""))
				if not barcode:
					continue
				if barcode in conflicted_barcodes:
					self.recently_changed_barcodes.pop(barcode, None)
				with self.web_api_pending_lock:
					if barcode in self.web_api_pending_changes:
						continue
				local = self.database.execute(
					"SELECT name, checked_out_by, checked_out_at, checkout_due_at, checkout_late "
					"FROM items WHERE barcode = ?", (barcode,),
				).fetchone()
				if local is None:
					continue
				borrower = remote.get("checked_out_by") or None
				checked_out_at = remote.get("checked_out_at") if borrower else None
				due_at = remote.get("checkout_due_at") if borrower else None
				is_late = int(remote.get("status") == "Late")
				if (local["checked_out_by"], local["checked_out_at"], local["checkout_due_at"], int(local["checkout_late"])) == (borrower, checked_out_at, due_at, is_late):
					continue
				if local["checked_out_by"] != borrower:
					if local["checked_out_by"]:
						self.record_history(barcode, local["name"], "Checked in", local["checked_out_by"])
						if not borrower:
							self.database.execute(
								"DELETE FROM reservations WHERE barcode = ? AND reserved_date <= ?",
								(barcode, datetime.now().strftime("%Y-%m-%d")),
							)
					if borrower:
						self.record_history(barcode, local["name"], "Checked out", borrower)
				self.database.execute(
					"UPDATE items SET checked_out_by = ?, checked_out_at = ?, checkout_due_at = ?, checkout_late = ? "
					"WHERE barcode = ?",
					(borrower, checked_out_at, due_at, is_late, barcode),
				)
				self.mark_recently_changed(barcode)
				changed = True
			if changed:
				self.database.commit()
		if changed:
			self.refresh_items()

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
				"SELECT items.barcode, items.name, items.category, items.unavailable, items.missing, "
				"items.checked_out_by, items.checked_out_at, items.checkout_due_at, items.checkout_late FROM items "
				"LEFT JOIN categories ON categories.name = items.category COLLATE NOCASE "
				"ORDER BY COALESCE(categories.sort_order, 999999), COALESCE(items.category, '') COLLATE NOCASE, "
				"CASE "
				"WHEN items.missing = 1 THEN 3 "
				"WHEN items.unavailable = 1 THEN 2 "
				"WHEN items.checked_out_by IS NOT NULL THEN 1 "
				"ELSE 0 END, items.name COLLATE NOCASE"
			).fetchall()
			values = [["Barcode", "Item", "Category", "Status", "Checked out by", "Checkout time", "Checkout due"]]
			for row in rows:
				today_reservation = self.get_reservation(row["barcode"])
				if row["missing"]:
					status = "Missing"
				elif row["unavailable"]:
					status = "Unavailable"
				elif row["checked_out_by"]:
					status = "Late" if row["checkout_late"] else "Checked out"
				elif today_reservation:
					status = "Reserved"
				else:
					status = "Available"
				values.append([
					row["barcode"], row["name"], row["category"] or "Uncategorized", status,
					row["checked_out_by"] or "", row["checked_out_at"] or "", row["checkout_due_at"] or "",
				])
			if values != self.last_export_values:
				worksheet.clear()
				worksheet.update(values, "A1")
				from gspread.utils import ValidationConditionType
				worksheet.add_validation(
					"D2:D1000",
					ValidationConditionType.one_of_list,
					["Available", "Unavailable", "Reserved", "Late", "Missing"],
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
				"reservations.borrower, reservations.status, items.unavailable, items.checked_out_by, items.checkout_late "
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
					booking_status = "Late" if booking["checkout_late"] else "Checked out"
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
						"SELECT name, unavailable, missing, checked_out_by FROM items WHERE barcode = ?", (barcode,)
					).fetchone()
					if item is None:
						skipped_items.append(f"{barcode} (not found)")
					elif item["missing"] and borrower and not item["checked_out_by"]:
						skipped_items.append(f"{barcode} (marked missing; scan it before checkout)")
					elif item["checked_out_by"] is None and borrower and self.database.execute(
						"SELECT 1 FROM reservations WHERE barcode = ? AND reserved_date <= ?",
						(barcode, datetime.now().strftime("%Y-%m-%d")),
					).fetchone():
						skipped_items.append(f"{barcode} (use the Check Out button for its reservation)")
					elif item["checked_out_by"] and not borrower:
						self.database.execute(
							"UPDATE items SET checked_out_by = NULL, checked_out_at = NULL, checkout_due_at = NULL, checkout_late = 0, unavailable = 0 "
							"WHERE barcode = ?",
							(barcode,),
						)
						self.record_history(barcode, item["name"], "Checked in", item["checked_out_by"])
						checked_in_count += 1
						changed = True
					elif item["unavailable"]:
						if status == "available":
							self.database.execute(
								"UPDATE items SET unavailable = 0, missing = 0 WHERE barcode = ?", (barcode,)
							)
							availability_count += 1
							changed = True
						elif borrower:
							skipped_items.append(f"{barcode} (unavailable)")
					elif status == "unavailable":
						if item["checked_out_by"]:
							skipped_items.append(f"{barcode} (checked out)")
						else:
							self.database.execute(
								"UPDATE items SET unavailable = 1, missing = 0 WHERE barcode = ?", (barcode,)
							)
							availability_count += 1
							changed = True
					elif item["checked_out_by"] and not self.names_match(item["checked_out_by"], borrower):
						skipped_items.append(f"{barcode} (already checked out)")
					elif borrower and not item["checked_out_by"]:
						period = self.get_active_bell_period() if self.bell_schedule_enabled() else None
						if self.bell_schedule_enabled() and period is None:
							skipped_items.append(f"{barcode} (no active bell period)")
							continue
						timestamp = datetime.now().strftime("%Y-%m-%d %H:%M")
						due_timestamp = f"{period['period_date']} {period['end_time']}" if period else None
						self.database.execute(
							"UPDATE items SET checked_out_by = ?, checked_out_at = ?, checkout_due_at = ?, checkout_late = 0 WHERE barcode = ?",
							(borrower, timestamp, due_timestamp, barcode),
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
			"""CREATE TABLE IF NOT EXISTS bell_periods (
				id INTEGER PRIMARY KEY AUTOINCREMENT,
				period_date TEXT NOT NULL,
				period_name TEXT NOT NULL,
				start_time TEXT NOT NULL,
				end_time TEXT NOT NULL,
				UNIQUE(period_date, period_name)
			)"""
		)
		self.database.execute(
			"""CREATE TABLE IF NOT EXISTS accounts (
				id INTEGER PRIMARY KEY AUTOINCREMENT,
				full_name TEXT NOT NULL,
				student_id TEXT NOT NULL UNIQUE,
				email TEXT NOT NULL,
				phone TEXT NOT NULL,
				sms_opt_in INTEGER NOT NULL DEFAULT 0,
				created_at TEXT NOT NULL
			)"""
		)
		account_columns = {column[1] for column in self.database.execute("PRAGMA table_info(accounts)")}
		if "sms_opt_in" not in account_columns:
			self.database.execute("ALTER TABLE accounts ADD COLUMN sms_opt_in INTEGER NOT NULL DEFAULT 0")
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
		if "missing" not in columns:
			self.database.execute("ALTER TABLE items ADD COLUMN missing INTEGER NOT NULL DEFAULT 0")
		if "category" not in columns:
			self.database.execute("ALTER TABLE items ADD COLUMN category TEXT")
		if "checkout_due_at" not in columns:
			self.database.execute("ALTER TABLE items ADD COLUMN checkout_due_at TEXT")
		if "checkout_late" not in columns:
			self.database.execute("ALTER TABLE items ADD COLUMN checkout_late INTEGER NOT NULL DEFAULT 0")
		category_columns = {column[1] for column in self.database.execute("PRAGMA table_info(categories)")}
		if "sort_order" not in category_columns:
			self.database.execute("ALTER TABLE categories ADD COLUMN sort_order INTEGER NOT NULL DEFAULT 0")
			# Backfill existing categories (from before priorities existed) alphabetically.
			for index, row in enumerate(
				self.database.execute("SELECT name FROM categories ORDER BY name COLLATE NOCASE").fetchall()
			):
				self.database.execute("UPDATE categories SET sort_order = ? WHERE name = ?", (index, row["name"]))
		self.database.commit()

	def get_active_bell_period(self, current: datetime | None = None) -> sqlite3.Row | None:
		"""Return the bell period containing the current time, if one is configured."""
		current = current or datetime.now()
		periods = self.database.execute(
			"SELECT * FROM bell_periods WHERE period_date = ? ORDER BY start_time",
			(current.strftime("%Y-%m-%d"),),
		).fetchall()
		current_time = current.strftime("%H:%M")
		for period in periods:
			if period["start_time"] <= current_time < period["end_time"]:
				return period
		return None

	def bell_schedule_enabled(self) -> bool:
		"""Return whether bell periods control checkout expiration; enabled by default."""
		setting = self.database.execute(
			"SELECT value FROM settings WHERE key = 'bell_schedule_enabled'"
		).fetchone()
		return setting is None or setting["value"] != "0"

	def set_bell_schedule_enabled(self, enabled: bool) -> None:
		"""Enable or disable bell-period checkout rules."""
		if not self.admin_mode:
			return
		self.database.execute(
			"INSERT INTO settings (key, value) VALUES ('bell_schedule_enabled', ?) "
			"ON CONFLICT(key) DO UPDATE SET value = excluded.value",
			("1" if enabled else "0",),
		)
		if not enabled:
			self.database.execute(
				"UPDATE items SET checkout_due_at = NULL, checkout_late = 0 "
				"WHERE checked_out_by IS NOT NULL"
			)
		self.database.commit()

	def parse_bell_time(self, value: str) -> str | None:
		"""Convert a bell time to internal HH:MM, accepting common 12-hour and PDF-export formats."""
		if value is None:
			return None
		normalized = value.strip().upper()
		normalized = normalized.replace("A.M.", "AM").replace("P.M.", "PM")
		normalized = normalized.replace("A.M", "AM").replace("P.M", "PM")
		normalized = normalized.replace(".", "").replace("–", "-").replace("—", "-")
		normalized = normalized.replace(" TO ", " ").replace("TO", " ")
		normalized = normalized.replace("-", " ")
		normalized = re.sub(r"(?<=\d)(AM|PM)", r" \1", normalized)
		normalized = re.sub(r"\s+", " ", normalized).strip()
		variants = []
		if "AM" in normalized or "PM" in normalized:
			variants.append(normalized)
			variants.append(normalized.replace(" AM", "AM").replace(" PM", "PM"))
		else:
			variants.append(normalized)
		for candidate in variants:
			for time_format in ("%I:%M %p", "%I %p", "%H:%M", "%I:%M%p", "%H:%M%p"):
				try:
					return datetime.strptime(candidate, time_format).strftime("%H:%M")
				except ValueError:
					continue
		return None

	def format_bell_time(self, value: str) -> str:
		"""Display an internal HH:MM bell time using a 24-hour clock."""
		try:
			return datetime.strptime(value, "%H:%M").strftime("%H:%M")
		except ValueError:
			return value

	def checkout_time_display(self, row: sqlite3.Row) -> str:
		"""Format the checkout period for the item table."""
		if not row["checked_out_at"]:
			return ""
		if not row["checkout_due_at"]:
			return row["checked_out_at"]
		return f"{row['checked_out_at']} – {row['checkout_due_at']}"

	def send_checkout_expiry_email(
		self, recipient: str, subject: str, body: str, settings: dict[str, str]
	) -> bool:
		"""Send an overdue notice through the configured SMTP account."""
		if settings.get("checkout_email_enabled") != "1" or not recipient:
			return False
		password = self.get_notification_secret("smtp_password")
		if not password:
			raise RuntimeError("SMTP password is missing from Keychain")
		message = EmailMessage()
		message["Subject"] = subject
		message["From"] = settings["smtp_from_email"]
		message["To"] = recipient
		message.set_content(body)
		with smtplib.SMTP_SSL(
			settings["smtp_host"],
			int(settings["smtp_port"]),
			timeout=15,
		) as server:
			server.login(settings["smtp_username"], password)
			refused = server.send_message(message)
			if recipient in refused:
				raise RuntimeError(f"SMTP refused recipient {recipient}: {refused[recipient]}")
		return True

	def send_checkout_expiry_message(self, recipient: str, body: str, settings: dict[str, str]) -> bool:
		"""Send an overdue SMS through the configured Twilio account."""
		if settings.get("checkout_sms_enabled") != "1" or not recipient:
			return False
		account_sid = settings.get("twilio_account_sid", "")
		auth_token = self.get_notification_secret("twilio_auth_token")
		if not account_sid or not auth_token:
			raise RuntimeError("Twilio credentials are missing")
		endpoint = f"https://api.twilio.com/2010-04-01/Accounts/{account_sid}/Messages.json"
		request = Request(
			endpoint,
			data=urlencode({
				"To": recipient,
				"From": settings.get("twilio_from_number", ""),
				"Body": body,
			}).encode("utf-8"),
			method="POST",
			headers={
				"Authorization": "Basic " + base64.b64encode(
					f"{account_sid}:{auth_token}".encode("utf-8")
				).decode("ascii"),
				"Content-Type": "application/x-www-form-urlencoded",
			},
		)
		with urlopen(request, timeout=15) as response:
			if response.status not in (200, 201):
				raise RuntimeError(f"Twilio returned HTTP {response.status}")
		return True

	def notify_checkout_expired(
		self, borrower: str, item_name: str, due_at: str, email: str | None, phone: str | None,
		sms_opt_in: bool, settings: dict[str, str],
	) -> list[str]:
		"""Send the overdue checkout notice through the configured email/message hooks."""
		due_display = due_at
		try:
			due_display = datetime.strptime(due_at, "%Y-%m-%d %H:%M").strftime("%B %d at %I:%M %p").lstrip("0")
		except ValueError:
			pass
		subject = f"Equipment checkout expired: {item_name}"
		body = (
			f"Hello {borrower},\n\n"
			f"Your checkout of {item_name} ended at {due_display}. "
			"The item has been marked late because it was not returned by the end of the class period.\n\n"
			"Please contact the equipment desk if you still have the item."
		)
		sms_body = body + "\n\nReply STOP to opt out of text reminders."
		failures = []
		if settings.get("checkout_email_enabled") == "1" and email:
			try:
				self.send_checkout_expiry_email(email, subject, body, settings)
			except Exception as error:
				failures.append(f"email to {email}: {error}")
		if settings.get("checkout_sms_enabled") == "1" and sms_opt_in and phone:
			try:
				self.send_checkout_expiry_message(phone, sms_body, settings)
			except Exception as error:
				failures.append(f"SMS to {phone}: {error}")
		return failures

	def expire_due_checkouts(self) -> None:
		"""Mark overdue items late and notify borrowers, then schedule the next check."""
		if self.expiration_check_running:
			return
		self.expiration_check_running = True
		changed = False
		notifications = []
		notification_settings = self.get_checkout_notification_settings()
		now = datetime.now()
		now_text = now.strftime("%Y-%m-%d %H:%M")
		try:
			with self.db_lock:
				rows = self.database.execute(
					"SELECT barcode, name, checked_out_by, checkout_due_at FROM items "
					"WHERE checked_out_by IS NOT NULL AND checkout_due_at IS NOT NULL "
					"AND checkout_late = 0 "
					"AND checkout_due_at <= ?",
					(now_text,),
				).fetchall()
				for row in rows:
					accounts = self.database.execute(
						"SELECT email, phone, sms_opt_in FROM accounts WHERE full_name = ? COLLATE NOCASE",
						(row["checked_out_by"],),
					).fetchall()
					account = accounts[0] if len(accounts) == 1 else None
					notifications.append((
						row["checked_out_by"], row["name"], row["checkout_due_at"],
						account["email"] if account else None,
						account["phone"] if account else None,
						bool(account["sms_opt_in"]) if account else False,
						notification_settings,
					))
					self.database.execute(
						"UPDATE items SET checkout_late = 1 "
						"WHERE barcode = ? AND checked_out_by IS NOT NULL AND checkout_late = 0",
						(row["barcode"],),
					)
					self.record_history(row["barcode"], row["name"], "Marked late", row["checked_out_by"])
					self.mark_recently_changed(row["barcode"])
					changed = True
				if changed:
					self.database.commit()
			for notification in notifications:
				future = self.notification_executor.submit(self.notify_checkout_expired, *notification)
				future.add_done_callback(self.notification_delivery_finished)
			if changed:
				self.refresh_items()
				self.sync_to_google_sheets(show_result=False)
		finally:
			self.expiration_check_running = False
			self.root.after(30_000, self.expire_due_checkouts)

	def notification_delivery_finished(self, future) -> None:
		"""Report provider failures on the Tk thread after asynchronous delivery."""
		try:
			failures = future.result()
		except Exception as error:
			failures = [str(error)]
		if not failures:
			return
		message = "Late-item notice delivery failed: " + "; ".join(failures)
		logging.error(message)
		try:
			self.root.after(0, lambda: self.set_action_feedback(message, "error"))
		except tk.TclError:
			pass

	def choose_schedule_dates(
		self,
		parent: tk.Misc,
		title: str = "Choose schedule dates",
		instruction: str = "Click dates to select them. Select several dates for the same schedule.",
		continuous_from_today: bool = False,
	) -> set[str] | None:
		"""Let the user select one or more dates from a calendar."""
		dialog = tk.Toplevel(parent)
		dialog.title(title)
		dialog.resizable(True, False)
		dialog.transient(parent)
		dialog.grab_set()
		frame = ttk.Frame(dialog, padding=14)
		frame.grid()
		today = datetime.now()
		today_text = today.strftime("%Y-%m-%d")
		month_year = [today.year, today.month]
		selected_dates = {today_text}
		month_label = tk.StringVar()
		selection_label = tk.StringVar()
		calendar_frame = ttk.Frame(frame)
		calendar_frame.grid(row=1, column=0, columnspan=3, pady=(8, 0))

		def render_calendar() -> None:
			for child in calendar_frame.winfo_children():
				child.destroy()
			year, month = month_year
			month_label.set(f"{calendar.month_name[month]} {year}")
			for column, day_name in enumerate(calendar.day_abbr):
				ttk.Label(calendar_frame, text=day_name).grid(row=0, column=column, padx=4, pady=3)
			for row_number, week in enumerate(calendar.monthcalendar(year, month), start=1):
				for column, day in enumerate(week):
					if not day:
						tk.Label(calendar_frame, text="", width=4).grid(
							row=row_number, column=column, padx=2, pady=2
						)
						continue
					date_text = f"{year:04d}-{month:02d}-{day:02d}"
					is_selected = date_text in selected_dates
					is_before_today = continuous_from_today and date_text < today_text
					date_cell = tk.Label(
						calendar_frame, text=str(day), width=4, height=2,
						bg="#5b9bf7" if is_selected else "#eeeeee" if is_before_today else "#ffffff",
						fg="#888888" if is_before_today else "#000000",
						relief="solid" if is_selected else "flat", borderwidth=1,
					)
					date_cell.grid(row=row_number, column=column, padx=2, pady=2)
					if not is_before_today:
						date_cell.bind(
							"<Button-1>",
							lambda _event, value=date_text: toggle_date(value),
						)
			selection_label.set(f"{len(selected_dates)} date(s) selected")

		def toggle_date(date_text: str) -> None:
			if continuous_from_today:
				selected_dates.clear()
				current_date = today
				end_date = datetime.strptime(date_text, "%Y-%m-%d")
				while current_date.date() <= end_date.date():
					selected_dates.add(current_date.strftime("%Y-%m-%d"))
					current_date += timedelta(days=1)
				render_calendar()
				return
			if date_text in selected_dates and len(selected_dates) > 1:
				selected_dates.remove(date_text)
			else:
				selected_dates.add(date_text)
			render_calendar()

		def change_month(offset: int) -> None:
			month_year[1] += offset
			if month_year[1] == 0:
				month_year[1], month_year[0] = 12, month_year[0] - 1
			elif month_year[1] == 13:
				month_year[1], month_year[0] = 1, month_year[0] + 1
			render_calendar()

		tk.Button(frame, text="<", command=lambda: change_month(-1)).grid(row=0, column=0)
		ttk.Label(frame, textvariable=month_label, width=22, anchor="center").grid(row=0, column=1)
		tk.Button(frame, text=">", command=lambda: change_month(1)).grid(row=0, column=2)
		tk.Label(frame, text=instruction, foreground="#555555", wraplength=320).grid(
			row=2, column=0, columnspan=3, pady=(8, 2)
		)
		tk.Label(frame, textvariable=selection_label, foreground="#555555").grid(
			row=3, column=0, columnspan=3
		)
		result: list[set[str] | None] = [None]
		def use_dates() -> None:
			result[0] = set(selected_dates)
			dialog.destroy()
		ttk.Button(frame, text="Use selected dates", command=use_dates).grid(
			row=4, column=2, pady=(10, 0)
		)
		render_calendar()
		dialog.wait_window()
		return result[0]

	def manage_bell_schedule_dialog(self) -> None:
		"""Admin-only editor for bell periods that can vary by date."""
		if not self.admin_mode:
			return
		dialog = tk.Toplevel(self.root)
		dialog.title("Manage bell schedule")
		dialog.geometry("860x700")
		dialog.minsize(760, 620)
		dialog.transient(self.root)
		frame = ttk.Frame(dialog, padding=12)
		frame.pack(fill="both", expand=True)
		toggle_label = tk.StringVar()

		def refresh_toggle_label() -> None:
			toggle_label.set(
				"Disable Bell Schedule" if self.bell_schedule_enabled() else "Enable Bell Schedule"
			)

		def toggle_bell_schedule() -> None:
			enabled = self.bell_schedule_enabled()
			if enabled and not messagebox.askyesno(
				"Disable bell schedule",
				"Disable period-based checkout expiration? Current due and late flags will be cleared.",
				parent=dialog,
			):
				return
			self.set_bell_schedule_enabled(not enabled)
			refresh_toggle_label()
			self.refresh_items()
			if self.selected_barcode:
				row = self.database.execute(
					"SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)
				).fetchone()
				if row:
					self.show_item(row)

		ttk.Button(frame, textvariable=toggle_label, command=toggle_bell_schedule).pack(
			anchor="e", pady=(0, 8)
		)
		refresh_toggle_label()
		today = datetime.now()
		month_year = [today.year, today.month]
		selected_date = [today.strftime("%Y-%m-%d")]
		month_label = tk.StringVar()
		selected_date_label = tk.StringVar()
		calendar_frame = ttk.Frame(frame)
		calendar_frame.pack(fill="x")
		calendar_header = ttk.Frame(frame)
		calendar_header.pack(fill="x")
		tk.Button(calendar_header, text="<", command=lambda: change_month(-1)).pack(side="left")
		ttk.Label(calendar_header, textvariable=month_label, width=24, anchor="center").pack(side="left", expand=True)
		tk.Button(calendar_header, text=">", command=lambda: change_month(1)).pack(side="right")
		tk.Label(
			frame, text="Click a date to view its bell schedule. Highlighted dates have a schedule.",
			foreground="#555555",
		).pack(anchor="w", pady=(4, 8))
		table = ttk.Treeview(
			frame, columns=("date", "period", "start", "end"), show="headings", selectmode="browse"
		)
		for column, heading, width in (
			("date", "Date", 120), ("period", "Period", 180),
			("start", "Starts", 100), ("end", "Ends", 100),
		):
			table.heading(column, text=heading)
			table.column(column, width=width, anchor="w")
		table.pack(fill="both", expand=True, pady=(4, 0))

		def select_date(date_text: str) -> None:
			selected_date[0] = date_text
			reload_periods()
			render_calendar()

		def render_calendar() -> None:
			for child in calendar_frame.winfo_children():
				child.destroy()
			year, month = month_year
			month_label.set(f"{calendar.month_name[month]} {year}")
			scheduled_dates = {
				row["period_date"] for row in self.database.execute(
					"SELECT DISTINCT period_date FROM bell_periods"
				).fetchall()
			}
			for column, day_name in enumerate(calendar.day_abbr):
				ttk.Label(calendar_frame, text=day_name).grid(row=0, column=column, padx=8, pady=3)
			for row_number, week in enumerate(calendar.monthcalendar(year, month), start=1):
				for column, day in enumerate(week):
					if not day:
						tk.Label(calendar_frame, text="", width=7).grid(
							row=row_number, column=column, padx=3, pady=3
						)
						continue
					date_text = f"{year:04d}-{month:02d}-{day:02d}"
					is_selected = date_text == selected_date[0]
					has_schedule = date_text in scheduled_dates
					date_cell = tk.Label(
						calendar_frame,
						text=f"{day}\n●" if has_schedule else str(day),
						width=7, height=2,
						bg="#5b9bf7" if is_selected else "#fff0cc" if has_schedule else "#ffffff",
						fg="#000000", relief="solid" if is_selected else "flat", borderwidth=1,
					)
					date_cell.grid(row=row_number, column=column, padx=3, pady=3)
					date_cell.bind("<Button-1>", lambda _event, value=date_text: select_date(value))
			selected_date_label.set(f"Schedule for {selected_date[0]}")

		def change_month(offset: int) -> None:
			month_year[1] += offset
			if month_year[1] == 0:
				month_year[1], month_year[0] = 12, month_year[0] - 1
			elif month_year[1] == 13:
				month_year[1], month_year[0] = 1, month_year[0] + 1
			render_calendar()

		tk.Label(frame, textvariable=selected_date_label, font=("Segoe UI", 11, "bold")).pack(
			anchor="w", pady=(4, 0)
		)

		def reload_periods() -> None:
			for row_id in table.get_children():
				table.delete(row_id)
			for period in self.database.execute(
				"SELECT * FROM bell_periods WHERE period_date = ? ORDER BY start_time",
				(selected_date[0],),
			).fetchall():
				table.insert("", "end", iid=str(period["id"]), values=(
					period["period_date"], period["period_name"],
					self.format_bell_time(period["start_time"]), self.format_bell_time(period["end_time"]),
				))

		def period_values(existing: sqlite3.Row | None = None) -> tuple[str, str, str, str] | None:
			defaults = (
				existing["period_date"] if existing else datetime.now().strftime("%Y-%m-%d"),
				existing["period_name"] if existing else "Period 1",
				self.format_bell_time(existing["start_time"]) if existing else "08:00",
				self.format_bell_time(existing["end_time"]) if existing else "08:50",
			)
			values = []
			for label, default in zip(("Date (YYYY-MM-DD)", "Period name", "Start time (e.g. 08:00)", "End time (e.g. 08:50)"), defaults):
				value = simpledialog.askstring("Bell schedule", label, initialvalue=default, parent=dialog)
				if value is None:
					return None
				values.append(value.strip())
			try:
				datetime.strptime(values[0], "%Y-%m-%d")
				start_time = self.parse_bell_time(values[2])
				end_time = self.parse_bell_time(values[3])
			except ValueError:
				messagebox.showwarning("Invalid schedule", "Use dates as YYYY-MM-DD and times such as 08:00 or 13:30.", parent=dialog)
				return None
			if not start_time or not end_time:
				messagebox.showwarning("Invalid schedule", "Use times such as 08:00 or 13:30.", parent=dialog)
				return None
			if not values[1] or start_time >= end_time:
				messagebox.showwarning("Invalid schedule", "Enter a period name and make sure the end is after the start.", parent=dialog)
				return None
			return values[0], values[1], start_time, end_time

		def add_period() -> None:
			dates = self.choose_schedule_dates(dialog)
			if not dates:
				return
			period_name = simpledialog.askstring("Bell schedule", "Period name:", initialvalue="Period 1", parent=dialog)
			start_time = simpledialog.askstring("Bell schedule", "Start time (e.g. 08:00):", initialvalue="08:00", parent=dialog)
			end_time = simpledialog.askstring("Bell schedule", "End time (e.g. 08:50):", initialvalue="08:50", parent=dialog)
			if None in (period_name, start_time, end_time):
				return
			period_name, start_time, end_time = period_name.strip(), start_time.strip(), end_time.strip()
			start_time = self.parse_bell_time(start_time)
			end_time = self.parse_bell_time(end_time)
			if not start_time or not end_time:
				messagebox.showwarning("Invalid schedule", "Use times such as 08:00 or 13:30.", parent=dialog)
				return
			if not period_name or start_time >= end_time:
				messagebox.showwarning("Invalid schedule", "Enter a period name and make sure the end is after the start.", parent=dialog)
				return
			try:
				for period_date in sorted(dates):
					self.database.execute(
						"INSERT INTO bell_periods (period_date, period_name, start_time, end_time) VALUES (?, ?, ?, ?)",
						(period_date, period_name, start_time, end_time),
					)
				self.database.commit()
			except sqlite3.IntegrityError:
				self.database.rollback()
				messagebox.showwarning("Duplicate period", "That period name already exists for one of the selected dates.", parent=dialog)
				dialog.lift()
				return
			reload_periods()
			render_calendar()

		def edit_period() -> None:
			selection = table.selection()
			if not selection:
				return
			period = self.database.execute("SELECT * FROM bell_periods WHERE id = ?", (selection[0],)).fetchone()
			values = period_values(period)
			if values is None:
				return
			try:
				self.database.execute(
					"UPDATE bell_periods SET period_date = ?, period_name = ?, start_time = ?, end_time = ? WHERE id = ?",
					(*values, period["id"]),
				)
				self.database.commit()
			except sqlite3.IntegrityError:
				messagebox.showwarning("Duplicate period", "That period name already exists for this date.", parent=dialog)
				dialog.lift()
				return
			reload_periods()
			render_calendar()

		def delete_period() -> None:
			selection = table.selection()
			if selection and messagebox.askyesno("Delete period", "Delete the selected bell period?", parent=dialog):
				self.database.execute("DELETE FROM bell_periods WHERE id = ?", (selection[0],))
				self.database.commit()
				reload_periods()
				render_calendar()

		def copy_schedule() -> None:
			periods = self.database.execute(
				"SELECT period_name, start_time, end_time FROM bell_periods "
				"WHERE period_date = ? ORDER BY start_time",
				(selected_date[0],),
			).fetchall()
			if not periods:
				messagebox.showinfo(
					"No schedule to copy",
					f"There is no bell schedule saved for {selected_date[0]}.",
					parent=dialog,
				)
				return
			target_dates = self.choose_schedule_dates(dialog)
			if not target_dates:
				return
			target_dates.discard(selected_date[0])
			if not target_dates:
				messagebox.showinfo(
					"Choose another date", "Select at least one date besides the source schedule.", parent=dialog
				)
				return
			if not messagebox.askyesno(
				"Copy bell schedule",
				f"Copy the {len(periods)} period(s) from {selected_date[0]} to "
				f"{len(target_dates)} date(s)? Existing schedules on those dates will be replaced.",
				parent=dialog,
			):
				return
			with self.db_lock:
				for target_date in sorted(target_dates):
					self.database.execute("DELETE FROM bell_periods WHERE period_date = ?", (target_date,))
					for period in periods:
						self.database.execute(
							"INSERT INTO bell_periods (period_date, period_name, start_time, end_time) "
							"VALUES (?, ?, ?, ?)",
							(target_date, period["period_name"], period["start_time"], period["end_time"]),
						)
				self.database.commit()
			reload_periods()
			render_calendar()

		buttons = ttk.Frame(frame)
		buttons.pack(fill="x", pady=(8, 0))
		self.bell_schedule_refresh_callback = lambda: (reload_periods(), render_calendar())

		def close_schedule_dialog() -> None:
			self.bell_schedule_refresh_callback = None
			dialog.destroy()

		left_buttons = ttk.Frame(buttons)
		left_buttons.pack(side="left")
		ttk.Button(left_buttons, text="Add period", command=add_period).pack(side="left")
		ttk.Button(
			left_buttons, text="Import Downloaded Schedule",
			command=lambda: self.import_bell_schedule_from_file(True),
		).pack(side="left", padx=(8, 0))
		ttk.Button(left_buttons, text="Copy Schedule", command=copy_schedule).pack(side="left", padx=(8, 0))
		ttk.Button(left_buttons, text="Edit", command=edit_period).pack(side="left", padx=(8, 0))
		ttk.Button(left_buttons, text="Delete", command=delete_period).pack(side="left", padx=(8, 0))
		ttk.Button(buttons, text="Close", command=close_schedule_dialog).pack(side="right")
		render_calendar()
		reload_periods()

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

	def get_booking_dates(self, barcode: str, borrower: str, created_at: str) -> set[str]:
		"""Return the dates for one calendar booking selection for this item and borrower."""
		rows = self.database.execute(
			"SELECT reserved_date, borrower FROM reservations "
			"WHERE barcode = ? AND created_at = ? AND status = 'Confirmed'",
			(barcode, created_at),
		).fetchall()
		return {
			row["reserved_date"]
			for row in rows
			if self.names_match(row["borrower"], borrower)
		}

	def booking_is_recent(self, created_at: str) -> bool:
		"""Return whether a recent booking can still be deleted without admin access."""
		for format_text in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M"):
			try:
				created_time = datetime.strptime(created_at, format_text)
				return (datetime.now() - created_time).total_seconds() <= BOOKING_DELETE_GRACE_SECONDS
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
		if hasattr(self, "default_bg"):
			self.apply_admin_background(self.admin_mode)
		if hasattr(self, "admin_status"):
			self.admin_status.set("Admin mode" if self.admin_mode else "Normal mode")
		if hasattr(self, "admin_button"):
			self.admin_button.configure(text="Leave Admin Mode" if self.admin_mode else "Enter Admin Mode")

		admin_only_buttons = []
		for attr_name in (
			"add_button", "edit_button", "photo_button",
			"unavailable_button", "delete_button", "history_button",
			"category_button", "export_button", "manage_accounts_button",
			"bell_schedule_button", "notification_settings_button", "web_api_settings_button",
		):
			button = getattr(self, attr_name, None)
			if button is not None:
				admin_only_buttons.append(button)
		for button in admin_only_buttons:
			if self.admin_mode:
				button.grid()
			else:
				button.grid_remove()

		if self.admin_mode:
			for attr_name in (
				"add_button", "edit_button", "photo_button",
				"unavailable_button", "delete_button", "history_button",
				"category_button", "export_button", "manage_accounts_button",
				"bell_schedule_button", "notification_settings_button", "web_api_settings_button",
			):
				button = getattr(self, attr_name, None)
				if button is not None:
					button.state(["!disabled"])
			for attr_name in ("edit_button", "photo_button", "unavailable_button", "delete_button"):
				button = getattr(self, attr_name, None)
				if button is not None:
					button.state(["!disabled"] if len(self.multi_scan_queue) == 1 else ["disabled"])
		checked_out_selection = any(
			self.database.execute(
				"SELECT 1 FROM items WHERE barcode = ? AND checked_out_by IS NOT NULL",
				(barcode,),
			).fetchone()
			for barcode in self.multi_scan_queue
		)
		if hasattr(self, "checkout_button"):
			if checked_out_selection:
				self.checkout_button.grid_remove()
			else:
				self.checkout_button.grid()
				self.checkout_button.configure(state="normal")
		if hasattr(self, "checkin_button"):
			if checked_out_selection:
				self.checkin_button.grid()
			else:
				self.checkin_button.grid_remove()
		if hasattr(self, "book_button"):
			self.book_button.state(["!disabled"] if self.multi_scan_queue else ["disabled"])
		if self.selected_barcode and hasattr(self, "unavailable_button"):
			row = self.database.execute(
				"SELECT unavailable FROM items WHERE barcode = ?", (self.selected_barcode,)
			).fetchone()
			self.unavailable_button.configure(text="Mark Available" if row and row["unavailable"] else "Mark Unavailable")
		if hasattr(self, "selection_status"):
			count = len(self.multi_scan_queue)
			self.selection_status.set(f"{count} selected" if count else "No items selected")

	def get_notification_secret(self, key: str) -> str | None:
		"""Read a provider secret from the macOS Keychain via keyring."""
		import keyring
		return keyring.get_password(NOTIFICATION_KEYRING_SERVICE, key)

	def set_notification_secret(self, key: str, value: str) -> None:
		"""Store a provider secret in the macOS Keychain via keyring."""
		import keyring
		keyring.set_password(NOTIFICATION_KEYRING_SERVICE, key, value)

	def web_api_settings_dialog(self) -> None:
		"""Configure and verify the hosted inventory API from admin mode."""
		if not self.admin_mode:
			return
		dialog = tk.Toplevel(self.root)
		dialog.title("Web inventory sync")
		dialog.transient(self.root)
		dialog.grab_set()
		frame = ttk.Frame(dialog, padding=16)
		frame.grid(sticky="nsew")
		frame.columnconfigure(1, weight=1)
		url = tk.StringVar(value=self.web_api_base_url)
		email = tk.StringVar(value=self.web_api_email)
		workspace = tk.StringVar()
		status = tk.StringVar(value="Test the connection before saving.")
		workspaces: dict[str, str] = {}
		tested: dict[str, object] = {}
		password_entry = ttk.Entry(frame, show="*", width=42)
		password_entry.insert(0, self.web_api_password)
		workspace_picker = ttk.Combobox(frame, textvariable=workspace, state="readonly", width=39)
		row = 0
		for label, variable in (("API server URL", url), ("Account email", email)):
			ttk.Label(frame, text=label + ":").grid(row=row, column=0, sticky="w", padx=(0, 10), pady=5)
			ttk.Entry(frame, textvariable=variable, width=42).grid(row=row, column=1, sticky="ew", pady=5)
			row += 1
		ttk.Label(frame, text="Account password:").grid(row=row, column=0, sticky="w", padx=(0, 10), pady=5)
		password_entry.grid(row=row, column=1, sticky="ew", pady=5)
		row += 1
		ttk.Label(frame, text="Inventory workspace:").grid(row=row, column=0, sticky="w", padx=(0, 10), pady=5)
		workspace_picker.grid(row=row, column=1, sticky="ew", pady=5)
		row += 1
		ttk.Label(frame, textvariable=status, wraplength=440).grid(
			row=row, column=0, columnspan=2, sticky="w", pady=(8, 10)
		)
		row += 1
		buttons = ttk.Frame(frame)
		buttons.grid(row=row, column=0, columnspan=2, sticky="ew")
		test_button = ttk.Button(buttons, text="Test connection")
		test_button.pack(side="left")
		save_button = ttk.Button(buttons, text="Save and sync", state="disabled")
		save_button.pack(side="left", padx=(8, 0))
		ttk.Button(buttons, text="Cancel", command=dialog.destroy).pack(side="right")

		def show_login_error(message: str) -> None:
			status.set(f"Connection failed: {message}")
			test_button.state(["!disabled"])

		def show_login_result(base_url: str, account_email: str, account_password: str, result: dict) -> None:
			available = result.get("inventories", [])
			if not available and result.get("inventory_id") is not None:
				available = [{"id": result["inventory_id"], "name": "Inventory", "role": "owner"}]
			if not available:
				show_login_error("This account does not have an inventory workspace.")
				return
			workspaces.clear()
			labels = []
			for inventory in available:
				label = f"{inventory['name']} (ID {inventory['id']})"
				workspaces[label] = str(inventory["id"])
				labels.append(label)
			workspace_picker.configure(values=labels)
			workspace.set(next(
				(label for label in labels if workspaces[label] == str(self.web_api_inventory_id)), labels[0]
			))
			tested.clear()
			tested.update({"url": base_url, "email": account_email, "password": account_password, "result": result})
			status.set(f"Connected as {result.get('email', account_email)}. Choose the inventory and save.")
			test_button.state(["!disabled"])
			save_button.state(["!disabled"])

		def test_connection() -> None:
			base_url = url.get().strip().rstrip("/")
			account_email = email.get().strip()
			account_password = password_entry.get() or self.web_api_password
			parsed_url = urlsplit(base_url)
			if parsed_url.scheme not in {"http", "https"} or not parsed_url.netloc:
				messagebox.showwarning("Invalid API URL", "Enter a complete http:// or https:// server URL.", parent=dialog)
				return
			if not account_email or not account_password:
				messagebox.showwarning("Account details required", "Enter the web account email and password.", parent=dialog)
				return
			test_button.state(["disabled"])
			save_button.state(["disabled"])
			status.set("Connecting and checking available inventories...")

			def request_login() -> None:
				try:
					request = Request(
						f"{base_url}/api/auth/login",
						data=json.dumps({"email": account_email, "password": account_password}).encode("utf-8"),
						headers={"Content-Type": "application/json", "Accept": "application/json"},
						method="POST",
					)
					with urlopen(request, timeout=20) as response:
						result = json.loads(response.read().decode("utf-8"))
					self.root.after(0, show_login_result, base_url, account_email, account_password, result)
				except Exception as error:
					message = str(error)
					if hasattr(error, "read"):
						try:
							details = json.loads(error.read().decode("utf-8"))
							message = details.get("detail", message)
						except Exception:
							pass
					self.root.after(0, show_login_error, message)

			threading.Thread(target=request_login, daemon=True).start()

		def save_and_sync() -> None:
			base_url = url.get().strip().rstrip("/")
			account_email = email.get().strip()
			account_password = password_entry.get() or self.web_api_password
			selected_workspace = workspaces.get(workspace.get())
			if not tested or (tested.get("url"), tested.get("email"), tested.get("password")) != (
				base_url, account_email, account_password
			):
				messagebox.showwarning("Test required", "Test the current server and account before saving.", parent=dialog)
				return
			if not selected_workspace:
				messagebox.showwarning("Choose an inventory", "Select the inventory this app should sync with.", parent=dialog)
				return
			try:
				self.set_notification_secret("web_api_password", account_password)
			except Exception as error:
				messagebox.showerror("Keychain unavailable", f"Could not save the API password securely: {error}", parent=dialog)
				return
			self.set_setting("web_api_base_url", base_url)
			self.set_setting("web_api_email", account_email)
			self.set_setting("web_api_inventory_id", selected_workspace)
			self.web_api_base_url = base_url
			self.web_api_email = account_email
			self.web_api_password = account_password
			self.web_api_inventory_id = selected_workspace
			login_result = tested["result"]
			self.web_api_token = login_result["token"]
			self.start_web_service_sync_cycle()
			threading.Thread(target=self.sync_to_web_service, args=(False,), daemon=True).start()
			if not self.web_api_poll_started:
				self.web_api_poll_started = True
				self.root.after(3_000, self.poll_web_service)
			status.set("Settings saved. The desktop app is syncing with this inventory.")
			dialog.after(800, dialog.destroy)

		test_button.configure(command=test_connection)
		save_button.configure(command=save_and_sync)
		dialog.bind("<Return>", lambda _event: test_connection())

	def get_checkout_notification_settings(self) -> dict[str, str]:
		"""Read one consistent provider configuration snapshot under the DB lock."""
		keys = (
			"checkout_email_enabled", "smtp_host", "smtp_port", "smtp_username", "smtp_from_email",
			"checkout_sms_enabled", "twilio_account_sid", "twilio_from_number",
		)
		with self.db_lock:
			rows = self.database.execute(
				"SELECT key, value FROM settings WHERE key IN (" + ",".join("?" for _ in keys) + ")",
				keys,
			).fetchall()
		settings = {row["key"]: row["value"] for row in rows}
		settings.setdefault("smtp_port", "465")
		return settings

	def notification_settings_dialog(self) -> None:
		"""Configure email and Twilio notices; provider secrets are stored in Keychain."""
		if not self.admin_mode:
			return
		dialog = tk.Toplevel(self.root)
		dialog.title("Overdue notification settings")
		dialog.transient(self.root)
		dialog.grab_set()
		frame = ttk.Frame(dialog, padding=16)
		frame.grid(sticky="nsew")

		email_enabled = tk.BooleanVar(value=self.get_setting("checkout_email_enabled") == "1")
		sms_enabled = tk.BooleanVar(value=self.get_setting("checkout_sms_enabled") == "1")
		settings = {
			"SMTP host": tk.StringVar(value=self.get_setting("smtp_host", "smtp.gmail.com")),
			"SMTP port": tk.StringVar(value=self.get_setting("smtp_port", "465")),
			"SMTP username": tk.StringVar(value=self.get_setting("smtp_username")),
			"From email": tk.StringVar(value=self.get_setting("smtp_from_email")),
			"Twilio account SID": tk.StringVar(value=self.get_setting("twilio_account_sid")),
			"Twilio from number": tk.StringVar(value=self.get_setting("twilio_from_number")),
		}
		row = 0
		ttk.Checkbutton(frame, text="Send overdue email notices", variable=email_enabled).grid(
			row=row, column=0, columnspan=2, sticky="w", pady=(0, 8)
		)
		row += 1
		for label in ("SMTP host", "SMTP port", "SMTP username", "From email"):
			ttk.Label(frame, text=label + ":").grid(row=row, column=0, sticky="w", padx=(0, 10), pady=3)
			ttk.Entry(frame, textvariable=settings[label], width=38).grid(row=row, column=1, sticky="ew", pady=3)
			row += 1
		ttk.Label(frame, text="SMTP password:").grid(row=row, column=0, sticky="w", padx=(0, 10), pady=3)
		ttk.Entry(frame, show="*", width=38).grid(row=row, column=1, sticky="ew", pady=3)
		smtp_password_entry = frame.grid_slaves(row=row, column=1)[0]
		row += 1
		ttk.Label(frame, text="Leave password blank to keep the saved Keychain value.", foreground="#555555").grid(
			row=row, column=1, sticky="w", pady=(0, 8)
		)
		row += 1
		ttk.Checkbutton(
			frame,
			text="Send SMS notices (only to borrowers who opted in)",
			variable=sms_enabled,
		).grid(row=row, column=0, columnspan=2, sticky="w", pady=(4, 8))
		row += 1
		for label in ("Twilio account SID", "Twilio from number"):
			ttk.Label(frame, text=label + ":").grid(row=row, column=0, sticky="w", padx=(0, 10), pady=3)
			ttk.Entry(frame, textvariable=settings[label], width=38).grid(row=row, column=1, sticky="ew", pady=3)
			row += 1
		ttk.Label(frame, text="Twilio auth token:").grid(row=row, column=0, sticky="w", padx=(0, 10), pady=3)
		twilio_token_entry = ttk.Entry(frame, show="*", width=38)
		twilio_token_entry.grid(row=row, column=1, sticky="ew", pady=3)
		row += 1
		ttk.Label(frame, text="Leave token blank to keep the saved Keychain value.", foreground="#555555").grid(
			row=row, column=1, sticky="w", pady=(0, 8)
		)
		row += 1

		def save() -> None:
			try:
				port = int(settings["SMTP port"].get().strip())
			except ValueError:
				messagebox.showwarning("Invalid SMTP port", "Enter an SMTP port from 1 to 65535.", parent=dialog)
				return
			if not 1 <= port <= 65535:
				messagebox.showwarning("Invalid SMTP port", "Enter an SMTP port from 1 to 65535.", parent=dialog)
				return
			smtp_password = smtp_password_entry.get().strip()
			twilio_token = twilio_token_entry.get().strip()
			try:
				saved_smtp_password = self.get_notification_secret("smtp_password")
				saved_twilio_token = self.get_notification_secret("twilio_auth_token")
				if email_enabled.get() and not (
					settings["SMTP host"].get().strip()
					and settings["SMTP username"].get().strip()
					and settings["From email"].get().strip()
					and (smtp_password or saved_smtp_password)
				):
					messagebox.showwarning(
						"Email settings incomplete", "Enter SMTP host, username, sender address, and password.", parent=dialog
					)
					return
				if sms_enabled.get() and not (
					settings["Twilio account SID"].get().strip()
					and settings["Twilio from number"].get().strip()
					and (twilio_token or saved_twilio_token)
				):
					messagebox.showwarning(
						"SMS settings incomplete", "Enter the Twilio SID, sending number, and auth token.", parent=dialog
					)
					return
				if smtp_password:
					self.set_notification_secret("smtp_password", smtp_password)
				if twilio_token:
					self.set_notification_secret("twilio_auth_token", twilio_token)
			except Exception as error:
				messagebox.showerror("Keychain error", f"Could not access the macOS Keychain: {error}", parent=dialog)
				return
			for label, key in (
				("SMTP host", "smtp_host"),
				("SMTP username", "smtp_username"),
				("From email", "smtp_from_email"),
				("Twilio account SID", "twilio_account_sid"),
				("Twilio from number", "twilio_from_number"),
			):
				self.set_setting(key, settings[label].get().strip())
			self.set_setting("smtp_port", str(port))
			self.set_setting("checkout_email_enabled", "1" if email_enabled.get() else "0")
			self.set_setting("checkout_sms_enabled", "1" if sms_enabled.get() else "0")
			dialog.destroy()
			self.set_action_feedback("Overdue notification settings saved.", "success")

		ttk.Button(frame, text="Save settings", command=save).grid(row=row, column=1, sticky="e", pady=(8, 0))
		dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)

	def choose_audit_categories(self) -> tuple[bool, set[str] | None]:
		"""Ask which item categories should be included, or return None for all."""
		category_names = self.get_categories()
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
		all_categories = tk.BooleanVar(value=False)
		category_values = {name: tk.BooleanVar(value=False) for name in category_names}
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
				category_labels = {name.casefold(): name for name in self.get_categories()}
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
		scanned_barcodes = set(self.audit_items_scanned)
		status_changed = False
		with self.db_lock:
			audit_rows = self.database.execute(
				"SELECT barcode, name, category, checked_out_by, unavailable, missing FROM items"
			).fetchall()
			for row in audit_rows:
				if not self.audit_item_is_in_scope(row):
					continue
				is_missing = (
					row["barcode"] not in scanned_barcodes
					and not row["checked_out_by"]
					and not row["unavailable"]
				)
				if bool(row["missing"]) != is_missing:
					self.database.execute(
						"UPDATE items SET missing = ? WHERE barcode = ?",
						(int(is_missing), row["barcode"]),
					)
					status_changed = True
			if status_changed:
				self.database.commit()
		
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
				checked_out_items = []
				unavailable_items = []
				for row in audit_rows:
					if not self.audit_item_is_in_scope(row):
						continue
					if row["barcode"] not in self.audit_items_scanned:
						if row["checked_out_by"]:
							checked_out_items.append(
								f"- {row['name']} ({row['barcode']}) ({row['checked_out_by']})"
							)
						elif row["unavailable"]:
							unavailable_items.append(f"- {row['name']} ({row['barcode']})")
						else:
							missing_items.append(f"- {row['name']} ({row['barcode']})")

				if len(missing_items) > 0:
					message += f"⚠️ Missing {len(missing_items)} items:\n\n"
					message += "\n".join(missing_items[:20])
					if len(missing_items) > 20:
						message += f"\n... and {len(missing_items) - 20} more."
				if checked_out_items:
					message += f"\n\nNot scanned (checked out: {len(checked_out_items)}):\n\n"
					message += "\n".join(checked_out_items[:20])
					if len(checked_out_items) > 20:
						message += f"\n... and {len(checked_out_items) - 20} more."
				if unavailable_items:
					message += f"\n\nNot scanned (unavailable: {len(unavailable_items)}):\n\n"
					message += "\n".join(unavailable_items[:20])
					if len(unavailable_items) > 20:
						message += f"\n... and {len(unavailable_items) - 20} more."
				
				if scanned_count > total_expected:
					message += f"\n\n❓ Note: You also scanned {scanned_count - total_expected} extra items."
		else:
			message += "No items were found in the database to audit."

		messagebox.showinfo("Audit Report", message)
		if status_changed:
			self.refresh_items()
			if self.selected_barcode:
				selected_row = self.database.execute(
					"SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)
				).fetchone()
				if selected_row:
					self.show_item(selected_row)
			self.sync_to_google_sheets(show_result=False)
		
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
		dialog.geometry("900x460")
		dialog.transient(self.root)
		frame = ttk.Frame(dialog, padding=12)
		frame.pack(fill="both", expand=True)
		filter_frame = ttk.Frame(frame)
		filter_frame.pack(fill="x", pady=(0, 8))
		filter_frame.columnconfigure(1, weight=1)
		search_value = tk.StringVar()
		checked_out_only = tk.BooleanVar(value=False)
		ttk.Label(filter_frame, text="Search:").grid(row=0, column=0, padx=(0, 8))
		search_entry = ttk.Entry(filter_frame, textvariable=search_value)
		search_entry.grid(row=0, column=1, sticky="ew", padx=(0, 12))
		columns = ("time", "action", "barcode", "item", "borrower")
		table = ttk.Treeview(frame, columns=columns, show="headings")
		table.tag_configure("checked_out", background="#ffd9d9", foreground="#9b1c1c")
		table.tag_configure("checked_in", background="#dff4df", foreground="#176b2c")
		def refresh_history(*_args) -> None:
			for row_id in table.get_children():
				table.delete(row_id)
			conditions = []
			parameters = []
			query = search_value.get().strip()
			if query:
				conditions.append(
					"(timestamp || ' ' || action || ' ' || barcode || ' ' || item_name || ' ' || "
					"COALESCE(borrower, '')) LIKE ?"
				)
				parameters.append(f"%{query}%")
			if checked_out_only.get():
				conditions.append(
					"EXISTS (SELECT 1 FROM items WHERE items.barcode = checkout_history.barcode "
					"AND items.checked_out_by IS NOT NULL)"
				)
			where_clause = " WHERE " + " AND ".join(conditions) if conditions else ""
			rows = self.database.execute(
				"SELECT timestamp, action, barcode, item_name, borrower "
				"FROM checkout_history" + where_clause + " ORDER BY id DESC",
				parameters,
			).fetchall()
			for row in rows:
				tag = "checked_out" if row["action"] == "Checked out" else (
					"checked_in" if row["action"] == "Checked in" else ""
				)
				table.insert("", "end", values=(
					row["timestamp"], row["action"], row["barcode"],
					row["item_name"], row["borrower"] or "",
			), tags=(tag,) if tag else ())

		search_value.trace_add("write", refresh_history)
		ttk.Checkbutton(
			filter_frame, text="Only items currently checked out", variable=checked_out_only,
			command=refresh_history,
		).grid(row=0, column=2, sticky="e")
		headings = {
			"time": "Time", "action": "Action", "barcode": "Barcode",
			"item": "Item", "borrower": "Borrower / returned by",
		}
		widths = {"time": 140, "action": 110, "barcode": 140, "item": 190, "borrower": 190}
		for column in columns:
			table.heading(column, text=headings[column])
			table.column(column, width=widths[column], anchor="w")
		table.pack(side="left", fill="both", expand=True)
		scrollbar = ttk.Scrollbar(frame, orient="vertical", command=table.yview)
		scrollbar.pack(side="right", fill="y")
		table.configure(yscrollcommand=scrollbar.set)
		refresh_history()

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
		"""Prompt for and resolve the borrower's account before checkout."""
		dialog = tk.Toplevel(parent)
		dialog.title("Check Out")
		dialog.transient(parent)
		dialog.grab_set()
		dialog.resizable(False, False)
		frame = ttk.Frame(dialog, padding=16)
		frame.grid(sticky="ew")
		frame.columnconfigure(0, weight=1)
		tk.Label(frame, text="Enter your name or student ID:").grid(
			row=0, column=0, sticky="w", pady=(0, 6)
		)
		name_query = tk.StringVar(value=self.borrower_name.get().strip())
		name_entry = ttk.Entry(frame, textvariable=name_query, width=34)
		name_entry.grid(row=1, column=0, columnspan=2, sticky="ew")
		result: list[str | None] = [None]

		def continue_checkout() -> None:
			value = name_query.get().strip()
			if not value:
				messagebox.showwarning("Name required", "Enter your name or student ID.", parent=dialog)
				name_entry.focus_set()
				return
			result[0] = value
			dialog.destroy()

		def open_signup() -> None:
			dialog.destroy()
			self.signup_dialog()
			self.set_action_feedback("Create your account, then click Check Out again.", "neutral")

		ttk.Button(
			frame,
			text="Haven't made an account? Sign Up",
			command=open_signup,
		).grid(row=2, column=0, sticky="w", pady=(10, 0))
		tk.Button(frame, text="Continue", command=continue_checkout).grid(
			row=2, column=1, sticky="e", padx=(12, 0), pady=(10, 0)
		)
		dialog.bind("<Return>", lambda _event: continue_checkout())
		dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
		name_entry.focus_set()
		dialog.wait_window()
		if result[0] is None:
			return None
		name_value = result[0]
		accounts = self.find_accounts(name_value)
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
		sms_opt_in = tk.BooleanVar(value=False)
		entries = []
		for row_number, (label, value) in enumerate(fields):
			ttk.Label(frame, text=f"{label}:").grid(row=row_number, column=0, sticky="w", padx=(0, 10), pady=4)
			entry = ttk.Entry(frame, textvariable=value, width=34)
			entry.grid(row=row_number, column=1, pady=4)
			entries.append(entry)
		ttk.Checkbutton(
			frame,
			text="I agree to one SMS when borrowed equipment becomes overdue. Msg/data rates may apply; reply STOP to opt out.",
			variable=sms_opt_in,
		).grid(row=len(fields), column=0, columnspan=2, sticky="w", pady=(6, 0))

		def save() -> None:
			values = [value.get().strip() for _, value in fields]
			if not all(values):
				messagebox.showwarning("Missing information", "Enter a name, student ID, email, and phone number.", parent=dialog)
				return
			try:
				self.database.execute(
					"INSERT INTO accounts (full_name, student_id, email, phone, sms_opt_in, created_at) "
					"VALUES (?, ?, ?, ?, ?, ?)",
					(*values, int(sms_opt_in.get()), datetime.now().strftime("%Y-%m-%d %H:%M:%S")),
				)
				self.database.commit()
			except sqlite3.IntegrityError:
				messagebox.showwarning("Student ID already registered", "That student ID already has an account.", parent=dialog)
				return
			dialog.destroy()
			messagebox.showinfo("Account created", f"Account created for {values[0]}.", parent=self.root)

		ttk.Button(frame, text="Create account", command=save).grid(row=len(fields) + 1, column=1, sticky="e", pady=(12, 0))
		entries[0].focus_set()

	def manage_accounts_dialog(self) -> None:
		"""Admin-only account list with edit and delete controls."""
		if not self.admin_mode:
			return
		dialog = tk.Toplevel(self.root)
		dialog.title("Manage accounts")
		dialog.geometry("900x400")
		dialog.transient(self.root)
		frame = ttk.Frame(dialog, padding=12)
		frame.pack(fill="both", expand=True)
		columns = ("name", "student_id", "email", "phone", "sms_opt_in")
		table = ttk.Treeview(frame, columns=columns, show="headings", selectmode="browse")
		for column, heading, width in (
			("name", "Name", 180), ("student_id", "Student ID", 120),
			("email", "Email", 220), ("phone", "Phone", 130), ("sms_opt_in", "SMS reminders", 120),
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
					"Yes" if account["sms_opt_in"] else "No",
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
			sms_opt_in = tk.BooleanVar(value=bool(account["sms_opt_in"]))
			edit_frame = ttk.Frame(edit_dialog, padding=16)
			edit_frame.grid()
			entries = []
			for row_number, (label, value) in enumerate(fields):
				ttk.Label(edit_frame, text=f"{label}:").grid(row=row_number, column=0, sticky="w", padx=(0, 10), pady=4)
				entry = ttk.Entry(edit_frame, textvariable=value, width=34)
				entry.grid(row=row_number, column=1, pady=4)
				entries.append(entry)
			ttk.Checkbutton(
				edit_frame,
				text="Borrower agreed to SMS overdue reminders",
				variable=sms_opt_in,
			).grid(row=len(fields), column=0, columnspan=2, sticky="w", pady=(6, 0))

			def save_changes() -> None:
				values = [value.get().strip() for _, value in fields]
				if not all(values):
					messagebox.showwarning("Missing information", "All account fields are required.", parent=edit_dialog)
					return
				try:
					self.database.execute(
						"UPDATE accounts SET full_name = ?, student_id = ?, email = ?, phone = ?, "
						"sms_opt_in = ? WHERE id = ?",
						(*values, int(sms_opt_in.get()), account["id"]),
					)
					self.database.commit()
				except sqlite3.IntegrityError:
					messagebox.showwarning("Student ID already registered", "That student ID already has an account.", parent=edit_dialog)
					return
				edit_dialog.destroy()
				reload_accounts()

			ttk.Button(edit_frame, text="Save changes", command=save_changes).grid(
				row=len(fields) + 1, column=1, sticky="e", pady=(12, 0)
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
		"""Build the main window with global actions above a selectable inventory list."""
		style = ttk.Style(self.root)
		self.default_bg = style.lookup("TFrame", "background") or self.root.cget("bg")
		self.root.columnconfigure(0, weight=1)
		self.root.rowconfigure(4, weight=1)

		header = ttk.Frame(self.root, padding=(20, 18, 20, 8))
		header.grid(row=0, column=0, sticky="ew")
		header.columnconfigure(0, weight=1)
		ttk.Label(header, text="Equipment Check-In System", font=("Segoe UI", 18, "bold")).grid(
			row=0, column=0, sticky="w"
		)
		ttk.Label(header, text="Scan an item or select it below, then choose an action.").grid(
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
		self.bell_schedule_button = ttk.Button(
			header, text="Bell Schedule", command=self.manage_bell_schedule_dialog, state="disabled"
		)
		self.bell_schedule_button.grid(row=0, column=8, rowspan=2, padx=(8, 0))

		scan_frame = ttk.LabelFrame(self.root, text="Scan item", padding=14)
		scan_frame.grid(row=1, column=0, padx=20, pady=8, sticky="ew")
		scan_frame.columnconfigure(0, weight=1)
		self.scan_entry = ttk.Entry(scan_frame, textvariable=self.scan_value, font=("Segoe UI", 14))
		self.scan_entry.grid(row=0, column=0, sticky="ew", padx=(0, 8))
		self.scan_entry.bind("<Return>", self.scan_item)
		ttk.Button(scan_frame, text="Scan / Find", command=self.scan_item).grid(row=0, column=1)

		self.audit_frame = ttk.LabelFrame(self.root, text="Inventory Audit", padding=14)
		self.audit_frame.grid(row=2, column=0, padx=20, pady=8, sticky="ew")
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

		actions = ttk.Frame(self.root, padding=(20, 4, 20, 8))
		actions.grid(row=3, column=0, sticky="ew")
		actions.columnconfigure(1, weight=1)
		tk.Label(actions, text="Select item(s), then check out or book.").grid(
			row=0, column=0, columnspan=2, sticky="w", padx=(0, 12)
		)
		self.checkout_button = self.create_colored_action_button(
			actions, "Check Out", self.check_out, "#1f5f8b", "#17496c"
		)
		self.checkout_button.grid(row=0, column=2, padx=(0, 8))
		self.checkin_button = self.create_colored_action_button(
			actions, "Check In", self.check_in, "#26734d", "#1d5a3b"
		)
		self.checkin_button.grid(row=0, column=3, padx=(0, 8))
		self.book_button = ttk.Button(actions, text="Book selected", command=self.book_multi_scan_queue, state="disabled")
		self.book_button.grid(row=0, column=4)
		ttk.Button(actions, text="Clear selection", command=self.clear_multi_scan_queue).grid(
			row=0, column=5, padx=(8, 0)
		)
		self.selection_status = tk.StringVar(value="No items selected")
		ttk.Label(actions, textvariable=self.selection_status).grid(row=0, column=6, padx=(12, 0))
		self.notification_settings_button = ttk.Button(
			actions, text="Notification settings", command=self.notification_settings_dialog
		)
		self.notification_settings_button.grid(row=0, column=7, padx=(8, 0))
		self.web_api_settings_button = ttk.Button(
			actions, text="Web sync setup", command=self.web_api_settings_dialog
		)
		self.web_api_settings_button.grid(row=0, column=8, padx=(8, 0))
		self.action_feedback = tk.StringVar(value="Scan an item or select it below.")
		self.action_feedback_label = tk.Label(
			actions, textvariable=self.action_feedback, anchor="w", foreground="#344054",
			font=("Segoe UI", 10, "bold"), wraplength=700,
		)
		self.action_feedback_label.grid(row=1, column=0, columnspan=9, sticky="ew", pady=(6, 0))

		list_frame = ttk.LabelFrame(self.root, text="Inventory", padding=10)
		list_frame.grid(row=4, column=0, padx=20, pady=(0, 20), sticky="nsew")
		list_frame.columnconfigure(0, weight=1)
		list_frame.rowconfigure(2, weight=1)
		search = ttk.Entry(list_frame, textvariable=self.search_value)
		search.grid(row=0, column=0, sticky="ew", padx=(0, 8), pady=(0, 8))
		search.insert(0, "Search barcode or item name")
		search.bind("<FocusIn>", lambda _: search.delete(0, tk.END) if search.get() == "Search barcode or item name" else None)
		search.bind("<KeyRelease>", lambda _: self.refresh_items())
		self.add_button = ttk.Button(list_frame, text="Add item", command=self.add_item_dialog, state="disabled")
		self.add_button.grid(row=0, column=1, pady=(0, 8))
		self.edit_button = ttk.Button(list_frame, text="Edit item", command=self.edit_item_dialog, state="disabled")
		self.edit_button.grid(row=0, column=2, padx=(8, 0), pady=(0, 8))
		self.photo_button = ttk.Button(list_frame, text="Photo", command=self.choose_photo, state="disabled")
		self.photo_button.grid(row=0, column=3, padx=(8, 0), pady=(0, 8))
		self.unavailable_button = ttk.Button(
			list_frame, text="Mark Unavailable", command=self.toggle_unavailable, state="disabled"
		)
		self.unavailable_button.grid(row=0, column=4, padx=(8, 0), pady=(0, 8))
		self.delete_button = ttk.Button(
			list_frame, text="Delete item", command=self.delete_selected_item, state="disabled"
		)
		self.delete_button.grid(row=0, column=5, padx=(8, 0), pady=(0, 8))
		self.category_button = ttk.Button(
			list_frame, text="Manage categories", command=self.manage_categories_dialog, state="disabled"
		)
		self.category_button.grid(row=0, column=6, padx=(8, 0), pady=(0, 8))

		columns_header = ttk.Frame(list_frame)
		columns_header.grid(row=1, column=0, columnspan=7, sticky="ew", pady=(0, 4))
		columns_header.columnconfigure(2, weight=3)
		columns_header.columnconfigure(3, weight=1)
		columns_header.columnconfigure(4, weight=2)
		for column, label in ((2, "Item"), (3, "Status"), (4, "Borrowed by")):
			ttk.Label(columns_header, text=label).grid(row=0, column=column, sticky="w", padx=8)

		items_container = ttk.Frame(list_frame)
		items_container.grid(row=2, column=0, columnspan=7, sticky="nsew")
		items_container.columnconfigure(0, weight=1)
		items_container.rowconfigure(0, weight=1)
		self.items_canvas = tk.Canvas(items_container, highlightthickness=0, borderwidth=0)
		self.items_canvas.grid(row=0, column=0, sticky="nsew")
		items_scrollbar = ttk.Scrollbar(items_container, orient="vertical", command=self.items_canvas.yview)
		items_scrollbar.grid(row=0, column=1, sticky="ns")
		self.items_canvas.configure(yscrollcommand=items_scrollbar.set)

		def scroll_inventory_items(event):
			"""Scroll the inventory canvas with the mouse wheel or trackpad."""
			canvas_left = self.items_canvas.winfo_rootx()
			canvas_top = self.items_canvas.winfo_rooty()
			if not (
				canvas_left <= event.x_root < canvas_left + self.items_canvas.winfo_width()
				and canvas_top <= event.y_root < canvas_top + self.items_canvas.winfo_height()
			):
				return
			if getattr(event, "delta", 0):
				steps = max(1, abs(event.delta) // 120)
				self.items_canvas.yview_scroll(-steps if event.delta > 0 else steps, "units")
			elif getattr(event, "num", None) == 4:
				self.items_canvas.yview_scroll(-1, "units")
			elif getattr(event, "num", None) == 5:
				self.items_canvas.yview_scroll(1, "units")
			return "break"

		self.root.bind_all("<MouseWheel>", scroll_inventory_items, add="+")
		self.root.bind_all("<Button-4>", scroll_inventory_items, add="+")
		self.root.bind_all("<Button-5>", scroll_inventory_items, add="+")

		self.items_inner = ttk.Frame(self.items_canvas)
		self.items_window = self.items_canvas.create_window((0, 0), window=self.items_inner, anchor="nw")
		self.items_inner.bind(
			"<Configure>",
			lambda _event: self.items_canvas.configure(scrollregion=self.items_canvas.bbox("all")),
		)
		self.items_canvas.bind(
			"<Configure>",
			lambda event: self.items_canvas.itemconfigure(self.items_window, width=event.width),
		)
		self.items_inner.columnconfigure(2, weight=3)
		self.items_inner.columnconfigure(3, weight=1)
		self.items_inner.columnconfigure(4, weight=2)

	def create_colored_action_button(
		self,
		parent: tk.Misc,
		text: str,
		command,
		background: str,
		active_background: str,
	) -> tk.Label:
		"""Build a keyboard-accessible colored action control that renders on macOS Aqua."""
		button = tk.Label(
			parent, text=text, bg=background, fg="#ffffff",
			font=("Segoe UI", 12, "bold"), width=13, height=2,
			padx=10, pady=8, relief="raised", borderwidth=1,
			cursor="hand2", takefocus=True,
		)
		button.bind("<Enter>", lambda _event: button.configure(bg=active_background))
		button.bind("<Leave>", lambda _event: button.configure(bg=background, relief="raised"))
		button.bind("<ButtonPress-1>", lambda _event: button.configure(relief="sunken"))
		def activate(_event=None):
			button.configure(bg=active_background, relief="raised")
			command()
			return "break"
		button.bind("<ButtonRelease-1>", activate)
		button.bind("<Return>", lambda _event: command())
		button.bind("<space>", lambda _event: command())
		return button

	def refresh_items(self) -> None:
		"""Rebuild the scrollable inventory with selected items at the top."""
		for child in self.items_inner.winfo_children():
			child.destroy()
		self.item_selection_vars.clear()
		self.item_row_images.clear()
		self.item_row_frames.clear()
		self.item_row_separators.clear()
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
			"WHEN items.missing = 1 THEN 3 "
			"WHEN items.unavailable = 1 THEN 2 "
			"WHEN items.checked_out_by IS NOT NULL THEN 1 "
			"ELSE 0 END, items.name COLLATE NOCASE",
			(f"%{search}%", f"%{search}%", f"%{search}%"),
		).fetchall()
		self.item_base_order = [row["barcode"] for row in rows]
		selected_order = {barcode: index for index, barcode in enumerate(self.multi_scan_queue)}
		rows = sorted(
			rows,
			key=lambda row: (
				0 if row["barcode"] in selected_order else 1,
				selected_order.get(row["barcode"], 0),
			),
		)
		if not rows:
			ttk.Label(self.items_inner, text="No items match this search.").grid(
				row=0, column=0, columnspan=5, sticky="w", padx=12, pady=18
			)
		for row_index, row in enumerate(rows):
			today_reservation = self.get_reservation(row["barcode"])
			if row["missing"]:
				status, status_color = "Missing", "#ff0000"
			elif row["unavailable"]:
				status, status_color = "Unavailable", "#333333"
			elif row["checked_out_by"]:
				status, status_color = ("Late", "#c62828") if row["checkout_late"] else ("Checked out", "#c62828")
			elif today_reservation:
				status, status_color = "Reserved", "#333333"
			else:
				status, status_color = "Available", "#208a3c"
			row_frame = ttk.Frame(self.items_inner, padding=(4, 5))
			row_frame.grid(row=row_index * 2, column=0, columnspan=5, sticky="ew")
			self.item_row_frames[row["barcode"]] = row_frame
			row_frame.bind(
				"<Button-1>",
				lambda _event, barcode=row["barcode"]: self.toggle_item_selected_from_row(barcode),
			)
			for column, weight in ((2, 3), (3, 1), (4, 2)):
				row_frame.columnconfigure(column, weight=weight)
			selected = row["barcode"] in selected_order
			selection_var = tk.BooleanVar(value=selected)
			self.item_selection_vars[row["barcode"]] = selection_var
			ttk.Checkbutton(
				row_frame,
				variable=selection_var,
				command=lambda barcode=row["barcode"], value=selection_var: self.set_item_selected(barcode, value.get()),
			).grid(row=0, column=0, rowspan=2, padx=(4, 10))
			if row["photo_path"]:
				try:
					image = Image.open(row["photo_path"])
					image.thumbnail((56, 56))
					photo = ImageTk.PhotoImage(image)
					self.item_row_images.append(photo)
					photo_label = ttk.Label(row_frame, image=photo)
					photo_label.grid(row=0, column=1, rowspan=2, padx=(0, 12))
				except (FileNotFoundError, OSError):
					photo_label = ttk.Label(row_frame, text="No photo", width=9)
					photo_label.grid(row=0, column=1, rowspan=2, padx=(0, 12))
			else:
				photo_label = ttk.Label(row_frame, text="No photo", width=9)
				photo_label.grid(row=0, column=1, rowspan=2, padx=(0, 12))
			photo_label.bind(
				"<Button-1>",
				lambda _event, barcode=row["barcode"]: self.toggle_item_selected_from_row(barcode),
			)
			name_label = ttk.Label(
				row_frame, text=row["name"], font=("Segoe UI", 11, "bold"), foreground=status_color
			)
			name_label.grid(
				row=0, column=2, sticky="w", padx=8
			)
			barcode_label = ttk.Label(
				row_frame,
				text=f"{row['barcode']}  ·  {row['category'] or 'Uncategorized'}",
				foreground="#666666",
			)
			barcode_label.grid(row=1, column=2, sticky="w", padx=8)
			status_label = tk.Label(row_frame, text=status, foreground=status_color, font=("Segoe UI", 10, "bold"))
			status_label.grid(row=0, column=3, rowspan=2, sticky="w", padx=8)
			borrower_label = tk.Label(row_frame, text=row["checked_out_by"] or "—")
			borrower_label.grid(
				row=0, column=4, rowspan=2, sticky="w", padx=8
			)
			for row_widget in (name_label, barcode_label, status_label, borrower_label):
				row_widget.bind(
					"<Button-1>",
					lambda _event, barcode=row["barcode"]: self.toggle_item_selected_from_row(barcode),
				)
			separator = ttk.Separator(self.items_inner, orient="horizontal")
			self.item_row_separators[row["barcode"]] = separator
		self.reorder_inventory_rows()
		self.update_admin_controls()

	def reorder_inventory_rows(self) -> None:
		"""Move existing inventory rows to reflect selection order without rebuilding them."""
		selected_order = {barcode: index for index, barcode in enumerate(self.multi_scan_queue)}
		base_order = {barcode: index for index, barcode in enumerate(self.item_base_order)}
		ordered_barcodes = sorted(
			self.item_base_order,
			key=lambda barcode: (
				(0, selected_order[barcode]) if barcode in selected_order else (1, base_order[barcode])
			),
		)
		for row_index, barcode in enumerate(ordered_barcodes):
			self.item_row_frames[barcode].grid_configure(row=row_index * 2)
			separator = self.item_row_separators[barcode]
			if row_index < len(ordered_barcodes) - 1:
				separator.grid(row=row_index * 2 + 1, column=0, columnspan=5, sticky="ew")
			else:
				separator.grid_remove()

	def toggle_item_selected_from_row(self, barcode: str) -> str:
		"""Toggle one inventory item's checkbox when any non-checkbox part of its row is clicked."""
		currently_selected = barcode in self.multi_scan_queue
		self.set_item_selected(barcode, not currently_selected)
		return "break"

	def scan_item(self, event_or_barcode: tk.Event | str | None = None, force: bool = False) -> None:
		"""Look up a scanned or typed barcode and add the item to the current selection."""
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
				self.scan_entry.focus_set()
				return
			self.clear_selection()
			self.scan_entry.focus_set()
			self.set_action_feedback(f"No item found for barcode {barcode}.", "error")
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
		if row["missing"]:
			with self.db_lock:
				self.database.execute("UPDATE items SET missing = 0 WHERE barcode = ?", (barcode,))
				self.database.commit()
			row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (barcode,)).fetchone()
			self.refresh_items()

		self.add_to_multi_scan_queue(row)

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
		# Clear the duplicate global buffer so this scanner input is handled once.
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
		if row["missing"]:
			status = "Missing"
		elif row["unavailable"]:
			status = "Unavailable"
		elif row["checked_out_by"]:
			status = "Late" if row["checkout_late"] else "Checked out"
			if row["checkout_due_at"]:
				status += f" until {row['checkout_due_at']}"
		elif self.get_reservation(row["barcode"]):
			status = "Reserved"
		else:
			status = "Available"
		self.item_status.set(status)
		self.item_category.set(row["category"] or "Uncategorized")
		self.borrower_name.set(row["checked_out_by"] or "")
		if row["photo_path"] and hasattr(self, "photo_preview"):
			self.update_photo_preview(row["photo_path"])
		self.update_admin_controls()

	def add_to_multi_scan_queue(self, row: sqlite3.Row) -> None:
		"""Select a scanned item and move it to the top of the inventory list."""
		barcode = row["barcode"]
		already_selected = barcode in self.multi_scan_queue
		if already_selected:
			self.multi_scan_queue.remove(barcode)
			self.multi_scan_queue.insert(0, barcode)
		else:
			self.multi_scan_queue.insert(0, barcode)
		self.reset_selection_clear_timer()
		self.selected_barcode = barcode
		selection_var = self.item_selection_vars.get(barcode)
		if selection_var:
			selection_var.set(True)
		self.reorder_inventory_rows()
		self.items_canvas.yview_moveto(0)
		self.update_admin_controls()
		feedback = f"{row['name']} is selected."
		self.set_action_feedback(feedback, "neutral" if already_selected else "selection")

	def set_item_selected(self, barcode: str, selected: bool) -> None:
		"""Add or remove an item from the shared manual and scanner selection."""
		if selected:
			if barcode not in self.multi_scan_queue:
				self.multi_scan_queue.append(barcode)
			self.selected_barcode = barcode
		else:
			if barcode in self.multi_scan_queue:
				self.multi_scan_queue.remove(barcode)
			if self.selected_barcode == barcode:
				self.selected_barcode = self.multi_scan_queue[0] if self.multi_scan_queue else None
		if self.multi_scan_queue:
			self.reset_selection_clear_timer()
		else:
			self.cancel_selection_clear_timer()
		selection_var = self.item_selection_vars.get(barcode)
		if selection_var:
			selection_var.set(selected)
		self.reorder_inventory_rows()
		self.update_admin_controls()
		count = len(self.multi_scan_queue)
		self.set_action_feedback(
			f"{count} item(s) selected." if count else "No items selected.", "neutral"
		)

	def reset_selection_clear_timer(self) -> None:
		"""Clear the current selection three minutes after its latest change."""
		self.cancel_selection_clear_timer()
		if self.multi_scan_queue:
			self.selection_clear_after_id = self.root.after(
				SELECTION_CLEAR_DELAY_MS, self.clear_selection_after_timeout
			)

	def cancel_selection_clear_timer(self) -> None:
		"""Cancel the pending selection expiry, if one is scheduled."""
		if self.selection_clear_after_id is not None:
			try:
				self.root.after_cancel(self.selection_clear_after_id)
			except tk.TclError:
				pass
			self.selection_clear_after_id = None

	def clear_selection_after_timeout(self) -> None:
		"""Clear selected items after three minutes without selection activity."""
		self.selection_clear_after_id = None
		if not self.multi_scan_queue:
			return
		self.clear_multi_scan_queue()
		self.set_action_feedback("Selection cleared after 3 minutes.", "neutral")

	def refresh_multi_scan_queue(self) -> None:
		"""Refresh the inventory view after a batch selection or checkout change."""
		self.refresh_items()

	def remove_from_multi_scan_queue(self) -> None:
		"""Clear the shared selection without affecting item status."""
		self.clear_multi_scan_queue()

	def clear_multi_scan_queue(self) -> None:
		"""Clear all manually or scanner-selected inventory items."""
		self.cancel_selection_clear_timer()
		self.multi_scan_queue.clear()
		self.selected_barcode = None
		self.refresh_multi_scan_queue()
		self.update_admin_controls()

	def checkout_multi_scan_queue(self) -> None:
		"""Check out selected items to one borrower, skipping items that aren't available."""
		if not self.multi_scan_queue:
			self.set_action_feedback("Select or scan an item before checking out.", "error")
			return
		account = self.resolve_borrower_account(self.root)
		if account is None:
			return
		schedule_enabled = self.bell_schedule_enabled()
		if schedule_enabled:
			due_at = self.choose_checkout_due_time(self.root)
		else:
			due_at = None
		if schedule_enabled and due_at is None:
			return
		borrower = account["full_name"]
		timestamp = datetime.now().strftime("%Y-%m-%d %H:%M")
		due_timestamp = due_at.strftime("%Y-%m-%d %H:%M") if due_at else None
		checked_out: list[str] = []
		checked_out_barcodes: list[str] = []
		skipped: list[str] = []
		with self.db_lock:
			for barcode in list(self.multi_scan_queue):
				try:
					item = self.database.execute(
						"SELECT name, checked_out_by, unavailable, missing FROM items WHERE barcode = ?", (barcode,)
					).fetchone()
					if item is None:
						skipped.append(f"{barcode} (not found)")
						continue
					if item["unavailable"]:
						skipped.append(f"{item['name']} (unavailable)")
						continue
					if item["missing"]:
						skipped.append(f"{item['name']} (marked missing; scan it before checkout)")
						continue
					if item["checked_out_by"]:
						skipped.append(f"{item['name']} (already checked out)")
						continue
					
					self.database.execute(
						"UPDATE items SET checked_out_by = ?, checked_out_at = ?, checkout_due_at = ?, checkout_late = 0 WHERE barcode = ?",
						(borrower, timestamp, due_timestamp, barcode),
					)
					self.record_history(barcode, item["name"], "Checked out", borrower)
					self.mark_recently_changed(barcode)
					checked_out.append(item["name"])
					checked_out_barcodes.append(barcode)
				except Exception as e:
					skipped.append(f"Error with {barcode}: {str(e)}")

			self.database.commit()
		self.multi_scan_queue.clear()
		self.cancel_selection_clear_timer()
		self.selected_barcode = None
		self.refresh_multi_scan_queue()
		if checked_out:
			self.sync_to_google_sheets(show_result=False)
			for barcode in checked_out_barcodes:
				self.queue_web_service_checkout_sync(barcode)
		message = f"Checked out {len(checked_out)} item(s) to {borrower}."
		if skipped:
			message += "\nSkipped: " + ", ".join(skipped)
		self.set_action_feedback(message, "error" if skipped or not checked_out else "success")

	def checkin_multi_scan_queue(self) -> None:
		"""Check in selected checked-out items, skipping the rest."""
		if not self.multi_scan_queue:
			self.set_action_feedback("Select a checked-out item before checking it in.", "error")
			return
		checked_in: list[str] = []
		checked_in_barcodes: list[str] = []
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
						"UPDATE items SET checked_out_by = NULL, checked_out_at = NULL, checkout_due_at = NULL, checkout_late = 0 "
						"WHERE barcode = ? AND checked_out_by IS NOT NULL",
						(barcode,),
					)
					if not update.rowcount:
						skipped.append(f"{item['name']} (check-in failed)")
						continue
					
					self.record_history(barcode, item["name"], "Checked in", item["checked_out_by"])
					self.mark_recently_changed(barcode)
					self.database.execute(
						"DELETE FROM reservations WHERE barcode = ? AND reserved_date <= ?",
						(barcode, datetime.now().strftime("%Y-%m-%d")),
					)
					checked_in.append(item["name"])
					checked_in_barcodes.append(barcode)
				except Exception as e:
					skipped.append(f"{barcode} (error: {str(e)})")
			self.database.commit()

		message = f"Checked in {len(checked_in)} item(s)."
		if skipped:
			message += "\nSkipped: " + ", ".join(skipped)
		self.clear_multi_scan_queue()
		self.set_action_feedback(message, "error" if skipped or not checked_in else "success")
		if checked_in:
			self.sync_to_google_sheets(show_result=False)
			for barcode in checked_in_barcodes:
				self.queue_web_service_checkout_sync(barcode)

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
			self.refresh_items()

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

	def checkout_due_time(self, mode: str = "period", current: datetime | None = None) -> datetime | None:
		"""Return the due time for a new checkout, either this period or the next school-day first period."""
		current = current or datetime.now()
		if mode == "day":
			next_day = self.database.execute(
				"SELECT period_date FROM bell_periods WHERE period_date > ? ORDER BY period_date, start_time LIMIT 1",
				(current.strftime("%Y-%m-%d"),),
			).fetchone()
			if next_day is None:
				messagebox.showwarning(
					"No next school day",
					"Add the next school day to the bell schedule before allowing full-day checkouts.",
					parent=self.root,
				)
				return None
			first_period = self.database.execute(
				"SELECT * FROM bell_periods WHERE period_date = ? ORDER BY start_time LIMIT 1",
				(next_day["period_date"],),
			).fetchone()
			if first_period is None:
				messagebox.showwarning(
					"No bell schedule for next day",
					"The next school day is missing a bell schedule, so full-day checkout cannot be assigned.",
					parent=self.root,
				)
				return None
			return datetime.strptime(
				f"{first_period['period_date']} {first_period['end_time']}", "%Y-%m-%d %H:%M"
			)
		period = self.get_active_bell_period(current)
		if period is None:
			messagebox.showwarning(
				"No active class period",
				"An admin must add the current date's bell schedule before checking out equipment.",
				parent=self.root,
			)
			return None
		return datetime.strptime(
			f"{period['period_date']} {period['end_time']}", "%Y-%m-%d %H:%M"
		)

	def checkout_due_time_after_dates(self, selected_dates: set[str]) -> datetime | None:
		"""Return the end of the first period on the next scheduled day after the last selected date."""
		if not selected_dates:
			return None
		first_period = self.database.execute(
			"SELECT period_date, end_time FROM bell_periods "
			"WHERE period_date > ? ORDER BY period_date, start_time LIMIT 1",
			(max(selected_dates),),
		).fetchone()
		if first_period is None:
			messagebox.showwarning(
				"No next school day",
				"Add a bell schedule after the last selected checkout day before checking out equipment.",
				parent=self.root,
			)
			return None
		return datetime.strptime(
			f"{first_period['period_date']} {first_period['end_time']}", "%Y-%m-%d %H:%M"
		)

	def choose_checkout_duration(self, parent: tk.Misc | None = None) -> str | None:
		"""Let the user choose a period, one day, or multiple days for checkout."""
		selected = {"value": None}
		dialog = tk.Toplevel(parent or self.root)
		dialog.title("Checkout duration")
		dialog.transient(parent or self.root)
		dialog.grab_set()
		dialog.resizable(False, False)
		frame = ttk.Frame(dialog, padding=16)
		frame.pack()
		tk.Label(frame, text="How long should this checkout last?", font=(None, 11, "bold")).grid(
			row=0, column=0, columnspan=2, sticky="w", pady=(0, 12)
		)
		def choose(mode: str) -> None:
			selected["value"] = mode
			dialog.destroy()
		button_padx = {"padx": 8, "pady": 6}
		tk.Button(frame, text="Entire day", width=16, command=lambda: choose("day")).grid(
			row=1, column=0, **button_padx
		)
		tk.Button(frame, text="For the period", width=16, command=lambda: choose("period")).grid(
			row=1, column=1, **button_padx
		)
		tk.Button(frame, text="Multiple days", command=lambda: choose("multiple_days")).grid(
			row=2, column=0, columnspan=2, sticky="ew", padx=8, pady=(0, 6)
		)
		dialog.wait_window()
		return selected["value"]

	def choose_checkout_due_time(self, parent: tk.Misc | None = None) -> datetime | None:
		"""Ask for a checkout duration and resolve its due time, including selected checkout days."""
		mode = self.choose_checkout_duration(parent)
		if mode is None:
			return None
		if mode == "multiple_days":
			selected_dates = self.choose_schedule_dates(
				parent or self.root,
				title="Select checkout days",
				instruction="Today stays selected. Pick an end date to select every day through that date.",
				continuous_from_today=True,
			)
			if selected_dates is None:
				return None
			return self.checkout_due_time_after_dates(selected_dates)
		return self.checkout_due_time(mode)

	def check_out(self) -> None:
		"""Check the selected item out to the typed borrower.

		The read-check-write happens under db_lock and the UPDATE only succeeds if
		the item is still available, so a concurrent background sheet sync can't
		cause this to report success when nothing actually changed.
		"""
		if len(self.multi_scan_queue) > 1:
			self.checkout_multi_scan_queue()
			return

		if not self.selected_barcode:
			self.set_action_feedback("Scan or select an item before checking it out.", "error")
			return
		account = self.resolve_borrower_account(self.root)
		if account is None:
			return
		borrower = account["full_name"]
		reservation = self.get_reservation(self.selected_barcode)
		is_booked_for_borrower = bool(
			reservation and self.names_match(reservation["borrower"], borrower)
		)
		schedule_enabled = self.bell_schedule_enabled()
		if schedule_enabled:
			if is_booked_for_borrower:
				booked_dates = self.get_booking_dates(
					self.selected_barcode, borrower, reservation["created_at"]
				)
				due_at = self.checkout_due_time_after_dates(booked_dates)
			else:
				due_at = self.choose_checkout_due_time(self.root)
		else:
			due_at = None
		if schedule_enabled and due_at is None:
			return
		succeeded = False
		with self.db_lock:
			item = self.database.execute(
				"SELECT name, unavailable, missing FROM items WHERE barcode = ?", (self.selected_barcode,)
			).fetchone()
			if item and item["missing"]:
				self.set_action_feedback("This item is marked missing. Scan it to confirm it is here.", "error")
				return
			if item and item["unavailable"]:
				self.set_action_feedback("This item is unavailable. Ask an admin for help.", "error")
				return
			if reservation and not self.names_match(reservation["borrower"], borrower):
				self.set_action_feedback(f"This item is booked for {reservation['borrower']} today.", "error")
				return
			timestamp = datetime.now().strftime("%Y-%m-%d %H:%M")
			due_timestamp = due_at.strftime("%Y-%m-%d %H:%M") if due_at else None
			update = self.database.execute(
				"UPDATE items SET checked_out_by = ?, checked_out_at = ?, checkout_due_at = ?, checkout_late = 0 "
				"WHERE barcode = ? AND checked_out_by IS NULL",
				(borrower, timestamp, due_timestamp, self.selected_barcode),
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
			self.set_action_feedback("Checkout did not go through. Check the item's status and try again.", "error")
			return
		message = f"Item checked out to {borrower}."
		if due_at:
			message = f"Item checked out to {borrower} until {due_at.strftime('%I:%M %p').lstrip('0')}."
		self.finish_action(message)

	def check_in(self) -> None:
		"""Check the selected item back in, the same race-safe way as check_out."""
		if len(self.multi_scan_queue) > 1:
			self.checkin_multi_scan_queue()
			return

		if not self.selected_barcode:
			self.set_action_feedback("Scan or select an item before checking it in.", "error")
			return
		succeeded = False
		with self.db_lock:
			item = self.database.execute(
				"SELECT name, checked_out_by FROM items WHERE barcode = ?", (self.selected_barcode,)
			).fetchone()
			was_checked_out = bool(item and item["checked_out_by"])
			update = self.database.execute(
				"UPDATE items SET checked_out_by = NULL, checked_out_at = NULL, checkout_due_at = NULL, checkout_late = 0 "
				"WHERE barcode = ? AND checked_out_by IS NOT NULL",
				(self.selected_barcode,),
			)
			succeeded = bool(was_checked_out and update.rowcount)
			if succeeded:
				self.record_history(self.selected_barcode, item["name"], "Checked in", item["checked_out_by"])
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
			self.set_action_feedback("Check In did not go through. Check the item's status and try again.", "error")
			return
		self.finish_action("Item checked in and available.")

	def set_action_feedback(self, message: str, tone: str = "neutral") -> None:
		"""Show an action result in plain language and signal success or error audibly."""
		foregrounds = {
			"success": "#176b3a",
			"error": "#a11212",
			"selection": "#205c7a",
			"neutral": "#344054",
		}
		self.action_feedback.set(message)
		self.action_feedback_label.configure(foreground=foregrounds.get(tone, foregrounds["neutral"]))
		sounds = {"success": "Pop", "error": "Error", "selection": "Tink"}
		if tone in sounds:
			self.play_sound(sounds[tone])

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
		"""Open the booking calendar for every currently selected item."""
		if not self.multi_scan_queue:
			messagebox.showwarning("No items selected", "Select or scan at least one item before booking.")
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
			created_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
			with self.db_lock:
				for date_text in selected_dates:
					for barcode, name in items:
						if existing.get(date_text, {}).get(barcode):
							self.database.execute(
								"UPDATE reservations SET borrower = ?, created_at = ?, status = 'Confirmed' "
								"WHERE barcode = ? AND reserved_date = ?",
								(borrower_name, created_at, barcode, date_text),
							)
						else:
							self.database.execute(
								"INSERT INTO reservations "
								"(barcode, item_name, reserved_date, borrower, created_at, status) "
								"VALUES (?, ?, ?, ?, ?, 'Confirmed')",
								(barcode, name, date_text, borrower_name, created_at),
							)
				self.database.commit()
			refresh_after_change()

		def delete_booking() -> None:
			existing = existing_bookings_for_selection()
			to_delete = [
				(date_text, booking) for date_text, day_map in existing.items() for booking in day_map.values()
			]
			if not to_delete:
				return
			blocked = []
			for date_text, booking in to_delete:
				if not self.admin_mode and not self.booking_is_recent(booking["created_at"]):
					blocked.append(f"{booking['barcode']} on {date_text} (created more than 5 minutes ago)")
			if blocked:
				messagebox.showwarning(
					"Admin approval required",
					"Bookings can only be deleted without admin mode within 5 minutes of creation:\n"
					+ "\n".join(blocked),
					parent=date_dialog,
				)
				return
			if messagebox.askyesno(
				"Delete booking",
				f"Delete {len(to_delete)} booking(s) across {len(items)} item(s)?",
				parent=date_dialog,
			):
				with self.db_lock:
					for _date_text, booking in to_delete:
						self.database.execute("DELETE FROM reservations WHERE id = ?", (booking["id"],))
					self.database.commit()
				refresh_after_change()

		delete_button = ttk.Button(frame, text="Delete Booking", command=delete_booking, state="disabled")
		delete_button.grid(row=5, column=0, pady=(12, 0))
		ttk.Button(frame, text="Book", command=save_booking).grid(row=5, column=2, pady=(12, 0))
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
			"UPDATE items SET unavailable = ?, missing = 0 WHERE barcode = ?",
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
		"""Show success feedback, refresh the UI, and sync to Sheets."""
		self.set_action_feedback(message, "success")
		row = self.database.execute("SELECT * FROM items WHERE barcode = ?", (self.selected_barcode,)).fetchone()
		if row:
			self.show_item(row)
		self.borrower_name.set("")
		self.refresh_items()
		self.sync_to_google_sheets(show_result=False)
		if self.selected_barcode:
			self.queue_web_service_checkout_sync(self.selected_barcode)

	def clear_selection(self) -> None:
		"""Clear the active item and all inventory checkbox selections."""
		self.cancel_selection_clear_timer()
		self.selected_barcode = None
		self.multi_scan_queue.clear()
		self.item_name.set("Scan an item to begin")
		self.item_status.set("Ready for scan")
		self.item_category.set("")
		self.borrower_name.set("")
		if hasattr(self, "items_inner"):
			self.refresh_items()
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
		"""Stop background workers and close the database before the window exits."""
		self.cancel_selection_clear_timer()
		self.google_executor.shutdown(wait=False, cancel_futures=True)
		self.web_api_executor.shutdown(wait=False, cancel_futures=True)
		self.notification_executor.shutdown(wait=False, cancel_futures=True)
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
	parser.add_argument(
		"--api-url",
		help="Optional hosted inventory API URL (for example https://your-service.onrender.com). ",
		default=WEB_API_BASE_URL,
	)
	parser.add_argument(
		"--api-email",
		help="Email address used to log in to the hosted inventory API.",
		default=WEB_API_EMAIL,
	)
	parser.add_argument(
		"--api-password",
		help="Password used to log in to the hosted inventory API.",
		default=WEB_API_PASSWORD,
	)
	parser.add_argument(
		"--api-inventory-id",
		type=int,
		help="Inventory ID to target when a user has more than one hosted inventory. Defaults to the first inventory.",
		default=(int(WEB_API_INVENTORY_ID) if WEB_API_INVENTORY_ID else None),
	)
	cli_args = parser.parse_args()
	if cli_args.database:
		DATABASE_FILE = str(Path(cli_args.database).expanduser().resolve())
		Path(DATABASE_FILE).parent.mkdir(parents=True, exist_ok=True)
		BACKUP_DIRECTORY = Path(DATABASE_FILE).parent / "database_backups"
	if cli_args.api_url:
		WEB_API_BASE_URL = cli_args.api_url.strip()
	if cli_args.api_email:
		WEB_API_EMAIL = cli_args.api_email.strip()
	if cli_args.api_password:
		WEB_API_PASSWORD = cli_args.api_password
	if cli_args.api_inventory_id is not None:
		WEB_API_INVENTORY_ID = str(cli_args.api_inventory_id)

	application = tk.Tk()
	CheckInSystem(application)
	application.mainloop()
