import os
import sqlite3
import tempfile
import threading
import unittest
from pathlib import Path
from unittest.mock import Mock

import coolscaner

os.environ["DATABASE_URL"] = f"sqlite:///{Path(tempfile.gettempdir()) / f'equipment-ledger-tests-{os.getpid()}.db'}"

from fastapi.testclient import TestClient

from web_service import app as service


class InventoryApiTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.client = TestClient(service.app)

    def setUp(self):
        service.Base.metadata.drop_all(service.engine)
        service.Base.metadata.create_all(service.engine)
        self.owner_a = self.register("owner-a@example.com", "A secure passphrase 123", "Studio A")
        self.owner_b = self.register("owner-b@example.com", "B secure passphrase 456", "Studio B")

    def register(self, email, password, inventory_name):
        response = self.client.post("/api/auth/register", json={
            "email": email,
            "password": password,
            "inventory_name": inventory_name,
        })
        self.assertEqual(response.status_code, 201, response.text)
        data = response.json()
        return {
            "token": data["token"],
            "inventory_id": str(data["inventory_id"]),
            "email": email,
            "password": password,
        }

    @staticmethod
    def headers(owner):
        return {
            "Authorization": f"Bearer {owner['token']}",
            "X-Inventory-ID": owner["inventory_id"],
        }

    def import_item(self, owner, barcode="cam-01", name="Camera"):
        response = self.client.post(
            "/api/import/sqlite",
            headers=self.headers(owner),
            json={"items": [{"barcode": barcode, "name": name}]},
        )
        self.assertEqual(response.status_code, 200, response.text)

    def test_workspaces_are_isolated(self):
        self.import_item(self.owner_a)
        self.import_item(self.owner_b, "mic-02", "Microphone")
        a_items = self.client.get("/api/items", headers=self.headers(self.owner_a)).json()
        b_items = self.client.get("/api/items", headers=self.headers(self.owner_b)).json()
        self.assertEqual([item["barcode"] for item in a_items], ["cam-01"])
        self.assertEqual([item["barcode"] for item in b_items], ["mic-02"])
        forbidden = self.client.get(
            "/api/items",
            headers={**self.headers(self.owner_a), "X-Inventory-ID": self.owner_b["inventory_id"]},
        )
        self.assertEqual(forbidden.status_code, 403)

    def test_checkout_checkin_history_and_bookings(self):
        self.import_item(self.owner_a)
        headers = self.headers(self.owner_a)
        checked_out = self.client.post(
            "/api/items/cam-01/checkout", headers=headers,
            json={"borrower": "Alex Borrower", "due_at": "2026-10-09 15:00"},
        )
        self.assertEqual(checked_out.status_code, 200, checked_out.text)
        item_snapshot = self.client.get("/api/items", headers=headers).json()[0]
        self.assertEqual(item_snapshot["status"], "Checked out")
        self.assertEqual(item_snapshot["checked_out_by"], "Alex Borrower")
        self.assertTrue(item_snapshot["checked_out_at"])
        self.assertEqual(item_snapshot["checkout_due_at"], "2026-10-09 15:00")
        self.assertEqual(
            self.client.post("/api/items/cam-01/checkout", headers=headers,
                               json={"borrower": "Another Person"}).status_code,
            409,
        )
        checked_in = self.client.post("/api/items/cam-01/checkin", headers=headers)
        self.assertEqual(checked_in.status_code, 200, checked_in.text)
        checked_in_snapshot = self.client.get("/api/items", headers=headers).json()[0]
        self.assertIsNone(checked_in_snapshot["checked_out_by"])
        self.assertIsNone(checked_in_snapshot["checkout_due_at"])
        history = self.client.get("/api/history", headers=headers).json()
        self.assertEqual([row["action"] for row in history], ["Checked in", "Checked out"])
        booking = self.client.post("/api/bookings", headers=headers, json={
            "barcode": "cam-01", "reserved_date": "2026-10-10", "borrower": "Alex Borrower",
        })
        self.assertEqual(booking.status_code, 201, booking.text)
        self.assertEqual(self.client.get("/api/bookings", headers=headers).json()[0]["barcode"], "cam-01")
        duplicate = self.client.post("/api/bookings", headers=headers, json={
            "barcode": "cam-01", "reserved_date": "2026-10-10", "borrower": "Another Person",
        })
        self.assertEqual(duplicate.status_code, 409)
        deleted = self.client.delete(f"/api/bookings/{booking.json()['id']}", headers=headers)
        self.assertEqual(deleted.status_code, 200)
        self.assertEqual(self.client.get("/api/bookings", headers=headers).json(), [])

    def test_borrower_roster_sync_updates_existing_inventory(self):
        self.import_item(self.owner_a)
        headers = self.headers(self.owner_a)
        synced = self.client.put("/api/borrowers/sync", headers=headers, json={
            "borrowers": [{
                "full_name": "Ada Student", "student_id": "s-100", "email": "ada@example.com",
                "phone": "555-1000", "sms_opt_in": True,
            }],
        })
        self.assertEqual(synced.status_code, 200, synced.text)
        self.assertEqual(self.client.get("/api/borrowers", headers=headers).json(), ["Ada Student"])
        self.assertEqual(self.client.get("/api/items", headers=headers).json()[0]["barcode"], "cam-01")
        self.assertEqual(self.client.get("/api/borrowers", headers=self.headers(self.owner_b)).json(), [])

    def test_checkout_due_time_follows_bell_schedule(self):
        headers = self.headers(self.owner_a)
        imported = self.client.post("/api/import/sqlite", headers=headers, json={
            "items": [{"barcode": "cam-01", "name": "Camera"}],
            "bell_periods": [
                {"period_date": "2026-10-09", "period_name": "P1", "start_time": "08:00", "end_time": "08:50"},
                {"period_date": "2026-10-09", "period_name": "P2", "start_time": "09:00", "end_time": "09:50"},
                {"period_date": "2026-10-12", "period_name": "P1", "start_time": "08:00", "end_time": "08:45"},
            ],
        })
        self.assertEqual(imported.status_code, 200, imported.text)

        def due_after(**due):
            response = self.client.post(
                "/api/items/cam-01/checkout", headers=headers, json={"borrower": "Alex", **due},
            )
            self.assertEqual(response.status_code, 200, response.text)
            value = self.client.get("/api/items", headers=headers).json()[0]["checkout_due_at"]
            self.client.post("/api/items/cam-01/checkin", headers=headers)
            return value

        self.assertEqual(due_after(due_mode="period", client_now="2026-10-09T09:15"), "2026-10-09 09:50")
        self.assertEqual(due_after(due_mode="day", client_now="2026-10-09T09:15"), "2026-10-12 08:45")
        self.assertEqual(
            due_after(due_mode="multiple_days", due_dates=["2026-10-09", "2026-10-10"], client_now="2026-10-09T09:15"),
            "2026-10-12 08:45",
        )
        outside_period = self.client.post("/api/items/cam-01/checkout", headers=headers, json={
            "borrower": "Alex", "due_mode": "period", "client_now": "2026-10-09T12:00",
        })
        self.assertEqual(outside_period.status_code, 409)
        no_days = self.client.post("/api/items/cam-01/checkout", headers=headers, json={
            "borrower": "Alex", "due_mode": "multiple_days", "client_now": "2026-10-09T09:15",
        })
        self.assertEqual(no_days.status_code, 422)
        self.assertIsNone(self.client.get("/api/items", headers=headers).json()[0]["checked_out_by"])

    def test_multi_date_booking_is_atomic_on_conflict(self):
        self.import_item(self.owner_a)
        headers = self.headers(self.owner_a)
        booking = self.client.post("/api/bookings/batch", headers=headers, json={
            "barcode": "cam-01",
            "reserved_dates": ["2026-10-10", "2026-10-11"],
            "borrower": "Alex Borrower",
        })
        self.assertEqual(booking.status_code, 201, booking.text)
        self.assertEqual(
            [row["reserved_date"] for row in booking.json()],
            ["2026-10-10", "2026-10-11"],
        )
        conflict = self.client.post("/api/bookings/batch", headers=headers, json={
            "barcode": "cam-01",
            "reserved_dates": ["2026-10-11", "2026-10-12"],
            "borrower": "Another Borrower",
        })
        self.assertEqual(conflict.status_code, 409)
        rows = self.client.get("/api/bookings", headers=headers).json()
        self.assertEqual([row["reserved_date"] for row in rows], ["2026-10-10", "2026-10-11"])

    def test_logout_revokes_token(self):
        headers = self.headers(self.owner_a)
        logout = self.client.post("/api/auth/logout", headers=headers)
        self.assertEqual(logout.status_code, 200, logout.text)
        response = self.client.get("/api/me", headers=headers)
        self.assertEqual(response.status_code, 401)

    def test_import_only_targets_empty_inventory(self):
        self.import_item(self.owner_a)
        response = self.client.post(
            "/api/import/sqlite", headers=self.headers(self.owner_a),
            json={"items": [{"barcode": "other", "name": "Other"}]},
        )
        self.assertEqual(response.status_code, 409)
        items = self.client.get("/api/items", headers=self.headers(self.owner_a)).json()
        self.assertEqual([item["barcode"] for item in items], ["cam-01"])

    def test_desktop_import_payload_includes_relevant_inventory_data(self):
        db_path = Path(tempfile.gettempdir()) / "equipment-ledger-desktop-payload.db"
        if db_path.exists():
            db_path.unlink()
        with sqlite3.connect(db_path) as database:
            database.execute(
                "CREATE TABLE items (barcode TEXT, name TEXT, category TEXT, unavailable INTEGER, missing INTEGER, checked_out_by TEXT, checked_out_at TEXT, checkout_due_at TEXT, checkout_late INTEGER)"
            )
            database.execute(
                "CREATE TABLE accounts (full_name TEXT, student_id TEXT, email TEXT, phone TEXT, sms_opt_in INTEGER)"
            )
            database.execute(
                "CREATE TABLE reservations (barcode TEXT, item_name TEXT, reserved_date TEXT, borrower TEXT, created_at TEXT, status TEXT)"
            )
            database.execute(
                "CREATE TABLE checkout_history (barcode TEXT, item_name TEXT, action TEXT, borrower TEXT, timestamp TEXT)"
            )
            database.execute(
                "CREATE TABLE categories (name TEXT, sort_order INTEGER)"
            )
            database.execute(
                "CREATE TABLE bell_periods (period_date TEXT, period_name TEXT, start_time TEXT, end_time TEXT)"
            )
            database.execute(
                "INSERT INTO items VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                ("cam-01", "Camera", "Media", 0, 0, "Ada", "2026-10-09 09:00", "2026-10-09 17:00", 0),
            )
            database.execute(
                "INSERT INTO accounts VALUES (?, ?, ?, ?, ?)",
                ("Ada Student", "s-100", "ada@example.com", "555-1000", 1),
            )
            database.execute(
                "INSERT INTO reservations VALUES (?, ?, ?, ?, ?, ?)",
                ("cam-01", "Camera", "2026-10-10", "Ada Student", "2026-10-09 08:00", "Confirmed"),
            )
            database.execute(
                "INSERT INTO checkout_history VALUES (?, ?, ?, ?, ?)",
                ("cam-01", "Camera", "Checked out", "Ada Student", "2026-10-09 09:00"),
            )
            database.execute(
                "INSERT INTO categories VALUES (?, ?)",
                ("Media", 1),
            )
            database.execute(
                "INSERT INTO bell_periods VALUES (?, ?, ?, ?)",
                ("2026-10-10", "Period 1", "08:00", "08:50"),
            )
        payload = coolscaner.build_web_service_import_payload(db_path)
        self.assertEqual(payload["items"][0]["barcode"], "cam-01")
        self.assertEqual(payload["categories"][0]["name"], "Media")
        self.assertEqual(payload["borrowers"][0]["student_id"], "s-100")
        self.assertEqual(payload["reservations"][0]["borrower"], "Ada Student")
        self.assertEqual(payload["bell_periods"][0]["period_name"], "Period 1")
        response = self.client.post("/api/import/sqlite", headers=self.headers(self.owner_a), json=payload)
        self.assertEqual(response.status_code, 200, response.text)
        self.assertEqual(
            self.client.get("/api/borrowers", headers=self.headers(self.owner_a)).json(),
            ["Ada Student"],
        )

    def test_desktop_checkout_and_web_checkin_sync_round_trip(self):
        self.import_item(self.owner_a)
        database = sqlite3.connect(":memory:")
        database.row_factory = sqlite3.Row
        database.execute(
            "CREATE TABLE items (barcode TEXT PRIMARY KEY, name TEXT, checked_out_by TEXT, "
            "checked_out_at TEXT, checkout_due_at TEXT, checkout_late INTEGER)"
        )
        database.execute(
            "CREATE TABLE checkout_history (barcode TEXT, item_name TEXT, action TEXT, borrower TEXT, timestamp TEXT)"
        )
        database.execute("CREATE TABLE reservations (barcode TEXT, reserved_date TEXT)")
        database.execute(
            "INSERT INTO items VALUES (?, ?, ?, ?, ?, ?)",
            ("cam-01", "Camera", "Alex Student", "2026-10-09 09:00", "2026-10-09 15:00", 0),
        )
        database.execute("INSERT INTO reservations VALUES (?, ?)", ("cam-01", "2026-10-08"))
        database.execute(
            "INSERT INTO checkout_history VALUES (?, ?, ?, ?, ?)",
            ("cam-01", "Camera", "Checked out", "Alex Student", "2026-10-09 09:00"),
        )
        desktop = coolscaner.CheckInSystem.__new__(coolscaner.CheckInSystem)
        desktop.web_api_base_url = "https://inventory.example.test"
        desktop.db_lock = threading.Lock()
        desktop.database = database
        desktop.web_api_pending_lock = threading.Lock()
        desktop.web_api_pending_changes = {}
        desktop.web_api_cycle_running = False
        desktop.web_api_token = "test-token"
        desktop.web_api_inventory_id = self.owner_a["inventory_id"]
        desktop.ensure_web_api_session = Mock(return_value=True)

        def request_api(method, path, payload=None, headers=None):
            request_options = {"headers": self.headers(self.owner_a)}
            if payload is not None:
                request_options["json"] = payload
            response = self.client.request(method, path, **request_options)
            return response.status_code, response.json()

        desktop.web_api_request = request_api
        desktop.root = Mock()
        desktop.root.after.side_effect = lambda _delay, callback, *args: callback(*args)
        desktop.record_history = coolscaner.CheckInSystem.record_history.__get__(desktop)
        desktop.mark_recently_changed = coolscaner.CheckInSystem.mark_recently_changed.__get__(desktop)
        desktop.recently_changed_barcodes = {}
        desktop.refresh_items = Mock()
        desktop.start_web_service_sync_cycle = Mock()

        desktop.queue_web_service_checkout_sync("cam-01")
        self.assertEqual(desktop.web_api_pending_changes["cam-01"]["checked_out_by"], "Alex Student")
        desktop.run_web_service_sync_cycle()
        self.assertEqual(
            self.client.get("/api/items", headers=self.headers(self.owner_a)).json()[0]["checked_out_by"],
            "Alex Student",
        )

        checked_in = self.client.post("/api/items/cam-01/checkin", headers=self.headers(self.owner_a))
        self.assertEqual(checked_in.status_code, 200, checked_in.text)
        desktop.run_web_service_sync_cycle()
        item = database.execute("SELECT * FROM items WHERE barcode = 'cam-01'").fetchone()
        self.assertIsNone(item["checked_out_by"])
        self.assertEqual(
            [row[0] for row in database.execute("SELECT action FROM checkout_history ORDER BY rowid")],
            ["Checked out", "Checked in"],
        )
        self.assertEqual(database.execute("SELECT COUNT(*) FROM reservations").fetchone()[0], 0)
        database.close()


if __name__ == "__main__":
    unittest.main()
