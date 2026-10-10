"""Import one existing Equipment Check-In SQLite database into a new cloud inventory."""

from __future__ import annotations

import argparse
import getpass
import json
import sqlite3
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen


def rows(db: sqlite3.Connection, query: str) -> list[dict]:
    try:
        return [dict(row) for row in db.execute(query).fetchall()]
    except sqlite3.OperationalError as error:
        if "no such table" in str(error).casefold():
            return []
        raise


def post_json(url: str, payload: dict, token: str | None = None, inventory_id: int | None = None) -> dict:
    headers = {"Content-Type": "application/json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    if inventory_id is not None:
        headers["X-Inventory-ID"] = str(inventory_id)
    request = Request(url, data=json.dumps(payload).encode("utf-8"), headers=headers, method="POST")
    try:
        with urlopen(request, timeout=45) as response:
            return json.loads(response.read().decode("utf-8"))
    except HTTPError as error:
        detail = error.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"Server returned HTTP {error.code}: {detail}") from error
    except URLError as error:
        raise RuntimeError(f"Could not connect to API: {error.reason}") from error


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database", type=Path, help="Path to the local check_in_system.db file")
    parser.add_argument("--api-url", required=True, help="Base URL, e.g. https://inventory.example.com")
    parser.add_argument("--email", required=True, help="Owner account email on the new service")
    parser.add_argument("--inventory-id", type=int, help="Workspace ID when the account has multiple inventories")
    args = parser.parse_args()
    if not args.database.is_file():
        parser.error(f"SQLite database not found: {args.database}")

    password = getpass.getpass("Cloud account password: ")
    base_url = args.api_url.rstrip("/")
    auth = post_json(f"{base_url}/api/auth/login", {"email": args.email, "password": password})
    token = auth["token"]
    inventories = auth.get("inventories", [])
    inventory_id = args.inventory_id
    if inventory_id is None:
        if len(inventories) != 1:
            parser.error("This account has multiple inventories; provide --inventory-id.")
        inventory_id = int(inventories[0]["id"])

    with sqlite3.connect(args.database) as db:
        db.row_factory = sqlite3.Row
        payload = {
            "items": rows(db,
                "SELECT barcode, name, category, unavailable, missing, checked_out_by, checked_out_at, "
                "checkout_due_at, checkout_late FROM items"),
            "borrowers": rows(db,
                "SELECT full_name, student_id, email, phone, sms_opt_in FROM accounts"),
            "reservations": rows(db,
                "SELECT barcode, item_name, reserved_date, borrower, created_at, status FROM reservations"),
            "history": rows(db,
                "SELECT barcode, item_name, action, borrower, timestamp FROM checkout_history ORDER BY id"),
            "categories": rows(db, "SELECT name, sort_order FROM categories ORDER BY sort_order, name"),
            "bell_periods": rows(db,
                "SELECT period_date, period_name, start_time, end_time FROM bell_periods"),
        }

    result = post_json(
        f"{base_url}/api/import/sqlite", payload, token=token, inventory_id=inventory_id,
    )
    print("Import complete:")
    for table, count in result["imported"].items():
        print(f"  {table}: {count}")
    print("The source SQLite database was not changed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
