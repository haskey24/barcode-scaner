# Equipment Ledger Web Service

This service is the first cloud/web replacement component for the desktop app's Google Sheets mirror. It provides separate account-owned inventories, a browser inventory page, checkout/check-in, bookings, history, and a one-time SQLite import endpoint.

## Local run

From the repository root, install the separate web dependencies and start the API:

```sh
python3 -m pip install -r web_service/requirements.txt
cd web_service
uvicorn app:app --reload
```

Open `http://127.0.0.1:8000`. Local development uses `web_service/inventory_dev.db`; set `DATABASE_URL` to use another database. The first person to register creates an owner account and a private inventory.

## Hosted deployment

The root `render.yaml` describes a Render web service and PostgreSQL database. In Render, create a Blueprint from this repository and review the service/database plans and current pricing before approving. When the deployment is healthy, open its `onrender.com` URL and register the inventory owner.

Use HTTPS in production. Keep the hosted PostgreSQL database private; only the API service should connect to it. Back up the database regularly. The API currently uses SQLAlchemy `create_all` for its initial schema; add managed schema migrations before evolving a production database.

## Import existing local data

1. Stop the desktop app so the database is not being changed during the import.
2. Make a separate backup copy of `check_in_system.db`.
3. Register an owner account on the deployed website.
4. From the repository root, run the importer, substituting the deployed service URL and owner email:

```sh
python3 web_service/import_sqlite.py check_in_system.db \
  --api-url https://YOUR-SERVICE.onrender.com \
  --email owner@example.com
```

The script prompts for the account password without echoing it. It imports items, borrower accounts, categories, reservations, checkout history, and bell periods. Import is accepted only into an empty inventory and never changes the source SQLite database. Local item photo files and local notification-provider settings are not uploaded by this initial importer.

Check item counts, current checkout statuses, booking dates, and recent history on the website before relying on the imported inventory.

## API overview

- `POST /api/auth/register` and `POST /api/auth/login`
- `GET /api/items`, `POST /api/items/{barcode}/checkout`, `POST /api/items/{barcode}/checkin`
- `GET /api/bookings`, `POST /api/bookings`, `DELETE /api/bookings/{id}`
- `GET /api/history`
- `POST /api/import/sqlite` (owner-only, empty inventory only)

Authenticated API requests use a bearer session token and an `X-Inventory-ID`; membership is checked before any inventory-scoped query. Browser sessions are held in tab-scoped session storage and can be revoked by signing out.

## Desktop app migration

The desktop app can now target the hosted service by passing `--api-url`, `--api-email`, and `--api-password` at launch. When those values are present, `coolscaner.py` authenticates against the API and imports the current local inventory into an empty hosted inventory instead of running the legacy Google Sheets sync path. If that hosted inventory already contains data, the desktop app synchronizes its borrower account roster separately without changing hosted inventory items.

After startup, desktop checkouts and check-ins are sent to the hosted API in the background, and the desktop polls hosted checkout state every 10 seconds so changes made on the web page appear locally. Keep the desktop app running for automatic updates.

API settings can also be configured from the desktop app: enter Admin Mode, choose **Web sync setup**, enter the server URL and web account credentials, test the connection, select the inventory workspace, then choose **Save and sync**. The server URL, email, and selected inventory are stored with the local app settings; the password is stored in macOS Keychain.

The local SQLite database remains the desktop app’s operating state, but the hosted service can be used as the shared inventory source for a new install or a migration from a legacy workstation. Desktop borrower accounts remain distinct from web owner sign-in accounts and provide the names shown in checkout and booking dropdowns.
