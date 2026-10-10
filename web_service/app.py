from __future__ import annotations

import hashlib
import hmac
import os
import secrets
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from typing import Annotated, Literal

from fastapi import Depends, FastAPI, Header, HTTPException, Query, status
from fastapi.responses import FileResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, ConfigDict, EmailStr, Field
from sqlalchemy import Boolean, Date, DateTime, ForeignKey, Integer, String, UniqueConstraint, create_engine, delete, select
from sqlalchemy.exc import IntegrityError
from sqlalchemy.orm import DeclarativeBase, Mapped, Session, mapped_column, sessionmaker


BASE_DIR = Path(__file__).resolve().parent
DATABASE_URL = os.environ.get("DATABASE_URL", f"sqlite:///{BASE_DIR / 'inventory_dev.db'}")
if DATABASE_URL.startswith("postgres://"):
    DATABASE_URL = "postgresql+psycopg://" + DATABASE_URL.removeprefix("postgres://")
elif DATABASE_URL.startswith("postgresql://"):
    DATABASE_URL = "postgresql+psycopg://" + DATABASE_URL.removeprefix("postgresql://")
TOKEN_DAYS = int(os.environ.get("TOKEN_DAYS", "30"))

engine_options = {"pool_pre_ping": True}
if DATABASE_URL.startswith("sqlite"):
    engine_options["connect_args"] = {"check_same_thread": False}
engine = create_engine(DATABASE_URL, **engine_options)
SessionLocal = sessionmaker(bind=engine, expire_on_commit=False)


class Base(DeclarativeBase):
    pass


class User(Base):
    __tablename__ = "users"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    email: Mapped[str] = mapped_column(String(320), unique=True, index=True)
    password_hash: Mapped[str] = mapped_column(String(256))
    created_at: Mapped[datetime] = mapped_column(DateTime(timezone=True), default=lambda: datetime.now(timezone.utc))


class Inventory(Base):
    __tablename__ = "inventories"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    name: Mapped[str] = mapped_column(String(160))
    created_at: Mapped[datetime] = mapped_column(DateTime(timezone=True), default=lambda: datetime.now(timezone.utc))


class Membership(Base):
    __tablename__ = "memberships"
    __table_args__ = (UniqueConstraint("user_id", "inventory_id"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    inventory_id: Mapped[int] = mapped_column(ForeignKey("inventories.id", ondelete="CASCADE"), index=True)
    role: Mapped[str] = mapped_column(String(20), default="owner")


class LoginSession(Base):
    __tablename__ = "login_sessions"
    token_hash: Mapped[str] = mapped_column(String(64), primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    expires_at: Mapped[datetime] = mapped_column(DateTime(timezone=True), index=True)


class Item(Base):
    __tablename__ = "items"
    __table_args__ = (UniqueConstraint("inventory_id", "barcode"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    inventory_id: Mapped[int] = mapped_column(ForeignKey("inventories.id", ondelete="CASCADE"), index=True)
    barcode: Mapped[str] = mapped_column(String(160))
    name: Mapped[str] = mapped_column(String(240))
    category: Mapped[str | None] = mapped_column(String(160), nullable=True)
    unavailable: Mapped[bool] = mapped_column(Boolean, default=False)
    missing: Mapped[bool] = mapped_column(Boolean, default=False)
    checked_out_by: Mapped[str | None] = mapped_column(String(240), nullable=True)
    checked_out_at: Mapped[str | None] = mapped_column(String(32), nullable=True)
    checkout_due_at: Mapped[str | None] = mapped_column(String(32), nullable=True)
    checkout_late: Mapped[bool] = mapped_column(Boolean, default=False)


class Borrower(Base):
    __tablename__ = "borrowers"
    __table_args__ = (UniqueConstraint("inventory_id", "student_id"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    inventory_id: Mapped[int] = mapped_column(ForeignKey("inventories.id", ondelete="CASCADE"), index=True)
    full_name: Mapped[str] = mapped_column(String(240))
    student_id: Mapped[str] = mapped_column(String(160))
    email: Mapped[str] = mapped_column(String(320), default="")
    phone: Mapped[str] = mapped_column(String(80), default="")
    sms_opt_in: Mapped[bool] = mapped_column(Boolean, default=False)


class Reservation(Base):
    __tablename__ = "reservations"
    __table_args__ = (UniqueConstraint("inventory_id", "barcode", "reserved_date"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    inventory_id: Mapped[int] = mapped_column(ForeignKey("inventories.id", ondelete="CASCADE"), index=True)
    barcode: Mapped[str] = mapped_column(String(160), index=True)
    item_name: Mapped[str] = mapped_column(String(240))
    reserved_date: Mapped[date] = mapped_column(Date)
    borrower: Mapped[str] = mapped_column(String(240))
    created_at: Mapped[datetime] = mapped_column(DateTime(timezone=True), default=lambda: datetime.now(timezone.utc))
    status: Mapped[str] = mapped_column(String(24), default="Confirmed")


class CheckoutHistory(Base):
    __tablename__ = "checkout_history"
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    inventory_id: Mapped[int] = mapped_column(ForeignKey("inventories.id", ondelete="CASCADE"), index=True)
    barcode: Mapped[str] = mapped_column(String(160), index=True)
    item_name: Mapped[str] = mapped_column(String(240))
    action: Mapped[str] = mapped_column(String(80))
    borrower: Mapped[str | None] = mapped_column(String(240), nullable=True)
    timestamp: Mapped[str] = mapped_column(String(32))


class Category(Base):
    __tablename__ = "categories"
    __table_args__ = (UniqueConstraint("inventory_id", "name"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    inventory_id: Mapped[int] = mapped_column(ForeignKey("inventories.id", ondelete="CASCADE"), index=True)
    name: Mapped[str] = mapped_column(String(160))
    sort_order: Mapped[int] = mapped_column(Integer, default=0)


class BellPeriod(Base):
    __tablename__ = "bell_periods"
    __table_args__ = (UniqueConstraint("inventory_id", "period_date", "period_name"),)
    id: Mapped[int] = mapped_column(Integer, primary_key=True)
    inventory_id: Mapped[int] = mapped_column(ForeignKey("inventories.id", ondelete="CASCADE"), index=True)
    period_date: Mapped[date] = mapped_column(Date)
    period_name: Mapped[str] = mapped_column(String(160))
    start_time: Mapped[str] = mapped_column(String(5))
    end_time: Mapped[str] = mapped_column(String(5))


class Credentials(BaseModel):
    email: EmailStr
    password: str = Field(min_length=12, max_length=256)


class RegisterRequest(Credentials):
    inventory_name: str = Field(min_length=1, max_length=160)


class BookingRequest(BaseModel):
    barcode: str = Field(min_length=1, max_length=160)
    reserved_date: date
    borrower: str = Field(min_length=1, max_length=240)


class BookingBatchRequest(BaseModel):
    barcode: str = Field(min_length=1, max_length=160)
    reserved_dates: list[date] = Field(min_length=1, max_length=366)
    borrower: str = Field(min_length=1, max_length=240)


class CheckoutRequest(BaseModel):
    borrower: str = Field(min_length=1, max_length=240)
    due_at: str | None = Field(default=None, max_length=32)
    due_mode: Literal["period", "day", "multiple_days"] | None = None
    due_dates: list[date] = Field(default_factory=list, max_length=366)
    client_now: datetime | None = None


class ImportPayload(BaseModel):
    model_config = ConfigDict(extra="forbid")
    items: list[dict] = Field(default_factory=list)
    borrowers: list[dict] = Field(default_factory=list)
    reservations: list[dict] = Field(default_factory=list)
    history: list[dict] = Field(default_factory=list)
    categories: list[dict] = Field(default_factory=list)
    bell_periods: list[dict] = Field(default_factory=list)


class BorrowerAccountPayload(BaseModel):
    full_name: str = Field(min_length=1, max_length=240)
    student_id: str = Field(min_length=1, max_length=160)
    email: str = Field(default="", max_length=320)
    phone: str = Field(default="", max_length=80)
    sms_opt_in: bool = False


class BorrowerSyncPayload(BaseModel):
    borrowers: list[BorrowerAccountPayload]


def get_db():
    with SessionLocal() as db:
        yield db


def password_digest(password: str, salt: bytes | None = None) -> str:
    salt = salt or secrets.token_bytes(16)
    digest = hashlib.scrypt(password.encode("utf-8"), salt=salt, n=2**14, r=8, p=1)
    return f"{salt.hex()}${digest.hex()}"


def password_matches(password: str, encoded: str) -> bool:
    try:
        salt_text, digest_text = encoded.split("$", 1)
        expected = bytes.fromhex(digest_text)
        actual = hashlib.scrypt(password.encode("utf-8"), salt=bytes.fromhex(salt_text), n=2**14, r=8, p=1)
    except (ValueError, TypeError):
        return False
    return hmac.compare_digest(actual, expected)


def create_token(db: Session, user: User) -> str:
    token = secrets.token_urlsafe(40)
    db.add(LoginSession(
        token_hash=hashlib.sha256(token.encode()).hexdigest(),
        user_id=user.id,
        expires_at=datetime.now(timezone.utc) + timedelta(days=TOKEN_DAYS),
    ))
    db.commit()
    return token


def auth_context(
    authorization: Annotated[str | None, Header()] = None,
    x_inventory_id: Annotated[int | None, Header()] = None,
    db: Session = Depends(get_db),
) -> tuple[User, Membership, Session]:
    if not authorization or not authorization.startswith("Bearer "):
        raise HTTPException(status.HTTP_401_UNAUTHORIZED, "Sign in to continue")
    token = authorization.removeprefix("Bearer ").strip()
    login = db.get(LoginSession, hashlib.sha256(token.encode()).hexdigest())
    now = datetime.now(timezone.utc)
    if login is None or login.expires_at.replace(tzinfo=timezone.utc) <= now:
        raise HTTPException(status.HTTP_401_UNAUTHORIZED, "Session expired; sign in again")
    user = db.get(User, login.user_id)
    memberships = db.scalars(select(Membership).where(Membership.user_id == login.user_id)).all()
    membership = next((entry for entry in memberships if entry.inventory_id == x_inventory_id), None)
    if membership is None and x_inventory_id is None and len(memberships) == 1:
        membership = memberships[0]
    if user is None or membership is None:
        raise HTTPException(status.HTTP_403_FORBIDDEN, "No access to this inventory")
    return user, membership, db


Context = Annotated[tuple[User, Membership, Session], Depends(auth_context)]

app = FastAPI(title="Equipment Inventory API", version="1.0.0")
Base.metadata.create_all(engine)
app.mount("/static", StaticFiles(directory=BASE_DIR / "static"), name="static")


@app.get("/")
def home():
    return FileResponse(BASE_DIR / "static" / "index.html")


@app.get("/health")
def health():
    return {"status": "ok"}


@app.post("/api/auth/register", status_code=status.HTTP_201_CREATED)
def register(payload: RegisterRequest, db: Session = Depends(get_db)):
    email = str(payload.email).strip().casefold()
    user = User(email=email, password_hash=password_digest(payload.password))
    db.add(user)
    try:
        db.flush()
        inventory = Inventory(name=payload.inventory_name.strip())
        db.add(inventory)
        db.flush()
        db.add(Membership(user_id=user.id, inventory_id=inventory.id, role="owner"))
        db.commit()
    except IntegrityError:
        db.rollback()
        raise HTTPException(status.HTTP_409_CONFLICT, "An account with that email already exists")
    return {"token": create_token(db, user), "email": user.email, "inventory_id": inventory.id}


@app.post("/api/auth/login")
def login(payload: Credentials, db: Session = Depends(get_db)):
    user = db.scalar(select(User).where(User.email == str(payload.email).strip().casefold()))
    if user is None or not password_matches(payload.password, user.password_hash):
        raise HTTPException(status.HTTP_401_UNAUTHORIZED, "Email or password is incorrect")
    memberships = db.scalars(select(Membership).where(Membership.user_id == user.id)).all()
    return {
        "token": create_token(db, user),
        "email": user.email,
        "inventories": [
            {"id": membership.inventory_id, "name": db.get(Inventory, membership.inventory_id).name, "role": membership.role}
            for membership in memberships
        ],
    }


@app.post("/api/auth/logout")
def logout(
    context: Context,
    authorization: Annotated[str | None, Header()] = None,
):
    _user, _membership, db = context
    if authorization and authorization.startswith("Bearer "):
        token = authorization.removeprefix("Bearer ").strip()
        login = db.get(LoginSession, hashlib.sha256(token.encode()).hexdigest())
        if login:
            db.delete(login)
            db.commit()
    return {"ok": True}


@app.get("/api/me")
def me(context: Context):
    user, membership, db = context
    memberships = db.scalars(select(Membership).where(Membership.user_id == user.id)).all()
    return {
        "email": user.email,
        "active_inventory_id": membership.inventory_id,
        "inventories": [
            {"id": item.inventory_id, "name": db.get(Inventory, item.inventory_id).name, "role": item.role}
            for item in memberships
        ],
    }


def item_status(item: Item, today: date) -> str:
    if item.missing:
        return "Missing"
    if item.unavailable:
        return "Unavailable"
    if item.checked_out_by:
        return "Late" if item.checkout_late else "Checked out"
    if item.reservations and any(r.reserved_date == today and r.status == "Confirmed" for r in item.reservations):
        return "Reserved"
    return "Available"


@app.get("/api/items")
def list_items(context: Context, q: str = Query(default="", max_length=160)):
    _user, membership, db = context
    statement = select(Item).where(Item.inventory_id == membership.inventory_id)
    if q.strip():
        pattern = f"%{q.strip()}%"
        statement = statement.where((Item.barcode.ilike(pattern)) | (Item.name.ilike(pattern)) | (Item.category.ilike(pattern)))
    rows = db.scalars(statement.order_by(Item.category, Item.name)).all()
    today = date.today()
    result = []
    for item in rows:
        reservation = db.scalar(select(Reservation).where(
            Reservation.inventory_id == membership.inventory_id,
            Reservation.barcode == item.barcode,
            Reservation.reserved_date == today,
            Reservation.status == "Confirmed",
        ))
        result.append({
            "barcode": item.barcode, "name": item.name, "category": item.category,
            "status": "Missing" if item.missing else "Unavailable" if item.unavailable else
                "Late" if item.checked_out_by and item.checkout_late else
                "Checked out" if item.checked_out_by else "Reserved" if reservation else "Available",
            "checked_out_by": item.checked_out_by, "checked_out_at": item.checked_out_at,
            "checkout_due_at": item.checkout_due_at,
        })
    return result


@app.get("/api/borrowers")
def list_borrowers(context: Context):
    _user, membership, db = context
    return db.execute(
        select(Borrower.full_name).where(Borrower.inventory_id == membership.inventory_id).order_by(Borrower.full_name)
    ).scalars().all()


@app.put("/api/borrowers/sync")
def sync_borrowers(payload: BorrowerSyncPayload, context: Context):
    _user, membership, db = context
    if membership.role not in {"owner", "admin"}:
        raise HTTPException(status.HTTP_403_FORBIDDEN, "Only an inventory owner can sync borrower accounts")
    db.execute(delete(Borrower).where(Borrower.inventory_id == membership.inventory_id))
    for row in payload.borrowers:
        db.add(Borrower(
            inventory_id=membership.inventory_id, full_name=row.full_name,
            student_id=row.student_id, email=row.email, phone=row.phone, sms_opt_in=row.sms_opt_in,
        ))
    try:
        db.commit()
    except IntegrityError as error:
        db.rollback()
        raise HTTPException(status.HTTP_422_UNPROCESSABLE_ENTITY, "Borrower accounts could not be synced") from error
    return {"synced": len(payload.borrowers)}


def add_history(db: Session, inventory_id: int, item: Item, action: str, borrower: str | None) -> None:
    db.add(CheckoutHistory(
        inventory_id=inventory_id, barcode=item.barcode, item_name=item.name,
        action=action, borrower=borrower, timestamp=datetime.now().strftime("%Y-%m-%d %H:%M"),
    ))


def bell_due_time(db: Session, inventory_id: int, payload: CheckoutRequest) -> str | None:
    """Mirror the desktop rules; a workspace with no bell schedule has no due time."""
    if payload.due_mode is None:
        return payload.due_at
    if db.scalar(select(BellPeriod.id).where(BellPeriod.inventory_id == inventory_id).limit(1)) is None:
        return None
    now = (payload.client_now or datetime.now()).replace(tzinfo=None)

    def end_of_first_period_after(day: date) -> str:
        first = db.scalar(select(BellPeriod).where(
            BellPeriod.inventory_id == inventory_id, BellPeriod.period_date > day,
        ).order_by(BellPeriod.period_date, BellPeriod.start_time).limit(1))
        if first is None:
            raise HTTPException(status.HTTP_409_CONFLICT, "Add a bell schedule after the checkout day before checking out equipment")
        return f"{first.period_date.isoformat()} {first.end_time}"

    if payload.due_mode == "multiple_days":
        if not payload.due_dates:
            raise HTTPException(status.HTTP_422_UNPROCESSABLE_ENTITY, "Select the checkout days")
        return end_of_first_period_after(max(payload.due_dates))
    if payload.due_mode == "day":
        return end_of_first_period_after(now.date())
    current_time = now.strftime("%H:%M")
    periods = db.scalars(select(BellPeriod).where(
        BellPeriod.inventory_id == inventory_id, BellPeriod.period_date == now.date(),
    ).order_by(BellPeriod.start_time)).all()
    active = next((p for p in periods if p.start_time <= current_time < p.end_time), None)
    if active is None:
        raise HTTPException(status.HTTP_409_CONFLICT, "No active class period right now; choose Entire day or Multiple days")
    return f"{active.period_date.isoformat()} {active.end_time}"


@app.post("/api/items/{barcode}/checkout")
def checkout_item(barcode: str, payload: CheckoutRequest, context: Context):
    _user, membership, db = context
    item = db.scalar(select(Item).where(Item.inventory_id == membership.inventory_id, Item.barcode == barcode).with_for_update())
    if item is None:
        raise HTTPException(status.HTTP_404_NOT_FOUND, "Item not found")
    if item.unavailable or item.missing or item.checked_out_by:
        raise HTTPException(status.HTTP_409_CONFLICT, "Item is not available for checkout")
    reservation = db.scalar(select(Reservation).where(
        Reservation.inventory_id == membership.inventory_id, Reservation.barcode == barcode,
        Reservation.reserved_date == date.today(), Reservation.status == "Confirmed",
    ))
    if reservation and reservation.borrower.casefold() != payload.borrower.strip().casefold():
        raise HTTPException(status.HTTP_409_CONFLICT, f"Item is booked for {reservation.borrower}")
    due_at = bell_due_time(db, membership.inventory_id, payload)
    item.checked_out_by = payload.borrower.strip()
    item.checked_out_at = datetime.now().strftime("%Y-%m-%d %H:%M")
    item.checkout_due_at = due_at
    item.checkout_late = False
    add_history(db, membership.inventory_id, item, "Checked out", item.checked_out_by)
    db.commit()
    return {"ok": True, "barcode": item.barcode, "checked_out_by": item.checked_out_by, "checkout_due_at": item.checkout_due_at}


@app.post("/api/items/{barcode}/checkin")
def checkin_item(barcode: str, context: Context):
    _user, membership, db = context
    item = db.scalar(select(Item).where(Item.inventory_id == membership.inventory_id, Item.barcode == barcode).with_for_update())
    if item is None:
        raise HTTPException(status.HTTP_404_NOT_FOUND, "Item not found")
    if not item.checked_out_by:
        raise HTTPException(status.HTTP_409_CONFLICT, "Item is not checked out")
    borrower = item.checked_out_by
    item.checked_out_by = None
    item.checked_out_at = None
    item.checkout_due_at = None
    item.checkout_late = False
    add_history(db, membership.inventory_id, item, "Checked in", borrower)
    db.execute(delete(Reservation).where(
        Reservation.inventory_id == membership.inventory_id,
        Reservation.barcode == barcode,
        Reservation.reserved_date <= date.today(),
    ))
    db.commit()
    return {"ok": True, "barcode": item.barcode}


@app.get("/api/bookings")
def list_bookings(context: Context, start: date | None = None, end: date | None = None):
    _user, membership, db = context
    statement = select(Reservation).where(Reservation.inventory_id == membership.inventory_id)
    if start:
        statement = statement.where(Reservation.reserved_date >= start)
    if end:
        statement = statement.where(Reservation.reserved_date <= end)
    return [
        {"id": row.id, "barcode": row.barcode, "item_name": row.item_name,
         "reserved_date": row.reserved_date.isoformat(), "borrower": row.borrower,
         "status": row.status}
        for row in db.scalars(statement.order_by(Reservation.reserved_date, Reservation.item_name)).all()
    ]


@app.post("/api/bookings", status_code=status.HTTP_201_CREATED)
def create_booking(payload: BookingRequest, context: Context):
    _user, membership, db = context
    item = db.scalar(select(Item).where(Item.inventory_id == membership.inventory_id, Item.barcode == payload.barcode))
    if item is None:
        raise HTTPException(status.HTTP_404_NOT_FOUND, "Item not found")
    if item.unavailable:
        raise HTTPException(status.HTTP_409_CONFLICT, "Item is unavailable")
    existing = db.scalar(select(Reservation).where(
        Reservation.inventory_id == membership.inventory_id,
        Reservation.barcode == payload.barcode,
        Reservation.reserved_date == payload.reserved_date,
    ))
    if existing:
        raise HTTPException(status.HTTP_409_CONFLICT, f"Already booked for {existing.borrower}")
    reservation = Reservation(
        inventory_id=membership.inventory_id, barcode=item.barcode, item_name=item.name,
        reserved_date=payload.reserved_date, borrower=payload.borrower.strip(),
    )
    db.add(reservation)
    try:
        db.commit()
    except IntegrityError:
        db.rollback()
        raise HTTPException(status.HTTP_409_CONFLICT, "That item was booked by another user")
    return {"id": reservation.id, "status": reservation.status}


@app.post("/api/bookings/batch", status_code=status.HTTP_201_CREATED)
def create_booking_batch(payload: BookingBatchRequest, context: Context):
    _user, membership, db = context
    item = db.scalar(select(Item).where(
        Item.inventory_id == membership.inventory_id, Item.barcode == payload.barcode,
    ))
    if item is None:
        raise HTTPException(status.HTTP_404_NOT_FOUND, "Item not found")
    if item.unavailable:
        raise HTTPException(status.HTTP_409_CONFLICT, "Item is unavailable")

    dates = sorted(set(payload.reserved_dates))
    if len(dates) != len(payload.reserved_dates):
        raise HTTPException(status.HTTP_422_UNPROCESSABLE_ENTITY, "Choose each booking date only once")
    existing = db.scalars(select(Reservation).where(
        Reservation.inventory_id == membership.inventory_id,
        Reservation.barcode == item.barcode,
        Reservation.reserved_date.in_(dates),
    )).all()
    if existing:
        conflict = min(existing, key=lambda row: row.reserved_date)
        raise HTTPException(
            status.HTTP_409_CONFLICT,
            f"Already booked for {conflict.borrower} on {conflict.reserved_date.isoformat()}",
        )

    reservations = [Reservation(
        inventory_id=membership.inventory_id, barcode=item.barcode, item_name=item.name,
        reserved_date=reserved_date, borrower=payload.borrower.strip(),
    ) for reserved_date in dates]
    db.add_all(reservations)
    try:
        db.commit()
    except IntegrityError as error:
        db.rollback()
        raise HTTPException(status.HTTP_409_CONFLICT, "One or more selected dates were booked by another user") from error
    return [
        {"id": row.id, "reserved_date": row.reserved_date.isoformat(), "status": row.status}
        for row in reservations
    ]


@app.delete("/api/bookings/{booking_id}")
def delete_booking(booking_id: int, context: Context):
    _user, membership, db = context
    booking = db.scalar(select(Reservation).where(
        Reservation.id == booking_id, Reservation.inventory_id == membership.inventory_id,
    ))
    if booking is None:
        raise HTTPException(status.HTTP_404_NOT_FOUND, "Booking not found")
    db.delete(booking)
    db.commit()
    return {"ok": True}


@app.get("/api/history")
def list_history(context: Context, limit: int = Query(default=200, ge=1, le=1000)):
    _user, membership, db = context
    rows = db.scalars(select(CheckoutHistory).where(
        CheckoutHistory.inventory_id == membership.inventory_id,
    ).order_by(CheckoutHistory.id.desc()).limit(limit)).all()
    return [
        {"timestamp": row.timestamp, "action": row.action, "barcode": row.barcode,
         "item_name": row.item_name, "borrower": row.borrower}
        for row in rows
    ]


@app.post("/api/import/sqlite")
def import_sqlite(payload: ImportPayload, context: Context):
    _user, membership, db = context
    if membership.role not in {"owner", "admin"}:
        raise HTTPException(status.HTTP_403_FORBIDDEN, "Only an inventory owner can import data")
    inventory_id = membership.inventory_id
    existing = db.scalar(select(Item.id).where(Item.inventory_id == inventory_id).limit(1))
    if existing is not None:
        raise HTTPException(status.HTTP_409_CONFLICT, "Import is allowed only into an empty inventory")
    try:
        for row in payload.categories:
            db.add(Category(inventory_id=inventory_id, name=str(row["name"]), sort_order=int(row.get("sort_order", 0))))
        for row in payload.items:
            db.add(Item(
                inventory_id=inventory_id, barcode=str(row["barcode"]), name=str(row["name"]),
                category=row.get("category"), unavailable=bool(row.get("unavailable", 0)),
                missing=bool(row.get("missing", 0)), checked_out_by=row.get("checked_out_by"),
                checked_out_at=row.get("checked_out_at"), checkout_due_at=row.get("checkout_due_at"),
                checkout_late=bool(row.get("checkout_late", 0)),
            ))
        for row in payload.borrowers:
            db.add(Borrower(
                inventory_id=inventory_id, full_name=str(row["full_name"]), student_id=str(row["student_id"]),
                email=str(row.get("email", "")), phone=str(row.get("phone", "")),
                sms_opt_in=bool(row.get("sms_opt_in", 0)),
            ))
        for row in payload.reservations:
            db.add(Reservation(
                inventory_id=inventory_id, barcode=str(row["barcode"]), item_name=str(row["item_name"]),
                reserved_date=date.fromisoformat(str(row["reserved_date"])), borrower=str(row["borrower"]),
                created_at=datetime.fromisoformat(str(row["created_at"])), status=str(row.get("status", "Confirmed")),
            ))
        for row in payload.history:
            db.add(CheckoutHistory(
                inventory_id=inventory_id, barcode=str(row["barcode"]), item_name=str(row["item_name"]),
                action=str(row["action"]), borrower=row.get("borrower"), timestamp=str(row["timestamp"]),
            ))
        for row in payload.bell_periods:
            db.add(BellPeriod(
                inventory_id=inventory_id, period_date=date.fromisoformat(str(row["period_date"])),
                period_name=str(row["period_name"]), start_time=str(row["start_time"]), end_time=str(row["end_time"]),
            ))
        db.commit()
    except (KeyError, ValueError, IntegrityError) as error:
        db.rollback()
        raise HTTPException(status.HTTP_422_UNPROCESSABLE_ENTITY, f"Import was not applied: {error}")
    return {
        "imported": {
            "items": len(payload.items), "borrowers": len(payload.borrowers),
            "reservations": len(payload.reservations), "history": len(payload.history),
            "categories": len(payload.categories), "bell_periods": len(payload.bell_periods),
        }
    }
