
import os
import json
import time
from pathlib import Path
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

import requests
import pyotp
from dotenv import load_dotenv
from SmartApi import SmartConnect

load_dotenv()

IST = ZoneInfo("Asia/Kolkata")
BASE_DIR = Path(__file__).resolve().parent

INSTRUMENT_URL = (
    "https://margincalculator.angelone.in/"
    "OpenAPI_File/files/OpenAPIScripMaster.json"
)
INSTRUMENT_FILE = BASE_DIR / "angel_instruments.json"

# Conservative request pacing. We can tune this after testing.
QUOTE_BATCH_SIZE = 50
QUOTE_REQUEST_DELAY = 1.1

_smart_api = None
_instruments = None
_last_quote_request = 0.0
# Cache hourly candles to avoid repeatedly requesting the same data.
_CANDLE_CACHE = {}
_CANDLE_CACHE_TTL = 300
_CANDLE_CACHE_LOCK = __import__("threading").Lock()

_LAST_CANDLE_REQUEST = 0.0
_CANDLE_REQUEST_LOCK = __import__("threading").Lock()
_CANDLE_REQUEST_DELAY = 1.2

def connect_angel():
    """Log in to Angel One using credentials stored in .env."""
    global _smart_api

    if _smart_api is not None:
        return _smart_api

    settings = {
        "ANGEL_API_KEY": os.getenv("ANGEL_API_KEY"),
        "ANGEL_CLIENT_ID": os.getenv("ANGEL_CLIENT_ID"),
        "ANGEL_PIN": os.getenv("ANGEL_PIN"),
        "ANGEL_TOTP_SECRET": os.getenv("ANGEL_TOTP_SECRET"),
    }

    missing = [
        key for key, value in settings.items() if not value
    ]

    if missing:
        raise RuntimeError(
            "Missing .env settings: " + ", ".join(missing)
        )

    api = SmartConnect(api_key=settings["ANGEL_API_KEY"])
    otp = pyotp.TOTP(settings["ANGEL_TOTP_SECRET"]).now()

    response = api.generateSession(
        settings["ANGEL_CLIENT_ID"],
        settings["ANGEL_PIN"],
        otp,
    )

    if not response or not response.get("status"):
        raise RuntimeError(
            "Angel One login failed: "
            + str(response.get("message", "Unknown error")
                  if response else "No response")
        )

    _smart_api = api
    print("[ANGEL] Login successful.")
    return _smart_api


def load_instruments(force_download=False):
    """
    Load the Angel One instrument master.
    Keep NSE cash-equity instruments only for the initial scanners.
    """
    global _instruments

    if _instruments is not None and not force_download:
        return _instruments

    records = None

    if INSTRUMENT_FILE.exists() and not force_download:
        try:
            with open(INSTRUMENT_FILE, "r", encoding="utf-8") as file:
                records = json.load(file)
        except (OSError, json.JSONDecodeError):
            records = None

    if not isinstance(records, list):
        response = requests.get(INSTRUMENT_URL, timeout=45)
        response.raise_for_status()
        records = response.json()

        if not isinstance(records, list):
            raise RuntimeError(
                "Angel One instrument master was not a list."
            )

        temporary_file = INSTRUMENT_FILE.with_suffix(".tmp")
        with open(temporary_file, "w", encoding="utf-8") as file:
            json.dump(records, file)
        temporary_file.replace(INSTRUMENT_FILE)

    print("[ANGEL DEBUG] Records loaded:", len(records))
    print("[ANGEL DEBUG] First record:", records[0] if records else None)
    print(
        "[ANGEL DEBUG] Segment counts:",
        {
            segment: sum(
                1 for item in records
                if isinstance(item, dict)
                and str(item.get("exch_seg", "")).strip().lower() == segment
            )
            for segment in {
                str(item.get("exch_seg", "")).strip().lower()
                for item in records
                if isinstance(item, dict)
            }
        }
    )
    equity_instruments = {}

    for item in records:
        if not isinstance(item, dict):
            continue

        segment = str(item.get("exch_seg", "")).strip().lower()
        symbol = str(item.get("symbol", "")).strip().upper()
        token = str(item.get("token", "")).strip()
        name = str(item.get("name", "")).strip()

        if segment not in ("nse_cm", "nse"):
            continue

        if not symbol.endswith("-EQ") or not token:
            continue

        stock_symbol = symbol[:-3]

        equity_instruments[stock_symbol] = {
            "symbol": stock_symbol,
            "trading_symbol": symbol,
            "token": token,
            "company": name or stock_symbol,
            "exchange": "NSE",
        }

    if not equity_instruments:
        raise RuntimeError(
            "No NSE cash-equity instruments found in the "
            "Angel One instrument master."
        )

    _instruments = equity_instruments
    print(
        f"[ANGEL] Loaded {len(_instruments)} NSE equity instruments."
    )
    return _instruments


def get_instrument(symbol):
    """Return the instrument metadata for a stock symbol."""
    instruments = load_instruments()
    return instruments.get(str(symbol).strip().upper())


def get_nse_equity_universe():
    """Return all mapped NSE cash-equity instruments."""
    return list(load_instruments().values())


def _pace_quote_requests():
    global _last_quote_request

    elapsed = time.monotonic() - _last_quote_request
    wait = QUOTE_REQUEST_DELAY - elapsed

    if wait > 0:
        time.sleep(wait)

    _last_quote_request = time.monotonic()


def get_market_quotes(instruments):
    """
    Fetch LTP quotes in batches.
    Input: instrument dictionaries from get_nse_equity_universe().
    Output: normalized stock rows for scanner calculations.
    """
    api = connect_angel()
    rows = []

    valid = [
        item for item in instruments
        if item.get("token") and item.get("symbol")
    ]

    for start in range(0, len(valid), QUOTE_BATCH_SIZE):
        batch = valid[start:start + QUOTE_BATCH_SIZE]
        tokens = [str(item["token"]) for item in batch]

        _pace_quote_requests()

        response = api.getMarketData(
            "FULL",
            {"NSE": tokens},
        )

        if not response or not response.get("status"):
            message = (
                response.get("message", "Unknown error")
                if response else "No response"
            )
            print(f"[ANGEL] Quote batch failed: {message}")
            continue

        data = response.get("data") or {}
        fetched = data.get("fetched") or []

        for quote in fetched:
            if not isinstance(quote, dict):
                continue

            trading_symbol = str(
                quote.get("tradingSymbol") or ""
            ).strip().upper()

            symbol = (
                trading_symbol[:-3]
                if trading_symbol.endswith("-EQ")
                else trading_symbol
            )

            if not symbol:
                continue

            ltp = float(quote.get("ltp") or 0)
            previous_close = float(quote.get("close") or 0)

            change = (
                ((ltp - previous_close) / previous_close) * 100
                if previous_close > 0 else 0
            )

            instrument = get_instrument(symbol) or {}

            rows.append({
                "symbol": symbol,
                "company": instrument.get("company", symbol),
                "price": round(ltp, 2),
                "previous_close": round(previous_close, 2),
                "change": round(change, 2),
                "open": float(quote.get("open") or 0),
                "high": float(quote.get("high") or 0),
                "low": float(quote.get("low") or 0),
                "volume": int(float(quote.get("tradeVolume") or 0)),
                "token": str(quote.get("symbolToken") or ""),
                "exchange": "NSE",
            })

    print(f"[ANGEL] Received quotes for {len(rows)} stocks.")
    return rows



def get_hourly_candles(symbol_token, days=5):
    """Fetch hourly candles with cache, serialized pacing, and validation."""
    global _LAST_CANDLE_REQUEST

    token = str(symbol_token).strip()
    if not token:
        return []

    cache_key = (token, days)
    now_ts = time.time()

    with _CANDLE_CACHE_LOCK:
        cached = _CANDLE_CACHE.get(cache_key)
        if cached and now_ts - cached["time"] < _CANDLE_CACHE_TTL:
            return cached["data"]

    # Serialize candle requests so concurrent Flask requests cannot
    # overwhelm the Angel One candle endpoint.
    with _CANDLE_REQUEST_LOCK:
        elapsed = time.monotonic() - _LAST_CANDLE_REQUEST
        wait = _CANDLE_REQUEST_DELAY - elapsed
        if wait > 0:
            time.sleep(wait)

        _LAST_CANDLE_REQUEST = time.monotonic()

        now = datetime.now(IST)
        start = now - timedelta(days=days)

        response = connect_angel().getCandleData({
            "exchange": "NSE",
            "symboltoken": token,
            "interval": "ONE_HOUR",
            "fromdate": start.strftime("%Y-%m-%d %H:%M"),
            "todate": now.strftime("%Y-%m-%d %H:%M"),
        })

    if not response or not response.get("status"):
        message = (
            response.get("message", "Unknown error")
            if response else "No response"
        )
        raise RuntimeError(f"Angel One candle request failed: {message}")

    candles = response.get("data") or []
    if not isinstance(candles, list):
        return []

    valid = []
    for candle in candles:
        if not isinstance(candle, (list, tuple)) or len(candle) < 6:
            continue
        try:
            timestamp = datetime.fromisoformat(
                str(candle[0]).replace("Z", "+00:00")
            )
            if timestamp.tzinfo is None:
                timestamp = timestamp.replace(tzinfo=IST)
            else:
                timestamp = timestamp.astimezone(IST)

            close = float(candle[4])
            volume = float(candle[5])

            if close <= 0:
                continue

            valid.append([
                timestamp.isoformat(),
                float(candle[1]),
                float(candle[2]),
                float(candle[3]),
                close,
                volume,
            ])
        except (ValueError, TypeError, IndexError):
            continue

    valid.sort(key=lambda row: row[0])

    # Do not cache failures or empty responses.
    if valid:
        with _CANDLE_CACHE_LOCK:
            _CANDLE_CACHE[cache_key] = {
                "time": time.time(),
                "data": valid,
            }

    return valid




if __name__ == "__main__":
    try:
        instruments = get_nse_equity_universe()
        print(f"[ANGEL] Instrument master working.")
        print(f"[ANGEL] Total NSE cash-equity stocks: {len(instruments)}")

        api = connect_angel()
        print("[ANGEL] Login successful.")
        print("[ANGEL] API is ready for dashboard use.")

    except Exception as exc:
        error_message = f"{type(exc).__name__}: {exc}"
        print(f"[ANGEL ERROR]: {error_message}")

        secret_moves_result_cache[cache_key] = {
            "time": time.time(),
            "payload": {
                "timeframe": timeframe,
                "direction": direction,
                "count": 0,
                "results": [],
                "error": error_message,
            },
        }
