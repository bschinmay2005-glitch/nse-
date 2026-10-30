from datetime import date, timedelta
from nse import NSE
import angel_api
import threading
import time
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import requests
import csv
from io import StringIO
from flask import Flask, jsonify, render_template, request

app = Flask(__name__)
BASE_DIR = Path(__file__).resolve().parent

NSE_HOME = "https://www.nseindia.com/"
NSE_API = "https://www.nseindia.com/api"

URLS = {
    "market": f"{NSE_API}/marketStatus",
    "volume": f"{NSE_API}/live-analysis-volume-gainers",
    "gainers": f"{NSE_API}/live-analysis-variations?index=gainers",
    "losers": f"{NSE_API}/live-analysis-variations?index=losers",
    "indices": f"{NSE_API}/allIndices",

}




REFRESH_SECONDS = 20
IST = ZoneInfo("Asia/Kolkata")

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/130.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": NSE_HOME,
}

data_lock = threading.Lock()
refresh_lock = threading.Lock()

market_data = {
    "market_status": "Connecting to NSE",
    "trade_date": None,
    "last_updated": None,
    "last_error": None,
    "volume_gainers": [],
    "price_gainers": [],
    "price_losers": [],
    "price_gainers_losers": [],
    "price_volume_gainers": [],
    "relative_moves": [],
}



# Store recent observations for trend highlighting.
TREND_WINDOW = 5
TREND_HISTORY = {}
# Cache verified stock-to-index membership to reduce NSE requests.
SECTOR_MEMBERSHIP_CACHE = {}
SECTOR_INDEX_MEMBERS_CACHE = {}
STOCK_SECTOR_MAP = {}
SECTOR_CACHE_TTL = 24 * 60 * 60
MAX_NEW_SECTOR_LOOKUPS_PER_REFRESH = 8
SECTOR_FETCH_CURSOR = 0

# Live NSE index membership used for market-cap filters.
MARKET_CAP_INDEXES = {
    "large": "NIFTY 100",
    "mid": "NIFTY MIDCAP 150",
    "small": "NIFTY SMALLCAP 250",
}

MARKET_CAP_CACHE_TTL = 15 * 60  # Refresh membership every 15 minutes
MARKET_CAP_INDEX_CACHE = {}
INCLUDE_MICRO_CAPS = False  # False = hide penny/micro-cap stocks
MAX_POOL = 300  # max stocks per list taken from Nifty 500
PV_MIN_RVOL = 0.8
HOURLY_HISTORY = {}      # symbol -> {"time": ..., "data": [candles]}
HOURLY_FAILED = {}       # symbol -> time of last failed fetch
HOURLY_TOP_N = 100       # how many most-traded stocks to keep hourly data for
HOURLY_CALL_GAP = 0.4    # seconds between Angel One calls (rate limit)
SECRET_MAX_CANDIDATES = 80           # stocks checked per Secret Gainers & Losers view
SECRET_NEW_FETCHES_PER_REQUEST = 10  # new history downloads allowed per click   # volume must reach 80% of the time-adjusted weekly average
AVG_VOL_CACHE = {}
AVG_VOL_LOOKUPS_PER_REFRESH = 0   # lookups now done by background worker
UNIVERSE_SYMBOLS = []             # filled each refresh, used by the worker
AVG_VOL_FILE = BASE_DIR / "avg_volume_cache.json"
NIFTY_CSV_URLS = {
    "large": "https://www.niftyindices.com/IndexConstituent/ind_nifty100list.csv",
    "mid":   "https://www.niftyindices.com/IndexConstituent/ind_niftymidcap150list.csv",
    "small": "https://www.niftyindices.com/IndexConstituent/ind_niftysmallcap250list.csv",
}


def update_trend_history(rows):
    seen = set()

    for row in rows:
        symbol = row.get("symbol")
        if not symbol or symbol in seen:
            continue

        seen.add(symbol)

        history = TREND_HISTORY.setdefault(symbol, [])
        history.append({
            "price": row.get("price"),
            "volume": row.get("volume"),
        })
        TREND_HISTORY[symbol] = history[-TREND_WINDOW:]


def get_trend_flags(symbol):
    history = TREND_HISTORY.get(symbol, [])

    result = {
        "price_trend": "neutral",
        "volume_trend": "neutral",
        "trend_signal": "neutral",
    }

    if len(history) < TREND_WINDOW:
        return result

    prices = [item["price"] for item in history]
    volumes = [item["volume"] for item in history]

    
    price_changes = [
        prices[i] - prices[i - 1]
        for i in range(1, len(prices))
    ]

    up_moves = sum(change > 0 for change in price_changes)
    down_moves = sum(change < 0 for change in price_changes)

    if prices[-1] > prices[0] and up_moves >= 3:
        result["price_trend"] = "bullish"
    elif prices[-1] < prices[0] and down_moves >= 3:
        result["price_trend"] = "bearish"


    # NSE volume is cumulative during the trading day.
    if all(volumes[i] > volumes[i - 1] for i in range(1, len(volumes))):
        result["volume_trend"] = "increasing"

    if result["volume_trend"] == "increasing":
        if result["price_trend"] == "bullish":
            result["trend_signal"] = "bullish"
        elif result["price_trend"] == "bearish":
            result["trend_signal"] = "bearish"

    return result



def to_number(value, default=0.0):
    if value is None or value == "":
        return default

    try:
        text = str(value).replace(",", "").replace("%", "").strip()
        if text.lower() in {"-", "—", "na", "n/a", "none", "null"}:
            return default
        return float(text)
    except (ValueError, TypeError):
        return default



def rounded(value, decimals=2):
    return round(to_number(value), decimals)


def fetch_json(session, url):
    response = session.get(url, timeout=15)
    response.raise_for_status()
    return response.json()



def create_nse_session():
    # The NSE homepage returns 403 in this environment,
    # but the market-status API responds successfully.
    # Try the API endpoints directly without the homepage request.
    session = requests.Session()
    session.headers.update(HEADERS)
    return session



def get_market_status(payload):
    states = payload.get("marketState", [])

    if not isinstance(states, list):
        return "Unknown", None

    for item in states:
        if not isinstance(item, dict):
            continue

        market_name = str(item.get("market", "")).lower()

        if "capital market" in market_name:
            return (
                item.get("marketStatus", "Unknown"),
                item.get("tradeDate"),
            )

    for item in states:
        if isinstance(item, dict) and item.get("marketStatus"):
            return item["marketStatus"], item.get("tradeDate")

    return "Unknown", None




def variation_rows(payload):
    """Extract stock rows from NSE's variation response."""
    if not isinstance(payload, dict):
        return []

    # allSec is NSE's all-securities list.
    all_sec = payload.get("allSec")

    if isinstance(all_sec, dict):
        rows = all_sec.get("data", [])
        if isinstance(rows, list) and rows:
            return rows

    if isinstance(all_sec, list) and all_sec:
        return all_sec

    # Fallback: combine the available index/security groups.
    combined = []
    seen = set()

    for group_name in (
        "NIFTY",
        "BANKNIFTY",
        "NIFTYNEXT50",
        "SecGtr20",
        "SecLwr20",
        "FOSec",
    ):
        group = payload.get(group_name, {})
        rows = group.get("data", []) if isinstance(group, dict) else group

        if not isinstance(rows, list):
            continue

        for row in rows:
            if not isinstance(row, dict):
                continue

            symbol = str(row.get("symbol") or "").strip().upper()
            if symbol and symbol not in seen:
                seen.add(symbol)
                combined.append(row)

    return combined




def normalize_index_changes(payload):
    """Return index names and their percentage changes."""
    index_changes = {}

    if not isinstance(payload, dict):
        return index_changes

    rows = payload.get("data", [])

    if not isinstance(rows, list):
        return index_changes

    for row in rows:
        if not isinstance(row, dict):
            continue

        name = row.get("index") or row.get("indexName")
        change = row.get("percentChange")

        if change is None:
            change = row.get("variation")

        try:
            if name is not None and change is not None:
                index_changes[str(name).strip().upper()] = float(change)
        except (TypeError, ValueError):
            continue

    return index_changes



def fetch_sector_constituents(session, index_name):
    """Fetch live constituent prices and percentage changes."""
    api_url = "https://www.nseindia.com/api/equity-stock-indices"

    response = session.get(
        api_url,
        params={"index": index_name},
        headers={"Referer": "https://www.nseindia.com/"},
        timeout=8,
    )
    response.raise_for_status()

    payload = response.json()
    rows = payload.get("data", [])

    if not isinstance(rows, list):
        return []

    result = []

    for item in rows:
        if not isinstance(item, dict):
            continue

        symbol = str(item.get("symbol") or "").strip().upper()

        # Ignore the index's own summary row.
        if not symbol or symbol.startswith("NIFTY "):
            continue

        change = item.get("pChange")
        if change is None:
            change = item.get("perChange")

        price = item.get("lastPrice")
        if price is None:
            price = item.get("ltp")

        if change is None:
            continue

        result.append({
            "symbol": symbol,
            "company": item.get("meta", {}).get("companyName", symbol)
                if isinstance(item.get("meta"), dict) else symbol,
            "price": rounded(price),
            "change": rounded(change),
            "volume": int(to_number(item.get("totalTradedVolume"))),
        })

    return result


def fetch_market_cap_symbols(session, index_name, category=None):
    """Fetch index members: NSE API first (2 tries), then niftyindices CSV."""
    for attempt in range(2):
        try:
            payload = fetch_json(
                session,
                f"{NSE_API}/equity-stock-indices?index={requests.utils.quote(index_name)}",
            )
            symbols = {
                str(i.get("symbol") or "").strip().upper()
                for i in payload.get("data", [])
                if isinstance(i, dict)
                and i.get("symbol")
                and not str(i["symbol"]).upper().startswith("NIFTY ")
            }
            if symbols:
                return symbols
        except Exception as exc:
            print(f"[MARKET CAP] NSE API attempt {attempt + 1} failed for {index_name}: {exc}")
            time.sleep(1)

    url = NIFTY_CSV_URLS.get(category)
    if url:
        try:
            r = requests.get(url, headers=HEADERS, timeout=15)
            r.raise_for_status()
            reader = csv.DictReader(StringIO(r.text))
            symbols = {
                (row.get("Symbol") or "").strip().upper()
                for row in reader if row.get("Symbol")
            }
            print(f"[MARKET CAP] {index_name}: {len(symbols)} from CSV fallback")
            return symbols
        except Exception as exc:
            print(f"[MARKET CAP] CSV fallback failed for {index_name}: {exc}")

    return set()

def day_fraction():
    """Fraction of the trading session elapsed (9:15-15:30 IST)."""
    now = datetime.now(IST)
    if now.weekday() >= 5:
        return 1.0
    open_t = now.replace(hour=9, minute=15, second=0, microsecond=0)
    close_t = now.replace(hour=15, minute=30, second=0, microsecond=0)
    if now <= open_t or now >= close_t:
        return 1.0
    frac = (now - open_t).total_seconds() / (close_t - open_t).total_seconds()
    return max(frac, 0.15)

def get_universe_rows(session):
    """All Nifty 500 stocks with live price/change/volume."""
    try:
        rows = fetch_sector_constituents(session, "NIFTY 500")
        if rows:
            print(f"[UNIVERSE] NIFTY 500: {len(rows)} stocks")
            return rows
    except Exception as exc:
        print(f"[UNIVERSE] NIFTY 500 failed: {exc}")

    # Fallback: combine the three cap indexes
    rows = []
    for index_name in MARKET_CAP_INDEXES.values():
        try:
            rows += fetch_sector_constituents(session, index_name)
        except Exception as exc:
            print(f"[UNIVERSE] {index_name} failed: {exc}")
    print(f"[UNIVERSE] fallback: {len(rows)} stocks")
    return rows

def get_live_market_cap_categories(session):
    """Build a symbol-to-category map from live NSE index membership."""
    now = time.time()

    for category, index_name in MARKET_CAP_INDEXES.items():
        cached = MARKET_CAP_INDEX_CACHE.get(category)

        if cached and now - cached["time"] < MARKET_CAP_CACHE_TTL:
            continue

        try:
            symbols = fetch_market_cap_symbols(session, index_name, category)

            if symbols:
                MARKET_CAP_INDEX_CACHE[category] = {
                    "time": now,
                    "symbols": symbols,
                }
                print(
                    f"[MARKET CAP] {index_name}: "
                    f"{len(symbols)} live constituents"
                )
            else:
                print(
                    f"[MARKET CAP] No constituents returned for "
                    f"{index_name}; retaining previous cache."
                )

        except Exception as exc:
            print(
                f"[MARKET CAP] Failed to refresh {index_name}: {exc}"
            )

    categories = {}

    # These index groups are intended to be separate.
    for category in ("large", "mid", "small"):
        cached = MARKET_CAP_INDEX_CACHE.get(category)

        if not cached:
            continue

        for symbol in cached["symbols"]:
            categories.setdefault(symbol, category)

    return categories

COMPANY_NAME_BY_SYMBOL = {}


def get_company_name(row, symbol):
    """Return a real company name, never the ticker repeated as the name."""
    candidates = [
        row.get("companyName"),
        row.get("company"),
        (row.get("meta") or {}).get("companyName")
        if isinstance(row.get("meta"), dict) else None,
        COMPANY_NAME_BY_SYMBOL.get(symbol.upper()),
    ]

    for name in candidates:
        if name and str(name).strip().upper() != symbol.strip().upper():
            return str(name).strip()

    return symbol
def normalize_variations(payload):
    result = []

    for row in variation_rows(payload):
        if not isinstance(row, dict):
            continue

        series = str(row.get("series") or "").strip().upper()

        if series and series != "EQ":
            continue

        symbol = str(row.get("symbol") or "").strip()
        if not symbol:
            continue

        result.append({
            "symbol": symbol,
            "company": get_company_name(row, symbol),
            "price": rounded(row.get("ltp")),
            "change": rounded(row.get("perChange")),
            "previous_close": rounded(row.get("prev_price")),
            "open": rounded(row.get("open_price")),
            "high": rounded(row.get("high_price")),
            "low": rounded(row.get("low_price")),
            "volume": int(to_number(row.get("trade_quantity"))),
        })

    return result




def normalize_volume(payload):
    rows = payload.get("data", [])
    result = []

    if not isinstance(rows, list):
        return result

    def first_value(row, *keys):
        for key in keys:
            value = row.get(key)
            if value is not None and str(value).strip() not in ("", "-", "—"):
                return value
        return None

    for row in rows:
        if not isinstance(row, dict):
            continue

        symbol = str(row.get("symbol") or "").strip()
        if not symbol:
            continue

        result.append({
            "symbol": symbol,
            "company": str(row.get("companyName") or symbol),
            "price": rounded(first_value(row, "ltp", "lastPrice")),
            "change": rounded(first_value(row, "pChange", "perChange")),
            "volume": int(to_number(
                first_value(row, "volume", "tradedQuantity", "trade_quantity")
            )),
            "average_volume": int(to_number(
                first_value(row, "week1AvgVolume", "week1avgVolume")
            )),
            "volume_change_pct": rounded(
                first_value(row, "week1volChange")
            ),
            "turnover": rounded(row.get("turnover")),
            "open": rounded(first_value(
                row, "open", "openPrice", "open_price"
            )),
            "high": rounded(first_value(
                row, "high", "highPrice", "high_price"
            )),
            "low": rounded(first_value(
                row, "low", "lowPrice", "low_price"
            )),
        })

    return result


# Historical weekly average-volume fallback.
# Cache results for each symbol for the current calendar day.
_WEEKLY_AVG_CACHE = {}
_HISTORY_CLIENT = None



def get_weekly_average_volume(symbol):
    global _HISTORY_CLIENT

    today = datetime.now(IST).date()
    cache_key = (symbol, today.isoformat())

    # Reuse only successful results.
    cached = _WEEKLY_AVG_CACHE.get(cache_key)
    if cached is not None and cached > 0:
        return cached

    try:
        if _HISTORY_CLIENT is None:
            _HISTORY_CLIENT = NSE(
                download_folder="nse_history_cache"
            )

        end_date = today - timedelta(days=1)
        start_date = end_date - timedelta(days=30)

        records = _HISTORY_CLIENT.fetch_equity_historical_data(
            symbol,
            from_date=start_date,
            to_date=end_date,
            series="EQ",
        )

        daily_volumes = []

        for record in records:
            if not isinstance(record, dict):
                continue

            value = to_number(
                record.get("CH_TOT_TRADED_QTY"),
                default=0,
            )

            if value > 0:
                daily_volumes.append(value)

        recent_volumes = daily_volumes[-5:]

        if not recent_volumes:
            print(f"[NSE] No historical volume found for {symbol}")
            return None

        average_volume = round(
            sum(recent_volumes) / len(recent_volumes)
        )

        # Cache only successful results.
        _WEEKLY_AVG_CACHE[cache_key] = average_volume
        return average_volume

    except Exception as exc:
        print(
            f"[NSE] Historical volume lookup failed for {symbol}: {exc}"
        )
        return None
SECTOR_MEMBERSHIP_CACHE = {}
SECTOR_CACHE_TTL = 24 * 60 * 60



def fetch_angel_one_quotes(instruments):
    try:
        if not instruments:
            return []

        return angel_api.get_market_quotes(instruments)

    except Exception as e:
        print(f"Angel One quote error: {e}")
        return []

def build_sector_summary(rows, change_key="change"):
    """Best and worst sector (by average % change) among the given stocks."""
    groups = {}

    for r in rows:
        sym = str(r.get("symbol") or "").strip().upper()
        sector = r.get("sector") or STOCK_SECTOR_MAP.get(sym) or ""
        sector = str(sector).replace("NIFTY ", "").strip()

        if not sector or sector in ("Other / Unmapped", "Broader Market"):
            continue

        groups.setdefault(sector, []).append(to_number(r.get(change_key)))

    if not groups:
        return None

    stats = [
        {"sector": s, "avg": round(sum(v) / len(v), 2), "count": len(v)}
        for s, v in groups.items()
    ]

    best = max(stats, key=lambda x: x["avg"])
    worst = min(stats, key=lambda x: x["avg"])

    return {
        "top_gain": best if best["avg"] > 0 else None,
        "top_loss": worst if worst["avg"] < 0 else None,
    }

def refresh_nse_data():
    # Avoid overlapping refreshes.
    if not refresh_lock.acquire(blocking=False):
        return

    try:
        session = create_nse_session()
        market_cap_categories = get_live_market_cap_categories(session)
        # Fetch everything before publishing a new snapshot.
        status_json = fetch_json(session, URLS["market"])
        indices_json = fetch_json(session, URLS["indices"])
        sector_changes = normalize_index_changes(indices_json)

        sector_indices = {
            name: change
            for name, change in sector_changes.items()
            if name.startswith("NIFTY ")
            and any(word in name for word in (
                "AUTO", "BANK", "FMCG", "IT", "MEDIA",
                "METAL", "PHARMA", "REALTY", "HEALTHCARE",
                "CONSUMER DURABLES", "OIL", "CHEMICALS",
                "CEMENT", "FINANCIAL SERVICES"
            ))
        }
        
        # Rank sectors by their live percentage change.
        valid_sector_changes = {
            name: to_number(change)
            for name, change in sector_indices.items()
            if to_number(change) is not None
        }

        top_3_bullish_sectors = sorted(
            [
                {"name": name, "change": change}
                for name, change in valid_sector_changes.items()
                if change > 0
            ],
            key=lambda item: item["change"],
            reverse=True,
        )[:4]

        top_3_bearish_sectors = sorted(
            [
                {"name": name, "change": change}
                for name, change in valid_sector_changes.items()
                if change < 0
            ],
            key=lambda item: item["change"],
        )[:4]

        print("NSE SECTOR INDICES:")
        for item in indices_json.get("data", []):
            if "SECTOR" in str(item.get("key", "")).upper():
                print(
                    item.get("index"),
                    "| Change:", item.get("percentChange"),
                    "| Group:", item.get("key")
                )

        print("[ANGEL] Bulk quote fetch temporarily disabled.")
        volume_json = fetch_json(session, URLS["volume"])
        print("VOLUME API FIELDS:", list(volume_json.get("data", [{}])[0].keys()) if volume_json.get("data") else "NO DATA")
        print("VOLUME API SAMPLE:", volume_json.get("data", [])[:1])
        gainers_json = fetch_json(session, URLS["gainers"])
        losers_json = fetch_json(session, URLS["losers"])
        
        print("[DEBUG] GAINERS response keys:", list(gainers_json.keys()))
        print("[DEBUG] GAINERS response sample:", str(gainers_json)[:1500])

        print("[DEBUG] LOSERS response keys:", list(losers_json.keys()))
        print("[DEBUG] LOSERS response sample:", str(losers_json)[:1500])


        status, trade_date = get_market_status(status_json)
        volume = normalize_volume(volume_json)
                # Symbols in NSE's own volume-gainers feed (before we merge anything in).
        nse_volume_symbols = {
            str(r.get("symbol") or "").strip().upper() for r in volume
        }

# Learn company names from the NSE volume feed.
        for row in volume:
            symbol = str(row.get("symbol") or "").strip().upper()
            company = str(row.get("company") or "").strip()

            if symbol and company and company.upper() != symbol:
                COMPANY_NAME_BY_SYMBOL[symbol] = company

        gainers = normalize_variations(gainers_json)
        losers = normalize_variations(losers_json)
        
        print("[CHECK] Gainers raw rows:", len(variation_rows(gainers_json)))
        print("[CHECK] Gainers normalized:", len(gainers))
        print("[CHECK] Losers raw rows:", len(variation_rows(losers_json)))
        print("[CHECK] Losers normalized:", len(losers))
        print("[CHECK] Gainers sample:", gainers[:2])
        print("[CHECK] Losers sample:", losers[:2])
                # ---- Widen the pool using the full Nifty 500 ----
        universe = get_universe_rows(session)

        if universe:
            def with_defaults(row):
                r = dict(row)
                for k in ("open", "high", "low", "average_volume",
                          "volume_change_pct", "turnover", "previous_close"):
                    r.setdefault(k, 0)
                return r

            def merge_into(target, extra):
                seen = {str(r.get("symbol")).strip().upper() for r in target}
                for r in extra:
                    sym = str(r.get("symbol")).strip().upper()
                    if sym not in seen:
                        target.append(with_defaults(r))
                        seen.add(sym)

            top_up = sorted(
                (r for r in universe if r["change"] > 0),
                key=lambda r: r["change"], reverse=True,
            )[:MAX_POOL]
            top_down = sorted(
                (r for r in universe if r["change"] < 0),
                key=lambda r: r["change"],
            )[:MAX_POOL]
            top_vol = sorted(
                universe, key=lambda r: r["volume"], reverse=True,
            )[:MAX_POOL]

            merge_into(gainers, top_up)
            merge_into(losers, top_down)
            merge_into(volume, top_vol)

            for r in universe:
                nm = str(r.get("company") or "").strip()
                sym = str(r.get("symbol") or "").strip().upper()
                if nm and nm.upper() != sym:
                    COMPANY_NAME_BY_SYMBOL.setdefault(sym, nm)

        
        candidate_rows = volume + gainers + losers
        rows_by_symbol = {}

        for row in candidate_rows:
            symbol = str(row.get("symbol") or "").strip().upper()
            if symbol and symbol not in rows_by_symbol:
                rows_by_symbol[symbol] = row
        
        relative_moves = []

        
        
        sector_names = [
            name for name in sector_indices
            if name in {
                
                "NIFTY BANK",
                "NIFTY FINANCIAL SERVICES 25/50",
                "NIFTY AUTO",
                "NIFTY FMCG",
                "NIFTY IT",
                "NIFTY MEDIA",
                "NIFTY METAL",
                "NIFTY PHARMA",
                "NIFTY PSU BANK",
                "NIFTY PRIVATE BANK",
                "NIFTY REALTY",
                "NIFTY HEALTHCARE INDEX",
                "NIFTY CONSUMER DURABLES",
                "NIFTY OIL & GAS",
                "NIFTY CHEMICALS",
                "NIFTY CEMENT",
            }
        ]


        print("[DEBUG] Sector names to fetch:", sector_names)

        
        # Refresh sectors continuously instead of once every 24 hours.
        global SECTOR_FETCH_CURSOR

        sector_count = len(sector_names)
        batch_size = min(
            MAX_NEW_SECTOR_LOOKUPS_PER_REFRESH,
            sector_count,
        )

        if sector_count > 0:
            start = SECTOR_FETCH_CURSOR % sector_count

            sectors_to_fetch = [
                sector_names[(start + i) % sector_count]
                for i in range(batch_size)
            ]

            SECTOR_FETCH_CURSOR = (
                start + batch_size
            ) % sector_count
        else:
            sectors_to_fetch = []


        for sector_name in sectors_to_fetch:
            try:
                members = fetch_sector_constituents(
                    session,
                    sector_name,
                )

                if not members:
                    print(
                        f"[SECTOR EMPTY] {sector_name}: "
                        "NSE returned no constituent rows; "
                        "retaining previous cache."
                    )
                    continue

                SECTOR_INDEX_MEMBERS_CACHE[sector_name] = {
                    "time": time.time(),
                    "rows": members,
                }

                for member in members:
                    symbol = str(
                        member.get("symbol") or ""
                    ).strip().upper()

                    if not symbol:
                        continue

                    STOCK_SECTOR_MAP[symbol] = (
                        sector_name.replace("NIFTY ", "")
                    )

                    company = member.get("company")

                    if (
                        company
                        and str(company).strip().upper() != symbol
                    ):
                        COMPANY_NAME_BY_SYMBOL[symbol] = (
                            str(company).strip()
                        )

                update_trend_history(members)

                print(
                    f"[SECTOR LIVE] {sector_name}: "
                    f"{len(members)} stocks"
                )

            except Exception as e:
                cached = SECTOR_INDEX_MEMBERS_CACHE.get(
                    sector_name
                )

                if cached:
                    cache_age = int(
                        time.time() - cached["time"]
                    )
                    print(
                        f"[SECTOR ERROR] {sector_name}: {e}. "
                        f"Retaining {len(cached['rows'])} cached "
                        f"stocks; cache age={cache_age}s."
                    )
                else:
                    print(
                        f"[SECTOR ERROR] {sector_name}: {e}. "
                        "No previous cache available."
                    )



        
        relative_moves = []

        for sector_name in sector_names:
            cached_sector = SECTOR_INDEX_MEMBERS_CACHE.get(sector_name)

            if not cached_sector:
                continue

            sector_change = to_number(sector_indices.get(sector_name))

            for stock in cached_sector.get("rows", []):
                stock_change = to_number(stock.get("change"))

                relative_moves.append({
    **stock,
    **get_trend_flags(stock.get("symbol")),
    "sector": sector_name,
    "stock_change": round(stock_change, 2),
    "sector_change": round(sector_change, 2),
    "relative_change": round(
        stock_change - sector_change, 2
    ),
})

        relative_moves.sort(
            key=lambda item: item["relative_change"],
            reverse=True,
        )




        
# Build a lookup of average volume using each stock's symbol.
        # Fill missing or zero weekly averages using historical data.
        
        # Match weekly averages by stock symbol.
        average_volume_by_symbol = {
            row["symbol"]: row["average_volume"]
            for row in volume
            if to_number(row.get("average_volume")) > 0
        }

        # Copy Open, High and Low from price data where available.
        variation_by_symbol = {
            row["symbol"]: row
            for row in gainers + losers
        }

        for row in volume:
            price_row = variation_by_symbol.get(row["symbol"], {})

            for field in ("open", "high", "low"):
                if not row.get(field):
                    row[field] = price_row.get(field, 0)

        # Add weekly averages to price gainers and losers.
        for row in gainers + losers:
            average = average_volume_by_symbol.get(row["symbol"])

            if average is not None:
                row["average_volume"] = average

        # Retrieve historical averages for stocks still missing them.

                # Fill weekly average volume for Nifty 500 stocks NSE's volume
        # feed doesn't cover. Only stocks that could qualify for
        # "Price & Volume Gainers" are looked up, a few per refresh.
        needs_avg = {}
        for row in volume + gainers + losers:
            sym = str(row.get("symbol") or "").strip().upper()
            if (
                sym
                and to_number(row.get("average_volume")) <= 0
                and abs(to_number(row.get("change"))) >= 0.5
                and to_number(row.get("volume")) >= 100000
            ):
                needs_avg[sym] = abs(to_number(row.get("change")))

        lookups_done = 0
        now_ts = time.time()
        today_str = datetime.now(IST).date().isoformat()

        for sym in sorted(needs_avg, key=needs_avg.get, reverse=True):
            cached = AVG_VOL_CACHE.get(sym)

            if cached:
                if cached["avg"] > 0 and cached["day"] == today_str:
                    continue  # good result, reuse
                if cached["avg"] == 0 and now_ts - cached["time"] < 1800:
                    continue  # failed recently, don't retry yet

            if lookups_done >= AVG_VOL_LOOKUPS_PER_REFRESH:
                break

            avg = get_weekly_average_volume(sym) or 0
            AVG_VOL_CACHE[sym] = {"time": now_ts, "avg": avg, "day": today_str}
            lookups_done += 1

        for row in volume + gainers + losers:
            sym = str(row.get("symbol") or "").strip().upper()
            cached = AVG_VOL_CACHE.get(sym)
            if (
                cached
                and cached["avg"] > 0
                and to_number(row.get("average_volume")) <= 0
            ):
                row["average_volume"] = cached["avg"]

        if lookups_done:
            print(f"[AVG VOL] looked up {lookups_done} symbols this refresh")
        # Use averages already supplied by NSE.
        # Never block the live dashboard on individual history requests.
        for row in volume + gainers + losers:
            current_average = to_number(row.get("average_volume"))
            row["average_volume"] = (
                round(current_average) if current_average > 0 else 0
            )



        # Combine price gainers and losers.
        price_gainers_losers = sorted(
            gainers + losers,
            key=lambda row: row["change"],
            reverse=True
        )

        
        # Positive price change AND current volume above one-week average.
        
        frac = day_fraction()

        # Stocks that are price movers (bull or bear)
        price_symbols = {
            str(r.get("symbol") or "").strip().upper()
            for r in gainers + losers
        }

        def is_volume_gainer(row):
            sym = str(row.get("symbol") or "").strip().upper()
            if sym in nse_volume_symbols:
                return True
            avg = to_number(row.get("average_volume"))
            return avg > 0 and to_number(row.get("volume")) >= avg * frac * PV_MIN_RVOL

        # Pool of every stock from either list (no duplicates)
        pv_pool = {}
        for row in gainers + losers + volume:
            sym = str(row.get("symbol") or "").strip().upper()
            if sym and sym not in pv_pool:
                pv_pool[sym] = row

        # Price & Volume Gainers = price mover (up or down) AND volume gainer
        combined = [
            row
            for sym, row in pv_pool.items()
            if sym in price_symbols
            and is_volume_gainer(row)
            and to_number(row.get("volume")) >= 100000
            and to_number(row.get("change")) != 0
        ]

        print(
            f"[PV DEBUG] price_movers={len(price_symbols)} "
            f"with_avg={sum(1 for r in pv_pool.values() if to_number(r.get('average_volume')) > 0)}"
            f"/{len(pv_pool)} common={len(combined)} day_fraction={frac:.2f}"
        )

        # Sort Volume Gainers by greatest increase over 1-week average volume.
        
        # Rank Volume Gainers by percentage above their 1-week average.
        def volume_strength(row):
            current = to_number(row.get("volume"))
            average = to_number(row.get("average_volume"))

            if current <= 0 or average <= 0:
                return -1

            return ((current - average) / average) * 100

        volume.sort(
            key=volume_strength,
            reverse=True,
        )


        # Sort Price & Volume Gainers by highest price-change percentage first.
        combined.sort(
            key=lambda row: abs(to_number(row.get("change"))),
            reverse=True,
        )

                # Exclude ETFs from every scanner before publishing data.
        all_scanner_lists = (
            volume,
            gainers,
            losers,
            price_gainers_losers,
            combined,
            relative_moves,
        )

        for scanner_rows in all_scanner_lists:
            scanner_rows[:] = [
                row for row in scanner_rows
                if not is_secret_etf(row)
            ]

        # Attach live NSE market-cap categories.
        # Attach live NSE market-cap categories.
        cap_map_ready = len(market_cap_categories) >= 300

        for scanner_rows in all_scanner_lists:
            for row in scanner_rows:
                symbol = str(row.get("symbol") or "").strip().upper()
                if not row.get("sector"):
                    row["sector"] = STOCK_SECTOR_MAP.get(symbol, "")
                row["market_cap_category"] = (
                    market_cap_categories.get(symbol)
                    or ("micro" if cap_map_ready else None)
                )
            if cap_map_ready and not INCLUDE_MICRO_CAPS:
                scanner_rows[:] = [
                    r for r in scanner_rows
                    if r["market_cap_category"] != "micro"
                ]

        sector_summaries = {
            "price_gainers_losers": build_sector_summary(price_gainers_losers),
            "volume_gainers": build_sector_summary(volume),
            "price_volume_gainers": build_sector_summary(combined),
            "relative_moves": build_sector_summary(relative_moves),
        }

        updated_at = datetime.now(IST).isoformat(
            timespec="seconds"
        )


        
        with data_lock:
            market_data.update({
                "market_status": status,
                "trade_date": trade_date,
                "last_updated": updated_at,
                "last_error": None,
                "volume_gainers": volume,
                "price_gainers": gainers,
                "price_losers": losers,
                "price_gainers_losers": price_gainers_losers,
                "price_volume_gainers": combined,
                "sector_indices": sector_indices,
                "top_3_bullish_sectors": top_3_bullish_sectors,
                "top_3_bearish_sectors": top_3_bearish_sectors,
                "relative_moves": relative_moves,
                "sector_summaries": sector_summaries,
            })

        print(f"[NSE] Data refreshed at {updated_at}")

    except Exception as exc:
        error = f"{type(exc).__name__}: {exc}"

        with data_lock:
            # Keep previously fetched data if NSE temporarily fails.
            market_data["last_error"] = error

        print(f"[NSE] Refresh failed: {error}")

    finally:
        refresh_lock.release()

def load_avg_volumes_from_bhavcopy():
    """Average the last 5 trading days' volume for every NSE stock."""
    client = NSE(download_folder="nse_history_cache")
    today = datetime.now(IST).date()

    day_volumes = []
    d = today - timedelta(days=1)
    tried = 0

    while len(day_volumes) < 5 and tried < 14:
        tried += 1
        if d.weekday() < 5:
            try:
                path = client.delivery_bhavcopy(d)
                vols = {}
                with open(path, newline="", encoding="utf-8", errors="ignore") as f:
                    for row in csv.DictReader(f):
                        row = {
                            str(k).strip().upper(): (v or "").strip()
                            for k, v in row.items() if k
                        }
                        if row.get("SERIES") != "EQ":
                            continue
                        qty = to_number(row.get("TTL_TRD_QNTY"))
                        sym = row.get("SYMBOL", "").upper()
                        if sym and qty > 0:
                            vols[sym] = qty
                if vols:
                    day_volumes.append(vols)
                    print(f"[AVG VOL] bhavcopy {d}: {len(vols)} stocks")
            except Exception as exc:
                print(f"[AVG VOL] bhavcopy {d} unavailable: {exc}")
        d -= timedelta(days=1)

    totals = {}
    for vols in day_volumes:
        for sym, qty in vols.items():
            totals.setdefault(sym, []).append(qty)

    day_str = today.isoformat()
    now = time.time()
    for sym, qtys in totals.items():
        AVG_VOL_CACHE[sym] = {
            "avg": round(sum(qtys) / len(qtys)),
            "day": day_str,
            "time": now,
        }

    return len(totals)


def avg_volume_worker():
    last_loaded = None

    while True:
        today_str = datetime.now(IST).date().isoformat()

        if last_loaded != today_str:
            try:
                n = load_avg_volumes_from_bhavcopy()
                print(f"[AVG VOL] loaded averages for {n} stocks")
                if n > 0:
                    last_loaded = today_str
            except Exception as exc:
                print(f"[AVG VOL] bulk load failed: {exc}")

        time.sleep(600)
def hourly_worker():
    """Keep Angel One hourly candles fresh for the most-traded stocks."""
    while True:
        symbols = []
        try:
            with data_lock:
                snap = dict(market_data)

            pool = {}
            for name in ("volume_gainers", "price_gainers", "price_losers"):
                for r in snap.get(name, []):
                    sym = str(r.get("symbol") or "").strip().upper()
                    if sym and sym not in pool and not is_secret_etf(r):
                        pool[sym] = (
                            to_number(r.get("price")) * to_number(r.get("volume"))
                        )

            symbols = sorted(pool, key=pool.get, reverse=True)[:HOURLY_TOP_N]
        except Exception as exc:
            print(f"[HOURLY] could not build symbol list: {exc}")

        if not symbols:
            time.sleep(10)
            continue

        now = datetime.now(IST)
        in_session = (
            now.weekday() < 5
            and (9, 15) <= (now.hour, now.minute) <= (15, 35)
        )
        max_age = 300 if in_session else 6 * 3600

        fetched = 0
        for sym in symbols:
            entry = HOURLY_HISTORY.get(sym)
            if entry and time.time() - entry["time"] < max_age:
                continue

            failed_at = HOURLY_FAILED.get(sym)
            if failed_at and time.time() - failed_at < 600:
                continue

            try:
                instrument = angel_api.get_instrument(sym)
                if not instrument or not instrument.get("token"):
                    HOURLY_FAILED[sym] = time.time()
                    continue

                candles = angel_api.get_hourly_candles(
                    instrument["token"], days=5
                )

                if candles:
                    HOURLY_HISTORY[sym] = {
                        "time": time.time(),
                        "data": [
                            {
                                "date": c[0],
                                "close": float(c[4]),
                                "volume": int(c[5]),
                            }
                            for c in candles if len(c) >= 6
                        ],
                    }
                    HOURLY_FAILED.pop(sym, None)
                    fetched += 1
                else:
                    HOURLY_FAILED[sym] = time.time()
                    print(f"[HOURLY] {sym}: no candles returned")

            except Exception as exc:
                HOURLY_FAILED[sym] = time.time()
                print(f"[HOURLY] {sym}: {exc}")
                time.sleep(3)  # back off if Angel is rate-limiting us

            time.sleep(HOURLY_CALL_GAP)

        if fetched:
            print(
                f"[HOURLY] refreshed {fetched} symbols, "
                f"{len(HOURLY_HISTORY)} cached"
            )

        time.sleep(10)

def background_worker():
    while True:
        refresh_nse_data()
        time.sleep(REFRESH_SECONDS)


# Secret Gainers & Losers
SECRET_HISTORY_CACHE = {}
secret_moves_result_cache = {}
SECRET_MOVES_RESULT_TTL = 20
SECRET_HISTORY_TTL = 900  # Cache history for 15 minutes


def is_secret_etf(row):
    """Exclude ETFs, exchange-traded products and mutual-fund products."""
    symbol = str(row.get("symbol") or "").strip().upper()
    company = str(row.get("company") or "").strip().upper()

    blocked_symbol_terms = (
        "BEES", "ETF", "GOLDETF", "SILVERETF", "LIQUIDETF",
        "BANKETF", "ITETF", "NIFTYETF", "JUNIORBEES",
        "MON100", "CPSEETF", "SETFGOLD", "LIQUIDBEES",
    )

    blocked_company_terms = (
        " ETF", "ETF ", " BEES", "BEES ", "MUTUAL FUND",
        "GOLD FUND", "SILVER FUND", "INDEX FUND",
        "EXCHANGE TRADED FUND",
    )

    if any(term in symbol for term in blocked_symbol_terms):
        return True

    if any(term in company for term in blocked_company_terms):
        return True

    return False


secret_history_cache = SECRET_HISTORY_CACHE
secret_nse_client = NSE(download_folder="nse_history_cache")
def get_secret_history(symbol, timeframe="day"):
    from datetime import date, timedelta
    import pandas as pd

    symbol = str(symbol or "").strip().upper()
    if not symbol:
        return []
    # Hourly views read what the background worker has already fetched.
    if timeframe in ("1hr", "4hr"):
        return (HOURLY_HISTORY.get(symbol) or {}).get("data", [])    

    # Use a unique cache key that includes the timeframe so 1hr, 4hr, and day don't overwrite each other
    hist_kind = "hourly" if timeframe in ("1hr", "4hr") else "daily"
    cache_key = f"secret_history_{hist_kind}_{symbol}"
    now = time.time()

    cached = secret_history_cache.get(cache_key)
    if cached and now - cached["time"] < 900:  # Cache for 15 minutes
        return cached["data"]

    # If user selected an hourly timeframe, fetch hourly candles from Angel One
    if timeframe in ("1hr", "4hr"):
        try:
            instrument = angel_api.get_instrument(symbol)
            if not instrument or not instrument.get("token"):
                return []

            candles = angel_api.get_hourly_candles(instrument["token"], days=5)
            if not candles:
                return []

            history = [
                {
                    "date": c[0],
                    "close": float(c[4]),
                    "volume": int(c[5])
                }
                for c in candles if len(c) >= 6
            ]

            # Save to cache so we don't spam Angel One and trigger rate limits
            secret_history_cache[cache_key] = {
                "time": now,
                "data": history
            }
            return history
        except Exception as exc:
            print(f"[SECRET HISTORY HOURLY] {symbol}: {exc}")
            return []

    try:
        end_date = datetime.now(IST).date() - timedelta(days=1)
        start_date = end_date - timedelta(days=90)

        raw = secret_nse_client.fetch_equity_historical_data(
            symbol,
            from_date=start_date,
            to_date=end_date,
            series="EQ",
        )

        if not raw:
            print(f"[SECRET HISTORY] {symbol}: NSE returned no rows")
            return []

        df = pd.DataFrame(raw)
        df.columns = [str(col).strip().upper() for col in df.columns]

        close_col = next(
            (c for c in (
                "CHCLOSINGPRICE", "CH_CLOSING_PRICE",
                "CLOSE", "CLOSE PRICE", "CLOSING PRICE"
            ) if c in df.columns),
            None,
        )

        volume_col = next(
            (c for c in (
                "CHTOTTRADEDQTY", "CH_TOT_TRADED_QTY",
                "VOLUME", "TOTAL TRADED QUANTITY"
            ) if c in df.columns),
            None,
        )

        date_col = next(
            (c for c in (
                "MTIMESTAMP", "CHTIMESTAMP",
                "CH_TIMESTAMP", "TIMESTAMP", "DATE"
            ) if c in df.columns),
            None,
        )

        if not close_col or not date_col:
            secret_history_cache[cache_key] = {
                "time": now,
                "data": [],
            }
            return []

        df["close_value"] = pd.to_numeric(
            df[close_col], errors="coerce"
        )

        if volume_col:
            df["volume_value"] = pd.to_numeric(
                df[volume_col], errors="coerce"
            )
        else:
            df["volume_value"] = 0

        df["date_value"] = pd.to_datetime(
            df[date_col], errors="coerce", dayfirst=True
        )

        df = df.dropna(subset=["date_value", "close_value"])
        df = df[df["close_value"] > 0]
        df = df.sort_values("date_value")
        df = df.drop_duplicates("date_value", keep="last")

        history = [
            {
                "date": row.date_value.strftime("%Y-%m-%d"),
                "close": float(row.close_value),
                "volume": int(row.volume_value)
                if pd.notna(row.volume_value) else 0,
            }
            for row in df.itertuples(index=False)
        ]

        secret_history_cache[cache_key] = {
            "time": now,
            "data": history,
        }

        return history

    except Exception as exc:
        print(
            f"[SECRET HISTORY] {symbol}: "
            f"{type(exc).__name__}: {exc}"
        )
        return []


def resolve_stock_sector(symbol, stock_dict):
    sym = symbol.strip().upper()

    # Live NSE sector cache first
    if sym in STOCK_SECTOR_MAP:
        return STOCK_SECTOR_MAP[sym]

    # Angel instrument fallback
    instrument = angel_api.get_instrument(sym)
    if instrument:
        return "Broader Market"

    return "Broader Market"



@app.route("/api/secret-moves")
def secret_moves_api():
    timeframe = request.args.get("timeframe", "day").lower()
    direction = request.args.get("direction", "both").lower()

    periods = {
        "1hr": 2,
        "4hr": 4,
        "day": 1,
        "week": 5,
        "month": 20,
    }

    if timeframe not in periods:
        return jsonify({"error": "Invalid timeframe"}), 400

    if direction not in ("gainers", "losers", "both"):
        return jsonify({"error": "Invalid direction"}), 400
    cache_key = f"{timeframe}:{direction}"
    cached_result = secret_moves_result_cache.get(cache_key)

    if (
        cached_result
        and time.time() - cached_result["time"] < SECRET_MOVES_RESULT_TTL
    ):
        return jsonify(cached_result["payload"])
    with data_lock:
            snapshot = dict(market_data)
            candidates = {}
            
            # Helper to extract a valid company name from any NSE row
            def extract_nse_company(row, sym):
                comp = str(row.get("company") or row.get("companyName") or "").strip()
                if comp and comp.upper() != sym:
                    return comp
                meta = row.get("meta")
                if isinstance(meta, dict):
                    meta_comp = str(meta.get("companyName") or "").strip()
                    if meta_comp and meta_comp.upper() != sym:
                        return meta_comp
                return sym

            # Discover candidates from all current live scanner lists.
            for list_name in (
                "volume_gainers",
                "price_gainers",
                "price_losers",
                "relative_moves",
            ):
                for row in snapshot.get(list_name, []):
                    symbol = str(row.get("symbol") or "").strip().upper()
                    if symbol and symbol not in candidates:
                        row_copy = dict(row)
                        row_copy["company"] = extract_nse_company(row_copy, symbol)
                        candidates[symbol] = row_copy

            # Include stocks found in cached sector constituents from NSE
            for cached_sector in SECTOR_INDEX_MEMBERS_CACHE.values():
                for row in cached_sector.get("rows", []):
                    symbol = str(row.get("symbol") or "").strip().upper()
                    if symbol and symbol not in candidates:
                        row_copy = dict(row)
                        row_copy["company"] = extract_nse_company(row_copy, symbol)
                        candidates[symbol] = row_copy

    # Build market-cap lookup from the cached live NSE index members.
    secret_market_caps = {}

    for category in ("large", "mid", "small"):
        cached = MARKET_CAP_INDEX_CACHE.get(category)

        if not cached:
            continue

        for symbol in cached.get("symbols", set()):
            secret_market_caps.setdefault(symbol, category)

    # Ensure every Secret Gainers & Losers candidate has a market-cap category.
    secret_cap_ready = len(secret_market_caps) >= 300

    for symbol, stock in candidates.items():
        stock["market_cap_category"] = (
            stock.get("market_cap_category")
            or secret_market_caps.get(symbol)
            or ("micro" if secret_cap_ready else None)
        )
    # DAY view: built entirely from live data already in the snapshot.
    if timeframe == "day":
        frac = day_fraction()
        live_results = []

        for symbol, stock in candidates.items():
            if is_secret_etf(stock):
                continue

            move = to_number(stock.get("change"))
            if move == 0:
                continue

            stock_direction = "gainer" if move > 0 else "loser"
            if direction != "both" and direction != stock_direction + "s":
                continue
            # Intraday consistency from today's hourly candles, if loaded.
            today_iso = datetime.now(IST).date().isoformat()
            candles = (HOURLY_HISTORY.get(symbol) or {}).get("data", [])
            today_closes = [
                c["close"] for c in candles
                if str(c.get("date", "")).startswith(today_iso)
            ]
            day_consistency = None
            if len(today_closes) >= 3:
                steps = [
                    today_closes[i] - today_closes[i - 1]
                    for i in range(1, len(today_closes))
                ]
                hits = sum(1 for s in steps if (s > 0 if move > 0 else s < 0))
                day_consistency = round(hits / len(steps) * 100, 1)
            vol = to_number(stock.get("volume"))
            avg = to_number(stock.get("average_volume"))
            if avg <= 0:
                avg = to_number((AVG_VOL_CACHE.get(symbol) or {}).get("avg"))

            expansion = avg > 0 and vol >= avg * frac * 1.10

            sector = (
                STOCK_SECTOR_MAP.get(symbol)
                or str(stock.get("sector") or "").replace("NIFTY ", "")
                or "Broader Market"
            )
            company = (
                COMPANY_NAME_BY_SYMBOL.get(symbol)
                or stock.get("company")
                or symbol
            )

            live_results.append({
                "symbol": symbol,
                "company": company,
                "price": to_number(stock.get("price")),
                "sector": sector,
                "move_percent": round(move, 2),
                "volume": vol,
                "average_volume": round(avg),
                "direction": stock_direction,
                "consistency": day_consistency,
                "signals": {
                    "quiet_accumulation": move > 0 and expansion and abs(move) <= 2.5,
                    "persistent_strength": False,
                    "possible_distribution": move < 0 and expansion,
                    "persistent_weakness": False,
                },
                "market_cap_category": stock.get("market_cap_category"),
            })

        if direction == "both":
            live_results.sort(key=lambda r: abs(r["move_percent"]), reverse=True)
        else:
            live_results.sort(
                key=lambda r: r["move_percent"],
                reverse=(direction == "gainers"),
            )

        payload = {
            "timeframe": timeframe,
            "direction": direction,
            "count": len(live_results),
            "results": live_results,
            "sector_summary": build_sector_summary(live_results, "move_percent"),            
        }
        secret_moves_result_cache[cache_key] = {
            "time": time.time(),
            "payload": payload,
        }
        return jsonify(payload)
    results = []
    required = periods[timeframe] + 1

# Convert candidates to a list so we can limit hourly checks to keep it fast
    # Most-traded stocks first, in a stable order so cached history keeps being reused
    candidate_items = sorted(
        candidates.items(),
        key=lambda kv: to_number(kv[1].get("price")) * to_number(kv[1].get("volume")),
        reverse=True,
    )[:SECRET_MAX_CANDIDATES]
    fetch_budget = SECRET_NEW_FETCHES_PER_REQUEST

    for symbol, stock in candidate_items:
        if is_secret_etf(stock):
            continue

        hist_kind = "hourly" if timeframe in ("1hr", "4hr") else "daily"
        cache_entry = secret_history_cache.get(f"secret_history_{hist_kind}_{symbol}")
        if timeframe not in ("1hr", "4hr") and (
            not cache_entry or time.time() - cache_entry["time"] >= 900
        ):
            # Not cached yet: only download a few per request so the page
            # responds quickly. The rest fill in on later refreshes.
            if fetch_budget <= 0:
                continue
            fetch_budget -= 1
            if hist_kind == "hourly":
                time.sleep(0.35)  # stay under Angel One's rate limit

        history = get_secret_history(symbol, timeframe=timeframe)

        if len(history) < required:
            continue

        recent = history[-required:]
        closes = [item["close"] for item in recent]

        first_close = closes[0]
        last_close = closes[-1]

        if first_close <= 0:
            continue

        move = ((last_close - first_close) / first_close) * 100

        changes = [
            closes[i] - closes[i - 1]
            for i in range(1, len(closes))
        ]

        if not changes:
            continue

        rises = sum(change > 0 for change in changes)
        falls = sum(change < 0 for change in changes)
        total = len(changes)

        rise_consistency = rises / total * 100
        fall_consistency = falls / total * 100


# Determine direction from the overall price move.
# Do not discard mixed-trend stocks before checking their signals.
        if move > 0:
            stock_direction = "gainer"
            consistency = rise_consistency
        elif move < 0:
            stock_direction = "loser"
            consistency = fall_consistency
        else:
            continue


        # Apply the selected direction filter.
        if direction != "both" and direction != stock_direction + "s":
            continue

        # Calculate the baseline from up to 20 completed sessions
        # before the latest session in the selected history.
        baseline_history = history[-21:-1]

        baseline_volumes = [
            to_number(item.get("volume"))
            for item in baseline_history
            if to_number(item.get("volume")) > 0
        ]

        average_volume = (
            sum(baseline_volumes) / len(baseline_volumes)
            if baseline_volumes else 0
        )

        latest_volume = to_number(history[-1].get("volume"))

        latest_daily_change = (
            (closes[-1] - closes[-2]) / closes[-2] * 100
            if len(closes) > 1 and closes[-2] > 0
            else 0
        )

        volume_expansion = (
            average_volume > 0
            and latest_volume >= average_volume * 1.10
        )

        # Calculate each signal only once.
        signals = []

        if move > 0 and consistency >= 50:
            signals.append("persistent_strength")

        if move < 0 and consistency >= 70:
            signals.append("persistent_weakness")

        if (
            move > 0
            and consistency >= 60
            and volume_expansion
            and abs(latest_daily_change) <= 2.5
        ):
            signals.append("quiet_accumulation")

        if move < 0 and volume_expansion:
            signals.append("possible_distribution")





    # Dynamically resolve sector from NSE cache if missing
# Dynamically resolve sector and company name using NSE live caches or on-demand quote lookup
        sector = stock.get("sector")
        if not sector or sector in ("Other / Unmapped", "Broader Market"):
            sector = STOCK_SECTOR_MAP.get(symbol)
            if not sector:
                for s_name, cache_data in SECTOR_INDEX_MEMBERS_CACHE.items():
                    if any(str(r.get("symbol")).strip().upper() == symbol for r in cache_data.get("rows", [])):
                        sector = s_name.replace("NIFTY ", "")
                        STOCK_SECTOR_MAP[symbol] = sector
                        break

        resolved_company = stock.get("company")
        if not resolved_company or str(resolved_company).strip().upper() == symbol:
            resolved_company = COMPANY_NAME_BY_SYMBOL.get(symbol)
        # Use cached or known metadata instead of making another
        # network request for every stock during the historical scan.
        if not sector or sector in (
            "Other / Unmapped",
            "Broader Market",
        ):
            sector = resolve_stock_sector(symbol, stock)

        if (
            not resolved_company
            or str(resolved_company).strip().upper() == symbol
        ):
            resolved_company = symbol

        if not sector:
            sector = "Broader Market"

        if not resolved_company:
            resolved_company = symbol


        results.append({
            "symbol": symbol,
            "company": resolved_company,
            "price": (
    to_number(stock.get("price"), default=0)
    if to_number(stock.get("price"), default=0) > 0
    else last_close
),
            "sector": sector,
            "move_percent": round(move, 2),
            "volume": latest_volume,
            "average_volume": round(average_volume),
            "direction": stock_direction,
            "consistency": round(consistency, 1),
            "signals": {
                "quiet_accumulation": "quiet_accumulation" in signals,
                "persistent_strength": "persistent_strength" in signals,
                "possible_distribution": "possible_distribution" in signals,
                "persistent_weakness": "persistent_weakness" in signals,
            },
"market_cap_category": stock.get("market_cap_category"),
        })

    if direction == "both":
        results.sort(
            key=lambda row: abs(row["move_percent"]),
            reverse=True,
        )
    else:
        results.sort(
            key=lambda row: row["move_percent"],
            reverse=(direction == "gainers"),
        )

    payload = {
        "timeframe": timeframe,
        "direction": direction,
        "count": len(results),
        "results": results,
        "sector_summary": build_sector_summary(results, "move_percent"),        
    }

    secret_moves_result_cache[cache_key] = {
        "time": time.time(),
        "payload": payload,
    }

    return jsonify(payload)

@app.route("/")
def homepage():
    return render_template("index.html")


@app.route("/api/market")
def market_api():
    with data_lock:
        snapshot = dict(market_data)

    snapshot["refresh_seconds"] = REFRESH_SECONDS
    snapshot["source"] = "NSE India"
    return jsonify(snapshot)


@app.route("/api/refresh", methods=["POST"])
def request_refresh():
    threading.Thread(
        target=refresh_nse_data,
        daemon=True,
    ).start()

    return jsonify({"message": "Refresh requested"}), 202


def classify_secret_move(history):
    """
    history: list of daily closing prices, oldest first.
    Returns the direction and consistency of the stock's move.
    """

    if not history or len(history) < 2:
        return None

    start_price = history[0]
    end_price = history[-1]

    if start_price <= 0:
        return None

    move_percent = ((end_price - start_price) / start_price) * 100

    # Count how often the closing price moved in the same direction.
    rises = 0
    falls = 0

    for i in range(1, len(history)):
        if history[i] > history[i - 1]:
            rises += 1
        elif history[i] < history[i - 1]:
            falls += 1

    total_changes = len(history) - 1

    if total_changes == 0:
        return None

    rise_consistency = rises / total_changes * 100
    fall_consistency = falls / total_changes * 100

    if move_percent > 0 and rise_consistency >= 60:
        direction = "Gainer"
        consistency = rise_consistency

    elif move_percent < 0 and fall_consistency >= 60:
        direction = "Loser"
        consistency = fall_consistency

    else:
        return None

    return {
        "direction": direction,
        "move_percent": round(move_percent, 2),
        "consistency": round(consistency, 1),
    }

# Cache for on-demand dynamic stock metadata fetched directly from NSE
STOCK_METADATA_CACHE = {}

def fetch_stock_metadata_from_nse(session, symbol):
    """Dynamically fetch official company name and sector from NSE quote API."""
    sym = str(symbol).strip().upper()
    if sym in STOCK_METADATA_CACHE:
        return STOCK_METADATA_CACHE[sym]

    try:
        url = f"{NSE_API}/quote-equity?symbol={requests.utils.quote(sym)}"
        response = session.get(url, timeout=5)
        if response.status_code == 200:
            data = response.json()

            info = data.get("info", {})
            company = str(info.get("companyName") or sym).strip()
            sector = str(info.get("industry") or info.get("secIndustry") or "Broader Market").strip()

            meta = {
                "company": company if company.upper() != sym else sym,
                "sector": sector.replace("NIFTY ", "")
            }
            STOCK_METADATA_CACHE[sym] = meta
            return meta
    except Exception:
        pass

    return {"company": sym, "sector": "Broader Market"}

if __name__ == "__main__":
    threading.Thread(
        target=background_worker,
        daemon=True,
    ).start()

    threading.Thread(
        target=avg_volume_worker,
        daemon=True,
    ).start()

    threading.Thread(
        target=hourly_worker,
        daemon=True,
    ).start()
    
    app.run(
        host="127.0.0.1",
        port=5000,
        debug=False,
        use_reloader=False,
    )
