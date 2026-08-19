import concurrent.futures
import json
import os
import re
import statistics
import threading
import time
from datetime import datetime, timedelta

import truststore

truststore.inject_into_ssl()  # trust the OS certificate store (like curl), not just certifi's bundle

import requests
import urllib3
from flask import Flask, jsonify, request, send_from_directory

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

app = Flask(__name__, static_folder=".", static_url_path="")

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}

# Yahoo Finance's quoteSummary endpoint requires a session cookie + crumb
# token. We fetch it lazily and cache it; on 401/429 we drop the cache and
# re-negotiate on the next request.
_session = None
_crumb = None
_session_lock = threading.Lock()


def get_session_and_crumb():
    global _session, _crumb
    with _session_lock:
        if _session is not None and _crumb is not None:
            return _session, _crumb
        s = requests.Session()
        s.headers.update(HEADERS)
        try:
            s.get("https://fc.yahoo.com", timeout=8)
        except requests.RequestException:
            pass
        r = s.get("https://query1.finance.yahoo.com/v1/test/getcrumb", timeout=8)
        r.raise_for_status()
        crumb = r.text.strip()
        _session, _crumb = s, crumb
        return s, crumb


def reset_session():
    global _session, _crumb
    with _session_lock:
        _session, _crumb = None, None


def raw(container, key):
    value = (container or {}).get(key)
    if isinstance(value, dict):
        return value.get("raw")
    return value


def market_of(symbol):
    return "국내" if resolve_krx_code(symbol) else "해외"


def num(value):
    """Parse a comma-formatted numeric string ("13,660,080") into a float."""
    if value is None:
        return None
    try:
        return float(str(value).replace(",", "").replace("원", "").strip())
    except ValueError:
        return None


def parse_krw(value):
    """Parse Korean-unit money strings like "24조 4,433억" into a won amount."""
    if not value:
        return None
    s = str(value).replace(",", "")
    total = 0.0
    matched = False
    for unit, mult in (("조", 1e12), ("억", 1e8), ("만", 1e4)):
        m = re.search(rf"(-?\d+(?:\.\d+)?){unit}", s)
        if m:
            total += float(m.group(1)) * mult
            s = s[: m.start()] + s[m.end() :]
            matched = True
    remainder = re.search(r"-?\d+(?:\.\d+)?", s)
    if remainder:
        total += float(remainder.group(0))
        matched = True
    return total if matched else None


# Full KRX-listed ETF universe, sourced from Naver Finance (which mirrors
# official KRX data). Cached in memory since it's ~1000+ rows and rarely
# changes within a session; used to power accurate Korean-name/code search
# and as a quick lookup for the domestic quote endpoint.
_krx_list_cache = {"items": None, "fetched_at": 0}
_KRX_LIST_TTL_SECONDS = 600


def fetch_krx_etf_list():
    now = time.time()
    cache = _krx_list_cache
    if cache["items"] is not None and now - cache["fetched_at"] < _KRX_LIST_TTL_SECONDS:
        return cache["items"]
    url = "https://finance.naver.com/api/sise/etfItemList.nhn"
    r = requests.get(url, headers=HEADERS, timeout=10)
    r.raise_for_status()
    data = json.loads(r.content.decode("cp949", errors="replace"))
    items = data.get("result", {}).get("etfItemList", [])
    cache["items"] = items
    cache["fetched_at"] = now
    return items


def search_krx_etfs(query):
    query_stripped = query.strip().lower()
    query_norm = _compact(query_stripped)
    if not query_norm:
        return []
    # Individual words, so a query like "코스닥 레버리지" still finds
    # "KODEX 코스닥150레버리지" even though "150" sits between the two
    # words in the actual name (the single-substring checks below would
    # miss that, since "코스닥레버리지" isn't a contiguous substring of it).
    word_norms = [_compact(w) for w in query_stripped.split() if w]
    try:
        items = fetch_krx_etf_list()
    except requests.RequestException:
        return []
    exact, prefix, contains, word_match = [], [], [], []
    for it in items:
        code = it.get("itemcode", "")
        code_norm = _compact(code.lower())
        name = it.get("itemname") or ""
        name_norm = _compact(name.lower())
        candidate = {
            "symbol": code,
            "name": name,
            "exchange": "KRX",
            "type": "ETF",
            "market": "국내",
        }
        if query_norm == code_norm or query_norm == name_norm:
            exact.append(candidate)
        elif code_norm.startswith(query_norm) or name_norm.startswith(query_norm):
            prefix.append(candidate)
        elif query_norm in name_norm or query_norm in code_norm:
            contains.append(candidate)
        elif len(word_norms) > 1 and all(w in name_norm or w in code_norm for w in word_norms):
            word_match.append(candidate)
    return (exact + prefix + contains + word_match)[:8]


def resolve_krx_code(symbol):
    """Return the canonical (correctly-cased) KRX item code for `symbol` if
    it refers to a KRX-listed ETF, else None. Handles plain 6-digit codes
    (the common case) as well as the ~25% of KRX ETF codes that mix in a
    letter (e.g. "0223R0"), matched case-insensitively."""
    bare = symbol[:-3] if symbol.endswith((".KS", ".KQ")) else symbol
    if re.fullmatch(r"\d{6}", bare):
        return bare
    if not (len(bare) == 6 and bare.isalnum()):
        return None
    try:
        items = fetch_krx_etf_list()
    except requests.RequestException:
        return None
    upper = bare.upper()
    for it in items:
        if it.get("itemcode", "").upper() == upper:
            return it["itemcode"]
    return None


def parse_korean_date(value):
    """Parse a Naver-style "2002년 10월 14일" string into "2002-10-14"."""
    if not value:
        return None
    m = re.search(r"(\d{4})년\s*(\d{1,2})월\s*(\d{1,2})일", value)
    if not m:
        return None
    year, month, day = m.groups()
    return f"{year}-{int(month):02d}-{int(day):02d}"


def fetch_naver_coinfo(code):
    """Scrape the desktop ETF info page for fields the mobile API lacks
    (listing date, fund type/category). No auth required."""
    url = f"https://finance.naver.com/item/coinfo.naver?code={code}"
    try:
        r = requests.get(url, headers=HEADERS, timeout=8)
        r.raise_for_status()
        text = r.content.decode("euc-kr", errors="replace")
    except requests.RequestException:
        return {}
    result = {}
    m = re.search(r"상장일</th>\s*<td>([^<]+)</td>", text)
    if m:
        result["inceptionDate"] = parse_korean_date(m.group(1).strip())
    m = re.search(r"유형</th>\s*<td><span[^>]*>([^<]+)</span></td>", text)
    if m:
        result["category"] = m.group(1).strip()
    m = re.search(r"기초지수</th>\s*<td><span[^>]*>([^<]+)</span></td>", text)
    if m:
        result["benchmarkIndex"] = m.group(1).strip()
    return result


def format_period_label(days):
    """Turn a day count into a short Korean label like "3년", "1년 2개월",
    "8개월", or "12일" — used so a volatility figure never claims to cover
    "3년" when the underlying series is actually shorter (e.g. a fund
    listed 8 months ago)."""
    if not days or days < 1:
        return None
    days = int(days)
    if days < 30:
        return f"{days}일"
    years, remaining_days = divmod(days, 365)
    months = remaining_days // 30
    if months >= 12:
        years += 1
        months = 0
    if years >= 1:
        return f"{years}년 {months}개월" if months else f"{years}년"
    return f"{months}개월"


def historical_var(returns, confidence=0.975):
    """Empirical (historical) VaR at the given confidence level, as a
    positive loss percentage — e.g. 2.15 means "on the worst 2.5% of days
    in the sample, the loss exceeded 2.15%". Uses linear interpolation
    between ranks, same convention as numpy's default percentile method."""
    if not returns:
        return None
    ordered = sorted(returns)
    n = len(ordered)
    idx = (1 - confidence) * (n - 1)
    lower = int(idx)
    upper = min(lower + 1, n - 1)
    frac = idx - lower
    percentile_return = ordered[lower] + frac * (ordered[upper] - ordered[lower])
    return -percentile_return * 100


def compute_risk_stats(dates, closes):
    """Annualized volatility (%) and 1-day historical VaR at 97.5%
    confidence (%), from parallel lists of dates and closes. Returns
    (volatility, var975, days_covered) — days_covered reflects whatever
    history is actually available, which may be less than the 3y window
    requested (e.g. a recently-listed fund)."""
    points = sorted(
        ((d, c) for d, c in zip(dates, closes) if d is not None and c is not None),
        key=lambda p: p[0],
    )
    if len(points) < 2:
        return None, None, None
    values = [c for _, c in points]
    returns = [(curr - prev) / prev for prev, curr in zip(values, values[1:]) if prev]
    if len(returns) < 2:
        return None, None, None
    volatility = statistics.stdev(returns) * (252 ** 0.5) * 100
    var975 = historical_var(returns, 0.975) * (250 ** 0.5)
    days_covered = (points[-1][0] - points[0][0]).days
    return volatility, var975, days_covered


def fetch_naver_daily_series_risk_stats(base_url):
    end = datetime.now().strftime("%Y%m%d")
    start = (datetime.now() - timedelta(days=3 * 365 + 14)).strftime("%Y%m%d")
    try:
        r = requests.get(base_url, params={"startDateTime": start, "endDateTime": end}, headers=HEADERS, timeout=10)
        r.raise_for_status()
        rows = r.json()
    except (requests.RequestException, ValueError):
        return None, None, None
    if not isinstance(rows, list):
        return None, None, None
    dates = []
    for row in rows:
        d = row.get("localDate")
        try:
            dates.append(datetime.strptime(d, "%Y%m%d").date() if d else None)
        except (ValueError, TypeError):
            dates.append(None)
    closes = [row.get("closePrice") for row in rows]
    return compute_risk_stats(dates, closes)


def fetch_domestic_risk_stats(code):
    return fetch_naver_daily_series_risk_stats(f"https://api.stock.naver.com/chart/domestic/item/{code}/day")


# Common ETF benchmark index names -> Naver's domestic index chart code.
# Naver doesn't expose a name->code search for indices, so this only covers
# the broad-market indices Naver actually has a chart feed for. Most other
# custom/thematic indices Korean ETFs track are FnGuide-calculated, handled
# separately below (fetch_fnindex_risk_stats) since FnGuide's own site has
# the history. iSelect (NH투자증권's index brand) needs a login on NH's own
# site, but TIGER-issued ETFs tracking one can still get their benchmark's
# risk stats via fetch_tiger_benchmark_risk_stats (the issuer's own site
# charts each fund's benchmark performance regardless of who calculates the
# index). A few others (KRX 자체 지수, WISE 등, or any non-TIGER ETF
# tracking an iSelect index) still have no free public historical series we
# could find — those stay unmapped and the UI shows "-" rather than
# guessing.
DOMESTIC_INDEX_CODES = {
    "코스피 200": "KPI200",
    "코스피200": "KPI200",
    "코스피 100": "KPI100",
    "코스피100": "KPI100",
    "코스피": "KOSPI",
    "코스닥": "KOSDAQ",
}

# Benchmark name -> Yahoo Finance index ticker, for the well-known global
# indices some domestic ETFs track (e.g. "KODEX 미국S&P500" -> S&P 500).
OVERSEAS_INDEX_TICKERS = {
    "S&P 500": "^GSPC",
    "S&P500": "^GSPC",
    "나스닥 100": "^NDX",
    "나스닥100": "^NDX",
    "NASDAQ 100": "^NDX",
    "나스닥종합": "^IXIC",
    "나스닥 종합": "^IXIC",
    "다우존스": "^DJI",
    "다우존스산업평균": "^DJI",
    "다우존스 산업평균": "^DJI",
    "러셀 2000": "^RUT",
    "러셀2000": "^RUT",
    "필라델피아 반도체": "^SOX",
    "필라델피아반도체": "^SOX",
    "니케이 225": "^N225",
    "니케이225": "^N225",
    "항셍": "^HSI",
    "항셍테크": "^HSTECH",
    "유로스톡스 50": "^STOXX50E",
    "유로스톡스50": "^STOXX50E",
    "독일DAX": "^GDAXI",
    "DAX": "^GDAXI",
    "영국FTSE100": "^FTSE",
    "FTSE100": "^FTSE",
}


def normalize_benchmark_name(name):
    """Strip parenthetical qualifiers ("(Price Return)", "(TR)") and common
    Korean/English suffix words so lookup keys match regardless of how the
    fund's disclosure page phrases the benchmark name (e.g. "S&P 500 Total
    Return Index" vs plain "S&P 500")."""
    if not name:
        return ""
    name = re.sub(r"\([^)]*\)", "", name)
    for suffix in ("지수", "Total Return", "Price Return", "Net Total Return", "Index", "TR", "PR", "NTR"):
        name = re.sub(re.escape(suffix), "", name, flags=re.IGNORECASE)
    return name.strip()


def _compact(text):
    return re.sub(r"[\s\-]", "", text)


def resolve_domestic_index_code(benchmark_name):
    normalized = _compact(normalize_benchmark_name(benchmark_name))
    if not normalized:
        return None
    for key in sorted(DOMESTIC_INDEX_CODES, key=len, reverse=True):
        if _compact(key) in normalized:
            return DOMESTIC_INDEX_CODES[key]
    return None


def resolve_overseas_index_ticker(benchmark_name):
    normalized = _compact(normalize_benchmark_name(benchmark_name)).upper()
    if not normalized:
        return None
    for key in sorted(OVERSEAS_INDEX_TICKERS, key=len, reverse=True):
        if _compact(key).upper() in normalized:
            return OVERSEAS_INDEX_TICKERS[key]
    return None


def fetch_domestic_index_risk_stats(index_code):
    if not index_code:
        return None, None, None
    return fetch_naver_daily_series_risk_stats(f"https://api.stock.naver.com/chart/domestic/index/{index_code}/day")


# FnGuide (에프앤가이드) calculates most of the custom/thematic indices
# Korean ETFs track that aren't in DOMESTIC_INDEX_CODES above. Its public
# index site (fnindex.co.kr) is a Next.js app with no dedicated search API,
# but every index detail page's SSR props embed the *entire* index catalog
# as a category tree (fetched once here and flattened into a name lookup)
# plus that specific index's ORG_IDX_CD (a per-index data-source code that
# varies index-to-index and is required for the history call). History
# itself comes from the same JSON endpoint the site's own "Excel export"
# button calls (`/api/getData`, a same-origin proxy to FnGuide's backend
# taking a `url` field) — despite the "excel" path segment it returns plain
# JSON, not a spreadsheet.
_fnindex_tree_cache = {"map": None, "fetched_at": 0}
_FNINDEX_TREE_TTL_SECONDS = 24 * 3600
_fnindex_org_code_cache = {}


def fetch_fnindex_name_map():
    now = time.time()
    cache = _fnindex_tree_cache
    if cache["map"] is not None and now - cache["fetched_at"] < _FNINDEX_TREE_TTL_SECONDS:
        return cache["map"]
    r = requests.get("https://www.fnindex.co.kr/overview/detail/I/FI00.WLT.BSY", headers=HEADERS, timeout=15)
    r.raise_for_status()
    m = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', r.text, re.S)
    mapping = {}
    if m:
        data = json.loads(m.group(1))
        tree = data.get("props", {}).get("pageProps", {}).get("indexList") or []

        def walk(nodes):
            for node in nodes:
                if isinstance(node, list):
                    walk(node)
                    continue
                name, code = node.get("IDX_NM"), node.get("IDX_CD")
                if name and code:
                    mapping[_compact(name.lower())] = code
                if node.get("children"):
                    walk(node["children"])

        walk(tree)
    cache["map"] = mapping
    cache["fetched_at"] = now
    return mapping


def resolve_fnindex_code(benchmark_name):
    normalized = _compact(normalize_benchmark_name(benchmark_name).lower())
    if not normalized:
        return None
    try:
        name_map = fetch_fnindex_name_map()
    except requests.RequestException:
        return None
    if normalized in name_map:
        return name_map[normalized]
    best = None
    for name, code in name_map.items():
        if name and (name in normalized or normalized in name):
            if best is None or len(name) > len(best[0]):
                best = (name, code)
    return best[1] if best else None


def fetch_fnindex_org_code(idx_cd):
    if idx_cd in _fnindex_org_code_cache:
        return _fnindex_org_code_cache[idx_cd]
    r = requests.get(f"https://www.fnindex.co.kr/overview/detail/I/{idx_cd}", headers=HEADERS, timeout=15)
    r.raise_for_status()
    m = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', r.text, re.S)
    org_code = None
    if m:
        data = json.loads(m.group(1))
        org_code = data.get("props", {}).get("pageProps", {}).get("indexInfo", {}).get("ORG_IDX_CD")
    _fnindex_org_code_cache[idx_cd] = org_code
    return org_code


def fetch_fnindex_risk_stats(idx_cd):
    try:
        org_code = fetch_fnindex_org_code(idx_cd)
    except requests.RequestException:
        return None, None, None
    if not org_code:
        return None, None, None
    try:
        r = requests.post(
            "https://www.fnindex.co.kr/api/getData",
            json={"url": f"/FI/index/{idx_cd}/excel/data/{org_code}/10Y"},
            headers={**HEADERS, "Content-Type": "application/json"},
            timeout=15,
        )
        r.raise_for_status()
        rows = (r.json() or {}).get("VALUE") or []
    except requests.RequestException:
        return None, None, None
    dates, closes = [], []
    for row in rows:
        dt = row.get("DT")
        try:
            dates.append(datetime.strptime(dt, "%Y.%m.%d").date() if dt else None)
        except ValueError:
            dates.append(None)
        closes.append(row.get("CLS_PRC"))
    return compute_risk_stats(dates, closes)


def fetch_tiger_benchmark_risk_stats(krx_code, inception_date):
    """Last-resort fallback for benchmark indices with no public historical
    series anywhere else — notably NH투자증권's "iSelect" brand (used by
    several TIGER-issued ETFs), whose own site turned out to need a login
    for historical data. TIGER's own fund detail page charts each of its
    funds' *own* benchmark-index performance regardless of which provider
    calculates it, so this only works when the ETF being priced is itself
    TIGER-issued (reuses the ticker map already built for TIGER holdings) —
    it can't look up an arbitrary index by name the way the other resolvers
    do. Returns a % of cumulative return since `inception_date` rather than
    an absolute index level, which `compute_risk_stats` doesn't care about
    (it only uses day-over-day % changes)."""
    try:
        ticker_map = fetch_tiger_ticker_map()
    except requests.RequestException:
        return None, None, None
    ksd_fund = ticker_map.get(krx_code)
    if not ksd_fund:
        return None, None, None
    start = inception_date.replace("-", "") if inception_date else (datetime.now() - timedelta(days=3 * 365 + 14)).strftime("%Y%m%d")
    r = requests.get(
        "https://investments.miraeasset.com/tigeretf/ko/product/chart/prdct-profit-list.ajax",
        params={"ksdFund": ksd_fund, "strtDt": start, "endDt": datetime.now().strftime("%Y%m%d"), "period": ""},
        headers={**KODEX_HEADERS, "X-Requested-With": "XMLHttpRequest"},
        timeout=15,
    )
    r.raise_for_status()
    rows = (r.json() or {}).get("rtnData") or []
    dates, levels = [], []
    for row in rows:
        wkdate = row.get("wkdateStr")
        jisu = row.get("jisu")
        if wkdate is None or jisu is None:
            continue
        try:
            dates.append(datetime.strptime(wkdate, "%Y-%m-%d").date())
        except ValueError:
            continue
        levels.append(100 * (1 + jisu / 100))
    return compute_risk_stats(dates, levels)


def fetch_benchmark_risk_stats(benchmark_name, krx_code=None, inception_date=None):
    domestic_code = resolve_domestic_index_code(benchmark_name)
    if domestic_code:
        return fetch_domestic_index_risk_stats(domestic_code)
    overseas_ticker = resolve_overseas_index_ticker(benchmark_name)
    if overseas_ticker:
        return fetch_overseas_risk_stats(overseas_ticker)
    fnindex_code = resolve_fnindex_code(benchmark_name)
    if fnindex_code:
        return fetch_fnindex_risk_stats(fnindex_code)
    if krx_code:
        try:
            return fetch_tiger_benchmark_risk_stats(krx_code, inception_date)
        except requests.RequestException:
            pass
    return None, None, None


def fetch_overseas_risk_stats(symbol):
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
    try:
        r = requests.get(url, params={"range": "3y", "interval": "1d"}, headers=HEADERS, timeout=10)
        r.raise_for_status()
        result = r.json().get("chart", {}).get("result")
    except requests.RequestException:
        return None, None, None
    if not result:
        return None, None, None
    timestamps = result[0].get("timestamp") or []
    quotes = result[0].get("indicators", {}).get("quote") or [{}]
    closes = quotes[0].get("close", [])
    dates = [datetime.utcfromtimestamp(ts).date() if ts is not None else None for ts in timestamps]
    return compute_risk_stats(dates, closes)


def fetch_60d_averages(code):
    """60-trading-day average volume/value, computed from daily OHLCV
    history (KRX doesn't expose a simple public endpoint with this
    pre-computed, so we derive it ourselves)."""
    end = datetime.now().strftime("%Y%m%d")
    start = (datetime.now() - timedelta(days=130)).strftime("%Y%m%d")
    url = f"https://api.stock.naver.com/chart/domestic/item/{code}/day"
    try:
        r = requests.get(url, params={"startDateTime": start, "endDateTime": end}, headers=HEADERS, timeout=8)
        r.raise_for_status()
        rows = r.json()
    except (requests.RequestException, ValueError):
        return {}
    if not isinstance(rows, list) or not rows:
        return {}
    recent = rows[-60:]
    volumes = [row["accumulatedTradingVolume"] for row in recent if row.get("accumulatedTradingVolume") is not None]
    values = [
        row["accumulatedTradingVolume"] * row["closePrice"]
        for row in recent
        if row.get("accumulatedTradingVolume") is not None and row.get("closePrice") is not None
    ]
    if not volumes:
        return {}
    return {
        "avgVolume60d": sum(volumes) / len(volumes),
        "avgTradingValue60d": (sum(values) / len(values)) if values else None,
    }


def fetch_domestic_quote(code):
    listing = None
    try:
        listing = next((it for it in fetch_krx_etf_list() if it.get("itemcode") == code), None)
    except requests.RequestException:
        listing = None

    detail = {}
    try:
        r = requests.get(
            f"https://m.stock.naver.com/api/stock/{code}/integration", headers=HEADERS, timeout=8
        )
        if r.status_code == 200:
            detail = r.json()
    except requests.RequestException:
        detail = {}

    name = (listing or {}).get("itemname") or detail.get("stockName")
    if not name:
        return {"symbol": code, "hasData": False}

    coinfo = fetch_naver_coinfo(code)
    averages_60d = fetch_60d_averages(code)
    volatility, var975, volatility_days = fetch_domestic_risk_stats(code)

    benchmark_volatility, benchmark_var975, benchmark_volatility_days = fetch_benchmark_risk_stats(
        coinfo.get("benchmarkIndex"), krx_code=code, inception_date=coinfo.get("inceptionDate")
    )

    total_map = {i["code"]: i.get("value") for i in detail.get("totalInfos", []) if "code" in i}
    key_ind = detail.get("etfKeyIndicator") or {}

    price = num((listing or {}).get("nowVal")) or num(total_map.get("lastClosePrice"))
    prev_close = num(total_map.get("lastClosePrice"))
    change = price - prev_close if price is not None and prev_close is not None else None
    change_pct = (change / prev_close * 100) if change and prev_close else None

    expense_ratio = key_ind.get("totalFee")
    dividend_yield = key_ind.get("dividendYieldTtm")

    return {
        "symbol": code,
        "name": name,
        "market": "국내",
        "currency": "KRW",
        "price": price,
        "change": change,
        "changePercent": change_pct,
        "previousClose": prev_close,
        "dayHigh": num(total_map.get("highPrice")),
        "dayLow": num(total_map.get("lowPrice")),
        "fiftyTwoWeekHigh": num(total_map.get("highPriceOf52WeeksAdjusted") or total_map.get("highPriceOf52Weeks")),
        "fiftyTwoWeekLow": num(total_map.get("lowPriceOf52WeeksAdjusted") or total_map.get("lowPriceOf52Weeks")),
        "volume": num(total_map.get("accumulatedTradingVolume")),
        "totalAssets": parse_krw(key_ind.get("totalNav")),
        "expenseRatio": (expense_ratio / 100) if expense_ratio is not None else None,
        "category": coinfo.get("category"),
        "fundFamily": key_ind.get("issuerName"),
        "exchange": "KRX",
        "yield": (dividend_yield / 100) if dividend_yield is not None else None,
        "inceptionDate": coinfo.get("inceptionDate"),
        "avgVolume60d": averages_60d.get("avgVolume60d"),
        "avgTradingValue60d": averages_60d.get("avgTradingValue60d"),
        "benchmarkIndex": coinfo.get("benchmarkIndex"),
        "volatility": volatility,
        "volatilityPeriod": format_period_label(volatility_days),
        "var975": var975,
        "var975Period": format_period_label(volatility_days),
        "benchmarkVolatility": benchmark_volatility,
        "benchmarkVolatilityPeriod": format_period_label(benchmark_volatility_days),
        "benchmarkVar975": benchmark_var975,
        "benchmarkVar975Period": format_period_label(benchmark_volatility_days),
        "hasData": price is not None,
        "updatedAt": datetime.now().isoformat(),
    }


def yahoo_search(query):
    url = "https://query2.finance.yahoo.com/v1/finance/search"
    params = {"q": query, "quotesCount": 8, "newsCount": 0, "lang": "ko-KR"}
    r = requests.get(url, params=params, headers=HEADERS, timeout=8)
    r.raise_for_status()
    quotes = r.json().get("quotes", [])
    results = []
    for q in quotes:
        symbol = q.get("symbol")
        if not symbol:
            continue
        results.append(
            {
                "symbol": symbol,
                "name": q.get("shortname") or q.get("longname") or symbol,
                "exchange": q.get("exchDisp", ""),
                "type": q.get("quoteType", ""),
                "market": market_of(symbol),
            }
        )
    return results


def resolve_candidates(query):
    query = query.strip()
    candidates = list(search_krx_etfs(query))
    existing_symbols = {c["symbol"] for c in candidates}

    try:
        search_results = yahoo_search(query)
    except requests.RequestException:
        search_results = []

    etf_first = [c for c in search_results if c["type"] == "ETF"]
    others = [c for c in search_results if c["type"] != "ETF"]
    for c in etf_first + others:
        if c["symbol"] not in existing_symbols:
            candidates.append(c)
            existing_symbols.add(c["symbol"])

    return candidates


def fetch_chart_meta(symbol):
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
    r = requests.get(url, headers=HEADERS, timeout=8)
    if r.status_code == 404:
        return None
    r.raise_for_status()
    result = r.json().get("chart", {}).get("result")
    if not result:
        return None
    return result[0].get("meta", {})


def fetch_fund_detail(symbol):
    """Best-effort fetch of fund-profile fields. Yahoo doesn't have this
    data for every ticker (notably many KRX-listed ETFs), so callers must
    tolerate an empty dict."""
    modules = "summaryDetail,defaultKeyStatistics,fundProfile"
    for attempt in range(2):
        try:
            session, crumb = get_session_and_crumb()
            url = f"https://query1.finance.yahoo.com/v10/finance/quoteSummary/{symbol}"
            r = session.get(url, params={"modules": modules, "crumb": crumb}, timeout=8)
            if r.status_code in (401, 429):
                reset_session()
                continue
            r.raise_for_status()
            result = r.json().get("quoteSummary", {}).get("result")
            return result[0] if result else {}
        except requests.RequestException:
            reset_session()
    return {}


def fetch_quote(symbol):
    krx_code = resolve_krx_code(symbol)
    if krx_code:
        return fetch_domestic_quote(krx_code)

    meta = fetch_chart_meta(symbol)
    if not meta or meta.get("regularMarketPrice") is None:
        return {"symbol": symbol, "hasData": False}

    detail = fetch_fund_detail(symbol)
    summary_detail = detail.get("summaryDetail") or {}
    fund_profile = detail.get("fundProfile") or {}
    key_stats = detail.get("defaultKeyStatistics") or {}
    fees = fund_profile.get("feesExpensesInvestment") or {}

    price = meta.get("regularMarketPrice")
    prev_close = meta.get("previousClose") or meta.get("chartPreviousClose")
    change = price - prev_close if prev_close is not None else None
    change_pct = (change / prev_close * 100) if change is not None and prev_close else None
    volatility, var975, volatility_days = fetch_overseas_risk_stats(symbol)

    return {
        "symbol": symbol,
        "name": meta.get("longName") or meta.get("shortName") or symbol,
        "market": market_of(symbol),
        "currency": meta.get("currency", ""),
        "price": price,
        "change": change,
        "changePercent": change_pct,
        "previousClose": prev_close,
        "dayHigh": meta.get("regularMarketDayHigh"),
        "dayLow": meta.get("regularMarketDayLow"),
        "fiftyTwoWeekHigh": meta.get("fiftyTwoWeekHigh"),
        "fiftyTwoWeekLow": meta.get("fiftyTwoWeekLow"),
        "volume": meta.get("regularMarketVolume"),
        "totalAssets": raw(summary_detail, "totalAssets"),
        "expenseRatio": raw(fees, "annualReportExpenseRatio"),
        "category": fund_profile.get("categoryName"),
        "fundFamily": fund_profile.get("family"),
        "exchange": meta.get("fullExchangeName") or meta.get("exchangeName"),
        "yield": raw(summary_detail, "yield"),
        "inceptionDate": raw(key_stats, "fundInceptionDate"),
        "avgVolume60d": None,
        "avgTradingValue60d": None,
        "benchmarkIndex": None,
        "volatility": volatility,
        "volatilityPeriod": format_period_label(volatility_days),
        "var975": var975,
        "var975Period": format_period_label(volatility_days),
        "benchmarkVolatility": None,
        "benchmarkVolatilityPeriod": None,
        "benchmarkVar975": None,
        "benchmarkVar975Period": None,
        "hasData": True,
        "updatedAt": datetime.now().isoformat(),
    }


KOFIA_URL = "https://dis.kofia.or.kr/proframeWeb/XMLSERVICES/"
KOFIA_REFERER = (
    "https://dis.kofia.or.kr/websquare/index.jsp?w2xPath=/wq/fundann/DISFundStdPrice.xml"
    "&divisionId=MDIS01004001000000&serviceId=SDIS01004001000"
)
KOFIA_HEADERS = {
    "User-Agent": HEADERS["User-Agent"],
    "Content-Type": "text/xml; charset=UTF-8",
    "Referer": KOFIA_REFERER,
}


def kofia_last_business_day():
    d = datetime.now() - timedelta(days=1)
    while d.weekday() >= 5:
        d -= timedelta(days=1)
    return d.strftime("%Y%m%d")


# KOFIA's fund search filters by a "기준일자" (as-of date), but that day's
# NAV data isn't always published by the time we'd naively assume (T-1
# business day) — publication can lag by a few extra days. Rather than
# hardcode an assumed lag, we probe backward from T-1 until we find a date
# that actually has data, and cache the result briefly since it only
# changes once a day when the next batch is published.
_kofia_base_date_cache = {"date": None, "checked_at": 0}
_KOFIA_BASE_DATE_TTL_SECONDS = 3600


def kofia_probe_has_data(date_str):
    body = f"""<?xml version="1.0" encoding="utf-8"?>
<message>
  <proframeHeader>
    <pfmAppName>FS-DIS2</pfmAppName>
    <pfmSvcName>DISFundStdPriceSO</pfmSvcName>
    <pfmFnName>select</pfmFnName>
  </proframeHeader>
  <systemHeader></systemHeader>
    <DISCondFuncDTO>
    <tmpV30>{date_str}</tmpV30>
    <tmpV3></tmpV3>
    <tmpV4></tmpV4>
    <tmpV7>1</tmpV7>
    <tmpV5></tmpV5>
    <tmpV11></tmpV11>
    <tmpV12>코스피200</tmpV12>
    <tmpV50></tmpV50>
    <tmpV51></tmpV51>
</DISCondFuncDTO>
</message>
"""
    r = requests.post(KOFIA_URL, data=body.encode("utf-8"), headers=KOFIA_HEADERS, timeout=15, verify=False)
    r.raise_for_status()
    m = re.search(r"<dbio_total_count_>(\d+)</dbio_total_count_>", r.text)
    return bool(m) and int(m.group(1)) > 0


def kofia_resolve_base_date():
    now = time.time()
    cache = _kofia_base_date_cache
    if cache["date"] and now - cache["checked_at"] < _KOFIA_BASE_DATE_TTL_SECONDS:
        return cache["date"]
    d = datetime.now() - timedelta(days=1)
    resolved = None
    for _ in range(10):
        while d.weekday() >= 5:
            d -= timedelta(days=1)
        date_str = d.strftime("%Y%m%d")
        try:
            if kofia_probe_has_data(date_str):
                resolved = date_str
                break
        except requests.RequestException:
            pass
        d -= timedelta(days=1)
    resolved = resolved or kofia_last_business_day()
    cache["date"] = resolved
    cache["checked_at"] = now
    return resolved


def parse_kofia_date(value):
    if not value or len(value) != 8:
        return None
    return f"{value[:4]}-{value[4:6]}-{value[6:8]}"


def fetch_kofia_funds(name_query):
    """Search public (공모) mutual funds by name via KOFIA's electronic
    disclosure system (dis.kofia.or.kr). No login required, confirmed by
    hand via the site's own search form. Its TLS chain isn't recognized by
    Python's bundled CA list even though OS-level clients (e.g. curl on
    Windows) trust it fine, so verification is disabled for this one
    external call — no credentials or sensitive data cross this request,
    it's a public read-only fund lookup."""
    body = f"""<?xml version="1.0" encoding="utf-8"?>
<message>
  <proframeHeader>
    <pfmAppName>FS-DIS2</pfmAppName>
    <pfmSvcName>DISFundStdPriceSO</pfmSvcName>
    <pfmFnName>select</pfmFnName>
  </proframeHeader>
  <systemHeader></systemHeader>
    <DISCondFuncDTO>
    <tmpV30>{kofia_resolve_base_date()}</tmpV30>
    <tmpV3></tmpV3>
    <tmpV4></tmpV4>
    <tmpV7>1</tmpV7>
    <tmpV5></tmpV5>
    <tmpV11></tmpV11>
    <tmpV12>{name_query}</tmpV12>
    <tmpV50></tmpV50>
    <tmpV51></tmpV51>
</DISCondFuncDTO>
</message>
"""
    r = requests.post(KOFIA_URL, data=body.encode("utf-8"), headers=KOFIA_HEADERS, timeout=20, verify=False)
    r.raise_for_status()
    blocks = re.findall(r"<selectMeta>(.*?)</selectMeta>", r.text, re.S)

    def field(block, tag):
        m = re.search(rf"<{tag}>([^<]*)</{tag}>", block)
        return m.group(1).strip() if m and m.group(1).strip() else None

    results = []
    for b in blocks:
        name = field(b, "tmpV2")
        code = field(b, "tmpV12")
        if not name or not code:
            continue
        aum_mm = field(b, "tmpV5")
        nav = field(b, "tmpV6")
        results.append(
            {
                "code": code,
                "name": name,
                "company": field(b, "tmpV1"),
                "type": field(b, "tmpV3"),
                "inceptionDate": parse_kofia_date(field(b, "tmpV4")),
                "aum": float(aum_mm) * 1_000_000 if aum_mm else None,
                "nav": float(nav) if nav else None,
                "baseDate": parse_kofia_date(field(b, "tmpV14")),
                "market": "공모펀드",
            }
        )
    return results


@app.route("/api/fund/search")
def api_fund_search():
    q = request.args.get("q", "").strip()
    if not q:
        return jsonify({"error": "검색어를 입력해주세요."}), 400
    try:
        results = fetch_kofia_funds(q)
    except requests.RequestException as e:
        return jsonify({"error": f"검색 중 오류가 발생했습니다: {e}"}), 502
    return jsonify({"results": results[:30]})


def fetch_kofia_nav_history(code, start_date, end_date):
    """Daily 기준가(NAV) history for one fund over [start_date, end_date]
    (YYYYMMDD strings), via KOFIA's "기준가격변동추이" service. Computing
    this for every search result would mean one heavy request per row, so
    callers should only use this for a single fund the user has opened."""
    body = f"""<?xml version="1.0" encoding="utf-8"?>
<message>
  <proframeHeader>
    <pfmAppName>FS-DIS2</pfmAppName>
    <pfmSvcName>DISFundStdPrcStutSO</pfmSvcName>
    <pfmFnName>select</pfmFnName>
  </proframeHeader>
  <systemHeader></systemHeader>
    <DISCondFuncDTO>
    <tmpV30>{start_date}</tmpV30>
    <tmpV31>{end_date}</tmpV31>
    <tmpV10>0</tmpV10>
    <tmpV12>{code}</tmpV12>
</DISCondFuncDTO>
</message>
"""
    r = requests.post(KOFIA_URL, data=body.encode("utf-8"), headers=KOFIA_HEADERS, timeout=30, verify=False)
    r.raise_for_status()
    blocks = re.findall(r"<selectMeta>(.*?)</selectMeta>", r.text, re.S)

    dates, closes = [], []
    for b in blocks:
        m1 = re.search(r"<tmpV1>([^<]*)</tmpV1>", b)
        m2 = re.search(r"<tmpV2>([^<]*)</tmpV2>", b)
        raw_date = m1.group(1).strip() if m1 else None
        raw_nav = m2.group(1).strip() if m2 else None
        try:
            dates.append(datetime.strptime(raw_date, "%Y%m%d").date() if raw_date else None)
        except ValueError:
            dates.append(None)
        try:
            closes.append(float(raw_nav) if raw_nav else None)
        except ValueError:
            closes.append(None)
    return dates, closes


def fetch_kofia_risk_stats(code):
    end_date = kofia_resolve_base_date()
    start_date = (datetime.now() - timedelta(days=3 * 365 + 14)).strftime("%Y%m%d")
    dates, closes = fetch_kofia_nav_history(code, start_date, end_date)
    volatility, var975, days_covered = compute_risk_stats(dates, closes)
    return {
        "volatility": volatility,
        "volatilityPeriod": format_period_label(days_covered),
        "var975": var975,
        "var975Period": format_period_label(days_covered),
    }


@app.route("/api/fund/risk/<path:code>")
def api_fund_risk(code):
    try:
        return jsonify(fetch_kofia_risk_stats(code))
    except requests.RequestException as e:
        return jsonify({"error": f"변동성 계산 중 오류가 발생했습니다: {e}"}), 502


# Each ETF issuer publishes its own funds' full daily holdings (구성종목) on
# its own site, no login required, but there's no single shared source (KRX's
# holdings page requires login). Each issuer needs its own per-site
# integration; only KODEX/SOL/TIGER are implemented so far, covering the
# majority of domestic ETFs by AUM. Other issuers (ACE/KBSTAR·RISE/...) fall
# through to the "not supported" message. Sites' own terms generally prohibit
# unauthorized bulk databasing of their content, so we only fetch a single
# ETF's holdings on demand (when a user opens that ETF's detail card) rather
# than mirroring the whole catalog.
KODEX_HEADERS = {"User-Agent": HEADERS["User-Agent"]}
_kodex_ticker_map_cache = {"map": None, "fetched_at": 0}
_KODEX_TICKER_MAP_TTL_SECONDS = 3600


def fetch_kodex_ticker_map():
    now = time.time()
    cache = _kodex_ticker_map_cache
    if cache["map"] is not None and now - cache["fetched_at"] < _KODEX_TICKER_MAP_TTL_SECONDS:
        return cache["map"]
    mapping = {}
    page = 1
    while True:
        r = requests.get(
            "https://m.samsungfund.com/api/v1/kodex/product.do",
            params={"srchTerm": "", "ordrSort": "DESC", "ordrColm": "NAV", "pageNo": page},
            headers=KODEX_HEADERS,
            timeout=15,
        )
        r.raise_for_status()
        items = r.json()
        if not items:
            break
        for it in items:
            ticker = it.get("stkTicker")
            fund_id = it.get("fId")
            if ticker and fund_id:
                mapping[ticker] = fund_id
        if len(items) < 20 or page > 20:  # 20/page; hard cap as a safety net
            break
        page += 1
    cache["map"] = mapping
    cache["fetched_at"] = now
    return mapping


def fetch_kodex_holdings(krx_code):
    """Return {"holdings": [...], "asOfDate": "..."} for a KODEX ETF, or
    None if krx_code isn't a KODEX-branded fund."""
    try:
        ticker_map = fetch_kodex_ticker_map()
    except requests.RequestException:
        return None
    fund_id = ticker_map.get(krx_code)
    if not fund_id:
        return None
    r = requests.get(f"https://m.samsungfund.com/api/v1/kodex/product/{fund_id}.do", headers=KODEX_HEADERS, timeout=15)
    r.raise_for_status()
    pdf = (r.json() or {}).get("pdf") or {}
    holdings = []
    for item in pdf.get("list") or []:
        weight = item.get("ratio")
        try:
            weight = float(weight) if weight not in (None, "") else None
        except ValueError:
            weight = None
        holdings.append(
            {
                "code": item.get("itmNo"),
                "name": item.get("secNm"),
                "weight": weight,
            }
        )
    return {
        "holdings": holdings,
        "asOfDate": parse_kofia_date(pdf.get("gijunYMD")),
    }


_sol_ticker_map_cache = {"map": None, "fetched_at": 0}
_SOL_TICKER_MAP_TTL_SECONDS = 3600


def fetch_sol_ticker_map():
    now = time.time()
    cache = _sol_ticker_map_cache
    if cache["map"] is not None and now - cache["fetched_at"] < _SOL_TICKER_MAP_TTL_SECONDS:
        return cache["map"]
    r = requests.post(
        "https://www.soletf.com/api/common/searchByEtfNameOrFilter",
        data={"viewCount": 300},
        headers=KODEX_HEADERS,
        timeout=15,
    )
    r.raise_for_status()
    items = (r.json() or {}).get("items") or []
    mapping = {}
    for it in items:
        ticker = it.get("ETF_CD6")
        fund_cd = it.get("FUND_CD")
        if ticker and fund_cd:
            mapping[ticker] = fund_cd
    cache["map"] = mapping
    cache["fetched_at"] = now
    return mapping


def fetch_sol_holdings(krx_code):
    """Return holdings for a SOL (신한자산운용) ETF, or None if krx_code isn't
    a SOL-branded fund."""
    try:
        ticker_map = fetch_sol_ticker_map()
    except requests.RequestException:
        return None
    fund_cd = ticker_map.get(krx_code)
    if not fund_cd:
        return None
    items = []
    work_dt = None
    for days_back in range(10):
        work_dt = (datetime.now() - timedelta(days=days_back)).strftime("%Y%m%d")
        r = requests.get(
            "https://www.soletf.com/api/fund/pdfList",
            params={"fund_cd": fund_cd, "work_dt": work_dt},
            headers=KODEX_HEADERS,
            timeout=15,
        )
        r.raise_for_status()
        items = r.json() or []
        if items:
            break
    holdings = []
    for item in items:
        wt = item.get("WT_DISP")
        try:
            weight = float(str(wt).replace("%", "")) if wt not in (None, "") else None
        except ValueError:
            weight = None
        holdings.append({"code": item.get("STOCK_CODE"), "name": item.get("SEC_NM"), "weight": weight})
    return {"holdings": holdings, "asOfDate": parse_kofia_date(work_dt) if items else None}


_tiger_ticker_map_cache = {"map": None, "fetched_at": 0}
_TIGER_TICKER_MAP_TTL_SECONDS = 3600


def fetch_tiger_ticker_map():
    """Map KRX 6-char code -> Mirae Asset's ksdFund ISIN-style code. The KRX
    code is embedded in the ISIN itself (KR7 + 6-char code + 3 more chars),
    so we only need one listing call to build the whole map."""
    now = time.time()
    cache = _tiger_ticker_map_cache
    if cache["map"] is not None and now - cache["fetched_at"] < _TIGER_TICKER_MAP_TTL_SECONDS:
        return cache["map"]
    r = requests.post(
        "https://investments.miraeasset.com/tigeretf/ko/product/search/list.ajax",
        data={
            "pdfNameYn": "N",
            "pageIndex": 1,
            "firstIndex": 0,
            "listCnt": 500,
            "periodType": "short",
            "listType": "table",
            "q": "",
        },
        headers=KODEX_HEADERS,
        timeout=20,
    )
    r.raise_for_status()
    mapping = {}
    for m in re.finditer(r'data-ksd-fund="(KR7[0-9A-Z]{9})"', r.text):
        ksd_fund = m.group(1)
        mapping[ksd_fund[3:9]] = ksd_fund
    cache["map"] = mapping
    cache["fetched_at"] = now
    return mapping


def fetch_tiger_holdings(krx_code):
    """Return holdings for a TIGER (미래에셋자산운용) ETF, or None if krx_code
    isn't a TIGER-branded fund."""
    try:
        ticker_map = fetch_tiger_ticker_map()
    except requests.RequestException:
        return None
    ksd_fund = ticker_map.get(krx_code)
    if not ksd_fund:
        return None
    r = requests.get(
        "https://investments.miraeasset.com/tigeretf/ko/product/search/detail/pdf.ajax",
        params={"ksdFund": ksd_fund},
        headers=KODEX_HEADERS,
        timeout=20,
    )
    r.raise_for_status()
    m = re.search(r'name="fixDate"[^>]*value="([\d.]+)"', r.text)
    fix_date = m.group(1) if m else ""

    r2 = requests.get(
        "https://investments.miraeasset.com/tigeretf/ko/product/search/detail/pdfListAjax.ajax",
        params={
            "ksdFund": ksd_fund,
            "pageIndex": 1,
            "firstIndex": 0,
            "listCnt": 500,
            "fixDate": fix_date,
            "prfPrd": "Week01",
            "order": "SRD",
        },
        headers=KODEX_HEADERS,
        timeout=20,
    )
    r2.raise_for_status()
    holdings = []
    for row in re.finditer(r"<tr[^>]*>(.*?)</tr>", r2.text, re.S):
        tds = re.findall(r"<td[^>]*>(.*?)</td>", row.group(1), re.S)
        if len(tds) < 5:
            continue
        code = re.sub(r"<[^>]+>", "", tds[0]).strip()
        name = re.sub(r"<[^>]+>", "", tds[1]).strip()
        weight_raw = re.sub(r"<[^>]+>", "", tds[4]).strip()
        try:
            weight = float(weight_raw) if weight_raw else None
        except ValueError:
            weight = None
        if code:
            holdings.append({"code": code, "name": name, "weight": weight})
    return {"holdings": holdings, "asOfDate": fix_date.replace(".", "-") if fix_date else None}


def fetch_kiwoom_holdings(krx_code):
    """Return holdings for a KIWOOM/KOSEF (키움투자자산운용) ETF, or None if
    krx_code isn't one of theirs. No ticker map is needed here — the site's
    API takes the KRX code directly and returns an empty list for codes it
    doesn't recognize, so a persistently empty result (across the lookback
    window) is treated as "not a KIWOOM fund"."""
    items = []
    work_dt = None
    for days_back in range(10):
        work_dt = (datetime.now() - timedelta(days=days_back)).strftime("%Y%m%d")
        r = requests.post(
            "https://www.kiwoometf.com/service/etf/KO02010200MAjax4",
            data={"schGubun1": krx_code, "startDate": work_dt},
            headers=KODEX_HEADERS,
            timeout=15,
        )
        r.raise_for_status()
        items = (r.json() or {}).get("pdfList") or []
        if items:
            break
    if not items:
        return None
    holdings = []
    for item in items:
        code = item.get("itemCode") or ""
        if code.startswith("KR7") and len(code) >= 9:
            code = code[3:9]
        wt = item.get("ratio")
        try:
            weight = float(str(wt).replace("%", "")) if wt not in (None, "") else None
        except ValueError:
            weight = None
        holdings.append({"code": code, "name": item.get("itemTitle"), "weight": weight})
    return {"holdings": holdings, "asOfDate": parse_kofia_date(work_dt)}


def fetch_rise_holdings(krx_code):
    """Return holdings for a RISE (KB자산운용, 구 KBSTAR) ETF, or None if
    krx_code isn't one of theirs. The fund detail page is fully
    server-rendered (holdings table included), so a single GET is enough
    once we've resolved the KRX code to RISE's own internal fund code via
    their search endpoint."""
    r = requests.post(
        "https://www.riseetf.co.kr/prod/finder/listJquery",
        data={"searchText": krx_code},
        headers=KODEX_HEADERS,
        timeout=15,
    )
    r.raise_for_status()
    m = re.search(r"finderDetail/([0-9A-Za-z]+)", r.text)
    if not m:
        return None
    fund_cd = m.group(1)

    r2 = requests.get(f"https://www.riseetf.co.kr/prod/finderDetail/{fund_cd}", headers=KODEX_HEADERS, timeout=20)
    r2.raise_for_status()
    html = r2.text
    date_m = re.search(r'id="datepicker_pdf" value="([\d\-]+)"', html)
    as_of = date_m.group(1) if date_m else None

    body_m = re.search(r'data-class="tab3PdfList">(.*?)</tbody>', html, re.S)
    holdings = []
    if body_m:
        for row in re.finditer(r"<tr>(.*?)</tr>", body_m.group(1), re.S):
            cells = re.findall(r"<t[hd][^>]*>(.*?)</t[hd]>", row.group(1), re.S)
            if len(cells) < 5:
                continue
            name = re.sub(r"<[^>]+>", "", cells[1]).strip()
            code = re.sub(r"<[^>]+>", "", cells[2]).strip()
            if code.startswith("KR7") and len(code) >= 9:
                code = code[3:9]
            weight_raw = re.sub(r"<[^>]+>", "", cells[4]).strip()
            try:
                weight = float(weight_raw) if weight_raw else None
            except ValueError:
                weight = None
            holdings.append({"code": code, "name": name, "weight": weight})
    return {"holdings": holdings, "asOfDate": as_of}


# Market (KOSPI/KOSDAQ) + market cap + market-cap rank for individual
# constituent stocks inside ETF holdings, sourced from Naver's mobile stock
# API (paginated market-cap ranking, 100 rows/page; ~25 pages for KOSPI +
# ~19 for KOSDAQ). A full pass is too slow to do inline in a request (it hit
# gunicorn's worker timeout on Render and 502'd), so it's refreshed in a
# background thread instead: a request that finds the cache missing/stale
# kicks off exactly one rebuild and immediately uses whatever's cached (or
# no enrichment at all, the first time) rather than waiting on it.
_market_cap_cache = {"map": None, "fetched_at": 0, "building": False}
_market_cap_lock = threading.Lock()
_MARKET_CAP_TTL_SECONDS = 3600


def _fetch_market_value_page(market, page):
    r = requests.get(
        f"https://m.stock.naver.com/api/stocks/marketValue/{market}",
        params={"page": page, "pageSize": 100},
        headers=HEADERS,
        timeout=8,
    )
    r.raise_for_status()
    return r.json()


def _fetch_market_value_all(market):
    first = _fetch_market_value_page(market, 1)
    stocks = list(first.get("stocks") or [])
    total = first.get("totalCount") or 0
    total_pages = -(-total // 100)  # ceil
    if total_pages > 1:
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as ex:
            futures = [ex.submit(_fetch_market_value_page, market, p) for p in range(2, total_pages + 1)]
            for fut in futures:
                try:
                    stocks.extend(fut.result().get("stocks") or [])
                except requests.RequestException:
                    continue  # a dropped page just leaves a small rank gap; best-effort
    return stocks


def _build_market_cap_map():
    try:
        mapping = {}
        for market, label in (("KOSPI", "코스피"), ("KOSDAQ", "코스닥")):
            try:
                stocks = _fetch_market_value_all(market)
            except requests.RequestException:
                continue
            for rank, s in enumerate(stocks, start=1):
                code = s.get("itemCode")
                if not code:
                    continue
                market_value = num(s.get("marketValue"))  # Naver reports this in 억원 (100M-won) units
                mapping[code] = {
                    "market": label,
                    "marketCap": market_value * 1e8 if market_value is not None else None,
                    "marketCapRank": rank,
                }
        if mapping:
            _market_cap_cache["map"] = mapping
    finally:
        # Stamp fetched_at even on failure so a persistently failing
        # upstream is retried at most once per TTL, not on every request.
        _market_cap_cache["fetched_at"] = time.time()
        _market_cap_cache["building"] = False


def fetch_market_cap_map():
    """Return whatever market-cap map is currently cached (possibly stale,
    possibly empty on first-ever call) without blocking. If the cache is
    missing or past its TTL, kick off exactly one background rebuild."""
    now = time.time()
    cache = _market_cap_cache
    is_stale = cache["map"] is None or now - cache["fetched_at"] >= _MARKET_CAP_TTL_SECONDS
    if is_stale and not cache["building"]:
        with _market_cap_lock:
            if not cache["building"]:
                cache["building"] = True
                threading.Thread(target=_build_market_cap_map, daemon=True).start()
    return cache["map"] or {}


# Some domestic ETFs (e.g. TIGER/KODEX 미국S&P500) hold US-listed stocks
# directly, disclosed in the PDF using Bloomberg-style codes like
# "NVDA US Equity". US market-cap ranking works the same way as the KRX one
# above (background-refreshed, non-blocking), but via Yahoo Finance's
# screener endpoint instead of Naver's, and scoped to the top ~2,000 US
# equities by market cap (8 pages of 250) rather than the whole market —
# realistic ETF holdings (S&P 500 / Nasdaq 100 / sector trackers) don't dip
# below that, and it keeps the background rebuild cheap.
_BLOOMBERG_US_EQUITY_RE = re.compile(r"^([A-Z.]{1,6})\s+US\s+Equity$", re.I)
_YAHOO_EXCHANGE_LABELS = {
    "NasdaqGS": "나스닥",
    "NasdaqGM": "나스닥",
    "NasdaqCM": "나스닥",
    "NYSE": "NYSE",
    "NYSEArca": "NYSE Arca",
    "NYSEAMERICAN": "NYSE American",
    "BATS": "BATS",
    "CBOE": "CBOE",
}
_US_MARKET_CAP_PAGES = 8
_us_market_cap_cache = {"map": None, "fetched_at": 0, "building": False}
_us_market_cap_lock = threading.Lock()


def _fetch_us_market_cap_page(session, crumb, offset):
    body = {
        "size": 250,
        "offset": offset,
        "sortField": "intradaymarketcap",
        "sortType": "DESC",
        "quoteType": "EQUITY",
        "query": {"operator": "AND", "operands": [{"operator": "EQ", "operands": ["region", "us"]}]},
    }
    r = session.post(
        "https://query1.finance.yahoo.com/v1/finance/screener",
        params={"crumb": crumb},
        json=body,
        timeout=15,
    )
    r.raise_for_status()
    results = r.json().get("finance", {}).get("result") or [{}]
    return results[0].get("quotes") or []


def _build_us_market_cap_map():
    try:
        session, crumb = get_session_and_crumb()
        mapping = {}
        rank = 1
        for page in range(_US_MARKET_CAP_PAGES):
            try:
                quotes = _fetch_us_market_cap_page(session, crumb, offset=page * 250)
            except requests.RequestException:
                break
            if not quotes:
                break
            for q in quotes:
                symbol = q.get("symbol")
                if not symbol:
                    continue
                exchange = q.get("fullExchangeName") or ""
                mapping[symbol.upper()] = {
                    "market": _YAHOO_EXCHANGE_LABELS.get(exchange, exchange or None),
                    "marketCap": q.get("marketCap"),
                    "marketCapRank": rank,
                    "currency": "USD",
                }
                rank += 1
        if mapping:
            _us_market_cap_cache["map"] = mapping
    except requests.RequestException:
        pass
    finally:
        # Stamp fetched_at even on failure (e.g. Yahoo's crumb-authenticated
        # endpoints being blocked from this host entirely) so a persistently
        # failing upstream is retried at most once per TTL instead of on
        # every single request that needs it.
        _us_market_cap_cache["fetched_at"] = time.time()
        _us_market_cap_cache["building"] = False


def fetch_us_market_cap_map():
    now = time.time()
    cache = _us_market_cap_cache
    is_stale = cache["map"] is None or now - cache["fetched_at"] >= _MARKET_CAP_TTL_SECONDS
    if is_stale and not cache["building"]:
        with _us_market_cap_lock:
            if not cache["building"]:
                cache["building"] = True
                threading.Thread(target=_build_us_market_cap_map, daemon=True).start()
    return cache["map"] or {}


# Fallback exchange lookup for US tickers the screener-based map above
# doesn't have. Yahoo's crumb-authenticated endpoints (quoteSummary,
# screener) turned out to be blocked from Render's outbound IP — confirmed
# by the fact that quoteSummary-sourced fields (AUM/expense ratio for
# overseas ETFs) were already silently empty in production before this
# feature existed. The unauthenticated chart endpoint (`/v8/finance/chart`),
# which the app already relies on for overseas price data, is NOT blocked,
# and its `meta` includes the listing exchange (just not market cap or
# rank) — so it's used here as a same-request-shape fallback, individually
# per ticker but cached indefinitely-ish and fetched in the background so a
# holdings view is never blocked on it.
_US_EXCHANGE_CACHE_TTL = 24 * 3600
_US_EXCHANGE_FALLBACK_LIMIT = 15
_us_exchange_cache = {}
_us_exchange_pending = set()
_us_exchange_lock = threading.Lock()


def _fetch_us_chart_exchange(ticker):
    try:
        r = requests.get(f"https://query1.finance.yahoo.com/v8/finance/chart/{ticker}", headers=HEADERS, timeout=8)
        r.raise_for_status()
        result = (r.json().get("chart") or {}).get("result") or [{}]
        meta = result[0].get("meta") or {}
        return meta.get("fullExchangeName") or meta.get("exchangeName")
    except requests.RequestException:
        return None


def _background_fetch_us_exchanges(tickers):
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
            results = dict(zip(tickers, ex.map(_fetch_us_chart_exchange, tickers)))
        now = time.time()
        with _us_exchange_lock:
            for t, exch in results.items():
                _us_exchange_cache[t] = {"exchange": exch, "fetched_at": now}
    finally:
        with _us_exchange_lock:
            _us_exchange_pending.difference_update(tickers)


def get_us_exchange_map(tickers):
    """Non-blocking: returns whatever's already cached for ALL of `tickers`
    (no limit on this side — once a ticker's cached, every holding using it
    benefits, however many there are), and kicks off a background fetch for
    up to _US_EXCHANGE_FALLBACK_LIMIT of the still-uncached ones. That cap
    throttles how many *new* lookups start per call (keeping each
    background thread pool small on constrained hosting) — it doesn't limit
    which holdings can ever end up enriched; a fund with hundreds of US
    names just fills in gradually across repeated views instead of all at
    once. Tickers already being fetched by an earlier, still-running call
    are skipped so repeat requests don't stack up duplicate thread pools."""
    now = time.time()
    with _us_exchange_lock:
        cached = {
            t: v["exchange"]
            for t, v in _us_exchange_cache.items()
            if t in tickers and now - v["fetched_at"] < _US_EXCHANGE_CACHE_TTL
        }
        candidates = [t for t in tickers if t not in cached and t not in _us_exchange_pending]
        to_fetch = candidates[:_US_EXCHANGE_FALLBACK_LIMIT]
        _us_exchange_pending.update(to_fetch)
    if to_fetch:
        threading.Thread(target=_background_fetch_us_exchanges, args=(to_fetch,), daemon=True).start()
    return cached


def enrich_holdings_with_market_cap(holdings):
    try:
        kr_map = fetch_market_cap_map()
    except requests.RequestException:
        kr_map = {}
    try:
        us_map = fetch_us_market_cap_map()
    except requests.RequestException:
        us_map = {}

    fallback_tickers = []
    fallback_indices = {}
    for i, h in enumerate(holdings):
        code = h.get("code") or ""
        info = kr_map.get(code)
        if not info:
            m = _BLOOMBERG_US_EQUITY_RE.match(code)
            if m:
                ticker = m.group(1).upper().replace(".", "-")
                info = us_map.get(ticker)
                if not info:
                    fallback_indices[i] = ticker
                    fallback_tickers.append(ticker)
        h["market"] = info["market"] if info else None
        h["marketCap"] = info["marketCap"] if info else None
        h["marketCapRank"] = info["marketCapRank"] if info else None
        h["currency"] = info.get("currency", "KRW") if info else None

    if fallback_tickers:
        # holdings are weight-sorted by every source, so fallback_tickers
        # already lists the most-viewed names first — that ordering is what
        # get_us_exchange_map uses to decide which uncached tickers to fetch
        # first when it throttles new lookups (see its docstring).
        exchange_map = get_us_exchange_map(fallback_tickers)
        for i, ticker in fallback_indices.items():
            exchange = exchange_map.get(ticker)
            if exchange:
                holdings[i]["market"] = _YAHOO_EXCHANGE_LABELS.get(exchange, exchange)
                holdings[i]["currency"] = "USD"
    return holdings


_ace_ticker_map_cache = {"map": None, "fetched_at": 0}
_ACE_TICKER_MAP_TTL_SECONDS = 3600


def fetch_ace_ticker_map():
    """ACE's own API host (papi.aceetf.co.kr — separate from the www site
    that serves the pages, which is why earlier attempts against www 404'd)
    exposes the whole fund list in one call; badge.stockCode is the plain
    KRX ticker, fundCd is the ISIN-style code its per-fund endpoints want."""
    now = time.time()
    cache = _ace_ticker_map_cache
    if cache["map"] is not None and now - cache["fetched_at"] < _ACE_TICKER_MAP_TTL_SECONDS:
        return cache["map"]
    r = requests.get(
        "https://papi.aceetf.co.kr/api/funds",
        params={"page": 1, "size": 300},
        headers=KODEX_HEADERS,
        timeout=15,
    )
    r.raise_for_status()
    items = (r.json() or {}).get("data") or []
    mapping = {}
    for it in items:
        ticker = (it.get("badge") or {}).get("stockCode")
        fund_cd = it.get("fundCd")
        if ticker and fund_cd:
            mapping[ticker] = fund_cd
    cache["map"] = mapping
    cache["fetched_at"] = now
    return mapping


def fetch_ace_holdings(krx_code):
    """Return holdings for an ACE (한국투자신탁운용) ETF, or None if
    krx_code isn't one of theirs."""
    try:
        ticker_map = fetch_ace_ticker_map()
    except requests.RequestException:
        return None
    fund_cd = ticker_map.get(krx_code)
    if not fund_cd:
        return None
    r = requests.get(
        f"https://papi.aceetf.co.kr/api/funds/{fund_cd}/pdf",
        params={"page": 1, "size": 1000},
        headers={**KODEX_HEADERS, "Accept": "application/json"},
        timeout=15,
    )
    r.raise_for_status()
    data = r.json() or {}
    holdings = []
    for item in data.get("pdfList") or []:
        holdings.append({"code": item.get("jm_KSC_CD"), "name": item.get("sec_NM"), "weight": item.get("wg")})
    return {"holdings": holdings, "asOfDate": data.get("std_DT")}


def fetch_plus_holdings(krx_code):
    """Return holdings for a PLUS (한화자산운용, 구 ARIRANG) ETF, or None if
    krx_code isn't one of theirs. `n` is the plain KRX ticker directly — no
    separate ticker map needed. The `d` (date, YYYYMMDD) query param is
    required; omitting it silently falls through to the SPA shell instead
    of erroring, which is why this wasn't found on the first attempt."""
    items = []
    work_dt = None
    for days_back in range(10):
        work_dt = (datetime.now() - timedelta(days=days_back)).strftime("%Y%m%d")
        r = requests.get(
            "https://www.plusetf.co.kr/api/v1/product/pdf/list",
            params={"n": krx_code, "page": 0, "d": work_dt, "pageSize": 500},
            headers=KODEX_HEADERS,
            timeout=15,
        )
        r.raise_for_status()
        items = (r.json() or {}).get("content") or []
        if items:
            break
    if not items:
        return None
    holdings = []
    for item in items:
        code = item.get("jmCd") or item.get("krJmCd")
        holdings.append({"code": code, "name": item.get("jmNm"), "weight": item.get("ratio")})
    return {"holdings": holdings, "asOfDate": parse_kofia_date(work_dt)}


_timefolio_ticker_map_cache = {"map": None, "fetched_at": 0}
_TIMEFOLIO_TICKER_MAP_TTL_SECONDS = 3600


def fetch_timefolio_ticker_map():
    """TIMEFOLIO's fund-list pages are plain server-rendered HTML (two
    categories: 001 overseas, 002 domestic) — no ajax/JSON API involved
    anywhere on this site, holdings included."""
    now = time.time()
    cache = _timefolio_ticker_map_cache
    if cache["map"] is not None and now - cache["fetched_at"] < _TIMEFOLIO_TICKER_MAP_TTL_SECONDS:
        return cache["map"]
    mapping = {}
    for cate in ("001", "002"):
        r = requests.get(
            "https://timeetf.co.kr/m11_list.php", params={"cate": cate}, headers=KODEX_HEADERS, timeout=15
        )
        r.raise_for_status()
        for m in re.finditer(
            rf'm11_view\.php\?idx=(\d+)&cate={cate}".*?codeNum"><span>([^<]+)</span>', r.text, re.S
        ):
            idx, ticker = m.group(1), m.group(2).strip()
            mapping[ticker] = (idx, cate)
    cache["map"] = mapping
    cache["fetched_at"] = now
    return mapping


def fetch_timefolio_holdings(krx_code):
    """Return holdings for a TIMEFOLIO (타임폴리오자산운용) ETF, or None if
    krx_code isn't one of theirs."""
    try:
        ticker_map = fetch_timefolio_ticker_map()
    except requests.RequestException:
        return None
    entry = ticker_map.get(krx_code)
    if not entry:
        return None
    idx, cate = entry
    r = requests.get(
        "https://timeetf.co.kr/m11_view.php", params={"idx": idx, "cate": cate}, headers=KODEX_HEADERS, timeout=15
    )
    r.raise_for_status()
    html = r.text
    section_m = re.search(r'id="constituentItems".*?</table>', html, re.S)
    if not section_m:
        return None
    date_m = re.search(r'id="pdfDate"[^>]*value="([\d-]+)"', html)
    as_of = date_m.group(1) if date_m else None
    holdings = []
    for row in re.finditer(
        r"<tr>\s*<td>(.*?)</td>\s*<td>(.*?)</td>\s*<td>.*?</td>\s*<td>.*?</td>\s*<td>(.*?)</td>\s*</tr>",
        section_m.group(0),
        re.S,
    ):
        code, name, weight_raw = (g.strip() for g in row.groups())
        try:
            weight = float(weight_raw) if weight_raw else None
        except ValueError:
            weight = None
        if code:
            holdings.append({"code": code, "name": name, "weight": weight})
    return {"holdings": holdings, "asOfDate": as_of}


_koact_ticker_map_cache = {"map": None, "fetched_at": 0}
_KOACT_TICKER_MAP_TTL_SECONDS = 3600


def fetch_koact_ticker_map():
    """KoAct is 삼성액티브자산운용 — a separate company from Samsung Asset
    Management (which runs KODEX), despite the shared "Samsung" naming —
    but its API shape is nearly identical to KODEX's, right down to the
    field names (fId/stkTicker here vs fund_id/stkTicker there)."""
    now = time.time()
    cache = _koact_ticker_map_cache
    if cache["map"] is not None and now - cache["fetched_at"] < _KOACT_TICKER_MAP_TTL_SECONDS:
        return cache["map"]
    mapping = {}
    page = 1
    while True:
        r = requests.get(
            "https://www.samsungactive.co.kr/api/v1/product/etf.do",
            params={"graphTerm": "week", "sort": "DESC", "orderType": "YIELD_WEEK", "pageNo": page},
            headers=KODEX_HEADERS,
            timeout=15,
        )
        r.raise_for_status()
        data = r.json() or {}
        items = data.get("etfs") or []
        if not items:
            break
        for it in items:
            ticker = it.get("stkTicker")
            fund_id = it.get("fId")
            if ticker and fund_id:
                mapping[ticker] = fund_id
        total = int(data.get("totalCnt") or 0)
        if len(mapping) >= total or page > 10:
            break
        page += 1
    cache["map"] = mapping
    cache["fetched_at"] = now
    return mapping


def fetch_koact_holdings(krx_code):
    """Return holdings for a KoAct (삼성액티브자산운용) ETF, or None if
    krx_code isn't one of theirs."""
    try:
        ticker_map = fetch_koact_ticker_map()
    except requests.RequestException:
        return None
    fund_id = ticker_map.get(krx_code)
    if not fund_id:
        return None
    r = requests.get(
        f"https://www.samsungactive.co.kr/api/v1/product/etf-pdf/{fund_id}.do",
        params={"gijunYMD": datetime.now().strftime("%Y%m%d")},
        headers=KODEX_HEADERS,
        timeout=15,
    )
    r.raise_for_status()
    pdf = (r.json() or {}).get("pdf") or {}
    holdings = []
    for item in pdf.get("list") or []:
        weight = item.get("ratio")
        try:
            weight = float(weight) if weight not in (None, "") else None
        except ValueError:
            weight = None
        holdings.append({"code": item.get("itmNo"), "name": item.get("secNm"), "weight": weight})
    return {"holdings": holdings, "asOfDate": parse_kofia_date(pdf.get("gijunYMD"))}


def fetch_etf_holdings(krx_code):
    for fetcher in (
        fetch_kodex_holdings,
        fetch_sol_holdings,
        fetch_tiger_holdings,
        fetch_kiwoom_holdings,
        fetch_rise_holdings,
        fetch_ace_holdings,
        fetch_plus_holdings,
        fetch_timefolio_holdings,
        fetch_koact_holdings,
    ):
        try:
            data = fetcher(krx_code)
        except requests.RequestException:
            continue
        if data is not None:
            data["holdings"] = enrich_holdings_with_market_cap(data["holdings"])
            return data
    return None


@app.route("/api/holdings/<path:symbol>")
def api_holdings(symbol):
    try:
        data = fetch_etf_holdings(symbol)
    except requests.RequestException as e:
        return jsonify({"error": f"구성종목 조회 중 오류가 발생했습니다: {e}"}), 502
    if data is None:
        return jsonify({"holdings": None, "message": "KODEX·SOL·TIGER·KIWOOM(KOSEF)·RISE(KBSTAR)·ACE·PLUS(구 ARIRANG)·TIMEFOLIO·KoAct 브랜드 ETF만 구성종목을 지원합니다."})
    return jsonify(data)


@app.route("/")
def index():
    return send_from_directory(BASE_DIR, "index.html")


@app.route("/api/search")
def api_search():
    q = request.args.get("q", "")
    if not q.strip():
        return jsonify({"error": "검색어를 입력해주세요."}), 400
    candidates = resolve_candidates(q)
    return jsonify({"results": candidates})


@app.route("/api/quote/<path:symbol>")
def api_quote(symbol):
    try:
        data = fetch_quote(symbol)
    except Exception as e:
        return jsonify({"error": f"조회 중 오류가 발생했습니다: {e}"}), 502
    return jsonify(data)


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5057))
    debug = os.environ.get("FLASK_DEBUG") == "1"
    app.run(debug=debug, host="0.0.0.0", port=port)
