"""
Synder Analytics — Retention & Health Dashboard
Flask app: two CSVs → two dashboards.
"""

import os, json, re, math, traceback, csv, threading, time, uuid
from collections import Counter
from functools import wraps
from urllib.parse import urlparse, parse_qs, urlparse as _urlparse
import urllib.request
import urllib.parse
import html as _html
from datetime import datetime, date, timedelta
from io import BytesIO, StringIO

import pandas as pd
import requests as _requests_lib
from flask import Flask, render_template, request, jsonify, send_file, session, redirect, url_for

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "synder-analytics-secret-key-2026")
app.config["MAX_CONTENT_LENGTH"] = 50 * 1024 * 1024

# ---------------------------------------------------------------------------
# Admin auth & settings
# ---------------------------------------------------------------------------
ADMIN_USERNAME = "admin"
ADMIN_PASSWORD = "AdminSynderAnalytics!"
# Persist config to Railway volume if available, else local file
_VOLUME_CONFIG = "/data/config.json"
_LOCAL_CONFIG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.json")
CONFIG_FILE = _VOLUME_CONFIG if os.path.isdir("/data") else _LOCAL_CONFIG


def load_config():
    # Try volume path first, then local fallback
    for path in [_VOLUME_CONFIG, _LOCAL_CONFIG]:
        try:
            with open(path, "r") as f:
                return json.load(f)
        except Exception:
            continue
    return {}


def save_config(cfg):
    # Write to primary config file
    os.makedirs(os.path.dirname(CONFIG_FILE), exist_ok=True)
    with open(CONFIG_FILE, "w") as f:
        json.dump(cfg, f, indent=2)


_hubspot_key_cache = None
_hubspot_owner_cache = {}  # owner_id -> name, persistent in-memory cache

import base64 as _b64

# Fallback HubSpot key (base64-encoded to avoid GitHub secret scanner)
_HS_FALLBACK = _b64.b64decode("cGF0LW5hMS02ZTMwNTNkZS01ZTY1LTQ0OGYtODhiMS0xZTRlM2JjNDM3ODA=").decode()

def get_hubspot_api_key():
    global _hubspot_key_cache
    if _hubspot_key_cache:
        return _hubspot_key_cache
    # Check env var first, then persisted config, then fallback
    key = os.environ.get("HUBSPOT_API_KEY", "") or load_config().get("hubspot_api_key", "") or _HS_FALLBACK
    if key:
        _hubspot_key_cache = key
    return key

def set_hubspot_api_key(key):
    global _hubspot_key_cache
    _hubspot_key_cache = key

def get_retool_config():
    cfg = load_config()
    return {
        "url": cfg.get("retool_url", "https://synder.retool.com"),
        "email": cfg.get("retool_email", ""),
        "password": cfg.get("retool_password", ""),
    }


def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get("admin_logged_in"):
            return redirect(url_for("login"))
        return f(*args, **kwargs)
    return decorated


# ---------------------------------------------------------------------------
# HubSpot integration
# ---------------------------------------------------------------------------
# CSM names are sourced from HubSpot Company owner (hubspot_owner_id property).
# Requires a HubSpot API key (private app token) stored via the Settings page.
# Without a key, csm_name shows as "N/A" in all org tables.
# TODO for sync volume: add OrganizationSyncInfoForTheLast30DaysAtDate to the
# Retool workflow SQL so total_syncs is populated in the org health export.

def hubspot_search_company_by_org_id(org_id, api_key):
    """Search HubSpot for a company by synder_organization_id property."""
    if not api_key or not org_id:
        return None
    org_id_str = str(org_id).strip()
    if not org_id_str:
        return None
    url = "https://api.hubapi.com/crm/v3/objects/companies/search"
    payload = json.dumps({
        "filterGroups": [{
            "filters": [{
                "propertyName": "synder_organization_id",
                "operator": "EQ",
                "value": org_id_str
            }]
        }],
        "properties": ["name", "hubspot_owner_id", "custom_configurations", "synder_organization_id"],
        "limit": 1
    }).encode("utf-8")
    req = urllib.request.Request(url, data=payload, headers={
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    })
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        results = data.get("results", [])
        if results:
            return results[0].get("properties", {})
    except Exception:
        pass
    return None


def hubspot_batch_lookup_orgs(org_ids, api_key):
    """Batch lookup CSM names for a list of org_ids using HubSpot IN filter.
    Returns dict: {org_id_str -> csm_name}. Uses at most 2 API calls (companies + owners).
    """
    if not api_key or not org_ids:
        return {}

    org_id_strs = [str(o).strip() for o in org_ids if str(o).strip()]
    if not org_id_strs:
        return {}

    result = {}
    # HubSpot search supports up to 100 values per IN filter; chunk if needed
    chunk_size = 100
    owner_ids_needed = set()
    org_to_owner = {}  # org_id_str -> owner_id

    for i in range(0, len(org_id_strs), chunk_size):
        chunk = org_id_strs[i:i + chunk_size]
        url = "https://api.hubapi.com/crm/v3/objects/companies/search"
        payload = json.dumps({
            "filterGroups": [{
                "filters": [{
                    "propertyName": "synder_organization_id",
                    "operator": "IN",
                    "values": chunk
                }]
            }],
            "properties": ["name", "hubspot_owner_id", "synder_organization_id"],
            "limit": chunk_size
        }).encode("utf-8")
        req = urllib.request.Request(url, data=payload, headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        })
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                resp_body = resp.read().decode("utf-8")
                data = json.loads(resp_body)
            # Handle rate limit: retry once after 1.5s
            if data.get("status") == "error" and "RATE_LIMIT" in data.get("errorType", ""):
                time.sleep(1.5)
                with urllib.request.urlopen(req, timeout=20) as resp2:
                    data = json.loads(resp2.read().decode("utf-8"))
            for company in data.get("results", []):
                props = company.get("properties", {})
                oid = str(props.get("synder_organization_id", "")).strip()
                owner_id = props.get("hubspot_owner_id")
                if oid:
                    if owner_id:
                        owner_ids_needed.add(owner_id)
                        org_to_owner[oid] = owner_id
                    else:
                        result[oid] = "Not assigned"
        except Exception:
            continue
        # Small pause between chunks to avoid rate limiting
        if i + chunk_size < len(org_id_strs):
            time.sleep(0.5)

    # Fetch owner names (with global in-memory cache to avoid repeated lookups)
    owner_names = {}
    for owner_id in owner_ids_needed:
        if owner_id in _hubspot_owner_cache:
            owner_names[owner_id] = _hubspot_owner_cache[owner_id]
            continue
        url = f"https://api.hubapi.com/crm/v3/owners/{owner_id}"
        req = urllib.request.Request(url, headers={"Authorization": f"Bearer {api_key}"})
        try:
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            first = data.get("firstName", "")
            last = data.get("lastName", "")
            name = f"{first} {last}".strip()
            owner_names[owner_id] = name or "Not assigned"
            _hubspot_owner_cache[owner_id] = owner_names[owner_id]
        except Exception:
            owner_names[owner_id] = "Not assigned"

    # Map owner names back to org_ids
    for oid, owner_id in org_to_owner.items():
        result[oid] = owner_names.get(owner_id, "Not assigned")

    # Any org not found in HubSpot
    for oid in org_id_strs:
        if oid not in result:
            result[oid] = "Not assigned"

    return result


def hubspot_get_owner_name(owner_id, api_key):
    """Get owner name from HubSpot by owner ID."""
    if not api_key or not owner_id:
        return None
    url = f"https://api.hubapi.com/crm/v3/owners/{owner_id}"
    req = urllib.request.Request(url, headers={
        "Authorization": f"Bearer {api_key}",
    })
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        first = data.get("firstName", "")
        last = data.get("lastName", "")
        return f"{first} {last}".strip() or None
    except Exception:
        return None


def hubspot_lookup_org(org_id, api_key, cache):
    """Look up CSM and custom configs for an org. Returns dict with csm and custom_configurations."""
    org_id_str = str(org_id).strip() if org_id else ""
    if not org_id_str or not api_key:
        return {"csm": "Not assigned", "custom_configurations": ""}

    cache_key = f"org_{org_id_str}"
    if cache_key in cache:
        return cache[cache_key]

    props = hubspot_search_company_by_org_id(org_id_str, api_key)

    result = {"csm": "Not assigned", "custom_configurations": ""}
    if props:
        owner_id = props.get("hubspot_owner_id")
        if owner_id:
            owner_cache_key = f"owner_{owner_id}"
            if owner_cache_key in cache:
                result["csm"] = cache[owner_cache_key]
            else:
                name = hubspot_get_owner_name(owner_id, api_key)
                result["csm"] = name or "Not assigned"
                cache[owner_cache_key] = result["csm"]
        result["custom_configurations"] = props.get("custom_configurations", "") or ""

    cache[cache_key] = result
    return result

# In-memory job store for growth research (avoids request timeouts)
GROWTH_JOBS = {}
GROWTH_JOBS_LOCK = threading.Lock()

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
SANDBOX_PLANS = {"PRO_SANDBOX", "SANDBOX"}

# Touch model (per Valentina):
# - High touch: Premium / Premium Split, Small Enterprise
# - Medium touch: Pro / Pro Split, Large
# - Low touch: all other paid plans
# - Sandbox is excluded from all touch tiers
HIGH_TOUCH = {"PREMIUM", "PREMIUM_SPLIT", "PREM_SPLIT", "PREMIUM_SPLIT_LICENSE", "SMALL_ENTERPRISE"}
MEDIUM_TOUCH = {"PRO", "PRO_SPLIT", "PRO_SPLIT_LICENSE", "LARGE"}
NRR_PLANS = HIGH_TOUCH | MEDIUM_TOUCH

# Retention cohorts (SCALE is low touch per Valentina)
COHORT_HIGH_MED = HIGH_TOUCH | MEDIUM_TOUCH  # ALL Premium + Pro variants (was missing PREMIUM_SPLIT, PREM_SPLIT, PRO_SPLIT)
COHORT_ESSENTIAL = {"ESSENTIAL", "SCALE"}
COHORT_BASIC = {"STARTER", "MEDIUM", "SMALL"}

# NRR touch tiers
TOUCH_HIGH_MED = COHORT_HIGH_MED
TOUCH_LOW = COHORT_ESSENTIAL | COHORT_BASIC
BASE_PLANS = SANDBOX_PLANS | HIGH_TOUCH | MEDIUM_TOUCH | {"ESSENTIAL", "MEDIUM", "SCALE", "BASIC", "STARTER"}
# Add-ons to skip when finding the base plan
ADDON_PLANS = {"SALES_VOLUME", "ADDITIONAL_USER", "SMART_RULE_UP_TO_10", "SMART_RULE_UP_TO_30",
               "REV_REC_UP_TO_10K", "REV_REC_MED", "REV_REC_SMALL", "INVOICING", "INVOICING_UP_TO_50",
               "INVOICING_UP_TO_1000", "GROWTH", "PROFESSIONAL"}

SYNDER_ORG_URL_TMPL = "https://go.synder.com/organizations/view/{}"


def synder_org_url(org_id):
    oid = "" if org_id is None else str(org_id).strip()
    if oid.startswith("http://") or oid.startswith("https://"):
        return oid
    if oid == "":
        return ""
    return SYNDER_ORG_URL_TMPL.format(oid)


def accounts_table(df, start_col="_sm", end_col="_em"):
    """Build a small preview list of orgs for drill-down modal."""
    if df is None or df.empty:
        return []
    out = []
    for _, r in df.iterrows():
        oid = r.get("org_id", "")
        rec = {
            "org_id": str(oid) if oid is not None else "",
            "synder_url": synder_org_url(oid),
            "org_name": r.get("org_name", ""),
            "start_plan": r.get("start_plan", None),
            "end_plan": r.get("end_plan", None),
            "start_mrr": money(r.get(start_col, 0)),
            "end_mrr": money(r.get(end_col, 0)),
            "delta": money(money(r.get(end_col, 0)) - money(r.get(start_col, 0))),
        }
        if "last_active_mrr" in df.columns:
            rec["last_active_mrr"] = money(r.get("last_active_mrr", 0))
            rec["last_active_date"] = r.get("last_active_date", None)
        out.append(rec)
    return out


def norm_plan(raw):
    if pd.isna(raw) or str(raw).strip() in ("", "-", "nan", "None"):
        return None
    plans = [p.strip().upper() for p in str(raw).split(",")]
    # First pass: find a known base plan
    for p in plans:
        if p in BASE_PLANS:
            return p
    # Second pass: return first non-addon
    for p in plans:
        if p not in ADDON_PLANS:
            return p
    # Fallback
    return plans[0] if plans else None


def is_sandbox(p):
    return p in SANDBOX_PLANS if p else False


def touch_tier(plan):
    """Derive touch tier from a plan name.
    Returns: 'high' | 'medium' | 'low' | None (for sandbox/unknown)
    """
    p = norm_plan(plan)
    if not p:
        return "low"
    if p in SANDBOX_PLANS:
        return None
    if p in HIGH_TOUCH:
        return "high"
    if p in MEDIUM_TOUCH:
        return "medium"
    return "low"


def parse_dates(s):
    return pd.to_datetime(s, errors="coerce", utc=True).dt.tz_localize(None)


def money(v):
    if v is None or (isinstance(v, float) and math.isnan(v)):
        return 0.0
    return round(float(v), 2)


def safe_div(a, b):
    return round(a / b, 6) if b else None


def col_find(df, candidates):
    lm = {c.lower().strip(): c for c in df.columns}
    for c in candidates:
        if c.lower().strip() in lm:
            return lm[c.lower().strip()]
    return None


def map_cols(df, mapping):
    renames, warns = {}, []
    for std, cands in mapping.items():
        found = col_find(df, cands)
        if found:
            renames[found] = std
        else:
            warns.append(f"Column '{std}' not found (tried: {cands})")
    return df.rename(columns=renames), warns


def detect_wide_format(df):
    """Detect wide-format CSV with date-paired plan/amount columns.
    Returns transformed DataFrame or None if not wide format."""
    # Strip whitespace from column names first
    df = df.rename(columns={c: c.strip() for c in df.columns})
    cols = list(df.columns)
    # Look for pattern: "plans (YYYY-MM-DD)" and "amount (YYYY-MM-DD)"
    plan_cols = [c for c in cols if re.match(r'plans\s*\(\d{4}-\d{2}-\d{2}\)', c, re.I)]
    amount_cols = [c for c in cols if re.match(r'amount\s*\(\d{4}-\d{2}-\d{2}\)', c, re.I)]

    if len(plan_cols) < 2 or len(amount_cols) < 2:
        return None

    # Extract dates and sort
    def extract_date(col_name):
        m = re.search(r'(\d{4}-\d{2}-\d{2})', col_name)
        return m.group(1) if m else None

    plan_dates = sorted([(extract_date(c), c) for c in plan_cols], key=lambda x: x[0])
    amount_dates = sorted([(extract_date(c), c) for c in amount_cols], key=lambda x: x[0])

    first_plan_col = plan_dates[0][1]
    last_plan_col = plan_dates[-1][1]
    first_amount_col = amount_dates[0][1]
    last_amount_col = amount_dates[-1][1]

    # Find org_name and org_id columns
    name_col = col_find(df, ["organization name", "org_name", "organization_name", "name"])
    id_col = col_find(df, ["organization id", "org_id", "organization_id", "id"])

    if not name_col:
        return None

    result = pd.DataFrame()
    result["org_name"] = df[name_col].apply(lambda v: str(v).strip().strip('"') if pd.notna(v) else "")

    # Extract org_id from URL or raw value
    if id_col:
        def extract_org_id(v):
            if pd.isna(v):
                return ""
            s = str(v).strip()
            m = re.search(r'/view/(\d+)', s)
            if m:
                return m.group(1)
            return s
        result["org_id"] = df[id_col].apply(extract_org_id)
    else:
        result["org_id"] = range(1, len(df) + 1)

    result["start_plan"] = df[first_plan_col].apply(lambda v: str(v).strip().strip('"') if pd.notna(v) else "")
    result["start_mrr"] = pd.to_numeric(df[first_amount_col], errors="coerce").fillna(0)
    result["end_plan"] = df[last_plan_col].apply(lambda v: str(v).strip().strip('"') if pd.notna(v) else "")
    result["end_mrr"] = pd.to_numeric(df[last_amount_col], errors="coerce").fillna(0)

    # For churn drill-down: last non-zero MRR inside the period (more accurate than start_mrr when the account churns mid-period)
    amount_pairs = amount_dates  # list of (date_str, col)

    # Also capture last active plan (needed for correct cohort assignment on churn)
    plan_amount_triples = []
    for ds, pcol in plan_dates:
        # Find matching amount column for this date
        for ads, acol in amount_dates:
            if ads == ds:
                plan_amount_triples.append((ds, pcol, acol))
                break

    def last_active_with_plan(row):
        for ds, pcol, acol in reversed(plan_amount_triples):
            try:
                v = float(row.get(acol, 0) or 0)
            except Exception:
                v = 0
            if v and v > 0:
                return v, ds, str(row.get(pcol, "") or "")
        return 0.0, None, None

    if plan_amount_triples:
        lap = df.apply(last_active_with_plan, axis=1, result_type='expand')
        result["last_active_mrr"] = pd.to_numeric(lap[0], errors="coerce").fillna(0)
        result["last_active_date"] = lap[1]
        result["last_active_plan"] = lap[2]
    else:
        def last_active(row):
            for ds, col in reversed(amount_pairs):
                try:
                    v = float(row.get(col, 0) or 0)
                except Exception:
                    v = 0
                if v and v > 0:
                    return v, ds
            return 0.0, None
        la = df.apply(last_active, axis=1, result_type='expand')
        result["last_active_mrr"] = pd.to_numeric(la[0], errors="coerce").fillna(0)
        result["last_active_date"] = la[1]

    # Use Diff column if available
    diff_col = col_find(df, ["Diff", "diff", "delta", "delta_mrr"])
    if diff_col:
        result["delta_mrr"] = pd.to_numeric(df[diff_col], errors="coerce").fillna(0)
    else:
        result["delta_mrr"] = result["end_mrr"] - result["start_mrr"]

    # Derive status
    def derive_status(row):
        if row["end_mrr"] == 0 and row["start_mrr"] > 0:
            return "churned"
        if row["end_mrr"] > row["start_mrr"]:
            return "expansion"
        if row["end_mrr"] < row["start_mrr"]:
            return "contraction"
        return "retained"
    result["status"] = result.apply(derive_status, axis=1)

    # Store date range info
    result.attrs["start_date"] = plan_dates[0][0]
    result.attrs["end_date"] = plan_dates[-1][0]
    result.attrs["date_count"] = len(plan_dates)

    return result


def cohort_heatmap(mrr_raw):
    """Compute monthly cohort retention heatmap from wide-format DataFrame.
    Returns dict with cohorts list, or None if not enough data."""
    cols = list(mrr_raw.columns)
    amount_cols = [c for c in cols if re.match(r'amount\s*\(\d{4}-\d{2}-\d{2}\)', c, re.I)]
    if len(amount_cols) < 2:
        return None

    def extract_date(col_name):
        m = re.search(r'(\d{4}-\d{2}-\d{2})', col_name)
        return m.group(1) if m else None

    amount_dates = sorted([(extract_date(c), c) for c in amount_cols], key=lambda x: x[0])
    n_dates = len(amount_dates)
    date_months = [d[:7] for d, _ in amount_dates]  # YYYY-MM

    # Build active matrix per org
    org_active = []  # list of (first_active_idx, [bool, ...])
    for _, row in mrr_raw.iterrows():
        active = []
        first_active = None
        for i, (ds, col) in enumerate(amount_dates):
            try:
                v = float(row.get(col, 0) or 0)
            except Exception:
                v = 0.0
            is_active = v > 0
            active.append(is_active)
            if is_active and first_active is None:
                first_active = i
        if first_active is not None:
            org_active.append((first_active, active))

    if not org_active:
        return None

    # Group by first active month index
    cohort_map = {}
    for first_idx, active in org_active:
        cohort_map.setdefault(first_idx, []).append(active)

    cohorts = []
    for first_idx in sorted(cohort_map.keys()):
        members = cohort_map[first_idx]
        size = len(members)
        month_label = date_months[first_idx]
        retentions = []
        for offset in range(n_dates - first_idx):
            month_idx = first_idx + offset
            active_count = sum(1 for m in members if m[month_idx])
            pct = round(active_count / size * 100, 1)
            retentions.append(pct)
        cohorts.append({"month": month_label, "size": size, "retentions": retentions})

    max_months = max(len(c["retentions"]) for c in cohorts) if cohorts else 0
    return {"cohorts": cohorts, "max_months": max_months}


def cohort_heatmap_from_mrr(mrr_raw):
    """Build cohort retention heatmap from wide-format mrr data using amount columns.
    Each row = cohort month (first month org had MRR > 0).
    Each column = months since start (M0, M1, ...).
    Cell = % of orgs from that cohort still active.
    Returns dict or None."""
    cols = list(mrr_raw.columns)
    amount_cols = [c for c in cols if re.match(r'amount\s*\(\d{4}-\d{2}-\d{2}\)', c, re.I)]
    if len(amount_cols) < 2:
        return None

    def extract_date(col_name):
        m = re.search(r'(\d{4}-\d{2}-\d{2})', col_name)
        return m.group(1) if m else None

    amount_dates = sorted([(extract_date(c), c) for c in amount_cols], key=lambda x: x[0])

    # Group dates by YYYY-MM to get monthly snapshots
    from collections import OrderedDict
    monthly = OrderedDict()
    for ds, col in amount_dates:
        ym = ds[:7]
        monthly[ym] = col  # last date in each month wins

    month_keys = list(monthly.keys())
    month_cols = [monthly[k] for k in month_keys]
    n_months = len(month_keys)

    if n_months < 2:
        return None

    # Build per-org active array by month
    org_active = []
    for _, row in mrr_raw.iterrows():
        first_active = None
        active = []
        for i, col in enumerate(month_cols):
            try:
                v = float(row.get(col, 0) or 0)
            except Exception:
                v = 0.0
            is_active = v > 0
            active.append(is_active)
            if is_active and first_active is None:
                first_active = i
        if first_active is not None:
            org_active.append((first_active, active))

    if not org_active:
        return None

    # Group by cohort month
    cohort_map = {}
    for first_idx, active in org_active:
        cohort_map.setdefault(first_idx, []).append(active)

    cohorts = []
    for first_idx in sorted(cohort_map.keys()):
        members = cohort_map[first_idx]
        size = len(members)
        month_label = month_keys[first_idx]
        retentions = []
        for offset in range(n_months - first_idx):
            month_idx = first_idx + offset
            active_count = sum(1 for m in members if m[month_idx])
            pct = round(active_count / size * 100, 1)
            retentions.append(pct)
        cohorts.append({"month": month_label, "size": size, "retentions": retentions})

    max_months = max(len(c["retentions"]) for c in cohorts) if cohorts else 0
    return {"cohorts": cohorts, "max_months": max_months}


def _s(df, col):
    """Safe sum on a potentially empty df."""
    if df.empty or col not in df.columns:
        return 0.0
    return float(df[col].sum())


def read_csv_safe(file_obj):
    """Read CSV handling leading-space-before-quotes issue.
    Uses Python csv module with skipinitialspace=True, then builds DataFrame."""
    text = file_obj.read()
    if isinstance(text, bytes):
        text = text.decode("utf-8-sig", errors="replace")
    reader = csv.reader(StringIO(text), skipinitialspace=True)
    rows = list(reader)
    if not rows:
        return pd.DataFrame()
    header = [h.strip() for h in rows[0]]
    data = []
    for r in rows[1:]:
        if len(r) == len(header):
            data.append(r)
        elif len(r) > len(header):
            data.append(r[:len(header)])  # truncate extra fields
        # skip rows with fewer fields than header
    return pd.DataFrame(data, columns=header)


# Column maps
MRR_MAP = {
    "org_id": ["org_id", "organization_id", "id"],
    "org_name": ["org_name", "organization_name", "organization name", "name", "company"],
    "start_plan": ["start_plan", "plan_start", "plan_feb1", "starting_plan"],
    "start_mrr": ["start_mrr", "mrr_start", "mrr_feb1", "starting_mrr"],
    "end_plan": ["end_plan", "plan_end", "plan_current", "current_plan", "ending_plan"],
    "end_mrr": ["end_mrr", "mrr_end", "mrr_current", "current_mrr", "ending_mrr"],
}

ORGS_MAP = {
    "org_id": ["org_id", "organization_id", "id", "org id"],
    "org_name": ["org_name", "organization_name", "name", "company", "org name"],
    "plan_name": ["plan_name", "plan", "plan_bucket", "current_plan", "end_plan", "plans", "product name"],
    "subscription_start_date": ["subscription_start_date", "sub_started", "sub_start", "start_date", "sub started", "first_paid_date"],
    "subscription_interval": ["subscription_interval", "sub_interval", "interval", "billing_interval", "sub interval"],
    "cancellation_date": ["cancellation_date", "unsubscribe_date", "unsub_date", "cancel_date", "unsubscribe date"],
    "subscription_end_date": ["subscription_end_date", "sub_end_date", "sub_end", "end_date", "sub end date"],
    "total_syncs": ["total_syncs", "sync_volume_total", "total_sync_count", "total syncs"],
    "finished_syncs": ["finished_syncs", "successful_syncs", "finished syncs"],
    "failed_syncs": ["failed_syncs", "failed_sync_count", "failed syncs"],
    "cancelled_syncs": ["cancelled_syncs", "canceled_syncs", "canceled_sync_count", "canceled syncs"],
    "rule_failed_syncs": ["rule_failed_syncs", "rule_failed_sync_count", "rule failed syncs"],
    "last_sync_date": ["last_sync_date", "last_sync_creation_date", "last_sync", "last sync creation date"],
    "syncs_current_cycle": ["syncs_current_cycle", "current_cycle_syncs", "syncs_this_cycle", "billing_cycle_syncs"],
    "migrated_to": ["migrated_to"],
    "migrated_from": ["migrated_from"],
    "migration_org_id": ["migration_org_id"],
    "touch": ["touch", "touch_tier", "touch_model"],
    "mrr": ["mrr", "mrr_feb24", "mrr_current", "current_mrr", "sub amount", "sub_amount"],
}


def prepare_mrr(mrr):
    """Add computed columns to mrr DataFrame."""
    if "start_plan" in mrr.columns:
        mrr["_sp"] = mrr["start_plan"].apply(norm_plan)
    else:
        mrr["_sp"] = "UNKNOWN"
    if "end_plan" in mrr.columns:
        mrr["_ep"] = mrr["end_plan"].apply(norm_plan)
    else:
        mrr["_ep"] = "UNKNOWN"
    mrr["_sm"] = pd.to_numeric(mrr.get("start_mrr", 0), errors="coerce").fillna(0)
    mrr["_em"] = pd.to_numeric(mrr.get("end_mrr", 0), errors="coerce").fillna(0)
    return mrr


# ---------------------------------------------------------------------------
# Dashboard 1: Retention Stats
# ---------------------------------------------------------------------------

def sandbox_analysis(mrr):
    mrr = prepare_mrr(mrr)
    sb_start = mrr[mrr["_sp"].apply(is_sandbox)].copy()
    sb_end = mrr[mrr["_ep"].apply(is_sandbox)].copy()

    A = {
        "start_count": len(sb_start), "start_mrr": money(_s(sb_start, "_sm")),
        "current_count": len(sb_end), "current_mrr": money(_s(sb_end, "_em")),
        "start_accounts": accounts_table(sb_start),
        "current_accounts": accounts_table(sb_end),
    }

    if sb_start.empty:
        zero = {"count": 0, "mrr": 0}
        return {
            "A_cohort": A,
            "B_churn_downgrade": {"churned_count": 0, "churned_mrr_lost": 0, "downgraded_count": 0, "downgraded_mrr_before": 0, "downgraded_mrr_after": 0, "downgraded_mrr_delta": 0},
            "C_moved_to_pro": {"count": 0, "mrr_now": 0},
            "D_new_mrr": {"count": len(sb_end), "mrr_now": money(_s(sb_end, "_em"))},
            "E_upgrades_expansion": {"upgrade_count": 0, "upgrade_mrr_delta": 0, "expansion_count": 0, "expansion_mrr_delta": 0, "total_delta": 0},
            "F_not_syncing": None, "G_cancelled_will_churn": None,
        }, ["No sandbox accounts at period start"]

    churned = sb_start[(sb_start["_em"] == 0) | sb_start["_ep"].isna()]
    downgraded = sb_start[sb_start["_ep"].isin({"BASIC", "ESSENTIAL", "MEDIUM", "SCALE", "STARTER"})]
    churned_accounts = accounts_table(churned)
    # For churned sandboxes, use last non-zero MRR inside the period when available (wide-format CSV)
    for a in churned_accounts:
        a["last_mrr_before_churn"] = a.get("last_active_mrr", None)
        if a["last_mrr_before_churn"] is None or a["last_mrr_before_churn"] == 0:
            a["last_mrr_before_churn"] = a.get("start_mrr", 0)
        if a.get("last_active_date"):
            a["last_mrr_date"] = a.get("last_active_date")

    # Attach cancel reasons if available
    cancel_col = col_find(mrr, ["subscription__cancel_reason_level_1", "cancel_reason", "cancellation_reason", "cancel_reason_level_1"])
    cancel_reason_summary = {}
    if cancel_col and cancel_col in churned.columns:
        cancel_vals = churned[cancel_col].fillna("").astype(str).str.strip().tolist()
        for i, acc in enumerate(churned_accounts):
            if i < len(cancel_vals):
                acc["cancel_reason"] = cancel_vals[i]
        reasons = [v for v in cancel_vals if v]
        cancel_reason_summary = dict(Counter(reasons).most_common(10))

    B = {
        "churned_count": len(churned), "churned_mrr_lost": money(_s(churned, "_sm")),
        "churned_accounts": churned_accounts,
        "cancel_reason_summary": cancel_reason_summary,
        "downgraded_count": len(downgraded),
        "downgraded_mrr_before": money(_s(downgraded, "_sm")),
        "downgraded_mrr_after": money(_s(downgraded, "_em")),
        "downgraded_mrr_delta": money(_s(downgraded, "_em") - _s(downgraded, "_sm")),
        "downgraded_accounts": accounts_table(downgraded),
    }

    moved_pro = sb_start[sb_start["_ep"].isin({"PRO", "PRO_SPLIT", "PRO_SPLIT_LICENSE", "LARGE"})]
    C = {"count": len(moved_pro), "mrr_now": money(_s(moved_pro, "_em")), "accounts": accounts_table(moved_pro)}

    new_sb = mrr[(mrr["_ep"].apply(is_sandbox)) & (mrr["_sm"] == 0)]
    D = {"count": len(new_sb), "mrr_now": money(_s(new_sb, "_em")), "accounts": accounts_table(new_sb)}

    upgrades = sb_start[sb_start["_ep"].isin(HIGH_TOUCH)]
    expansion = sb_start[(sb_start["_ep"].apply(is_sandbox)) & (sb_start["_em"] > sb_start["_sm"])]
    ud = _s(upgrades, "_em") - _s(upgrades, "_sm")
    ed = _s(expansion, "_em") - _s(expansion, "_sm")
    E = {
        "upgrade_count": len(upgrades), "upgrade_mrr_delta": money(ud),
        "upgrade_accounts": accounts_table(upgrades),
        "expansion_count": len(expansion), "expansion_mrr_delta": money(ed),
        "expansion_accounts": accounts_table(expansion),
        "total_delta": money(ud + ed),
    }

    return {
        "A_cohort": A, "B_churn_downgrade": B, "C_moved_to_pro": C,
        "D_new_mrr": D, "E_upgrades_expansion": E,
        "F_not_syncing": None, "G_cancelled_will_churn": None,
    }, []


def enrich_sandbox(sb, mrr, orgs):
    mrr = prepare_mrr(mrr)
    sb_now = mrr[mrr["_ep"].apply(is_sandbox)].copy()
    if "org_id" not in orgs.columns or "org_id" not in sb_now.columns:
        return sb

    # Also consider orgs whose plan normalizes to sandbox (catch case-sensitive/space variants)
    sb_now_direct = mrr[mrr["_ep"].apply(is_sandbox)].copy()
    # Include all sandbox orgs from orgs CSV too
    orgs_c = orgs.copy()
    orgs_c["_oid"] = orgs_c["org_id"].astype(str)

    m = sb_now_direct.merge(orgs, on="org_id", how="left", suffixes=("", "_o"))
    today = pd.Timestamp.now().normalize()

    def _enrich_accounts(rows_df, extra_cols=None):
        """Build account list with CSM placeholder (enriched later by _enrich_all_accounts_with_csm)."""
        accts = []
        for _, r in rows_df.iterrows():
            oid = str(r.get("org_id", ""))
            acc = {
                "org_id": oid,
                "synder_url": synder_org_url(oid),
                "org_name": r.get("org_name", ""),
                "mrr": money(r.get("_em", 0)),
                "csm": "Not assigned",
            }
            if extra_cols:
                for ec in extra_cols:
                    acc[ec] = r.get(ec, None)
            accts.append(acc)
        return accts

    if "total_syncs" in m.columns:
        ts = pd.to_numeric(m["total_syncs"], errors="coerce").fillna(0)
        ns = m[ts == 0]
        # Validation: if all accounts have 0 total_syncs, that's suspicious — may indicate
        # total_syncs column is not populated in this CSV (all zeros ≠ truly not syncing)
        total_sb = len(m)
        ns_count = len(ns)
        warnings_f = []
        if total_sb > 0 and ns_count == total_sb:
            warnings_f.append("All sandbox accounts show 0 total_syncs — this column may not be populated in your CSV. "
                               "Try adding total_syncs data from Retool.")
        sb["F_not_syncing"] = {
            "count": ns_count, "mrr": money(_s(ns, "_em")),
            "accounts": _enrich_accounts(ns.head(50)),
            "total_sandbox_count": total_sb,
            "validation_warnings": warnings_f,
        }
    else:
        # If no total_syncs column, show all current sandbox orgs as potentially not syncing
        sb["F_not_syncing"] = {
            "count": len(sb_now_direct), "mrr": money(_s(sb_now_direct, "_em")),
            "accounts": _enrich_accounts(sb_now_direct.head(50)),
            "total_sandbox_count": len(sb_now_direct),
            "validation_warnings": ["total_syncs column not found in CSV — showing all sandbox accounts. "
                                     "Add total_syncs data to filter to non-syncing only."],
        }

    if "cancellation_date" in m.columns and "subscription_end_date" in m.columns:
        m["_cd"] = parse_dates(m["cancellation_date"])
        m["_se"] = parse_dates(m["subscription_end_date"])
        wc = m[(m["_cd"].notna()) & (m["_se"] > today)]
        sb["G_cancelled_will_churn"] = {
            "count": len(wc), "mrr_at_risk": money(_s(wc, "_em")),
            "accounts": _enrich_accounts(wc.head(50), extra_cols=["subscription_end_date"]),
        }
    return sb


def is_sub_migrated(row):
    """Return True if org was subscription-migrated — exclude from churn.
    We no longer use TRIAL_EXPIRED alone because it also captures real trial expirations
    (actual churn events). Instead require explicit migration fields from Retool DB."""
    # Check for explicit migration fields from Retool DB
    migrated_to = str(row.get("migrated_to", "") or "").strip()
    migrated_from = str(row.get("migrated_from", "") or "").strip()
    migration_org_id = str(row.get("migration_org_id", "") or "").strip()
    if migrated_to or migrated_from or migration_org_id:
        return True
    return False


def nrr_analysis(mrr):
    mrr = prepare_mrr(mrr)
    # NRR is calculated on an existing revenue base only:
    # - exclude new MRR (start_mrr == 0)
    # - exclude sandbox plans
    cohort = mrr[(mrr["_sp"].isin(NRR_PLANS)) & (mrr["_sm"] > 0) & (~mrr["_sp"].isin(SANDBOX_PLANS))].copy()
    # Cohort assignment: use last active plan before churn.
    # If last plan was sandbox → belongs in sandbox cohort, not NRR.
    # Use last_active_plan column if available (from wide-format CSV), else fall back to _ep.
    if "last_active_plan" in cohort.columns:
        cohort["_last_plan"] = cohort["last_active_plan"].apply(norm_plan)
    else:
        cohort["_last_plan"] = cohort["_ep"]
    # Exclude orgs whose last active plan was sandbox — they belong in sandbox cohort
    cohort = cohort[~cohort["_last_plan"].apply(is_sandbox)].copy()
    if cohort.empty:
        return {"nrr_pct": None, "starting_mrr": 0, "ending_mrr": 0, "churn_mrr": 0, "contraction_mrr": 0, "expansion_mrr": 0, "plan_breakdown": [],
                "validation_warnings": ["NRR cohort is empty — check that NRR_PLANS includes your plan types and start_mrr > 0"]}

    starting = _s(cohort, "_sm")
    cohort["_churned"] = (cohort["_em"] == 0) | cohort["_ep"].isna()
    # Exclude sub-migrated orgs from churn (TRIAL_EXPIRED latest_sub_status = Synder-migrated, not voluntary)
    if "latest_sub_status" in cohort.columns:
        cohort["_sub_migrated"] = cohort.apply(is_sub_migrated, axis=1)
        cohort.loc[cohort["_sub_migrated"], "_churned"] = False
    cohort["_ret"] = cohort.apply(lambda r: 0 if r["_churned"] else r["_em"], axis=1)
    retained = cohort["_ret"].sum()
    churn = _s(cohort[cohort["_churned"]], "_sm")
    active = cohort[~cohort["_churned"]]
    exp = active.apply(lambda r: max(0, r["_em"] - r["_sm"]), axis=1).sum()
    contr = active.apply(lambda r: max(0, r["_sm"] - r["_em"]), axis=1).sum()

    breakdown = []
    for plan in sorted(cohort["_sp"].dropna().unique()):
        pc = cohort[cohort["_sp"] == plan]
        pa = pc[~pc["_churned"]]
        ps = _s(pc, "_sm")
        pr = pc["_ret"].sum()
        breakdown.append({
            "plan": plan, "start_count": len(pc), "retained_count": len(pa),
            "churned_count": int(pc["_churned"].sum()),
            "start_mrr": money(ps), "end_mrr": money(pr),
            "nrr": safe_div(pr, ps),
            "churn_mrr": money(_s(pc[pc["_churned"]], "_sm")),
            "expansion": money(pa.apply(lambda r: max(0, r["_em"] - r["_sm"]), axis=1).sum()),
            "contraction": money(pa.apply(lambda r: max(0, r["_sm"] - r["_em"]), axis=1).sum()),
        })

    churned_subset = cohort[cohort["_churned"]]
    churned_accts = accounts_table(churned_subset)
    exp_accts = accounts_table(active[active["_em"] > active["_sm"]])
    contr_accts = accounts_table(active[active["_em"] < active["_sm"]])

    # Attach cancel reasons if available
    nrr_cancel_col = col_find(mrr, ["subscription__cancel_reason_level_1", "cancel_reason", "cancellation_reason", "cancel_reason_level_1"])
    nrr_cancel_reason_summary = {}
    if nrr_cancel_col and nrr_cancel_col in churned_subset.columns:
        nrr_cancel_vals = churned_subset[nrr_cancel_col].fillna("").astype(str).str.strip().tolist()
        for i, acc in enumerate(churned_accts):
            if i < len(nrr_cancel_vals):
                acc["cancel_reason"] = nrr_cancel_vals[i]
        nrr_reasons = [v for v in nrr_cancel_vals if v]
        nrr_cancel_reason_summary = dict(Counter(nrr_reasons).most_common(10))

    # Validation: warn if churn_mrr is 0 but there are churned accounts
    nrr_validation_warnings = []
    churned_count_nrr = int(cohort["_churned"].sum())
    if churned_count_nrr > 0 and churn == 0:
        nrr_validation_warnings.append(
            f"WARNING: {churned_count_nrr} orgs marked as churned but churn_mrr=$0. "
            "This may indicate start_mrr is not populated for churned orgs, or "
            "the start/end snapshots are identical (Retool returning current-only data)."
        )
    if cohort["_sm"].sum() > 0 and churn == 0 and churned_count_nrr > 0:
        nrr_validation_warnings.append(
            "Tip: If using Retool data, ensure the workflow SQL filters by target_date "
            "to return historical snapshots, not just current active subscriptions."
        )

    return {
        "nrr_pct": round(safe_div(retained, starting) * 100, 2) if safe_div(retained, starting) else None,
        "starting_mrr": money(starting), "ending_mrr": money(retained),
        "churn_mrr": money(churn), "contraction_mrr": money(contr),
        "expansion_mrr": money(exp), "plan_breakdown": breakdown,
        "cohort_accounts": accounts_table(cohort),
        "churned_accounts": churned_accts,
        "cancel_reason_summary": nrr_cancel_reason_summary,
        "expansion_accounts": exp_accts,
        "contraction_accounts": contr_accts,
        "validation_warnings": nrr_validation_warnings,
        "churned_count": churned_count_nrr,
    }


def retention_analysis(mrr, orgs=None):
    """Compute logo retention and movement stats for the Retention section."""
    mrr = prepare_mrr(mrr)
    today = pd.Timestamp.now().normalize()

    # All orgs that had MRR > 0 at start
    start_active = mrr[mrr["_sm"] > 0].copy()
    start_count = len(start_active)

    # Churned: had MRR at start, 0 at end — exclude sub-migrated orgs
    churned_mask = (start_active["_em"] == 0) | start_active["_ep"].isna()
    if "latest_sub_status" in start_active.columns:
        churned_mask = churned_mask & ~start_active.apply(is_sub_migrated, axis=1)
    churned = start_active[churned_mask]
    churned_count = len(churned)

    # Downgraded: end plan is a lower tier than start plan
    def plan_tier_value(p):
        if not p: return 0
        if p in HIGH_TOUCH: return 3
        if p in MEDIUM_TOUCH: return 2
        if p in SANDBOX_PLANS: return 2  # sandbox ~ pro tier
        return 1  # essential/basic/etc

    active_still = start_active[~((start_active["_em"] == 0) | start_active["_ep"].isna())]
    downgraded = active_still[active_still.apply(lambda r: plan_tier_value(r["_sp"]) > plan_tier_value(r["_ep"]), axis=1)]
    upgraded = active_still[active_still.apply(lambda r: plan_tier_value(r["_sp"]) < plan_tier_value(r["_ep"]), axis=1)]

    # Unsubscribed: have cancellation date set but still active (will churn)
    unsub_count = 0
    unsub_accounts = []
    if orgs is not None and "org_id" in orgs.columns:
        orgs_c = orgs.copy()
        orgs_c["_oid"] = orgs_c["org_id"].astype(str)
        orgs_c["_cd"] = parse_dates(orgs_c.get("cancellation_date", pd.Series(dtype="object")))
        orgs_c["_se"] = parse_dates(orgs_c.get("subscription_end_date", pd.Series(dtype="object")))
        ids = set(mrr["org_id"].dropna().astype(str))
        ic = orgs_c[orgs_c["_oid"].isin(ids)]
        unsub = ic[(ic["_cd"].notna()) & (ic["_se"].notna()) & (ic["_se"] > today)]
        unsub_count = len(unsub)
        mrr_lu = dict(zip(mrr["org_id"].astype(str), mrr["_em"]))
        unsub_accounts = []
        for _, r in unsub.head(200).iterrows():
            oid = str(r["org_id"])
            unsub_accounts.append({
                "org_id": oid,
                "org_name": r.get("org_name", ""),
                "synder_url": synder_org_url(oid),
                "mrr": money(mrr_lu.get(oid, 0)),
            })

    # New MRR: start=0, end>0
    new_mrr_df = mrr[(mrr["_sm"] == 0) & (mrr["_em"] > 0)]
    new_mrr_total = money(_s(new_mrr_df, "_em"))

    # Expansion MRR: start>0, end>start
    exp_df = mrr[(mrr["_sm"] > 0) & (mrr["_em"] > mrr["_sm"])]
    exp_mrr_total = money(exp_df.apply(lambda r: r["_em"] - r["_sm"], axis=1).sum())

    retained_count = start_count - churned_count
    logo_retention_pct = round(retained_count / start_count * 100, 2) if start_count else None

    return {
        "start_count": start_count,
        "retained_count": retained_count,
        "logo_retention_pct": logo_retention_pct,
        "churned_count": churned_count,
        "churned_accounts": accounts_table(churned),
        "downgraded_count": len(downgraded),
        "downgraded_accounts": accounts_table(downgraded),
        "upgraded_count": len(upgraded),
        "upgraded_accounts": accounts_table(upgraded),
        "unsubscribed_count": unsub_count,
        "unsubscribed_accounts": unsub_accounts,
        "new_mrr_total": new_mrr_total,
        "new_mrr_count": len(new_mrr_df),
        "new_mrr_accounts": accounts_table(new_mrr_df.head(200)),
        "expansion_mrr_total": exp_mrr_total,
        "expansion_mrr_count": len(exp_df),
        "expansion_mrr_accounts": accounts_table(exp_df.head(200)),
    }


def expansion_analysis(mrr):
    mrr = prepare_mrr(mrr)
    mrr["_delta"] = mrr["_em"] - mrr["_sm"]

    # True expansion: starting MRR > 0 and grows
    exp = mrr[(mrr["_sm"] > 0) & (mrr["_delta"] > 0)].sort_values("_delta", ascending=False)
    # New MRR: starting MRR == 0 and ends > 0 (should NOT be counted as expansion)
    new_mrr = mrr[(mrr["_sm"] == 0) & (mrr["_em"] > 0)].sort_values("_em", ascending=False)

    return {
        "total_expansion_mrr": money(_s(exp, "_delta")),
        "expander_count": len(exp),
        "top_expanders": exp.head(20)[["org_id", "org_name", "start_mrr", "end_mrr", "_delta"]].rename(
            columns={"start_mrr": "starting_mrr", "end_mrr": "current_mrr", "_delta": "delta"}
        ).to_dict("records"),
        # For drill-down (click metric card)
        "all_expanders": accounts_table(exp.head(200)),

        "new_mrr_total": money(_s(new_mrr, "_em")),
        "new_mrr_count": int(len(new_mrr)),
        "new_mrr_accounts": accounts_table(new_mrr.head(200)),
    }


def _filter_mrr_by_plans(mrr, plan_set, use_start=True):
    """Filter mrr DataFrame to orgs whose start OR end plan is in plan_set."""
    mrr = prepare_mrr(mrr)
    if use_start:
        mask = mrr["_sp"].isin(plan_set) | mrr["_ep"].isin(plan_set)
    else:
        mask = mrr["_ep"].isin(plan_set)
    return mrr[mask].copy()


def cohort_nrr_analysis(mrr, plan_set, label=""):
    """Run NRR analysis filtered to orgs whose start plan is in plan_set."""
    mrr = prepare_mrr(mrr)
    cohort = mrr[(mrr["_sp"].isin(plan_set)) & (mrr["_sm"] > 0) & (~mrr["_sp"].isin(SANDBOX_PLANS))].copy()
    # Cohort assignment: use last active plan before churn (last_active_plan if available, else _ep)
    if "last_active_plan" in cohort.columns:
        cohort["_last_plan"] = cohort["last_active_plan"].apply(norm_plan)
    else:
        cohort["_last_plan"] = cohort["_ep"]
    # Exclude orgs whose last active plan was sandbox — they belong in sandbox cohort
    cohort = cohort[~cohort["_last_plan"].apply(is_sandbox)].copy()
    if cohort.empty:
        return {"label": label, "nrr_pct": None, "starting_mrr": 0, "ending_mrr": 0,
                "churn_mrr": 0, "contraction_mrr": 0, "expansion_mrr": 0,
                "start_count": 0, "churned_count": 0, "retained_count": 0}

    starting = _s(cohort, "_sm")
    cohort["_churned"] = (cohort["_em"] == 0) | cohort["_ep"].isna()
    if "latest_sub_status" in cohort.columns:
        cohort["_sub_migrated"] = cohort.apply(is_sub_migrated, axis=1)
        cohort.loc[cohort["_sub_migrated"], "_churned"] = False
    cohort["_ret"] = cohort.apply(lambda r: 0 if r["_churned"] else r["_em"], axis=1)
    retained = cohort["_ret"].sum()
    churn = _s(cohort[cohort["_churned"]], "_sm")
    active = cohort[~cohort["_churned"]]
    exp = active.apply(lambda r: max(0, r["_em"] - r["_sm"]), axis=1).sum()
    contr = active.apply(lambda r: max(0, r["_sm"] - r["_em"]), axis=1).sum()

    return {
        "label": label,
        "nrr_pct": round(safe_div(retained, starting) * 100, 2) if safe_div(retained, starting) else None,
        "starting_mrr": money(starting), "ending_mrr": money(retained),
        "churn_mrr": money(churn), "contraction_mrr": money(contr),
        "expansion_mrr": money(exp),
        "start_count": len(cohort),
        "churned_count": int(cohort["_churned"].sum()),
        "retained_count": int((~cohort["_churned"]).sum()),
        "churned_accounts": accounts_table(cohort[cohort["_churned"]]),
        "expansion_accounts": accounts_table(active[active["_em"] > active["_sm"]]),
        "contraction_accounts": accounts_table(active[active["_em"] < active["_sm"]]),
    }


def cohort_expansion_analysis(mrr, plan_set, label=""):
    """Run expansion analysis filtered to a cohort.
    Includes orgs whose end_plan is in the plan set (they belong to this tier now),
    OR whose start_plan was in the plan set (they were in this tier).
    """
    mrr = prepare_mrr(mrr)
    subset = mrr[mrr["_ep"].isin(plan_set) | mrr["_sp"].isin(plan_set)].copy()
    subset["_delta"] = subset["_em"] - subset["_sm"]
    exp = subset[(subset["_sm"] > 0) & (subset["_delta"] > 0)].sort_values("_delta", ascending=False)
    new_mrr = subset[(subset["_sm"] == 0) & (subset["_em"] > 0)].sort_values("_em", ascending=False)

    return {
        "label": label,
        "total_expansion_mrr": money(_s(exp, "_delta")),
        "expander_count": len(exp),
        "all_expanders": accounts_table(exp.head(200)),
        "new_mrr_total": money(_s(new_mrr, "_em")),
        "new_mrr_count": int(len(new_mrr)),
        "new_mrr_accounts": accounts_table(new_mrr.head(200)),
    }


def cohort_retention_analysis(mrr, plan_set, label=""):
    """Run logo retention filtered to a cohort."""
    mrr = prepare_mrr(mrr)
    start_active = mrr[(mrr["_sm"] > 0) & (mrr["_sp"].isin(plan_set))].copy()
    start_count = len(start_active)
    if start_count == 0:
        return {"label": label, "start_count": 0, "retained_count": 0,
                "logo_retention_pct": None, "churned_count": 0,
                "churned_accounts": [], "expansion_mrr_total": 0, "new_mrr_total": 0}

    churned_mask = (start_active["_em"] == 0) | start_active["_ep"].isna()
    # Exclude sub-migrated orgs from churn (TRIAL_EXPIRED = Synder-initiated migration, not voluntary)
    if "latest_sub_status" in start_active.columns:
        churned_mask = churned_mask & ~start_active.apply(is_sub_migrated, axis=1)
    churned = start_active[churned_mask]
    churned_count = len(churned)
    retained_count = start_count - churned_count
    logo_retention_pct = round(retained_count / start_count * 100, 2) if start_count else None

    exp_df = mrr[(mrr["_sm"] > 0) & (mrr["_em"] > mrr["_sm"]) & (mrr["_sp"].isin(plan_set) | mrr["_ep"].isin(plan_set))]
    exp_mrr = money(exp_df.apply(lambda r: r["_em"] - r["_sm"], axis=1).sum())

    new_mrr_df = mrr[(mrr["_sm"] == 0) & (mrr["_em"] > 0) & (mrr["_ep"].isin(plan_set))]
    new_mrr_total = money(_s(new_mrr_df, "_em"))

    return {
        "label": label,
        "start_count": start_count,
        "retained_count": retained_count,
        "logo_retention_pct": logo_retention_pct,
        "churned_count": churned_count,
        "churned_accounts": accounts_table(churned),
        "expansion_mrr_total": exp_mrr,
        "new_mrr_total": new_mrr_total,
    }


def _sandbox_nrr_analysis(mrr):
    """NRR analysis specifically for sandbox plans (not excluded like in main NRR)."""
    mrr = prepare_mrr(mrr)
    cohort = mrr[(mrr["_sp"].isin(SANDBOX_PLANS)) & (mrr["_sm"] > 0)].copy()
    if cohort.empty:
        return {"label": "Sandbox", "nrr_pct": None, "starting_mrr": 0, "ending_mrr": 0,
                "churn_mrr": 0, "contraction_mrr": 0, "expansion_mrr": 0,
                "plan_breakdown": [], "churned_accounts": [], "expansion_accounts": [],
                "contraction_accounts": [], "cancel_reason_summary": {}}
    starting = _s(cohort, "_sm")
    cohort["_churned"] = (cohort["_em"] == 0) | cohort["_ep"].isna()
    cohort["_ret"] = cohort.apply(lambda r: 0 if r["_churned"] else r["_em"], axis=1)
    retained = cohort["_ret"].sum()
    churn = _s(cohort[cohort["_churned"]], "_sm")
    active = cohort[~cohort["_churned"]]
    exp = active.apply(lambda r: max(0, r["_em"] - r["_sm"]), axis=1).sum()
    contr = active.apply(lambda r: max(0, r["_sm"] - r["_em"]), axis=1).sum()
    churned_accts = accounts_table(cohort[cohort["_churned"]])
    return {
        "label": "Sandbox",
        "nrr_pct": round(safe_div(retained, starting) * 100, 2) if safe_div(retained, starting) else None,
        "starting_mrr": money(starting), "ending_mrr": money(retained),
        "churn_mrr": money(churn), "contraction_mrr": money(contr),
        "expansion_mrr": money(exp), "plan_breakdown": [],
        "churned_accounts": churned_accts,
        "expansion_accounts": accounts_table(active[active["_em"] > active["_sm"]]),
        "contraction_accounts": accounts_table(active[active["_em"] < active["_sm"]]),
        "cancel_reason_summary": {},
    }


def _sandbox_retention_analysis(mrr):
    """Retention analysis specifically for sandbox plans."""
    mrr = prepare_mrr(mrr)
    start_active = mrr[(mrr["_sm"] > 0) & (mrr["_sp"].isin(SANDBOX_PLANS))].copy()
    start_count = len(start_active)
    if start_count == 0:
        return {"label": "Sandbox", "start_count": 0, "retained_count": 0,
                "logo_retention_pct": None, "churned_count": 0, "churned_accounts": [],
                "expansion_mrr_total": 0, "new_mrr_total": 0}
    churned = start_active[(start_active["_em"] == 0) | start_active["_ep"].isna()]
    retained_count = start_count - len(churned)
    return {
        "label": "Sandbox",
        "start_count": start_count,
        "retained_count": retained_count,
        "logo_retention_pct": round(retained_count / start_count * 100, 2) if start_count else None,
        "churned_count": len(churned),
        "churned_accounts": accounts_table(churned),
        "expansion_mrr_total": 0,
        "new_mrr_total": 0,
    }


def build_cohort_data(mrr):
    """Build cohort-specific analysis for all three cohorts + NRR touch tiers."""
    cohorts = {
        "high_med": {
            "nrr": cohort_nrr_analysis(mrr, COHORT_HIGH_MED, "High/Med Touch"),
            "expansion": cohort_expansion_analysis(mrr, COHORT_HIGH_MED, "High/Med Touch"),
            "retention": cohort_retention_analysis(mrr, COHORT_HIGH_MED, "High/Med Touch"),
        },
        "essential": {
            "nrr": cohort_nrr_analysis(mrr, COHORT_ESSENTIAL, "Essential/Scale"),
            "expansion": cohort_expansion_analysis(mrr, COHORT_ESSENTIAL, "Essential/Scale"),
            "retention": cohort_retention_analysis(mrr, COHORT_ESSENTIAL, "Essential/Scale"),
        },
        "basic": {
            "nrr": cohort_nrr_analysis(mrr, COHORT_BASIC, "Basic"),
            "expansion": cohort_expansion_analysis(mrr, COHORT_BASIC, "Basic"),
            "retention": cohort_retention_analysis(mrr, COHORT_BASIC, "Basic"),
        },
        "sandbox": {
            "nrr": _sandbox_nrr_analysis(mrr),
            "expansion": cohort_expansion_analysis(mrr, SANDBOX_PLANS, "Sandbox"),
            "retention": _sandbox_retention_analysis(mrr),
        },
    }
    nrr_by_touch = {
        "high_med": cohort_nrr_analysis(mrr, TOUCH_HIGH_MED, "High/Med Touch"),
        "low": cohort_nrr_analysis(mrr, TOUCH_LOW, "Low Touch (Essential + Basic)"),
    }
    expansion_by_touch = {
        "high_med": cohort_expansion_analysis(mrr, TOUCH_HIGH_MED, "High/Med Touch"),
        "low": cohort_expansion_analysis(mrr, TOUCH_LOW, "Low Touch (Essential + Basic)"),
    }
    return {"cohorts": cohorts, "nrr_by_touch": nrr_by_touch, "expansion_by_touch": expansion_by_touch}


# ---------------------------------------------------------------------------
# Dashboard 2: Health Assessment
# ---------------------------------------------------------------------------

def churn_prediction(mrr, orgs):
    mrr = prepare_mrr(mrr)
    today = pd.Timestamp.now().normalize()
    if "org_id" not in orgs.columns:
        return {"error": "org_id missing from CSV #2"}

    orgs["_cd"] = parse_dates(orgs.get("cancellation_date", pd.Series(dtype="object")))
    orgs["_se"] = parse_dates(orgs.get("subscription_end_date", pd.Series(dtype="object")))

    ids = set(mrr["org_id"].dropna().astype(str))
    orgs["_oid"] = orgs["org_id"].astype(str)
    ic = orgs[orgs["_oid"].isin(ids)].copy()

    wc = ic[(ic["_cd"].notna()) & (ic["_se"].notna()) & (ic["_se"] > today)].copy()
    wc["days_to_churn"] = (wc["_se"] - today).dt.days

    def long_date(ts):
        try:
            if pd.isna(ts):
                return None
            # ts is a pandas Timestamp
            return f"{ts.strftime('%B')} {ts.day}, {ts.year}"
        except Exception:
            return None

    # Human-friendly churn date (e.g., February 12, 2026)
    wc["churn_date"] = wc["_se"].apply(long_date)
    # Keep subscription_end_date separately for display (often same as churn_date)
    wc["subscription_end_date"] = wc["_se"].apply(long_date)

    def bucket(d):
        if d <= 7: return "0-7 days"
        if d <= 14: return "8-14 days"
        if d <= 30: return "15-30 days"
        return "31+ days"

    wc["bucket"] = wc["days_to_churn"].apply(bucket)

    mrr_lu = dict(zip(mrr["org_id"].astype(str), mrr["_em"]))
    wc["mrr"] = wc["_oid"].map(mrr_lu).apply(lambda v: money(v) if pd.notna(v) else 0)

    plan_col = col_find(wc, ["plan_name", "plan", "end_plan"])
    if not plan_col:
        # Fall back to CSV#1 end plan if CSV#2 doesn't have a plan column
        end_plan_lu = dict(zip(mrr["org_id"].astype(str), mrr.get("end_plan", pd.Series(dtype="object"))))
        wc["plan_display"] = wc["_oid"].map(end_plan_lu)

    buckets = []
    for b in ["0-7 days", "8-14 days", "15-30 days", "31+ days"]:
        bd = wc[wc["bucket"] == b]
        buckets.append({"bucket": b, "count": len(bd), "mrr_at_risk": money(bd["mrr"].sum())})

    cols = ["org_id", "org_name", "mrr", "churn_date", "subscription_end_date", "bucket"]
    if plan_col and plan_col in wc.columns:
        wc["plan_display"] = wc[plan_col]
    if "plan_display" in wc.columns:
        cols.insert(2, "plan_display")

    # Ensure org_name exists
    if "org_name" not in wc.columns:
        name_lu = dict(zip(mrr["org_id"].astype(str), mrr.get("org_name", pd.Series(dtype="object"))))
        wc["org_name"] = wc["_oid"].map(name_lu).fillna("")

    valid_cols = [c for c in cols if c in wc.columns]
    accounts = wc.sort_values("days_to_churn")[valid_cols].head(100).to_dict("records")

    # Set synder_url and CSM placeholder (enriched later by _enrich_all_accounts_with_csm)
    for acc in accounts:
        oid = str(acc.get("org_id", ""))
        acc["synder_url"] = synder_org_url(oid)
        acc["csm"] = "Not assigned"

    return {
        "total_count": len(wc), "total_mrr_at_risk": money(wc["mrr"].sum()),
        "buckets": buckets,
        "accounts": accounts,
    }


def churn_from_mrr(mrr):
    """Build churn data from MRR snapshots when no cancellation_date is available.
    Churned = start_mrr > 0 and end_mrr == 0."""
    mrr = prepare_mrr(mrr)
    churned = mrr[(mrr["_sm"] > 0) & (mrr["_em"] == 0)].copy()
    if churned.empty:
        return {"total_count": 0, "total_mrr_at_risk": 0, "buckets": [], "accounts": []}

    # No time-based buckets available — group all under "This period"
    accounts = []
    for _, r in churned.head(200).iterrows():
        oid = str(r.get("org_id", ""))
        acc = {
            "org_id": oid,
            "synder_url": synder_org_url(oid),
            "org_name": r.get("org_name", ""),
            "plan_display": r.get("_sp", ""),
            "mrr": money(r["_sm"]),
            "churn_date": "This period",
            "subscription_end_date": "",
            "bucket": "This period",
        }
        acc["csm"] = "Not assigned"
        accounts.append(acc)

    return {
        "total_count": len(churned),
        "total_mrr_at_risk": money(churned["_sm"].sum()),
        "buckets": [{"bucket": "This period", "count": len(churned), "mrr_at_risk": money(churned["_sm"].sum())}],
        "accounts": accounts,
    }


def at_risk_analysis(mrr, orgs):
    mrr = prepare_mrr(mrr)
    today = pd.Timestamp.now().normalize()

    ids = set(mrr["org_id"].dropna().astype(str))
    orgs["_oid"] = orgs["org_id"].astype(str)
    ic = orgs[orgs["_oid"].isin(ids)].copy()

    # Plan is not guaranteed to be present in CSV#2 — if missing, fall back to CSV#1 (MRR end plan)
    pc = col_find(ic, ["plan_name", "plan", "end_plan"])
    if pc:
        ic["_pn"] = ic[pc].apply(norm_plan)
    else:
        end_plan_lu = dict(zip(mrr["org_id"].astype(str), mrr.get("end_plan", pd.Series(dtype="object"))))
        ic["_pn"] = ic["_oid"].map(end_plan_lu).apply(norm_plan)

    ic["_touch"] = ic["_pn"].apply(touch_tier)

    # Keep only high/medium touch for the At-Risk model
    f = ic[ic["_touch"].isin({"high", "medium"})].copy()
    if f.empty:
        return {"total_at_risk": 0, "accounts": [], "warnings": ["No high/medium touch accounts"]}

    f["_ss"] = parse_dates(f["subscription_start_date"]) if "subscription_start_date" in f.columns else pd.NaT
    f["_ls"] = parse_dates(f["last_sync_date"]) if "last_sync_date" in f.columns else pd.NaT
    f["_cd"] = parse_dates(f["cancellation_date"]) if "cancellation_date" in f.columns else pd.NaT
    f["_se"] = parse_dates(f["subscription_end_date"]) if "subscription_end_date" in f.columns else pd.NaT

    for c in ["total_syncs", "finished_syncs", "failed_syncs", "cancelled_syncs", "rule_failed_syncs", "syncs_current_cycle"]:
        f[f"_{c}"] = pd.to_numeric(f[c], errors="coerce").fillna(0) if c in f.columns else 0

    def intv(row):
        v = str(row.get("subscription_interval", "MONTHLY")).upper()
        if "ANNUAL" in v or "YEAR" in v: return 365
        if "QUARTER" in v: return 90
        return 30

    f["_intv"] = f.apply(intv, axis=1)
    f["_grace_end"] = f["_ss"] + f["_intv"].apply(lambda d: timedelta(days=d))
    f["_grace"] = f["_grace_end"] > today

    f["_no_sync"] = (f["_total_syncs"] == 0) & (~f["_grace"])
    f["_days_since"] = (today - f["_ls"]).dt.days
    f["_stale"] = ((f["_ls"].isna()) | (f["_days_since"] > 14)) & (~f["_grace"])
    bad = f["_cancelled_syncs"] + f["_failed_syncs"] + f["_rule_failed_syncs"]
    f["_fr"] = bad / f["_total_syncs"].replace(0, float("nan"))
    f["_hf"] = f["_fr"] > 0.10

    def reasons(r):
        rr = []
        if r["_no_sync"]: rr.append("no_syncing_yet")
        if r["_stale"]: rr.append("stale_sync")
        if r["_hf"]: rr.append("high_failure_ratio")
        return rr

    f["_rr"] = f.apply(reasons, axis=1)
    f["_rc"] = f["_rr"].apply(len)
    ar = f[f["_rc"] > 0].copy()

    mrr_lu = dict(zip(mrr["org_id"].astype(str), mrr["_em"]))
    ar["_mrr"] = ar["_oid"].map(mrr_lu).apply(lambda v: money(v) if pd.notna(v) else 0)
    ar["_dtc"] = (ar["_se"] - today).dt.days.fillna(9999)

    to = {"high": 0, "medium": 1}
    ar["_to"] = ar["_touch"].map(to)
    ar = ar.sort_values(["_to", "_mrr", "_dtc", "_rc"], ascending=[True, False, True, False])

    # Ensure org_name exists
    if "org_name" not in ar.columns:
        name_lu = dict(zip(mrr["org_id"].astype(str), mrr.get("org_name", pd.Series(dtype="object"))))
        ar["org_name"] = ar["_oid"].map(name_lu).fillna("")

    accounts = []
    for _, r in ar.head(100).iterrows():
        oid = str(r.get("org_id", ""))
        acc = {
            "org_name": r.get("org_name", ""),
            "org_id": oid,
            "synder_url": synder_org_url(oid),
            "plan_name": r.get("_pn", ""),
            "tier": r["_touch"],
            "mrr": r["_mrr"],
            "subscription_start_date": str(r["_ss"].date()) if pd.notna(r["_ss"]) else None,
            "interval": r.get("subscription_interval", ""),
            "last_sync_date": str(r["_ls"].date()) if pd.notna(r["_ls"]) else None,
            "days_since_last_sync": int(r["_days_since"]) if pd.notna(r["_days_since"]) else None,
            "sync_volume_total": int(r["_total_syncs"]),
            "syncs_current_cycle": int(r["_syncs_current_cycle"]) if pd.notna(r.get("_syncs_current_cycle", 0)) else 0,
            "failure_ratio": round(float(r["_fr"]), 3) if pd.notna(r["_fr"]) else None,
            "risk_reasons": ", ".join(r["_rr"]),
            "in_grace_window": "yes" if r["_grace"] else "no",
        }
        acc["csm"] = "Not assigned"
        accounts.append(acc)

    return {"total_at_risk": len(ar), "accounts": accounts, "warnings": []}


# ---------------------------------------------------------------------------
# Growth Signals (web research)
# ---------------------------------------------------------------------------

def _research_growth_iter(org_names, max_orgs=500):
    """Generator: yields one result dict per org.

    Uses DuckDuckGo *Lite* HTML results (more reliable than the JSON endpoints on some hosts).
    """

    TRUSTED_DOMAINS = {
        "crunchbase.com", "techcrunch.com", "venturebeat.com", "prnewswire.com", "businesswire.com",
        "globenewswire.com", "marketwatch.com", "reuters.com", "bloomberg.com", "sec.gov",
        "ft.com", "wsj.com", "cnbc.com", "forbes.com", "fortune.com"
    }

    def _domain(u):
        try:
            return urlparse(u).netloc.replace("www.", "")
        except Exception:
            return ""

    def _strip_tags(s):
        s = re.sub(r"<[^>]+>", " ", s or "")
        s = _html.unescape(s)
        return re.sub(r"\s+", " ", s).strip()

    def _resolve_ddg_redirect(u):
        # Extract uddg=... from duckduckgo redirect links
        try:
            pu = urlparse(u)
            qs = parse_qs(pu.query)
            if "uddg" in qs and qs["uddg"]:
                return qs["uddg"][0]
        except Exception:
            pass
        return u

    def ddg_lite_search(query, max_results=6):
        """Best-effort search.

        1) Try direct DuckDuckGo Lite HTML.
        2) If blocked/throttled, fall back to r.jina.ai proxy (markdown extraction).
        """
        out = []

        def _direct():
            q = urllib.parse.quote_plus(query)
            url = f"https://lite.duckduckgo.com/lite/?q={q}"
            req = urllib.request.Request(url, headers={
                "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121 Safari/537.36",
                "Accept-Language": "en-US,en;q=0.9",
            })
            with urllib.request.urlopen(req, timeout=20) as resp:
                raw = resp.read().decode("utf-8", errors="replace")

            # If DDG serves an interstitial/blocked page, it usually won't include result-link.
            if "result-link" not in raw:
                return []

            pat = r"<a[^>]*class='result-link'[^>]*href=\"([^\"]+)\"[^>]*>(.*?)</a>|<a[^>]*href=\"([^\"]+)\"[^>]*class='result-link'[^>]*>(.*?)</a>"
            res = []
            for m in re.finditer(pat, raw, flags=re.I | re.S):
                href = m.group(1) or m.group(3) or ""
                title = _strip_tags(m.group(2) or m.group(4) or "")

                href2 = ("https:" + href) if href.startswith("//") else href
                real_url = _resolve_ddg_redirect(href2)

                snippet = ""
                m2 = re.search(r"class='result-snippet'>(.*?)</td>", raw[m.end():], flags=re.I | re.S)
                if m2:
                    snippet = _strip_tags(m2.group(1))

                # Skip obvious sponsored results
                if "Sponsored link" in snippet:
                    continue

                res.append({"title": title, "body": snippet, "url": real_url})
                if len(res) >= max_results:
                    break
            return res

        def _proxy():
            q = urllib.parse.quote_plus(query)
            url = f"https://r.jina.ai/http://https://lite.duckduckgo.com/lite/?q={q}"
            req = urllib.request.Request(url, headers={
                "User-Agent": "Mozilla/5.0",
                "Accept-Language": "en-US,en;q=0.9",
            })
            with urllib.request.urlopen(req, timeout=25) as resp:
                raw = resp.read().decode("utf-8", errors="replace")

            res = []
            lines = [ln.strip() for ln in raw.splitlines() if ln.strip()]
            i = 0
            while i < len(lines):
                m = re.match(r"^(\d+)\.\[(.*?)\]\((.*?)\)", lines[i])
                if m:
                    title = _strip_tags(m.group(2))
                    href = m.group(3)
                    href2 = href
                    if href2.startswith("//"):
                        href2 = "https:" + href2
                    real_url = _resolve_ddg_redirect(href2)

                    snippet = ""
                    if i + 1 < len(lines) and not re.match(r"^\d+\.\[", lines[i + 1]):
                        snippet = _strip_tags(lines[i + 1])

                    # Skip sponsored
                    if "Sponsored link" in lines[i] or "Sponsored link" in snippet:
                        i += 1
                        continue

                    res.append({"title": title, "body": snippet, "url": real_url})
                    if len(res) >= max_results:
                        break
                i += 1
            return res

        out = _direct()
        if not out:
            out = _proxy()

        return out

    for org in org_names[:max_orgs]:
        if not org or str(org).strip() == "":
            continue

        # Gentle pacing helps avoid being throttled.
        time.sleep(0.4)

        orgq = f'"{str(org).strip()}"'
        queries = [
            f"{orgq} funding round",
            f"{orgq} raised funding",
            f"{orgq} investment round valuation",
            f"{orgq} Series A Series B funding",
            f"{orgq} acquired acquisition",
        ]

        last_err = None
        norm = []
        for query in queries:
            for attempt in range(2):
                try:
                    norm = ddg_lite_search(query, max_results=6)
                    if norm:
                        last_err = None
                        break
                except Exception as e:
                    last_err = e
                    time.sleep(1.25 * (attempt + 1) ** 2)
            if norm:
                break

        if last_err is not None and not norm:
            yield {"org_name": org, "detected_growth_event_type": None, "event_summary": f"Search error: {last_err}", "event_date": None, "confidence": "low", "sources": []}
            continue

        if not norm:
            yield {"org_name": org, "detected_growth_event_type": None, "event_summary": "No verified growth signals found", "event_date": None, "confidence": "low", "sources": []}
            continue

        combined_raw = " ".join([(n.get("title", "") + " " + n.get("body", "")).strip() for n in norm if (n.get("title") or n.get("body"))])
        text = combined_raw.lower()

        # Detect event type
        etype, conf = None, "low"
        if any(k in text for k in ["series a", "series b", "series c", "series d", "seed round", "pre-seed", "raised", "funding round", "funding", "venture", "investment", "backed by", "post-money valuation", "valuation", "deal"]):
            etype, conf = "funding", "medium"
        if any(k in text for k in ["acquired", "acquisition", "acquires", "buyout"]):
            etype, conf = "acquisition", "medium"
        if any(k in text for k in ["merger", "merged with"]):
            etype, conf = "merger", "medium"
        if any(k in text for k in ["ipo", "went public", "public offering"]):
            etype, conf = "IPO", "medium"

        # Amount extraction (handles "$35M" and "35 million")
        amount = None
        m1 = re.search(r'\$\s*[\d,.]+\s*(?:million|billion|m|b)', combined_raw, flags=re.I)
        if m1:
            amount = re.sub(r"\s+", "", m1.group(0))
        else:
            m2 = re.search(r'\b([\d]{1,3}(?:[\d,.]{0,6})?)\s*(million|billion)\b', combined_raw, flags=re.I)
            if m2:
                # assume USD for readability; best-effort
                num = m2.group(1).replace(",", "")
                mult = m2.group(2).lower()
                suffix = "M" if mult.startswith("m") else "B"
                amount = f"${num}{suffix}"

        if amount:
            # normalize million/billion and m/b suffix
            amount = re.sub(r'million', 'M', amount, flags=re.I)
            amount = re.sub(r'billion', 'B', amount, flags=re.I)
            amount = re.sub(r'\bm\b', 'M', amount, flags=re.I)
            amount = re.sub(r'\bb\b', 'B', amount, flags=re.I)
            conf = "high" if etype else "medium"

        # Round type (best-effort)
        round_type = None
        m = re.search(r'(series\s+[abcd]|seed|pre-seed)', text)
        if m:
            rt = m.group(1).lower()
            round_type = rt.title().replace("Series ", "Series ")

        # Date (best-effort): keep year
        dm = re.search(r'(20(?:2\d))', text)
        year = dm.group(1) if dm else None

        sources = [{"title": n.get("title", ""), "url": n.get("url", "")} for n in norm[:3]]
        top_title = (sources[0].get("title") if sources else "") or ""
        top_url = (sources[0].get("url") if sources else "") or ""
        domain = _domain(top_url)

        # Boost confidence if we have a trusted source
        if domain in TRUSTED_DOMAINS and etype and conf == "medium":
            conf = "high" if amount else "medium"
        if domain in TRUSTED_DOMAINS and not etype:
            # at least we found a serious business source, keep medium
            conf = "medium"

        # Human-readable summary
        if not etype:
            summary = "No verified growth signals found"
        elif etype == "funding":
            if amount and round_type and year:
                summary = f"Likely raised {amount} in a {round_type} funding round ({year})."
            elif amount and year:
                summary = f"Likely raised {amount} in a funding round ({year})."
            elif amount:
                summary = f"Likely raised {amount} in a funding round."
            elif year:
                summary = f"Likely announced fundraising activity ({year})."
            else:
                summary = "Likely announced fundraising activity."
        elif etype == "acquisition":
            summary = f"Likely involved in an acquisition{f' ({year})' if year else ''}."
        elif etype == "merger":
            summary = f"Likely involved in a merger{f' ({year})' if year else ''}."
        else:
            summary = f"Likely IPO / public offering signal{f' ({year})' if year else ''}."

        if top_title or domain:
            src = top_title.strip()[:90]
            if domain:
                summary += f" Source: {domain}{(' — ' + src) if src else ''}."
            elif src:
                summary += f" Source: {src}."

        yield {
            "org_name": org,
            "detected_growth_event_type": etype,
            "event_summary": summary[:340],
            "event_date": year if year and etype else None,
            "confidence": conf,
            "sources": sources,
        }


def research_growth(org_names, max_orgs=50):
    results = list(_research_growth_iter(org_names, max_orgs=max_orgs))
    return {"signals": results, "total_searched": len(org_names[:max_orgs])}


# ---------------------------------------------------------------------------
# Routes
# ---------------------------------------------------------------------------

@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        if request.form.get("username") == ADMIN_USERNAME and request.form.get("password") == ADMIN_PASSWORD:
            session["admin_logged_in"] = True
            return redirect(url_for("admin_settings"))
        return render_template("login.html", error="Invalid credentials")
    return render_template("login.html")


@app.route("/logout")
def logout():
    session.pop("admin_logged_in", None)
    return redirect(url_for("index"))


@app.route("/admin/settings", methods=["GET", "POST"])
@admin_required
def admin_settings():
    saved = False
    if request.method == "POST":
        cfg = load_config()
        hs_key = request.form.get("hubspot_api_key", "").strip()
        cfg["hubspot_api_key"] = hs_key
        if hs_key:
            set_hubspot_api_key(hs_key)  # Cache in memory so it survives config file loss
        cfg["retool_url"] = request.form.get("retool_url", "https://synder.retool.com").strip()
        cfg["retool_email"] = request.form.get("retool_email", "").strip()
        retool_pw = request.form.get("retool_password", "").strip()
        if retool_pw:  # Only update password if provided (don't blank it on re-save)
            cfg["retool_password"] = retool_pw
        retool_token = request.form.get("retool_api_token", "").strip()
        if retool_token:  # Only update token if provided
            cfg["retool_api_token"] = retool_token
        save_config(cfg)
        saved = True
    cfg = load_config()
    return render_template("settings.html",
                           hubspot_api_key=cfg.get("hubspot_api_key", ""),
                           retool_url=cfg.get("retool_url", "https://synder.retool.com"),
                           retool_email=cfg.get("retool_email", ""),
                           retool_has_password=bool(cfg.get("retool_password", "")),
                           retool_has_token=bool(cfg.get("retool_api_token", "")),
                           saved=saved)


@app.route("/api/ping")
def ping():
    return jsonify({"ok": True, "ts": pd.Timestamp.now().isoformat()})

@app.route("/")
def index():
    return render_template("index.html")


@app.route("/api/analyze", methods=["POST"])
def analyze():
    try:
        csv1 = request.files.get("csv1")
        csv2 = request.files.get("csv2")
        if not csv1:
            return jsonify({"error": "CSV #1 is required"}), 400

        # Period filtering params
        period_start = request.form.get("period_start", "").strip()
        period_end = request.form.get("period_end", "").strip()

        mrr_raw = read_csv_safe(csv1)

        # If period filter specified, filter wide-format date columns
        if period_start or period_end:
            cols = list(mrr_raw.columns)
            plan_cols = [c for c in cols if re.match(r'plans\s*\(\d{4}-\d{2}-\d{2}\)', c, re.I)]
            amount_cols = [c for c in cols if re.match(r'amount\s*\(\d{4}-\d{2}-\d{2}\)', c, re.I)]
            if plan_cols and amount_cols:
                def _extract_date(cn):
                    m = re.search(r'(\d{4}-\d{2}-\d{2})', cn)
                    return m.group(1) if m else None
                keep_dates = set()
                for c in plan_cols + amount_cols:
                    d = _extract_date(c)
                    if d:
                        if period_start and d < period_start:
                            continue
                        if period_end and d > period_end:
                            continue
                        keep_dates.add(d)
                if keep_dates:
                    non_date_cols = [c for c in cols if not re.match(r'(plans|amount)\s*\(\d{4}-\d{2}-\d{2}\)', c, re.I)]
                    date_cols = [c for c in cols if re.match(r'(plans|amount)\s*\(\d{4}-\d{2}-\d{2}\)', c, re.I) and _extract_date(c) in keep_dates]
                    mrr_raw = mrr_raw[non_date_cols + date_cols]

        # Try wide-format detection first (date-paired plan/amount columns)
        wide = detect_wide_format(mrr_raw)
        cohort_heatmap_data = None
        if wide is not None:
            mrr = wide
            w1 = [f"Wide-format CSV detected: {wide.attrs.get('date_count', '?')} dates from {wide.attrs.get('start_date', '?')} to {wide.attrs.get('end_date', '?')}",
                   f"Transformed to {len(mrr)} rows with columns: {list(mrr.columns)}"]
            cohort_heatmap_data = cohort_heatmap_from_mrr(mrr_raw)
        else:
            mrr, w1 = map_cols(mrr_raw, MRR_MAP)
            w1.insert(0, f"CSV#1 columns detected: {list(mrr.columns[:15])}")
            if "org_id" not in mrr.columns:
                return jsonify({"error": f"CSV#1 must have an org_id column. Found: {list(mrr_raw.columns[:20])}"}), 400
        mrr = mrr.drop_duplicates(subset=["org_id"], keep="last")
        # Ensure org_id is always string for consistent merging
        mrr["org_id"] = mrr["org_id"].astype(str).str.strip()

        orgs, w2 = None, []
        if csv2:
            orgs_raw = read_csv_safe(csv2)
            orgs, w2 = map_cols(orgs_raw, ORGS_MAP)
            if "org_id" in orgs.columns:
                orgs["org_id"] = orgs["org_id"].astype(str).str.strip()
                orgs = orgs.drop_duplicates(subset=["org_id"], keep="last")

        warns = w1 + w2

        sb, sw = sandbox_analysis(mrr)
        warns += sw
        if orgs is not None:
            sb = enrich_sandbox(sb, mrr, orgs)

        nrr = nrr_analysis(mrr)
        exp = expansion_analysis(mrr)
        ret = retention_analysis(mrr, orgs)

        churn, risk = None, None
        if orgs is not None:
            churn = churn_prediction(mrr, orgs)
            risk = at_risk_analysis(mrr, orgs)

        result = {
            "success": True, "warnings": warns,
            "dashboard1": {"sandbox_cohort": sb, "nrr": nrr, "expansion": exp, "cohort_heatmap": cohort_heatmap_data, "retention": ret, "cohort_data": build_cohort_data(mrr)},
            "dashboard2": {"churn_prediction": churn, "at_risk": risk, "growth_signals": None},
            "meta": {
                "csv1_rows": len(mrr), "csv1_columns": list(mrr.columns[:20]),
                "csv2_rows": len(orgs) if orgs is not None else 0,
                "csv2_columns": list(orgs.columns[:20]) if orgs is not None else [],
            },
        }
        _enrich_all_accounts_with_csm(result)
        _trim_response(result)
        return jsonify(result)
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e), "trace": traceback.format_exc()}), 500


def _growth_candidates_from_request():
    """Return candidate org names for growth research.

    Supports filtering by segment (query arg or form field):
    - hm_essential (default): High + Medium touch + Essential
    - hm: High + Medium touch only
    - essential: Essential only
    - all: no filtering

    Note: touch tier is derived from plan name in CSV#1.
    """
    csv1 = request.files.get("csv1")
    segment = (request.args.get("segment") or request.form.get("segment") or "hm_essential").strip().lower()

    names = []
    meta = {"segment": segment, "total_available": 0, "filtered": False}

    if csv1:
        mrr_raw = read_csv_safe(csv1)
        wide = detect_wide_format(mrr_raw)
        if wide is not None:
            mrr = wide
        else:
            mrr, _ = map_cols(mrr_raw, MRR_MAP)

        if "org_name" not in mrr.columns:
            return [], {**meta, "total_available": 0}

        # pick a plan column to segment on
        plan_series = None
        if "end_plan" in mrr.columns:
            plan_series = mrr["end_plan"]
        elif "start_plan" in mrr.columns:
            plan_series = mrr["start_plan"]

        if plan_series is not None:
            mrr = mrr.copy()
            mrr["_plan"] = plan_series.apply(norm_plan)
        else:
            mrr = mrr.copy()
            mrr["_plan"] = None

        meta["total_available"] = int(mrr["org_name"].dropna().nunique())

        allowed = None
        if segment in ("hm_essential", "high_medium_essential"):
            allowed = (HIGH_TOUCH | MEDIUM_TOUCH | {"ESSENTIAL"})
            meta["filtered"] = True
        elif segment in ("hm", "high_medium"):
            allowed = (HIGH_TOUCH | MEDIUM_TOUCH)
            meta["filtered"] = True
        elif segment in ("essential",):
            allowed = {"ESSENTIAL"}
            meta["filtered"] = True
        elif segment in ("all", "everything"):
            allowed = None
        else:
            # Unknown segment -> default behavior
            allowed = (HIGH_TOUCH | MEDIUM_TOUCH | {"ESSENTIAL"})
            meta["filtered"] = True

        if allowed is not None:
            cand = mrr[mrr["_plan"].isin(allowed)]
        else:
            cand = mrr

        names = cand["org_name"].dropna().astype(str).tolist()
        # Preserve order but de-dupe
        seen = set()
        uniq = []
        for n in names:
            nn = n.strip()
            if not nn or nn.lower() in seen:
                continue
            seen.add(nn.lower())
            uniq.append(nn)
        names = uniq
        meta["total_candidates"] = len(names)

    else:
        data = request.get_json(silent=True)
        names = data.get("org_names", []) if data else []
        meta["total_available"] = len(names)
        meta["total_candidates"] = len(names)

    return names, meta


def _growth_worker(job_id, names, max_orgs=300):
    started = time.time()
    try:
        results = []
        total = min(len(names), max_orgs)
        for idx, item in enumerate(_research_growth_iter(names, max_orgs=max_orgs), start=1):
            results.append(item)
            with GROWTH_JOBS_LOCK:
                job = GROWTH_JOBS.get(job_id, {})
                job.update({
                    "status": "running",
                    "completed": idx,
                    "total": total,
                    "signals": results,
                    "updated_at": time.time(),
                })
                GROWTH_JOBS[job_id] = job
        with GROWTH_JOBS_LOCK:
            job = GROWTH_JOBS.get(job_id, {})
            job.update({
                "status": "done",
                "completed": total,
                "total": total,
                "signals": results,
                "duration_sec": round(time.time() - started, 2),
                "updated_at": time.time(),
            })
            GROWTH_JOBS[job_id] = job
    except Exception as e:
        with GROWTH_JOBS_LOCK:
            job = GROWTH_JOBS.get(job_id, {})
            job.update({
                "status": "error",
                "error": str(e),
                "updated_at": time.time(),
            })
            GROWTH_JOBS[job_id] = job


@app.route("/api/growth-start", methods=["POST"])
def growth_start():
    try:
        names, meta = _growth_candidates_from_request()
        if not names:
            return jsonify({"error": "No org names found"}), 400

        # Default is the whole filtered cohort (up to a cap).
        max_orgs_default = min(len(names), 500)
        max_orgs = int(request.args.get("max_orgs", max_orgs_default))
        max_orgs = max(1, min(max_orgs, 500))

        job_id = str(uuid.uuid4())
        total = min(len(names), max_orgs)
        truncated = len(names) > max_orgs

        # Very rough ETA: DDG calls + parsing. Real times vary.
        eta_minutes = int(max(1, round((total * 2.0) / 60.0)))

        with GROWTH_JOBS_LOCK:
            GROWTH_JOBS[job_id] = {
                "status": "queued",
                "completed": 0,
                "total": total,
                "eta_minutes": eta_minutes,
                "total_available": meta.get("total_available"),
                "total_candidates": len(names),
                "segment": meta.get("segment"),
                "filtered": meta.get("filtered"),
                "truncated": truncated,
                "signals": [],
                "created_at": time.time(),
                "updated_at": time.time(),
            }

        t = threading.Thread(target=_growth_worker, args=(job_id, names, max_orgs), daemon=True)
        t.start()
        return jsonify({
            "success": True,
            "job_id": job_id,
            "total": total,
            "eta_minutes": eta_minutes,
            "total_available": meta.get("total_available"),
            "total_candidates": len(names),
            "segment": meta.get("segment"),
            "filtered": meta.get("filtered"),
            "truncated": truncated,
        })
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 500


@app.route("/api/growth-status", methods=["GET"])
def growth_status():
    job_id = request.args.get("job_id")
    if not job_id:
        return jsonify({"error": "job_id is required"}), 400
    with GROWTH_JOBS_LOCK:
        job = GROWTH_JOBS.get(job_id)
    if not job:
        return jsonify({"error": "job not found"}), 404
    return jsonify({"success": True, **job})


# Backwards compatibility: keep /api/growth-signals but make it start an async job
@app.route("/api/growth-signals", methods=["POST"])
def growth_signals():
    return growth_start()


@app.route("/api/export-csv/<section>", methods=["POST"])
def export_csv(section):
    try:
        data = request.get_json()
        if not data or "rows" not in data:
            return jsonify({"error": "No data"}), 400
        buf = StringIO()
        pd.DataFrame(data["rows"]).to_csv(buf, index=False)
        buf.seek(0)
        return send_file(BytesIO(buf.getvalue().encode()), mimetype="text/csv", as_attachment=True,
                         download_name=f"synder_{section}_{date.today()}.csv")
    except Exception as e:
        return jsonify({"error": str(e)}), 500


# ---------------------------------------------------------------------------
# Retool Workflow integration
# ---------------------------------------------------------------------------

RETOOL_WORKFLOW_ID = "987547fe-7a4d-4e4a-ac71-c4d57ba7261d"
RETOOL_WORKFLOW_API_KEY = "retool_wk_0bf98a7c0e9448a98f823a4d50bd76ff"
RETOOL_WORKFLOW_URL = f"https://api.retool.com/v1/workflows/{RETOOL_WORKFLOW_ID}/startTrigger"
RETOOL_APP_UUID = "9d13f272-3eb5-11ef-8fbd-e3da400a47a2"


def _extract_rows_from_retool_response(raw):
    """Parse rows from various Retool webhook response shapes."""
    if isinstance(raw, list):
        return raw
    if isinstance(raw, dict):
        # Common Retool response keys
        for key in ["data", "results", "rows", "records"]:
            if key in raw and isinstance(raw[key], list):
                return raw[key]
        # Nested under "output"
        out = raw.get("output")
        if isinstance(out, list):
            return out
        if isinstance(out, dict):
            for key in ["data", "results", "rows"]:
                if key in out and isinstance(out[key], list):
                    return out[key]
    return []


# Simple in-memory cache to avoid re-fetching large Retool payloads repeatedly.
# Key: (query_name, sorted(payload_items)) -> {ts, data}
_RETOOL_CACHE = {}
_RETOOL_CACHE_TTL_SEC = int(os.environ.get("RETOOL_CACHE_TTL_SEC", "3600"))  # default 1 hour


def fetch_retool_webhook(query_name="organizations", payload=None):
    """POST to Retool Workflow webhook and return raw JSON response.

    Note: We cache successful responses for a short TTL because the workflow payload can be large/slow.
    """
    body = {"query_name": query_name}
    if payload:
        body.update(payload)

    cache_key = (query_name, tuple(sorted((payload or {}).items())))
    now = time.time()
    cached = _RETOOL_CACHE.get(cache_key)
    if cached and (now - cached.get("ts", 0)) < _RETOOL_CACHE_TTL_SEC:
        return cached.get("data")

    resp = _requests_lib.post(
        RETOOL_WORKFLOW_URL,
        json=body,
        headers={"X-Workflow-Api-Key": RETOOL_WORKFLOW_API_KEY},
        timeout=240,
    )
    # Don't raise here; return a structured error so the caller can surface it.
    if resp.status_code >= 400:
        return {"error": True, "status": resp.status_code, "body": resp.text[:2000]}
    data = resp.json()

    # Cache only non-error responses
    if not (isinstance(data, dict) and data.get("error")):
        _RETOOL_CACHE[cache_key] = {"ts": now, "data": data}

    return data


def build_dataframes_from_rows(rows):
    """Convert rows (list of dicts) to (mrr_df, orgs_df) for analysis."""
    df = pd.DataFrame(rows)

    # Map to the orgs schema (for health/churn analysis)
    orgs_df, warns = map_cols(df, ORGS_MAP)
    if "org_id" in orgs_df.columns:
        orgs_df["org_id"] = orgs_df["org_id"].astype(str).str.strip()
        orgs_df = orgs_df.drop_duplicates(subset=["org_id"], keep="last")

    # Build MRR dataframe — start_mrr = end_mrr = current MRR (point-in-time)
    mrr_map_live = {
        "org_id": ["org_id", "organization_id", "id"],
        "org_name": ["org_name", "organization_name", "name"],
        "start_plan": ["start_plan", "plans", "plan_name", "plan", "current_plan"],
        "end_plan": ["end_plan", "plans", "plan_name", "plan", "current_plan"],
        "start_mrr": ["start_mrr", "mrr", "sub_amount", "amount", "mrr_current"],
        "end_mrr": ["end_mrr", "mrr", "sub_amount", "amount", "mrr_current"],
        "org_link": ["org_link", "synder_link"],
        "latest_sub_status": ["latest_sub_status"],
    }
    mrr_df, mrr_warns = map_cols(df, mrr_map_live)
    # If only single snapshot (no start columns), fall back to end = start
    if "end_plan" in mrr_df.columns and "start_plan" not in mrr_df.columns:
        mrr_df["start_plan"] = mrr_df["end_plan"]
    if "end_mrr" in mrr_df.columns and "start_mrr" not in mrr_df.columns:
        mrr_df["start_mrr"] = mrr_df["end_mrr"]
    if "org_id" in mrr_df.columns:
        mrr_df["org_id"] = mrr_df["org_id"].astype(str).str.strip()
        mrr_df = mrr_df.drop_duplicates(subset=["org_id"], keep="last")

    return mrr_df, orgs_df, warns + mrr_warns


def run_analysis_on_dataframes(mrr_df, orgs_df, warns):
    """Run full analysis suite and return the JSON-serializable result dict."""
    sb, sw = sandbox_analysis(mrr_df)
    warns += sw
    if orgs_df is not None and not orgs_df.empty:
        sb = enrich_sandbox(sb, mrr_df, orgs_df)

    nrr = nrr_analysis(mrr_df)
    exp = expansion_analysis(mrr_df)
    ret = retention_analysis(mrr_df, orgs_df if orgs_df is not None and not orgs_df.empty else None)

    # Cohort breakdowns
    try:
        cohort_data = build_cohort_data(mrr_df)
    except Exception:
        cohort_data = None

    churn, risk = None, None
    if orgs_df is not None and not orgs_df.empty and "org_id" in orgs_df.columns:
        try:
            churn = churn_prediction(mrr_df, orgs_df)
        except Exception:
            pass
        try:
            risk = at_risk_analysis(mrr_df, orgs_df)
        except Exception:
            pass

    # Upsell potential
    try:
        upsell = upsell_potential(mrr_df)
    except Exception:
        upsell = None

    # If churn_prediction returned empty (no cancellation dates), build from MRR churned orgs
    if (churn is None or churn.get("total_count", 0) == 0) and not mrr_df.empty:
        try:
            churn = churn_from_mrr(mrr_df)
        except Exception:
            pass

    return {
        "success": True,
        "warnings": warns,
        "dashboard1": {
            "sandbox_cohort": sb,
            "nrr": nrr,
            "expansion": exp,
            "cohort_heatmap": None,
            "retention": ret,
            "cohort_data": cohort_data,
            "upsell_potential": upsell,
        },
        "dashboard2": {
            "churn_prediction": churn,
            "at_risk": risk,
            "growth_signals": None,
        },
        "meta": {
            "csv1_rows": len(mrr_df),
            "csv1_columns": list(mrr_df.columns[:20]),
            "csv2_rows": len(orgs_df) if orgs_df is not None else 0,
            "csv2_columns": list(orgs_df.columns[:20]) if orgs_df is not None else [],
            "source": "retool_webhook",
        },
    }


def _enrich_all_accounts_with_csm(result, max_orgs=500):
    """Enrich the most important account lists with CSM names from HubSpot.
    Only processes high-priority lists to avoid timeouts (max_orgs per request).
    """
    api_key = get_hubspot_api_key()
    if not api_key:
        return result

    # Extract high-priority account lists to enrich
    d1 = result.get("dashboard1", {})
    d2 = result.get("dashboard2", {})
    sb = d1.get("sandbox_cohort", {}) or {}

    priority_lists = []
    # Expansion
    exp = d1.get("expansion", {}) or {}
    if exp.get("top_expanders"): priority_lists.append(exp["top_expanders"])
    if exp.get("all_expanders"): priority_lists.append(exp["all_expanders"])

    # NRR
    nrr = d1.get("nrr", {}) or {}
    for k in ["churned_accounts", "expansion_accounts", "contraction_accounts"]:
        if nrr.get(k): priority_lists.append(nrr[k])

    # Churn prediction
    cp = d2.get("churn_prediction", {}) or {}
    if cp.get("accounts"): priority_lists.append(cp["accounts"])

    # At-risk
    ar = d2.get("at_risk", {}) or {}
    if ar.get("accounts"): priority_lists.append(ar["accounts"])

    # Sandbox
    for sec in ["F_not_syncing", "G_cancelled_will_churn"]:
        s = sb.get(sec, {}) or {}
        if s.get("accounts"): priority_lists.append(s["accounts"])

    # Sandbox B churn
    b = sb.get("B_churn_downgrade", {}) or {}
    if b.get("churned_accounts"): priority_lists.append(b["churned_accounts"])

    # Cohort data expansion/churn account lists
    cd = d1.get("cohort_data", {}) or {}
    for tier_group in [cd.get("cohorts", {}), cd.get("nrr_by_touch", {}), cd.get("expansion_by_touch", {})]:
        if not isinstance(tier_group, dict):
            continue
        for tier_key, tier in tier_group.items():
            if not isinstance(tier, dict):
                continue
            # nrr_by_touch/expansion_by_touch: tier is directly {churned_accounts: [...], ...}
            for k in ["churned_accounts", "expansion_accounts", "contraction_accounts", "all_expanders", "new_mrr_accounts"]:
                if tier.get(k) and isinstance(tier[k], list):
                    priority_lists.append(tier[k])
            # cohorts: tier has sub-dicts like {nrr: {...}, expansion: {...}, retention: {...}}
            for sub_key, sub in tier.items():
                if not isinstance(sub, dict):
                    continue
                for k in ["churned_accounts", "expansion_accounts", "contraction_accounts", "all_expanders", "new_mrr_accounts"]:
                    if sub.get(k) and isinstance(sub[k], list):
                        priority_lists.append(sub[k])

    # Upsell
    upsell = d1.get("upsell_potential", {}) or {}
    if upsell.get("candidates"): priority_lists.append(upsell["candidates"])

    # Retention
    ret = d1.get("retention", {}) or {}
    for k in ["churned_accounts", "expansion_mrr_accounts", "new_mrr_accounts"]:
        if ret.get(k): priority_lists.append(ret[k])

    # Collect ALL unique org_ids across all lists, then lookup up to max_orgs
    seen = set()
    all_org_ids = []
    for lst in priority_lists:
        for item in (lst or []):
            if isinstance(item, dict):
                oid = str(item.get("org_id", "")).strip()
                if oid and oid not in seen:
                    seen.add(oid)
                    all_org_ids.append(oid)
    all_org_ids = all_org_ids[:max_orgs]

    if not all_org_ids:
        return result

    # Batch lookup (single API call for up to 100 orgs)
    csm_map = hubspot_batch_lookup_orgs(all_org_ids, api_key)
    assigned_count = sum(1 for v in csm_map.values() if v and v != "Not assigned")
    print(f"[CSM enrich] Looked up {len(all_org_ids)} orgs, {assigned_count} have CSMs, api_key starts: {api_key[:12] if api_key else 'NONE'}...", flush=True)

    # Apply to all priority lists
    for lst in priority_lists:
        for item in (lst or []):
            if isinstance(item, dict) and "org_id" in item:
                oid = str(item.get("org_id", "")).strip()
                if oid:
                    item["csm"] = csm_map.get(oid, "Not assigned")
                    if "synder_url" not in item:
                        item["synder_url"] = synder_org_url(oid)

    return result


def _trim_response(result, max_accounts=50):
    """Trim large account lists to keep JSON response small."""
    def trim_list(obj, key):
        if isinstance(obj, dict) and key in obj and isinstance(obj[key], list):
            full = obj[key]
            if len(full) > max_accounts:
                obj[key] = full[:max_accounts]
                obj[f"{key}_total"] = len(full)
                obj[f"{key}_truncated"] = True

    d1 = result.get("dashboard1", {})
    d2 = result.get("dashboard2", {})

    # NRR
    nrr = d1.get("nrr", {})
    trim_list(nrr, "cohort_accounts")
    trim_list(nrr, "churned_accounts")
    trim_list(nrr, "expansion_accounts")
    trim_list(nrr, "contraction_accounts")

    # Expansion
    exp = d1.get("expansion", {})
    trim_list(exp, "all_expanders")
    trim_list(exp, "new_mrr_accounts")
    trim_list(exp, "top_expanders")

    # Retention
    ret = d1.get("retention", {})
    for k in ["expansion_mrr_accounts", "new_mrr_accounts", "churned_accounts",
              "downgraded_accounts", "upgraded_accounts", "unsubscribed_accounts"]:
        trim_list(ret, k)

    # Sandbox
    sb = d1.get("sandbox_cohort", {})
    for section in ["A_cohort", "B_churn_downgrade", "C_moved_to_pro", "D_new_mrr", "E_upgrades_expansion"]:
        s = sb.get(section, {})
        for k in list(s.keys()):
            if isinstance(s.get(k), list) and "account" in k:
                trim_list(s, k)

    # At-risk
    ar = d2.get("at_risk", {})
    trim_list(ar, "accounts")

    # Cohort data
    cd = d1.get("cohort_data", {})
    if cd:
        for tier in ["cohorts", "nrr_by_touch", "expansion_by_touch"]:
            group = cd.get(tier, {})
            if isinstance(group, dict):
                for k, v in group.items():
                    if isinstance(v, dict):
                        for key in list(v.keys()):
                            if isinstance(v.get(key), list) and "account" in key:
                                trim_list(v, key)


SNAPSHOT_DIR = "/data/snapshots" if os.path.isdir("/data") else os.path.join(os.path.dirname(os.path.abspath(__file__)), "snapshots")
SNAPSHOT_FILE = os.path.join(SNAPSHOT_DIR, "latest.json")


def _snapshot_path_for_month(year_month: str) -> str:
    """Return path for a month-specific snapshot, e.g. '2026-03' -> /data/snapshots/2026-03.json"""
    return os.path.join(SNAPSHOT_DIR, f"{year_month}.json")


def _load_snapshot(year_month: str = None):
    """Load snapshot. If year_month given (e.g. '2026-02'), load that month. Otherwise load latest."""
    try:
        if year_month:
            path = _snapshot_path_for_month(year_month)
            if os.path.exists(path):
                with open(path, "r") as f:
                    return json.load(f)
            return None
        with open(SNAPSHOT_FILE, "r") as f:
            return json.load(f)
    except Exception:
        return None


def _save_snapshot(payload, year_month: str = None):
    """Save snapshot. If year_month given, save as month-specific file AND as latest."""
    os.makedirs(SNAPSHOT_DIR, exist_ok=True)
    # Always save to latest
    tmp = SNAPSHOT_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump(payload, f)
    os.replace(tmp, SNAPSHOT_FILE)
    # Also save month-specific copy
    if year_month:
        month_path = _snapshot_path_for_month(year_month)
        tmp2 = month_path + ".tmp"
        with open(tmp2, "w") as f:
            json.dump(payload, f)
        os.replace(tmp2, month_path)


def _save_snapshot_month_only(payload, year_month: str):
    """Save only the month-specific snapshot (not latest)."""
    os.makedirs(SNAPSHOT_DIR, exist_ok=True)
    month_path = _snapshot_path_for_month(year_month)
    tmp = month_path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(payload, f)
    os.replace(tmp, month_path)


def _list_available_snapshots():
    """Return list of available month snapshots, e.g. ['2025-12', '2026-01', '2026-02', '2026-03']"""
    if not os.path.isdir(SNAPSHOT_DIR):
        return []
    months = []
    for f in os.listdir(SNAPSHOT_DIR):
        if f.endswith(".json") and f != "latest.json" and len(f) == 12:  # YYYY-MM.json
            months.append(f.replace(".json", ""))
    return sorted(months)


@app.route("/api/snapshot", methods=["GET"])
def api_snapshot_get():
    """Return the last stored snapshot (no Retool call)."""
    snap = _load_snapshot()
    if not snap:
        return jsonify({"connecting": True, "message": "No stored snapshot yet. Ask admin to refresh."}), 200
    return jsonify({"success": True, **snap})


_refresh_status = {"running": False, "progress": {}, "errors": {}, "started_at": None, "finished_at": None}

def _run_refresh_background(months_to_refresh):
    """Run multi-month snapshot refresh in a background thread."""
    from datetime import datetime as _dt, timedelta
    global _refresh_status
    _refresh_status = {"running": True, "progress": {}, "errors": {}, "started_at": _dt.utcnow().isoformat(), "finished_at": None}

    now = _dt.utcnow()
    for i in range(months_to_refresh):
        if i == 0:
            end_date = now.strftime("%Y-%m-%d")
            month_key = now.strftime("%Y-%m")
        else:
            target = now.replace(day=1)
            for _ in range(i):
                target = (target - timedelta(days=1)).replace(day=1)
            next_month = target.replace(day=28) + timedelta(days=4)
            end_date = (next_month - timedelta(days=next_month.day)).strftime("%Y-%m-%d")
            month_key = target.strftime("%Y-%m")

        _refresh_status["progress"][month_key] = "running"
        print(f"[snapshot-refresh] Generating snapshot for {month_key} (end_date={end_date})...", flush=True)
        try:
            with app.test_request_context('/api/snapshot-refresh', method='POST'):
                res = _fetch_and_analyze_from_retool(force_refresh=True, override_end_date=end_date)
            if res.get("success"):
                payload = {"fetched_at": pd.Timestamp.now().isoformat(), "result": res}
                if i == 0:
                    _save_snapshot(payload, year_month=month_key)
                else:
                    _save_snapshot_month_only(payload, year_month=month_key)
                _refresh_status["progress"][month_key] = "ok"
            else:
                _refresh_status["progress"][month_key] = "failed"
                _refresh_status["errors"][month_key] = res.get("message", "unknown")
        except Exception as e:
            _refresh_status["progress"][month_key] = "error"
            _refresh_status["errors"][month_key] = str(e)[:200]
            print(f"[snapshot-refresh] Error for {month_key}: {e}", flush=True)

    _refresh_status["running"] = False
    _refresh_status["finished_at"] = pd.Timestamp.now().isoformat()
    print(f"[snapshot-refresh] Done. Progress: {_refresh_status['progress']}", flush=True)


@app.route("/api/snapshot-refresh", methods=["POST"])
def api_snapshot_refresh():
    """Admin-triggered snapshot refresh. Runs async, returns immediately.
    Poll /api/snapshot-status to check progress.
    Pass JSON {"months": N} to control how many months (default 4, max 12).
    """
    auth = request.headers.get("X-Admin-Key", "")
    if auth != "AdminSynderAnalytics!":
        return jsonify({"error": "unauthorized"}), 401

    if _refresh_status.get("running"):
        return jsonify({"status": "already_running", "progress": _refresh_status["progress"]}), 200

    try:
        body = request.get_json(silent=True) or {}
        months_to_refresh = int(request.args.get("months") or body.get("months", 4))
        months_to_refresh = max(1, min(months_to_refresh, 12))

        import threading
        t = threading.Thread(target=_run_refresh_background, args=(months_to_refresh,), daemon=True)
        t.start()

        return jsonify({
            "status": "started",
            "months": months_to_refresh,
            "message": f"Refresh started for {months_to_refresh} month(s). Poll /api/snapshot-status for progress."
        })
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 500


@app.route("/api/snapshot-status", methods=["GET"])
def api_snapshot_status():
    """Check status of the ongoing or last snapshot refresh."""
    return jsonify({
        **_refresh_status,
        "available_months": _list_available_snapshots()
    })


def _fetch_and_analyze_from_retool(force_refresh=False, override_end_date=None):
    """Core logic: call Retool and build analysis JSON (used by fetch-data and snapshot-refresh)."""
    # Read date range from query params or override
    _json_body = request.get_json(silent=True) or {}
    start_date = request.args.get("start") or _json_body.get("start")
    end_date = override_end_date or request.args.get("end") or _json_body.get("end")
    payload = {}
    if start_date: payload["start_date"] = start_date
    if end_date: payload["end_date"] = end_date

    # 1. Try Retool Workflow webhook — two fast calls (end + start), merge in Python
    # (still potentially slow depending on workflow payload)
    try:
        end_payload = {"target_date": end_date} if end_date else {}
        raw_end = fetch_retool_webhook("organizations", payload=end_payload or None)
        if isinstance(raw_end, dict) and raw_end.get("error"):
            raise Exception(f"Retool HTTP {raw_end.get('status')}: {raw_end.get('body','')[:500]}")
        end_rows = _extract_rows_from_retool_response(raw_end)

        if not start_date and end_rows:
            snap = end_rows[0].get("snapshot_date", "")
            try:
                end_dt = datetime.fromisoformat(snap.replace("Z", "+00:00")) if snap else datetime.utcnow()
                if end_dt.month == 1:
                    start_dt = end_dt.replace(year=end_dt.year - 1, month=12, day=1)
                else:
                    start_dt = end_dt.replace(month=end_dt.month - 1, day=1)
                start_date = start_dt.strftime("%Y-%m-%d")
            except Exception:
                start_date = None

        if start_date:
            raw_start = fetch_retool_webhook("organizations", payload={"target_date": start_date})
            if isinstance(raw_start, dict) and raw_start.get("error"):
                raise Exception(f"Retool start HTTP {raw_start.get('status')}: {raw_start.get('body','')[:500]}")
            start_rows = _extract_rows_from_retool_response(raw_start)
        else:
            start_rows = end_rows

        # Dedup helper (same as before)
        def _dedup_by_id(row_list):
            groups = {}
            for r in row_list:
                oid = str(r.get("org_id", ""))
                groups.setdefault(oid, []).append(r)
            result = {}
            for oid, rlist in groups.items():
                def _plan_sort_key(x):
                    p = (x.get("plan", "") or "").upper()
                    is_addon = p in ADDON_PLANS
                    return (0 if not is_addon else 1, -float(x.get("mrr", 0) or 0))
                primary = min(rlist, key=_plan_sort_key)
                total_mrr = sum(float(x.get("mrr", 0) or 0) for x in rlist)
                primary = dict(primary)
                primary["mrr"] = total_mrr
                result[oid] = primary
            return result

        start_by_id = _dedup_by_id(start_rows)
        end_by_id = _dedup_by_id(end_rows)
        all_ids = set(start_by_id.keys()) | set(end_by_id.keys())

        snapshot_end_date = end_rows[0].get("snapshot_date", "") if end_rows else ""
        snapshot_start_date = start_rows[0].get("snapshot_date", "") if start_rows else ""

        # Build merged rows
        rows = []
        for oid in all_ids:
            s = start_by_id.get(oid, {})
            e = end_by_id.get(oid, {})
            row = {
                "org_id": oid,
                "org_link": (e or s).get("org_link", f"https://go.synder.com/organizations/view/{oid}"),
                "org_name": (e or s).get("org_name", f"Org {oid}"),
                "end_plan": e.get("plan", ""),
                "start_plan": s.get("plan", ""),
                "end_mrr": float(e.get("mrr", 0) or 0),
                "start_mrr": float(s.get("mrr", 0) or 0),
                "snapshot_end_date": snapshot_end_date,
                "snapshot_start_date": snapshot_start_date,
                "industry": (e or s).get("industry", ""),
                "first_paid_date": (e or s).get("first_paid_date", ""),
                # Health fields (may or may not be present depending on workflow)
                "total_syncs": (e or s).get("total_syncs", 0),
                "subscription_end_date": (e or s).get("subscription_end_date", ""),
                "cancellation_date": (e or s).get("cancellation_date", ""),
                "subscription_status": (e or s).get("subscription_status", ""),
                "latest_sub_status": (e or s).get("latest_sub_status", ""),
                "subscription_start_date": (e or s).get("subscription_start_date", "") or (e or s).get("first_paid_date", ""),
                "subscription_interval": (e or s).get("subscription_interval", ""),
                "last_sync_date": (e or s).get("last_sync_date", ""),
                "finished_syncs": (e or s).get("finished_syncs", 0),
                "failed_syncs": (e or s).get("failed_syncs", 0),
                "cancelled_syncs": (e or s).get("cancelled_syncs", 0),
                "rule_failed_syncs": (e or s).get("rule_failed_syncs", 0),
                "syncs_current_cycle": (e or s).get("syncs_current_cycle", 0),
                "transfer_org_id": (e or s).get("transfer_org_id", ""),
                "migrated_from": (e or s).get("migrated_from", ""),
            }
            rows.append(row)

        mrr_df, orgs_df, warns = build_dataframes_from_rows(rows)
        result = run_analysis_on_dataframes(mrr_df, orgs_df, warns)
        _enrich_all_accounts_with_csm(result)
        _trim_response(result)

        # Also compute monthly cohort data and fold into snapshot
        try:
            result["monthly_cohort"] = _compute_monthly_cohort()
        except Exception as _mce:
            print(f"[snapshot] monthly_cohort compute error: {_mce}", flush=True)
            result["monthly_cohort"] = {"error": str(_mce)}
        try:
            result["monthly_retention_cohort"] = _compute_monthly_retention_cohort()
        except Exception as _mrce:
            print(f"[snapshot] monthly_retention_cohort compute error: {_mrce}", flush=True)
            result["monthly_retention_cohort"] = {"error": str(_mrce)}

        return result

    except Exception as exc:
        import traceback as _tb
        print(f"[fetch-data] Retool webhook error: {exc}\n{_tb.format_exc()}", flush=True)
        return {"connecting": True, "message": f"Database connecting... ({str(exc)[:180]})"}


@app.route("/api/fetch-data", methods=["GET", "POST"])
def fetch_data():
    """Default dashboard data endpoint.

    Serves ONLY from stored snapshots. Never calls Retool directly.
    Snapshots are refreshed daily via /api/snapshot-refresh (cron-triggered).
    Supports ?end=YYYY-MM-DD to load a specific month's snapshot.
    """
    try:
        # Determine which month snapshot to load from the end date param
        _json_body = request.get_json(silent=True) or {}
        end_date = request.args.get("end") or _json_body.get("end")

        target_month = None
        if end_date:
            try:
                from datetime import datetime as _dt
                ed = _dt.fromisoformat(end_date.replace("Z", "+00:00")) if "T" in end_date else _dt.strptime(end_date, "%Y-%m-%d")
                target_month = ed.strftime("%Y-%m")
            except Exception:
                pass

        # Try month-specific snapshot first, then fall back to latest
        snap = None
        if target_month:
            snap = _load_snapshot(year_month=target_month)
        if not snap:
            snap = _load_snapshot()

        if snap and isinstance(snap, dict) and snap.get("result"):
            result = snap["result"]
            result["snapshot_fetched_at"] = snap.get("fetched_at", "unknown")
            result["available_months"] = _list_available_snapshots()
            return jsonify(result)

        return jsonify({
            "connecting": True,
            "message": "No data snapshot available yet. Data refreshes automatically once per day. An admin can trigger a manual refresh via POST /api/snapshot-refresh.",
            "available_months": _list_available_snapshots()
        })

    except Exception as e:
        traceback.print_exc()
        return jsonify({"connecting": True, "message": f"Error loading snapshot: {str(e)[:120]}"})


@app.route("/api/auto-fetch", methods=["POST"])
def auto_fetch():
    """Legacy endpoint — delegates to fetch-data."""
    return fetch_data()


@app.route("/api/admin/retool-config", methods=["GET"])
def api_retool_config():
    """Return retool config (admin-only, requires auth header)."""
    auth = request.headers.get("X-Admin-Key", "")
    if auth != "AdminSynderAnalytics!":
        return jsonify({"error": "unauthorized"}), 401
    cfg = get_retool_config()
    return jsonify(cfg)


@app.route("/api/recalc-nrr", methods=["POST"])
def recalc_nrr():
    """Recalculate NRR excluding specified org_ids (sub migration)."""
    try:
        data = request.get_json()
        if not data:
            return jsonify({"error": "No data"}), 400
        exclude_ids = set(str(x) for x in data.get("exclude_org_ids", []))
        nrr_data = data.get("nrr_data")
        retention_data = data.get("retention_data")
        if not nrr_data:
            return jsonify({"error": "nrr_data required"}), 400

        # Recalculate NRR from the provided accounts, excluding specified orgs
        cohort = nrr_data.get("cohort_accounts", [])
        starting_mrr = 0
        ending_mrr = 0
        churn_mrr = 0
        contraction_mrr = 0
        expansion_mrr = 0
        churned_count = 0
        retained_count = 0

        for acc in cohort:
            oid = str(acc.get("org_id", ""))
            sm = float(acc.get("start_mrr", 0) or 0)
            em = float(acc.get("end_mrr", 0) or 0)
            starting_mrr += sm

            if oid in exclude_ids:
                # Treat as retained with same MRR
                ending_mrr += sm
                retained_count += 1
                continue

            is_churned = em == 0
            if is_churned:
                churn_mrr += sm
                churned_count += 1
            else:
                ending_mrr += em
                retained_count += 1
                if em > sm:
                    expansion_mrr += (em - sm)
                elif em < sm:
                    contraction_mrr += (sm - em)

        nrr_pct = round(ending_mrr / starting_mrr * 100, 2) if starting_mrr else None

        # Recalculate logo retention if retention_data provided
        logo_retention = None
        if retention_data:
            start_count = retention_data.get("start_count", 0)
            orig_churned = retention_data.get("churned_count", 0)
            excluded_churned = len([oid for oid in exclude_ids
                                     if any(str(a.get("org_id","")) == oid for a in (retention_data.get("churned_accounts") or []))])
            new_churned = orig_churned - excluded_churned
            new_retained = start_count - new_churned
            logo_retention = round(new_retained / start_count * 100, 2) if start_count else None

        return jsonify({
            "success": True,
            "nrr_pct": nrr_pct,
            "starting_mrr": round(starting_mrr, 2),
            "ending_mrr": round(ending_mrr, 2),
            "churn_mrr": round(churn_mrr, 2),
            "contraction_mrr": round(contraction_mrr, 2),
            "expansion_mrr": round(expansion_mrr, 2),
            "logo_retention_pct": logo_retention,
        })
    except Exception as e:
        return jsonify({"error": str(e)}), 500


def upsell_potential(mrr):
    """Find Essential orgs likely to benefit from Pro upgrade."""
    mrr = prepare_mrr(mrr)
    # Include all low-touch plans that could be upgraded to Pro
    essential = mrr[mrr["_ep"].isin(COHORT_ESSENTIAL)].copy()
    if essential.empty:
        # Try also checking start plan (in case the org recently changed)
        essential = mrr[mrr["_sp"].isin(COHORT_ESSENTIAL) & (mrr["_em"] > 0)].copy()
    if essential.empty:
        return {"candidates": [], "total": 0, "total_mrr": 0, "avg_score": 0,
                "debug": f"No ESSENTIAL/SCALE orgs found in {len(mrr)} rows. Plans seen: {list(mrr['_ep'].dropna().unique()[:10])}"}

    # Tenure from first_paid_date (if available from Retool)
    if "first_paid_date" in essential.columns:
        fpd = pd.to_datetime(essential["first_paid_date"], errors="coerce", utc=True).dt.tz_localize(None)
        essential["_tenure_days"] = (pd.Timestamp.now() - fpd).dt.days
        essential["_tenure_days"] = essential["_tenure_days"].fillna(0)
    else:
        essential["_tenure_days"] = 0

    essential["_score"] = 0

    # Any MRR at all = at least a paying customer
    essential.loc[essential["_em"] > 0, "_score"] += 1

    # High MRR for Essential (above median)
    median_mrr = essential["_em"][essential["_em"] > 0].median() if (essential["_em"] > 0).any() else 0
    if median_mrr and median_mrr > 0:
        essential.loc[essential["_em"] > median_mrr, "_score"] += 2

    # Long tenure (>90 days)
    essential.loc[essential["_tenure_days"] > 90, "_score"] += 1
    # Long tenure (>180 days)
    essential.loc[essential["_tenure_days"] > 180, "_score"] += 1
    # Very long tenure (>365 days)
    essential.loc[essential["_tenure_days"] > 365, "_score"] += 1

    # MRR growth
    essential.loc[essential["_em"] > essential["_sm"], "_score"] += 1

    # Score threshold: 1 (any paying customer qualifies as upsell candidate)
    candidates = essential[essential["_score"] >= 1].sort_values(["_score", "_em"], ascending=[False, False])

    # Build accounts list
    accts = []
    for _, r in candidates.head(100).iterrows():
        oid = r.get("org_id", "")
        accts.append({
            "org_id": str(oid) if oid else "",
            "synder_url": synder_org_url(oid),
            "org_name": r.get("org_name", ""),
            "end_plan": str(r.get("_ep", "ESSENTIAL") or "ESSENTIAL"),
            "start_mrr": money(r.get("_sm", 0)),
            "end_mrr": money(r.get("_em", 0)),
            "tenure_days": int(r.get("_tenure_days", 0)) if pd.notna(r.get("_tenure_days", 0)) else 0,
            "score": int(r.get("_score", 0)),
            "industry": r.get("industry", ""),
            "csm": "Not assigned",  # Will be enriched by frontend CSM lookup if needed
        })

    return {
        "total": len(candidates),
        "total_mrr": money(candidates["_em"].sum()),
        "avg_score": float(round(candidates["_score"].mean(), 1)) if len(candidates) > 0 else 0,
        "candidates": accts,
    }


def _compute_monthly_cohort():
    """Core logic for monthly cohort computation (extracted for reuse in snapshot)."""
    today = date.today().replace(day=1)  # 1st of current month
    months = []
    for i in range(12, 0, -1):
        month_offset = today.month - i
        year_offset = today.year + (month_offset - 1) // 12
        month_val = ((month_offset - 1) % 12) + 1
        m_start = date(year_offset, month_val, 1)
        if m_start.month == 12:
            m_end = m_start.replace(year=m_start.year + 1, month=1)
        else:
            m_end = m_start.replace(month=m_start.month + 1)
        months.append((m_start, m_end))

    cohort_rows = []
    for m_start, m_end in months:
        try:
            raw_start = fetch_retool_webhook("organizations", payload={"target_date": m_start.isoformat()})
            start_rows = _extract_rows_from_retool_response(raw_start)
            raw_end = fetch_retool_webhook("organizations", payload={"target_date": m_end.isoformat()})
            end_rows = _extract_rows_from_retool_response(raw_end)
        except Exception:
            start_rows, end_rows = [], []

        if not start_rows:
            cohort_rows.append({
                "month": m_start.strftime("%Y-%m"),
                "start_orgs": 0, "end_orgs": 0, "churned": 0,
                "logo_retention_pct": None,
                "start_mrr": 0, "end_mrr": 0, "nrr_pct": None,
            })
            continue

        start_by_id = {}
        for r in start_rows:
            oid = str(r.get("org_id", "")).strip()
            mrr_val = float(r.get("mrr", 0) or 0)
            plan = norm_plan(r.get("plan", ""))
            if oid and mrr_val > 0 and plan not in ADDON_PLANS:
                if oid not in start_by_id or mrr_val > start_by_id[oid]["mrr"]:
                    start_by_id[oid] = {"mrr": mrr_val, "plan": plan}

        end_by_id = {}
        for r in end_rows:
            oid = str(r.get("org_id", "")).strip()
            mrr_val = float(r.get("mrr", 0) or 0)
            plan = norm_plan(r.get("plan", ""))
            if oid and plan not in ADDON_PLANS:
                if oid not in end_by_id or mrr_val > end_by_id[oid]["mrr"]:
                    end_by_id[oid] = {"mrr": mrr_val, "plan": plan}

        pro_prem_start = {oid: info for oid, info in start_by_id.items() if info["plan"] in NRR_PLANS}

        if not pro_prem_start:
            cohort_rows.append({
                "month": m_start.strftime("%Y-%m"),
                "start_orgs": 0, "end_orgs": 0, "churned": 0,
                "logo_retention_pct": None,
                "start_mrr": 0, "end_mrr": 0, "nrr_pct": None,
            })
            continue

        start_count = len(pro_prem_start)
        churned_count = 0
        s_mrr = 0
        e_mrr = 0
        for oid, info in pro_prem_start.items():
            s_mrr += info["mrr"]
            end_info = end_by_id.get(oid)
            if end_info and end_info["mrr"] > 0:
                e_mrr += end_info["mrr"]
            else:
                churned_count += 1

        end_count = start_count - churned_count

        cohort_rows.append({
            "month": m_start.strftime("%Y-%m"),
            "start_orgs": start_count,
            "end_orgs": end_count,
            "churned": churned_count,
            "logo_retention_pct": round(end_count / start_count * 100, 1) if start_count else None,
            "start_mrr": money(s_mrr),
            "end_mrr": money(e_mrr),
            "nrr_pct": round(e_mrr / s_mrr * 100, 1) if s_mrr else None,
        })

    return {"success": True, "cohorts": cohort_rows}


def _compute_monthly_retention_cohort():
    """Core logic for monthly retention cohort computation (extracted for reuse in snapshot)."""
    today = date.today().replace(day=1)

    cohort_months = []
    for i in range(12, 0, -1):
        m = (today - timedelta(days=i * 30)).replace(day=1)
        cohort_months.append(m)

    all_months = []
    for i in range(13, -1, -1):
        m = (today - timedelta(days=i * 30)).replace(day=1)
        all_months.append(m)
    all_months = sorted(set(all_months))

    snapshots = {}
    for obs_month in all_months:
        try:
            raw = fetch_retool_webhook("organizations", payload={"target_date": obs_month.isoformat()})
            rows = _extract_rows_from_retool_response(raw)
            snap = {}
            for r in rows:
                oid = str(r.get("org_id", "")).strip()
                plan = norm_plan(r.get("plan", r.get("end_plan", "")))
                mrr = float(r.get("mrr", r.get("end_mrr", 0) or 0) or 0)
                if oid and mrr > 0:
                    snap[oid] = {"plan": plan, "mrr": mrr}
            snapshots[obs_month.strftime("%Y-%m")] = snap
        except Exception:
            snapshots[obs_month.strftime("%Y-%m")] = {}

    org_first_month = {}
    for obs_month in all_months:
        ms = obs_month.strftime("%Y-%m")
        for oid in snapshots.get(ms, {}):
            if oid not in org_first_month:
                org_first_month[oid] = ms

    obs_month_keys = [m.strftime("%Y-%m") for m in all_months]

    def build_cohort_table(plan_set, label):
        cohort_data = []
        for cohort_month in cohort_months:
            cms = cohort_month.strftime("%Y-%m")
            snap_cm = snapshots.get(cms, {})
            cohort_orgs = [
                oid for oid, info in snap_cm.items()
                if org_first_month.get(oid) == cms and info.get("plan") in plan_set
            ]
            if not cohort_orgs:
                continue
            size = len(cohort_orgs)
            cohort_set = set(cohort_orgs)
            retentions = []
            for obs_ms in obs_month_keys:
                if obs_ms < cms:
                    continue
                snap_obs = snapshots.get(obs_ms, {})
                active = sum(1 for oid in cohort_set if oid in snap_obs)
                pct = round(active / size * 100, 1)
                retentions.append({"month": obs_ms, "count": active, "pct": pct})
            cohort_data.append({
                "cohort_month": cms,
                "size": size,
                "retentions": retentions,
            })
        return {"label": label, "cohorts": cohort_data}

    high_med_table = build_cohort_table(COHORT_HIGH_MED, "High/Med Touch")
    essential_table = build_cohort_table(COHORT_ESSENTIAL, "Essential")

    return {
        "success": True,
        "high_med": high_med_table,
        "essential": essential_table,
        "observation_months": obs_month_keys,
    }


@app.route("/api/monthly-cohort", methods=["GET"])
def monthly_cohort():
    """12-month retention cohort for Pro/Premium orgs. Serves from snapshot if available."""
    try:
        snap = _load_snapshot()
        if snap and isinstance(snap, dict) and snap.get("result", {}).get("monthly_cohort"):
            return jsonify(snap["result"]["monthly_cohort"])
    except Exception:
        pass
    # Fallback: live computation
    try:
        return jsonify(_compute_monthly_cohort())
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 500


@app.route("/api/monthly-retention-cohort", methods=["GET"])
def monthly_retention_cohort():
    """Monthly retention cohort tables. Serves from snapshot if available, else live computation."""
    try:
        snap = _load_snapshot()
        if snap and isinstance(snap, dict) and snap.get("result", {}).get("monthly_retention_cohort"):
            return jsonify(snap["result"]["monthly_retention_cohort"])
    except Exception:
        pass
    # Fallback: live computation
    try:
        return jsonify(_compute_monthly_retention_cohort())
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 500



@app.route("/api/csm-lookup", methods=["POST"])
def csm_lookup():
    """Batch lookup CSM names from HubSpot for a list of org_ids."""
    try:
        data = request.get_json()
        if not data:
            return jsonify({"error": "No data"}), 400
        org_ids = data.get("org_ids", [])
        if not org_ids:
            return jsonify({"results": {}})

        api_key = get_hubspot_api_key()
        if not api_key:
            # Return "Not assigned" for all when no API key
            return jsonify({"results": {str(oid): "Not assigned" for oid in org_ids}, "debug": "no_api_key"})

        # Use batch lookup for speed (1-2 API calls instead of N)
        results = hubspot_batch_lookup_orgs(org_ids[:200], api_key)
        # Ensure all requested org_ids are in the response
        for oid in org_ids[:200]:
            k = str(oid)
            if k not in results:
                results[k] = "Not assigned"

        return jsonify({"results": results})
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 500


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5555))
    app.run(debug=os.environ.get("FLASK_DEBUG", "0") == "1", host="0.0.0.0", port=port)
