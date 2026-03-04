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
CONFIG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.json")


def load_config():
    try:
        with open(CONFIG_FILE, "r") as f:
            return json.load(f)
    except Exception:
        return {}


def save_config(cfg):
    with open(CONFIG_FILE, "w") as f:
        json.dump(cfg, f, indent=2)


def get_hubspot_api_key():
    return load_config().get("hubspot_api_key", "")

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
        "properties": ["name", "hubspot_owner_id", "custom_configurations"],
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
        return {"csm": "N/A", "custom_configurations": ""}

    cache_key = f"org_{org_id_str}"
    if cache_key in cache:
        return cache[cache_key]

    props = hubspot_search_company_by_org_id(org_id_str, api_key)

    result = {"csm": "N/A", "custom_configurations": ""}
    if props:
        owner_id = props.get("hubspot_owner_id")
        if owner_id:
            owner_cache_key = f"owner_{owner_id}"
            if owner_cache_key in cache:
                result["csm"] = cache[owner_cache_key]
            else:
                name = hubspot_get_owner_name(owner_id, api_key)
                result["csm"] = name or "N/A"
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

# Retention cohorts
COHORT_HIGH_MED = {"PRO", "PREMIUM", "LARGE", "SCALE", "SMALL_ENTERPRISE", "PRO_SPLIT_LICENSE", "PREMIUM_SPLIT_LICENSE"}
COHORT_ESSENTIAL = {"ESSENTIAL"}
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
    "subscription_start_date": ["subscription_start_date", "sub_started", "sub_start", "start_date", "sub started"],
    "subscription_interval": ["subscription_interval", "sub_interval", "interval", "billing_interval", "sub interval"],
    "cancellation_date": ["cancellation_date", "unsubscribe_date", "unsub_date", "cancel_date", "unsubscribe date"],
    "subscription_end_date": ["subscription_end_date", "sub_end_date", "sub_end", "end_date", "sub end date"],
    "total_syncs": ["total_syncs", "sync_volume_total", "total_sync_count", "total syncs"],
    "finished_syncs": ["finished_syncs", "successful_syncs", "finished syncs"],
    "failed_syncs": ["failed_syncs", "failed_sync_count", "failed syncs"],
    "cancelled_syncs": ["cancelled_syncs", "canceled_syncs", "canceled_sync_count", "canceled syncs"],
    "rule_failed_syncs": ["rule_failed_syncs", "rule_failed_sync_count", "rule failed syncs"],
    "last_sync_date": ["last_sync_date", "last_sync_creation_date", "last_sync", "last sync creation date"],
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
    m = sb_now.merge(orgs, on="org_id", how="left", suffixes=("", "_o"))
    today = pd.Timestamp.now().normalize()

    if "total_syncs" in m.columns:
        ts = pd.to_numeric(m["total_syncs"], errors="coerce").fillna(0)
        ns = m[ts == 0]
        sb["F_not_syncing"] = {
            "count": len(ns), "mrr": money(_s(ns, "_em")),
            "accounts": ns[["org_id", "org_name", "_em"]].rename(columns={"_em": "mrr"}).head(50).to_dict("records"),
        }

    if "cancellation_date" in m.columns and "subscription_end_date" in m.columns:
        m["_cd"] = parse_dates(m["cancellation_date"])
        m["_se"] = parse_dates(m["subscription_end_date"])
        wc = m[(m["_cd"].notna()) & (m["_se"] > today)]
        sb["G_cancelled_will_churn"] = {
            "count": len(wc), "mrr_at_risk": money(_s(wc, "_em")),
            "accounts": wc[["org_id", "org_name", "_em", "_se"]].rename(
                columns={"_em": "mrr", "_se": "subscription_end_date"}
            ).head(50).to_dict("records"),
        }
    return sb


def nrr_analysis(mrr):
    mrr = prepare_mrr(mrr)
    # NRR is calculated on an existing revenue base only:
    # - exclude new MRR (start_mrr == 0)
    # - exclude sandbox plans
    cohort = mrr[(mrr["_sp"].isin(NRR_PLANS)) & (mrr["_sm"] > 0) & (~mrr["_sp"].isin(SANDBOX_PLANS))].copy()
    if cohort.empty:
        return {"nrr_pct": None, "starting_mrr": 0, "ending_mrr": 0, "churn_mrr": 0, "contraction_mrr": 0, "expansion_mrr": 0, "plan_breakdown": []}

    starting = _s(cohort, "_sm")
    cohort["_churned"] = (cohort["_em"] == 0) | cohort["_ep"].isna()
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
    }


def retention_analysis(mrr, orgs=None):
    """Compute logo retention and movement stats for the Retention section."""
    mrr = prepare_mrr(mrr)
    today = pd.Timestamp.now().normalize()

    # All orgs that had MRR > 0 at start
    start_active = mrr[mrr["_sm"] > 0].copy()
    start_count = len(start_active)

    # Churned: had MRR at start, 0 at end
    churned = start_active[(start_active["_em"] == 0) | start_active["_ep"].isna()]
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
    if cohort.empty:
        return {"label": label, "nrr_pct": None, "starting_mrr": 0, "ending_mrr": 0,
                "churn_mrr": 0, "contraction_mrr": 0, "expansion_mrr": 0,
                "start_count": 0, "churned_count": 0, "retained_count": 0}

    starting = _s(cohort, "_sm")
    cohort["_churned"] = (cohort["_em"] == 0) | cohort["_ep"].isna()
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
    """Run expansion analysis filtered to a cohort."""
    mrr = prepare_mrr(mrr)
    subset = mrr[mrr["_sp"].isin(plan_set) | mrr["_ep"].isin(plan_set)].copy()
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

    churned = start_active[(start_active["_em"] == 0) | start_active["_ep"].isna()]
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


def build_cohort_data(mrr):
    """Build cohort-specific analysis for all three cohorts + NRR touch tiers."""
    cohorts = {
        "high_med": {
            "nrr": cohort_nrr_analysis(mrr, COHORT_HIGH_MED, "High/Med Touch"),
            "expansion": cohort_expansion_analysis(mrr, COHORT_HIGH_MED, "High/Med Touch"),
            "retention": cohort_retention_analysis(mrr, COHORT_HIGH_MED, "High/Med Touch"),
        },
        "essential": {
            "nrr": cohort_nrr_analysis(mrr, COHORT_ESSENTIAL, "Essential"),
            "expansion": cohort_expansion_analysis(mrr, COHORT_ESSENTIAL, "Essential"),
            "retention": cohort_retention_analysis(mrr, COHORT_ESSENTIAL, "Essential"),
        },
        "basic": {
            "nrr": cohort_nrr_analysis(mrr, COHORT_BASIC, "Basic"),
            "expansion": cohort_expansion_analysis(mrr, COHORT_BASIC, "Basic"),
            "retention": cohort_retention_analysis(mrr, COHORT_BASIC, "Basic"),
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

    # HubSpot CSM lookup + sandbox detection
    api_key = get_hubspot_api_key()
    hs_cache = {}
    for acc in accounts:
        oid = acc.get("org_id", "")
        if api_key and oid:
            hs = hubspot_lookup_org(oid, api_key, hs_cache)
            acc["csm"] = hs["csm"]
            if hs["custom_configurations"] and "enable_pro_sandbox" in hs["custom_configurations"]:
                plan = acc.get("plan_display", "") or ""
                if plan.upper() in ("PRO", "PRO_SPLIT", "PRO_SPLIT_LICENSE"):
                    acc["plan_display"] = "Sandbox"
        else:
            acc["csm"] = "N/A"

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
    api_key = get_hubspot_api_key()
    hs_cache = {}
    accounts = []
    for _, r in churned.head(200).iterrows():
        oid = str(r.get("org_id", ""))
        acc = {
            "org_id": oid,
            "org_name": r.get("org_name", ""),
            "plan_display": r.get("_sp", ""),
            "mrr": money(r["_sm"]),
            "churn_date": "This period",
            "subscription_end_date": "",
            "bucket": "This period",
        }
        if api_key and oid:
            hs = hubspot_lookup_org(oid, api_key, hs_cache)
            acc["csm"] = hs["csm"]
        else:
            acc["csm"] = "N/A"
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

    for c in ["total_syncs", "finished_syncs", "failed_syncs", "cancelled_syncs", "rule_failed_syncs"]:
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
    api_key = get_hubspot_api_key()
    hs_cache = {}
    for _, r in ar.head(100).iterrows():
        acc = {
            "org_name": r.get("org_name", ""),
            "org_id": r.get("org_id", ""),
            "plan_name": r.get("_pn", ""),
            "tier": r["_touch"],
            "mrr": r["_mrr"],
            "subscription_start_date": str(r["_ss"].date()) if pd.notna(r["_ss"]) else None,
            "interval": r.get("subscription_interval", ""),
            "last_sync_date": str(r["_ls"].date()) if pd.notna(r["_ls"]) else None,
            "days_since_last_sync": int(r["_days_since"]) if pd.notna(r["_days_since"]) else None,
            "sync_volume_total": int(r["_total_syncs"]),
            "failure_ratio": round(float(r["_fr"]), 3) if pd.notna(r["_fr"]) else None,
            "risk_reasons": ", ".join(r["_rr"]),
            "in_grace_window": "yes" if r["_grace"] else "no",
        }
        oid = acc["org_id"]
        if api_key and oid:
            hs = hubspot_lookup_org(oid, api_key, hs_cache)
            acc["csm"] = hs["csm"]
        else:
            acc["csm"] = "N/A"
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
        cfg["hubspot_api_key"] = request.form.get("hubspot_api_key", "").strip()
        cfg["retool_url"] = request.form.get("retool_url", "https://synder.retool.com").strip()
        cfg["retool_email"] = request.form.get("retool_email", "").strip()
        retool_pw = request.form.get("retool_password", "").strip()
        if retool_pw:  # Only update password if provided (don't blank it on re-save)
            cfg["retool_password"] = retool_pw
        save_config(cfg)
        saved = True
    cfg = load_config()
    return render_template("settings.html",
                           hubspot_api_key=cfg.get("hubspot_api_key", ""),
                           retool_url=cfg.get("retool_url", "https://synder.retool.com"),
                           retool_email=cfg.get("retool_email", ""),
                           retool_has_password=bool(cfg.get("retool_password", "")),
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

        return jsonify({
            "success": True, "warnings": warns,
            "dashboard1": {"sandbox_cohort": sb, "nrr": nrr, "expansion": exp, "cohort_heatmap": cohort_heatmap_data, "retention": ret, "cohort_data": build_cohort_data(mrr)},
            "dashboard2": {"churn_prediction": churn, "at_risk": risk, "growth_signals": None},
            "meta": {
                "csv1_rows": len(mrr), "csv1_columns": list(mrr.columns[:20]),
                "csv2_rows": len(orgs) if orgs is not None else 0,
                "csv2_columns": list(orgs.columns[:20]) if orgs is not None else [],
            },
        })
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


def fetch_retool_webhook(query_name="organizations", payload=None):
    """POST to Retool Workflow webhook and return raw JSON response."""
    body = {"query_name": query_name}
    if payload:
        body.update(payload)
    resp = _requests_lib.post(
        RETOOL_WORKFLOW_URL,
        json=body,
        headers={"X-Workflow-Api-Key": RETOOL_WORKFLOW_API_KEY},
        timeout=180,
    )
    # Don't raise here; return a structured error so the caller can surface it.
    if resp.status_code >= 400:
        return {"error": True, "status": resp.status_code, "body": resp.text[:2000]}
    return resp.json()


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


@app.route("/api/fetch-data", methods=["GET", "POST"])
def fetch_data():
    """Fetch live data from Retool Workflow webhook and run analysis."""
    try:
        # Read date range from query params
        _json_body = request.get_json(silent=True) or {}
        start_date = request.args.get("start") or _json_body.get("start")
        end_date = request.args.get("end") or _json_body.get("end")
        payload = {}
        if start_date: payload["start_date"] = start_date
        if end_date: payload["end_date"] = end_date

        # 1. Try Retool Workflow webhook
        try:
            raw = fetch_retool_webhook("organizations", payload=payload or None)
            if isinstance(raw, dict) and raw.get("error"):
                raise Exception(f"Retool HTTP {raw.get('status')}: {raw.get('body','')[:500]}")
            rows = _extract_rows_from_retool_response(raw)
        except Exception as e:
            rows = []
            webhook_error = str(e)
            import traceback as _tb
            print(f"[fetch-data] Retool webhook error: {e}\n{_tb.format_exc()}", flush=True)
        else:
            webhook_error = None

        if rows:
            mrr_df, orgs_df, warns = build_dataframes_from_rows(rows)
            if "org_id" not in mrr_df.columns:
                rows = []
            else:
                result = run_analysis_on_dataframes(mrr_df, orgs_df, warns)
                # Trim large account lists to keep response under 100KB
                _trim_response(result)
                return jsonify(result)

        # 2. Fallback: friendly "connecting" response
        msg = "Database connecting..."
        if webhook_error:
            msg += f" ({webhook_error[:120]})"
        else:
            msg += " (Workflow returned empty data — SQL blocks need to be configured in Retool)"
        return jsonify({"connecting": True, "message": msg})

    except Exception as e:
        traceback.print_exc()
        return jsonify({"connecting": True, "message": f"Database connecting... ({str(e)[:120]})"})


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
    essential = mrr[mrr["_ep"] == "ESSENTIAL"].copy()
    if essential.empty:
        return {"candidates": [], "total": 0, "total_mrr": "$0.00", "avg_score": 0}

    # Tenure from first_paid_date
    if "first_paid_date" in essential.columns:
        essential["_tenure_days"] = (pd.Timestamp.now() - pd.to_datetime(essential["first_paid_date"], errors="coerce")).dt.days
    else:
        essential["_tenure_days"] = 0

    essential["_score"] = 0

    # High MRR for Essential (above median)
    median_mrr = essential["_em"].median()
    if median_mrr > 0:
        essential.loc[essential["_em"] > median_mrr, "_score"] += 2

    # Long tenure (>180 days)
    essential.loc[essential["_tenure_days"] > 180, "_score"] += 2

    # Very long tenure (>365 days)
    essential.loc[essential["_tenure_days"] > 365, "_score"] += 1

    # MRR growth
    essential.loc[essential["_em"] > essential["_sm"], "_score"] += 1

    candidates = essential[essential["_score"] >= 2].sort_values("_score", ascending=False)

    # Build accounts list
    accts = []
    for _, r in candidates.head(100).iterrows():
        oid = r.get("org_id", "")
        accts.append({
            "org_id": str(oid) if oid else "",
            "synder_url": synder_org_url(oid),
            "org_name": r.get("org_name", ""),
            "end_plan": "ESSENTIAL",
            "start_mrr": money(r.get("_sm", 0)),
            "end_mrr": money(r.get("_em", 0)),
            "tenure_days": int(r.get("_tenure_days", 0)) if pd.notna(r.get("_tenure_days", 0)) else 0,
            "score": int(r.get("_score", 0)),
            "industry": r.get("industry", ""),
        })

    return {
        "total": len(candidates),
        "total_mrr": money(candidates["_em"].sum()),
        "avg_score": float(round(candidates["_score"].mean(), 1)) if len(candidates) > 0 else 0,
        "candidates": accts,
    }


@app.route("/api/monthly-cohort", methods=["GET"])
def monthly_cohort():
    """12-month retention cohort for Pro/Premium orgs using parameterized Retool workflow calls."""
    try:
        today = date.today().replace(day=1)  # 1st of current month
        months = []
        for i in range(12, 0, -1):
            # Start = 1st of month (i months ago)
            m_start = (today - timedelta(days=i * 30)).replace(day=1)
            # End = 1st of next month
            if m_start.month == 12:
                m_end = m_start.replace(year=m_start.year + 1, month=1)
            else:
                m_end = m_start.replace(month=m_start.month + 1)
            months.append((m_start, m_end))

        cohort_rows = []
        for m_start, m_end in months:
            try:
                raw = fetch_retool_webhook("organizations", payload={
                    "start_date": m_start.isoformat(),
                    "end_date": m_end.isoformat(),
                })
                rows = _extract_rows_from_retool_response(raw)
                df = pd.DataFrame(rows) if rows else pd.DataFrame()
            except Exception:
                df = pd.DataFrame()

            if df.empty or "start_mrr" not in df.columns:
                cohort_rows.append({
                    "month": m_start.strftime("%Y-%m"),
                    "start_orgs": 0, "end_orgs": 0, "churned": 0,
                    "logo_retention_pct": None,
                    "start_mrr": 0, "end_mrr": 0, "nrr_pct": None,
                })
                continue

            df["_sm"] = pd.to_numeric(df.get("start_mrr", 0), errors="coerce").fillna(0)
            df["_em"] = pd.to_numeric(df.get("end_mrr", 0), errors="coerce").fillna(0)
            df["_sp"] = df.get("start_plan", "").apply(norm_plan)
            df["_ep"] = df.get("end_plan", "").apply(norm_plan)

            # Filter to Pro/Premium only
            pro_prem = NRR_PLANS  # HIGH_TOUCH | MEDIUM_TOUCH
            cohort = df[(df["_sp"].isin(pro_prem)) & (df["_sm"] > 0)].copy()

            if cohort.empty:
                cohort_rows.append({
                    "month": m_start.strftime("%Y-%m"),
                    "start_orgs": 0, "end_orgs": 0, "churned": 0,
                    "logo_retention_pct": None,
                    "start_mrr": 0, "end_mrr": 0, "nrr_pct": None,
                })
                continue

            start_count = len(cohort)
            churned = cohort[(cohort["_em"] == 0) | cohort["_ep"].isna()]
            churned_count = len(churned)
            end_count = start_count - churned_count
            s_mrr = cohort["_sm"].sum()
            e_mrr = cohort[~((cohort["_em"] == 0) | cohort["_ep"].isna())]["_em"].sum()

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

        return jsonify({"success": True, "cohorts": cohort_rows})
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 500


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5555))
    app.run(debug=os.environ.get("FLASK_DEBUG", "0") == "1", host="0.0.0.0", port=port)
