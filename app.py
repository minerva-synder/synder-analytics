"""
Synder Analytics — Retention & Health Dashboard
Flask app: two CSVs → two dashboards.
"""

import os, json, re, math, traceback, csv, threading, time, uuid
from datetime import datetime, date, timedelta
from io import BytesIO, StringIO

import pandas as pd
from flask import Flask, render_template, request, jsonify, send_file

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", os.urandom(24))
app.config["MAX_CONTENT_LENGTH"] = 50 * 1024 * 1024

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
    "org_name": ["org_name", "organization_name", "name", "company"],
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
    "cancellation_date": ["cancellation_date", "unsubscribe_date", "cancel_date", "unsubscribe date"],
    "subscription_end_date": ["subscription_end_date", "sub_end_date", "end_date", "sub end date"],
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

    B = {
        "churned_count": len(churned), "churned_mrr_lost": money(_s(churned, "_sm")),
        "churned_accounts": churned_accounts,
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

    churned_accts = accounts_table(cohort[cohort["_churned"]])
    exp_accts = accounts_table(active[active["_em"] > active["_sm"]])
    contr_accts = accounts_table(active[active["_em"] < active["_sm"]])

    return {
        "nrr_pct": round(safe_div(retained, starting) * 100, 2) if safe_div(retained, starting) else None,
        "starting_mrr": money(starting), "ending_mrr": money(retained),
        "churn_mrr": money(churn), "contraction_mrr": money(contr),
        "expansion_mrr": money(exp), "plan_breakdown": breakdown,
        "cohort_accounts": accounts_table(cohort),
        "churned_accounts": churned_accts,
        "expansion_accounts": exp_accts,
        "contraction_accounts": contr_accts,
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
    return {
        "total_count": len(wc), "total_mrr_at_risk": money(wc["mrr"].sum()),
        "buckets": buckets,
        "accounts": wc.sort_values("days_to_churn")[valid_cols].head(100).to_dict("records"),
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
    for _, r in ar.head(100).iterrows():
        accounts.append({
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
        })

    return {"total_at_risk": len(ar), "accounts": accounts, "warnings": []}


# ---------------------------------------------------------------------------
# Growth Signals (web research)
# ---------------------------------------------------------------------------

def _research_growth_iter(org_names, max_orgs=50):
    """Generator: yields one result dict per org."""
    try:
        from duckduckgo_search import DDGS
    except ImportError:
        raise RuntimeError("duckduckgo-search not installed")

    ddgs = DDGS()

    for org in org_names[:max_orgs]:
        if not org or str(org).strip() == "":
            continue
        query = f'"{org}" (funding OR acquisition OR merger OR "series" OR investment OR IPO) 2024 OR 2025 OR 2026'
        try:
            sr = list(ddgs.text(query, max_results=5))
        except Exception as e:
            yield {"org_name": org, "detected_growth_event_type": None, "event_summary": f"Search error: {e}", "event_date": None, "confidence": "low", "sources": []}
            continue

        if not sr:
            yield {"org_name": org, "detected_growth_event_type": None, "event_summary": "No verified signals found", "event_date": None, "confidence": "low", "sources": []}
            continue

        text = " ".join([r.get("body", "") + " " + r.get("title", "") for r in sr]).lower()

        etype, conf = None, "low"
        if any(k in text for k in ["series a", "series b", "series c", "series d", "raised", "funding round", "venture"]):
            etype, conf = "funding", "medium"
        if any(k in text for k in ["acquired", "acquisition", "acquires"]):
            etype, conf = "acquisition", "medium"
        if any(k in text for k in ["merger", "merged with"]):
            etype, conf = "merger", "medium"
        if any(k in text for k in ["ipo", "went public", "public offering"]):
            etype, conf = "IPO", "medium"

        amounts = re.findall(r'\$[\d,.]+\s*(?:million|billion|M|B)', text)
        if amounts:
            conf = "high"
        dm = re.search(r'(20(?:24|25|26))', text)

        sources = [{"title": r.get("title", ""), "url": r.get("href", "")} for r in sr[:3]]
        summary = sr[0].get("body", "")[:250] if etype else "No verified signals found"
        if amounts:
            summary = f"{amounts[0]}. {summary}"

        yield {
            "org_name": org, "detected_growth_event_type": etype,
            "event_summary": summary[:300],
            "event_date": dm.group(0) if dm and etype else None,
            "confidence": conf, "sources": sources,
        }


def research_growth(org_names, max_orgs=50):
    results = list(_research_growth_iter(org_names, max_orgs=max_orgs))
    return {"signals": results, "total_searched": len(org_names[:max_orgs])}


# ---------------------------------------------------------------------------
# Routes
# ---------------------------------------------------------------------------

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

        mrr_raw = read_csv_safe(csv1)

        # Try wide-format detection first (date-paired plan/amount columns)
        wide = detect_wide_format(mrr_raw)
        if wide is not None:
            mrr = wide
            w1 = [f"Wide-format CSV detected: {wide.attrs.get('date_count', '?')} dates from {wide.attrs.get('start_date', '?')} to {wide.attrs.get('end_date', '?')}",
                   f"Transformed to {len(mrr)} rows with columns: {list(mrr.columns)}"]
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

        churn, risk = None, None
        if orgs is not None:
            churn = churn_prediction(mrr, orgs)
            risk = at_risk_analysis(mrr, orgs)

        return jsonify({
            "success": True, "warnings": warns,
            "dashboard1": {"sandbox_cohort": sb, "nrr": nrr, "expansion": exp},
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


def _names_from_request():
    csv1 = request.files.get("csv1")
    if csv1:
        mrr_raw = read_csv_safe(csv1)
        wide = detect_wide_format(mrr_raw)
        if wide is not None:
            mrr = wide
        else:
            mrr, _ = map_cols(mrr_raw, MRR_MAP)
        names = mrr["org_name"].dropna().unique().tolist() if "org_name" in mrr.columns else []
    else:
        data = request.get_json(silent=True)
        names = data.get("org_names", []) if data else []
    return names


def _growth_worker(job_id, names, max_orgs=50):
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
        names = _names_from_request()
        if not names:
            return jsonify({"error": "No org names found"}), 400

        max_orgs = int(request.args.get("max_orgs", 50))
        max_orgs = max(1, min(max_orgs, 50))

        job_id = str(uuid.uuid4())
        total = min(len(names), max_orgs)
        with GROWTH_JOBS_LOCK:
            GROWTH_JOBS[job_id] = {
                "status": "queued",
                "completed": 0,
                "total": total,
                "signals": [],
                "created_at": time.time(),
                "updated_at": time.time(),
            }

        t = threading.Thread(target=_growth_worker, args=(job_id, names, max_orgs), daemon=True)
        t.start()
        return jsonify({"success": True, "job_id": job_id, "total": total})
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


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5555))
    app.run(debug=os.environ.get("FLASK_DEBUG", "0") == "1", host="0.0.0.0", port=port)
