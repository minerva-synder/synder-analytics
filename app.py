"""
Synder Analytics — Retention & Health Dashboard
Flask app: two CSVs → two dashboards.
"""

import os, json, re, math, traceback
from datetime import datetime, date, timedelta
from io import BytesIO, StringIO

import pandas as pd
from flask import Flask, render_template, request, jsonify, send_file

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", os.urandom(24))
app.config["MAX_CONTENT_LENGTH"] = 50 * 1024 * 1024

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
SANDBOX_PLANS = {"PRO_SANDBOX", "SANDBOX"}
HIGH_TOUCH = {"PREMIUM", "PREMIUM_SPLIT", "PREM_SPLIT", "SMALL_ENTERPRISE"}
MEDIUM_TOUCH = {"PRO", "PRO_SPLIT", "LARGE"}
NRR_PLANS = HIGH_TOUCH | MEDIUM_TOUCH


def norm_plan(raw):
    if pd.isna(raw) or str(raw).strip() in ("", "-", "nan", "None"):
        return None
    plans = [p.strip().upper() for p in str(raw).split(",")]
    for p in plans:
        if p != "SALES_VOLUME":
            return p
    return plans[0]


def is_sandbox(p):
    return p in SANDBOX_PLANS if p else False


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
    "org_id": ["org_id", "organization_id", "id"],
    "org_name": ["org_name", "organization_name", "name", "company"],
    "plan_name": ["plan_name", "plan", "current_plan", "end_plan"],
    "subscription_start_date": ["subscription_start_date", "sub_started", "sub_start", "start_date"],
    "subscription_interval": ["subscription_interval", "sub_interval", "interval", "billing_interval"],
    "cancellation_date": ["cancellation_date", "unsubscribe_date", "cancel_date"],
    "subscription_end_date": ["subscription_end_date", "sub_end_date", "end_date"],
    "total_syncs": ["total_syncs", "sync_volume_total", "total_sync_count"],
    "finished_syncs": ["finished_syncs", "successful_syncs"],
    "failed_syncs": ["failed_syncs", "failed_sync_count"],
    "cancelled_syncs": ["cancelled_syncs", "canceled_syncs", "canceled_sync_count"],
    "rule_failed_syncs": ["rule_failed_syncs", "rule_failed_sync_count"],
    "last_sync_date": ["last_sync_date", "last_sync_creation_date", "last_sync"],
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
    downgraded = sb_start[sb_start["_ep"].isin({"BASIC", "ESSENTIAL", "MEDIUM"})]
    B = {
        "churned_count": len(churned), "churned_mrr_lost": money(_s(churned, "_sm")),
        "downgraded_count": len(downgraded),
        "downgraded_mrr_before": money(_s(downgraded, "_sm")),
        "downgraded_mrr_after": money(_s(downgraded, "_em")),
        "downgraded_mrr_delta": money(_s(downgraded, "_em") - _s(downgraded, "_sm")),
    }

    moved_pro = sb_start[sb_start["_ep"].isin({"PRO", "PRO_SPLIT"})]
    C = {"count": len(moved_pro), "mrr_now": money(_s(moved_pro, "_em"))}

    new_sb = mrr[(mrr["_ep"].apply(is_sandbox)) & (mrr["_sm"] == 0)]
    D = {"count": len(new_sb), "mrr_now": money(_s(new_sb, "_em"))}

    upgrades = sb_start[sb_start["_ep"].isin({"PREMIUM", "PREMIUM_SPLIT", "PREM_SPLIT", "SMALL_ENTERPRISE"})]
    expansion = sb_start[(sb_start["_ep"].apply(is_sandbox)) & (sb_start["_em"] > sb_start["_sm"])]
    ud = _s(upgrades, "_em") - _s(upgrades, "_sm")
    ed = _s(expansion, "_em") - _s(expansion, "_sm")
    E = {
        "upgrade_count": len(upgrades), "upgrade_mrr_delta": money(ud),
        "expansion_count": len(expansion), "expansion_mrr_delta": money(ed),
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
    cohort = mrr[mrr["_sp"].isin(NRR_PLANS)].copy()
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

    return {
        "nrr_pct": round(safe_div(retained, starting) * 100, 2) if safe_div(retained, starting) else None,
        "starting_mrr": money(starting), "ending_mrr": money(retained),
        "churn_mrr": money(churn), "contraction_mrr": money(contr),
        "expansion_mrr": money(exp), "plan_breakdown": breakdown,
    }


def expansion_analysis(mrr):
    mrr = prepare_mrr(mrr)
    mrr["_delta"] = mrr["_em"] - mrr["_sm"]
    exp = mrr[mrr["_delta"] > 0].sort_values("_delta", ascending=False)
    return {
        "total_expansion_mrr": money(_s(exp, "_delta")),
        "expander_count": len(exp),
        "top_expanders": exp.head(20)[["org_name", "start_mrr", "end_mrr", "_delta"]].rename(
            columns={"start_mrr": "starting_mrr", "end_mrr": "current_mrr", "_delta": "delta"}
        ).to_dict("records"),
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

    def bucket(d):
        if d <= 7: return "0-7 days"
        if d <= 14: return "8-14 days"
        if d <= 30: return "15-30 days"
        return "31+ days"

    wc["bucket"] = wc["days_to_churn"].apply(bucket)

    mrr_lu = dict(zip(mrr["org_id"].astype(str), mrr["_em"]))
    wc["mrr"] = wc["_oid"].map(mrr_lu).apply(lambda v: money(v) if pd.notna(v) else 0)

    plan_col = col_find(wc, ["plan_name", "plan", "end_plan"])

    buckets = []
    for b in ["0-7 days", "8-14 days", "15-30 days", "31+ days"]:
        bd = wc[wc["bucket"] == b]
        buckets.append({"bucket": b, "count": len(bd), "mrr_at_risk": money(bd["mrr"].sum())})

    cols = ["org_id", "org_name", "mrr", "days_to_churn", "bucket"]
    if plan_col and plan_col in wc.columns:
        wc["plan_display"] = wc[plan_col]
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

    pc = col_find(ic, ["plan_name", "plan", "end_plan"])
    if not pc:
        return {"error": "No plan column in CSV #2", "accounts": []}
    ic["_pn"] = ic[pc].apply(norm_plan)

    ht = ic[ic["_pn"].isin(HIGH_TOUCH)].copy(); ht["_touch"] = "high"
    mt = ic[ic["_pn"].isin(MEDIUM_TOUCH)].copy(); mt["_touch"] = "medium"
    f = pd.concat([ht, mt], ignore_index=True)
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

def research_growth(org_names):
    try:
        from duckduckgo_search import DDGS
    except ImportError:
        return {"error": "duckduckgo-search not installed"}

    results = []
    ddgs = DDGS()

    for org in org_names[:50]:
        if not org or str(org).strip() == "":
            continue
        query = f'"{org}" (funding OR acquisition OR merger OR "series" OR investment OR IPO) 2024 OR 2025 OR 2026'
        try:
            sr = list(ddgs.text(query, max_results=5))
        except Exception as e:
            results.append({"org_name": org, "detected_growth_event_type": None, "event_summary": f"Search error: {e}", "event_date": None, "confidence": "low", "sources": []})
            continue

        if not sr:
            results.append({"org_name": org, "detected_growth_event_type": None, "event_summary": "No verified signals found", "event_date": None, "confidence": "low", "sources": []})
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

        results.append({
            "org_name": org, "detected_growth_event_type": etype,
            "event_summary": summary[:300],
            "event_date": dm.group(0) if dm and etype else None,
            "confidence": conf, "sources": sources,
        })

    return {"signals": results, "total_searched": len(org_names[:50])}


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

        mrr_raw = pd.read_csv(csv1, on_bad_lines="skip", engine="python", sep=",", quotechar='"')

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

        orgs, w2 = None, []
        if csv2:
            orgs_raw = pd.read_csv(csv2, on_bad_lines="skip", engine="python", sep=",", quotechar='"')
            orgs, w2 = map_cols(orgs_raw, ORGS_MAP)
            if "org_id" in orgs.columns:
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


@app.route("/api/growth-signals", methods=["POST"])
def growth_signals():
    try:
        csv1 = request.files.get("csv1")
        if csv1:
            mrr_raw = pd.read_csv(csv1, on_bad_lines="skip", engine="python", sep=",", quotechar='"')
            wide = detect_wide_format(mrr_raw)
            if wide is not None:
                mrr = wide
            else:
                mrr, _ = map_cols(mrr_raw, MRR_MAP)
            names = mrr["org_name"].dropna().unique().tolist() if "org_name" in mrr.columns else []
        else:
            data = request.get_json(silent=True)
            names = data.get("org_names", []) if data else []
        if not names:
            return jsonify({"error": "No org names found"}), 400
        return jsonify({"success": True, **research_growth(names)})
    except Exception as e:
        traceback.print_exc()
        return jsonify({"error": str(e)}), 500


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
