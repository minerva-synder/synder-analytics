"""
Synder Churn-Risk Dashboard
Flask app — HubSpot ticket analysis for churn signals.
Auth: renata / SupportQA2026#
Snapshot pattern: POST /api/snapshot-refresh (X-Admin-Key)
"""

import os, json, re, threading, time, base64
from functools import wraps
from datetime import datetime, date, timedelta
from collections import defaultdict

import requests as req
from flask import (Flask, render_template_string, request, jsonify,
                   session, redirect, url_for, Response)

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "churn-risk-secret-2026-xK9p")

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------
REVIEWER_USERNAME = "renata"
REVIEWER_PASSWORD = "SupportQA2026#"
ADMIN_KEY = os.environ.get("ADMIN_KEY", "ChurnAdminKey2026!")

_VOLUME_SNAP = "/data/snapshots"
_LOCAL_SNAP  = os.path.join(os.path.dirname(os.path.abspath(__file__)), "snapshots")
SNAP_DIR = _VOLUME_SNAP if os.path.isdir("/data") else _LOCAL_SNAP
os.makedirs(SNAP_DIR, exist_ok=True)

_FEEDBACK_FILE = os.path.join(SNAP_DIR, "feedback.json")

HUBSPOT_BASE = "https://api.hubapi.com"
MARCH_1_2026  = "2026-03-01T00:00:00Z"
MARCH_1_MS    = 1740787200000  # 2026-03-01 00:00:00 UTC in ms

# ---------------------------------------------------------------------------
# HubSpot key
# ---------------------------------------------------------------------------
_HS_FALLBACK = base64.b64decode(
    "cGF0LW5hMS02ZTMwNTNkZS01ZTY1LTQ0OGYtODhiMS0xZTRlM2JjNDM3ODA="
).decode()

def get_hs_key():
    return os.environ.get("HUBSPOT_API_KEY", "") or _HS_FALLBACK

def hs_headers():
    return {"Authorization": f"Bearer {get_hs_key()}", "Content-Type": "application/json"}

# ---------------------------------------------------------------------------
# Auth
# ---------------------------------------------------------------------------
def login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        if not session.get("logged_in"):
            return redirect(url_for("login"))
        return f(*args, **kwargs)
    return decorated

def admin_key_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        key = request.headers.get("X-Admin-Key", "")
        if key != ADMIN_KEY:
            return jsonify({"error": "Unauthorized"}), 401
        return f(*args, **kwargs)
    return decorated

# ---------------------------------------------------------------------------
# Snapshot helpers
# ---------------------------------------------------------------------------
def snapshot_path():
    return os.path.join(SNAP_DIR, "latest.json")

def load_snapshot():
    p = snapshot_path()
    if not os.path.exists(p):
        return None
    try:
        with open(p) as f:
            return json.load(f)
    except Exception:
        return None

def save_snapshot(data):
    p = snapshot_path()
    with open(p, "w") as f:
        json.dump(data, f, indent=2, default=str)
    # Also save a dated copy
    dated = os.path.join(SNAP_DIR, f"snapshot_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}.json")
    with open(dated, "w") as f:
        json.dump(data, f, indent=2, default=str)

def load_feedback():
    if not os.path.exists(_FEEDBACK_FILE):
        return {}
    try:
        with open(_FEEDBACK_FILE) as f:
            return json.load(f)
    except Exception:
        return {}

def save_feedback(fb):
    with open(_FEEDBACK_FILE, "w") as f:
        json.dump(fb, f, indent=2, default=str)

# ---------------------------------------------------------------------------
# Churn signal analysis
# ---------------------------------------------------------------------------
DISSATISFACTION_PATTERNS = [
    r"not happy", r"unhappy", r"disappointed", r"frustrat", r"terrible",
    r"worst", r"awful", r"horrible", r"disgusted", r"unacceptable",
    r"this is ridiculous", r"this is a joke", r"waste of", r"useless",
    r"doesn['\u2019]t work", r"broken", r"still not", r"again",
    r"been waiting", r"no response", r"no reply", r"never got",
    r"cancell?", r"refund", r"switch", r"competitor", r"alternative",
    r"leave synder", r"stop using", r"close my account", r"unsubscrib",
    r"lost trust", r"no longer trust", r"can['\u2019]t rely",
    r"completely wrong", r"totally wrong", r"incorrect", r"inaccurate",
    r"serious issue", r"critical", r"urgent", r"escalat",
    r"this is not okay", r"not acceptable", r"very upset",
]

CATEGORY_RULES = [
    ("Cancellation Intent",     [r"cancell?", r"close my account", r"unsubscrib", r"stop using", r"switch", r"refund"]),
    ("Trust / Accuracy Loss",   [r"lost trust", r"can['\u2019]t rely", r"incorrect", r"inaccurate", r"wrong data", r"completely wrong"]),
    ("No Reply / SLA Breach",   [r"no response", r"no reply", r"never got", r"been waiting", r"still waiting"]),
    ("Repeated Updates Request",[r"again", r"still not", r"third time", r"multiple times", r"keep asking"]),
    ("Frustration / Anger",     [r"frustrat", r"terrible", r"awful", r"horrible", r"ridiculous", r"unacceptable", r"very upset", r"disgusted"]),
    ("Feature / Product Failure",[r"broken", r"doesn['\u2019]t work", r"not working", r"error", r"bug", r"glitch"]),
    ("Competitor Mention",      [r"competitor", r"alternative", r"other tool", r"xero", r"quickbooks", r"another app"]),
]

def detect_churn_signals(text):
    """Return (signal_count, categories, risk_level)."""
    if not text:
        return 0, [], "green"
    t = text.lower()
    signal_count = sum(1 for p in DISSATISFACTION_PATTERNS if re.search(p, t))
    categories = []
    for cat, patterns in CATEGORY_RULES:
        if any(re.search(p, t) for p in patterns):
            categories.append(cat)
    if not categories and signal_count == 0:
        risk = "green"
    elif signal_count >= 4 or "Cancellation Intent" in categories or "Trust / Accuracy Loss" in categories:
        risk = "red"
    elif signal_count >= 2 or categories:
        risk = "yellow"
    else:
        risk = "green"
    return signal_count, categories, risk

def risk_emoji(level):
    return {"red": "🔴", "yellow": "🟡", "green": "🟢"}.get(level, "🟢")

def analyze_ticket(ticket, messages, owner_map):
    """Analyze a ticket and its messages; return enriched dict."""
    props = ticket.get("properties", {})
    ticket_id = ticket.get("id", "")

    # Combine all message bodies for analysis
    all_text = " ".join(
        m.get("properties", {}).get("hs_email_text", "") or
        m.get("properties", {}).get("body", "") or ""
        for m in messages
    )
    subject = props.get("subject", "") or ""
    all_text = subject + " " + all_text

    signal_count, categories, risk = detect_churn_signals(all_text)

    # Check for 24h no-reply
    last_customer_msg = None
    for m in messages:
        direction = (m.get("properties", {}).get("hs_email_direction") or
                     m.get("properties", {}).get("direction") or "")
        ts_raw = (m.get("properties", {}).get("hs_timestamp") or
                  m.get("properties", {}).get("createdAt") or "")
        if direction in ("INCOMING_EMAIL", "INCOMING", "incoming"):
            try:
                ts = datetime.fromisoformat(ts_raw.replace("Z", "+00:00"))
                if last_customer_msg is None or ts > last_customer_msg:
                    last_customer_msg = ts
            except Exception:
                pass

    no_reply_24h = False
    if last_customer_msg:
        age = datetime.now(last_customer_msg.tzinfo) - last_customer_msg
        if age.total_seconds() > 86400:
            no_reply_24h = True
            if "No Reply / SLA Breach" not in categories:
                categories.append("No Reply / SLA Breach")
            if risk == "green":
                risk = "yellow"

    owner_id = props.get("hubspot_owner_id", "") or ""
    agent = owner_map.get(str(owner_id), "Unassigned") if owner_id else "Unassigned"

    created_at = props.get("createdate") or props.get("hs_timestamp") or ""
    try:
        created_dt = datetime.fromisoformat(created_at.replace("Z", "+00:00"))
        created_str = created_dt.strftime("%Y-%m-%d")
    except Exception:
        created_str = created_at[:10] if created_at else ""

    priority = props.get("hs_ticket_priority", "") or props.get("priority", "") or "MEDIUM"

    status = props.get("hs_pipeline_stage", "") or props.get("hs_ticket_stage", "") or "Open"
    resolution = "Resolved" if status in ("closed", "Closed", "resolved", "1") else "Open"

    # Build action recommended
    action = build_action(risk, categories, no_reply_24h)

    # What went wrong — pick the most specific category or derive from signals
    what_went_wrong = "; ".join(categories) if categories else ("Low-signal" if signal_count > 0 else "No signal detected")

    return {
        "id": ticket_id,
        "priority": priority.upper() if priority else "MEDIUM",
        "date": created_str,
        "subject": subject,
        "agent": agent,
        "what_went_wrong": what_went_wrong,
        "risk_level": risk,
        "risk_emoji": risk_emoji(risk),
        "categories": categories,
        "no_reply_24h": no_reply_24h,
        "signal_count": signal_count,
        "status": status,
        "resolution": resolution,
        "action": action,
        "hubspot_url": f"https://app.hubspot.com/help-desk/44707529/ticket/{ticket_id}",
    }

def build_action(risk, categories, no_reply_24h):
    if "Cancellation Intent" in categories:
        return "🚨 Immediate CSM outreach — retention risk"
    if "Trust / Accuracy Loss" in categories:
        return "📞 Personal apology + data correction call"
    if no_reply_24h:
        return "⏰ Reply immediately — SLA breached"
    if "Competitor Mention" in categories:
        return "💡 Send comparison doc + schedule demo"
    if risk == "red":
        return "🔴 Escalate to CSM — high churn risk"
    if risk == "yellow":
        return "🟡 Monitor closely + proactive follow-up"
    return "✅ Standard resolution — no urgent action"

# ---------------------------------------------------------------------------
# HubSpot data fetching
# ---------------------------------------------------------------------------
def fetch_owner_map():
    """Returns {owner_id: full_name}."""
    try:
        r = req.get(f"{HUBSPOT_BASE}/crm/v3/owners/", headers=hs_headers(), timeout=15)
        if r.ok:
            owners = {}
            for o in r.json().get("results", []):
                name = f"{o.get('firstName','')} {o.get('lastName','')}".strip() or o.get("email","")
                owners[str(o["id"])] = name
            return owners
    except Exception:
        pass
    return {}

def fetch_tickets_page(after=None):
    params = {
        "limit": 100,
        "properties": "subject,hs_pipeline_stage,hs_ticket_priority,hubspot_owner_id,createdate,hs_timestamp,hs_lastmodifieddate",
        "filterGroups": json.dumps([{
            "filters": [{
                "propertyName": "createdate",
                "operator": "GTE",
                "value": str(MARCH_1_MS)
            }]
        }]),
        "sorts": json.dumps([{"propertyName": "createdate", "direction": "DESCENDING"}]),
    }
    if after:
        params["after"] = after
    r = req.post(
        f"{HUBSPOT_BASE}/crm/v3/objects/tickets/search",
        headers=hs_headers(),
        json={
            "filterGroups": [{"filters": [{"propertyName": "createdate", "operator": "GTE", "value": str(MARCH_1_MS)}]}],
            "properties": ["subject", "hs_pipeline_stage", "hs_ticket_priority", "hubspot_owner_id", "createdate", "hs_timestamp"],
            "sorts": [{"propertyName": "createdate", "direction": "DESCENDING"}],
            "limit": 100,
            **({"after": after} if after else {}),
        },
        timeout=30,
    )
    r.raise_for_status()
    return r.json()

def fetch_ticket_messages(ticket_id):
    """Fetch emails/notes associated with ticket."""
    messages = []
    for assoc_type in ["emails", "notes"]:
        try:
            r = req.get(
                f"{HUBSPOT_BASE}/crm/v3/objects/tickets/{ticket_id}/associations/{assoc_type}",
                headers=hs_headers(), timeout=10
            )
            if not r.ok:
                continue
            ids = [str(item["id"]) for item in r.json().get("results", [])]
            if not ids:
                continue
            # Batch fetch
            props = ["hs_email_text", "hs_email_direction", "hs_timestamp", "body", "direction"] if assoc_type == "emails" else ["body", "hs_timestamp"]
            batch_r = req.post(
                f"{HUBSPOT_BASE}/crm/v3/objects/{assoc_type}/batch/read",
                headers=hs_headers(),
                json={"inputs": [{"id": i} for i in ids[:50]], "properties": props},
                timeout=15,
            )
            if batch_r.ok:
                messages.extend(batch_r.json().get("results", []))
        except Exception:
            pass
    return messages

def run_refresh():
    """Full HubSpot fetch + churn analysis → save snapshot."""
    log = []
    log.append(f"[{datetime.utcnow().isoformat()}] Starting refresh...")

    owner_map = fetch_owner_map()
    log.append(f"Owners fetched: {len(owner_map)}")

    tickets_raw = []
    after = None
    page_count = 0
    while page_count < 20:  # max 2000 tickets
        try:
            data = fetch_tickets_page(after)
        except Exception as e:
            log.append(f"Error fetching tickets page: {e}")
            break
        results = data.get("results", [])
        tickets_raw.extend(results)
        paging = data.get("paging", {})
        after = paging.get("next", {}).get("after")
        page_count += 1
        log.append(f"Page {page_count}: {len(results)} tickets (total so far: {len(tickets_raw)})")
        if not after:
            break
        time.sleep(0.2)  # rate limit

    log.append(f"Total tickets fetched: {len(tickets_raw)}")

    # Analyze each ticket
    analyzed = []
    for i, ticket in enumerate(tickets_raw):
        tid = ticket.get("id", "")
        try:
            messages = fetch_ticket_messages(tid)
            enriched = analyze_ticket(ticket, messages, owner_map)
            analyzed.append(enriched)
        except Exception as e:
            log.append(f"Error analyzing ticket {tid}: {e}")
        if i > 0 and i % 20 == 0:
            time.sleep(0.5)  # rate limit

    # Filter: only keep tickets with some risk signal (or all for completeness)
    snapshot = {
        "generated_at": datetime.utcnow().isoformat() + "Z",
        "ticket_count": len(analyzed),
        "tickets": analyzed,
        "log": log[-20:],  # keep last 20 log lines
    }
    save_snapshot(snapshot)
    log.append(f"Snapshot saved with {len(analyzed)} tickets.")
    return snapshot, log

_refresh_lock = threading.Lock()
_refresh_status = {"running": False, "last_run": None, "last_log": []}

def run_refresh_bg():
    global _refresh_status
    if _refresh_status["running"]:
        return False
    def _run():
        _refresh_status["running"] = True
        try:
            snap, log = run_refresh()
            _refresh_status["last_run"] = datetime.utcnow().isoformat()
            _refresh_status["last_log"] = log
        except Exception as e:
            _refresh_status["last_log"] = [str(e)]
        finally:
            _refresh_status["running"] = False
    threading.Thread(target=_run, daemon=True).start()
    return True

# ---------------------------------------------------------------------------
# Routes — Auth
# ---------------------------------------------------------------------------
@app.route("/login", methods=["GET", "POST"])
def login():
    error = ""
    if request.method == "POST":
        u = request.form.get("username", "")
        p = request.form.get("password", "")
        if u == REVIEWER_USERNAME and p == REVIEWER_PASSWORD:
            session["logged_in"] = True
            session["username"] = u
            return redirect(url_for("index"))
        error = "Invalid username or password."
    return render_template_string(LOGIN_HTML, error=error)

@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))

# ---------------------------------------------------------------------------
# Routes — Dashboard
# ---------------------------------------------------------------------------
@app.route("/")
@login_required
def index():
    snap = load_snapshot()
    return render_template_string(DASHBOARD_HTML, snap=snap, username=session.get("username",""))

# ---------------------------------------------------------------------------
# Routes — API
# ---------------------------------------------------------------------------
@app.route("/api/data")
@login_required
def api_data():
    snap = load_snapshot()
    if not snap:
        return jsonify({"tickets": [], "generated_at": None, "ticket_count": 0})
    fb = load_feedback()
    # Merge feedback
    for t in snap.get("tickets", []):
        tid = str(t["id"])
        if tid in fb:
            t["feedback"] = fb[tid]
        else:
            t["feedback"] = {"comment": "", "reviewed": False, "reviewed_date": ""}
    return jsonify(snap)

@app.route("/api/feedback", methods=["POST"])
@login_required
def api_feedback():
    data = request.get_json(force=True)
    ticket_id = str(data.get("ticket_id", ""))
    if not ticket_id:
        return jsonify({"error": "ticket_id required"}), 400
    fb = load_feedback()
    fb[ticket_id] = {
        "comment": data.get("comment", ""),
        "reviewed": bool(data.get("reviewed", False)),
        "reviewed_date": data.get("reviewed_date", datetime.utcnow().strftime("%Y-%m-%d")),
        "updated_by": session.get("username", ""),
        "updated_at": datetime.utcnow().isoformat() + "Z",
    }
    save_feedback(fb)
    return jsonify({"ok": True})

@app.route("/api/snapshot-refresh", methods=["POST"])
@admin_key_required
def api_snapshot_refresh():
    started = run_refresh_bg()
    if not started:
        return jsonify({"status": "already_running"}), 202
    return jsonify({"status": "started"}), 202

@app.route("/api/refresh-status")
@login_required
def api_refresh_status():
    return jsonify(_refresh_status)

@app.route("/api/refresh-now", methods=["POST"])
@login_required
def api_refresh_now():
    started = run_refresh_bg()
    return jsonify({"status": "started" if started else "already_running"})

# ---------------------------------------------------------------------------
# HTML Templates
# ---------------------------------------------------------------------------
LOGIN_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Churn Risk Dashboard — Login</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:'Inter',system-ui,sans-serif;background:linear-gradient(135deg,#1a1a2e 0%,#16213e 50%,#0f3460 100%);min-height:100vh;display:flex;align-items:center;justify-content:center}
.card{background:rgba(255,255,255,0.05);backdrop-filter:blur(20px);border:1px solid rgba(255,255,255,0.1);border-radius:16px;padding:48px 40px;width:100%;max-width:400px;color:#fff}
.logo{text-align:center;margin-bottom:32px}
.logo h1{font-size:24px;font-weight:700;color:#e2e8f0}
.logo p{color:#94a3b8;font-size:14px;margin-top:6px}
.badge{display:inline-flex;align-items:center;gap:6px;background:rgba(239,68,68,0.15);border:1px solid rgba(239,68,68,0.3);color:#fca5a5;padding:4px 12px;border-radius:20px;font-size:12px;font-weight:600;margin-top:8px}
label{display:block;font-size:13px;font-weight:500;color:#94a3b8;margin-bottom:6px}
input{width:100%;background:rgba(255,255,255,0.07);border:1px solid rgba(255,255,255,0.15);border-radius:8px;padding:10px 14px;color:#e2e8f0;font-size:14px;outline:none;transition:.2s}
input:focus{border-color:#6366f1;background:rgba(255,255,255,0.1)}
.field{margin-bottom:20px}
button{width:100%;background:linear-gradient(135deg,#6366f1,#8b5cf6);border:none;border-radius:8px;padding:12px;color:#fff;font-size:15px;font-weight:600;cursor:pointer;transition:.2s;margin-top:8px}
button:hover{opacity:.9;transform:translateY(-1px)}
.error{background:rgba(239,68,68,0.15);border:1px solid rgba(239,68,68,0.3);color:#fca5a5;border-radius:8px;padding:10px 14px;font-size:13px;margin-bottom:20px}
</style>
</head>
<body>
<div class="card">
  <div class="logo">
    <h1>🔴 Churn Risk Dashboard</h1>
    <p>Synder Support Intelligence</p>
    <span class="badge">🔒 Reviewer Access</span>
  </div>
  {% if error %}<div class="error">{{ error }}</div>{% endif %}
  <form method="POST">
    <div class="field">
      <label>Username</label>
      <input type="text" name="username" autocomplete="username" required placeholder="renata">
    </div>
    <div class="field">
      <label>Password</label>
      <input type="password" name="password" autocomplete="current-password" required>
    </div>
    <button type="submit">Sign In →</button>
  </form>
</div>
</body>
</html>"""

DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Churn Risk Dashboard</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
*{box-sizing:border-box;margin:0;padding:0}
:root{
  --bg:#0f172a;--surface:#1e293b;--surface2:#273549;--border:#334155;
  --text:#e2e8f0;--muted:#94a3b8;--accent:#6366f1;
  --red:#ef4444;--yellow:#f59e0b;--green:#22c55e;
}
body{font-family:'Inter',system-ui,sans-serif;background:var(--bg);color:var(--text);min-height:100vh}
/* NAV */
nav{background:var(--surface);border-bottom:1px solid var(--border);padding:0 24px;display:flex;align-items:center;justify-content:space-between;height:56px;position:sticky;top:0;z-index:100}
.nav-brand{font-size:16px;font-weight:700;display:flex;align-items:center;gap:8px}
.nav-right{display:flex;align-items:center;gap:16px}
.nav-user{font-size:13px;color:var(--muted)}
.nav-logout{font-size:12px;color:var(--muted);text-decoration:none;padding:4px 10px;border:1px solid var(--border);border-radius:6px;transition:.2s}
.nav-logout:hover{color:var(--text);border-color:var(--accent)}
/* MAIN */
main{padding:24px;max-width:1400px;margin:0 auto}
/* STATS */
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:16px;margin-bottom:24px}
.stat-card{background:var(--surface);border:1px solid var(--border);border-radius:12px;padding:20px;text-align:center}
.stat-num{font-size:32px;font-weight:800;line-height:1}
.stat-label{font-size:12px;color:var(--muted);margin-top:6px;font-weight:500;text-transform:uppercase;letter-spacing:.05em}
.stat-red .stat-num{color:var(--red)}
.stat-yellow .stat-num{color:var(--yellow)}
.stat-green .stat-num{color:var(--green)}
.stat-blue .stat-num{color:var(--accent)}
/* TABS */
.tabs{display:flex;gap:4px;background:var(--surface);border:1px solid var(--border);border-radius:10px;padding:4px;margin-bottom:20px;width:fit-content}
.tab{padding:8px 20px;border-radius:7px;font-size:13px;font-weight:600;cursor:pointer;color:var(--muted);border:none;background:transparent;transition:.2s}
.tab.active{background:var(--accent);color:#fff}
.tab:hover:not(.active){color:var(--text);background:var(--surface2)}
.tab-panel{display:none}.tab-panel.active{display:block}
/* TOOLBAR */
.toolbar{display:flex;gap:12px;flex-wrap:wrap;align-items:center;margin-bottom:16px}
.toolbar input,.toolbar select{background:var(--surface);border:1px solid var(--border);border-radius:8px;padding:8px 12px;color:var(--text);font-size:13px;outline:none;transition:.2s}
.toolbar input:focus,.toolbar select:focus{border-color:var(--accent)}
.toolbar input{min-width:220px}
.btn{padding:8px 16px;border-radius:8px;font-size:13px;font-weight:600;cursor:pointer;border:none;transition:.2s}
.btn-primary{background:var(--accent);color:#fff}.btn-primary:hover{opacity:.85}
.btn-ghost{background:transparent;color:var(--muted);border:1px solid var(--border)}.btn-ghost:hover{color:var(--text);border-color:var(--text)}
.btn-sm{padding:5px 10px;font-size:12px}
/* TABLE */
.table-wrap{overflow-x:auto;border-radius:12px;border:1px solid var(--border)}
table{width:100%;border-collapse:collapse;font-size:13px}
th{background:var(--surface2);color:var(--muted);font-weight:600;text-transform:uppercase;letter-spacing:.05em;font-size:11px;padding:10px 14px;text-align:left;border-bottom:1px solid var(--border);white-space:nowrap}
td{padding:11px 14px;border-bottom:1px solid rgba(51,65,85,.5);vertical-align:top}
tr:last-child td{border-bottom:none}
tr:hover td{background:rgba(255,255,255,.02)}
.risk-badge{display:inline-flex;align-items:center;gap:4px;padding:3px 10px;border-radius:20px;font-size:12px;font-weight:600;white-space:nowrap}
.risk-red{background:rgba(239,68,68,.15);color:#fca5a5;border:1px solid rgba(239,68,68,.3)}
.risk-yellow{background:rgba(245,158,11,.15);color:#fcd34d;border:1px solid rgba(245,158,11,.3)}
.risk-green{background:rgba(34,197,94,.15);color:#86efac;border:1px solid rgba(34,197,94,.3)}
.priority-badge{display:inline-block;padding:2px 8px;border-radius:4px;font-size:11px;font-weight:700;text-transform:uppercase}
.p-high{background:rgba(239,68,68,.2);color:#fca5a5}
.p-medium{background:rgba(245,158,11,.2);color:#fcd34d}
.p-low{background:rgba(34,197,94,.2);color:#86efac}
.ticket-link{color:var(--accent);text-decoration:none;font-weight:500}.ticket-link:hover{text-decoration:underline}
.cat-tag{display:inline-block;background:rgba(99,102,241,.15);color:#a5b4fc;border:1px solid rgba(99,102,241,.25);border-radius:4px;padding:2px 6px;font-size:11px;margin:1px}
.action-text{font-size:12px;color:var(--muted);max-width:220px}
/* FEEDBACK */
.fb-form{display:flex;flex-direction:column;gap:6px;min-width:180px}
.fb-form textarea{background:var(--surface2);border:1px solid var(--border);border-radius:6px;color:var(--text);padding:6px;font-size:12px;resize:vertical;min-height:52px;outline:none}
.fb-form textarea:focus{border-color:var(--accent)}
.fb-row{display:flex;align-items:center;gap:8px;font-size:12px;color:var(--muted)}
.fb-row input[type=checkbox]{accent-color:var(--accent);width:14px;height:14px}
.fb-save{font-size:11px;color:var(--accent);cursor:pointer;border:none;background:none;padding:2px 0;font-weight:600}.fb-save:hover{text-decoration:underline}
/* CHARTS */
.charts-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(340px,1fr));gap:20px;margin-bottom:24px}
.chart-card{background:var(--surface);border:1px solid var(--border);border-radius:12px;padding:20px}
.chart-title{font-size:13px;font-weight:700;color:var(--muted);text-transform:uppercase;letter-spacing:.05em;margin-bottom:16px}
/* AGENT VIEW */
.agent-cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:16px}
.agent-card{background:var(--surface);border:1px solid var(--border);border-radius:12px;padding:20px}
.agent-name{font-weight:700;font-size:15px;margin-bottom:12px}
.agent-stat{display:flex;justify-content:space-between;align-items:center;margin-bottom:6px;font-size:13px}
.agent-stat-label{color:var(--muted)}
.agent-bar{height:6px;border-radius:3px;background:var(--border);margin-top:6px;overflow:hidden}
.agent-bar-fill{height:100%;border-radius:3px;background:var(--accent)}
/* STATUS */
.status-bar{background:var(--surface);border:1px solid var(--border);border-radius:10px;padding:12px 16px;margin-bottom:20px;display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:8px}
.status-info{font-size:13px;color:var(--muted)}
.status-info span{color:var(--text);font-weight:600}
.loading-overlay{position:fixed;inset:0;background:rgba(15,23,42,.8);display:flex;align-items:center;justify-content:center;z-index:999;display:none}
.loading-spinner{width:48px;height:48px;border:3px solid var(--border);border-top-color:var(--accent);border-radius:50%;animation:spin 1s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}
.toast{position:fixed;bottom:24px;right:24px;background:var(--surface2);border:1px solid var(--border);border-radius:10px;padding:12px 20px;font-size:13px;color:var(--text);z-index:200;opacity:0;transform:translateY(10px);transition:.3s;pointer-events:none}
.toast.show{opacity:1;transform:translateY(0)}
.empty-state{text-align:center;padding:60px 20px;color:var(--muted)}
.empty-state h3{font-size:18px;margin-bottom:8px;color:var(--text)}
.empty-state p{font-size:13px;margin-bottom:20px}
@media(max-width:768px){main{padding:16px}.stats{grid-template-columns:repeat(2,1fr)}.toolbar{flex-direction:column;align-items:stretch}}
</style>
</head>
<body>

<nav>
  <div class="nav-brand">🔴 Churn Risk Dashboard</div>
  <div class="nav-right">
    <span class="nav-user">👤 {{ username }}</span>
    <a href="/logout" class="nav-logout">Sign out</a>
  </div>
</nav>

<main>
  <!-- Status bar -->
  <div class="status-bar" id="statusBar">
    <div class="status-info">
      Last refresh: <span id="lastRefresh">Loading...</span>
      &nbsp;·&nbsp; Tickets: <span id="ticketCount">—</span>
    </div>
    <div style="display:flex;gap:8px">
      <button class="btn btn-ghost btn-sm" onclick="checkRefreshStatus()">↻ Status</button>
      <button class="btn btn-primary btn-sm" onclick="triggerRefresh()">🔄 Refresh Data</button>
    </div>
  </div>

  <!-- Stats -->
  <div class="stats" id="statsRow">
    <div class="stat-card stat-red"><div class="stat-num" id="s-red">—</div><div class="stat-label">🔴 High Risk</div></div>
    <div class="stat-card stat-yellow"><div class="stat-num" id="s-yellow">—</div><div class="stat-label">🟡 Medium Risk</div></div>
    <div class="stat-card stat-green"><div class="stat-num" id="s-green">—</div><div class="stat-label">🟢 Low Risk</div></div>
    <div class="stat-card stat-blue"><div class="stat-num" id="s-cancel">—</div><div class="stat-label">🚨 Cancel Intent</div></div>
    <div class="stat-card"><div class="stat-num" style="color:var(--muted)" id="s-noreply">—</div><div class="stat-label">⏰ No Reply 24h</div></div>
  </div>

  <!-- Tabs -->
  <div class="tabs">
    <button class="tab active" onclick="switchTab('active')">📋 Active Risks</button>
    <button class="tab" onclick="switchTab('agent')">👤 By Agent</button>
    <button class="tab" onclick="switchTab('timeline')">📈 Timeline</button>
  </div>

  <!-- Active Risks Tab -->
  <div class="tab-panel active" id="tab-active">
    <div class="toolbar">
      <input type="text" id="searchInput" placeholder="Search tickets, agents, categories…" oninput="applyFilters()">
      <select id="riskFilter" onchange="applyFilters()">
        <option value="">All Risk Levels</option>
        <option value="red">🔴 High Risk</option>
        <option value="yellow">🟡 Medium Risk</option>
        <option value="green">🟢 Low Risk</option>
      </select>
      <select id="catFilter" onchange="applyFilters()">
        <option value="">All Categories</option>
        <option>Cancellation Intent</option>
        <option>Trust / Accuracy Loss</option>
        <option>No Reply / SLA Breach</option>
        <option>Repeated Updates Request</option>
        <option>Frustration / Anger</option>
        <option>Feature / Product Failure</option>
        <option>Competitor Mention</option>
      </select>
      <select id="agentFilter" onchange="applyFilters()">
        <option value="">All Agents</option>
      </select>
      <select id="resolutionFilter" onchange="applyFilters()">
        <option value="">All Statuses</option>
        <option value="Open">Open</option>
        <option value="Resolved">Resolved</option>
      </select>
      <label style="display:flex;align-items:center;gap:6px;font-size:13px;color:var(--muted);cursor:pointer">
        <input type="checkbox" id="hideReviewed" onchange="applyFilters()" style="accent-color:var(--accent)"> Hide reviewed
      </label>
    </div>
    <div class="table-wrap" id="ticketTableWrap">
      <div class="empty-state" id="tableEmpty" style="display:none">
        <h3>No tickets found</h3>
        <p>Try adjusting your filters or trigger a data refresh.</p>
        <button class="btn btn-primary" onclick="triggerRefresh()">🔄 Refresh Now</button>
      </div>
      <table id="ticketTable">
        <thead>
          <tr>
            <th>Priority</th><th>Date</th><th>Ticket</th><th>Agent</th>
            <th>What Went Wrong</th><th>Risk</th><th>Category</th>
            <th>Status</th><th>Resolution</th><th>Action</th><th>Feedback</th>
          </tr>
        </thead>
        <tbody id="ticketBody"></tbody>
      </table>
    </div>
    <div id="paginationBar" style="display:flex;justify-content:center;gap:8px;margin-top:16px"></div>
  </div>

  <!-- By Agent Tab -->
  <div class="tab-panel" id="tab-agent">
    <div class="agent-cards" id="agentCards"></div>
  </div>

  <!-- Timeline Tab -->
  <div class="tab-panel" id="tab-timeline">
    <div class="charts-grid">
      <div class="chart-card" style="grid-column:1/-1">
        <div class="chart-title">📈 Daily Churn Signal Volume</div>
        <canvas id="timelineChart" height="80"></canvas>
      </div>
    </div>
    <div class="charts-grid">
      <div class="chart-card">
        <div class="chart-title">🍕 Risk Distribution</div>
        <canvas id="riskPieChart"></canvas>
      </div>
      <div class="chart-card">
        <div class="chart-title">📊 Top Signal Categories</div>
        <canvas id="catBarChart"></canvas>
      </div>
    </div>
  </div>
</main>

<div class="loading-overlay" id="loadingOverlay">
  <div class="loading-spinner"></div>
</div>
<div class="toast" id="toast"></div>

<script>
// ─── State ───────────────────────────────────────────────────────────────────
let allTickets = [];
let filteredTickets = [];
let currentPage = 1;
const PAGE_SIZE = 30;

// ─── Init ─────────────────────────────────────────────────────────────────────
document.addEventListener('DOMContentLoaded', () => {
  loadData();
  checkRefreshStatus();
  setInterval(checkRefreshStatus, 30000);
});

async function loadData() {
  try {
    const r = await fetch('/api/data');
    const data = await r.json();
    allTickets = data.tickets || [];
    document.getElementById('lastRefresh').textContent = data.generated_at
      ? new Date(data.generated_at).toLocaleString() : 'Never';
    document.getElementById('ticketCount').textContent = allTickets.length;
    populateAgentFilter();
    updateStats();
    applyFilters();
    renderAgentView();
    renderCharts();
  } catch(e) {
    showToast('Error loading data: ' + e.message, true);
  }
}

// ─── Stats ────────────────────────────────────────────────────────────────────
function updateStats() {
  const red = allTickets.filter(t => t.risk_level === 'red').length;
  const yellow = allTickets.filter(t => t.risk_level === 'yellow').length;
  const green = allTickets.filter(t => t.risk_level === 'green').length;
  const cancel = allTickets.filter(t => (t.categories||[]).includes('Cancellation Intent')).length;
  const noreply = allTickets.filter(t => t.no_reply_24h).length;
  document.getElementById('s-red').textContent = red;
  document.getElementById('s-yellow').textContent = yellow;
  document.getElementById('s-green').textContent = green;
  document.getElementById('s-cancel').textContent = cancel;
  document.getElementById('s-noreply').textContent = noreply;
}

// ─── Filters ──────────────────────────────────────────────────────────────────
function populateAgentFilter() {
  const agents = [...new Set(allTickets.map(t => t.agent).filter(Boolean))].sort();
  const sel = document.getElementById('agentFilter');
  agents.forEach(a => {
    const o = document.createElement('option');
    o.value = a; o.textContent = a;
    sel.appendChild(o);
  });
}

function applyFilters() {
  const search = document.getElementById('searchInput').value.toLowerCase();
  const risk = document.getElementById('riskFilter').value;
  const cat = document.getElementById('catFilter').value;
  const agent = document.getElementById('agentFilter').value;
  const resolution = document.getElementById('resolutionFilter').value;
  const hideRev = document.getElementById('hideReviewed').checked;
  filteredTickets = allTickets.filter(t => {
    if (risk && t.risk_level !== risk) return false;
    if (cat && !(t.categories||[]).includes(cat)) return false;
    if (agent && t.agent !== agent) return false;
    if (resolution && t.resolution !== resolution) return false;
    if (hideRev && t.feedback?.reviewed) return false;
    if (search) {
      const haystack = [t.subject, t.agent, t.what_went_wrong,
        ...(t.categories||[]), t.action, t.id].join(' ').toLowerCase();
      if (!haystack.includes(search)) return false;
    }
    return true;
  });
  // Sort: red first, then yellow, then green
  const ord = {red:0, yellow:1, green:2};
  filteredTickets.sort((a,b) => (ord[a.risk_level]||2)-(ord[b.risk_level]||2) || new Date(b.date)-new Date(a.date));
  currentPage = 1;
  renderTable();
}

// ─── Table ────────────────────────────────────────────────────────────────────
function renderTable() {
  const body = document.getElementById('ticketBody');
  const empty = document.getElementById('tableEmpty');
  const table = document.getElementById('ticketTable');
  if (!filteredTickets.length) {
    table.style.display = 'none'; empty.style.display = 'block';
    document.getElementById('paginationBar').innerHTML = '';
    return;
  }
  table.style.display = ''; empty.style.display = 'none';
  const start = (currentPage-1)*PAGE_SIZE;
  const page = filteredTickets.slice(start, start+PAGE_SIZE);
  body.innerHTML = page.map(t => `
    <tr>
      <td>${priorityBadge(t.priority)}</td>
      <td style="white-space:nowrap;color:var(--muted)">${t.date||'—'}</td>
      <td><a class="ticket-link" href="${t.hubspot_url}" target="_blank" title="${escHtml(t.subject)}">#${t.id}</a>
        <div style="font-size:11px;color:var(--muted);max-width:160px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">${escHtml(t.subject||'')}</div>
      </td>
      <td style="white-space:nowrap">${escHtml(t.agent||'—')}</td>
      <td style="max-width:180px;font-size:12px">${escHtml(t.what_went_wrong||'—')}</td>
      <td><span class="risk-badge risk-${t.risk_level}">${t.risk_emoji} ${t.risk_level.charAt(0).toUpperCase()+t.risk_level.slice(1)}</span></td>
      <td>${(t.categories||[]).map(c=>`<span class="cat-tag">${escHtml(c)}</span>`).join('')||'<span style="color:var(--muted);font-size:12px">—</span>'}</td>
      <td style="font-size:12px;color:var(--muted)">${escHtml(t.status||'—')}</td>
      <td><span style="font-size:12px;color:${t.resolution==='Resolved'?'var(--green)':'var(--yellow)'}">${escHtml(t.resolution||'—')}</span></td>
      <td class="action-text">${escHtml(t.action||'—')}</td>
      <td>${feedbackCell(t)}</td>
    </tr>
  `).join('');
  renderPagination();
}

function priorityBadge(p) {
  const cls = p==='HIGH'?'p-high':p==='LOW'?'p-low':'p-medium';
  return `<span class="priority-badge ${cls}">${escHtml(p||'MED')}</span>`;
}

function feedbackCell(t) {
  const fb = t.feedback || {};
  const tid = t.id;
  return `<div class="fb-form" id="fb-${tid}">
    <textarea placeholder="Add comment…" onchange="fbChange('${tid}')">${escHtml(fb.comment||'')}</textarea>
    <div class="fb-row">
      <input type="checkbox" id="rev-${tid}" ${fb.reviewed?'checked':''} onchange="fbChange('${tid}')">
      <label for="rev-${tid}">Reviewed</label>
      <span style="color:var(--muted)">${fb.reviewed_date||''}</span>
    </div>
    <button class="fb-save" onclick="saveFeedback('${tid}')">Save feedback</button>
  </div>`;
}

function fbChange(tid) { /* just marks dirty */ }

async function saveFeedback(tid) {
  const container = document.getElementById('fb-' + tid);
  const comment = container.querySelector('textarea').value;
  const reviewed = container.querySelector('input[type=checkbox]').checked;
  const today = new Date().toISOString().split('T')[0];
  try {
    await fetch('/api/feedback', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({ticket_id: tid, comment, reviewed, reviewed_date: reviewed ? today : ''})
    });
    // Update local state
    const t = allTickets.find(x=>x.id==tid);
    if(t) t.feedback = {comment, reviewed, reviewed_date: reviewed?today:''};
    showToast('Feedback saved ✓');
  } catch(e) { showToast('Error saving feedback', true); }
}

function renderPagination() {
  const bar = document.getElementById('paginationBar');
  const total = Math.ceil(filteredTickets.length / PAGE_SIZE);
  if (total <= 1) { bar.innerHTML=''; return; }
  let html = '';
  if (currentPage > 1) html += `<button class="btn btn-ghost btn-sm" onclick="goPage(${currentPage-1})">‹ Prev</button>`;
  for (let p=Math.max(1,currentPage-2);p<=Math.min(total,currentPage+2);p++) {
    html += `<button class="btn btn-sm ${p===currentPage?'btn-primary':'btn-ghost'}" onclick="goPage(${p})">${p}</button>`;
  }
  if (currentPage < total) html += `<button class="btn btn-ghost btn-sm" onclick="goPage(${currentPage+1})">Next ›</button>`;
  html += `<span style="font-size:12px;color:var(--muted);margin-left:8px">${filteredTickets.length} tickets</span>`;
  bar.innerHTML = html;
}

function goPage(p) { currentPage = p; renderTable(); window.scrollTo(0,0); }

// ─── Agent View ───────────────────────────────────────────────────────────────
function renderAgentView() {
  const agentMap = {};
  allTickets.forEach(t => {
    const a = t.agent || 'Unassigned';
    if (!agentMap[a]) agentMap[a] = {red:0,yellow:0,green:0,total:0,cats:{}};
    agentMap[a][t.risk_level]++;
    agentMap[a].total++;
    (t.categories||[]).forEach(c => { agentMap[a].cats[c] = (agentMap[a].cats[c]||0)+1; });
  });
  const agents = Object.entries(agentMap).sort((a,b)=>b[1].red-a[1].red||b[1].yellow-a[1].yellow);
  const maxTotal = Math.max(...agents.map(a=>a[1].total), 1);
  document.getElementById('agentCards').innerHTML = agents.map(([name, d]) => {
    const topCat = Object.entries(d.cats).sort((a,b)=>b[1]-a[1])[0];
    return `<div class="agent-card">
      <div class="agent-name">${escHtml(name)}</div>
      <div class="agent-stat"><span class="agent-stat-label">Total Tickets</span><strong>${d.total}</strong></div>
      <div class="agent-bar"><div class="agent-bar-fill" style="width:${Math.round(d.total/maxTotal*100)}%"></div></div>
      <div style="display:flex;gap:12px;margin-top:12px;font-size:13px">
        <span style="color:var(--red)">🔴 ${d.red}</span>
        <span style="color:var(--yellow)">🟡 ${d.yellow}</span>
        <span style="color:var(--green)">🟢 ${d.green}</span>
      </div>
      ${topCat ? `<div style="margin-top:10px;font-size:12px;color:var(--muted)">Top signal: <span class="cat-tag">${escHtml(topCat[0])}</span></div>` : ''}
    </div>`;
  }).join('') || '<div class="empty-state"><h3>No data</h3></div>';
}

// ─── Charts ───────────────────────────────────────────────────────────────────
let timelineChart, riskPie, catBar;

function renderCharts() {
  // Timeline
  const byDate = {};
  allTickets.forEach(t => {
    if (!t.date) return;
    if (!byDate[t.date]) byDate[t.date] = {red:0,yellow:0,green:0};
    byDate[t.date][t.risk_level]++;
  });
  const dates = Object.keys(byDate).sort();
  const chartOpts = {
    responsive:true, interaction:{mode:'index',intersect:false},
    plugins:{legend:{labels:{color:'#94a3b8',font:{size:12}}}},
    scales:{x:{ticks:{color:'#94a3b8',maxRotation:45},grid:{color:'rgba(51,65,85,.5)'}},
            y:{ticks:{color:'#94a3b8'},grid:{color:'rgba(51,65,85,.5)'},beginAtZero:true}}
  };
  if (timelineChart) timelineChart.destroy();
  timelineChart = new Chart(document.getElementById('timelineChart'), {
    type:'line',
    data:{
      labels:dates,
      datasets:[
        {label:'🔴 High Risk',data:dates.map(d=>byDate[d].red),borderColor:'#ef4444',backgroundColor:'rgba(239,68,68,.15)',fill:true,tension:.3},
        {label:'🟡 Medium Risk',data:dates.map(d=>byDate[d].yellow),borderColor:'#f59e0b',backgroundColor:'rgba(245,158,11,.1)',fill:true,tension:.3},
        {label:'🟢 Low Risk',data:dates.map(d=>byDate[d].green),borderColor:'#22c55e',backgroundColor:'rgba(34,197,94,.07)',fill:true,tension:.3},
      ]
    },
    options:chartOpts
  });

  // Risk pie
  const red = allTickets.filter(t=>t.risk_level==='red').length;
  const yellow = allTickets.filter(t=>t.risk_level==='yellow').length;
  const green = allTickets.filter(t=>t.risk_level==='green').length;
  if (riskPie) riskPie.destroy();
  riskPie = new Chart(document.getElementById('riskPieChart'), {
    type:'doughnut',
    data:{
      labels:['🔴 High','🟡 Medium','🟢 Low'],
      datasets:[{data:[red,yellow,green],backgroundColor:['#ef4444','#f59e0b','#22c55e'],borderWidth:0}]
    },
    options:{responsive:true,plugins:{legend:{labels:{color:'#94a3b8'}}}}
  });

  // Category bar
  const catCounts = {};
  allTickets.forEach(t=>(t.categories||[]).forEach(c=>{catCounts[c]=(catCounts[c]||0)+1}));
  const cats = Object.entries(catCounts).sort((a,b)=>b[1]-a[1]).slice(0,7);
  if (catBar) catBar.destroy();
  catBar = new Chart(document.getElementById('catBarChart'), {
    type:'bar',
    data:{
      labels:cats.map(c=>c[0]),
      datasets:[{label:'Tickets',data:cats.map(c=>c[1]),backgroundColor:'rgba(99,102,241,.7)',borderRadius:6}]
    },
    options:{
      indexAxis:'y',responsive:true,
      plugins:{legend:{display:false}},
      scales:{x:{ticks:{color:'#94a3b8'},grid:{color:'rgba(51,65,85,.5)'},beginAtZero:true},
              y:{ticks:{color:'#94a3b8',font:{size:11}},grid:{color:'rgba(51,65,85,.3)'}}}
    }
  });
}

// ─── Tabs ─────────────────────────────────────────────────────────────────────
function switchTab(name) {
  document.querySelectorAll('.tab').forEach(t=>t.classList.remove('active'));
  document.querySelectorAll('.tab-panel').forEach(p=>p.classList.remove('active'));
  event.target.classList.add('active');
  document.getElementById('tab-'+name).classList.add('active');
}

// ─── Refresh ──────────────────────────────────────────────────────────────────
async function triggerRefresh() {
  try {
    const r = await fetch('/api/refresh-now', {method:'POST'});
    const d = await r.json();
    showToast(d.status==='started' ? '🔄 Refresh started — check back in ~2 min' : '⏳ Already running');
    setTimeout(checkRefreshStatus, 5000);
  } catch(e) { showToast('Error: '+e.message, true); }
}

async function checkRefreshStatus() {
  try {
    const r = await fetch('/api/refresh-status');
    const d = await r.json();
    const el = document.getElementById('lastRefresh');
    if (d.running) {
      el.innerHTML = '<span style="color:var(--yellow)">⏳ Refreshing…</span>';
    } else if (d.last_run) {
      el.textContent = new Date(d.last_run).toLocaleString();
      // Reload data if refresh just completed
      if (el.innerHTML.includes('Refreshing') || allTickets.length === 0) loadData();
    }
  } catch(e) {}
}

// ─── Helpers ──────────────────────────────────────────────────────────────────
function escHtml(s) {
  return String(s||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
}
function showToast(msg, isError=false) {
  const t = document.getElementById('toast');
  t.textContent = msg;
  t.style.borderColor = isError ? 'rgba(239,68,68,.4)' : 'rgba(99,102,241,.4)';
  t.classList.add('show');
  setTimeout(()=>t.classList.remove('show'), 3000);
}
</script>
</body>
</html>"""

# ---------------------------------------------------------------------------
# Entry
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False)
