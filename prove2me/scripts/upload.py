#!/usr/bin/env python3
"""Idempotent, resumable uploader for the generated Prove2Me tree (private uploads).

  python3 upload.py status            # what is recorded, nothing sent
  python3 upload.py preflight         # name checks against the platform, nothing created
  python3 upload.py definitions       # publish the definition bundles, in import order
  python3 upload.py theorems          # publish the theorem stubs
  python3 upload.py solutions         # verify the solutions, dependencies first

Every action is recorded in out/upload_state.json before and after its API call, so an interrupted
run resumes without duplicates. Each uploaded file's sha256 is recorded; a file that changed after
it was published stops the run instead of being silently re-sent.
Needs PROVE2ME_API_KEY in the environment (see p2m.py).
"""
import hashlib
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import p2m  # noqa: E402

P = os.path.dirname(HERE)
WS = os.path.join(P, "workspace")
OUT = os.path.join(P, "out")
STATE = os.path.join(OUT, "upload_state.json")
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
PRIVATE = True
TAGS = ["cvp-ncp-preprocessing", "lattices", "coding-theory", "hardness-of-approximation",
        "preprocessing"]

plan = json.load(open(os.path.join(OUT, "plan.json")))

# Definition bundles held back (with everything that imports them), e.g. while their content is
# still being decided: P2M_HOLD=LatticePrepro_Main
HOLD_ROOTS = {h for h in os.environ.get("P2M_HOLD", "").split(",") if h}
HELD_DEFS = set()
for _d in plan["definitions"]:  # topological order
    if _d["definition_name"] in HOLD_ROOTS or any(i in HELD_DEFS for i in _d["imports"]):
        HELD_DEFS.add(_d["definition_name"])


def _imports_held(text):
    return any(f"import Definitions.Def_{h}\n" in text + "\n" for h in HELD_DEFS)


HELD_THMS = {n["theorem_name"] for n in plan["nodes"] if _imports_held(n["preamble"])}
_changed = True
HELD_SOLS = set(HELD_THMS)
while _changed:
    _changed = False
    for _n in plan["nodes"]:
        if _n["theorem_name"] in HELD_SOLS:
            continue
        if (any(d in HELD_SOLS or d in HELD_THMS for d in _n["node_deps"])
                or any(i in HELD_DEFS for i in _n["definition_imports"])):
            HELD_SOLS.add(_n["theorem_name"])
            _changed = True
META = {}
for f in sorted(os.listdir(os.path.join(OUT, "meta"))):
    if f.startswith("batch_") and f.endswith(".json") and not f.endswith("_items.json"):
        for o in json.load(open(os.path.join(OUT, "meta", f))):
            META[o.get("theorem_name") or o.get("definition_name")] = o


def load_state():
    if os.path.exists(STATE):
        return json.load(open(STATE))
    return {"env": ENV, "definitions": {}, "theorems": {}, "solutions": {}}


def save_state(st):
    tmp = STATE + ".tmp"
    json.dump(st, open(tmp, "w"), indent=1)
    os.replace(tmp, STATE)


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def def_text(d):
    return open(os.path.join(WS, "Definitions", f"Def_{d['definition_name']}.lean")).read()


def sol_text(n):
    return open(os.path.join(WS, "Solutions", f"Sol_{n['slug']}.lean")).read()


def def_waves():
    level = {}
    for d in plan["definitions"]:  # plan order is topological
        level[d["definition_name"]] = 1 + max([level[i] for i in d["imports"]], default=-1)
    waves = {}
    for d in plan["definitions"]:
        waves.setdefault(level[d["definition_name"]], []).append(d)
    return [waves[k] for k in sorted(waves)]


def node_waves():
    by_name = {n["theorem_name"]: n for n in plan["nodes"]}
    level = {}

    def lv(name):
        if name not in level:
            level[name] = 1 + max([lv(d) for d in by_name[name]["node_deps"]], default=-1)
        return level[name]
    waves = {}
    for n in plan["nodes"]:
        waves.setdefault(lv(n["theorem_name"]), []).append(n)
    return [waves[k] for k in sorted(waves)]


def find_exact(c, kind, name):
    """Published items with exactly this name in our environment (the search is fuzzy)."""
    path, key = ("/definitions", "definition_name") if kind == "definition" else ("/theorems", "theorem_name")
    q = name.split(".")[-1] if kind == "theorem" else name
    hits = []
    for view in ("compact",):
        r = c.get(path, q=q, view=view, env=ENV, limit=100)
        items = r.get("definitions" if kind == "definition" else "theorems", r.get("items", []))
        hits += [i for i in items if i.get(key) == name]
    return hits


def poll_job(c, job_id, every=8, timeout=1800):
    t0 = time.time()
    while True:
        j = c.get(f"/publish-jobs/{job_id}")
        if j.get("status") in ("PUBLISHED", "FAILED", "ERROR"):
            return j
        if time.time() - t0 > timeout:
            return j
        time.sleep(every)


def poll_submission(c, sid, every=10, timeout=2400):
    t0 = time.time()
    while True:
        r = c.get("/verify", submission_id=sid)
        s = r.get("status")
        # SKETCH_ACCEPTED is an intermediate state (statement and sketch checked, full check
        # still running); keep polling until a final verdict.
        if s in ("ACCEPTED", "FAILED", "ERROR", "REJECTED"):
            return r
        if time.time() - t0 > timeout:
            return r
        time.sleep(every)


def item_id(j):
    return j.get("theorem_id") or j.get("definition_id") or j.get("id")


# --------------------------------------------------------------------------- commands

def cmd_status(st):
    for kind in ("definitions", "theorems", "solutions"):
        recs = st[kind]
        counts = {}
        for r in recs.values():
            counts[r.get("status")] = counts.get(r.get("status"), 0) + 1
        log(f"{kind}: {len(recs)} recorded {counts}")
        for name, r in recs.items():
            if r.get("status") not in ("PUBLISHED", "ACCEPTED"):
                log(f"   {name}: {r.get('status')} {r.get('error', '')[:300]}")


def cmd_preflight(c, st):
    clashes = []
    for d in plan["definitions"]:
        name = d["definition_name"]
        if name in st["definitions"] or name in HELD_DEFS:
            continue
        if find_exact(c, "definition", name):
            clashes.append(("definition", name))
    for n in plan["nodes"]:
        name = n["theorem_name"]
        if name in st["theorems"] or name in HELD_THMS:
            continue
        if find_exact(c, "theorem", name):
            clashes.append(("theorem", name))
    missing = [x for x in [d["definition_name"] for d in plan["definitions"]] +
               [n["theorem_name"] for n in plan["nodes"]] if x not in META]
    log(f"preflight: {len(plan['definitions'])} definitions, {len(plan['nodes'])} theorems, "
        f"name clashes: {clashes or 'none'}, missing metadata: {missing or 'none'}")
    return not clashes and not missing


def cmd_definitions(c, st):
    for wave in def_waves():
        pending = []
        for d in wave:
            name = d["definition_name"]
            if name in HELD_DEFS:
                continue
            text = def_text(d)
            rec = st["definitions"].get(name)
            if rec and rec.get("status") == "PUBLISHED":
                if rec["sha256"] != sha(text):
                    sys.exit(f"{name} changed after it was published; refusing to continue")
                continue
            if rec and rec.get("job_id") and rec.get("status") in ("PENDING", "COMPILING", "SUBMITTED"):
                pending.append(name)
                continue
            for imp in d["imports"]:
                if st["definitions"].get(imp, {}).get("status") != "PUBLISHED":
                    sys.exit(f"{name}: import {imp} is not published")
            m = META[name]
            body = {"definition_name": name, "definition_title": m["definition_title"],
                    "definition": text, "natural_language_statement": m["natural_language_statement"],
                    "source": m["source"], "tags": TAGS, "env": ENV, "private": PRIVATE}
            st["definitions"][name] = {"status": "SUBMITTING", "sha256": sha(text)}
            save_state(st)
            r = c.post("/submit-definition", body)
            if not r.get("job_id"):
                st["definitions"][name].update(status="REJECTED", error=json.dumps(r)[:2000])
                save_state(st)
                sys.exit(f"{name}: rejected before queueing: {json.dumps(r)[:800]}")
            st["definitions"][name].update(status="SUBMITTED", job_id=r["job_id"])
            save_state(st)
            log(f"definition queued: {name}")
            pending.append(name)
        for name in pending:
            j = poll_job(c, st["definitions"][name]["job_id"])
            st["definitions"][name].update(status=j.get("status"), id=item_id(j),
                                           error=j.get("error_message", ""))
            save_state(st)
            log(f"definition {j.get('status')}: {name} {j.get('error_message', '')[:600]}")
        bad = [n for n in pending if st["definitions"][n]["status"] != "PUBLISHED"]
        if bad:
            sys.exit(f"stopping: {bad} did not publish")


def cmd_theorems(c, st):
    if any(st["definitions"].get(d["definition_name"], {}).get("status") != "PUBLISHED"
           for d in plan["definitions"] if d["definition_name"] not in HELD_DEFS):
        sys.exit("publish the definitions first")
    todo = []
    for n in plan["nodes"]:
        name = n["theorem_name"]
        if name in HELD_THMS:
            continue
        rec = st["theorems"].get(name)
        stmt = n["preamble"] + "\n\n" + n["formal_statement"]
        if rec and rec.get("status") == "PUBLISHED":
            if rec["sha256"] != sha(stmt):
                sys.exit(f"{name} changed after it was published; refusing to continue")
            continue
        if rec and rec.get("job_id") and rec.get("status") in ("PENDING", "COMPILING", "SUBMITTED"):
            continue
        todo.append(n)
    if todo:
        problems = []
        for n in todo:
            m = META[n["theorem_name"]]
            problems.append({"theorem_name": n["theorem_name"], "theorem_title": m["theorem_title"],
                             "formal_statement": n["formal_statement"],
                             "natural_language_statement": m["natural_language_statement"],
                             "preamble": n["preamble"], "source": m["source"], "tags": TAGS})
            st["theorems"][n["theorem_name"]] = {
                "status": "SUBMITTING", "sha256": sha(n["preamble"] + "\n\n" + n["formal_statement"])}
        save_state(st)
        r = c.post("/submit-problem", {"problems": problems, "env": ENV, "private": PRIVATE})
        for j in r.get("jobs", []):
            st["theorems"][j["name"]].update(status="SUBMITTED", job_id=j["job_id"])
        for e in r.get("errors", []):
            nm = e.get("name") or e.get("theorem_name")
            if nm in st["theorems"]:
                st["theorems"][nm].update(status="REJECTED", error=json.dumps(e)[:2000])
        save_state(st)
        log(f"theorems queued: {len(r.get('jobs', []))}, rejected before queueing: {len(r.get('errors', []))}")
    for name, rec in st["theorems"].items():
        if rec.get("status") in ("SUBMITTED", "PENDING", "COMPILING"):
            j = poll_job(c, rec["job_id"])
            rec.update(status=j.get("status"), id=item_id(j), error=j.get("error_message", ""))
            save_state(st)
            log(f"theorem {j.get('status')}: {name} {j.get('error_message', '')[:600]}")
    bad = [k for k, v in st["theorems"].items() if v.get("status") != "PUBLISHED"]
    if bad:
        sys.exit(f"stopping: {bad} did not publish")


def explanation(n):
    parts = [f"Proof taken from the Lean formalization accompanying the paper "
             f"(`{n['module'].replace('.', '/')}.lean`, lines {n['source_lines'][0]}–{n['source_lines'][1]}), "
             f"ported to Lean v4.33.1."]
    if n["node_deps"]:
        parts.append("It uses the platform theorems " + ", ".join(f"`{d}`" for d in n["node_deps"]) + ".")
    if n["inlined"]:
        parts.append(f"{len(n['inlined'])} helper declarations of the formalization are included in the file.")
    return " ".join(parts)


def cmd_solutions(c, st):
    if any(st["theorems"].get(n["theorem_name"], {}).get("status") != "PUBLISHED" for n in plan["nodes"]
           if n["theorem_name"] not in HELD_THMS):
        sys.exit("publish the theorems first")
    for wave in node_waves():
        pending = []
        for n in wave:
            name = n["theorem_name"]
            if name in HELD_SOLS:
                continue
            text = sol_text(n)
            rec = st["solutions"].get(name)
            if rec and rec.get("status") == "ACCEPTED":
                continue
            if rec and rec.get("submission_id") and rec.get("status") in ("SUBMITTED", "PENDING", "RUNNING",
                                                                 "SKETCH_ACCEPTED"):
                pending.append(name)
                continue
            for dep in n["node_deps"]:
                if st["solutions"].get(dep, {}).get("status") != "ACCEPTED":
                    sys.exit(f"{name}: dependency {dep} is not proved yet")
            st["solutions"][name] = {"status": "SUBMITTING", "sha256": sha(text)}
            save_state(st)
            r = c.verify(st["theorems"][name]["id"], text, explanation(n))
            sid = r.get("submission_id") or r.get("id")
            if not sid:
                st["solutions"][name].update(status="REJECTED", error=json.dumps(r)[:2000])
                save_state(st)
                sys.exit(f"{name}: no submission id: {json.dumps(r)[:800]}")
            st["solutions"][name].update(status="SUBMITTED", submission_id=sid)
            save_state(st)
            log(f"solution submitted: {name}")
            pending.append(name)
        for name in pending:
            r = poll_submission(c, st["solutions"][name]["submission_id"])
            err = r.get("error_message") or r.get("message") or r.get("feedback") or ""
            st["solutions"][name].update(status=r.get("status"), error=str(err)[:4000])
            save_state(st)
            log(f"solution {r.get('status')}: {name} {str(err)[:600]}")
        bad = [x for x in pending if st["solutions"][x]["status"] != "ACCEPTED"]
        if bad:
            sys.exit(f"stopping: {bad} were not accepted")


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else "status"
    st = load_state()
    if st.get("env") != ENV:
        sys.exit("state file is for another environment")
    if HOLD_ROOTS:
        log(f"holding back {len(HELD_DEFS)} definitions, {len(HELD_THMS)} theorem stubs, "
            f"{len(HELD_SOLS)} solutions: {sorted(HELD_DEFS)}")
    if what == "status":
        cmd_status(st)
        return
    c = p2m.Client()
    c._refresh()
    if c.version != p2m.SKILL_VERSION:
        log(f"warning: platform version {c.version} differs from the skill copy {p2m.SKILL_VERSION}")
    if what == "preflight":
        sys.exit(0 if cmd_preflight(c, st) else 1)
    elif what == "definitions":
        cmd_definitions(c, st)
    elif what == "theorems":
        cmd_theorems(c, st)
    elif what == "solutions":
        cmd_solutions(c, st)
    else:
        sys.exit(f"unknown command {what}")
    cmd_status(st)


if __name__ == "__main__":
    main()
