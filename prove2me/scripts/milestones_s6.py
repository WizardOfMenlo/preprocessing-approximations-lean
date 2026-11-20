#!/usr/bin/env python3
"""Publish the Section 6 items and add their milestones to the live mission.

  python3 milestones_s6.py            # report only
  python3 milestones_s6.py --public   # make the Section 6 theorems (and what they depend on) public
  python3 milestones_s6.py --link     # create the milestones of mission/milestones_s6.json

`--public` cannot be undone. `--link` is idempotent (a milestone whose theorem is already linked
is skipped) and its milestones can be edited or deleted later. Both need every Section 6 proof to
be accepted first. State: out/s6_state.json. Needs PROVE2ME_API_KEY.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import p2m  # noqa: E402

P = os.path.dirname(HERE)
OUT = os.path.join(P, "out")
STATE = os.path.join(OUT, "s6_state.json")
up = json.load(open(os.path.join(OUT, "upload_state.json")))
meta = json.load(open(os.path.join(OUT, "meta", "batch_E.json")))
milestones = json.load(open(os.path.join(P, "mission", "milestones_s6.json")))
THMS = [o["theorem_name"] for o in meta if "theorem_name" in o]
DEFS = [o["definition_name"] for o in meta if "definition_name" in o]


def main():
    args = sys.argv[1:]
    for n in THMS:
        if up["theorems"].get(n, {}).get("status") != "PUBLISHED":
            sys.exit(f"{n} is not published")
        if up["solutions"].get(n, {}).get("status") != "ACCEPTED":
            sys.exit(f"the proof of {n} is not accepted")
    for n in DEFS:
        if up["definitions"].get(n, {}).get("status") != "PUBLISHED":
            sys.exit(f"{n} is not published")
    c = p2m.Client()
    st = json.load(open(STATE)) if os.path.exists(STATE) else {"made_public": {}, "milestones": {}}
    pid = json.load(open(os.path.join(OUT, "proposal_state.json")))["proposal_id"]
    mid = c.get(f"/mission-proposals/{pid}").get("mission_id")
    if not mid:
        sys.exit("the proposal has no mission")

    def show():
        for kind, names in (("definitions", DEFS), ("theorems", THMS)):
            for n in names:
                r = c.get(f"/theorems/{up[kind][n]['id']}")
                print(f"  {r.get('visibility'):8} {str(r.get('status')):8} {n}")

    if "--public" in args:
        for n in THMS:
            r = c.post(f"/theorems/{up['theorems'][n]['id']}/make-public", {})
            st["made_public"][n] = r.get("made_public", r)
            json.dump(st, open(STATE, "w"), indent=1)
            print("made public:", n, json.dumps(r)[:300])
    print("visibility and status:")
    show()

    ms = c.get(f"/missions/{mid}/milestones", limit=100, offset=0).get("milestones", [])
    linked = {(m.get("theorem") or {}).get("id"): m for m in ms}
    print(f"mission {mid}: {len(ms)} milestones, {sum(1 for m in ms if m.get('completed'))} completed")
    if "--link" in args:
        for m in milestones:
            tid = up["theorems"][m["theorem_name"]]["id"]
            if tid in linked:
                st["milestones"][m["theorem_name"]] = linked[tid]["id"]
                continue
            r = c.post(f"/missions/{mid}/milestones", {
                "title": m["milestone_title"], "milestone_description": m["milestone_description"],
                "theorem_id": tid})
            st["milestones"][m["theorem_name"]] = r.get("id")
            json.dump(st, open(STATE, "w"), indent=1)
            print("milestone created:", m["milestone_title"], "| completed:", r.get("completed"))
        json.dump(st, open(STATE, "w"), indent=1)
        ms = c.get(f"/missions/{mid}/milestones", limit=100, offset=0).get("milestones", [])
        print(f"mission {mid}: {len(ms)} milestones, {sum(1 for m in ms if m.get('completed'))} completed")
        for m in ms[-len(milestones):]:
            print(f"  {m.get('sort_order')}: {m.get('title')} | {(m.get('theorem') or {}).get('theorem_name')} "
                  f"| completed {m.get('completed')}")


if __name__ == "__main__":
    main()
