#!/usr/bin/env python3
"""Suggest the launched mission to the ACM STOC 2027 collection.

  python3 suggest.py            # report where the proposal stands; suggest once it is a public mission
  python3 suggest.py --check    # report only, never post

A collection accepts only public missions, and the mission exists only after a moderator has
approved the proposal (status `Reviewed`, `mission_id` set). A suggestion can be made once per
collection and its reason cannot be changed afterwards.
State: out/suggestion_state.json. Needs PROVE2ME_API_KEY.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import p2m  # noqa: E402

OUT = os.path.join(os.path.dirname(HERE), "out")
STATE = os.path.join(OUT, "suggestion_state.json")
SLUG = "acm-stoc-2027"
REASON = ("Lean 4 formalization of STOC 2027 submission #847, \"Nearly Optimal Hardness for CVP and "
          "NCP with Preprocessing\": Theorem 5.1 (fixed codes with gap M^(1-eps) and fixed lattices "
          "with gap M^(1/s-eps) in every l_p norm, for 3SAT). The goal and all 22 milestones are "
          "proved.")


def main():
    check_only = "--check" in sys.argv[1:]
    c = p2m.Client()
    pid = json.load(open(os.path.join(OUT, "proposal_state.json")))["proposal_id"]
    r = c.get(f"/mission-proposals/{pid}")
    mid = r.get("mission_id")
    print(f"proposal: status {r.get('status')}, visibility {r.get('visibility')}, mission_id {mid}")
    for rv in r.get("reviews") or []:
        print(f"review ({rv.get('decision')}, {rv.get('created_at')}): {(rv.get('report') or '')[:1500]}")
    for it in r.get("items", []):
        for f in it.get("flags") or []:
            print(f"flag on {it.get('theorem_name')}: {f.get('comment')}")
    if not mid or r.get("status") != "Reviewed":
        print("not a public mission yet; nothing suggested")
        return 2
    # There is no GET /missions/<id> (405); the public catalog is the check that it is public.
    cat = c.get("/missions", q=r.get("name"), visibility="public").get("missions", [])
    if not any(m.get("id") == mid and m.get("visibility") == "public" for m in cat):
        print("mission is not in the public catalog; nothing suggested")
        return 2
    mine = c.get(f"/collections/{SLUG}/suggestions", limit=100, offset=0)
    print("existing suggestions:", json.dumps(mine)[:600])
    if check_only:
        return 0
    s = c.post(f"/collections/{SLUG}/suggestions", {"mission_id": mid, "reason": REASON})
    json.dump({"collection": SLUG, "mission_id": mid, "suggestion": s}, open(STATE, "w"), indent=1)
    print("suggested:", json.dumps(s))
    return 0


if __name__ == "__main__":
    sys.exit(main())
