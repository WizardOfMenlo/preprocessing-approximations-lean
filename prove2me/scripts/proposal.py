#!/usr/bin/env python3
"""Create (or update) the private mission proposal on top of the uploaded tree.

  python3 proposal.py           # create the proposal once, then sync items, order and milestones

The proposal holds reference items only (everything is already published privately): the
definition bundles the goal's statement is read against, the milestone theorems and the goal.
Only the human can confirm the items and click **Submit Proposal** on the website.
State: out/proposal_state.json. Needs PROVE2ME_API_KEY.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import p2m  # noqa: E402

P = os.path.dirname(HERE)
OUT = os.path.join(P, "out")
STATE = os.path.join(OUT, "proposal_state.json")
up = json.load(open(os.path.join(OUT, "upload_state.json")))
milestones = json.load(open(os.path.join(P, "mission", "milestones.json")))
description = open(os.path.join(P, "mission", "description.md")).read()
if "{{" in description:
    sys.exit("description.md still has a placeholder")

NAME = "Nearly Optimal Hardness for CVP and NCP with Preprocessing"
GOAL = "LatticePrepro.ThreeSAT.fixed_code_and_lattice_gaps"
FIELDS = ["3d5dcffe-9f61-4780-a1ac-4495e16c3fa5",   # Complexity Theory
          "105f8c80-f763-4beb-822c-d9265917c2b1"]   # Theoretical Computer Science
DEFS = ["LatticePrepro_Conversions_Codes", "LatticePrepro_Conversions_Lattices",
        "LatticePrepro_Lattices_Distance", "LatticePrepro_Verifier_ThreeSAT",
        "LatticePrepro_Main", "LatticePrepro_ThreeSAT"]


def tid(kind, name):
    rec = up[kind].get(name, {})
    if rec.get("status") != "PUBLISHED" or not rec.get("id"):
        sys.exit(f"{name} is not published")
    return rec["id"]


def main():
    c = p2m.Client()
    st = json.load(open(STATE)) if os.path.exists(STATE) else {}
    if "proposal_id" not in st:
        r = c.post("/mission-proposals", {"name": NAME, "description": description,
                                          "mission_type": "ResearchPaper", "field_ids": FIELDS,
                                          "env": up["env"], "visibility": "private"})
        st = {"proposal_id": r["id"], "items": {}}
        json.dump(st, open(STATE, "w"), indent=1)
        print("proposal created:", r["id"], r.get("status"))
    pid = st["proposal_id"]
    c.patch(f"/mission-proposals/{pid}", {"description": description, "field_ids": FIELDS})
    wanted = ([("definitions", d) for d in DEFS] +
              [("theorems", m["theorem_name"]) for m in milestones] + [("theorems", GOAL)])
    for kind, name in wanted:
        if name in st["items"]:
            continue
        r = c.post(f"/mission-proposals/{pid}/items", {"kind": "reference", "theorem_id": tid(kind, name)})
        st["items"][name] = r["id"]
        json.dump(st, open(STATE, "w"), indent=1)
        print("item added:", name)
    order = [st["items"][name] for _, name in wanted]
    c.patch(f"/mission-proposals/{pid}", {"main_item_id": st["items"][GOAL], "item_order": order})
    st.setdefault("milestones", {})
    for m in milestones:
        if m["theorem_name"] in st["milestones"]:
            continue
        r = c.post(f"/mission-proposals/{pid}/milestones", {
            "item_id": st["items"][m["theorem_name"]], "milestone_title": m["milestone_title"],
            "milestone_description": m["milestone_description"]})
        st["milestones"][m["theorem_name"]] = r.get("id") or True
        json.dump(st, open(STATE, "w"), indent=1)
        print("milestone set:", m["milestone_title"])
    r = c.get(f"/mission-proposals/{pid}")
    ms = c.get(f"/mission-proposals/{pid}/milestones")
    n_ms = len(ms.get("milestones", ms if isinstance(ms, list) else []))
    print(f"proposal {pid}: status {r.get('status')}, {len(r.get('items', []))} items, "
          f"{n_ms} milestones, visibility {r.get('visibility')}")


if __name__ == "__main__":
    main()
