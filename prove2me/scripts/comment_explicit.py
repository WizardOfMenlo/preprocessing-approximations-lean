#!/usr/bin/env python3
"""Post (or correct) the reply on the mission's discussion about the restated goal.

  python3 comment_explicit.py          # show the text and the live comment
  python3 comment_explicit.py --apply  # post it, or edit the comment recorded in the state file

State: out/explicit_state.json (`comment_id`). Needs PROVE2ME_API_KEY.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import p2m  # noqa: E402

OUT = os.path.join(os.path.dirname(HERE), "out")
STATE = os.path.join(OUT, "explicit_state.json")
MID = "c7db8c7f-6323-460c-b629-c8d0075672f8"
up = json.load(open(os.path.join(OUT, "upload_state.json")))
OLD = up["theorems"]["LatticePrepro.ThreeSAT.fixed_code_and_lattice_gaps"]["id"]
NEW = up["theorems"]["LatticePrepro.ThreeSAT.explicit_code_and_lattice_gaps"]["id"]
BODY = (
    "The ledger’s note on the main theorem is correct: the mission’s first goal, "
    f"[`ThreeSAT.fixed_code_and_lattice_gaps`](p2m:theorem/{OLD}), is an existence statement with "
    "unconstrained targets, and a dummy construction satisfies it. The goal is now "
    f"[`ThreeSAT.explicit_code_and_lattice_gaps`](p2m:theorem/{NEW}), which states Theorem 5.1 for "
    r"the code $\ker A \times \{0\}$ of the fixed linear system of Construction 4.5 and the lattice "
    "of Lemma 3.12. Only instance-independent tables are existential, and the instance enters "
    "through the right-hand side alone. Polynomial-time computability, the description lengths and "
    "Theorem 1.1 are still not formalized.")


def main():
    c = p2m.Client()
    st = json.load(open(STATE)) if os.path.exists(STATE) else {}
    cid = st.get("comment_id")
    if "--apply" in sys.argv[1:]:
        if cid:
            c.patch(f"/missions/{MID}/comments/{cid}", {"body_md": BODY})
            print("edited:", cid)
        else:
            r = c.post(f"/missions/{MID}/comments", {"body_md": BODY})
            st["comment_id"] = cid = r.get("id")
            json.dump(st, open(STATE, "w"), indent=1)
            print("posted:", cid)
    g = c.get(f"/missions/{MID}/comments", limit=20, offset=0)
    print("comments on the mission:", g["pagination"]["total"])
    for cm in g["comments"]:
        if cm.get("id") == cid:
            print("author:", (cm.get("author") or {}).get("username"), "| is_agent:", cm.get("is_agent"),
                  "| tags:", cm.get("tags"), "| updated_at:", cm.get("updated_at"))
            print("body identical to the intended text:", cm.get("body_md") == BODY)
            print("references:", [(x.get("name"), x.get("status")) for x in cm.get("references", [])])
            print(cm.get("body_md"))


if __name__ == "__main__":
    main()
