#!/usr/bin/env python3
"""Make the explicit-construction items public and move the mission onto them.

  python3 publish_explicit.py                # report only
  python3 publish_explicit.py --public       # make the new theorems (and what they need) public
  python3 publish_explicit.py --goal         # retarget the mission's goal
  python3 publish_explicit.py --link         # add the milestones of mission/milestones_explicit.json
                                             # and keep the old goal as a milestone
  python3 publish_explicit.py --notes        # add a note to the existence-form statements
  python3 publish_explicit.py --description  # update the mission description

`--public` cannot be undone. The other steps can be reverted with the same endpoints. All of them
need every proof of batch F to be accepted. State: out/explicit_state.json. Needs PROVE2ME_API_KEY.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import p2m  # noqa: E402

P = os.path.dirname(HERE)
OUT = os.path.join(P, "out")
STATE = os.path.join(OUT, "explicit_state.json")
up = json.load(open(os.path.join(OUT, "upload_state.json")))
meta = json.load(open(os.path.join(OUT, "meta", "batch_F.json")))
milestones = json.load(open(os.path.join(P, "mission", "milestones_explicit.json")))
THMS = [o["theorem_name"] for o in meta if "theorem_name" in o]
DEFS = [o["definition_name"] for o in meta if "definition_name" in o]
LP = "LatticePrepro."
NEW_GOAL = LP + "ThreeSAT.explicit_code_and_lattice_gaps"
OLD_GOAL = LP + "ThreeSAT.fixed_code_and_lattice_gaps"

DUMMY = ("The Lean statement does not require the targets to be computable, so this form is also "
         "satisfied by a construction unrelated to the paper, in which the target records whether "
         "the instance is in the language.")
# existence-form statements -> the statement for the paper's construction, and whether the remark
# about dummy constructions applies (it has been checked for `CodeGap`; `LatticeGap` has the same
# shape)
NOTES = {
    LP + "code_gap": (LP + "QuadraticVerifier.Tables.codeFamily_hasGap", "some code with targets has the gap", True),
    LP + "lattice_gap": (LP + "QuadraticVerifier.Tables.latticeFamily_hasGap", "some lattice with targets has the gap", True),
    LP + "exists_code_gap": (LP + "QuadraticVerifier.Tables.codeFamily_hasGap", "some code with targets has the gap", True),
    LP + "exists_lattice_gap": (LP + "QuadraticVerifier.Tables.latticeFamily_hasGap", "some lattice with targets has the gap", True),
    LP + "ThreeSAT.exists_code_gap": (LP + "ThreeSAT.explicit_code_gap", "some code with targets has the gap", True),
    LP + "ThreeSAT.exists_lattice_gap": (LP + "ThreeSAT.explicit_lattice_gap", "some lattice with targets has the gap", True),
    OLD_GOAL: (NEW_GOAL, "some code and some lattice with targets have the gap", True),
    LP + "exists_gapReduction": (LP + "QuadraticVerifier.Tables.system_spec", "some linear system family has these properties", False),
    LP + "exists_latticeReduction": (LP + "LinearSystemFamily.exists_latticeReduction_eq", "some lattice reduction exists", False),
}
MARK = "**Note (existence form).**"


def note(name):
    target, what, dummy = NOTES[name]
    return (f"\n\n{MARK} This statement asserts only that {what}. " + (DUMMY + " " if dummy else "")
            + f"The statement for the object that the paper constructs is `{target}`.")


MS_NOTE = (" This milestone is the existence form: it does not name the code or lattice, and since "
           "the Lean statement does not require the targets to be computable it is also satisfied "
           "by a construction unrelated to the paper. The milestone for the paper's construction is "
           "\"{}\".")
MS_PAIRS = {  # existence-form milestone theorem -> title of the explicit milestone
    LP + "code_gap": "Theorem 5.1 (codes) — the paper's code for any quadratic verifier",
    LP + "lattice_gap": "Theorem 5.1 (lattices) — the paper's lattice for any quadratic verifier",
    LP + "ThreeSAT.exists_code_gap": "Theorem 5.1 (codes, 3SAT) — the paper's code with $M\\le n^{C}$",
    LP + "ThreeSAT.exists_lattice_gap": "Theorem 5.1 (lattices, 3SAT) — the paper's lattice with $M\\le n^{C}$",
}
OLD_GOAL_MS = {
    "title": "Theorem 5.1 (3SAT, existence form) — both parts",
    "milestone_description": (
        "Theorem 5.1 for 3SAT in existence form: for every finite field $F$ and every "
        "$0<\\varepsilon<1$ there are fixed codes with gap $M^{1-\\varepsilon}$, and for every norm "
        "exponent $1\\le p\\le\\infty$ and every $0<\\varepsilon<1/s$, $s=\\min\\{p,2\\}$, there are "
        "fixed full-rank lattices with gap $M^{1/s-\\varepsilon}$, with $M\\le n^{C}$. This was the "
        "mission's first goal. It does not name the code or lattice, and since the Lean statement "
        "does not require the targets to be computable it is also satisfied by a construction "
        "unrelated to the paper; the goal is now the statement for the paper's construction."),
}


def new_description(s):
    def rep(old, new):
        nonlocal s
        if new in s:
            return
        assert s.count(old) == 1, (old[:60], s.count(old))
        s = s.replace(old, new)
    lat = (r"$$x \in \mathrm{SAT}_v \implies \operatorname{dist}_p(t_x, \Lambda_v) \le R, \qquad "
           r"x \notin \mathrm{SAT}_v \implies \operatorname{dist}_p(t_x, \Lambda_v) > M^{1/s-\varepsilon} \cdot R.$$")
    rep(lat + "\n", lat + "\n\n"
        r"In the goal, $\mathcal C_v$, $\Lambda_v$, $t_x$ and $R$ are the objects that the paper "
        r"constructs, not arbitrary ones. $\mathcal C_v$ is the code $\ker A \times \{0\}$ of the "
        r"fixed linear system $A v = b_x$ of Construction 4.5 for the 3SAT verifier, extended to "
        r"$\mathbb F$, and $t_x$ is the target of Lemma 3.11. $\Lambda_v$, its targets and its "
        r"radius are those of Lemma 3.12 for the same system. The instance enters only through "
        r"the right-hand side $b_x$." "\n")
    rep("and Theorem 5.1 for an arbitrary quadratic verifier, from which the 3SAT form follows.\n",
        "and Theorem 5.1 for an arbitrary quadratic verifier, from which the 3SAT form follows.\n\n"
        "Each step that the paper proves by a construction has a milestone for the object it "
        "constructs: Theorem 4.8 for the fixed linear system of Construction 4.5, Lemma 3.12 for "
        "the Construction A lattice and its Walsh–Hadamard transform, and Theorem 5.1 for the "
        "resulting code and lattice. The milestones marked \"existence form\" assert only that "
        "some object with the stated properties exists.\n")
    rep("- **Existence** is stated as `Nonempty` of a structure (`CodeGap`, `LatticeGap`) that "
        "bundles the code or lattice, the targets, the radius and the bounds. The constant $C$ is "
        "existential in the goal; the milestones give it explicitly as `sizeExp`.\n",
        "- **The goal names the construction.** The code is `Tables.codeFamily` and the lattice is "
        "`Tables.latticeFamily`, both defined from the fixed linear system of Construction 4.5. "
        "What is asserted to exist is the *tables*: a base and an explicit moment representation "
        "(Theorem A.8), which do not depend on the instance. The constant $C$ is existential in "
        "the goal; the milestones give it explicitly as `sizeExp`.\n"
        "- **Existence form.** Theorem 5.1 is also stated as `Nonempty` of a structure (`CodeGap`, "
        "`LatticeGap`) that bundles some code or lattice with targets, a radius and the bounds. "
        "This was the mission's first goal. Since the targets are not required to be computable, "
        "this form is also satisfied by a construction unrelated to the paper, in which the "
        "target records whether the instance is satisfiable. It is kept as milestones for "
        "reference; the statements to rely on are the ones for the paper's construction.\n")
    return s


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
    st = json.load(open(STATE)) if os.path.exists(STATE) else {}
    for k in ("made_public", "milestones", "notes", "ms_notes"):
        st.setdefault(k, {})

    def save():
        json.dump(st, open(STATE, "w"), indent=1)

    pid = json.load(open(os.path.join(OUT, "proposal_state.json")))["proposal_id"]
    mid = c.get(f"/mission-proposals/{pid}").get("mission_id")
    if not mid:
        sys.exit("the proposal has no mission")
    tid = lambda n: up["theorems"][n]["id"]

    if "--public" in args:
        for n in THMS:
            r = c.post(f"/theorems/{tid(n)}/make-public", {})
            st["made_public"][n] = r.get("made_public", r)
            save()
            print("made public:", n, "| newly public:", len(r.get("made_public", [])))
    vis = {}
    for kind, names in (("definitions", DEFS), ("theorems", THMS)):
        for n in names:
            r = c.get(f"/theorems/{up[kind][n]['id']}")
            vis[n] = (r.get("visibility"), r.get("status"))
    print("new items:", {v: sum(1 for x in vis.values() if x == v) for v in set(vis.values())})

    if "--goal" in args:
        if any(v[0] != "public" for v in vis.values()):
            sys.exit("make the new items public first")
        r = c.patch(f"/missions/{mid}", {"main_statement": tid(NEW_GOAL)})
        st["goal"] = tid(NEW_GOAL)
        save()
        print("goal retargeted:", json.dumps((r.get("main_theorem") or r).get("theorem_name")))

    ms = c.get(f"/missions/{mid}/milestones", limit=100, offset=0).get("milestones", [])
    by_thm = {(m.get("theorem") or {}).get("id"): m for m in ms}
    if "--link" in args:
        todo = [(m["theorem_name"], m["milestone_title"], m["milestone_description"]) for m in milestones]
        todo.append((OLD_GOAL, OLD_GOAL_MS["title"], OLD_GOAL_MS["milestone_description"]))
        for name, title, desc in todo:
            if tid(name) in by_thm:
                st["milestones"][name] = by_thm[tid(name)]["id"]
                continue
            r = c.post(f"/missions/{mid}/milestones", {"title": title, "milestone_description": desc,
                                                       "theorem_id": tid(name)})
            st["milestones"][name] = r.get("id")
            save()
            print("milestone created:", title, "| completed:", r.get("completed"))
        save()
        ms = c.get(f"/missions/{mid}/milestones", limit=100, offset=0).get("milestones", [])
        by_thm = {(m.get("theorem") or {}).get("id"): m for m in ms}

    if "--notes" in args:
        for name in NOTES:
            r = c.get(f"/theorems/{tid(name)}")
            cur = r.get("natural_language_statement") or ""
            if MARK in cur:
                continue
            c.patch(f"/theorems/{tid(name)}", {"natural_language_statement": cur + note(name),
                                               "reason": "Point to the statement for the paper's construction"})
            st["notes"][name] = True
            save()
            print("note added:", name)
        for name, explicit_title in MS_PAIRS.items():
            m = by_thm.get(tid(name))
            if not m or "existence form" in (m.get("milestone_description") or ""):
                continue
            c.patch(f"/milestones/{m['id']}", {
                "milestone_description": m["milestone_description"] + MS_NOTE.format(explicit_title),
                "reason": "Mark the existence form and point to the milestone for the paper's construction"})
            st["ms_notes"][name] = m["id"]
            save()
            print("milestone note added:", m.get("title"))

    if "--description" in args:
        path = os.path.join(P, "mission", "description.md")
        new = new_description(open(path).read())
        c.patch(f"/missions/{mid}", {"description": new})
        open(path, "w").write(new)
        st["description"] = True
        save()
        print("description updated:", len(new), "characters")

    g = [m for m in c.get("/missions", q="Nearly Optimal Hardness for CVP and NCP with Preprocessing",
                          visibility="public")["missions"] if m["id"] == mid]
    goal = (g[0].get("main_theorem") or {}) if g else {}
    print(f"mission goal: {goal.get('theorem_name')} ({goal.get('status')})")
    print(f"milestones: {len(ms)}, completed {sum(1 for m in ms if m.get('completed'))}")


if __name__ == "__main__":
    main()
