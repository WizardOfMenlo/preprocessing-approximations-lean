"""Write the Lean files used by check.sh (type extraction and per-solution checks)."""
import json, os
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(HERE), "out")
plan = json.load(open(os.path.join(OUT, "plan.json")))
names = [n["theorem_name"] for n in plan["nodes"]]
os.makedirs(os.path.join(OUT, "check"), exist_ok=True)
for f in os.listdir(os.path.join(OUT, "check")):
    if f.startswith("Sol_"):
        os.remove(os.path.join(OUT, "check", f))
lst = "[" + ", ".join(f"`{n}" for n in names) + "]"
body = '''
open Lean Meta
run_meta do
  let names : List Name := %s
  let mut out : Array String := #[]
  for n in names do
    let ci ← getConstInfo n
    out := out.push (Json.mkObj [("name", Json.str (toString n)),
      ("lps", Json.str (toString ci.levelParams)), ("type", Json.str (toString ci.type))]).compress
  IO.FS.writeFile "%s" (String.intercalate "\\n" out.toList ++ "\\n")
'''
open(os.path.join(OUT, "check/TypesOrig.lean"), "w").write(
    "import LatticePrepro\n" + body % (lst, "../out/check/types_orig.jsonl"))
open(os.path.join(OUT, "check/TypesStub.lean"), "w").write(
    "".join(f"import Theorems.Thm_{n['slug']}\n" for n in plan["nodes"]) + body % (lst, "../out/check/types_stub.jsonl"))
for n in plan["nodes"]:
    open(os.path.join(OUT, f"check/Sol_{n['slug']}.lean"), "w").write(f'''import Theorems.Thm_{n['slug']}
import Solutions.Sol_{n['slug']}
open Lean Meta
run_meta do
  let a ← getConstInfo `solution
  let b ← getConstInfo `{n['theorem_name']}
  let ta := a.type.instantiateLevelParams a.levelParams (b.levelParams.map Level.param)
  unless a.levelParams.length == b.levelParams.length && ta == b.type do
    throwError "MISMATCH {n['theorem_name']}"
  logInfo "OK {n['theorem_name']}"
''')
