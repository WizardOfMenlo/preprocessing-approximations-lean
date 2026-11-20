#!/bin/bash
# Build the generated tree and check it against the original library:
#  1. Definitions, Theorems and Solutions build on Lean 4.33.1 / Mathlib 0df444a;
#  2. every stub's statement is the original theorem's statement (raw elaborated types, up to the
#     module-dependent hygienic names of anonymous binders);
#  3. every `solution` has exactly the type of its stub (alpha-equivalence);
#  4. no solution contains `sorry` or imports its own stub, and each has one `theorem solution`.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$HERE/../workspace"
lake build Definitions Theorems Solutions 2>&1 | grep -E '^(error|✖)' -A4 | head -40
lake build Definitions Theorems Solutions >/dev/null 2>&1 || { echo "BUILD FAILED"; exit 1; }
echo "build: ok"
python3 "$HERE/mkcheck.py"
lake env lean ../out/check/TypesOrig.lean >/dev/null && lake env lean ../out/check/TypesStub.lean >/dev/null || { echo "type extraction failed"; exit 1; }
python3 - <<'PY'
import json, re, sys
norm = lambda t: re.sub(r"_@\.(?:[A-Za-z_][A-Za-z0-9_']*\.)+\d+\._hygCtx", "_@.M._hygCtx", t)
o = {json.loads(l)["name"]: json.loads(l) for l in open("../out/check/types_orig.jsonl") if l.strip()}
s = {json.loads(l)["name"]: json.loads(l) for l in open("../out/check/types_stub.jsonl") if l.strip()}
bad = [n for n in o if (norm(o[n]["type"]), o[n]["lps"]) != (norm(s[n]["type"]), s[n]["lps"])]
print(f"statements: {len(o)} compared, {len(bad)} differ {bad}")
sys.exit(1 if bad else 0)
PY
find ../out/check -name 'Sol_*.lean' | sort | xargs -P 6 -n 1 lake env lean 2>&1 | grep -oE '^OK|MISMATCH.*|error.*' | sort | uniq -c
python3 - <<'PY'
import glob, os, re
bad = []
for f in glob.glob("Solutions/Sol_*.lean"):
    t = open(f).read(); slug = os.path.basename(f)[4:-5]
    if re.search(r"\bsorry\b", t): bad.append(("sorry", f))
    if re.search(rf"^import Theorems\.Thm_{re.escape(slug)}$", t, re.M): bad.append(("self-import", f))
    if len(re.findall(r"^theorem solution\b", t, re.M)) != 1: bad.append(("solution count", f))
print("gating rules:", "ok" if not bad else bad)
PY
