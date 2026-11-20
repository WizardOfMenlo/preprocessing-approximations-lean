#!/bin/bash
# Populate prove2me/workspace/.lake/packages with Lean v4.33.1 + Mathlib 0df444a (the Prove2Me
# default environment), cloning from the repo's own dependency checkouts (no network), then run
#   (cd prove2me/workspace && lake exe cache get)  to unpack the prebuilt Mathlib.
set -euo pipefail
R="$(cd "$(dirname "$0")/../.." && pwd)"
E="$(cd "$(dirname "$0")/.." && pwd)/workspace"
MREV=0df444a360eaa60ab8c11dca51a86af692955474

rm -rf "$E/.lake" "$E/lake-manifest.json"
mkdir -p "$E/.lake/packages"

clone() { # name rev
  git clone -q --no-checkout "$R/.lake/packages/$1" "$E/.lake/packages/$1"
  git -C "$E/.lake/packages/$1" -c advice.detachedHead=false checkout -q "$2"
  echo "$1 -> $(git -C "$E/.lake/packages/$1" rev-parse --short HEAD)"
}

clone mathlib "$MREV"
git -C "$E/.lake/packages/mathlib" remote set-url origin https://github.com/leanprover-community/mathlib4.git

# The package list Mathlib itself pins at that commit.
python3 - "$E" "$MREV" <<'PY'
import json, subprocess, sys
E, rev = sys.argv[1], sys.argv[2]
m = json.load(open(f"{E}/.lake/packages/mathlib/lake-manifest.json"))
pk = [{"url": "https://github.com/leanprover-community/mathlib4.git", "type": "git", "subDir": None,
       "scope": "", "rev": rev, "name": "mathlib", "manifestFile": "lake-manifest.json",
       "inputRev": rev, "inherited": False, "configFile": "lakefile.lean"}]
for p in m["packages"]:
    p = dict(p); p["inherited"] = True; pk.append(p)
out = {"version": m["version"], "packagesDir": ".lake/packages", "packages": pk,
       "name": "prove2me", "lakeDir": ".lake"}
json.dump(out, open(f"{E}/lake-manifest.json", "w"), indent=1)
with open(f"{E}/deps.txt", "w") as f:
    for p in m["packages"]:
        f.write(f'{p["name"]} {p["rev"]} {p["url"]}\n')
print("manifest written:", [p["name"] for p in pk], "version", m["version"])
PY

while read -r name rev url; do
  clone "$name" "$rev"
  git -C "$E/.lake/packages/$name" remote set-url origin "$url"
done < "$E/deps.txt"
rm "$E/deps.txt"
ls "$E/.lake/packages"
