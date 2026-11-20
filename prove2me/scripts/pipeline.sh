#!/bin/bash
# Regenerate and check the whole Prove2Me tree from the repo sources:
#   repo build (Lean 4.34, --wfail) → port to Lean 4.33.1 → build → extract → generate → check.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
R="$(cd "$HERE/../.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"

step() { echo "== $*"; }

step "repo build (Lean 4.34, --wfail)"
( cd "$R" && lake build --wfail 2>&1 | grep -E '^(error|warning|✖)' -A4 | head -30 )
( cd "$R" && lake build --wfail >/dev/null 2>&1 ) || { echo "REPO BUILD FAILED"; exit 1; }
echo "ok"

step "port to Lean 4.33.1"
bash "$HERE/port_433.sh" || exit 1

step "workspace build of the ported library"
( cd "$HERE/../workspace" && lake build LatticePrepro 2>&1 | grep -E '^(error|✖)' -A4 | head -30 )
( cd "$HERE/../workspace" && lake build LatticePrepro >/dev/null 2>&1 ) || { echo "PORT BUILD FAILED"; exit 1; }
echo "ok"

step "extract"
bash "$HERE/extract_all.sh" || exit 1

step "generate"
python3 "$HERE/generate.py" || exit 1

step "check"
bash "$HERE/check.sh"
echo "PIPELINE_DONE"
