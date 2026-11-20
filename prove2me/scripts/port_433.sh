#!/bin/bash
# Copy the repo sources (Lean 4.34.0) into the Prove2Me workspace (Lean 4.33.1) and apply the
# mechanical renames needed there. The repo stays the source of truth; the copy is derived.
#
# Lean 4.34 renamed `if_pos`/`if_neg` to `ite_eq_left`/`ite_eq_right` and `dif_pos`/`dif_neg` to
# `dite_eq_left`/`dite_eq_right` (old names deprecated);
# Lean 4.33.1 only has the old names.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
R="$(cd "$HERE/../.." && pwd)"
E="$HERE/../workspace"

rm -rf "$E/LatticePrepro" "$E/LatticePrepro.lean"
cp -R "$R/LatticePrepro" "$E/LatticePrepro"
cp "$R/LatticePrepro.lean" "$E/LatticePrepro.lean"

find "$E/LatticePrepro" -name '*.lean' -print0 | xargs -0 perl -pi -e '
  s/\bite_eq_left\b(?!_iff)/if_pos/g;
  s/\bite_eq_right\b(?!_iff)/if_neg/g;
  s/\bdite_eq_left\b(?!_iff)/dif_pos/g;
  s/\bdite_eq_right\b(?!_iff)/dif_neg/g;
'
echo "ported: $(diff -rq "$R/LatticePrepro" "$E/LatticePrepro" | wc -l | tr -d ' ') file(s) differ from the repo sources"
