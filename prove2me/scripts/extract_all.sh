#!/bin/bash
# Run the three extractors over the ported sources. Run after `lake build LatticePrepro`.
#   bash scripts/extract_all.sh          # everything
#   bash scripts/extract_all.sh one F    # (internal) one file
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
cd "$HERE/../workspace"

if [ "${1:-}" = "one" ]; then
  f="$2"
  m="$(echo "${f%.lean}" | tr / .)"
  lake env lean --run ../scripts/ExtractSyntax.lean "$f" "$m" \
    > "../out/syntax/$m.jsonl" 2> "../out/syntax/$m.err" || echo "SYNTAX FAILED $m"
  lake env lean --run ../scripts/ExtractRefs.lean "$f" \
    > "../out/refs/$m.jsonl" 2> "../out/refs/$m.err" || echo "REFS FAILED $m"
  exit 0
fi

mkdir -p ../out/syntax ../out/refs
find LatticePrepro -name '*.lean' | sort > ../out/files.txt
lake env lean ../scripts/ExtractDecls.lean
xargs -P 6 -n 1 bash "$HERE/extract_all.sh" one < ../out/files.txt
echo "syntax errors: $(cat ../out/syntax/*.err | wc -l | tr -d ' ') lines; ref errors: $(cat ../out/refs/*.err | wc -l | tr -d ' ') lines"
