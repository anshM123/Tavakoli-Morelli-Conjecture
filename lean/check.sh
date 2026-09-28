#!/usr/bin/env bash
# Check the Tavakoli-Morelli formalisation. Run from this directory (the Lake project root), e.g.
#   export PATH="$HOME/.elan/bin:$PATH"; lake exe cache get; bash check.sh
set -euo pipefail
out=.lake/build/lib/lean/TMProof
mkdir -p "$out"
for f in TM TM2; do
  echo "== TMProof/$f.lean"
  lake env lean -o "$out/$f.olean" -i "$out/$f.ilean" "TMProof/$f.lean"
done
echo "== TMProof/Axioms.lean"
lake env lean TMProof/Axioms.lean
echo "== forbidden keywords (sorry/admit/axiom/native_decide):"
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' TMProof/*.lean || echo "none"
