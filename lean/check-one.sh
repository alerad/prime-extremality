#!/bin/sh
# Compile one skeleton module against the built leancert checkout, writing its
# olean into .lake/check so dependents can import it.  Usage:
#   ./check-one.sh Transport          # compiles RntPaper/Transport.lean
#   ./check-one.sh Basic Endpoint     # several, in order
# Run ./check.sh once first so every dependency olean exists.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
LEANCERT="${LEANCERT:-$HOME/research/leancert}"
export PATH="$HOME/.elan/bin:$PATH"
LC="$(cd "$LEANCERT" && lake env printenv LEAN_PATH)"
OUT="${OUT:-$HERE/.lake/check}"
mkdir -p "$OUT/RntPaper"
export LEAN_PATH="$LC:$OUT"
cd "$HERE"
for f in "$@"; do
  echo "== RntPaper/$f.lean"
  lean -o "$OUT/RntPaper/$f.olean" -i "$OUT/RntPaper/$f.ilean" "RntPaper/$f.lean" \
    | grep -v "declaration uses .sorry." || true
done
