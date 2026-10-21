#!/bin/sh
# Audit the axioms of the built development (run `lake build` first).
# Imports every module under RntPaper/ and runs scripts/AxiomCheck.lean.
set -e
cd "$(dirname "$0")/.."
OUT=.lake/AxiomCheckAll.lean
mkdir -p .lake
{
  find RntPaper -name '*.lean' | sort | sed -e 's/\.lean$//' -e 's|/|.|g' -e 's/^/import /'
  cat scripts/AxiomCheck.lean
} > "$OUT"
exec lake env lean "$OUT"
