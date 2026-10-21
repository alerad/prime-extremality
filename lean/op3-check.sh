#!/bin/sh
# Build the PrimeNumberTheoremAnd bridges (Theorems 1.6, 5.10 and the unconditional
# stability asymptotic). Needs the PNT+ closure compiled into $PNT_BUILD (see README).
set -e
cd "$(dirname "$0")"
export PNT_BUILD="${PNT_BUILD:-$HOME/research/formalizations/round2/.deps/build-upstream-435}"
exec ./build35.py RntPaper.PNT RntPaper.TailSecond "$@"
