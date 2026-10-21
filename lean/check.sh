#!/bin/sh
# Build every module that does not need PrimeNumberTheoremAnd (Lean v4.35, see README).
set -e
cd "$(dirname "$0")"
exec ./build35.py RntPaper RntPaper.Moments RntPaper.TailAsymptotic RntPaper.Tail.Saddle2 \
  RntPaper.Tail.Phi2 RntPaper.Tail.ExpSum2 RntPaper.Tail.Second "$@"
