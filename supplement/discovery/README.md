# Follow-up results on open problems 2 and 3 (2026-10-31 / 11-01)

`notes.tex` / `notes.pdf` state and prove the results; "[P, …]" refers to `../../main.tex`.

| Result (notes numbering) | Status | Where |
|---|---|---|
| Thm 2.4 local law: `I_N - Λ = (1+O(q^{-1/4} log^4 q)) sqrt(2π/Φ''(t_q)) e^{-M_q-t_q} Σ_q`, every N | proof | notes §2.2 |
| Cor 2.5 two-sided bounds for every N (asymptotic sharpening of [P, Prop 5.5]) | proof | notes §2.3 |
| Thm 2.7 heuristic of open problem 3 holds for all N outside O_A(X/(log X)^A) | proof (uses Huxley's almost-all PNT) | notes §2.4 |
| Cor 2.9 heuristic for all N would imply `p_{n+1}-p_n ≪ sqrt(p_n log p_n)` | proof | notes §2.5 |
| Thm 3.2 relative version of open problem 2: exact cone; powers iff `k ≤ 2α₀` (Cor 3.3) | proof + **Lean** | notes §3.1, `../../lean/RntPaper/Relative.lean` |
| Thm 3.5 absolute moments for `0 < k ≤ 3b` when `J_b(1) > 0` (`51/8` with b = 17/8) | **Lean** | `../../lean/RntPaper/MomentsOdd.lean` |
| Thm 3.7 absolute moments for `0 < k < 3 + 6√3` | proof + exact certificates + **Lean** | `envelope_certificate.py`, `../../lean/RntPaper/Moments1339.lean` |
| **Thm 3.8: the primes minimize E min(Z_A^k, c^k) for every N iff `k ≤ k₉ = 125.8404540694…`** | proof + 5,350 exact certificates + **Lean** (certificates by `native_decide`) | notes §3.3, `stage1/`, `../../lean/RntPaper/K9Theorem.lean` |
| `k₉` is algebraic of degree 19 (explicit irreducible integer polynomial) | exact computation | `k9_minpoly.py` |

Independent reviews, both with their own code: `review/REPORT.md` (sections 2–3.1) and
`review2/REPORT.md` (Theorem 3.8 and its certification; every case re-verified by different exact
methods, plus an exhaustive search over 2.19 million maximal primitive sets for N ≤ 62). Neither found a
fatal issue; all gaps and minor issues they raised are fixed in the notes.

## Scripts

Floating point is evidence only. `envelope_certificate.py` and `stage1/cert_stage3.py` are exact and
exit 1 on failure.

- §2: `op3_local.py` (telescoping terms δ(p), saddle data; writes `op3_data.npz`, `op3_rows.npy`;
  about 15 min), `op3_tables.py` (figure/table data, main term with e^{-M_q-t_q}), `op3_check_thmA.py`,
  `op3_variance.py`.
- §3.1–3.2: `op2_relative.py`, `envelope_certificate.py` (under a second), exploratory `s23.py`, `h23.py`, `h235.py`.
- §3.3 (Theorem 3.8), in `stage1/`:
  - `cert_lib.py` (exact certificate primitives: root isolation, exact endpoint integrals, V1),
    `cert_stage3.py` (builds and runs all 5,350 certificates in parallel, about a minute on 14
    cores; exits 1 on any failure; log `cert_stage3_log.jsonl`). Optional env vars `KINDS=...`,
    `LOG=...`, `JOBS=...`. Earlier partial runs: `cert_part1_log.jsonl`, `cert_part2_log.jsonl`.
  - `cross_check.py`: independent 40-digit quadrature of a sample of certificate values.
  - floating-point exploration: `explore.py`, `tails.py`, `stage3_explore.py`, `merged_tail2.py`,
    `signscan.py`; counterexample search `cex_search.py`.
- Evidence also used in the notes: `op2_absolute_scan.py`, `op2_scan_fast.py N0 N1`, `op2_families.py`,
  `weight_aware_probe.py`, `next_round_probe.py`.

The Lean module builds with `cd ../../lean && ./build35.py RntPaper.MomentsOdd` (or `lake build`, whose
globs include it). Its main theorems use only `propext`, `Classical.choice` and `Quot.sound`. It is not
imported by `RntPaper.lean`, and `lean/README.md` does not list it yet.

## Lean formalization (2026-11-02)

All in `../../lean/RntPaper/`, untracked and not yet imported by `RntPaper.lean`. Build a module with
`cd ../../lean && ./build35.py RntPaper.<Module>`.

- Theorem 3.2 and Corollary 3.3: `RelativeL1.lean` (L¹ Stieltjes lemma), `RelativeCone.lean`, `Relative.lean`:
  `relative_cone_iff`, `relative_cone_le`, `relative_cone_lt`, `alpha0`, `alpha0_mem`, `relative_powers_iff`,
  `twoPrimes_moment_lt`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Theorem 3.7: `Moments1339Cert.lean` (9 certificates by `decide +kernel`), `Moments1339.lean`:
  `moment_primesLE_lt_1339`, `moment_primes_lt_1339`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Theorem 3.8: certificate library `CertPoly`, `CertAnalytic` (single-crossing / variation-diminishing and
  envelope lemmas), `CertCheck`, `CertFast` (integer bisection), `CertV1`; the case enumeration with
  completeness proofs `K9Defs`, `K9Enum` (parameters of the envelope certificates in `K9Data`, re-verified);
  `K9Tight` (`k9` as the root in `(125.84, 125.85)`, uniqueness, sign of `E Z^k_{A₉} − E Z^k_{𝒫₉}`);
  `K9Sound`, `K9Descent`, `K9Main` (the weighted ordered descent, finite and arbitrary sets); 114 computation
  files `K9Cert/*.lean`; `K9Theorem.lean`: `moment_primesLE_k9`, `moment_primes_k9`, `moment_A9_lt`,
  `k9_threshold`, `k9_unique_root`. Axioms: the standard three plus the auto-generated `native_decide`
  axioms of the certificate theorems (kernel evaluation was tested and is about 100× too slow for the
  largest cases). Compiling `K9Cert` takes about 10 minutes on 12 cores.
