# Independent review of Theorem 3.8 (k₉) and its certification (second round, 2026-11-01)

Reviewer: independent agent; none of its code imports `cert_lib`/`cert_stage3`. Scripts and outputs are in
this folder (`rv_*.py`, `*.out`, `*.json(l)`). Saved here in substance from the reviewer's final report
(the harness blocked the reviewer from writing this file). Numbering: thm:k9 = Thm 3.8, lem:wexch =
Lemma 3.9, prop:cert = Prop 3.10, lem:stieltjesL1 = Lemma 3.1.

## Verdict
**Correct, with two presentation-level gaps (one-line fixes).** Every computational claim reproduced
independently; no counterexample in the searched space. Not re-checked: step (i)'s reliance on the
paper's Remark 4.4 (formalized in the paper's Lean development) and J_s(1) > 0 for s ≤ 17/8.

## GAPs
- **G1 (step (iii))**: "A ⊇ P ∩ [11,N]" fails when 11 ∉ A and no composite is divisible by 11 (stage p only
  adds primes in (p,N]); the descent simulation `rv_descent_sim.py` hits this in 1,506/20,000 runs, always
  missing exactly {11}. Fix: in (iii) add every missing prime in [11,N] (legal: composites are 7-smooth).
- **G2 (prop:cert(b))**: "for every 0<k≤126 if S≠A₉" goes through maximality; for S = {4,5,7,9} (and
  {5,6,7,9}) the only maximal superset with the same max is A₉, certified only up to k₉. The theorem needs
  only k ≤ k₉, so it is unaffected; and P_{4,5,7,9} − P_{2,3,5,7} > 0 on (0,1) exactly (same for {5,6,7,9}).
  Fix: restate (b) ("126 unless S ⊆ A₉") or add the two direct checks.

## MINOR
- M1: "no element of A is divisible by q∈(p,N]" → "no composite element".
- M2: strictness hypothesis of lem:stieltjesL1 in lem:wexch's proof not checked (it holds: c<1 gives
  w(c)>0; c=1 and B∖B₀≠∅ gives mass of d(−w) on (0,1); B∖B₀=∅ gives G(c)).
- M3: infinite case: say steps (ii)–(iii) run with infinitely many primes in B (P_B continuous nonincreasing).
- M4: "B_p < m_p" fails for p = 47, 53, 59 (B_p = m_p); only B_p ≤ m_p is needed.
- M5: "above 24" → "≥ 24", "exceeds 64" → "≥ 64".
- M6: V1 description vs code: N₂ truncation only in merged tails (all logged with N₂ = 120); single tails
  truncate at B_p in v = u^p; the code's merged envelope replaces C(A₀)∩[N₂,∞) by all n ≥ N₂ (weaker,
  valid; both versions verified).
- M7: the equality statement at k₉ needs its short argument; `cex_search.py` tests only c = 1 at
  k ∈ {120, 125.8}.
- M8: `cert_stage3.py` default run includes 487 obsolete `merged_tail` tasks (fail by design) → exit 1;
  docstring cites "notes, section 4".
- M9: `crossing_type` relies on sympy `Poly.intervals` (correct in all 4,076 uses); a more robust criterion
  is to check R_K(y) > 0 for all y directly, with monotonicity in k from [P, Lemma 3.1].

## Checked and correct
Stage-p structure (p-smooth composites, addable primes, p·max T ≤ N, B₀ ⊆ B); lem:wexch and lem:stieltjesL1
incl. strictness; maximality reduction (weight depends only on max); both tail envelopes; weight primes
[11,64] in merged tails; no gaps between explicit ranges and tails; small N, covering, Dickson, variation
diminishing; code: crossing_type (cannot misreport two sign changes as 'single' unless sympy misses roots),
R1 and partial_integrals exact, V1 scaling correct, psi decreasing, c v₁^B < 1 enforced, lhs > rhs ⇒
positive running integrals for all y and k ≤ K.

## Independent re-verification (all cases)
- Enumeration (Bron–Kerbosch): 3113 / 928 / 243 / 1031 (12 vacuous) / 35, case sets identical to the logs;
  N = 46 has 22,299 maximal primitive sets.
- All 4,076 explicit cases: (A) own root isolation (flint) + exact R₁₂₆(1); (B) direct exact proof that
  R₁₂₆(y) > 0 for all y ∈ (0,1]. All pass; minimum margins 5.81e−8 (S = {4,6,7,9,10,15,25}) and 1.43e−5
  (p = 11, T = {2,3,5}).
- A₉: one sign change; R(125.84) = +3.58e−11, R(125.85) = −7.52e−10; k₉ = 125.8404540694456574832455…
- All 1,274 tails: rigorous interval arithmetic (outward rounding), a different method from V1; all pass.
- All 1,262 logged V1 certificates: L − T ≥ 0 by exact root counting, lhs/rhs recomputed exactly; all pass.

## Counterexample search (floating point, all truncation levels c)
- Exhaustive N = 7…62: 2,194,792 maximal primitive sets, none below k₉; only A₉ (125.8405) and the N = 25–28
  set (139.923) fall below 140.
- Random greedy maximal sets N = 70…400: 53,575 sets, none fails at k = 150.
- Simulated annealing (256 runs, antichains of 13-smooth composites ≤ 400): nothing below k₉.
