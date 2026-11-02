# Independent review of notes.tex (first round, 2026-11-01)

Reviewer: independent agent with its own code (scripts `r_*.py` and outputs `r_*.out` in this folder).
Saved here verbatim in substance from the reviewer's final report; numbering = compiled notes.pdf
(lemmas share the theorem counter: almost-all theorem = Thm 2.7, all-N corollary = Cor 2.9).

## Verdict
No FATAL errors. All theorems true as stated. One small GAP, several MINOR issues. Every claimed number
reproduced independently.

## GAP
- **G1 (Thm 3.1, (b)⇒(a))**: the paper's Lemma 3.3 assumes a continuous integrand; here w ∈ L¹ only.
  The conclusion holds via Fubini: ∫₀^z P_B g = P_B(z)G(z) + ∫_(0,z] G d(−P_B) for g ∈ L¹. Fix: state
  the L¹ version.

## MINOR
- M1: remark after Cor 2.5: attaining the upper bound needs a gap ≍ √q (log q)^{3/2} *after* q, not
  ≫ √(q log q).
- M2: at the maximal gaps (q = 19661, 31469, 89753) Σ_q is *above* average (more primes follow q);
  the gap lies before q. The notes' interpretation was reversed.
- M3: correlation 0.9995 is for N > 5000; for N > 20000: corr 0.99978, slope 1.0010, intercept −0.0583.
- M4: "140.0 (N = 25)" should be 139.9229.
- M5: prime powers contribute O((log X)^{7/2}) (not O(log² X)) in windows h ≤ H(log X)²; harmless.
- M6: bookkeeping in Thm 2.7 (x may exceed 2X; grid covers [(N/X)H/(log X)², …]; state c ≥ t_qH, C ≤ t_qH).
- M7: Remark 2.8: the o(1) also contains Thm 2.4's o(1) and the O(1/log N) from Σ_q.
- M8: include the Jacobian factor e^{−t_q} in Thm 2.4's main term; then the residual is ≤ 0.0012 for
  N > 20000 (+0.0024, +0.0015, +0.0003, +0.0004 at N = 1009, 10007, 31397, 99989).
- M9: cross-reference collisions (cite paper results as [P, …]).
- M10: Thm 3.4 needs minimality on [1, b] ⊆ [1, 17/4], not "[1, 2b] from Remark 4.4".
- M11: `primes_minimize_Mk_N9` assumes 1 ≤ k ≤ 3146/25; 0 < k < 1 from the concave case.
- M12: Cor 2.5 sharpens Prop 5.5 only asymptotically (Prop 5.5 is explicit and PNT-free).
- M13: envelope_certificate.py: assert 1 − c v^{M+1} ≥ 0 on [0, v1]; the "{}" envelope includes
  (1 − v⁵) although 5 ∉ T (valid but weaker).
- M14: cosmetic (L(t)/L(mt) at mt = 1; "uniformly" in Thm 2.4).

## Recomputations (all ✓)
α₀ = 2.1431219182519166720…; k₉ = 125.840454069445657483245507029900387791… (certified ±1.4e−87, unique
simple positive root); −log(I_N − Λ) at N = 1009/10007/31397 = 47.952712/130.735241/216.824649; Thm 2.4
residuals +0.02273/+0.00717/+0.00338; R_{75/28}(1) = 5976995696/61712689944165; all Theorem 3.6
certificates re-run independently; conjecture evidence for N ≤ 30 reproduced.

## Answers to specific questions
No circularity in Thm 3.1 (induction on N, all weight indices). Infinite sets in Thm 3.4 handled
correctly. The compression at 5 sees only blocks in ⟨2,3,5⟩. Brun–Titchmarsh constants correct.
Thm 2.4's split is fine when Σ_q is small (Σ_q ≥ 1). Kumchev Thm 7 matches Lemma 2.6 verbatim.
