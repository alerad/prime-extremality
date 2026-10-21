# Formalizing "Prime extremality for product integrals over primitive sets"

This directory is a Lean 4 skeleton for the paper in `../main.tex`. Every
theorem of the paper is stated; the ones already provable from existing
libraries are proved, the rest are `sorry` with the intended proof route in
the docstring. This file records what exists, what is missing, and the order
in which to close the gaps.

## 1. Where the existing Lean work stands

Two repositories already cover parts of the paper.

**`~/research/leancert` (Lean 4.34.0, Mathlib v4.34.0, built locally).**
`LeanCert.QProduct` is the finite q-product layer plus the prime limit:

| Declaration | Content | Paper use |
|---|---|---|
| `qProd`, `F`, `moment` | `∏_{n∈S}(1-uⁿ)`, `∫₀¹ qProd`, `∫₀¹ qProd·uᵏ` | `P_A`, `F_1`, moments |
| `finiteIntegralRat_correct`, `momentRat_correct` | exact rational values by powerset expansion | small exact checks |
| `verify_finiteIntegral_*`, `verify_limit_interval` | boolean certificates → real enclosures | Λ enclosures |
| `primesLE`, `primeLambda` | primes ≤ N; Λ as `sInf` of truncations | `𝒫_N`, Λ |
| `primeLambda_eq_integral_tprod` | Λ = ∫₀¹ ∏'_p (1-u^p) | 𝓛(1) = Λ |
| `sInf_F_filter_eq_integral_tprod` | same bridge for any decidable exponent predicate (dominated convergence) | infinite sets at c = 1 |
| `primeLambda_sandwich`, `primeLambdaLimitCert` | tail-corrected truncations, `DirectedLimitCert` | Λ digits (coarse) |
| `one_sub_prod_one_sub_le_sum`, `qProd_sub_le_commonPrefix_sum`, `F_sub_le_two_mul_moment_of_two_mem` | Weierstrass bound and tail collapse | endpoint estimate, tail bounds |
| `leancert` tactic | exact polynomial integrals over ℚ, interval bounds | Lemma 2.2 arithmetic, Prop 1.3 |

**`~/research/formalizations/productinvariants` (Lean 4.30.0-rc2, Mathlib
5450b53, not built locally, depends on leancert at an old commit).** This is
the artifact cited in paper §6. It proves, all at `c = 1` and for finite sets:

| Declaration | File | Paper |
|---|---|---|
| `block_partial_pos_of_two_le` / `blockE_partial_pos` | `Finite/TailDomination16`, `Finite/BlockEPartial` | Thm 1.4, finite T, **all c** (Bernstein certificate, cutoff 16) |
| `integral_pos_of_single_crossing` | `Finite/BlockExchange` | abstract "Layer 1" behind Lemma 2.1 |
| `integral_weight_mul_nonneg/pos` | `Finite/WeightedRunningPositivity` | Lemma 3.1/3.3 with C¹ weight, on [0,1] |
| `running_pos_comp_pow(_pos)` | `Finite/PowerSubstitution` | Cor 3.2, **all c**, integer p |
| `phaseIntegral_blockStep_diff`, `weighted_blockE_pow_pos_of_nonempty` | `Finite/BlockExchangePow` | identity (1.2), Prop 3.4 at c = 1 |
| `compressAt`, `antichain_descends_to_allPrime`, `lambda_le/lt_phaseIntegral_antichain` | `Finite/Antichain` | §4 descent, Λ < F(A) |
| `phaseProduct'`, `hasDerivAt_phaseProduct`, … | `Finite/PhaseProductDeriv` | derivative of the weight `P_B` |
| `polyOfList`, `aeval_pos_of_myBernLo_pos` | `Finite/BernsteinBridge` | Bernstein certificates by `native_decide` |
| `IPoly`, `primePhaseIntegralRat`, `Lambda_bounds_2003` | `Certified/*` | 26 digits of Λ |
| `prime_phase_tail_bound` | `Prime/TailBound` | Prop 5.2 with R = {2} |

Not formalized anywhere (paper §6): uniformity in `c` for the extremal
theorems, strict finite uniqueness, the infinite case, the elementary proof of
Theorem 1.4 (Lemma 2.1 + Lemma 2.2), Proposition 1.3, Corollary 1.5, general-R
tail bound, Proposition 5.1.

## 2. Architecture decision

Build the new development **on leancert (4.34.0)** and **port** the needed
productinvariants files into it, rather than depending on productinvariants:

- the two repositories pin different toolchains and productinvariants pins an
  old leancert commit, so they cannot be imported together;
- the port is mechanical: `phaseProduct := qProd`, `phaseIntegral := F`; the
  files to port are `WeightedRunningPositivity`, `PhaseProductDeriv`,
  `PowerSubstitution`, `BlockExchange` (Layer 1 only, already ported here),
  `BlockExchangePow`, `Antichain`, `Exchange`, `BernsteinBridge/Probe`,
  `TailDomination16` (or drop it, see §3 Phase 4), `Certified/PolynomialIntegral`
  and `LambdaHighPrecision`, `Prime/TailBound` — about 3,000 lines, mostly
  Mathlib-only proofs that should survive the 4.30 → 4.34 move with local fixes.

The alternative, upgrading productinvariants in place to 4.34.0 and adding
new files there, is equally valid; the skeleton here is written so its
statements can move either way.

## 3. Phases

Each phase lists the `sorry` obligations in this skeleton and how to close them.

### Phase 0: build setup

`lakefile.toml` requires leancert as a path dependency so the built Mathlib
under `~/research/leancert/.lake` is reused. Two ways to check the files:

- `./check.sh` compiles the modules in order with `lean` against leancert's
  `LEAN_PATH` (no `lake update`, no Mathlib download; this is how the skeleton
  was verified).
- `lake build` in this directory. Lake will materialize leancert's transitive
  dependencies under `.lake/packages`; run `lake exe cache get` afterwards.
  `lean-runtime adopt ~/research/leancert` would instead share the existing
  environment, but its dry run reports it replaces 7.4 GiB of local package
  directories in the leancert checkout, so it was not run.

`lake` and `lean` are not on `PATH` in this shell; use `~/.elan/bin`.

### Phase 1: port the c = 1 engine, parameterized by c

Target: `Transport.lean`.

- `integral_weight_mul_pos_upto`: same proof as `integral_weight_mul_pos`
  with `1` replaced by `c` (`integral_mul_deriv_eq_deriv_mul` on `[0,c]`).
  The strictness disjunction covers Lemma 3.1 (`w(c) > 0`) and Lemma 3.3
  (`w' < 0` somewhere) in one statement.
- `qProd'`, `hasDerivAt_qProd`, `qProd'_nonpos`, `continuous_qProd'`,
  `qProd'_neg_of_nonempty`, `continuous_blockE`: verbatim ports.
- `running_pos_comp_pow_pos`: verbatim port (`PowerSubstitution.lean` already
  quantifies over `c`). It consumes `blockE_partial_pos` from Phase 4.
- `Fc_blockStep_diff`: port of `phaseIntegral_blockStep_diff` with
  `integral_sub` on `[0,c]`.
- `block_exchange_lt` (Prop 3.4, finite): combine the three above. Note the
  paper's case split at `c = 1`: for `c < 1` use `w(c) = P_B(c) > 0`; for
  `c = 1`, `B = ∅` is `running_pos_comp_pow_pos` itself and `B ≠ ∅` uses
  `qProd'_neg_of_nonempty`.

### Phase 2: Theorem 1.1 (finite, all c, strict)

Target: `Extremal.lean`, finite half.

- `compressAt_isPrimitiveFin`, `compressAt_bounded`, `sum_compressAt_lt`:
  ports of `compressAt_isDivAntichain`, `compressAt_inInterval`,
  `sum_compressAt_lt` (the descent measure is the element sum).
- `Fc_compressAt_lt`: instantiate `block_exchange_lt` with
  `B = A.filter (¬ p ∣ ·)`, `T = quotients p A`, using
  `multiples_eq_image_quotients` and `quotients_ge_two_of_not_mem` from the
  port of `Antichain.lean`.
- `Fc_insert_lt`: port of `phaseIntegral_insert_lt` on `[0,c]`
  (`integral_pos` with integrand `x^q · P_R(x)`).
- `Fc_primesLE_lt`: strong induction on `A.sum id` as in
  `antichain_descends_to_allPrime_aux`, but carrying (i) the level `c` and
  (ii) strictness from the first step. Then add missing primes one at a time.

This closes "uniformity in c" and "strict finite uniqueness" from paper §6.

### Phase 3: infinite sets, Theorem 1.2

Targets: `Basic.lean` facts about `qProdSet`, `UniversalInequality.lean`,
`Transport.lean` (`block_exchange_lt_set`), `Extremal.lean` (infinite half).

Analytic groundwork for `qProdSet A u = ∏' n : A, (1 - uⁿ)`:

- multipliability on `[0,1)`: `Real.multipliable_one_add_of_summable`-style
  lemma applied to `-uⁿ`, summable by comparison with the geometric series
  (`summable_indicator_pow` in `LeanCert.QProduct.InfiniteProduct` is the
  same fact in predicate form);
- `qProdSet` is the pointwise limit of the finite truncations
  (`qProd_filter_tendsto_tprod` there, generalized from predicates to sets or
  used with `DecidablePred (· ∈ A)` as in `tendsto_Fc_truncation`);
- antitonicity `qProdSet T ≤ qProd S` for `S ⊆ T`, and `Hfun ≤ qProdSet T`
  (`Hfun_le_qProdSet`): every omitted factor lies in `[0,1]`, so
  `Multipliable.tprod_le_of_prod_le`-type lemmas or a truncation limit apply;
- `tendsto_Fc_truncation`, `tendsto_Fc_primesLE`: dominated convergence with
  bound `1` on `[0,c]`, copying `tendsto_F_filter_integral_tprod` with `1`
  replaced by `c`.

Theorem 1.4 for infinite `T` (`running_pos_set`) without Section 2: use the
cutoff-16 certificate's *uniform* error term. For any finite
`S ⊇ T₀ = {2..16}`, `∫₀ᶜ P_S ≥ ∫₀ᶜ P_{T₀} - Err₁₆(c)`, and the certificate
says the right side exceeds `c - c²/2` by `c²Q₁₆(c) > 0`. Apply to the
truncations of `T ∪ T₀`, pass to the limit, and use `P_T ≥ P_{T∪T₀}`. The
limit inherits a bound that is already strict, so no strictness is lost.
(With Phase 4 done, `Hfun_le_qProdSet` plus `running_pos_Hfun` is shorter.)

Proposition 3.4 for infinite `B, T` (`block_exchange_lt_set`) without
Stieltjes integration by parts: with `g(u) = E_T(uᵖ)` and
`G(y) = ∫₀ʸ g > 0`,

1. for `c < 1`: the finite engine on the truncation `B_N` gives
   `∫₀ᶜ P_{B_N} g ≥ P_{B_N}(c) G(c) ≥ P_B(c) G(c) > 0`; let `N → ∞`
   (dominated convergence, `|P_{B_N} g| ≤ |g|`);
2. for `c = 1`, pick `b ∈ B`, write `P_{B_N} = (1-u^b) P_{B_N∖b}`; then
   `-P_{B_N}' ≥ b u^{b-1} P_{B_N∖b} ≥ b u^{b-1} P_{B∖b}`, so the integration
   by parts tail is at least `κ := ∫₀¹ b u^{b-1} P_{B∖b}(u) G(u) du > 0`,
   independent of `N`; let `N → ∞`.

Then `Lfun_le_FcSet` (truncate, apply `Fc_primesLE_le`, take limits) and
`Lfun_lt_FcSet` exactly as in the paper: one strict compression or one strict
prime insertion, followed by the non-strict lower bound. `FcSet_primes` is a
reindexing of `Nat.Primes` against the subtype of `Primes`
(`Equiv.tprod_eq`).

### Phase 4: the elementary proof of Theorem 1.4 (paper §2)

Targets: `Endpoint.lean`, `SingleCrossing.lean`.

Already proved here: the three rational integrals of Lemma 2.2 (`leancert`),
`Qtilde_one`, and the abstract single-crossing lemma (verbatim port, compiles
on 4.34.0).

- `polyLower_le_Hfun`: `Hfun x = P₅(x) · ∏'_{n≥6}(1-xⁿ)` (split the `tprod`
  over `{2..5}` and `{n ≥ 6}`), then the infinite Weierstrass inequality
  `∏'(1-yₙ) ≥ 1 - ∑' yₙ` (finite version `one_sub_prod_one_sub_le_sum` plus a
  limit), with `∑'_{n≥6} xⁿ = x⁶/(1-x)`.
- `endpoint_estimate`: `integral_mono_on` with `polyLower_le_Hfun` (the bound
  may be negative near 1, which is harmless) and `integral_polyLower`.
- `hlog_eq_tsum`, `hlog_strictConcaveOn`: `Real.log` of the `tprod` is the
  `tsum` of logs (`Real.log_tprod`-style lemma or `HasProd.log`); apply
  `hasDerivAt_tsum_of_isPreconnected` twice on `[0,r]`, `r < 1`, with the
  summable majorants `n rⁿ⁻¹` and `n² rⁿ⁻²`, then
  `strictConcaveOn_of_deriv2_neg` on `Ico 0 1` with the explicit `h''`.
- `single_crossing`: from strict concavity, `hlog 0 = 0`, positivity near `0`,
  negativity near `1`: the set `{h ≥ 0}` is an interval `[0,a]`.
- `running_pos_Hfun`: `integral_pos_of_single_crossing` with
  `E = Hfun - (1-x)`, `hend` from `endpoint_estimate`, and
  `∫₀ᶜ (1-x) = c - c²/2`.
- `Qtilde_pos` (Remark 2.4): done. LeanCert (branch
  `feat/bernstein-polynomial-bounds`) proves it with plain `leancert` through
  its new Bernstein polynomial certificate; no productinvariants port needed.

With Phase 4 done, `blockE_partial_pos` follows from `running_pos_Hfun` and
`Hfun_le_qProd`, and the 615-line `TailDomination16.lean` need not be ported;
keep it only to reproduce the paper's Appendix A route.

### Phase 5: consequences

Target: `Consequences.lean`.

- Prop 1.3: `qProd_A9_ratio` is Finset algebra (`primesLE N` splits as
  `{2,3} ∪ rest` for `N ≥ 9`, `Finset.prod_union`); `ratio_lt_one_near_one` is
  proved (`leancert` on `[0.98,1]`); `pointwise_failure` combines them with
  `qProd (primesLE N) x > 0` on `[0,1)`. `A9_isPrimitiveFin` is a finite
  divisibility check: for primes `p ≥ 5` and `{4,6,9}` nothing divides.
- Cor 1.5: the law of `Z_S` is the Stieltjes measure of `1 - P_S` clamped to
  `[0,1]` (`bottleneckCDF`). `expectPhi_hinge` is the layer-cake identity
  `∫ min(x,c) dμ = ∫₀ᶜ (1 - F(x)) dx`. The general concave case needs the
  representation `φ(x) = φ(0⁺) + a x + ∫ min(x,t) μ(dt)` with `μ` the
  Stieltjes measure of `-φ'₊`; Mathlib has `StieltjesFunction` and right
  derivatives but not this representation packaged. Treat as a stretch goal;
  the hinge case is Theorem 1.1 verbatim.
- Prop 5.1 for integer `k ∈ {1,2}` (`Mc_primesLE_lt`): rerun Phases 1–2 with
  weight `k u^{k-1}`. For `k = 2` the substitution trick of
  `PowerSubstitution.lean` uses the antiderivative `A(u) = G(uᵖ)` and the
  integer-power weight `2u^{2-p}/p`, nonincreasing for `p ≥ 2`; no `rpow`.
  Real `k ∈ (1,2)` would need `rpow` throughout and is out of scope here.
- Open problem 2 data: `A9_beats_primes_at_126` and `primes_beat_A9_at_125`
  are proved (`momentRat` + `native_decide`).
- Prop 5.2 with `R = {2}` (`tail_bound`): port `Prime/TailBound.lean`, then
  identify productinvariants' `Lambda` with `primeLambda` (both are the
  infimum of the same truncation sequence). The general finite `R` version is
  new work: beta-integral bounds `K_R(m) ≍ m^{-|R|-1}` plus partial summation
  with `π(x) ≪ x/log x` (Mathlib has Chebyshev bounds in
  `Mathlib.NumberTheory.Chebyshev`).

### Phase 6: Λ digits and release

- `primeLambda_digits26`: done. LeanCert's `QProduct.Sparse` module
  (branch `feat/bernstein-polynomial-bounds`) evaluates `F (primesLE 2003)`
  and the tail moment exactly in linear time per factor; the skeleton proves
  the 26-digit enclosure by one `native_decide` (about two minutes).
- Replace the `path` dependency by a pinned `git`/`rev`, add a CI workflow
  (`lake build`, `#print axioms` audit distinguishing `Lean.ofReduceBool`), and
  update the paper's §6 table with the new declaration names.

## 4. Effort and risk

| Phase | New Lean (est.) | Risk |
|---|---|---|
| 1 port engine | 800 lines ported, 100 new | Mathlib name drift 4.30 → 4.34 (`integral_mul_deriv_eq_deriv_mul` and `integral_pos` unchanged as of this check) |
| 2 finite theorem | 500 ported, 200 new | none structural |
| 3 infinite sets | 600 new | `tprod` API conventions at `u = 1` (define `qProdSet` only via integrals on `[0,c]`, never evaluate at 1) |
| 4 elementary route | 700 new | second derivative of a `tsum`; Bernstein bridge port |
| 5 consequences | 300 new + Stieltjes (open-ended) | Corollary 1.5 general case |
| 6 digits, release | 900 ported | `native_decide` build time for N = 2003 |

The load-bearing order is 1 → 2 → 3; Phase 4 is what makes the artifact
match the paper's main-text proof and is independent of 1–3 except for
supplying `blockE_partial_pos` (otherwise supplied by the certificate port).

## 5. Status (2026-09-22): complete

Every theorem of the paper stated in this development is proved. `./check.sh`
compiles all nine modules with **zero `sorry`** (about 3,900 lines). Axiom
footprint of the main results (`#print axioms`):

- `Fc_primesLE_lt` (Theorem 1.1), `Lfun_le_FcSet`/`Lfun_lt_FcSet` (Theorem 1.2),
  `running_pos_set`/`blockE_partial_pos` (Theorem 1.4), `single_crossing`,
  `endpoint_estimate`, `block_exchange_lt_set` (Proposition 3.4),
  `pointwise_failure` (Proposition 1.3), `icv_minimality` and `expectPhi_hinge`
  (Corollary 1.5), `Mc_primesLE_lt` (Proposition 5.1, k ∈ {1,2}), `tail_bound`
  (Proposition 5.2, R = {2}): `propext`, `Classical.choice`, `Quot.sound` only.
- `primeLambda_digits26` (26 digits of Λ) and `A9_beats_primes_at_126`
  (open problem 2 data) additionally use `native_decide` (an auxiliary
  `..._native.native_decide.ax_*` axiom), as in the paper's §6 disclosure.
  `Qtilde_pos` (Remark 2.4) uses only the three standard axioms (re-audited
  2026-09-24).

Deviations from the paper's proofs, all mathematically equivalent:

- Lemma 2.1: strict concavity of `h` is obtained from strict concavity of
  `log(1+x)` plus termwise concavity of `∑ log(1-xⁿ)`, not from the second
  derivative of the series.
- Proposition 3.4 (finite): no case split at `c = 1`; strictness comes from
  `w' < 0` at `c/2` when `B ≠ ∅`. The hypothesis `T ≠ ∅` is unused.
- Proposition 3.4 (infinite): no Stieltjes integration by parts. The
  integrand is bounded below by the continuous envelope `H(uᵖ) - (1 - uᵖ)`,
  and the gap is bounded below by `κ_c = ∫₀ᶜ b u^{b-1} H(u) G̃(u) du > 0`
  uniformly over the finite truncations of `B`, then dominated convergence.
- Corollary 1.5: the Stieltjes representation of `φ` is replaced by uniform-grid
  piecewise-linear interpolants, which are nonnegative hinge combinations, and
  dominated convergence.
- Statement hygiene: `Fc_compressAt_lt`/`sum_compressAt_lt` carry `p ∉ A`
  (true by primitivity, needed for strictness) and `compressAt_bounded`
  carries primitivity; `Qtilde_pos` and the 26-digit sandwich go through
  LeanCert's Bernstein and sparse q-product certificates (merged upstream).

Module map: `Basic` (definitions), `Endpoint` (Lemma 2.2, analytic facts on
`H`), `InfiniteProduct` (tprod foundations, dominated convergence),
`SingleCrossing` (Lemma 2.1), `UniversalInequality` (Theorem 1.4),
`Transport` (§3), `Extremal` (§4), `Consequences` (§1.2, §5), `Lambda` (§5.2).

**Theorem 1.6 (2026-09-24).** The tail asymptotics of §5.4 are proved in
`Tail/*`, `TailAsymptotic` and `PNT` (built by `./op3-check.sh`, zero `sorry`).
`tail_asymptotic_pnt` and `tail_asymptotic_nth_pnt` depend only on `propext`,
`Classical.choice`, `Quot.sound`; the prime number theorem enters through
PrimeNumberTheoremAnd's `chebyshev_asymptotic` and `nth_prime_asymp`. Blueprint
and proof structure: `OP3_PLAN.md`.

Remaining follow-ups outside the paper's claims: Proposition 5.1 for real
`k ∈ (1,2)` (needs `rpow`), the general-`R` tail estimate of Proposition 5.2,
and replacing the `path` dependency on leancert by a pinned revision before
publication.
