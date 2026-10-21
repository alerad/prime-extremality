# rnt-paper/lean

Lean 4 formalization of *Prime extremality for product integrals over primitive
sets* (`../main.tex`). Lean **v4.35.0**, Mathlib `56a00585`, built against
[LeanCert](https://github.com/alerad/leancert) (`~/research/leancert`), its q-product
library [leancert-qproduct](../../../leancert-qproduct) (`QProduct.*`, formerly
`LeanCert.QProduct.*`) and, for the prime number theorem, PrimeNumberTheoremAnd at
upstream commit `127b50e5` (unmodified).

- `FORMALIZATION_PLAN.md`: inventory and phase plan from the original development.
- `RntPaper/*.lean`: one module per paper section. No `sorry`. Every main theorem
  depends only on `propext`, `Classical.choice`, `Quot.sound`, except the digits of Λ
  and the `k = 126` comparison, which use `native_decide`.

## Checking

The development is compiled module by module with `lean` (no Lake), reusing the built
Mathlib of the leancert checkout. `build35.py` resolves imports, compiles in dependency
order in parallel into `.lake/check35`, and skips up-to-date modules (`FORCE=1` rebuilds,
`VERBOSE=1` prints Lean's messages, e.g. `#print axioms` output).

```sh
./check.sh        # everything except the PrimeNumberTheoremAnd bridges (~3 min clean)
./op3-check.sh    # PNT.lean and TailSecond.lean (needs the PNT+ closure below)
```

One-time setup for the PNT+ closure (same Mathlib commit as leancert, so no download):

```sh
cd ~/research/formalizations/PrimeNumberTheoremAnd
git fetch https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git main
git worktree add --detach ../round2/.deps/pnt435 127b50e5
cd ../round2/.deps/LeanArchitect
git fetch origin 9f3bb53916b9d6fa05b7777389e1844f82b1c9a6
git worktree add --detach ../arch435 9f3bb53916b9d6fa05b7777389e1844f82b1c9a6
cd .. && export BASE_LEAN_PATH="$(cd ~/research/leancert && lake env printenv LEAN_PATH)" \
  LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
for m in PrimeNumberTheoremAnd.Consequences PrimeNumberTheoremAnd.MediumPNT; do
  python3 leanc.py $PWD/build-upstream-435 $m $PWD/pnt435,$PWD/arch435; done
```

`lakefile.toml` records the same dependencies for an ordinary `lake build`.

## Layout

| Module | Paper |
|---|---|
| `InfiniteProduct` | tprod foundations for infinite exponent sets, dominated convergence |
| `Basic` | §1 definitions: `Fc`, `qProdSet`, `IsPrimitive`, `blockE`, `Hfun`, `Lfun`, `compressAt` |
| `Endpoint` | Lemma 2.2; degree-18 Bernstein certificate (alternative to Lemma 2.1, not in the paper) |
| `SingleCrossing` | Lemma 2.1, abstract single-crossing lemma, Theorem 1.4 for `H` |
| `UniversalInequality` | Theorem 1.4 (finite and arbitrary `T`), Remark 2.3 |
| `Transport` | §3: weighted running positivity, power substitution, Proposition 3.4 (any integer `p ≥ 1`) |
| `Extremal` | §4: Theorems 1.1 and 1.2 |
| `Ambient` | §4.1: Theorem 4.1, extremality of `Min(U)` over primitive subsets of any `U` |
| `Consequences` | Proposition 1.3, Remark 4.4 increasing-concave minimality (finite), polynomial tail bound `R = {2}` (not in the paper), open problem 2 data |
| `Moments` | real-order moments for `k ∈ [1,2]`, finite sets (superseded by `MomentsSmall`) |
| `Lambda` | Λ enclosures, 26-digit sandwich |
| `Qfun`, `ProductCont` | `Q = ∏_p(1-xᵖ)`; continuity of every `P_A` on `[0,1]` |
| `PrimeCrossing` | Remark 4.4: single crossing of `Q - (1-x)`, `J_s(z) > 0` from `J_b(1) > 0` |
| `MomentCert` | Remark 4.4: exact certificate `J_{17/8}(1) > 0`, `J_3(1) ≤ -23/8580` |
| `MomentsWeight` | weighted positivity against `P_B`, power substitution with real weight, `v = uᵖ` |
| `MomentsReal` | Remark 4.4, moments for `1 ≤ k ≤ 17/4`: real block exchange, primitive quotient blocks, bootstrap |
| `MomentsSmall` | Remark 4.4, moments for `0 < k ≤ 1`, the full range `0 < k ≤ 17/4`, and the general form `k ≤ 2b` when `J_b(1) > 0` |
| `Stability` | Proposition 5.7 (omitting a prime: minimizer `B_p`, cost `D_c(p)`), Corollary 5.8 |
| `StabilitySaddle` | Proposition 5.9: `M_p ≤ -log Δ₁(p) ≤ M_p + log p + 3`, asymptotic under `θ ~ id` |
| `Tail/Defs`, `Tail/PrimeSums` | §5.2 definitions; Lemma 5.1 (`θ ~ x` ⇒ exponential prime sums), primes in `(N, (1+ε)N]` |
| `Tail/Phi` | Lemma 5.2 (`t log(1/t) Φ(t) → ζ(2)`) |
| `Tail/Sandwich`, `Tail/Laplace` | Lemma 5.3 (unconditional sandwich of `I_N - Λ` by `Φ`) |
| `TailAsymptotic` | Theorem 1.5 under the hypotheses `θ ~ id` (and `p_n ~ n log n`) |
| `Tail/Defs2` | §5.5 interfaces: `ThetaErrLog2`, `ExpSumExpansion`, `PhiExpansion`, `tailLam`, `tailShape`, `tailErr` |
| `Tail/ExpSum2` | Theorem 5.10, step 1: `S(u) = (1+γ/L)/(uL) + O(1/(uL³))` under `θ(x) = x + O(x/log² x)` |
| `Tail/Phi2` | Theorem 5.10, step 2: `Φ(t) = a(1+κ/L)/(tL) + O(1/(tL³))`; `Σ log m/m² = -ζ'(2)` |
| `Tail/Saddle2` | Theorem 5.10, step 3 / Lemma A.1: second-order saddle bounds for `N t + Φ(t)` |
| `Tail/Second` | Theorem 5.10, step 4: primes in `(N, N + KN/log² N]`, transfer to `-log(I_N - Λ)` |
| `Tail/QuantPNT` | `θ(x) = x + O(x/log² x)` from PNT+ `MediumPNT` |
| `TailSecond` | Theorem 5.10 unconditionally (`tail_second_order_pnt`) |
| `PNT` | Theorem 1.5 and the asymptotic of Proposition 5.9 unconditionally, via PrimeNumberTheoremAnd |

`RntPaper.lean` imports everything that does not need PrimeNumberTheoremAnd.

## Paper results → Lean declarations

Numbering follows the current `../main.tex`.

| Result | Declaration | File (under `RntPaper/`) |
|---|---|---|
| Thm 1.1 | `Fc_primesLE_lt` | `Extremal.lean` |
| Thm 1.2 | `Lfun_le_FcSet`, `Lfun_lt_FcSet` | `Extremal.lean` |
| Prop 1.3 | `pointwise_failure` | `Consequences.lean` |
| Thm 1.4 | `running_pos_set` | `UniversalInequality.lean` |
| Lem 2.1 | `single_crossing` | `SingleCrossing.lean` |
| Lem 2.2 | `endpoint_estimate` | `Endpoint.lean` |
| Bernstein certificate (not in paper) | `Qtilde_pos` | `Endpoint.lean` |
| Prop 3.4 | `block_exchange_lt_set` | `Transport.lean` |
| Thm 4.1 | `Fc_minLE_lt`, `FcSet_minElems_lt`, `minElems_ge_two` | `Ambient.lean` |
| Rem 4.4, increasing-concave (finite) | `icv_minimality` | `Consequences.lean` |
| Rem 4.4, moments `0 < k ≤ 17/4` | `moment_primesLE_lt`, `moment_primes_lt`, `moment_primes_lt_of_Jw` | `MomentsSmall.lean` |
| Rem 4.4, weighted crossing | `Qfun_single_crossing`, `Jw_pos_of` | `PrimeCrossing.lean` |
| Rem 4.4, `J_{17/8}(1) > 0`, `J_3(1) < 0` | `moment_cert`, `Jw_three_neg` | `MomentCert.lean`, `MomentsSmall.lean` |
| Polynomial tail bound, `R = {2}` (not in paper) | `tail_bound` | `Consequences.lean` |
| §5.1, 26 digits of Λ | `primeLambda_digits26` | `Lambda.lean` |
| Lem 5.1 | `primeLogExpSum_asymp`, `primeExpSum_asymp` | `Tail/PrimeSums.lean` |
| Lem 5.2 | `primePhi_asymp` | `Tail/Phi.lean` |
| Lem 5.3 | `tail_le_of_primePhi`, `tail_ge_of_window` | `Tail/Laplace.lean` |
| Thm 1.5 | `tail_asymptotic_pnt`, `tail_asymptotic_nth_pnt` | `PNT.lean` |
| Prop 5.7 | `FcSet_omitSet_lt`, `FcSet_omitSet_eq` | `Stability.lean` |
| Cor 5.8 | `omitCost_le_FcSet_sub`, `eq_primes_of_lt`, `tendsto_FcSet_iff` | `Stability.lean` |
| Prop 5.9 | `saddleMin_le_neg_log_omitMoment`, `neg_log_omitMoment_le_saddleMin` | `StabilitySaddle.lean` |
| Prop 5.9, asymptotic | `omitMoment_asymptotic_pnt` | `PNT.lean` |
| Thm 5.10 | `tail_second_order_pnt` | `TailSecond.lean` |
| Lem A.1 | `saddle_second_order` | `Tail/Saddle2.lean` |

