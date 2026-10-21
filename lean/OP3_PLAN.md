# Theorem 1.6: tail asymptotics of Λ from the prime number theorem

**Status (2026-09-24): proved, zero `sorry`.** Formerly open problem 3 of the
paper; now Theorem 1.6 with the proof in paper §5.4 (Lemmas 5.3–5.5). It states
`-log(J_n - Λ) ~ (2π/√3)√n`, where `J_n = I_{p_n}` and
`I_N = ∫₀¹ ∏_{p≤N}(1-x^p) dx`. This file is the proof blueprint; the Lean
development is `RntPaper/Tail/*.lean`, `RntPaper/TailAsymptotic.lean` and
`RntPaper/PNT.lean` (build: `./op3-check.sh`).

## Statement

**Theorem.** Assume `θ(x) ~ x` (PNT). Then, with `a = ζ(2) = π²/6`,

    -log(I_N - Λ) ~ 2√(2aN / log N) = 2π √(N / (3 log N))     (N → ∞).

If also `p_n ~ n log n` (a PNT consequence), then `-log(J_n - Λ) ~ (2π/√3)√n`.

Both inputs come from PrimeNumberTheoremAnd (`chebyshev_asymptotic`,
`nth_prime_asymp`, both on `propext/choice/Quot.sound` only). In Lean the core
theorem takes `θ ~[atTop] id` (Mathlib's `Chebyshev.theta`) as a hypothesis, and
a bridge file discharges it with PNT+. Chebyshev bounds alone would give only
`-log(I_N - Λ) ≍ √(N/log N)`; PNT gives the constant.

Numerical check (`../supplement/tail_asymptotic_check.py`, floating point):
`-log(J_n - Λ)/√n = 3.513, 3.675, 3.719, 3.733, 3.728, 3.722` at
`n = 30, 100, 300, 1000, 2000, 4000` (target `3.6276`, approached slowly because of
`1/log` corrections). The measured value minus the saddle value
`M_N = min_t [N t + Φ(t)]` is `2.7 … 4.2`. Lemma 5.5(a) proves only
`-log(I_N - Λ) ≥ M_N - 2 log N - 1`; whether the difference is `O(log N)` in
both directions is paper open problem 3.

## Notation

For `t > 0`: `S(u) = Σ_p e^{-pu}`, `W(u) = Σ_p log p · e^{-pu}`,
`Φ(t) = Σ_p -log(1 - e^{-pt})` (so `Q(e^{-t}) = e^{-Φ(t)}`),
`L(t) = log(1/t)`, `P_N(x) = ∏_{p≤N}(1-x^p)`, `λ_N = 2√(2aN/log N)`.

## Lemma A (PNT ⇒ exponential prime sums)

(A1) `u W(u) → 1` as `u → 0⁺`.
Summation by parts: `W(u) = (1 - e^{-u}) Σ_{n≥1} θ(n) e^{-nu}` (`θ(n) ≤ n log 4`
gives convergence). For `n ≥ n₀(ε)`, `|θ(n) - n| ≤ εn`, and `Σ n e^{-nu} = e^{-u}/(1-e^{-u})²`;
the finitely many `n < n₀` contribute `O(1)`. Hence `u W(u) → 1`.

(A2) `u L(u) S(u) → 1`.
Upper: split at `y = u^{-(1-δ)}`. Primes `p ≤ y` contribute `≤ y = o(1/(uL))`, and
for `p > y`, `1 ≤ log p / ((1-δ) L(u))`, so the rest is `≤ W(u)/((1-δ)L(u))`.
Lower: for `Y = u^{-(1+δ)}`, `S(u) ≥ (W(u) - Σ_{n>Y} log n · e^{-nu}) / ((1+δ)L(u))`. The tail
is `≤ e^{-u^{-δ}/2} · O(u^{-2}) = o(1/u)`.

## Lemma B (`Φ(t) ~ a/(t L(t))`)

`Φ(t) = Σ_{k≥1} S(kt)/k` (Tonelli; nonnegative double series).
Lower: for fixed `K`, `Σ_{k≤K} S(kt)/k · tL(t) → Σ_{k≤K} 1/k²`, since
`L(kt)/L(t) → 1`. Let `K → ∞`.
Upper: use two bounds. (i) `S(u) ≤ 1/u` for all `u > 0`, since `S(u) ≤ Σ_{n≥1} e^{-nu} = 1/(e^u-1)`.
(ii) `S(u) ≤ C/(uL(u))` for `u ≤ u₀`, from (A2).
Split the sum over `k` into three ranges:
- `k ≤ K`: the limit gives `Σ_{k≤K} 1/k²`.
- `K < k ≤ t^{-1/2}`: here `L(kt) ≥ L(t)/2`, so the range contributes `≤ (2C/(tL(t))) Σ_{k>K} 1/k²`.
- `k > t^{-1/2}`: this range contributes `≤ Σ 1/(k² t) ≤ 2/√t = o(1/(tL(t)))`.

## Lemma C = paper Lemma 5.5 (unconditional sandwich)

Put `M_N = inf_{t>0} (N t + Φ(t))`.

(C1) `0 ≤ P_N - P_M ≤ P_N · min(1, x^{N+1}/(1-x))` for `M ≥ N`; integrating and
letting `M → ∞` gives `I_N - Λ ≤ sup_x P_N(x) min(1, x^{N+1}/(1-x))`
(`tail_le_of_forall`).
(C2) `e^{-Φ(t)} ≤ P_N(e^{-t}) ≤ exp(-Φ(t) + e^{-(N+1)t}/(1-e^{-t})²)`
(`exp_neg_primePhi_le_qProd`, `qProd_le_exp_neg_primePhi`).
(a) For `N ≥ 3`, `I_N - Λ ≤ e N² e^{-M_N}` (`tail_le_of_primePhi`): with
`s = 2 log N / N`, for `t ≥ s` the error term in (C2) is `≤ 1`, and
`1/(1-e^{-t}) ≤ N`, so the integrand is `≤ e N e^{-(Nt+Φ(t))}`; for `t < s` use
monotonicity of `P_N` and `Φ(s) ≥ M_N - 2 log N`.
(b) For a prime `q > N` and `Φ ≤ A` on `[τ, (1+ε)τ]`,
`I_N - Λ ≥ e^{-τ} (ετ/(1+ετ)) exp(-(A + q(1+ε)τ))` (`tail_ge_of_window`).

## Lemma D (asymptotic assembly, `TailAsymptotic.lean`)

Write `ℓ = log N`, `c = 2π/√3`, `a = ζ(2)` (`c² = 8a`), `r_N = √(N/ℓ)`, so
`λ_N = c r_N`. Fix `ε`, and `t₀` with `(1∓ε)a ≶ t L(t) Φ(t)` on `(0, t₀)`.

*Upper bound on `I_N - Λ`* (`saddle_lower`, `tail_upper_bound`). Show
`N t + Φ(t) ≥ κ c r_N + 2ℓ + 1` for all `t > 0`, then apply (a):
- `t ≥ t₀`: `N t ≥ N t₀`.
- `t < t₀` and `L(t) ≤ (½+ε)ℓ`: `(Nt + Φ)² ≥ 4 N t Φ ≥ 4N(1-ε)a/((½+ε)ℓ) ≥ (κ' c r_N)²`
  when `κ'²(1+2ε) ≤ 1-ε`.
- `L(t) > (½+ε)ℓ`: `t < t₁ = N^{-½-ε}`, so `Φ(t) ≥ Φ(t₁) ≥ (1-ε)a N^{½+ε}/((½+ε)ℓ)`
  (`Φ` is decreasing, `primePhi_anti`).
All eventual comparisons reduce to `ℓ² ≤ K e^{γℓ}` (`eventually_sq_le_exp`).

*Lower bound on `I_N - Λ`* (`window_lower`, `tail_lower_bound`). Take a prime
`q ∈ (N, (1+ε)N]` (`exists_prime_between`) and `τ = √(2a/(Nℓ))`, so `Nτ = c r_N/2`.
On the window, `L(t) ≥ (1-ε)ℓ/2`, so `Φ ≤ ((1+ε)/(1-ε)) Nτ`, and
`q(1+ε)τ ≤ (1+ε)² Nτ`; the prefactor is `≥ ε/(6N)`. Apply (b).

`tail_asymptotic` combines the two one-sided bounds.

## Corollary (n-form)

With `N = p_n ~ n log n` we have `log p_n ~ log n` and `p_n/log p_n ~ n`,
so `λ_{p_n} ~ (2π/√3)√n`.

## Lean layout

| Lemma | Lean | File |
|---|---|---|
| A1, A2 (paper 5.3) | `primeLogExpSum_asymp`, `primeExpSum_asymp` | `Tail/PrimeSums.lean` |
| primes in short intervals | `exists_prime_between` | `Tail/PrimeSums.lean` |
| B (paper 5.4) | `primePhi_asymp` | `Tail/Phi.lean` |
| C (paper 5.5) | `tail_le_of_forall`, `le_tail_of_window`, `tail_le_of_primePhi`, `tail_ge_of_window` | `Tail/Sandwich.lean`, `Tail/Laplace.lean` |
| D | `saddle_lower`, `window_lower`, `tail_upper_bound`, `tail_lower_bound`, `tail_asymptotic` | `TailAsymptotic.lean` |
| Cor | `nth_prime_div_log_tendsto`, `tail_asymptotic_nth` | `TailAsymptotic.lean` |
| bridge | `tail_asymptotic_pnt`, `tail_asymptotic_nth_pnt` | `PNT.lean` (PNT+ `chebyshev_asymptotic`, `nth_prime_asymp`) |
