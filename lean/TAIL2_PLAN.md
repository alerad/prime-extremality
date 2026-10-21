# Blueprint: second-order tail asymptotics (paper §5.5)

Target, unconditional modulo PrimeNumberTheoremAnd's `MediumPNT`:

    D_N := -log(I_N - Λ) = λ_N [ 1 - log ℓ/(2ℓ) + C/ℓ + O((log ℓ/ℓ)²) ],
    ℓ = log N,  λ_N = 2√(2aN/ℓ) = 2π√(N/(3ℓ)),  a = ζ(2) = π²/6,
    C = κ + ½ log(2a),  κ = γ + σ/a,  σ = Σ_{m≥1} log m / m² = -ζ'(2).

The interfaces are in `RntPaper/Tail/Defs2.lean` (`ThetaErrLog2`, `ExpSumExpansion`,
`PhiExpansion`, `logSqSum`, `tailKappa`, `tailLam`, `tailShape`, `tailErr`).

Module graph:

    Tail/Defs2 ── Tail/ExpSum2 (B) ── Tail/Phi2 (C) ── Tail/Second (E) ── PNT (bridge)
             └─── Tail/Saddle2 (D) ─────────────────────┘

Throughout, `L = -log u` (or `-log t`), and all statements are for small `u, t`.

## B. `Tail/ExpSum2.lean`: `theorem primeExpSum_expansion (hθ : ThetaErrLog2) :
##     ExpSumExpansion Real.eulerMascheroniConstant`

Let g(x) = e^{-xu}/log x, which is positive and decreasing on [2,∞).

1. **Abel summation.** Since θ(n) - θ(n-1) = log n · [n prime] and θ(1) = 0,
   Σ_{n=2}^{M} (θ(n)-θ(n-1)) g(n) = θ(M) g(M) - Σ_{n=2}^{M-1} θ(n)(g(n+1) - g(n)).
   Also θ(M) g(M) ≤ M log 4 · e^{-Mu} → 0. Hence
   S(u) = Σ_{n≥2} θ(n)(g(n) - g(n+1)), a series of nonnegative terms.
   (`Tail/PrimeSums.lean` already does a discrete Abel summation for W(u); reuse its style
   and the lemmas `theta_nat`, `theta_succ`.)
2. Write θ(n) = n + E(n) with |E(n)| ≤ K n / log² n.
   - **Main part.** Σ_{n≥2} n(g(n) - g(n+1)) = 2g(2) + Σ_{n≥3} g(n), by telescoping;
     the boundary term M g(M+1) → 0.
   - **Sum vs integral.** For decreasing positive g:
     ∫_2^∞ g ≤ Σ_{n≥2} g(n) ≤ g(2) + ∫_2^∞ g, and g(2) ≤ 1/log 2.
     Mathlib has `AntitoneOn.integral_le_sum` / `AntitoneOn.sum_le_integral` on finite
     ranges; pass to the limit.
   - **Error part.** 0 ≤ g(n) - g(n+1) ≤ e^{-nu}/(n log² n) + u e^{-nu}/log n.
     This uses 1/log n - 1/log(n+1) ≤ 1/(n log² n) and 1 - e^{-u} ≤ u. Hence
     |Σ E(n)(g(n)-g(n+1))| ≤ K Σ_{n≥2} [ e^{-nu}/log⁴ n + (nu) e^{-nu}/log³ n ].
3. **Bounding lemma.** For j ∈ {0,1}, k ≥ 1 and 0 < u ≤ 1:
   Σ_{n≥2} (nu)^j e^{-nu}/log^k n ≤ u^{-1/2}/log^k 2 + 4·2^k/(u L^k).
   Split at n ≤ u^{-1/2}, where each term is ≤ 1/log^k 2, versus n > u^{-1/2}, where
   log n ≥ L/2. Use Σ e^{-nu} ≤ 1/u and u Σ n e^{-nu} ≤ 4/u for u ≤ 1.
   Since u^{1/2} L^3 → 0, the first term is ≤ C/(uL³) for small u.
4. **The integral.** I(u) = ∫_2^∞ e^{-xu}/log x dx = (1/u) ∫_{2u}^∞ e^{-y}/(L + log y) dy.
   For y ≥ 2u (so L + log y ≥ log 2 > 0):
   1/(L+log y) = 1/L - log y/L² + log² y /(L² (L + log y)). Then:
   - ∫_{2u}^∞ e^{-y} = e^{-2u} ∈ [1-2u, 1];
   - ∫_{2u}^∞ e^{-y} log y = -γ - ∫_0^{2u} e^{-y} log y, and the last integral is at most
     ∫_0^{2u} |log y| = O(u L) in absolute value;
   - ∫_{2u}^∞ e^{-y} log² y/(L+log y): for y ≥ √u, L + log y ≥ L/2, giving
     ≤ (2/L) ∫_0^∞ e^{-y} log² y; for 2u ≤ y ≤ √u, giving ≤ √u L²/log 2.
   Hence |u I(u) - 1/L - γ/L²| ≤ C/L³ for small u.
   **γ input:** `Real.eulerMascheroniConstant_eq_neg_deriv : γ = -deriv Gamma 1`
   (Mathlib.NumberTheory.Harmonic.GammaDeriv), together with `Complex.hasDerivAt_GammaIntegral`
   (Mathlib.Analysis.SpecialFunctions.Gamma.Deriv), which gives
   ∫_0^∞ e^{-y} log y dy = Γ'(1) = -γ. Integrability of e^{-y} log² y on (0,∞) is also needed.
5. Collect: S(u) = I(u) + O(1) + O(1/(uL³)), and O(1) ≤ 1/(uL³) for small u.

## C. `Tail/Phi2.lean`: `theorem primePhi_expansion {g : ℝ} (hS : ExpSumExpansion g) :
##     PhiExpansion primePhi (π ^ 2 / 6) (g + logSqSum / (π ^ 2 / 6))`

Inputs: `primePhi_eq_tsum : primePhi t = ∑' m : ℕ, primeExpSum (m * t) / m` (the m = 0 term
is 0); `phi_primeExpSum_le_inv : primeExpSum u ≤ 1/u`; `hasSum_zeta_two`.

Let M1 = ⌊t^{-1/2}⌋, so for m ≤ M1, mt ≤ √t < u₁ and L_m := L - log m ≥ L/2.
- **m > M1.** 0 ≤ Σ_{m>M1} S(mt)/m ≤ Σ_{m>M1} 1/(m² t) ≤ 1/(t M1) = O(t^{-1/2}) = o(1/(tL³)).
  The corresponding tails of the main-term series are also o(1/(tL³)).
- **m ≤ M1.** S(mt)/m = (1/(m² t)) (1/L_m)(1 + g/L_m) + O(K/(m² t L_m³)). Expand:
  - 1/L_m = 1/L + log m/L² + log² m/(L² L_m) = 1/L + log m/L² + O(log² m/L³);
  - 1/L_m² = 1/L² + O(log m/L³), using L_m ≥ L/2;
  - 1/L_m³ ≤ 8/L³.

  So S(mt)/m = (1/(m² t))[1/L + (g + log m)/L²] + O((1 + log m + log² m)/(m² t L³)).
- **Sums.** Σ_{m≤M1} 1/m² = a - O(1/M1); Σ_{m≤M1} log m/m² = σ - O(M1^{-1/2});
  Σ (1 + log m + log² m)/m² < ∞. Use log m ≤ 2√m to get tails such as
  Σ_{m>M} log m/m² ≤ 4/√M.
- **Result.** Φ(t) = (1/t)[a/L + (g a + σ)/L²] + O(1/(tL³)) = a(1 + κ/L)/(tL) + O(1/(tL³)),
  with κ = g + σ/a.

Optional: `logSqSum = -(deriv riemannZeta 2).re`, for the paper's form with -ζ'(2)/ζ(2).

## D. `Tail/Saddle2.lean`: abstract saddle analysis

    theorem saddle_second_order {Φ : ℝ → ℝ} {a κ : ℝ} (ha : 0 < a)
        (hanti : ∀ s t, 0 < s → s ≤ t → Φ t ≤ Φ s) (hnonneg : ∀ t, 0 < t → 0 ≤ Φ t)
        (hΦ : PhiExpansion Φ a κ) :
        ∃ K : ℝ, ∀ᶠ N : ℝ in atTop,
          (∀ t : ℝ, 0 < t → tailLam a N * (tailShape a κ N - K * tailErr N) ≤ N * t + Φ t) ∧
          ∃ τ : ℝ, 1 / N ≤ τ ∧ τ ≤ 1 ∧ N * τ ≤ tailLam a N ∧
            N * τ + Φ τ ≤ tailLam a N * (tailShape a κ N + K * tailErr N)

Parametrize t = e^{-u}, so L = u, and put c(u) = (a/u)(1 + κ/u). Then
Φ(e^{-u}) = c(u) e^u + O(e^u/u³). Choose the explicit reference point

    u0 = ½ (ℓ + log ℓ - log(2a)),   so e^{2u0} = Nℓ/(2a),

and set α = N e^{-u0}, β = c(u0) e^{u0}, m = 2√(αβ) = 2√(N c(u0)).

- **Expansion of m.** u0 = (ℓ/2)(1 + (log ℓ - log 2a)/ℓ), hence
  u0^{-1/2} = √(2/ℓ)(1 - (log ℓ - log 2a)/(2ℓ) + O((log ℓ/ℓ)²)), and
  √(1+κ/u0) = 1 + κ/ℓ + O(log ℓ/ℓ²). Therefore
  m = 2√(Na/u0) √(1+κ/u0) = λ_N [1 - log ℓ/(2ℓ) + (κ + ½ log 2a)/ℓ + O((log ℓ/ℓ)²)].
  Also α/β = (2u0/ℓ)/(1+κ/u0) = 1 + O(log ℓ/ℓ), so v* := ½ log(α/β) = O(log ℓ/ℓ).
- **Upper bound.** Take τ = e^{-u0}. Then
  Nτ + Φ(τ) ≤ α + β(1 + K'/u0²) = m + (√α - √β)² + βK'/u0², and
  (√α - √β)² = β(√(α/β) - 1)² = β·O((log ℓ/ℓ)²). This gives the upper bound.
  The side conditions 1/N ≤ τ ≤ 1 and Nτ = α ≤ λ_N hold for large N.
- **Lower bound for all t > 0.** Write t = e^{-(u0+v)}, so that
  Nt + Φ(t) ≥ α e^{-v} + β ρ(v) e^{v}, where Φ(t) ≥ c⁻(u0+v) e^{u0+v}, c⁻ = c - K/u³, and
  ρ(v) = c⁻(u0+v)/c(u0).
  - t ≥ t₀: Nt + Φ(t) ≥ N t₀ ≥ λ_N·2 for large N, using Φ ≥ 0.
  - t < t₀ and v ≤ 0: the function u ↦ (1/u)(1 + κ/u - K/u²) is decreasing for u ≥ U
    (choose t₀ ≤ e^{-U}), so ρ(v) ≥ 1 - K''/u0². AM–GM gives
    α e^{-v} + βρ e^{v} ≥ 2√(αβ(1 - K''/u0²)) ≥ m(1 - K''/u0²).
  - 0 ≤ v ≤ 2: ρ(v) ≥ 1 - v/u0 - (|κ| v + K)/u0². The bound
    e^{w} + e^{-w} ≥ 2 + w²/2 with w = v - v* gives
    α e^{-v} + β e^{v} ≥ m + (m/4)(v - v*)². So
    Nt + Φ(t) ≥ m + (m/4)(v-v*)² - β e² (v/u0 + C/u0²)
             ≥ m - β e² v*/u0 - O(β/u0²)
    after minimizing the quadratic in v. This is m(1 - O((log ℓ/ℓ)²)).
  - v ≥ 2: since Φ is antitone, Φ(t) ≥ Φ(e^{-(u0+2)}) ≥ c⁻(u0+2) e^{u0+2} ≈ e² β ≥ m
    for large N.
  Combine with the expansion of m.

## E. `Tail/Second.lean` (assembly) and the PNT bridge

- **Prime in a short interval.** From `ThetaErrLog2`:
  ∃ K, ∀ᶠ N : ℕ, ∃ q prime, N < q ∧ q ≤ N + K N/ℓ².
  Indeed θ(N+h) - θ(N) ≥ h - K'(N+h)/log² N·2 > 0 for h = 3K'N/ℓ².
- **Lower bound.** `tail_le_of_primePhi` with B = λ(shape - K err) gives
  D_N ≥ B - 1 - 2 log N.
- **Upper bound.** `tail_ge_of_window` with q, τ from D, ε = 1/ℓ², and A = Φ(τ)
  (Φ is antitone). This gives D_N ≤ Φ(τ) + q(1+ε)τ + τ + log((1+ετ)/(ετ)), and
  (q(1+ε) - N)τ ≤ Nτ·O(1/ℓ²) ≤ λ_N·O(1/ℓ²).
- The log N terms are o(λ_N (log ℓ/ℓ)²).
- **Bridge.** `MediumPNT` gives (ψ - id) = O(x exp(-c (log x)^{1/10})).
  Mathlib's `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` gives ψ - θ = O(√x log x).
  Both are O(x/log² x), which yields `ThetaErrLog2`.
