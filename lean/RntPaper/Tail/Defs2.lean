import RntPaper.Tail.Defs

/-!
# Second-order tail asymptotics: shared definitions (paper §5.5)

Interfaces between the modules proving
`-log(I_N - Λ) = λ_N [1 - log ℓ/(2ℓ) + C/ℓ + O((log ℓ/ℓ)²)]`, `ℓ = log N`:

* `ThetaErrLog2`: the analytic input `θ(x) = x + O(x / log² x)` (a consequence of the prime
  number theorem with classical error term, discharged from PrimeNumberTheoremAnd);
* `ExpSumExpansion g`: `S(u) = (1 + g/L)/(uL) + O(1/(uL³))`, `L = log(1/u)`;
* `PhiExpansion Φ a κ`: `Φ(t) = a(1 + κ/L)/(tL) + O(1/(tL³))`, `L = log(1/t)`;
* `tailLam`, `tailShape`, `tailErr`: the main term, the second-order shape, and the error scale.
-/

namespace RntPaper

open Real

/-- Quantitative prime number theorem: `|θ(x) - x| ≤ K x / log² x` for `x ≥ 2`. -/
def ThetaErrLog2 : Prop :=
  ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ K * x / Real.log x ^ 2

/-- Second-order expansion of `S(u) = ∑_p e^{-pu}` with constant `g`. -/
def ExpSumExpansion (g : ℝ) : Prop :=
  ∃ K u₁ : ℝ, 0 < u₁ ∧ u₁ < 1 ∧ ∀ u : ℝ, 0 < u → u < u₁ →
    |primeExpSum u - (1 + g / (-Real.log u)) / (u * (-Real.log u))| ≤
      K / (u * (-Real.log u) ^ 3)

/-- Second-order expansion of a function `Φ` near `0`, with constants `a` and `κ`. -/
def PhiExpansion (Φ : ℝ → ℝ) (a κ : ℝ) : Prop :=
  ∃ K t₀ : ℝ, 0 < t₀ ∧ t₀ < 1 ∧ ∀ t : ℝ, 0 < t → t < t₀ →
    |Φ t - a * (1 + κ / (-Real.log t)) / (t * (-Real.log t))| ≤
      K / (t * (-Real.log t) ^ 3)

/-- `σ = ∑_{m ≥ 1} log m / m² = -ζ'(2)`. -/
noncomputable def logSqSum : ℝ := ∑' m : ℕ, Real.log m / (m : ℝ) ^ 2

/-- `κ = γ + σ/ζ(2) = γ - ζ'(2)/ζ(2)`. -/
noncomputable def tailKappa : ℝ := eulerMascheroniConstant + logSqSum / (π ^ 2 / 6)

/-- `λ = 2 √(2 a N / log N)`; for `a = ζ(2)` this is `2π √(N / (3 log N))`. -/
noncomputable def tailLam (a N : ℝ) : ℝ := 2 * √(2 * a * N / Real.log N)

/-- `1 - log ℓ / (2ℓ) + (κ + ½ log(2a)) / ℓ`, `ℓ = log N`. -/
noncomputable def tailShape (a κ N : ℝ) : ℝ :=
  1 - Real.log (Real.log N) / (2 * Real.log N) + (κ + Real.log (2 * a) / 2) / Real.log N

/-- `(log ℓ / ℓ)²`, `ℓ = log N`. -/
noncomputable def tailErr (N : ℝ) : ℝ := (Real.log (Real.log N) / Real.log N) ^ 2

end RntPaper
