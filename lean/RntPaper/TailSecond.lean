import RntPaper.Tail.QuantPNT
import RntPaper.Tail.ExpSum2
import RntPaper.Tail.Phi2
import RntPaper.Tail.Saddle2
import RntPaper.Tail.Second

/-!
# Theorem 5.10: second-order tail asymptotics, unconditionally

With `ℓ = log N`, `λ_N = 2π√(N/(3ℓ))`, and `C = γ - ζ'(2)/ζ(2) + ½ log(2ζ(2))`,

  `-log(I_N - Λ) = λ_N (1 - log ℓ/(2ℓ) + C/ℓ + O((log ℓ/ℓ)²))`.

The only arithmetic input is PrimeNumberTheoremAnd's `MediumPNT`, through
`thetaErrLog2_of_mediumPNT`.
-/

namespace RntPaper

open QProduct Real Filter

/-- The second-order expansion under `θ(x) = x + O(x/log² x)`. -/
theorem tail_second_order (hθ : ThetaErrLog2) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop,
      |-Real.log (F (primesLE N) - primeLambda) -
          tailLam (π ^ 2 / 6) N * tailShape (π ^ 2 / 6) tailKappa N| ≤
        K * (tailLam (π ^ 2 / 6) N * tailErr N) :=
  tail_second_order_of (by positivity) hθ
    (saddle_second_order (by positivity) (fun _ _ hs hst => primePhi_anti hs hst)
      (fun _ ht => primePhi_nonneg ht)
      (primePhi_expansion (primeExpSum_expansion hθ)))

/-- **Theorem 5.10**, unconditionally (via `MediumPNT`). -/
theorem tail_second_order_pnt :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop,
      |-Real.log (F (primesLE N) - primeLambda) -
          tailLam (π ^ 2 / 6) N * tailShape (π ^ 2 / 6) tailKappa N| ≤
        K * (tailLam (π ^ 2 / 6) N * tailErr N) :=
  tail_second_order thetaErrLog2_of_mediumPNT

/-- The constants in the paper's form: `λ = 2π√(N/(3ℓ))` and
`κ = γ - ζ'(2)/ζ(2)`. -/
theorem tailLam_zeta_two (N : ℝ) (hℓ : 0 ≤ Real.log N) (hN : 0 ≤ N) :
    tailLam (π ^ 2 / 6) N = 2 * π * √(N / (3 * Real.log N)) := by
  unfold tailLam
  rw [show 2 * (π ^ 2 / 6) * N / Real.log N = π ^ 2 * (N / (3 * Real.log N)) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq pi_pos.le]
  ring

theorem tailKappa_eq : tailKappa =
    eulerMascheroniConstant - (deriv riemannZeta 2).re / (π ^ 2 / 6) := by
  rw [tailKappa, logSqSum_eq_neg_deriv_riemannZeta]
  ring

end RntPaper
