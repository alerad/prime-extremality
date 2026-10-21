import RntPaper.InfiniteProduct

/-!
# The prime product `Q(x) = ∏_p (1 - xᵖ)` as a function

Shared name for the integrand of `𝓛`, used by the stability and moment modules.
-/

namespace RntPaper

open QProduct MeasureTheory Set

/-- `Q(x) = ∏_p (1 - xᵖ)`, the integrand of `𝓛` (paper Theorem 1.2). -/
noncomputable def Qfun (x : ℝ) : ℝ := qProdSet Primes x

theorem FcSet_primes_eq (c : ℝ) : FcSet c Primes = ∫ x in (0 : ℝ)..c, Qfun x := rfl

theorem Lfun_eq_integral_Qfun (c : ℝ) : Lfun c = ∫ x in (0 : ℝ)..c, Qfun x := by
  rw [← FcSet_primes c]; rfl

end RntPaper
