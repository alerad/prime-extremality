import RntPaper.InfiniteProduct
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ZetaValues

/-!
# Tail asymptotics of `Λ`: definitions (blueprint `OP3_PLAN.md`)
-/

namespace RntPaper

open QProduct Real Filter Topology Asymptotics MeasureTheory Set

/-! ## Exponential prime sums -/

/-- `S(u) = ∑_p e^{-pu}`. -/
noncomputable def primeExpSum (u : ℝ) : ℝ :=
  ∑' p : Nat.Primes, rexp (-((p : ℝ) * u))

/-- `W(u) = ∑_p log p · e^{-pu}`. -/
noncomputable def primeLogExpSum (u : ℝ) : ℝ :=
  ∑' p : Nat.Primes, Real.log p * rexp (-((p : ℝ) * u))

/-- `Φ(t) = ∑_p -log(1 - e^{-pt}) = -log ∏_p (1 - e^{-pt})`. -/
noncomputable def primePhi (t : ℝ) : ℝ :=
  ∑' p : Nat.Primes, -Real.log (1 - rexp (-((p : ℝ) * t)))

end RntPaper
