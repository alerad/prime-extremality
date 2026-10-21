import RntPaper.TailAsymptotic
import RntPaper.StabilitySaddle
import PrimeNumberTheoremAnd.Consequences

/-!
# Discharging the PNT hypotheses with PrimeNumberTheoremAnd

`RntPaper.TailAsymptotic` assumes `θ ~ id` (and `p_n ~ n log n` for the
`n`-form). PrimeNumberTheoremAnd proves both (`chebyshev_asymptotic`,
`nth_prime_asymp`); this file is the only place that imports it.
-/

namespace RntPaper

open QProduct Real Filter Topology

/-- Open problem 3, unconditionally: `-log(I_N - Λ) ~ 2π √(N / (3 log N))`. -/
theorem tail_asymptotic_pnt :
    Tendsto (fun N : ℕ => -Real.log (F (primesLE N) - primeLambda) / √(N / Real.log N))
      atTop (𝓝 (2 * π / √3)) :=
  tail_asymptotic chebyshev_asymptotic

/-- Open problem 3 as posed in the paper: `-log(J_n - Λ) ~ (2π/√3) √n`. -/
theorem tail_asymptotic_nth_pnt :
    Tendsto (fun n : ℕ => -Real.log (F (primesLE (Nat.nth Nat.Prime n)) - primeLambda) / √n)
      atTop (𝓝 (2 * π / √3)) :=
  tail_asymptotic_nth chebyshev_asymptotic nth_prime_asymp

/-- Stability threshold, unconditionally: `-log Δ₁(p) ~ 2π √(p / (3 log p))`, where
`Δ₁(p) = ∫₀¹ xᵖ Q(x) dx` is the least excess `F₁(A) - Λ` forced by omitting `p`. -/
theorem omitMoment_asymptotic_pnt :
    Tendsto (fun p : ℕ => -Real.log (omitMoment p 1) / √(p / Real.log p))
      atTop (𝓝 (2 * π / √3)) :=
  omitMoment_asymptotic chebyshev_asymptotic

end RntPaper
