import RntPaper.Tail.Defs2
import PrimeNumberTheoremAnd.MediumPNT

/-!
# `θ(x) = x + O(x / log² x)` from PrimeNumberTheoremAnd

`MediumPNT` gives `ψ(x) = x + O(x exp(-c (log x)^{1/10}))`, and Mathlib gives
`|ψ(x) - θ(x)| ≤ 2 √x log x`. Both error terms are `O(x / log² x)`.
-/

namespace RntPaper

open Real Filter Asymptotics Topology

/-- Eventually `log² x · e^{-c (log x)^{1/10}} ≤ 1`. -/
theorem qpnt_log_sq_exp_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) ≤ 1 := by
  have hs : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  have h20 := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 20).comp
    ((hs.const_mul_atTop hc))
  have hc20 : (0 : ℝ) < c ^ 20 := by positivity
  filter_upwards [h20.eventually (gt_mem_nhds hc20), tendsto_log_atTop.eventually_ge_atTop 0]
    with x hx hℓ
  simp only [Function.comp] at hx
  set s := Real.log x ^ ((1 : ℝ) / 10) with hsdef
  have hs0 : 0 ≤ s := Real.rpow_nonneg hℓ _
  have hℓs : Real.log x ^ 2 = s ^ 20 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hℓ]
    norm_num
  rw [hℓs]
  have h1 : (c * s) ^ 20 * Real.exp (-(c * s)) = c ^ 20 * (s ^ 20 * Real.exp (-c * s)) := by
    rw [mul_pow, neg_mul]; ring
  rw [h1] at hx
  have := (mul_lt_mul_iff_right₀ hc20).mp (by linarith : c ^ 20 * (s ^ 20 * Real.exp (-c * s)) <
    c ^ 20 * 1)
  exact this.le

/-- Eventually `log³ x ≤ √x`. -/
theorem qpnt_log_cube_le_sqrt : ∀ᶠ x : ℝ in atTop, Real.log x ^ 3 ≤ √x := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  calc Real.log x ^ 3 ≤ (x ^ (1 / 6 : ℝ)) ^ 3 := pow_le_pow_left₀ (Real.log_nonneg hx1) hx 3
    _ = √x := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num

/-- **Quantitative PNT input.** `|θ(x) - x| ≤ K x / log² x` for all `x ≥ 2`. -/
theorem thetaErrLog2_of_mediumPNT : ThetaErrLog2 := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hC⟩ := hO.bound
  -- eventually `|θ x - x| ≤ (|C| + 2) x / log² x`
  have hev : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ (|C| + 2) * x / Real.log x ^ 2 := by
    filter_upwards [hC, qpnt_log_sq_exp_le hc, qpnt_log_cube_le_sqrt,
      eventually_ge_atTop 3] with x hCx hexp hcube hx3
    have hx0 : 0 < x := by linarith
    have hℓ1 : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hℓ0 : 0 < Real.log x := by linarith
    set ℓ := Real.log x with hℓdef
    set E := Real.exp (-c * ℓ ^ ((1 : ℝ) / 10)) with hE
    have hE0 : 0 < E := exp_pos _
    simp only [Pi.sub_apply, id, Real.norm_eq_abs] at hCx
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ x * E)] at hCx
    have hpt := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : (1 : ℝ) ≤ x)
    -- `x E ≤ x / ℓ²` and `2 √x ℓ ≤ 2 x / ℓ²`
    have h1 : x * E ≤ x / ℓ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc x * E * ℓ ^ 2 = x * (ℓ ^ 2 * E) := by ring
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hexp hx0.le
        _ = x := mul_one x
    have h2 : 2 * √x * ℓ ≤ 2 * x / ℓ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have hsx : √x * √x = x := Real.mul_self_sqrt hx0.le
      have := mul_le_mul_of_nonneg_left hcube (Real.sqrt_nonneg x)
      nlinarith
    have hCabs : C * (x * E) ≤ |C| * (x / ℓ ^ 2) :=
      (le_abs_self C).trans' le_rfl |>.trans' le_rfl |> fun _ =>
        mul_le_mul (le_abs_self C) h1 (by positivity) (abs_nonneg C)
    have htri : |Chebyshev.theta x - x| ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
      have := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
      rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at this
      linarith
    have : (|C| + 2) * x / ℓ ^ 2 = |C| * (x / ℓ ^ 2) + 2 * x / ℓ ^ 2 := by ring
    rw [this]
    linarith
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
  -- on `[2, x₀]` use `|θ x - x| ≤ (log 4 + 1) x`
  set X := max x₀ 3 with hX
  have hX3 : 3 ≤ X := le_max_right _ _
  refine ⟨max (|C| + 2) ((Real.log 4 + 1) * Real.log X ^ 2), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hℓ0 : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hxX : x₀ ≤ x
  · refine (hx₀ x hxX).trans ?_
    gcongr
    exact le_max_left _ _
  · push Not at hxX
    have hxX' : x ≤ X := (le_of_lt hxX).trans (le_max_left _ _)
    have hθ := Chebyshev.theta_le_log4_mul_x hx0.le
    have hθ0 := Chebyshev.theta_nonneg x
    have hb : |Chebyshev.theta x - x| ≤ (Real.log 4 + 1) * x := by
      rw [abs_le]; constructor <;> nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    have hlogX : Real.log x ^ 2 ≤ Real.log X ^ 2 :=
      pow_le_pow_left₀ hℓ0.le (Real.log_le_log hx0 hxX') 2
    refine hb.trans ?_
    rw [le_div_iff₀ (by positivity)]
    calc (Real.log 4 + 1) * x * Real.log x ^ 2 ≤ (Real.log 4 + 1) * x * Real.log X ^ 2 := by
          gcongr
      _ = (Real.log 4 + 1) * Real.log X ^ 2 * x := by ring
      _ ≤ max (|C| + 2) ((Real.log 4 + 1) * Real.log X ^ 2) * x := by
          gcongr
          exact le_max_right _ _

end RntPaper
