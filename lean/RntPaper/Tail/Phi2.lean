import RntPaper.Tail.Defs2
import RntPaper.Tail.Phi
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Second-order expansion of `Φ` (blueprint `TAIL2_PLAN.md`, section C)

From `S(u) = (1 + g/L)/(uL) + O(1/(uL³))` we derive
`Φ(t) = a(1 + κ/L)/(tL) + O(1/(tL³))`, `a = π²/6`, `κ = g + σ/a`, `σ = ∑ log m/m²`.

Route: `Φ(t) = ∑_m S(mt)/m` and the main term `T_m = (1/(m²t))(1/L + (g + log m)/L²)` sums to
`a(1 + κ/L)/(tL)` exactly. Each difference `S(mt)/m - T_m` is bounded by
`C (1 + log m)³/(m² t L³)`: for `m² t ≤ 1` by expanding `1/(L - log m)`, and for `m² t > 1`
(where `L < 2 log m`) crudely from `S(u) ≤ 1/u`. No cut-off sums are needed.
-/

namespace RntPaper

open Real

/-- `∑ (1 + log m)³/m² < ∞`, via `1 + log m ≤ 7 m^{1/6}`. -/
lemma phi2_summable_weight :
    Summable (fun m : ℕ => (1 + Real.log m) ^ 3 / (m : ℝ) ^ 2) := by
  have hs := (Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 343
  refine hs.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have := Real.log_nonneg this
    positivity
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := by linarith
    have hl0 := Real.log_nonneg hm1
    set y := (m : ℝ) ^ ((1 : ℝ) / 6) with hy
    have hy1 : 1 ≤ y := Real.one_le_rpow hm1 (by norm_num)
    have hlog : Real.log m ≤ 6 * y := by
      have := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 1 / 6)
      rw [← hy] at this
      linarith [show y / (1 / 6) = 6 * y by ring]
    have h6 : (m : ℝ) = y ^ 6 := by
      rw [hy, ← Real.rpow_mul_natCast hm0.le]; norm_num
    have h9 : (m : ℝ) ^ (3 / 2 : ℝ) = y ^ 9 := by
      rw [hy, ← Real.rpow_mul_natCast hm0.le]; norm_num
    have hy0 : 0 < y := by linarith
    show (1 + Real.log m) ^ 3 / (m : ℝ) ^ 2 ≤ 343 * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹
    rw [h9, div_le_iff₀ (by positivity)]
    have hr : 343 * (y ^ 9)⁻¹ * (m : ℝ) ^ 2 = (7 * y) ^ 3 := by
      rw [h6]; field_simp; ring
    rw [hr]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 3

lemma phi2_weight_nonneg (m : ℕ) : 0 ≤ (1 + Real.log m) ^ 3 / (m : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have := Real.log_nonneg this
  positivity

/-- `∑ log m/m² < ∞`. -/
lemma phi2_summable_log_div_sq :
    Summable (fun m : ℕ => Real.log m / (m : ℝ) ^ 2) := by
  refine phi2_summable_weight.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
  · exact div_nonneg (Real.log_natCast_nonneg m) (by positivity)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have h := Real.log_natCast_nonneg m
    nlinarith [sq_nonneg (Real.log m), pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1)
      (by linarith : (1 : ℝ) ≤ 1 + Real.log m) 2]

/-- `∑ log² m/m² < ∞`. -/
lemma phi2_summable_log_sq_div_sq :
    Summable (fun m : ℕ => Real.log m ^ 2 / (m : ℝ) ^ 2) := by
  refine phi2_summable_weight.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
  · positivity
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have h := Real.log_natCast_nonneg m
    nlinarith [sq_nonneg (Real.log m), mul_nonneg h (sq_nonneg (Real.log m))]

lemma phi2_hasSum_logSqSum :
    HasSum (fun m : ℕ => Real.log m / (m : ℝ) ^ 2) logSqSum :=
  phi2_summable_log_div_sq.hasSum

set_option maxHeartbeats 800000 in
/-- The term-wise bound `|S(mt)/m - T_m| ≤ C (1 + log m)³/(m² t L³)`. -/
lemma phi2_term_bound {g K u₁ : ℝ}
    (hK : ∀ u : ℝ, 0 < u → u < u₁ →
      |primeExpSum u - (1 + g / (-Real.log u)) / (u * (-Real.log u))| ≤
        K / (u * (-Real.log u) ^ 3))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < u₁ ^ 2) (htone : t < 1) (hu₁ : 0 < u₁) (m : ℕ) :
    |primeExpSum (m * t) / m - 1 / ((m : ℝ) ^ 2 * t) *
        (1 / (-Real.log t) + (g + Real.log m) / (-Real.log t) ^ 2)| ≤
      (8 + 8 * |g| + 8 * |K|) / (t * (-Real.log t) ^ 3) *
        ((1 + Real.log m) ^ 3 / (m : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set L := -Real.log t with hLdef
  have hL : 0 < L := neg_pos.2 (Real.log_neg ht0 htone)
  set x := Real.log m with hxdef
  have hx : 0 ≤ x := Real.log_nonneg hm1
  set u := (m : ℝ) * t with hudef
  have hu0 : 0 < u := mul_pos hm0 ht0
  set P := (m : ℝ) ^ 2 * t with hPdef
  have hP0 : 0 < P := by positivity
  set s := u * primeExpSum u with hsdef
  set main := 1 / L + (g + x) / L ^ 2 with hmain
  set C := 8 + 8 * |g| + 8 * |K| with hC
  have hlogP : Real.log P = 2 * x - L := by
    rw [hPdef, Real.log_mul (by positivity) ht0.ne', Real.log_pow]
    push_cast; ring
  have hlhs : primeExpSum u / m - 1 / P * main = (s - main) / P := by
    rw [hsdef, hPdef, hudef]; field_simp
  have hrhs : C / (t * L ^ 3) * ((1 + x) ^ 3 / (m : ℝ) ^ 2) = (C * (1 + x) ^ 3 / L ^ 3) / P := by
    rw [hPdef]; field_simp
  rw [hlhs, hrhs, abs_div, abs_of_pos hP0]
  apply div_le_div_of_nonneg_right _ hP0.le
  have hgabs := abs_nonneg g
  have hKabs := abs_nonneg K
  have h1x : 1 ≤ (1 + x) ^ 3 := one_le_pow₀ (by linarith)
  have hxx : x ≤ (1 + x) ^ 3 := by nlinarith [sq_nonneg x]
  have hx2 : x ^ 2 ≤ (1 + x) ^ 3 := by nlinarith [sq_nonneg x]
  have hx3 : x ^ 3 ≤ (1 + x) ^ 3 := pow_le_pow_left₀ hx (by linarith) 3
  rcases le_or_gt P 1 with hP1 | hP1
  · -- `m² t ≤ 1`: expand `1/(L - log m)`
    have h2x : 2 * x ≤ L := by
      have := Real.log_nonpos hP0.le hP1
      linarith
    have huu : u < u₁ := by
      by_contra h
      push Not at h
      have : u ^ 2 = P * t := by rw [hudef, hPdef]; ring
      nlinarith
    set ℓ := L - x with hℓdef
    have hℓ : -Real.log u = ℓ := by
      rw [hudef, Real.log_mul hm0.ne' ht0.ne', hℓdef, hLdef, hxdef]; ring
    have hℓL : L / 2 ≤ ℓ := by linarith
    have hℓ0 : 0 < ℓ := by linarith
    have hE := hK u hu0 huu
    rw [hℓ] at hE
    set A := (1 + g / ℓ) / ℓ with hA
    have hsA : |s - A| ≤ 8 * |K| / L ^ 3 := by
      have he : s - A = u * (primeExpSum u - (1 + g / ℓ) / (u * ℓ)) := by
        rw [hsdef, hA]; field_simp
      rw [he, abs_mul, abs_of_pos hu0]
      calc u * |primeExpSum u - (1 + g / ℓ) / (u * ℓ)| ≤ u * (K / (u * ℓ ^ 3)) :=
            mul_le_mul_of_nonneg_left hE hu0.le
        _ = K / ℓ ^ 3 := by field_simp
        _ ≤ |K| / ℓ ^ 3 := div_le_div_of_nonneg_right (le_abs_self K) (by positivity)
        _ ≤ |K| / (L / 2) ^ 3 :=
            div_le_div_of_nonneg_left hKabs (by positivity) (pow_le_pow_left₀ (by positivity) hℓL 3)
        _ = 8 * |K| / L ^ 3 := by field_simp; ring
    have hid : A - main = x ^ 2 / (L ^ 2 * ℓ) + g * x * (L + ℓ) / (L ^ 2 * ℓ ^ 2) := by
      rw [hA, hmain]
      have : L = ℓ + x := by rw [hℓdef]; ring
      rw [this]
      field_simp
      ring
    have hT1 : x ^ 2 / (L ^ 2 * ℓ) ≤ 2 * x ^ 2 / L ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg L)) (by linarith : 0 ≤ 2 * ℓ - L)]
    have hT1' : 0 ≤ x ^ 2 / (L ^ 2 * ℓ) := by positivity
    have hT2 : |g * x * (L + ℓ) / (L ^ 2 * ℓ ^ 2)| ≤ 8 * |g| * x / L ^ 3 := by
      have hden : (0 : ℝ) < L ^ 2 * ℓ ^ 2 := by positivity
      have hLℓpos : 0 < L + ℓ := by linarith
      rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_of_nonneg hx, abs_of_pos hLℓpos,
        div_le_div_iff₀ hden (by positivity)]
      have hℓ2 : L ^ 2 ≤ 4 * ℓ ^ 2 := by
        have := pow_le_pow_left₀ hL.le (by linarith : L ≤ 2 * ℓ) 2
        linarith [show (2 * ℓ) ^ 2 = 4 * ℓ ^ 2 by ring]
      have hLℓ : L + ℓ ≤ 2 * L := by linarith
      have hq : (L + ℓ) * L ^ 3 ≤ 8 * (L ^ 2 * ℓ ^ 2) :=
        calc (L + ℓ) * L ^ 3 ≤ (2 * L) * L ^ 3 := mul_le_mul_of_nonneg_right hLℓ (by positivity)
          _ = L ^ 2 * (2 * L ^ 2) := by ring
          _ ≤ L ^ 2 * (2 * (4 * ℓ ^ 2)) := by gcongr
          _ = 8 * (L ^ 2 * ℓ ^ 2) := by ring
      have := mul_le_mul_of_nonneg_left hq (mul_nonneg hgabs hx)
      calc |g| * x * (L + ℓ) * L ^ 3 = |g| * x * ((L + ℓ) * L ^ 3) := by ring
        _ ≤ |g| * x * (8 * (L ^ 2 * ℓ ^ 2)) := this
        _ = 8 * |g| * x * (L ^ 2 * ℓ ^ 2) := by ring
    have htot : |s - main| ≤ (8 * |K| + 2 * x ^ 2 + 8 * |g| * x) / L ^ 3 := by
      have : s - main = (s - A) + (x ^ 2 / (L ^ 2 * ℓ) + g * x * (L + ℓ) / (L ^ 2 * ℓ ^ 2)) := by
        rw [← hid]; ring
      rw [this]
      calc _ ≤ |s - A| + (|x ^ 2 / (L ^ 2 * ℓ)| + |g * x * (L + ℓ) / (L ^ 2 * ℓ ^ 2)|) :=
            (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
        _ ≤ 8 * |K| / L ^ 3 + (2 * x ^ 2 / L ^ 3 + 8 * |g| * x / L ^ 3) := by
            rw [abs_of_nonneg hT1']
            gcongr
        _ = _ := by ring
    refine htot.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [hC]
    linarith [mul_le_mul_of_nonneg_left h1x hKabs, mul_le_mul_of_nonneg_left hxx hgabs]
  · -- `m² t > 1`: then `L < 2 log m`; use `0 ≤ S(u) ≤ 1/u`
    have h2x : L < 2 * x := by
      have := Real.log_pos hP1
      linarith
    have hs0 : 0 ≤ s := mul_nonneg hu0.le (phi_primeExpSum_nonneg u)
    have hs1 : s ≤ 1 := by
      have := phi_primeExpSum_le_inv hu0
      rw [hsdef]
      rw [le_div_iff₀ hu0] at this
      linarith
    have hm_up : main ≤ 1 / L + (|g| + x) / L ^ 2 := by
      rw [hmain]
      gcongr
      exact le_abs_self g
    have hm_lo : -(1 / L + (|g| + x) / L ^ 2) ≤ main := by
      rw [hmain]
      have h1 : 0 ≤ 1 / L := by positivity
      have h2 : -(|g| + x) / L ^ 2 ≤ (g + x) / L ^ 2 :=
        div_le_div_of_nonneg_right (by linarith [neg_abs_le g]) (by positivity)
      rw [neg_div] at h2
      linarith
    have htot : |s - main| ≤ (L ^ 3 + L ^ 2 + (|g| + x) * L) / L ^ 3 := by
      have he : (L ^ 3 + L ^ 2 + (|g| + x) * L) / L ^ 3 = 1 + (1 / L + (|g| + x) / L ^ 2) := by
        field_simp
        ring
      rw [he, abs_le]
      constructor <;> linarith
    refine htot.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have hL3 : L ^ 3 ≤ 8 * x ^ 3 := by
      have := pow_le_pow_left₀ hL.le h2x.le 3
      nlinarith
    have hL2 : L ^ 2 ≤ 4 * x ^ 2 := by
      have := pow_le_pow_left₀ hL.le h2x.le 2
      nlinarith
    have hL1 : (|g| + x) * L ≤ (|g| + x) * (2 * x) :=
      mul_le_mul_of_nonneg_left h2x.le (by positivity)
    rw [hC]
    have hK3 : 0 ≤ |K| * (1 + x) ^ 3 := mul_nonneg hKabs (by positivity)
    linarith [mul_le_mul_of_nonneg_left hxx hgabs, sq_nonneg x, mul_nonneg hgabs hx]

/-- Section C: `Φ(t) = a(1 + κ/L)/(tL) + O(1/(tL³))` with `a = π²/6`, `κ = g + σ/a`. -/
theorem primePhi_expansion {g : ℝ} (hS : ExpSumExpansion g) :
    PhiExpansion primePhi (π ^ 2 / 6) (g + logSqSum / (π ^ 2 / 6)) := by
  obtain ⟨K, u₁, hu₁0, hu₁1, hK⟩ := hS
  set C := 8 + 8 * |g| + 8 * |K| with hC
  set W := ∑' m : ℕ, (1 + Real.log m) ^ 3 / (m : ℝ) ^ 2 with hW
  refine ⟨C * W, u₁ ^ 2, by positivity, by nlinarith, fun t ht0 ht1 => ?_⟩
  have htone : t < 1 := by nlinarith
  have hL : 0 < -Real.log t := neg_pos.2 (Real.log_neg ht0 htone)
  set L := -Real.log t with hLdef
  set T : ℕ → ℝ := fun m => 1 / ((m : ℝ) ^ 2 * t) * (1 / L + (g + Real.log m) / L ^ 2) with hT
  set D : ℕ → ℝ := fun m => primeExpSum (m * t) / m - T m with hD
  have hb : ∀ m, ‖D m‖ ≤ C / (t * L ^ 3) * ((1 + Real.log m) ^ 3 / (m : ℝ) ^ 2) := fun m => by
    rw [Real.norm_eq_abs]
    exact phi2_term_bound hK ht0 ht1 htone hu₁0 m
  have hw := phi2_summable_weight.hasSum.mul_left (C / (t * L ^ 3))
  have hDs : Summable D := Summable.of_norm_bounded hw.summable hb
  have hpi : (π ^ 2 / 6 : ℝ) ≠ 0 := by positivity
  have hTs : HasSum T (π ^ 2 / 6 * (1 + (g + logSqSum / (π ^ 2 / 6)) / L) / (t * L)) := by
    have h1 := hasSum_zeta_two.mul_left (1 / t * (1 / L + g / L ^ 2))
    have h2 := phi2_hasSum_logSqSum.mul_left (1 / t * (1 / L ^ 2))
    convert h1.add h2 using 1
    · funext m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [hT]
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      simp only [hT]
      field_simp
      ring
    · field_simp
      ring
  have hsum : HasSum (fun m : ℕ => primeExpSum (m * t) / m) (∑' m, D m +
      π ^ 2 / 6 * (1 + (g + logSqSum / (π ^ 2 / 6)) / L) / (t * L)) := by
    convert hDs.hasSum.add hTs using 1
    funext m
    simp only [hD]
    ring
  rw [primePhi_eq_tsum ht0, hsum.tsum_eq, add_sub_cancel_right]
  have := tsum_of_norm_bounded hw hb
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [← hW]
  field_simp

/-- `σ = ∑ log m/m² = -ζ'(2)`. -/
theorem logSqSum_eq_neg_deriv_riemannZeta : logSqSum = -(deriv riemannZeta 2).re := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hd : deriv riemannZeta 2 = deriv (LSeries 1) 2 := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2,
      fun _ hz => (LSeries_one_eq_riemannZeta hz).symm⟩
  have hab : LSeries.abscissaOfAbsConv 1 < ((2 : ℂ).re : EReal) := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast h2
  rw [hd, LSeries_deriv hab, Complex.neg_re, neg_neg]
  have hterm : ∀ n : ℕ, LSeries.term (LSeries.logMul 1) 2 n =
      ((Real.log n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn.ne']
    have : ((2 : ℂ)) = ((2 : ℕ) : ℂ) := by norm_num
    rw [this, Complex.cpow_natCast]
    push_cast
    simp [LSeries.logMul]
  rw [LSeries, tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_re, logSqSum]

end RntPaper
