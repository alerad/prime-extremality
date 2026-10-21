import RntPaper.Qfun
import RntPaper.Transport
import LeanCert.Tactic

/-!
# Moment certificates for `Q(x) = ∏_p (1 - xᵖ)`

* `moment_cert`: `J_{17/8}(1) = ∫₀¹ x^{9/8} (Q(x) - (1 - x)) dx > 0`.
  Route: `Q(x) ≥ R(x) (1 - x² - x¹⁹)` with `R = ∏_{p ∈ {3,…,17}} (1 - xᵖ)`
  (the primes `≥ 19` are odd, so `∏_{p≥19}(1-xᵖ) ≥ 1 - x¹⁹/(1-x²)`), then the
  degree-75 polynomial is integrated exactly against `x^{9/8}`.
* `moment_three_neg`: `J_3(1) ≤ -23/8580`, from `Q ≤ (1-x²)(1-x³)(1-x⁵)`.
-/

namespace RntPaper

open QProduct MeasureTheory Set intervalIntegral Filter
open scoped Topology

/-- `R(x) = ∏_{p ∈ {3,5,7,11,13,17}} (1 - xᵖ)`. -/
noncomputable def Rcert (x : ℝ) : ℝ := ∏ p ∈ ({3, 5, 7, 11, 13, 17} : Finset ℕ), (1 - x ^ p)

/-- The small primes `{2,3,5,7,11,13,17}`. -/
def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17}

theorem continuous_Rcert : Continuous Rcert := by
  unfold Rcert; fun_prop

theorem Rcert_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ Rcert x :=
  Finset.prod_nonneg fun _ _ => sub_nonneg.mpr (pow_le_one₀ h0 h1)

theorem qProd_smallPrimes (x : ℝ) : qProd smallPrimes x = (1 - x ^ 2) * Rcert x := by
  simp [qProd, smallPrimes, Rcert]

/-- Primes outside `{2,…,17}` are odd and `≥ 19`. -/
theorem large_prime_form {n : ℕ} (hn : n ∈ Primes) (hs : n ∉ smallPrimes) :
    n = 19 + 2 * ((n - 19) / 2) := by
  have hp : Nat.Prime n := hn
  have h19 : 19 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> simp_all (config := { decide := true }) 
  rcases hp.eq_two_or_odd' with h2 | hodd
  · omega
  · obtain ⟨k, hk⟩ := hodd
    omega

/-- `Σ_{n ∈ F} xⁿ ≤ x¹⁹/(1-x²)` for any finite set `F` of large primes. -/
theorem sum_large_primes_le (F : Finset ℕ) (hF : ∀ n ∈ F, n ∈ Primes ∧ n ∉ smallPrimes)
    {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    ∑ n ∈ F, x ^ n ≤ x ^ 19 / (1 - x ^ 2) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ∈ F, n < N := ⟨F.sup id + 1, fun n hn =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
  have hsub : F ⊆ (Finset.range N).image (fun k => 19 + 2 * k) := by
    intro n hn
    rw [Finset.mem_image]
    refine ⟨(n - 19) / 2, ?_, (large_prime_form (hF n hn).1 (hF n hn).2).symm⟩
    have := hN n hn
    rw [Finset.mem_range]; omega
  have hx2 : x ^ 2 < 1 := by nlinarith
  calc ∑ n ∈ F, x ^ n
      ≤ ∑ n ∈ (Finset.range N).image (fun k => 19 + 2 * k), x ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg h0 _
    _ = ∑ k ∈ Finset.range N, x ^ 19 * (x ^ 2) ^ k := by
        rw [Finset.sum_image (fun a _ b _ h => by omega)]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ = x ^ 19 * ∑ k ∈ Finset.Ico 0 N, (x ^ 2) ^ k := by
        rw [← Finset.mul_sum, Finset.range_eq_Ico]
    _ ≤ x ^ 19 * ((x ^ 2) ^ 0 / (1 - x ^ 2)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one (by positivity) hx2)
          (pow_nonneg h0 _)
    _ = x ^ 19 / (1 - x ^ 2) := by ring

/-- `∏_{p ≥ 19} (1 - xᵖ) ≥ 1 - x¹⁹/(1-x²)`. -/
theorem qProdSet_large_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    1 - x ^ 19 / (1 - x ^ 2) ≤ qProdSet (Primes \ (smallPrimes : Set ℕ)) x := by
  classical
  refine ge_of_tendsto (qProdSet_eq_lim _ h0 h1) (Eventually.of_forall fun N => ?_)
  set F := (Finset.range (N + 1)).filter (· ∈ Primes \ (smallPrimes : Set ℕ))
  have hF : ∀ n ∈ F, n ∈ Primes ∧ n ∉ smallPrimes := by
    intro n hn
    simp only [F, Finset.mem_filter, Set.mem_sdiff, Finset.mem_coe] at hn
    exact hn.2
  have hW := one_sub_prod_one_sub_le_sum F (fun n => x ^ n) (fun _ _ => pow_nonneg h0 _)
    (fun _ _ => pow_le_one₀ h0 h1.le)
  have hS := sum_large_primes_le F hF h0 h1
  unfold qProd
  linarith

/-- **The polynomial minorant** `Q(x) ≥ R(x)(1 - x² - x¹⁹)` on `[0,1)`. -/
theorem Rcert_mul_le_Qfun {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Rcert x * (1 - x ^ 2 - x ^ 19) ≤ Qfun x := by
  have hsplit : Primes = (smallPrimes : Set ℕ) ∪ (Primes \ (smallPrimes : Set ℕ)) := by
    refine (Set.union_sdiff_cancel ?_).symm
    intro n hn
    simp only [smallPrimes, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Primes]
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hpos : 0 < 1 - x ^ 2 := by linarith
  have hR := Rcert_nonneg h0 h1.le
  unfold Qfun
  rw [hsplit, qProdSet_union Set.disjoint_sdiff_right h0 h1, qProdSet_coe,
    qProd_smallPrimes]
  have hL := qProdSet_large_ge h0 h1
  calc Rcert x * (1 - x ^ 2 - x ^ 19)
      = (1 - x ^ 2) * Rcert x * (1 - x ^ 19 / (1 - x ^ 2)) := by
        field_simp
    _ ≤ (1 - x ^ 2) * Rcert x * qProdSet (Primes \ (smallPrimes : Set ℕ)) x :=
        mul_le_mul_of_nonneg_left hL (mul_nonneg hpos.le hR)

/-- `Q(x) ≤ (1-x²)(1-x³)(1-x⁵)` on `[0,1)`. -/
theorem Qfun_le_P235 {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Qfun x ≤ (1 - x ^ 2) * (1 - x ^ 3) * (1 - x ^ 5) := by
  have := qProdSet_le_qProd (T := Primes) ({2, 3, 5} : Finset ℕ) (by
    intro n hn
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl <;> norm_num [Primes]) h0 h1
  unfold Qfun
  refine this.trans (le_of_eq ?_)
  simp [qProd]
  ring

/-! ## Exact integration of the polynomial minorant -/

/-- Coefficients of `R(x)(1 - x² - x¹⁹) - (1 - x)` (degree 75). -/
def cfList : List ℤ :=
  [0, 1, -1, -1, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, 0, 0, 2, 0, 0,
   -1, 1, -1, 0, -1, 2, -1, 0, -2, 2, -1, 1, -2, 2, -1, 1, -2, 2, -1, 2, -1, 2, -2, 1, -2,
   2, -1, 2, -1, 2, -2, 0, -2, 1, -1, 1, -1, 1, -1, 0, -1, 1, 0, 1, 0, 1, 0, 0, -1]

def cf (m : ℕ) : ℤ := cfList.getD m 0

theorem poly_expand (x : ℝ) :
    Rcert x * (1 - x ^ 2 - x ^ 19) - (1 - x) =
      ∑ m ∈ Finset.range 76, (cf m : ℝ) * x ^ m := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cf, cfList, List.getD_cons_succ,
    List.getD_cons_zero]
  simp [Rcert]
  ring

theorem integral_rpow_mul_pow (m : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ ((17:ℝ) / 8 - 1) * x ^ m = 1 / ((m : ℝ) + 17 / 8) := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hcongr : EqOn (fun x : ℝ => x ^ ((17:ℝ) / 8 - 1) * x ^ m)
      (fun x : ℝ => x ^ ((17:ℝ) / 8 - 1 + m)) (uIcc 0 1) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    simp only
    rw [Real.rpow_add' hx.1 (by linarith), Real.rpow_natCast]
  rw [integral_congr hcongr, integral_rpow (Or.inl (by linarith))]
  have h1 : (17:ℝ) / 8 - 1 + m + 1 = m + 17 / 8 := by ring
  rw [h1, Real.zero_rpow (by linarith), Real.one_rpow, sub_zero]

theorem integral_poly_cert :
    ∫ x in (0:ℝ)..1, x ^ ((17:ℝ) / 8 - 1) * (Rcert x * (1 - x ^ 2 - x ^ 19) - (1 - x))
      = ∑ m ∈ Finset.range 76, (cf m : ℝ) * (1 / ((m : ℝ) + 17 / 8)) := by
  simp_rw [poly_expand, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [← integral_rpow_mul_pow m, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  · intro m _
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul (Real.continuous_rpow_const (by norm_num)).continuousOn ?_
    fun_prop

theorem sum_cert_pos :
    0 < ∑ m ∈ Finset.range 76, (cf m : ℝ) * (1 / ((m : ℝ) + 17 / 8)) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cf, cfList, List.getD_cons_succ,
    List.getD_cons_zero]
  norm_num

/-- The moment certificate: J_{17/8}(1) > 0. -/
theorem moment_cert : 0 < ∫ x in (0:ℝ)..1, x ^ ((17:ℝ) / 8 - 1) * (Qfun x - (1 - x)) := by
  refine sum_cert_pos.trans_le ?_
  rw [← integral_poly_cert]
  have hw : ContinuousOn (fun x : ℝ => x ^ ((17:ℝ) / 8 - 1)) (uIcc 0 1) :=
    (Real.continuous_rpow_const (by norm_num)).continuousOn
  apply intervalIntegral.integral_mono_ae_restrict zero_le_one
  · refine IntervalIntegrable.continuousOn_mul ?_ hw
    exact (by have := continuous_Rcert; fun_prop : Continuous fun x : ℝ =>
      Rcert x * (1 - x ^ 2 - x ^ 19) - (1 - x)).intervalIntegrable _ _
  · refine IntervalIntegrable.continuousOn_mul ?_ hw
    exact (intervalIntegrable_qProdSet Primes ⟨zero_le_one, le_rfl⟩).sub
      ((by fun_prop : Continuous fun x : ℝ => 1 - x).intervalIntegrable _ _)
  · filter_upwards [ae_restrict_ne_one (Icc (0:ℝ) 1),
      ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx1 hx
    have hlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have := Rcert_mul_le_Qfun hx.1 hlt
    have hw0 : 0 ≤ x ^ ((17:ℝ) / 8 - 1) := Real.rpow_nonneg hx.1 _
    exact mul_le_mul_of_nonneg_left (by linarith) hw0

theorem integral_P235_moment :
    (∫ x in (0:ℝ)..1, x ^ 2 * ((1 - x ^ 2) * (1 - x ^ 3) * (1 - x ^ 5) - (1 - x)))
      = -23 / 8580 := by
  leancert

/-- J_3(1) ≤ -23/8580 < 0. -/
theorem moment_three_neg :
    (∫ x in (0:ℝ)..1, x ^ ((3:ℝ) - 1) * (Qfun x - (1 - x))) ≤ -23 / 8580 := by
  have hr : ∀ x : ℝ, x ^ ((3:ℝ) - 1) = x ^ 2 := fun x => by
    rw [show (3:ℝ) - 1 = (2:ℕ) by norm_num, Real.rpow_natCast]
  simp_rw [hr]
  rw [← integral_P235_moment]
  apply intervalIntegral.integral_mono_ae_restrict zero_le_one
  · refine IntervalIntegrable.continuousOn_mul ?_ (by fun_prop)
    exact (intervalIntegrable_qProdSet Primes ⟨zero_le_one, le_rfl⟩).sub
      ((by fun_prop : Continuous fun x : ℝ => 1 - x).intervalIntegrable _ _)
  · exact (by fun_prop : Continuous fun x : ℝ =>
      x ^ 2 * ((1 - x ^ 2) * (1 - x ^ 3) * (1 - x ^ 5) - (1 - x))).intervalIntegrable _ _
  · filter_upwards [ae_restrict_ne_one (Icc (0:ℝ) 1),
      ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx1 hx
    have hlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have := Qfun_le_P235 hx.1 hlt
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg x)

end RntPaper
