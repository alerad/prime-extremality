import RntPaper.Extremal
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Convex.Continuous

/-!
# Consequences (paper §1.2, §5)

* Proposition 1.3: pointwise extremality fails (`A_N = 𝒫_N ∖ {2,3} ∪ {4,6,9}`).
* Corollary 1.5: increasing-concave minimality, stated through the law of
  the bottleneck variable as a Stieltjes measure with survival function `P_A`.
* Proposition 5.1: powers `k ∈ {1,2}` (integer `k`; real `k ∈ (1,2)` needs `rpow`).
* Proposition 5.2: tail bound with `R = {2}`.
* Open problem 2 data: `k = 126` at `N = 9`.
-/

namespace RntPaper

open QProduct MeasureTheory Set Filter Topology

/-! ## Proposition 1.3 -/

/-- `A_N = (𝒫_N ∖ {2,3}) ∪ {4,6,9}`. -/
def A9 (N : ℕ) : Finset ℕ :=
  ((primesLE N).filter (fun p => p ≠ 2 ∧ p ≠ 3)) ∪ {4, 6, 9}

theorem mem_A9 {N a : ℕ} :
    a ∈ A9 N ↔ (Nat.Prime a ∧ a ≤ N ∧ a ≠ 2 ∧ a ≠ 3) ∨ a = 4 ∨ a = 6 ∨ a = 9 := by
  simp only [A9, Finset.mem_union, Finset.mem_filter, mem_primesLE, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

theorem A9_isPrimitiveFin {N : ℕ} (_hN : 9 ≤ N) : IsPrimitiveFin (A9 N) := by
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · rcases mem_A9.mp (Finset.mem_coe.mp ha) with ⟨hp, -⟩ | rfl | rfl | rfl
    · exact hp.two_le
    all_goals norm_num
  · have ha' := mem_A9.mp (Finset.mem_coe.mp ha)
    have hb' := mem_A9.mp (Finset.mem_coe.mp hb)
    rcases ha' with ⟨hpa, -, ha2, ha3⟩ | rfl | rfl | rfl <;>
      rcases hb' with ⟨hpb, -, hb2, hb3⟩ | rfl | rfl | rfl
    · exact (Nat.prime_dvd_prime_iff_eq hpa hpb).mp hab
    -- a prime, b ∈ {4,6,9}: `a ≤ b` forces `a ∈ {2,3}` or a non-prime
    all_goals try
      (have hle := Nat.le_of_dvd (by norm_num) hab
       have h2 := hpa.two_le
       interval_cases a <;> omega)
    -- a ∈ {4,6,9}, b prime: `a ∣ b` forces `a = b`, but `a` is not prime
    all_goals try
      (rcases hpb.eq_one_or_self_of_dvd _ hab with h | h
       · omega
       · subst h; norm_num at hpb)
    -- a, b ∈ {4,6,9}
    all_goals first | rfl | omega

theorem A9_bounded {N : ℕ} (hN : 9 ≤ N) : ∀ a ∈ A9 N, a ≤ N := by
  have _ := hN
  intro a ha
  rcases mem_A9.mp ha with ⟨-, h, -⟩ | rfl | rfl | rfl <;> omega

/-- For `N ≥ 3`, `𝒫_N = {2,3} ∪ (𝒫_N ∖ {2,3})`. -/
theorem primesLE_eq_union {N : ℕ} (hN : 3 ≤ N) :
    primesLE N = {2, 3} ∪ (primesLE N).filter (fun p => p ≠ 2 ∧ p ≠ 3) := by
  ext p
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter,
    mem_primesLE]
  constructor
  · intro h
    by_cases h2 : p = 2
    · exact Or.inl (Or.inl h2)
    by_cases h3 : p = 3
    · exact Or.inl (Or.inr h3)
    exact Or.inr ⟨h, h2, h3⟩
  · rintro ((rfl | rfl) | ⟨h, -⟩)
    · exact ⟨Nat.prime_two, by omega⟩
    · exact ⟨Nat.prime_three, by omega⟩
    · exact h

/-- `P_{A_N}(x)·(1-x²)(1-x³) = P_{𝒫_N}(x)·(1-x⁴)(1-x⁶)(1-x⁹)`. -/
theorem qProd_A9_ratio {N : ℕ} (hN : 9 ≤ N) (x : ℝ) :
    qProd (A9 N) x * ((1 - x ^ 2) * (1 - x ^ 3))
      = qProd (primesLE N) x * ((1 - x ^ 4) * (1 - x ^ 6) * (1 - x ^ 9)) := by
  classical
  set R := (primesLE N).filter (fun p => p ≠ 2 ∧ p ≠ 3) with hR
  have hsplit : primesLE N = {2, 3} ∪ R := primesLE_eq_union (by omega)
  have hdisj1 : Disjoint ({2, 3} : Finset ℕ) R := by
    rw [Finset.disjoint_left]
    intro p hp hpR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    have := (Finset.mem_filter.mp hpR).2
    omega
  have hdisj2 : Disjoint R ({4, 6, 9} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro p hpR hp
    have hprime := (mem_primesLE.mp (Finset.mem_filter.mp hpR).1).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num at hprime
  have h1 : qProd (A9 N) x = qProd R x * ((1 - x ^ 4) * (1 - x ^ 6) * (1 - x ^ 9)) := by
    unfold A9
    rw [← hR]
    unfold qProd
    rw [Finset.prod_union hdisj2]
    congr 1
    simp [Finset.prod_insert]
    ring
  have h2 : qProd (primesLE N) x = ((1 - x ^ 2) * (1 - x ^ 3)) * qProd R x := by
    rw [hsplit]
    unfold qProd
    rw [Finset.prod_union hdisj1]
    congr 1
    simp [Finset.prod_insert]
  rw [h1, h2]
  ring

/-- `P_S(x) > 0` for `x ∈ [0,1)` when all exponents are positive. -/
theorem qProd_pos_of_lt_one {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) : 0 < qProd S x := by
  unfold qProd
  apply Finset.prod_pos
  intro n hn
  have : x ^ n < 1 := pow_lt_one₀ hx.1 hx.2 (by have := hS n hn; omega)
  linarith

/-- The ratio `(1+x²)(1+x³)(1-x⁹)` is `< 1` on `[0.98, 1]` (it crosses `1` at
`x ≈ 0.965`). Interval certificate. -/
theorem ratio_lt_one_near_one :
    ∀ x ∈ Icc (0.98 : ℝ) 1, (1 + x ^ 2) * (1 + x ^ 3) * (1 - x ^ 9) < 1 := by
  leancert (trust := kernel)

/-- **Proposition 1.3.** `P_{A_N} < P_{𝒫_N}` on a neighbourhood of `1`, although
`F_c(𝒫_N) < F_c(A_N)` for every `c` (Theorem 1.1). -/
theorem pointwise_failure {N : ℕ} (hN : 9 ≤ N) :
    ∀ x ∈ Ico (0.98 : ℝ) 1, qProd (A9 N) x < qProd (primesLE N) x := by
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := by
    have := hx.1
    norm_num at this
    linarith
  have hx1 : x < 1 := hx.2
  have hP : 0 < qProd (primesLE N) x :=
    qProd_pos_of_lt_one (fun n hn => (mem_primesLE.mp hn).1.one_lt.le) ⟨hx0, hx1⟩
  have hD : 0 < (1 - x ^ 2) * (1 - x ^ 3) := by
    have h2 : x ^ 2 < 1 := pow_lt_one₀ hx0 hx1 (by norm_num)
    have h3 : x ^ 3 < 1 := pow_lt_one₀ hx0 hx1 (by norm_num)
    exact mul_pos (by linarith) (by linarith)
  have hr := ratio_lt_one_near_one x ⟨hx.1, hx1.le⟩
  have hratio := qProd_A9_ratio hN x
  have hfac : (1 - x ^ 4) * (1 - x ^ 6) * (1 - x ^ 9)
      = ((1 - x ^ 2) * (1 - x ^ 3)) * ((1 + x ^ 2) * (1 + x ^ 3) * (1 - x ^ 9)) := by ring
  rw [hfac] at hratio
  have hA : qProd (A9 N) x
      = qProd (primesLE N) x * ((1 + x ^ 2) * (1 + x ^ 3) * (1 - x ^ 9)) := by
    apply mul_right_cancel₀ hD.ne'
    rw [hratio]
    ring
  rw [hA]
  calc qProd (primesLE N) x * ((1 + x ^ 2) * (1 + x ^ 3) * (1 - x ^ 9))
      < qProd (primesLE N) x * 1 := mul_lt_mul_of_pos_left hr hP
    _ = qProd (primesLE N) x := mul_one _

theorem A9_ne_primesLE (N : ℕ) : A9 N ≠ primesLE N := by
  intro h
  have h4 : 4 ∈ A9 N := mem_A9.mpr (Or.inr (Or.inl rfl))
  rw [h] at h4
  exact absurd (mem_primesLE.mp h4).1 (by norm_num)

theorem pointwise_failure_integrals {N : ℕ} (hN : 9 ≤ N) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) : Fc c (primesLE N) < Fc c (A9 N) :=
  Fc_primesLE_lt (A9_isPrimitiveFin hN) (A9_bounded hN) (A9_ne_primesLE N) hc

/-! ## Corollary 1.5 -/

/-- `P_S` is nonincreasing on `[0,1]` (each factor `1 - uⁿ` is). -/
theorem qProd_antitoneOn (S : Finset ℕ) : AntitoneOn (qProd S) (Icc 0 1) := by
  intro x hx y hy hxy
  unfold qProd
  apply Finset.prod_le_prod₀
  · intro n _
    exact sub_nonneg.mpr (pow_le_one₀ hy.1 hy.2)
  · intro n _
    exact sub_le_sub_left (pow_le_pow_left₀ hx.1 hxy n) 1

theorem cdf_mono (S : Finset ℕ) :
    Monotone (fun x : ℝ => if x < 0 then 0 else if x < 1 then 1 - qProd S x else 1) := by
  intro x y hxy
  simp only
  by_cases hx0 : x < 0
  · simp only [hx0, ↓reduceIte]
    by_cases hy0 : y < 0
    · simp only [hy0, ↓reduceIte, le_refl]
    · simp only [hy0, ↓reduceIte]
      by_cases hy1 : y < 1
      · simp only [hy1, ↓reduceIte]
        exact sub_nonneg.mpr (qProd_le_one S ⟨not_lt.mp hy0, hy1.le⟩)
      · simp only [hy1, ↓reduceIte]
        norm_num
  · simp only [hx0, ↓reduceIte]
    have hy0 : ¬ y < 0 := fun h => hx0 (lt_of_le_of_lt hxy h)
    simp only [hy0, ↓reduceIte]
    by_cases hx1 : x < 1
    · simp only [hx1, ↓reduceIte]
      by_cases hy1 : y < 1
      · simp only [hy1, ↓reduceIte]
        have := qProd_antitoneOn S ⟨not_lt.mp hx0, hx1.le⟩ ⟨not_lt.mp hy0, hy1.le⟩ hxy
        linarith
      · simp only [hy1, ↓reduceIte]
        linarith [qProd_nonneg S ⟨not_lt.mp hx0, hx1.le⟩]
    · simp only [hx1, ↓reduceIte]
      have hy1 : ¬ y < 1 := fun h => hx1 (lt_of_le_of_lt hxy h)
      simp only [hy1, ↓reduceIte, le_refl]

theorem cdf_right_continuous (S : Finset ℕ) (x : ℝ) :
    ContinuousWithinAt (fun x : ℝ => if x < 0 then 0 else if x < 1 then 1 - qProd S x else 1)
      (Ici x) x := by
  by_cases hx0 : x < 0
  · have hev : (fun y : ℝ => if y < 0 then 0 else if y < 1 then 1 - qProd S y else 1)
        =ᶠ[𝓝[≥] x] fun _ => (0 : ℝ) := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx0)] with y hy
      have hy' : y < 0 := hy
      simp [hy']
    exact continuousWithinAt_const.congr_of_eventuallyEq hev (by simp [hx0])
  · by_cases hx1 : x < 1
    · have hev : (fun y : ℝ => if y < 0 then 0 else if y < 1 then 1 - qProd S y else 1)
          =ᶠ[𝓝[≥] x] fun y => 1 - qProd S y := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx1), self_mem_nhdsWithin] with y hy1 hy2
        have hy0 : ¬ y < 0 := fun h => hx0 (lt_of_le_of_lt hy2 h)
        have hy1' : y < 1 := hy1
        simp [hy0, hy1']
      exact ((continuous_const.sub (qProd_continuous S)).continuousWithinAt).congr_of_eventuallyEq
        hev (by simp [hx0, hx1])
    · have hev : (fun y : ℝ => if y < 0 then 0 else if y < 1 then 1 - qProd S y else 1)
          =ᶠ[𝓝[≥] x] fun _ => (1 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : ¬ y < 0 := fun h => hx0 (lt_of_le_of_lt hy h)
        have hy1 : ¬ y < 1 := fun h => hx1 (lt_of_le_of_lt hy h)
        simp [hy0, hy1]
      exact continuousWithinAt_const.congr_of_eventuallyEq hev (by simp [hx0, hx1])

/-- Distribution function of the bottleneck `Z_S`: `x ↦ 1 - P_S(x)` on `[0,1]`,
clamped outside. -/
noncomputable def bottleneckCDF (S : Finset ℕ) : StieltjesFunction ℝ where
  toFun x := if x < 0 then 0 else if x < 1 then 1 - qProd S x else 1
  mono' := cdf_mono S
  right_continuous' := cdf_right_continuous S

theorem bottleneckCDF_apply (S : Finset ℕ) (x : ℝ) :
    bottleneckCDF S x = if x < 0 then 0 else if x < 1 then 1 - qProd S x else 1 := rfl

theorem bottleneckCDF_of_neg (S : Finset ℕ) {x : ℝ} (hx : x < 0) : bottleneckCDF S x = 0 := by
  rw [bottleneckCDF_apply]
  simp only [hx, ↓reduceIte]

theorem bottleneckCDF_of_mem (S : Finset ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    bottleneckCDF S x = 1 - qProd S x := by
  rw [bottleneckCDF_apply]
  simp only [not_lt.mpr h0, h1, ↓reduceIte]

theorem bottleneckCDF_of_one_le (S : Finset ℕ) {x : ℝ} (h : 1 ≤ x) : bottleneckCDF S x = 1 := by
  rw [bottleneckCDF_apply]
  have h0 : ¬ x < 0 := by linarith
  simp only [h0, not_lt.mpr h, ↓reduceIte]

theorem bottleneckCDF_tendsto_atTop (S : Finset ℕ) :
    Tendsto (bottleneckCDF S) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (bottleneckCDF_of_one_le S hx).symm

theorem bottleneckCDF_tendsto_atBot (S : Finset ℕ) :
    Tendsto (bottleneckCDF S) atBot (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  exact (bottleneckCDF_of_neg S hx).symm

instance (S : Finset ℕ) : IsProbabilityMeasure (bottleneckCDF S).measure :=
  (bottleneckCDF S).isProbabilityMeasure (bottleneckCDF_tendsto_atBot S)
    (bottleneckCDF_tendsto_atTop S)

/-- Survival function: `ℙ(Z_S > x) = 1 - F(x)`. -/
theorem bottleneckCDF_measure_Ioi (S : Finset ℕ) (x : ℝ) :
    (bottleneckCDF S).measure (Ioi x) = ENNReal.ofReal (1 - bottleneckCDF S x) :=
  (bottleneckCDF S).measure_Ioi (bottleneckCDF_tendsto_atTop S) x

/-- `Z_S ≥ 0` almost surely. -/
theorem bottleneckCDF_measure_Iio_zero (S : Finset ℕ) :
    (bottleneckCDF S).measure (Iio 0) = 0 := by
  rw [(bottleneckCDF S).measure_Iio (bottleneckCDF_tendsto_atBot S) 0]
  have : Function.leftLim (bottleneckCDF S) 0 = 0 := by
    apply leftLim_eq_of_tendsto
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (bottleneckCDF_of_neg S hx).symm
  rw [this]
  simp

/-- `𝔼 φ(Z_S)`. -/
noncomputable def expectPhi (S : Finset ℕ) (φ : ℝ → ℝ) : ℝ :=
  ∫ x, φ x ∂(bottleneckCDF S).measure

/-- Hinge functions: `𝔼 min(Z_S, c) = F_c(S)` (layer-cake formula). -/
theorem expectPhi_hinge (S : Finset ℕ) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    expectPhi S (fun x => min x c) = Fc c S := by
  set μ := (bottleneckCDF S).measure with hμ
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext a; simp
    rw [this]
    exact bottleneckCDF_measure_Iio_zero S
  have hnn : 0 ≤ᵐ[μ] fun x => min x c := by
    filter_upwards [hae] with x hx
    exact le_min hx hc.1.le
  have hint : Integrable (fun x => min x c) μ := by
    refine Integrable.of_bound (continuous_id.min continuous_const).aestronglyMeasurable c ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hc.1.le)]
    exact min_le_right _ _
  unfold expectPhi
  rw [hint.integral_eq_integral_meas_lt hnn]
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      μ.real {a | t < min a c} = (Ioo 0 c).indicator (qProd S) t := by
    intro t ht
    have ht' : 0 < t := ht
    by_cases htc : t < c
    · have hset : {a : ℝ | t < min a c} = Ioi t := by
        ext a
        simp [lt_min_iff, htc]
      have ht1 : t < 1 := htc.trans_le hc.2
      have htm : t ∈ Ioo 0 c := ⟨ht', htc⟩
      rw [hset, measureReal_def, bottleneckCDF_measure_Ioi, indicator_of_mem htm,
        bottleneckCDF_of_mem S ht'.le ht1,
        ENNReal.toReal_ofReal (by linarith [qProd_nonneg S ⟨ht'.le, ht1.le⟩])]
      ring
    · have hset : {a : ℝ | t < min a c} = ∅ := by
        ext a
        simp [lt_min_iff, htc]
      rw [hset, indicator_of_notMem (fun h => htc h.2)]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr Ioo_subset_Ioi_self, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hc.1.le]
  rfl

/-! ### The bottleneck law lives on `(0,1]` -/

/-- `P_S(0) = 1` when `0 ∉ S`. -/
theorem qProd_zero_of_pos {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) : qProd S 0 = 1 := by
  unfold qProd
  apply Finset.prod_eq_one
  intro n hn
  rw [zero_pow (by have := hS n hn; omega), sub_zero]

theorem bottleneckCDF_zero {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) : bottleneckCDF S 0 = 0 := by
  rw [bottleneckCDF_of_mem S le_rfl one_pos, qProd_zero_of_pos hS, sub_self]

/-- No mass at or below `0` when `0 ∉ S`. -/
theorem bottleneckCDF_measure_Iic_zero {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) :
    (bottleneckCDF S).measure (Iic 0) = 0 := by
  rw [(bottleneckCDF S).measure_Iic (bottleneckCDF_tendsto_atBot S) 0, bottleneckCDF_zero hS]
  simp

theorem bottleneckCDF_measure_Ioi_one (S : Finset ℕ) :
    (bottleneckCDF S).measure (Ioi 1) = 0 := by
  rw [bottleneckCDF_measure_Ioi, bottleneckCDF_of_one_le S le_rfl]
  simp

/-- `Z_S ∈ (0,1]` almost surely when `0 ∉ S`. -/
theorem bottleneckCDF_ae_mem_Ioc {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) :
    ∀ᵐ x ∂(bottleneckCDF S).measure, x ∈ Ioc (0 : ℝ) 1 := by
  rw [ae_iff]
  have : {x : ℝ | ¬ x ∈ Ioc (0 : ℝ) 1} = Iic 0 ∪ Ioi 1 := by
    ext x
    simp only [mem_Ioc, mem_union, mem_Iic, mem_Ioi, not_and_or, not_lt, not_le]
    rfl
  rw [this]
  exact measure_union_null (bottleneckCDF_measure_Iic_zero hS) (bottleneckCDF_measure_Ioi_one S)

/-! ### Nonnegative hinge combinations -/

theorem integrable_hinge (S : Finset ℕ) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x => min x c) (bottleneckCDF S).measure := by
  have hae : ∀ᵐ x ∂(bottleneckCDF S).measure, 0 ≤ x := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext a; simp
    rw [this]
    exact bottleneckCDF_measure_Iio_zero S
  refine Integrable.of_bound (continuous_id.min continuous_const).aestronglyMeasurable c ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hc.1.le)]
  exact min_le_right _ _

/-- `𝔼 [b + ∑ w_k min(Z_S, t_k)] = b + ∑ w_k F_{t_k}(S)`. -/
theorem expectPhi_hingeSum (S : Finset ℕ) (b : ℝ) {m : ℕ} (w t : ℕ → ℝ)
    (ht : ∀ k < m, t k ∈ Ioc (0 : ℝ) 1) :
    expectPhi S (fun x => b + ∑ k ∈ Finset.range m, w k * min x (t k))
      = b + ∑ k ∈ Finset.range m, w k * Fc (t k) S := by
  unfold expectPhi
  have hint : ∀ k ∈ Finset.range m,
      Integrable (fun x => w k * min x (t k)) (bottleneckCDF S).measure :=
    fun k hk => (integrable_hinge S (ht k (Finset.mem_range.mp hk))).const_mul _
  rw [integral_add (integrable_const b) (integrable_finsetSum _ hint), integral_const,
    probReal_univ, one_smul, integral_finsetSum _ hint]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, ← expectPhi_hinge S (ht k (Finset.mem_range.mp hk))]
  rfl

/-- Corollary 1.5 for nonnegative combinations of hinges (plus a constant). -/
theorem expectPhi_hingeSum_le {N : ℕ} {A : Finset ℕ} (hA : IsPrimitiveFin A)
    (hAN : ∀ a ∈ A, a ≤ N) (b : ℝ) {m : ℕ} (w t : ℕ → ℝ) (hw : ∀ k < m, 0 ≤ w k)
    (ht : ∀ k < m, t k ∈ Ioc (0 : ℝ) 1) :
    expectPhi (primesLE N) (fun x => b + ∑ k ∈ Finset.range m, w k * min x (t k))
      ≤ expectPhi A (fun x => b + ∑ k ∈ Finset.range m, w k * min x (t k)) := by
  rw [expectPhi_hingeSum _ b w t ht, expectPhi_hingeSum _ b w t ht]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  exact mul_le_mul_of_nonneg_left (Fc_primesLE_le hA hAN (ht k hk')) (hw k hk')

/-! ### Uniform-grid interpolants as hinge combinations -/

/-- Chord slope of `φ` on the `k`-th cell `[k/n, (k+1)/n]` of the uniform grid
(zero for `k ≥ n`). -/
noncomputable def gridSlope (φ : ℝ → ℝ) (n k : ℕ) : ℝ :=
  if k < n then (n : ℝ) * (φ (((k : ℝ) + 1) / n) - φ ((k : ℝ) / n)) else 0

/-- The piecewise-linear interpolant of `φ` at the knots `k/n`, written as
`φ(0) + ∑ (s_k - s_{k+1}) · min(x, (k+1)/n)`. -/
noncomputable def gridInterp (φ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  φ 0 + ∑ k ∈ Finset.range n,
    (gridSlope φ n k - gridSlope φ n (k + 1)) * min x (((k : ℝ) + 1) / n)

theorem gridInterp_continuous (φ : ℝ → ℝ) (n : ℕ) : Continuous (gridInterp φ n) :=
  continuous_const.add (continuous_finsetSum _ fun _ _ =>
    continuous_const.mul (continuous_id.min continuous_const))

theorem gridSlope_of_lt (φ : ℝ → ℝ) {n k : ℕ} (hk : k < n) :
    gridSlope φ n k = (n : ℝ) * (φ (((k : ℝ) + 1) / n) - φ ((k : ℝ) / n)) := by
  simp [gridSlope, hk]

theorem gridSlope_of_le (φ : ℝ → ℝ) {n k : ℕ} (hk : n ≤ k) : gridSlope φ n k = 0 := by
  simp [gridSlope, hk]

theorem cell_mem_Icc {n k : ℕ} (hk : k < n) :
    (k : ℝ) / n ∈ Icc (0 : ℝ) 1 ∧ ((k : ℝ) + 1) / n ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hk
  exact ⟨⟨by positivity, div_le_one_of_le₀ (by linarith) hn.le⟩,
    ⟨by positivity, div_le_one_of_le₀ hk1 hn.le⟩⟩

theorem gridSlope_nonneg {φ : ℝ → ℝ} (hmono : MonotoneOn φ (Icc 0 1)) (n k : ℕ) :
    0 ≤ gridSlope φ n k := by
  by_cases hk : k < n
  · rw [gridSlope_of_lt φ hk]
    have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    obtain ⟨h1, h2⟩ := cell_mem_Icc hk
    apply mul_nonneg hn.le
    rw [sub_nonneg]
    exact hmono h1 h2 (by gcongr; linarith)
  · rw [gridSlope_of_le φ (not_lt.mp hk)]

theorem gridSlope_succ_le {φ : ℝ → ℝ} (hmono : MonotoneOn φ (Icc 0 1))
    (hconc : ConcaveOn ℝ (Icc 0 1) φ) (n k : ℕ) :
    gridSlope φ n (k + 1) ≤ gridSlope φ n k := by
  by_cases hk : k + 1 < n
  · rw [gridSlope_of_lt φ hk, gridSlope_of_lt φ (by omega)]
    have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    obtain ⟨hx, -⟩ := cell_mem_Icc (show k < n by omega)
    obtain ⟨-, hz⟩ := cell_mem_Icc hk
    push_cast at hz ⊢
    have h := hconc.slope_anti_adjacent (x := (k : ℝ) / n) (y := ((k : ℝ) + 1) / n)
      (z := ((k : ℝ) + 1 + 1) / n) hx hz (by gcongr; linarith) (by gcongr; linarith)
    have hzy : ((k : ℝ) + 1 + 1) / n - ((k : ℝ) + 1) / n = 1 / n := by ring
    have hyx : ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n := by ring
    rw [hzy, hyx, div_le_div_iff_of_pos_right (by positivity)] at h
    exact mul_le_mul_of_nonneg_left h hn.le
  · rw [gridSlope_of_le φ (not_lt.mp hk)]
    exact gridSlope_nonneg hmono n k

/-- Abel summation: the hinge form equals `φ(0) + ∑ s_k · (cell length below x)`. -/
theorem gridInterp_eq_sum_cells (φ : ℝ → ℝ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gridInterp φ n x = φ 0 + ∑ k ∈ Finset.range n,
      gridSlope φ n k * (min x (((k : ℝ) + 1) / n) - min x ((k : ℝ) / n)) := by
  unfold gridInterp
  congr 1
  set s := gridSlope φ n with hs
  set m : ℕ → ℝ := fun k => min x ((k : ℝ) / n) with hm
  have hm' : ∀ k : ℕ, min x (((k : ℝ) + 1) / n) = m (k + 1) := by
    intro k
    simp only [hm]
    push_cast
    rfl
  simp_rw [hm']
  have h1 : ∑ k ∈ Finset.range n, s (k + 1) * m (k + 1)
      = ∑ k ∈ Finset.range n, s k * m k + s n * m n - s 0 * m 0 := by
    have := Finset.sum_range_succ' (fun k => s k * m k) n
    rw [Finset.sum_range_succ] at this
    linarith
  have h2 : s n = 0 := gridSlope_of_le φ le_rfl
  have h3 : m 0 = 0 := by
    simp only [hm]
    rw [Nat.cast_zero, zero_div, min_eq_right hx]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2, h3]
  ring

/-- On the cell `[j/n, (j+1)/n]` the interpolant is the chord. -/
theorem gridInterp_eval (φ : ℝ → ℝ) {n j : ℕ} (hj : j < n) {x : ℝ}
    (hx : x ∈ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n)) :
    gridInterp φ n x = φ ((j : ℝ) / n) + gridSlope φ n j * (x - (j : ℝ) / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
  rw [gridInterp_eq_sum_cells φ n hx0, ← Finset.sum_range_add_sum_Ico _ hj.le,
    Finset.sum_eq_sum_Ico_succ_bot hj]
  have hA : ∑ k ∈ Finset.range j,
      gridSlope φ n k * (min x (((k : ℝ) + 1) / n) - min x ((k : ℝ) / n))
      = φ ((j : ℝ) / n) - φ 0 := by
    have := Finset.sum_range_sub (fun k : ℕ => φ ((k : ℝ) / n)) j
    rw [Nat.cast_zero, zero_div] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < j := Finset.mem_range.mp hk
    have hk1 : (k : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hk'
    have h1 : min x (((k : ℝ) + 1) / n) = ((k : ℝ) + 1) / n :=
      min_eq_right (le_trans (by gcongr) hx.1)
    have h2 : min x ((k : ℝ) / n) = (k : ℝ) / n :=
      min_eq_right (le_trans (by gcongr) hx.1)
    rw [h1, h2, gridSlope_of_lt φ (by omega)]
    push_cast
    field_simp
    ring
  have hB : ∑ k ∈ Finset.Ico (j + 1) n,
      gridSlope φ n k * (min x (((k : ℝ) + 1) / n) - min x ((k : ℝ) / n)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : j + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk1 : (j : ℝ) + 1 ≤ k := by exact_mod_cast hk'
    have h1 : min x (((k : ℝ) + 1) / n) = x :=
      min_eq_left (le_trans hx.2 (by gcongr; linarith))
    have h2 : min x ((k : ℝ) / n) = x := min_eq_left (le_trans hx.2 (by gcongr))
    rw [h1, h2, sub_self, mul_zero]
  have hC : min x (((j : ℝ) + 1) / n) - min x ((j : ℝ) / n) = x - (j : ℝ) / n := by
    rw [min_eq_left hx.2, min_eq_right hx.1]
  rw [hA, hB, hC]
  ring

theorem gridInterp_mem_cell {φ : ℝ → ℝ} (hmono : MonotoneOn φ (Icc 0 1)) {n j : ℕ}
    (hj : j < n) {x : ℝ} (hx : x ∈ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n)) :
    gridInterp φ n x ∈ Icc (φ ((j : ℝ) / n)) (φ (((j : ℝ) + 1) / n)) := by
  rw [gridInterp_eval φ hj hx]
  have hs := gridSlope_nonneg hmono n j
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  constructor
  · nlinarith [hx.1]
  · have h1 : gridSlope φ n j * (x - (j : ℝ) / n) ≤ gridSlope φ n j * (1 / n) := by
      apply mul_le_mul_of_nonneg_left _ hs
      have : ((j : ℝ) + 1) / n = (j : ℝ) / n + 1 / n := by ring
      linarith [hx.2]
    have h2 : gridSlope φ n j * (1 / n) = φ (((j : ℝ) + 1) / n) - φ ((j : ℝ) / n) := by
      rw [gridSlope_of_lt φ hj]
      field_simp
    linarith

theorem floor_cell {n : ℕ} (hn : 0 < n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ⌊(n : ℝ) * x⌋₊ < n ∧
      x ∈ Icc ((⌊(n : ℝ) * x⌋₊ : ℝ) / n) (((⌊(n : ℝ) * x⌋₊ : ℝ) + 1) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.floor_lt (by positivity)]
    nlinarith
  · rw [div_le_iff₀ hn']
    linarith [Nat.floor_le (a := (n : ℝ) * x) (by positivity)]
  · rw [le_div_iff₀ hn']
    linarith [Nat.lt_floor_add_one ((n : ℝ) * x)]

theorem exists_cell {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∃ j < n, x ∈ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h1 : x < 1
  · obtain ⟨h, hmem⟩ := floor_cell hn hx.1.le h1
    exact ⟨_, h, hmem⟩
  · have hx1 : x = 1 := le_antisymm hx.2 (not_lt.mp h1)
    refine ⟨n - 1, by omega, ?_⟩
    rw [Nat.cast_pred hn, hx1, sub_add_cancel, div_self hn'.ne']
    exact ⟨(div_le_one hn').mpr (by linarith), le_rfl⟩

/-- `φ 0 ≤ gridInterp φ n x ≤ φ 1` on `(0,1]`. -/
theorem gridInterp_bounds {φ : ℝ → ℝ} (hmono : MonotoneOn φ (Icc 0 1)) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) : gridInterp φ n x ∈ Icc (φ 0) (φ 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gridInterp]
    exact hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  · obtain ⟨j, hj, hxj⟩ := exists_cell hn hx
    obtain ⟨h1, h2⟩ := cell_mem_Icc hj
    have h := gridInterp_mem_cell hmono hj hxj
    exact ⟨(hmono ⟨le_rfl, zero_le_one⟩ h1 h1.1).trans h.1,
      h.2.trans (hmono h2 ⟨zero_le_one, le_rfl⟩ h2.2)⟩

/-- An increasing concave function on `[0,1]` is continuous on `(0,1]`
(left-continuity at `1` from the chord bound). -/
theorem concave_continuousOn_Ioc {φ : ℝ → ℝ} (hmono : MonotoneOn φ (Icc 0 1))
    (hconc : ConcaveOn ℝ (Icc 0 1) φ) : ContinuousOn φ (Ioc 0 1) := by
  apply ConcaveOn.continuousOn_Ioc (hconc.subset Ioc_subset_Icc_self (convex_Ioc 0 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun y => (1 - y) * φ 0 + y * φ 1)
    (h := fun _ => φ 1)
  · have : Continuous fun y : ℝ => (1 - y) * φ 0 + y * φ 1 := by fun_prop
    have h : Tendsto (fun y : ℝ => (1 - y) * φ 0 + y * φ 1) (𝓝[Iic 1] 1)
        (𝓝 ((1 - 1) * φ 0 + 1 * φ 1)) := (this.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa using h
  · exact tendsto_const_nhds
  · filter_upwards [Icc_mem_nhdsLE zero_lt_one] with y hy
    have := hconc.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
      (sub_nonneg.mpr hy.2) hy.1 (by ring)
    simpa using this
  · filter_upwards [Icc_mem_nhdsLE zero_lt_one] with y hy
    exact hmono hy (right_mem_Icc.mpr zero_le_one) hy.2

theorem tendsto_gridInterp {φ : ℝ → ℝ} (hmono : MonotoneOn φ (Icc 0 1))
    (hconc : ConcaveOn ℝ (Icc 0 1) φ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun n => gridInterp φ n x) atTop (𝓝 (φ x)) := by
  by_cases h1 : x < 1
  · have hcont : ContinuousAt φ x :=
      (continuousWithinAt_iff_continuousAt (Ioc_mem_nhds hx.1 h1)).mp
        (concave_continuousOn_Ioc hmono hconc x hx)
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have ha : Tendsto (fun n : ℕ => (⌊(n : ℝ) * x⌋₊ : ℝ) / n) atTop (𝓝 x) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n : ℕ => x - 1 / n)
        (h := fun _ => x)
      · simpa using tendsto_const_nhds.sub hinv
      · exact tendsto_const_nhds
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [le_div_iff₀ hn', sub_mul, one_div, inv_mul_cancel₀ hn'.ne']
        linarith [Nat.lt_floor_add_one ((n : ℝ) * x), mul_comm (n : ℝ) x]
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [div_le_iff₀ hn']
        linarith [Nat.floor_le (a := (n : ℝ) * x) (mul_nonneg hn'.le hx.1.le), mul_comm (n : ℝ) x]
    have hb : Tendsto (fun n : ℕ => ((⌊(n : ℝ) * x⌋₊ : ℝ) + 1) / n) atTop (𝓝 x) := by
      have : (fun n : ℕ => ((⌊(n : ℝ) * x⌋₊ : ℝ) + 1) / n)
          = fun n : ℕ => (⌊(n : ℝ) * x⌋₊ : ℝ) / n + 1 / n := by
        funext n; ring
      rw [this]
      simpa using ha.add hinv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hcont.tendsto.comp ha)
      (hcont.tendsto.comp hb)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨hj, hxj⟩ := floor_cell hn hx.1.le h1
      exact (gridInterp_mem_cell hmono hj hxj).1
    · filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨hj, hxj⟩ := floor_cell hn hx.1.le h1
      exact (gridInterp_mem_cell hmono hj hxj).2
  · have hx1 : x = 1 := le_antisymm hx.2 (not_lt.mp h1)
    subst hx1
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hj : n - 1 < n := by omega
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_pred hn
    have hmem : (1 : ℝ) ∈ Icc (((n - 1 : ℕ) : ℝ) / n) ((((n - 1 : ℕ) : ℝ) + 1) / n) := by
      rw [hcast, sub_add_cancel, div_self hn'.ne']
      exact ⟨(div_le_one hn').mpr (by linarith), le_rfl⟩
    rw [gridInterp_eval φ hj hmem, gridSlope_of_lt φ hj, hcast, sub_add_cancel, div_self hn'.ne']
    field_simp
    ring

/-! ### Passage to the limit -/

/-- Dominated convergence: `𝔼 L_n(Z_S) → 𝔼 φ(Z_S)` for the grid interpolants. -/
theorem tendsto_expectPhi_gridInterp {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) {φ : ℝ → ℝ}
    (hmono : MonotoneOn φ (Icc 0 1)) (hconc : ConcaveOn ℝ (Icc 0 1) φ) :
    Tendsto (fun n => expectPhi S (gridInterp φ n)) atTop (𝓝 (expectPhi S φ)) := by
  unfold expectPhi
  apply tendsto_integral_of_dominated_convergence (fun _ => max |φ 0| |φ 1|)
  · intro n
    exact (gridInterp_continuous φ n).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [bottleneckCDF_ae_mem_Ioc hS] with x hx
    obtain ⟨h1, h2⟩ := gridInterp_bounds hmono n hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (φ 0), le_max_left |φ 0| |φ 1|]
    · linarith [le_abs_self (φ 1), le_max_right |φ 0| |φ 1|]
  · filter_upwards [bottleneckCDF_ae_mem_Ioc hS] with x hx
    exact tendsto_gridInterp hmono hconc hx

/-- **Corollary 1.5.** For increasing concave `φ` on `[0,1]`,
`𝔼 φ(Z_{𝒫_N}) ≤ 𝔼 φ(Z_A)`.  Proof: the uniform-grid interpolants `L_n` of `φ` are
nonnegative hinge combinations `φ(0) + ∑ (s_k - s_{k+1}) min(x, (k+1)/n)` (slopes
`s_k` nonincreasing by concavity, nonnegative by monotonicity), so
`𝔼 L_n(Z_{𝒫_N}) ≤ 𝔼 L_n(Z_A)` by `expectPhi_hinge` and Theorem 1.1; `L_n → φ`
pointwise on `(0,1]` (where both laws live and `φ` is continuous), and
dominated convergence passes to the limit.  This replaces the paper's Stieltjes
representation `φ(x) = φ(0⁺) + a x + ∫ min(x,t) μ(dt)` by its discrete version. -/
theorem icv_minimality {N : ℕ} {A : Finset ℕ} (hA : IsPrimitiveFin A)
    (hAN : ∀ a ∈ A, a ≤ N) {φ : ℝ → ℝ}
    (hmono : MonotoneOn φ (Icc 0 1)) (hconc : ConcaveOn ℝ (Icc 0 1) φ) :
    expectPhi (primesLE N) φ ≤ expectPhi A φ := by
  have hP : ∀ n ∈ primesLE N, 1 ≤ n := fun n hn => (mem_primesLE.mp hn).1.one_lt.le
  have hA1 : ∀ n ∈ A, 1 ≤ n := fun n hn => by
    have := hA.1 n (Finset.mem_coe.mpr hn)
    omega
  refine le_of_tendsto_of_tendsto' (tendsto_expectPhi_gridInterp hP hmono hconc)
    (tendsto_expectPhi_gridInterp hA1 hmono hconc) (fun n => ?_)
  exact expectPhi_hingeSum_le hA hAN (φ 0) (fun k => gridSlope φ n k - gridSlope φ n (k + 1))
    (fun k => ((k : ℝ) + 1) / n)
    (fun k _ => sub_nonneg.mpr (gridSlope_succ_le hmono hconc n k))
    (fun k hk => ⟨div_pos (by positivity) (by exact_mod_cast (show 0 < n by omega)),
      (cell_mem_Icc hk).2.2⟩)

/-! ## Proposition 5.1 (integer `k ∈ {1,2}`) -/

/-- `∫₀ᶜ k u^{k-1} P_S(u) du = 𝔼 min(Z_Sᵏ, cᵏ)`. -/
noncomputable def Mc (k : ℕ) (c : ℝ) (S : Finset ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..c, (k : ℝ) * u ^ (k - 1) * qProd S u

theorem Mc_one (c : ℝ) (S : Finset ℕ) : Mc 1 c S = Fc c S := by
  unfold Mc Fc
  simp

/-- `𝔼 Z_Sᵏ = k · moment S (k-1)` in LeanCert's notation. -/
theorem Mc_one_eq_moment (k : ℕ) (_hk : 1 ≤ k) (S : Finset ℕ) :
    Mc k 1 S = k * moment S (k - 1) := by
  unfold Mc moment
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext u
  ring

/-! ### The `k = 2` engine: weight `2u`

Ports of the Section 3 machinery with the integrand `P_A(u)` replaced by
`2u·P_A(u)`.  The key new point is `running_pos_two_mul_comp_pow`: for a prime
`p ≥ 2`, `∫₀ʸ 2u·E_T(uᵖ) du > 0`, proved by integration by parts on `[ε, y]`
against the antiderivative `A(u) = G(uᵖ)`, `G(t) = ∫₀ᵗ E_T`, with the singular
but nonincreasing weight `w(u) = 2/(p·u^{p-2})`, and `ε → 0`. -/

/-- `|E_T(v)| ≤ 1` on `[0,1]`. -/
theorem abs_blockE_le_one (T : Finset ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    |blockE T v| ≤ 1 := by
  unfold blockE
  have h0 := qProd_nonneg T hv
  have h1 := qProd_le_one T hv
  rw [abs_le]
  constructor <;> linarith [hv.1, hv.2]

/-- `G(t) = ∫₀ᵗ E_T` satisfies `|G(t)| ≤ t` on `[0,1]`. -/
theorem abs_integral_blockE_le (T : Finset ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |∫ v in (0 : ℝ)..t, blockE T v| ≤ t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
    (f := blockE T) (fun x hx => by
      rw [uIoc_of_le ht.1] at hx
      exact abs_blockE_le_one T ⟨hx.1.le, hx.2.trans ht.2⟩)
  simpa [abs_of_nonneg ht.1] using h

/-- **Corollary 3.2 with weight `2u`.** For `p ≥ 2`, `∫₀ʸ 2u·E_T(uᵖ) du > 0`. -/
theorem running_pos_two_mul_comp_pow {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {p : ℕ}
    (hp : 2 ≤ p) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..y, 2 * u * blockE T (u ^ p) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  have hEc : Continuous (blockE T) := continuous_blockE T
  -- the integrand and its continuity
  set f : ℝ → ℝ := fun u => 2 * u * blockE T (u ^ (m + 2)) with hf
  have hfc : Continuous f := by
    simp only [hf]
    exact (continuous_const.mul continuous_id).mul (hEc.comp (continuous_pow _))
  -- G and A = G ∘ (·^(m+2))
  set G : ℝ → ℝ := fun t => ∫ v in (0 : ℝ)..t, blockE T v with hG
  have hGpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < G t := fun t ht => by
    have := running_pos_comp_pow_pos hT (le_refl 1) ht
    simpa [hG] using this
  have hGderiv : ∀ t, HasDerivAt G (blockE T t) t := fun t =>
    (hEc.integral_hasStrictDerivAt 0 t).hasDerivAt
  set A : ℝ → ℝ := fun u => G (u ^ (m + 2)) with hA
  have hAderiv : ∀ u, HasDerivAt A (blockE T (u ^ (m + 2)) * ((m + 2 : ℕ) * u ^ (m + 1))) u :=
    fun u => by
      have h1 : HasDerivAt (fun x : ℝ => x ^ (m + 2)) ((m + 2 : ℕ) * u ^ (m + 2 - 1)) u :=
        hasDerivAt_pow (m + 2) u
      have h2 : HasDerivAt (G ∘ fun x : ℝ => x ^ (m + 2))
          (blockE T (u ^ (m + 2)) * ((m + 2 : ℕ) * u ^ (m + 2 - 1))) u :=
        HasDerivAt.comp (h := fun x : ℝ => x ^ (m + 2)) u (hGderiv (u ^ (m + 2))) h1
      have h3 : m + 2 - 1 = m + 1 := by omega
      rw [h3] at h2
      exact h2
  have hApos : ∀ u ∈ Ioc (0 : ℝ) 1, 0 < A u := fun u hu =>
    hGpos _ ⟨pow_pos hu.1 _, pow_le_one₀ hu.1.le hu.2⟩
  have hAle : ∀ u ∈ Icc (0 : ℝ) 1, A u ≤ u ^ (m + 2) := fun u hu =>
    (le_abs_self _).trans (abs_integral_blockE_le T ⟨pow_nonneg hu.1 _, pow_le_one₀ hu.1 hu.2⟩)
  -- the weight w(u) = 2 / ((m+2) u^m) and its derivative
  set w : ℝ → ℝ := fun u => 2 * ((m + 2 : ℕ) * u ^ m)⁻¹ with hw
  set w' : ℝ → ℝ := fun u => 2 * (-((m + 2 : ℕ) * ((m : ℕ) * u ^ (m - 1))) / ((m + 2 : ℕ) * u ^ m) ^ 2)
    with hw'
  have hwderiv : ∀ u : ℝ, 0 < u → HasDerivAt w (w' u) u := fun u hu => by
    have h1 : HasDerivAt (fun u : ℝ => (m + 2 : ℕ) * u ^ m) ((m + 2 : ℕ) * ((m : ℕ) * u ^ (m - 1))) u :=
      (hasDerivAt_pow m u).const_mul _
    have hne : ((m + 2 : ℕ) : ℝ) * u ^ m ≠ 0 := by positivity
    have h2 := (h1.inv hne).const_mul (2 : ℝ)
    simpa [hw, hw'] using h2
  have hw'nonpos : ∀ u : ℝ, 0 < u → w' u ≤ 0 := fun u hu => by
    simp only [hw']
    have hnum : 0 ≤ ((m + 2 : ℕ) : ℝ) * ((m : ℕ) * u ^ (m - 1)) := by positivity
    have hden : 0 ≤ (((m + 2 : ℕ) : ℝ) * u ^ m) ^ 2 := by positivity
    have := div_nonneg hnum hden
    rw [neg_div]
    linarith
  have hwpos : ∀ u : ℝ, 0 < u → 0 < w u := fun u hu => by
    simp only [hw]; positivity
  have hwA : ∀ u : ℝ, 0 < u →
      w u * (blockE T (u ^ (m + 2)) * ((m + 2 : ℕ) * u ^ (m + 1))) = f u := fun u hu => by
    simp only [hw, hf]
    have hum : u ^ m ≠ 0 := pow_ne_zero _ hu.ne'
    have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  -- the lower bound L = w(y) A(y) > 0
  set L := w y * A y with hL
  have hLpos : 0 < L := mul_pos (hwpos y hy.1) (hApos y hy)
  -- choose ε
  set ε := min (y / 2) (L / 8) with hε
  have hε0 : 0 < ε := lt_min (by linarith [hy.1]) (by linarith)
  have hεy : ε < y := (min_le_left _ _).trans_lt (by linarith [hy.1])
  have hεL : ε ≤ L / 8 := min_le_right _ _
  have hε1 : ε ≤ 1 / 2 := (min_le_left _ _).trans (by linarith [hy.2])
  -- integration by parts on [ε, y]
  have hIcc : uIcc ε y = Icc ε y := uIcc_of_le hεy.le
  have hw'cont : ContinuousOn w' (uIcc ε y) := by
    rw [hIcc]
    simp only [hw']
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := y)
    (u := w) (v := A) (u' := w')
    (v' := fun u => blockE T (u ^ (m + 2)) * ((m + 2 : ℕ) * u ^ (m + 1)))
    (fun x hx => hwderiv x (by rw [hIcc] at hx; linarith [hx.1]))
    (fun x _ => hAderiv x)
    (hw'cont.intervalIntegrable)
    ((hEc.comp (continuous_pow _)).mul (continuous_const.mul (continuous_pow _))
      |>.intervalIntegrable _ _)
  have hcongr : ∫ u in ε..y, f u
      = ∫ u in ε..y, w u * (blockE T (u ^ (m + 2)) * ((m + 2 : ℕ) * u ^ (m + 1))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hIcc] at hx
    exact (hwA x (by linarith [hx.1])).symm
  have htail : ∫ u in ε..y, w' u * A u ≤ 0 := by
    have h := intervalIntegral.integral_nonneg (f := fun u => -(w' u * A u)) (μ := volume)
      hεy.le (fun u hu => by
        have := mul_nonpos_of_nonpos_of_nonneg (hw'nonpos u (by linarith [hu.1]))
          (hApos u ⟨by linarith [hu.1], hu.2.trans hy.2⟩).le
        linarith)
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hwεAε : w ε * A ε ≤ 2 * ε ^ 2 := by
    have h1 : w ε * A ε ≤ w ε * ε ^ (m + 2) :=
      mul_le_mul_of_nonneg_left (hAle ε ⟨hε0.le, by linarith⟩) (hwpos ε hε0).le
    have h2 : w ε * ε ^ (m + 2) = 2 * ε ^ 2 / (m + 2 : ℕ) := by
      simp only [hw]
      have hum : ε ^ m ≠ 0 := pow_ne_zero _ hε0.ne'
      have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have h3 : 2 * ε ^ 2 / (m + 2 : ℕ) ≤ 2 * ε ^ 2 := by
      apply div_le_self (by positivity)
      exact_mod_cast (by omega : 1 ≤ m + 2)
    linarith
  have hmid : L - 2 * ε ^ 2 ≤ ∫ u in ε..y, f u := by
    rw [hcongr, hibp]
    linarith
  -- the initial piece [0, ε]
  have hhead : -(2 * ε) ≤ ∫ u in (0 : ℝ)..ε, f u := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ε) (C := 2)
      (f := f) (fun x hx => by
        rw [uIoc_of_le hε0.le] at hx
        have hx1 : x ≤ 1 := by linarith [hx.2]
        simp only [hf, Real.norm_eq_abs, abs_mul, abs_two, abs_of_pos hx.1]
        have hE : |blockE T (x ^ (m + 2))| ≤ 1 :=
          abs_blockE_le_one T (v := x ^ (m + 2)) ⟨pow_nonneg hx.1.le _, pow_le_one₀ hx.1.le hx1⟩
        have h1 : 2 * x * |blockE T (x ^ (m + 2))| ≤ 2 * x * 1 :=
          mul_le_mul_of_nonneg_left hE (by linarith [hx.1])
        linarith)
    rw [Real.norm_eq_abs, abs_le] at h
    simpa [abs_of_pos hε0] using h.1
  have hsplit : ∫ u in (0 : ℝ)..y, f u = (∫ u in (0 : ℝ)..ε, f u) + ∫ u in ε..y, f u :=
    (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)).symm
  show 0 < ∫ u in (0 : ℝ)..y, f u
  rw [hsplit]
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  nlinarith

/-- Identity (1.2) with weight `2u`. -/
theorem Mc2_blockStep_diff {B T : Finset ℕ} {p : ℕ} (hp : 0 < p)
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B) (c : ℝ) :
    Mc 2 c (B ∪ T.image (· * p)) - Mc 2 c (insert p B)
      = ∫ u in (0 : ℝ)..c, qProd B u * (2 * u * blockE T (u ^ p)) := by
  classical
  have hinj : Set.InjOn (· * p) (T : Set ℕ) := fun a _ b _ h =>
    Nat.eq_of_mul_eq_mul_right hp h
  have hpt : ∀ u : ℝ, qProd (B ∪ T.image (· * p)) u - qProd (insert p B) u
      = qProd B u * blockE T (u ^ p) := by
    intro u
    unfold qProd blockE
    rw [Finset.prod_union hdisj, Finset.prod_insert hpB, Finset.prod_image hinj]
    simp_rw [pow_mul']
    unfold qProd
    ring
  unfold Mc
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro u _
    simp only
    have := hpt u
    norm_num
    linear_combination (2 * u) * this
  · exact ((continuous_const.mul (continuous_pow _)).mul (qProd_continuous _)).intervalIntegrable _ _
  · exact ((continuous_const.mul (continuous_pow _)).mul (qProd_continuous _)).intervalIntegrable _ _

/-- **Proposition 3.4 with weight `2u`**, finite sets. -/
theorem Mc2_block_exchange_lt {B T : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hB : ∀ b ∈ B, 2 ≤ b) (hT : ∀ t ∈ T, 2 ≤ t)
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mc 2 c (insert p B) < Mc 2 c (B ∪ T.image (· * p)) := by
  rw [← sub_pos, Mc2_blockStep_diff hp.pos hdisj hpB]
  refine integral_weight_mul_pos_upto (g := fun u => 2 * u * blockE T (u ^ p))
    (w := qProd B) (w' := qProd' B) hc ?_ (fun x _ => hasDerivAt_qProd B x)
    (continuous_qProd' B) (qProd_nonneg B ⟨hc.1.le, hc.2⟩) ?_ ?_ ?_
  · exact (continuous_const.mul continuous_id).mul
      ((continuous_blockE T).comp (continuous_pow p))
  · intro x hx
    exact qProd'_nonpos B ⟨hx.1, hx.2.trans hc.2⟩
  · intro y hy
    exact running_pos_two_mul_comp_pow hT hp.two_le ⟨hy.1, hy.2.trans hc.2⟩
  · rcases hc.2.lt_or_eq with hc1 | hc1
    · left
      exact qProd_pos_of_lt_one (fun n hn => by have := hB n hn; omega) ⟨hc.1.le, hc1⟩
    · rcases B.eq_empty_or_nonempty with hBe | hBne
      · left
        simp [hBe]
      · right
        refine ⟨1 / 2, ⟨by norm_num, by rw [hc1]; norm_num⟩, ?_⟩
        exact qProd'_neg_of_nonempty hBne (fun n hn => by have := hB n hn; omega)
          ⟨by norm_num, by norm_num⟩

/-- Decomposition `A = B ∪ p·T` with `B = {a ∈ A : p ∤ a}` and `T` the quotients. -/
theorem eq_filter_union_image_quotients (p : ℕ) (A : Finset ℕ) :
    A = A.filter (fun a => ¬ p ∣ a) ∪ (quotients p A).image (· * p) := by
  classical
  ext a
  simp only [Finset.mem_union, Finset.mem_filter, quotients, Finset.mem_image]
  constructor
  · intro ha
    by_cases h : p ∣ a
    · right
      exact ⟨a / p, ⟨a, ⟨ha, h⟩, rfl⟩, Nat.div_mul_cancel h⟩
    · exact Or.inl ⟨ha, h⟩
  · rintro (⟨ha, -⟩ | ⟨t, ⟨b, ⟨hb, hpb⟩, rfl⟩, rfl⟩)
    · exact ha
    · rwa [Nat.div_mul_cancel hpb]

/-- Strict compression with weight `2u` (needs `p ∉ A`; if `p ∈ A` then
`compressAt p A = A`). -/
theorem Mc2_compressAt_lt {A : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hA : IsPrimitiveFin A) (hpA : p ∉ A) (hmult : ∃ a ∈ A, p ∣ a)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mc 2 c (compressAt p A) < Mc 2 c A := by
  classical
  set B := A.filter (fun a => ¬ p ∣ a) with hB
  set T := quotients p A with hT
  have hdecomp : A = B ∪ T.image (· * p) := eq_filter_union_image_quotients p A
  have hB2 : ∀ b ∈ B, 2 ≤ b := fun b hb => hA.1 b (Finset.mem_filter.mp hb).1
  have hT2 : ∀ t ∈ T, 2 ≤ t := by
    intro t ht
    simp only [hT, quotients, Finset.mem_image, Finset.mem_filter] at ht
    obtain ⟨a, ⟨haA, hpa⟩, rfl⟩ := ht
    have ha2 : 2 ≤ a := hA.1 a haA
    have hne : a ≠ p := fun h => hpA (h ▸ haA)
    obtain ⟨k, rfl⟩ := hpa
    rw [Nat.mul_div_cancel_left _ hp.pos]
    rcases k with _ | _ | k
    · omega
    · exact absurd (by ring) hne
    · omega
  have hdisj : Disjoint B (T.image (· * p)) := by
    rw [Finset.disjoint_left]
    intro b hb hbT
    simp only [Finset.mem_image] at hbT
    obtain ⟨t, -, rfl⟩ := hbT
    exact (Finset.mem_filter.mp hb).2 (dvd_mul_left p t)
  have hpB : p ∉ B := fun h => (Finset.mem_filter.mp h).2 (dvd_refl p)
  have h := Mc2_block_exchange_lt hp hB2 hT2 hdisj hpB hc
  rw [← hdecomp] at h
  exact h

/-- Adding a missing exponent strictly lowers `M_c` (weight `2u`). -/
theorem Mc2_insert_lt {R : Finset ℕ} {q : ℕ} (hq : q ∉ R) (hR : ∀ n ∈ R, 1 ≤ n)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mc 2 c (insert q R) < Mc 2 c R := by
  rw [← sub_pos]
  unfold Mc
  have hint : ∀ S : Finset ℕ,
      IntervalIntegrable (fun u : ℝ => ((2 : ℕ) : ℝ) * u ^ (2 - 1) * qProd S u) volume 0 c :=
    fun S => ((continuous_const.mul (continuous_pow _)).mul (qProd_continuous S)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub (hint R) (hint (insert q R))]
  have hpt : ∀ u : ℝ, (2 : ℕ) * u ^ (2 - 1) * qProd R u - (2 : ℕ) * u ^ (2 - 1) * qProd (insert q R) u
      = 2 * u * (u ^ q * qProd R u) := by
    intro u
    unfold qProd
    rw [Finset.prod_insert hq]
    norm_num
    ring
  simp_rw [hpt]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact ((continuous_const.mul continuous_id).mul
      ((continuous_pow q).mul (qProd_continuous R))).intervalIntegrable _ _
  · intro u hu
    have hR' : 0 < qProd R u := qProd_pos_of_lt_one hR ⟨hu.1.le, hu.2.trans_le hc.2⟩
    have hq' : 0 < u ^ q := pow_pos hu.1 q
    exact mul_pos (mul_pos two_pos hu.1) (mul_pos hq' hR')
  · exact hc.1

/-! ### Abstract descent -/

/-- Strict descent measure, with the hypothesis `p ∉ A` (if `p ∈ A` then
`compressAt p A = A`). -/
theorem sum_compressAt_lt' {A : Finset ℕ} {p : ℕ} (hpA : p ∉ A) (hA : IsPrimitiveFin A)
    (hmult : ∃ a ∈ A, p ∣ a) : (compressAt p A).sum id < A.sum id := by
  classical
  obtain ⟨a, haA, hpa⟩ := hmult
  have hB : A.filter (fun x => ¬ p ∣ x) ⊆ A.erase a := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_erase]
    refine ⟨?_, hx.1⟩
    rintro rfl
    exact hx.2 hpa
  have hpB : p ∉ A.filter (fun x => ¬ p ∣ x) := by simp
  unfold compressAt
  rw [Finset.sum_insert hpB]
  have h1 : (A.filter (fun x => ¬ p ∣ x)).sum id ≤ (A.erase a).sum id :=
    Finset.sum_le_sum_of_subset hB
  have h2 := Finset.sum_erase_add A id haA
  have hpa' : p < a := by
    have hle := Nat.le_of_dvd (by have := hA.1 a haA; omega) hpa
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ haA) hpA
  simp only [id] at h1 h2 ⊢
  omega

/-- **Abstract descent.** A functional `J` on finite exponent sets that strictly
decreases under prime compression at a prime `p ∉ A` dividing some element, and
under insertion of a missing exponent, is uniquely minimised over primitive
subsets of `[2,N]` by `𝒫_N`. -/
theorem descent_lt {J : Finset ℕ → ℝ} {N : ℕ}
    (hcomp : ∀ (A : Finset ℕ) (p : ℕ), IsPrimitiveFin A → Nat.Prime p → p ∉ A →
      (∃ a ∈ A, p ∣ a) → J (compressAt p A) < J A)
    (hins : ∀ (R : Finset ℕ) (q : ℕ), q ∉ R → (∀ n ∈ R, 1 ≤ n) → J (insert q R) < J R)
    {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N) :
    J (primesLE N) < J A := by
  classical
  -- all-prime sets: insert the missing primes one at a time
  have hprime : ∀ (n : ℕ) (R : Finset ℕ), (primesLE N \ R).card = n → R ⊆ primesLE N →
      R ≠ primesLE N → J (primesLE N) < J R := by
    intro n
    induction n with
    | zero =>
      intro R hcard hsub hne
      have h := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard)
      exact absurd (Finset.Subset.antisymm hsub h) hne
    | succ n ih =>
      intro R hcard hsub hne
      obtain ⟨q, hq⟩ : (primesLE N \ R).Nonempty := by
        rw [← Finset.card_pos]; omega
      have hq' := Finset.mem_sdiff.mp hq
      have hR1 : ∀ x ∈ R, 1 ≤ x := fun x hx => (mem_primesLE.mp (hsub hx)).1.one_lt.le
      have hlt := hins R q hq'.2 hR1
      have hsub' : insert q R ⊆ primesLE N := Finset.insert_subset hq'.1 hsub
      by_cases heq : insert q R = primesLE N
      · rw [← heq]; exact hlt
      · have hcard' : (primesLE N \ insert q R).card = n := by
          rw [Finset.sdiff_insert, Finset.card_erase_of_mem hq, hcard]
          rfl
        exact (ih _ hcard' hsub' heq).trans hlt
  -- general sets: strong induction on the element sum
  have main : ∀ (n : ℕ) (A : Finset ℕ), A.sum id = n → IsPrimitiveFin A →
      (∀ a ∈ A, a ≤ N) → A ≠ primesLE N → J (primesLE N) < J A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hsum hA hAN hne
      by_cases hall : ∀ a ∈ A, Nat.Prime a
      · exact hprime _ A rfl (fun a ha => mem_primesLE.mpr ⟨hall a ha, hAN a ha⟩) hne
      · push Not at hall
        obtain ⟨a, haA, hnp⟩ := hall
        have ha2 : 2 ≤ a := hA.1 a haA
        obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
        have hpne : p ≠ a := fun h => hnp (h ▸ hp)
        have hpA : p ∉ A := fun hpA => hpne (hA.2 p hpA a haA hpa)
        have hmult : ∃ a ∈ A, p ∣ a := ⟨a, haA, hpa⟩
        have hstep := hcomp A p hA hp hpA hmult
        have hA' := compressAt_isPrimitiveFin hA hp hmult
        have hAN' := compressAt_bounded hA hAN hmult
        have hlt := sum_compressAt_lt' hpA hA hmult
        by_cases heq : compressAt p A = primesLE N
        · rw [← heq]; exact hstep
        · exact (ih _ (hsum ▸ hlt) _ rfl hA' hAN' heq).trans hstep
  exact main _ A rfl hA hAN hne

/-- **Proposition 5.1**, `k ∈ {1,2}`.  `k = 1` is Theorem 1.1; `k = 2` runs the
abstract descent with the weight-`2u` engine above. -/
theorem Mc_primesLE_lt {k : ℕ} (hk : k = 1 ∨ k = 2) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mc k c (primesLE N) < Mc k c A := by
  rcases hk with rfl | rfl
  · rw [Mc_one, Mc_one]
    exact Fc_primesLE_lt hA hAN hne hc
  · exact descent_lt (J := Mc 2 c)
      (fun A p hA hp hpA hmult => Mc2_compressAt_lt hp hA hpA hmult hc)
      (fun R q hq hR => Mc2_insert_lt hq hR hc) hA hAN hne

/-! ## Open problem 2: large `k` -/

/-- At `N = 9` the antichain `{4,5,6,7,9}` beats the primes for `k = 126`
(`𝔼 Zᵏ = k · moment S (k-1)`); exact rational check via LeanCert's `momentRat`. -/
theorem A9_beats_primes_at_126 :
    moment (A9 9) 125 < moment (primesLE 9) 125 := by
  rw [← momentRat_correct, ← momentRat_correct]
  exact_mod_cast (by native_decide : momentRat (A9 9) 125 < momentRat (primesLE 9) 125)

/-- ... and not for `k = 125`. -/
theorem primes_beat_A9_at_125 :
    moment (primesLE 9) 124 < moment (A9 9) 124 := by
  rw [← momentRat_correct, ← momentRat_correct]
  exact_mod_cast (by native_decide : momentRat (primesLE 9) 124 < momentRat (A9 9) 124)

/-! ## Proposition 5.2 (tail bound, `R = {2}`) -/

/-- The sharp tail kernel `K_{{2}}(q) = ∫₀¹ x^q (1 - x²) dx = 2/((q+1)(q+3))`. -/
noncomputable def tailKernel (q : ℕ) : ℝ := 2 / ((q : ℝ) + 1) / ((q : ℝ) + 3)

theorem tailKernel_nonneg (q : ℕ) : 0 ≤ tailKernel q := by
  unfold tailKernel
  positivity

theorem integral_one_sub_sq_mul_pow (q : ℕ) :
    (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * u ^ q) = tailKernel q := by
  have hint1 : IntervalIntegrable (fun u : ℝ => u ^ q) volume (0 : ℝ) 1 :=
    (continuous_id.pow q).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun u : ℝ => u ^ (q + 2)) volume (0 : ℝ) 1 :=
    (continuous_id.pow (q + 2)).intervalIntegrable 0 1
  have hcongr : (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * u ^ q)
      = ∫ u in (0 : ℝ)..1, (u ^ q - u ^ (q + 2)) := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    ring
  rw [hcongr, intervalIntegral.integral_sub hint1 hint2, integral_pow, integral_pow]
  unfold tailKernel
  push_cast
  field_simp
  ring

/-- Enlarging a set `S ∋ 2` to `T ⊇ S` lowers `F` by at most
`∑_{q ∈ T∖S} K_{{2}}(q)` (port of productinvariants `sharp_error_bound_two_over`). -/
theorem F_sub_le_sum_tailKernel {S T : Finset ℕ} (hST : S ⊆ T) (h2 : 2 ∈ S) :
    F S - F T ≤ ∑ q ∈ T \ S, tailKernel q := by
  have hpt : ∀ u ∈ Icc (0 : ℝ) 1,
      qProd S u - qProd T u ≤ ∑ q ∈ T \ S, (1 - u ^ 2) * u ^ q := by
    intro u hu
    have h := qProd_sub_le_commonPrefix_sum (R := {2}) (S := S) (T := T)
      (Finset.singleton_subset_iff.mpr h2) hST hu
    have h2' : qProd ({2} : Finset ℕ) u = 1 - u ^ 2 := by simp [qProd]
    rw [h2', Finset.mul_sum] at h
    exact h
  have hintS : IntervalIntegrable (fun u => qProd S u) volume (0 : ℝ) 1 :=
    (qProd_continuous S).intervalIntegrable 0 1
  have hintT : IntervalIntegrable (fun u => qProd T u) volume (0 : ℝ) 1 :=
    (qProd_continuous T).intervalIntegrable 0 1
  have hterm : ∀ q ∈ T \ S, IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) * u ^ q) volume 0 1 :=
    fun q _ => ((continuous_const.sub (continuous_id.pow 2)).mul
      (continuous_id.pow q)).intervalIntegrable 0 1
  have hintSum : IntervalIntegrable (fun u : ℝ => ∑ q ∈ T \ S, (1 - u ^ 2) * u ^ q) volume 0 1 :=
    (continuous_finsetSum (T \ S) fun q _ =>
      (continuous_const.sub (continuous_id.pow 2)).mul (continuous_id.pow q)).intervalIntegrable 0 1
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := fun u => qProd S u - qProd T u) (g := fun u => ∑ q ∈ T \ S, (1 - u ^ 2) * u ^ q)
    (by norm_num) (hintS.sub hintT) hintSum hpt
  rw [intervalIntegral.integral_sub hintS hintT,
    intervalIntegral.integral_finsetSum hterm] at hmono
  simp_rw [integral_one_sub_sq_mul_pow] at hmono
  exact hmono

/-- The infinite tail of primes strictly above `N`. -/
abbrev PrimeTail (N : ℕ) := {p : ℕ // Nat.Prime p ∧ N < p}

theorem tailKernel_le (p : ℕ) (hp : 0 < p) : tailKernel p ≤ 2 * (1 / ((p : ℝ) ^ 2)) := by
  unfold tailKernel
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_div, mul_one_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

theorem summable_tailKernel (N : ℕ) : Summable fun p : PrimeTail N => tailKernel p.1 := by
  have hpow : Summable fun p : PrimeTail N => 2 * (1 / ((p.1 : ℝ) ^ 2)) :=
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).subtype
      (fun p => Nat.Prime p ∧ N < p)).mul_left 2
  exact hpow.of_nonneg_of_le (fun p => tailKernel_nonneg p.1)
    (fun p => tailKernel_le p.1 p.2.1.pos)

theorem tail_bound_finite {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    F (primesLE N) - F (primesLE M) ≤ ∑ q ∈ primesLE M \ primesLE N, tailKernel q :=
  F_sub_le_sum_tailKernel (primesLE_subset hNM) (mem_primesLE.mpr ⟨Nat.prime_two, hN⟩)

theorem sum_sdiff_tailKernel_le_tsum (N M : ℕ) :
    ∑ q ∈ primesLE M \ primesLE N, tailKernel q ≤ ∑' p : PrimeTail N, tailKernel p.1 := by
  classical
  have hmem : ∀ q ∈ primesLE M \ primesLE N, Nat.Prime q ∧ N < q := by
    intro q hq
    rw [Finset.mem_sdiff, mem_primesLE, mem_primesLE] at hq
    exact ⟨hq.1.1, by by_contra h; exact hq.2 ⟨hq.1.1, by omega⟩⟩
  have hsum : ∑ q ∈ primesLE M \ primesLE N, tailKernel q
      = ∑ p ∈ (primesLE M \ primesLE N).subtype (fun p => Nat.Prime p ∧ N < p),
          tailKernel p.1 := by
    rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hmem]
  rw [hsum]
  exact (summable_tailKernel N).sum_le_tsum _ (fun p _ => tailKernel_nonneg p.1)

/-- `0 ≤ I_N - Λ ≤ ∑_{p>N} 2/((p+1)(p+3))` for `N ≥ 2`
(productinvariants `prime_phase_tail_bound`, restated over `primeLambda`). -/
theorem tail_bound {N : ℕ} (hN : 2 ≤ N) :
    F (primesLE N) - primeLambda
      ≤ ∑' p : {p : ℕ // Nat.Prime p ∧ N < p}, (2 : ℝ) / (((p : ℕ) : ℝ) + 1) / (((p : ℕ) : ℝ) + 3) := by
  have hlim : Tendsto (fun M => F (primesLE N) - F (primesLE M)) atTop
      (𝓝 (F (primesLE N) - primeLambda)) := by
    refine tendsto_const_nhds.sub ?_
    refine tendsto_primeFRat_primeLambda.congr (fun M => ?_)
    unfold primeFRat
    rw [finiteIntegralRat_correct]
  exact le_of_tendsto hlim (Filter.eventually_atTop.2
    ⟨N, fun M hNM => (tail_bound_finite hN hNM).trans (sum_sdiff_tailKernel_le_tsum N M)⟩)

theorem primeLambda_le_F_primesLE (N : ℕ) : primeLambda ≤ F (primesLE N) := by
  have h := primeLambda_le_trunc N
  unfold primeFRat at h
  rwa [finiteIntegralRat_correct] at h

end RntPaper
