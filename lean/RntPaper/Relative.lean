import RntPaper.RelativeCone

/-!
# Relative extremality: the general weight theorem and the power weights

* `relative_cone_iff`, `relative_cone_le`, `relative_cone_lt` (in `RelativeCone.lean`): for a
  weight `w ∈ L¹(0,1)`, `w ≥ 0`, `Min(U)` minimizes `F_{w,c}` over the primitive subsets of
  every `U ⊆ {2,3,…}` iff `∫₀¹ w(u) [Q(u^D) - (1 - u^D)] du ≥ 0` for every `D ≥ 2`.
* The threshold `α₀ = sup {b > 0 : J_b(1) > 0}` of `J_s(1) = ∫₀¹ x^{s-1}(Q(x) - (1-x)) dx`:
  `J_s(1) > 0` for `0 < s < α₀`, `J_s(1) < 0` for `s > α₀`, `J_{α₀}(1) = 0`, `17/8 < α₀ < 3`.
* Power weights `w = k u^{k-1}`: relative extremality over all finite `U` holds iff `k ≤ 2α₀`
  (`relative_powers_iff`); for `k > 2α₀` the set `2𝒫` beats `Min(U) = {2}` inside
  `U = 2ℕ_{≥1}` (`twoPrimes_moment_lt`).
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set Filter Topology

/-! ## `J_s(1)` for real `s > 0` -/

theorem abs_g_le_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |Qfun x - (1 - x)| ≤ 1 := by
  have h0 := Qfun_nonneg hx
  have h1 : Qfun x ≤ 1 := by
    rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h, Qfun_one]; norm_num
    · exact qProdSet_le_one _ hx.1 h
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem intervalIntegrable_Jw_integrand {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun x => x ^ (s - 1) * (Qfun x - (1 - x))) volume 0 1 := by
  refine (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s - 1)).mul_continuousOn
    ?_
  rw [uIcc_of_le zero_le_one]
  exact Qfun_continuousOn.sub (by fun_prop)

/-- **Variation diminishing.** If `J_b(1) ≥ 0` then `J_s(1) > 0` for every `0 < s < b`:
`(x^{s-b} - x*^{s-b}) x^{b-1} g(x) > 0` off the crossing point `x*` of `g = Q - (1 - x)`. -/
theorem Jw_one_pos_of_lt {b s : ℝ} (hs : 0 < s) (hsb : s < b) (hb : 0 ≤ Jw b 1) :
    0 < Jw s 1 := by
  obtain ⟨xs, hxs, hposo, hnego⟩ := Qfun_single_crossing
  set c := xs ^ (s - b) with hc
  have hb0 : 0 < b := hs.trans hsb
  have hneg : s - b < 0 := by linarith
  set f : ℝ → ℝ := fun x =>
    x ^ (s - 1) * (Qfun x - (1 - x)) - c * (x ^ (b - 1) * (Qfun x - (1 - x))) with hf
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_Jw_integrand hs).sub ((intervalIntegrable_Jw_integrand hb0).const_mul c)
  have hform : ∀ x, 0 < x → f x = (x ^ (s - b) - c) * x ^ (b - 1) * (Qfun x - (1 - x)) := by
    intro x hx
    have hsplit : x ^ (s - 1) = x ^ (s - b) * x ^ (b - 1) := by
      rw [← Real.rpow_add hx]; ring_nf
    simp only [hf, hsplit]
    ring
  have hfi1 : IntervalIntegrable f volume 0 xs := by
    refine hfi.mono_set ?_
    rw [uIcc_of_le hxs.1.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hxs.2.le
  have hfi2 : IntervalIntegrable f volume xs 1 := by
    refine hfi.mono_set ?_
    rw [uIcc_of_le hxs.2.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hxs.1.le le_rfl
  have hI1 : 0 < ∫ x in (0 : ℝ)..xs, f x := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hfi1 (fun x hx => ?_) hxs.1
    rw [hform x hx.1]
    have h1 : c < x ^ (s - b) := Real.rpow_lt_rpow_of_neg hx.1 hx.2 hneg
    have h2 : 0 < x ^ (b - 1) := Real.rpow_pos_of_pos hx.1 _
    have h3 := hposo x hx
    exact mul_pos (mul_pos (by linarith) h2) (by linarith)
  have hI2 : 0 < ∫ x in xs..1, f x := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hfi2 (fun x hx => ?_) hxs.2
    have hx0 : 0 < x := hxs.1.trans hx.1
    rw [hform x hx0]
    have h1 : x ^ (s - b) < c := Real.rpow_lt_rpow_of_neg hxs.1 hx.1 hneg
    have h2 : 0 < x ^ (b - 1) := Real.rpow_pos_of_pos hx0 _
    have h3 := hnego x hx
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) h2) (by linarith)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hfi1 hfi2
  have hdiff : (∫ x in (0 : ℝ)..1, f x) = Jw s 1 - c * Jw b 1 := by
    simp only [hf]
    rw [intervalIntegral.integral_sub (intervalIntegrable_Jw_integrand hs)
      ((intervalIntegrable_Jw_integrand hb0).const_mul c), intervalIntegral.integral_const_mul]
    rfl
  have hc0 : 0 < c := Real.rpow_pos_of_pos hxs.1 _
  have : 0 ≤ c * Jw b 1 := mul_nonneg hc0.le hb
  linarith

/-- Continuity of `s ↦ J_s(1)` on `(1, ∞)`. -/
theorem continuousAt_Jw_one {s₀ : ℝ} (hs₀ : 1 < s₀) : ContinuousAt (fun s => Jw s 1) s₀ := by
  unfold Jw
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => (1 : ℝ))
  · filter_upwards [lt_mem_nhds hs₀] with s hs
    exact (intervalIntegrable_iff.mp (intervalIntegrable_Jw_integrand (by linarith))).aestronglyMeasurable
  · filter_upwards [lt_mem_nhds hs₀] with s hs
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    have h1 : x ^ (s - 1) ≤ 1 := Real.rpow_le_one hx.1.le hx.2 (by linarith)
    have h2 := abs_g_le_one ⟨hx.1.le, hx.2⟩
    calc x ^ (s - 1) * |Qfun x - (1 - x)| ≤ 1 * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    exact ((Real.continuousAt_const_rpow hx.1.ne').comp
      (continuousAt_id.sub continuousAt_const)).mul continuousAt_const

/-! ## The threshold `α₀` -/

/-- `α₀ = sup {b > 0 : J_b(1) > 0}`. -/
noncomputable def alpha0 : ℝ := sSup {b : ℝ | 0 < b ∧ 0 < Jw b 1}

theorem alpha0_set_bddAbove : BddAbove {b : ℝ | 0 < b ∧ 0 < Jw b 1} :=
  ⟨3, fun _ hb => (lt_three_of_Jw_pos hb.2).le⟩

theorem seventeen_eighths_mem : (17 / 8 : ℝ) ∈ {b : ℝ | 0 < b ∧ 0 < Jw b 1} :=
  ⟨by norm_num, Jw_seventeen_eighths⟩

theorem seventeen_eighths_le_alpha0 : 17 / 8 ≤ alpha0 :=
  le_csSup alpha0_set_bddAbove seventeen_eighths_mem

theorem alpha0_le_three : alpha0 ≤ 3 :=
  csSup_le ⟨_, seventeen_eighths_mem⟩ fun _ hb => (lt_three_of_Jw_pos hb.2).le

/-- `J_s(1) > 0` for `0 < s < α₀`. -/
theorem Jw_one_pos_of_lt_alpha0 {s : ℝ} (hs : 0 < s) (h : s < alpha0) : 0 < Jw s 1 := by
  obtain ⟨b, hb, hsb⟩ := exists_lt_of_lt_csSup ⟨_, seventeen_eighths_mem⟩ h
  exact Jw_one_pos_of_lt hs hsb hb.2.le

/-- `J_s(1) < 0` for `s > α₀`. -/
theorem Jw_one_neg_of_alpha0_lt {s : ℝ} (h : alpha0 < s) : Jw s 1 < 0 := by
  by_contra hge
  push Not at hge
  have h0 : 0 < alpha0 := lt_of_lt_of_le (by norm_num) seventeen_eighths_le_alpha0
  have hpos : 0 < Jw ((alpha0 + s) / 2) 1 :=
    Jw_one_pos_of_lt (by linarith) (by linarith) hge
  have hle : (alpha0 + s) / 2 ≤ alpha0 :=
    le_csSup alpha0_set_bddAbove ⟨by linarith, hpos⟩
  linarith

/-- `J_{α₀}(1) = 0`. -/
theorem Jw_alpha0 : Jw alpha0 1 = 0 := by
  have h1 : 1 < alpha0 := lt_of_lt_of_le (by norm_num) seventeen_eighths_le_alpha0
  have hc := (continuousAt_Jw_one h1).tendsto
  apply le_antisymm
  · refine le_of_tendsto (hc.mono_left (nhdsWithin_le_nhds (s := Ioi alpha0))) ?_
    filter_upwards [self_mem_nhdsWithin (s := Ioi alpha0)] with s hs
    exact (Jw_one_neg_of_alpha0_lt hs).le
  · refine ge_of_tendsto (hc.mono_left (nhdsWithin_le_nhds (s := Iio alpha0))) ?_
    filter_upwards [Ioo_mem_nhdsLT h1] with s hs
    exact (Jw_one_pos_of_lt_alpha0 (by linarith [hs.1]) hs.2).le

theorem seventeen_eighths_lt_alpha0 : 17 / 8 < alpha0 := by
  rcases eq_or_lt_of_le seventeen_eighths_le_alpha0 with h | h
  · have := Jw_alpha0
    rw [← h] at this
    linarith [Jw_seventeen_eighths]
  · exact h

theorem alpha0_lt_three : alpha0 < 3 := by
  rcases eq_or_lt_of_le alpha0_le_three with h | h
  · have := Jw_alpha0
    rw [h] at this
    linarith [Jw_three_neg]
  · exact h

/-- **`17/8 < α₀ < 3`.** -/
theorem alpha0_mem : alpha0 ∈ Ioo (17 / 8 : ℝ) 3 :=
  ⟨seventeen_eighths_lt_alpha0, alpha0_lt_three⟩

/-- `J_s(1) ≥ 0 ⟺ s ≤ α₀` for `s > 0`. -/
theorem Jw_one_nonneg_iff {s : ℝ} (hs : 0 < s) : 0 ≤ Jw s 1 ↔ s ≤ alpha0 := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    linarith [Jw_one_neg_of_alpha0_lt hlt]
  · intro h
    rcases eq_or_lt_of_le h with rfl | hlt
    · rw [Jw_alpha0]
    · exact (Jw_one_pos_of_lt_alpha0 hs hlt).le

/-! ## The substitution `v = u^D` with a possibly singular weight -/

/-- `∫₀¹ u^{k-1} f(u^D) du = (1/D) ∫₀¹ v^{k/D-1} f(v) dv` for every real `k` and `D ≥ 1`
(both sides as Bochner integrals; no integrability needed). -/
theorem integral_rpow_comp_pow_eq (f : ℝ → ℝ) {D : ℕ} (hD : 1 ≤ D) (k : ℝ) :
    (∫ u in (0 : ℝ)..1, u ^ (k - 1) * f (u ^ D))
      = (1 / D) * ∫ v in (0 : ℝ)..1, v ^ (k / D - 1) * f v := by
  have hD0 : D ≠ 0 := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have himg : (fun u : ℝ => u ^ D) '' Ioc 0 1 = Ioc 0 1 := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨pow_pos hu.1 D, pow_le_one₀ hu.1.le hu.2⟩
    · intro hv
      refine ⟨v ^ ((D : ℝ)⁻¹), ⟨Real.rpow_pos_of_pos hv.1 _,
        Real.rpow_le_one hv.1.le hv.2 (by positivity)⟩, ?_⟩
      exact Real.rpow_inv_natCast_pow hv.1.le hD0
  have hinj : InjOn (fun u : ℝ => u ^ D) (Ioc 0 1) := fun x hx y hy hxy =>
    (pow_left_inj₀ hx.1.le hy.1.le hD0).mp hxy
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := Ioc (0 : ℝ) 1)
    (f := fun u : ℝ => u ^ D) (f' := fun u => (D : ℝ) * u ^ (D - 1)) measurableSet_Ioc
    (fun x _ => by simpa using (hasDerivAt_pow D x).hasDerivWithinAt) hinj
    (fun v => v ^ (k / D - 1) * f v)
  rw [himg] at hcv
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    hcv, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have hu0 : 0 < u := hu.1
  have hcancel := rpow_comp_pow_mul_pow_pred hD k hu0
  simp only [smul_eq_mul]
  rw [abs_of_nonneg (by positivity)]
  rw [← hcancel]
  field_simp

/-- Condition (b) for the power weight: `∫₀¹ k u^{k-1} g(u^D) du = (k/D) J_{k/D}(1)`. -/
theorem integral_power_weight_g (k : ℝ) {D : ℕ} (hD : 1 ≤ D) :
    (∫ u in (0 : ℝ)..1, k * u ^ (k - 1) * (Qfun (u ^ D) - (1 - u ^ D)))
      = k / D * Jw (k / D) 1 := by
  have h := integral_rpow_comp_pow_eq (fun v => Qfun v - (1 - v)) hD k
  have e : (∫ u in (0 : ℝ)..1, k * u ^ (k - 1) * (Qfun (u ^ D) - (1 - u ^ D)))
      = k * ∫ u in (0 : ℝ)..1, u ^ (k - 1) * (Qfun (u ^ D) - (1 - u ^ D)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext u; ring
  rw [e, h]
  unfold Jw
  ring

/-! ## Power weights -/

theorem power_weight_integrable {k : ℝ} (hk : 0 < k) :
    IntervalIntegrable (fun u : ℝ => k * u ^ (k - 1)) volume 0 1 :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < k - 1)).const_mul k

theorem power_weight_nonneg {k : ℝ} (hk : 0 < k) :
    ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ k * u ^ (k - 1) :=
  Filter.Eventually.of_forall fun _ hu => mul_nonneg hk.le (Real.rpow_nonneg hu.1.le _)

/-- **Corollary (1).** For `k > 0`, the moment `𝓜ₖ,₁(A) = ∫₀¹ k u^{k-1} P_A(u) du` is minimized
by `Min(U)` among the primitive subsets of every finite `U ⊆ {2,3,…}` iff `k ≤ 2α₀`. -/
theorem relative_powers_iff {k : ℝ} (hk : 0 < k) :
    (∀ U : Finset ℕ, (∀ u ∈ U, 2 ≤ u) → ∀ A : Set ℕ, IsPrimitive A → A ⊆ ↑U →
        MSet k 1 (minElems ↑U) ≤ MSet k 1 A) ↔ k ≤ 2 * alpha0 := by
  have hiff := relative_cone_iff (power_weight_integrable hk) (power_weight_nonneg hk)
  have hcond : (∀ D : ℕ, 2 ≤ D →
      0 ≤ ∫ u in (0 : ℝ)..1, k * u ^ (k - 1) * (Qfun (u ^ D) - (1 - u ^ D))) ↔
      k ≤ 2 * alpha0 := by
    constructor
    · intro h
      have h2 := h 2 le_rfl
      rw [integral_power_weight_g k (by norm_num)] at h2
      have hk2 : 0 < k / (2 : ℕ) := by positivity
      have := (Jw_one_nonneg_iff hk2).mp (nonneg_of_mul_nonneg_right h2 hk2)
      push_cast at this
      linarith
    · intro h D hD
      rw [integral_power_weight_g k (by omega)]
      have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
      have hkD : 0 < k / D := by positivity
      refine mul_nonneg hkD.le ((Jw_one_nonneg_iff hkD).mpr ?_)
      rw [div_le_iff₀ (by linarith)]
      nlinarith [seventeen_eighths_le_alpha0]
  exact hiff.trans hcond

/-- **Corollary (2).** For every `k > 2α₀`, the primitive set `2𝒫 = {4, 6, 10, 14, …}` has a
smaller `k`-th moment than `{2} = Min(U)` inside `U = {2, 4, 6, 8, …}`:
`𝓜ₖ,₁(2𝒫) < 𝓜ₖ,₁({2})`. -/
theorem twoPrimes_moment_lt {k : ℝ} (hk : 2 * alpha0 < k) :
    MSet k 1 ((fun n => 2 * n) '' Primes) < MSet k 1 {2} := by
  have hk0 : 0 < k := lt_of_le_of_lt (by linarith [seventeen_eighths_le_alpha0]) hk
  have hw := power_weight_integrable hk0
  have himg : (fun n : ℕ => 2 * n) '' Primes = (· * 2) '' Primes := by
    congr 1; funext n; ring
  have e1 : MSet k 1 ((fun n => 2 * n) '' Primes) = FwD (fun u => k * u ^ (k - 1)) 2 1 Primes := by
    unfold MSet FwD
    rw [himg]
    simp_rw [qProdSet_image_mul Primes (by norm_num : 0 < 2)]
  have e2 : MSet k 1 {2} = ∫ u in (0 : ℝ)..1, k * u ^ (k - 1) * (1 - u ^ 2) := by
    unfold MSet
    simp_rw [qProdSet_singleton]
  have hg := integral_w_g hw 2 ⟨zero_le_one, le_rfl⟩
  rw [integral_power_weight_g k (by norm_num)] at hg
  have hk2 : 0 < k / (2 : ℕ) := by positivity
  have hJ : Jw (k / (2 : ℕ)) 1 < 0 := Jw_one_neg_of_alpha0_lt (by push_cast; linarith)
  have := mul_neg_of_pos_of_neg hk2 hJ
  rw [e1, e2]
  linarith

end RntPaper
