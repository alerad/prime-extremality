import RntPaper.CertPoly

/-!
# From certificates to running integrals

`RunPos g K`: for every real `1 ≤ k ≤ K` and `y ∈ (0,1]`, `∫₀ʸ u^{k-1} g(u) du > 0`.

* `runPos_of_signChange` (SC): `g` changes sign once on `(0,1)`, from `+` to `-`, and
  `∫₀¹ u^{K-1} g > 0`. Variation diminishing: `u^{k-K}` is nonincreasing.
* `runNonneg_of_signChange`: the same with `∫₀¹ u^{K-1} g ≥ 0` gives `≥ 0` for `k ≤ K`
  and `> 0` for `k < K` (the tight case `A₉`).
* `runPos_of_V1` (V1): an envelope `E ≥ L` on `[0,u₁]` with `W (L - T) ≥ 0` there and
  `∫₀^{u₁} u^{K-1} W (L - T) > ∫_{u₁}^1 u^{K-1} W T`.
-/

namespace RntPaper

open MeasureTheory intervalIntegral Set

/-- Running integrals of `u^{k-1} g` are positive for all `1 ≤ k ≤ K`. -/
def RunPos (g : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ k : ℝ, 1 ≤ k → k ≤ K → ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * g u

theorem continuous_rpow_mul {g : ℝ → ℝ} (hg : Continuous g) {k : ℝ} (hk : 1 ≤ k) :
    Continuous fun u : ℝ => u ^ (k - 1) * g u :=
  (Real.continuous_rpow_const (by linarith)).mul hg

theorem rpow_sub_le_of_le {u x : ℝ} (hu : 0 < u) (hux : u ≤ x) {e : ℝ} (he : e ≤ 0) :
    x ^ e ≤ u ^ e :=
  Real.rpow_le_rpow_of_nonpos hu hux he

theorem rpow_sub_lt_of_lt {u x : ℝ} (hu : 0 < u) (hux : u < x) {e : ℝ} (he : e < 0) :
    x ^ e < u ^ e :=
  Real.rpow_lt_rpow_of_neg hu hux he

/-- Positivity on an initial segment where `g > 0`. -/
theorem integral_pos_of_pos_init {g : ℝ → ℝ} (hg : Continuous g) {k : ℝ} (hk : 1 ≤ k)
    {x0 y : ℝ} (hy : 0 < y) (hyx : y ≤ x0) (hpos : ∀ u ∈ Ioo 0 x0, 0 < g u) :
    0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * g u := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_rpow_mul hg hk).intervalIntegrable (μ := volume) 0 y) (fun u hu => ?_) hy
  exact mul_pos (Real.rpow_pos_of_pos hu.1 _) (hpos u ⟨hu.1, hu.2.trans_le hyx⟩)

/-- The variation-diminishing comparison:
`∫₀¹ u^{k-1} g ≥ x₀^{k-K} ∫₀¹ u^{K-1} g`, strictly if `k < K`. -/
theorem vd_compare {g : ℝ → ℝ} (hg : Continuous g) {x0 : ℝ} (hx0 : x0 ∈ Ioo (0 : ℝ) 1)
    (hpos : ∀ u ∈ Ioo 0 x0, 0 < g u) (hneg : ∀ u ∈ Icc x0 1, g u ≤ 0)
    {k K : ℝ} (hk : 1 ≤ k) (hkK : k ≤ K) :
    x0 ^ (k - K) * (∫ u in (0 : ℝ)..1, u ^ (K - 1) * g u) ≤ ∫ u in (0 : ℝ)..1, u ^ (k - 1) * g u
    ∧ (k < K → x0 ^ (k - K) * (∫ u in (0 : ℝ)..1, u ^ (K - 1) * g u)
        < ∫ u in (0 : ℝ)..1, u ^ (k - 1) * g u) := by
  have hK : 1 ≤ K := hk.trans hkK
  set f : ℝ → ℝ := fun u => u ^ (k - 1) * g u - x0 ^ (k - K) * (u ^ (K - 1) * g u) with hf
  have hfc : Continuous f :=
    (continuous_rpow_mul hg hk).sub (continuous_const.mul (continuous_rpow_mul hg hK))
  have hfeq : ∀ u, 0 < u → f u = u ^ (K - 1) * (u ^ (k - K) - x0 ^ (k - K)) * g u := by
    intro u hu
    simp only [hf]
    have : u ^ (k - 1) = u ^ (K - 1) * u ^ (k - K) := by
      rw [← Real.rpow_add hu]; ring_nf
    rw [this]; ring
  have hdiff : (∫ u in (0 : ℝ)..1, u ^ (k - 1) * g u)
      - x0 ^ (k - K) * (∫ u in (0 : ℝ)..1, u ^ (K - 1) * g u) = ∫ u in (0 : ℝ)..1, f u := by
    have h1 : IntervalIntegrable (fun u => u ^ (k - 1) * g u) volume 0 1 :=
      (continuous_rpow_mul hg hk).intervalIntegrable 0 1
    have h2 : IntervalIntegrable (fun u => x0 ^ (k - K) * (u ^ (K - 1) * g u)) volume 0 1 :=
      (continuous_const.mul (continuous_rpow_mul hg hK)).intervalIntegrable 0 1
    simp only [hf]
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  have hf0 : ∀ u ∈ Ioo (0 : ℝ) x0, 0 ≤ f u ∧ (k < K → 0 < f u) := by
    intro u hu
    rw [hfeq u hu.1]
    have h1 : 0 < u ^ (K - 1) := Real.rpow_pos_of_pos hu.1 _
    have h2 : x0 ^ (k - K) ≤ u ^ (k - K) := rpow_sub_le_of_le hu.1 hu.2.le (by linarith)
    have h3 := hpos u hu
    refine ⟨mul_nonneg (mul_nonneg h1.le (by linarith)) h3.le, fun hlt => ?_⟩
    have h2' : x0 ^ (k - K) < u ^ (k - K) := rpow_sub_lt_of_lt hu.1 hu.2 (by linarith)
    exact mul_pos (mul_pos h1 (by linarith)) h3
  have hf1 : ∀ u ∈ Icc x0 (1 : ℝ), 0 ≤ f u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hx0.1 hu.1
    rw [hfeq u hu0]
    have h1 : 0 < u ^ (K - 1) := Real.rpow_pos_of_pos hu0 _
    have h2 : u ^ (k - K) ≤ x0 ^ (k - K) := rpow_sub_le_of_le hx0.1 hu.1 (by linarith)
    have h3 := hneg u hu
    exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h1.le (by linarith)) h3
  have hsplit : (∫ u in (0 : ℝ)..1, f u) = (∫ u in (0 : ℝ)..x0, f u) + ∫ u in x0..1, f u :=
    (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable (μ := volume) _ _)
      (hfc.intervalIntegrable (μ := volume) _ _)).symm
  have hA : 0 ≤ ∫ u in (0 : ℝ)..x0, f u := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hx0.1.le
    have : ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) x0)), u ≠ 0 ∧ u ≠ x0 := by
      filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ)),
        ae_restrict_of_ae (Measure.ae_ne volume x0)] with u h1 h2 using ⟨h1, h2⟩
    filter_upwards [this, ae_restrict_mem measurableSet_Icc] with u hne hu
    exact (hf0 u ⟨lt_of_le_of_ne hu.1 (Ne.symm hne.1), lt_of_le_of_ne hu.2 hne.2⟩).1
  have hB : 0 ≤ ∫ u in x0..1, f u :=
    intervalIntegral.integral_nonneg hx0.2.le fun u hu => hf1 u hu
  refine ⟨?_, fun hlt => ?_⟩
  · have : 0 ≤ ∫ u in (0 : ℝ)..1, f u := by rw [hsplit]; linarith
    linarith
  · have hA' : 0 < ∫ u in (0 : ℝ)..x0, f u :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hfc.intervalIntegrable (μ := volume) _ _)
        (fun u hu => (hf0 u hu).2 hlt) hx0.1
    have : 0 < ∫ u in (0 : ℝ)..1, f u := by rw [hsplit]; linarith
    linarith

/-- Past the sign change the running integral only decreases to its value at `1`. -/
theorem integral_ge_full {g : ℝ → ℝ} (hg : Continuous g) {x0 : ℝ}
    (hneg : ∀ u ∈ Icc x0 1, g u ≤ 0) {k : ℝ} (hk : 1 ≤ k) {y : ℝ} (hxy : x0 ≤ y) (hy1 : y ≤ 1)
    (hx0 : 0 ≤ x0) :
    (∫ u in (0 : ℝ)..1, u ^ (k - 1) * g u) ≤ ∫ u in (0 : ℝ)..y, u ^ (k - 1) * g u := by
  have hc := continuous_rpow_mul hg hk
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 y)
    (hc.intervalIntegrable (μ := volume) y 1)
  have : (∫ u in y..1, u ^ (k - 1) * g u) ≤ 0 := by
    have h := intervalIntegral.integral_nonneg (μ := volume) (f := fun u => -(u ^ (k - 1) * g u)) hy1
      (fun u hu => by
        have hu0 : 0 ≤ u := le_trans hx0 (hxy.trans hu.1)
        have := hneg u ⟨hxy.trans hu.1, hu.2⟩
        have := Real.rpow_nonneg hu0 (k - 1)
        nlinarith)
    rw [intervalIntegral.integral_neg] at h
    linarith
  linarith

/-- **SC, nonstrict form.** One sign change and `∫₀¹ u^{K-1} g ≥ 0`: for `1 ≤ k ≤ K` all
running integrals are `≥ 0`, and `> 0` if `k < K` or the endpoint integral is positive. -/
theorem runNonneg_of_signChange {g : ℝ → ℝ} (hg : Continuous g) {x0 : ℝ}
    (hx0 : x0 ∈ Ioo (0 : ℝ) 1) (hpos : ∀ u ∈ Ioo 0 x0, 0 < g u)
    (hneg : ∀ u ∈ Icc x0 1, g u ≤ 0) {K : ℝ} (hI : 0 ≤ ∫ u in (0 : ℝ)..1, u ^ (K - 1) * g u)
    {k : ℝ} (hk : 1 ≤ k) (hkK : k ≤ K) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 ≤ ∫ u in (0 : ℝ)..y, u ^ (k - 1) * g u ∧
      ((k < K ∨ 0 < ∫ u in (0 : ℝ)..1, u ^ (K - 1) * g u) →
        0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * g u) := by
  rcases le_or_gt y x0 with hyx | hyx
  · have := integral_pos_of_pos_init hg hk hy.1 hyx hpos
    exact ⟨this.le, fun _ => this⟩
  · have hfull := integral_ge_full hg hneg hk hyx.le hy.2 hx0.1.le
    obtain ⟨hvd, hvd'⟩ := vd_compare hg hx0 hpos hneg hk hkK
    have hxp : 0 < x0 ^ (k - K) := Real.rpow_pos_of_pos hx0.1 _
    refine ⟨by nlinarith [mul_nonneg hxp.le hI], fun h => ?_⟩
    rcases h with h | h
    · have := hvd' h; nlinarith [mul_nonneg hxp.le hI]
    · nlinarith [mul_pos hxp h]

/-- **SC.** One sign change and `∫₀¹ u^{K-1} g > 0` give `RunPos g K`. -/
theorem runPos_of_signChange {g : ℝ → ℝ} (hg : Continuous g) {x0 : ℝ}
    (hx0 : x0 ∈ Ioo (0 : ℝ) 1) (hpos : ∀ u ∈ Ioo 0 x0, 0 < g u)
    (hneg : ∀ u ∈ Icc x0 1, g u ≤ 0) {K : ℝ} (hI : 0 < ∫ u in (0 : ℝ)..1, u ^ (K - 1) * g u) :
    RunPos g K := fun _k hk hkK _y hy =>
  (runNonneg_of_signChange hg hx0 hpos hneg hI.le hk hkK hy).2 (Or.inr hI)

/-- No sign change at all. -/
theorem runPos_of_pos {g : ℝ → ℝ} (hg : Continuous g) (hpos : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < g u)
    (K : ℝ) : RunPos g K := fun _k hk _ _y hy =>
  integral_pos_of_pos_init hg hk hy.1 hy.2 hpos

/-- **V1.** Let `W, E, T, L` be continuous, `W, E, T ≥ 0` on `[0,1]`, `L ≤ E` and
`W (L - T) ≥ 0` on `[0,u₁]`, `W (L - T) > 0` on `(0,u₀)`, and
`∫₀^{u₁} u^{K-1} W (L - T) > ∫_{u₁}^1 u^{K-1} W T` (`K ≥ 1` real). Then the running integrals
of `u^{k-1} W (E - T)` are positive for every `1 ≤ k ≤ K`. -/
theorem runPos_of_V1 {W E T L : ℝ → ℝ} (hWc : Continuous W) (hEc : Continuous E)
    (hTc : Continuous T) (hLc : Continuous L)
    (hW : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ W u) (hE : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ E u)
    (hT : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ T u) {u0 u1 : ℝ} (hu0 : 0 < u0) (hu01 : u0 ≤ u1)
    (hu1 : u1 < 1) (hLE : ∀ u ∈ Icc (0 : ℝ) u1, L u ≤ E u)
    (hLT : ∀ u ∈ Icc (0 : ℝ) u1, 0 ≤ W u * (L u - T u))
    (hLTpos : ∀ u ∈ Ioo (0 : ℝ) u0, 0 < W u * (L u - T u)) {K : ℝ}
    (hI : (∫ u in u1..1, u ^ (K - 1) * (W u * T u))
      < ∫ u in (0 : ℝ)..u1, u ^ (K - 1) * (W u * (L u - T u))) :
    RunPos (fun u => W u * (E u - T u)) K := by
  intro k hk hkK y hy
  have hK : 1 ≤ K := hk.trans hkK
  have hu1p : 0 < u1 := hu0.trans_le hu01
  set gE : ℝ → ℝ := fun u => W u * (E u - T u) with hgE
  set gL : ℝ → ℝ := fun u => W u * (L u - T u) with hgL
  set gT : ℝ → ℝ := fun u => W u * T u with hgT
  have hgEc : Continuous gE := hWc.mul (hEc.sub hTc)
  have hgLc : Continuous gL := hWc.mul (hLc.sub hTc)
  have hgTc : Continuous gT := hWc.mul hTc
  -- lower bound by `gL` on `[0,u₁]`
  have hEL : ∀ u ∈ Icc (0 : ℝ) u1, gL u ≤ gE u := fun u hu =>
    mul_le_mul_of_nonneg_left (by linarith [hLE u hu]) (hW u ⟨hu.1, hu.2.trans hu1.le⟩)
  -- positivity of `∫₀ʸ u^{k-1} gL` for `y ≤ u₁`
  have hposL : ∀ z ∈ Ioc (0 : ℝ) u1, 0 < ∫ u in (0 : ℝ)..z, u ^ (k - 1) * gL u := by
    intro z hz
    set z0 := min z u0
    have hz0 : 0 < z0 := lt_min hz.1 hu0
    have h1 : 0 < ∫ u in (0 : ℝ)..z0, u ^ (k - 1) * gL u :=
      integral_pos_of_pos_init hgLc hk hz0 (min_le_right _ _) hLTpos
    have h2 : 0 ≤ ∫ u in z0..z, u ^ (k - 1) * gL u :=
      intervalIntegral.integral_nonneg (min_le_left _ _) fun u hu =>
        mul_nonneg (Real.rpow_nonneg (hz0.le.trans hu.1) _)
          (hLT u ⟨hz0.le.trans hu.1, hu.2.trans hz.2⟩)
    have := intervalIntegral.integral_add_adjacent_intervals
      ((continuous_rpow_mul hgLc hk).intervalIntegrable (μ := volume) 0 z0)
      ((continuous_rpow_mul hgLc hk).intervalIntegrable (μ := volume) z0 z)
    linarith
  have hmonoL : ∀ z ∈ Icc (0 : ℝ) u1, (∫ u in (0 : ℝ)..z, u ^ (k - 1) * gL u)
      ≤ ∫ u in (0 : ℝ)..z, u ^ (k - 1) * gE u := fun z hz =>
    intervalIntegral.integral_mono_on hz.1 ((continuous_rpow_mul hgLc hk).intervalIntegrable (μ := volume) _ _)
      ((continuous_rpow_mul hgEc hk).intervalIntegrable (μ := volume) _ _) fun u hu =>
        mul_le_mul_of_nonneg_left (hEL u ⟨hu.1, hu.2.trans hz.2⟩) (Real.rpow_nonneg hu.1 _)
  rcases le_or_gt y u1 with hyu | hyu
  · exact lt_of_lt_of_le (hposL y ⟨hy.1, hyu⟩) (hmonoL y ⟨hy.1.le, hyu⟩)
  · -- `y > u₁`
    have hcE := continuous_rpow_mul hgEc hk
    have hcT := continuous_rpow_mul hgTc hk
    have hcL := continuous_rpow_mul hgLc hk
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcE.intervalIntegrable (μ := volume) 0 u1)
      (hcE.intervalIntegrable (μ := volume) u1 y)
    -- on `[u₁,y]`: `u^{k-1} gE ≥ -u^{k-1} gT`
    have htail : -(∫ u in u1..y, u ^ (k - 1) * gT u) ≤ ∫ u in u1..y, u ^ (k - 1) * gE u := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_mono_on hyu.le (hcT.neg.intervalIntegrable (μ := volume) _ _)
        (hcE.intervalIntegrable (μ := volume) _ _)
      intro u hu
      have hu0 : 0 ≤ u := hu1p.le.trans hu.1
      have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, hu.2.trans hy.2⟩
      have hWE := mul_nonneg (hW u huI) (hE u huI)
      have hr := Real.rpow_nonneg hu0 (k - 1)
      have heq : u ^ (k - 1) * gE u + u ^ (k - 1) * gT u = u ^ (k - 1) * (W u * E u) := by
        simp only [hgE, hgT]; ring
      show -(u ^ (k - 1) * gT u) ≤ u ^ (k - 1) * gE u
      nlinarith [mul_nonneg hr hWE]
    have hT1 : (∫ u in u1..y, u ^ (k - 1) * gT u) ≤ ∫ u in u1..1, u ^ (k - 1) * gT u := by
      have := intervalIntegral.integral_add_adjacent_intervals (hcT.intervalIntegrable (μ := volume) u1 y)
        (hcT.intervalIntegrable (μ := volume) y 1)
      have : 0 ≤ ∫ u in y..1, u ^ (k - 1) * gT u :=
        intervalIntegral.integral_nonneg hy.2 fun u hu => by
          have hu0 : 0 ≤ u := hu1p.le.trans (hyu.le.trans hu.1)
          exact mul_nonneg (Real.rpow_nonneg hu0 _)
            (mul_nonneg (hW u ⟨hu0, hu.2⟩) (hT u ⟨hu0, hu.2⟩))
      linarith
    -- ratio comparisons with `u₁^{k-K}`
    have hr : 0 < u1 ^ (k - K) := Real.rpow_pos_of_pos hu1p _
    have hLbig : u1 ^ (k - K) * (∫ u in (0 : ℝ)..u1, u ^ (K - 1) * gL u)
        ≤ ∫ u in (0 : ℝ)..u1, u ^ (k - 1) * gL u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_ae_restrict hu1p.le
        ((continuous_const.mul (continuous_rpow_mul hgLc hK)).intervalIntegrable (μ := volume) _ _)
        (hcL.intervalIntegrable (μ := volume) _ _)
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with u hu hu0
      have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hsplitu : u ^ (k - 1) = u ^ (K - 1) * u ^ (k - K) := by
        rw [← Real.rpow_add hup]; ring_nf
      show u1 ^ (k - K) * (u ^ (K - 1) * gL u) ≤ u ^ (k - 1) * gL u
      rw [hsplitu]
      have h1 : 0 ≤ gL u := hLT u hu
      have h2 : u1 ^ (k - K) ≤ u ^ (k - K) := rpow_sub_le_of_le hup hu.2 (by linarith)
      have h3 := Real.rpow_nonneg hup.le (K - 1)
      calc u1 ^ (k - K) * (u ^ (K - 1) * gL u) ≤ u ^ (k - K) * (u ^ (K - 1) * gL u) :=
            mul_le_mul_of_nonneg_right h2 (mul_nonneg h3 h1)
        _ = u ^ (K - 1) * u ^ (k - K) * gL u := by ring
    have hTsmall : (∫ u in u1..1, u ^ (k - 1) * gT u)
        ≤ u1 ^ (k - K) * ∫ u in u1..1, u ^ (K - 1) * gT u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hu1.le (hcT.intervalIntegrable (μ := volume) _ _)
        ((continuous_const.mul (continuous_rpow_mul hgTc hK)).intervalIntegrable (μ := volume) _ _)
      intro u hu
      have hup : 0 < u := hu1p.trans_le hu.1
      have hsplitu : u ^ (k - 1) = u ^ (K - 1) * u ^ (k - K) := by
        rw [← Real.rpow_add hup]; ring_nf
      show u ^ (k - 1) * gT u ≤ u1 ^ (k - K) * (u ^ (K - 1) * gT u)
      rw [hsplitu]
      have h1 : 0 ≤ gT u := mul_nonneg (hW u ⟨hup.le, hu.2⟩) (hT u ⟨hup.le, hu.2⟩)
      have h2 : u ^ (k - K) ≤ u1 ^ (k - K) := rpow_sub_le_of_le hu1p hu.1 (by linarith)
      have h3 := Real.rpow_nonneg hup.le (K - 1)
      calc u ^ (K - 1) * u ^ (k - K) * gT u = u ^ (k - K) * (u ^ (K - 1) * gT u) := by ring
        _ ≤ u1 ^ (k - K) * (u ^ (K - 1) * gT u) := mul_le_mul_of_nonneg_right h2 (mul_nonneg h3 h1)
    have hmid := hmonoL u1 ⟨hu1p.le, le_rfl⟩
    have hIr := mul_lt_mul_of_pos_left hI hr
    linarith

end RntPaper
