import RntPaper.MomentsWeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The L¹ Stieltjes lemma

For an integrable `h` on `[0,z]` with nonnegative running integrals `H(y) = ∫₀ʸ h ≥ 0`, and
a product weight `P_S` (finite or infinite `S`), `∫₀ᶻ P_S h ≥ 0`; strictly positive when
`H > 0` on `(0,z]` and `S ⊆ {2,3,…}`.

For finite `S` this is the integration by parts `∫₀ᶻ φ h = φ(z) H(z) - ∫₀ᶻ φ' H` with the
absolutely continuous primitive `H` (Mathlib's `AbsolutelyContinuousOnInterval`); infinite `S`
follows by dominated convergence along the truncations, dominated by `|h|`.
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set Filter Topology

/-- **Integration by parts against an L¹ function.** `φ` is `C¹`, `h` integrable on `[0,z]`. -/
theorem integral_mul_eq_ibp_L1 {φ φ' h : ℝ → ℝ} {z : ℝ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ')
    (hh : IntervalIntegrable h volume 0 z) :
    (∫ u in (0 : ℝ)..z, φ u * h u) =
      φ z * (∫ u in (0 : ℝ)..z, h u) - ∫ u in (0 : ℝ)..z, φ' u * (∫ t in (0 : ℝ)..u, h t) := by
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, h t with hGdef
  have hG : AbsolutelyContinuousOnInterval G 0 z :=
    hh.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hderφ : deriv φ = φ' := funext fun x => (hφ x).deriv
  have hφC : ContDiff ℝ 1 φ :=
    contDiff_one_iff_deriv.mpr ⟨fun x => (hφ x).differentiableAt, hderφ ▸ hφ'⟩
  have hφAC : AbsolutelyContinuousOnInterval φ 0 z :=
    hφC.contDiffOn.absolutelyContinuousOnInterval
  have hibp := hφAC.integral_mul_deriv_eq_deriv_mul hG
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hcongr : (∫ u in (0 : ℝ)..z, φ u * deriv G u) = ∫ u in (0 : ℝ)..z, φ u * h u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hh.ae_hasDerivAt_integral] with x hx hxI
    have hx' := hx (uIoc_subset_uIcc hxI) 0 (by simp)
    rw [hx'.deriv]
  rw [hcongr, hG0, hderφ] at hibp
  rw [hibp]
  simp [hGdef]

/-- Integration by parts for the finite product weight. -/
theorem integral_qProd_mul_eq_ibp_L1 (S : Finset ℕ) {h : ℝ → ℝ} {z : ℝ}
    (hh : IntervalIntegrable h volume 0 z) :
    (∫ u in (0 : ℝ)..z, qProd S u * h u) =
      qProd S z * (∫ u in (0 : ℝ)..z, h u)
        - ∫ u in (0 : ℝ)..z, qProd' S u * (∫ t in (0 : ℝ)..u, h t) :=
  integral_mul_eq_ibp_L1 (fun x => hasDerivAt_qProd S x) (continuous_qProd' S) hh

/-- Continuity of the running integral on `[0,z]`. -/
theorem continuousOn_runInt_L1 {h : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hh : IntervalIntegrable h volume 0 z) :
    ContinuousOn (fun y => ∫ t in (0 : ℝ)..y, h t) (Icc 0 z) := by
  have := intervalIntegral.continuousOn_primitive_interval' hh (a := 0) (by simp)
  rwa [uIcc_of_le hz] at this

/-- Dominated convergence along truncations, against an L¹ function. -/
theorem tendsto_integral_qProd_truncation_mul_L1 (B : Set ℕ) [DecidablePred (· ∈ B)] {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {h : ℝ → ℝ} (hh : IntervalIntegrable h volume 0 c) :
    Tendsto
      (fun N => ∫ u in (0 : ℝ)..c, qProd ((Finset.range (N + 1)).filter (· ∈ B)) u * h u)
      atTop (𝓝 (∫ u in (0 : ℝ)..c, qProdSet B u * h u)) := by
  simp only [intervalIntegral.integral_of_le hc.1]
  have hhI : IntegrableOn h (Ioc 0 c) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.1).mp hh
  apply tendsto_integral_of_dominated_convergence (bound := fun u => ‖h u‖)
  · exact fun N => ((qProd_continuous _).aestronglyMeasurable.restrict).mul hhI.1
  · exact hhI.norm
  · intro N
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.trans hc.2⟩
    rw [norm_mul]
    calc ‖qProd ((Finset.range (N + 1)).filter (· ∈ B)) u‖ * ‖h u‖ ≤ 1 * ‖h u‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg (qProd_nonneg _ hu')]
          exact qProd_le_one _ hu'
      _ = ‖h u‖ := one_mul _
  · have hmem : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) c)), u ∈ Ioc (0 : ℝ) c :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hmem, ae_restrict_ne_one (Ioc (0 : ℝ) c)] with u hu hu1
    exact (qProdSet_eq_lim B hu.1.le (lt_of_le_of_ne (hu.2.trans hc.2) hu1)).mul
      tendsto_const_nhds

/-- **L¹ Stieltjes lemma, finite weight.** -/
theorem integral_qProd_mul_nonneg_L1 (S : Finset ℕ) {h : ℝ → ℝ} {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hh : IntervalIntegrable h volume 0 z)
    (hH : ∀ y ∈ Icc (0 : ℝ) z, 0 ≤ ∫ u in (0 : ℝ)..y, h u) :
    0 ≤ ∫ u in (0 : ℝ)..z, qProd S u * h u := by
  rw [integral_qProd_mul_eq_ibp_L1 S hh]
  have hbdry : 0 ≤ qProd S z * ∫ u in (0 : ℝ)..z, h u :=
    mul_nonneg (qProd_nonneg S hz) (hH z ⟨hz.1, le_rfl⟩)
  have hGc := continuousOn_runInt_L1 hz.1 hh
  have htail : (∫ u in (0 : ℝ)..z, qProd' S u * ∫ t in (0 : ℝ)..u, h t) ≤ 0 := by
    have hle : (∫ u in (0 : ℝ)..z, qProd' S u * ∫ t in (0 : ℝ)..u, h t)
        ≤ ∫ _ in (0 : ℝ)..z, (0 : ℝ) := by
      apply intervalIntegral.integral_mono_on hz.1
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hz.1]
        exact (continuous_qProd' S).continuousOn.mul hGc
      · exact _root_.intervalIntegrable_const
      · intro u hu
        exact mul_nonpos_of_nonpos_of_nonneg (qProd'_nonpos S ⟨hu.1, hu.2.trans hz.2⟩) (hH u hu)
    simpa using hle
  linarith

/-- **L¹ Stieltjes lemma.** If `h` is integrable on `[0,z]` with `∫₀ʸ h ≥ 0` for every
`y ∈ [0,z]`, then `∫₀ᶻ P_S(u) h(u) du ≥ 0` for every exponent set `S`. -/
theorem integral_qProdSet_mul_nonneg_L1 (S : Set ℕ) {h : ℝ → ℝ} {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hh : IntervalIntegrable h volume 0 z)
    (hH : ∀ y ∈ Icc (0 : ℝ) z, 0 ≤ ∫ u in (0 : ℝ)..y, h u) :
    0 ≤ ∫ u in (0 : ℝ)..z, qProdSet S u * h u := by
  classical
  refine ge_of_tendsto (tendsto_integral_qProd_truncation_mul_L1 S hz hh)
    (Filter.Eventually.of_forall fun N => ?_)
  exact integral_qProd_mul_nonneg_L1 _ hz hh hH

/-- Positivity of `κ = ∫₀ᶜ b u^{b-1} H(u) G(u) du` when `G ≥ 0` on `[0,c]`, `G > 0` on `(0,c]`. -/
theorem kappaG_pos_upto {b : ℕ} (hb : 1 ≤ b) {G : ℝ → ℝ} {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1)
    (hGc : ContinuousOn G (Icc 0 c))
    (hG0 : ∀ y ∈ Icc (0 : ℝ) c, 0 ≤ G y) (hGpos : ∀ y ∈ Ioc (0 : ℝ) c, 0 < G y) :
    0 < kappaG b G c := by
  unfold kappaG
  apply intervalIntegral.integral_pos hc.1
  · exact ((continuous_const.mul (continuous_pow _)).mul continuous_HfunExt).continuousOn.mul hGc
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans hc.2⟩
    have h1 : 0 ≤ (b : ℝ) * x ^ (b - 1) := mul_nonneg (by positivity) (pow_nonneg hx.1.le _)
    have h2 : 0 ≤ HfunExt x := by rw [HfunExt_of_mem hx']; exact Hfun_nonneg hx'
    exact mul_nonneg (mul_nonneg h1 h2) (hG0 x ⟨hx.1.le, hx.2⟩)
  · refine ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.1]⟩, ?_⟩
    have hmem : c / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have h1 : 0 < (b : ℝ) * (c / 2) ^ (b - 1) := mul_pos hbR (pow_pos (by linarith [hc.1]) _)
    have h2 : 0 < HfunExt (c / 2) := by
      rw [HfunExt_of_mem hmem]
      exact Hfun_pos_of_lt hmem.1 (by linarith [hc.2])
    exact mul_pos (mul_pos h1 h2) (hGpos _ ⟨by linarith [hc.1], by linarith [hc.1]⟩)

/-- **Strict L¹ Stieltjes lemma.** If `S ⊆ {2,3,…}`, `h` is integrable on `[0,c]`, `∫₀ʸ h ≥ 0`
on `[0,c]` and `∫₀ʸ h > 0` on `(0,c]`, then `∫₀ᶜ P_S(u) h(u) du > 0`. -/
theorem integral_qProdSet_mul_pos_L1 {S : Set ℕ} (hS : ∀ n ∈ S, 2 ≤ n) {h : ℝ → ℝ} {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) (hh : IntervalIntegrable h volume 0 c)
    (hH0 : ∀ y ∈ Icc (0 : ℝ) c, 0 ≤ ∫ u in (0 : ℝ)..y, h u)
    (hH : ∀ y ∈ Ioc (0 : ℝ) c, 0 < ∫ u in (0 : ℝ)..y, h u) :
    0 < ∫ u in (0 : ℝ)..c, qProdSet S u * h u := by
  classical
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  set G : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, h t with hGdef
  have hGc : ContinuousOn G (Icc 0 c) := continuousOn_runInt_L1 hc.1.le hh
  rcases S.eq_empty_or_nonempty with hSe | ⟨b, hb⟩
  · subst hSe
    have hone : (∫ u in (0 : ℝ)..c, qProdSet ∅ u * h u) = ∫ u in (0 : ℝ)..c, h u := by
      apply intervalIntegral.integral_congr
      intro u _
      simp [qProdSet]
    rw [hone]
    exact hH c ⟨hc.1, le_rfl⟩
  · have hb1 : 1 ≤ b := le_trans (by norm_num) (hS b hb)
    have hκ := kappaG_pos_upto hb1 hc hGc hH0 hH
    have hfin : ∀ S' : Finset ℕ, (∀ n ∈ S', 2 ≤ n) → b ∈ S' →
        kappaG b G c ≤ ∫ u in (0 : ℝ)..c, qProd S' u * h u := by
      intro S' hS' hbS'
      rw [integral_qProd_mul_eq_ibp_L1 S' hh]
      have hbdry : 0 ≤ qProd S' c * ∫ u in (0 : ℝ)..c, h u :=
        mul_nonneg (qProd_nonneg S' hcI) (hH0 c ⟨hc.1.le, le_rfl⟩)
      have htail : kappaG b G c ≤ -∫ u in (0 : ℝ)..c, qProd' S' u * G u := by
        unfold kappaG
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_mono_on hc.1.le
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hc.1.le]
          exact ((continuous_const.mul (continuous_pow _)).mul
            continuous_HfunExt).continuousOn.mul hGc
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hc.1.le]
          exact ((continuous_qProd' S').continuousOn.mul hGc).neg
        · intro u hu
          have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hc.2⟩
          have := mul_le_mul_of_nonneg_right (le_neg_qProd' hS' hbS' hu') (hH0 u hu)
          linarith
      linarith
    have hlim : kappaG b G c ≤ ∫ u in (0 : ℝ)..c, qProdSet S u * h u := by
      refine ge_of_tendsto (tendsto_integral_qProd_truncation_mul_L1 S hcI hh) ?_
      filter_upwards [Filter.eventually_ge_atTop b] with N hN
      apply hfin
      · intro n hn
        exact hS n (Finset.mem_filter.mp hn).2
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩
    linarith

end RntPaper
