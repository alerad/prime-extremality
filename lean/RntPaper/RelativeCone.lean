import RntPaper.RelativeL1
import RntPaper.MomentsSmall
import RntPaper.Ambient

/-!
# The relative cone: extremality of `Min(U)` for a general weight

For a weight `w ∈ L¹(0,1)`, `w ≥ 0`, and `c ∈ (0,1]` put `F_{w,c}(A) = ∫₀ᶜ w(u) P_A(u) du`.
With `g(v) = Q(v) - (1 - v)`, the following are equivalent:

(a) `F_{w,1}(A) ≥ F_{w,1}(Min U)` for every finite `U ⊆ {2,3,…}` and primitive `A ⊆ U`;
(b) `∫₀¹ w(u) g(u^D) du ≥ 0` for every integer `D ≥ 2`.

Under (b), `F_{w,c}(Min U) ≤ F_{w,c}(A)` for all `c ∈ (0,1]`, all `U ⊆ {2,3,…}` and all primitive
`A ⊆ U` (finite or infinite); under strict (b) and `w > 0` a.e. the minimizer is unique.

The proof is the compression argument of `Ambient.lean` run in the variable `u` with the
index `D` (`∫₀ᶻ w(u) P_A(u^D) du`), by strong induction on the size bound `N` of `U`: the running
integrals of the compression integrand `w(u) E_T(u^{Dd})` are controlled by the induction
hypothesis at `N/d` (index `Dd`), by `P_{𝒫_M} ≥ Q`, and by the single crossing of `g`; the
weight `P_B(u^D)` is then handled by the L¹ Stieltjes lemma (`RelativeL1.lean`).
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set Filter Topology
open scoped Classical

/-- `F_{w,c}(A) = ∫₀ᶜ w(u) P_A(u) du`. -/
noncomputable def Fw (w : ℝ → ℝ) (c : ℝ) (A : Set ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..c, w u * qProdSet A u

/-- `∫₀ᶻ w(u) P_A(u^D) du` (the functional with index `D`). -/
noncomputable def FwD (w : ℝ → ℝ) (D : ℕ) (z : ℝ) (A : Set ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..z, w u * qProdSet A (u ^ D)

theorem FwD_one (w : ℝ → ℝ) (c : ℝ) (A : Set ℕ) : FwD w 1 c A = Fw w c A := by
  simp [FwD, Fw]

/-! ## Continuity and integrability -/

theorem contOn_qProdSet_pow {A : Set ℕ} (hA : ∀ n ∈ A, 1 ≤ n) (D : ℕ) :
    ContinuousOn (fun u : ℝ => qProdSet A (u ^ D)) (Icc 0 1) :=
  (qProdSet_continuousOn_Icc hA).comp (continuous_pow D).continuousOn
    (fun _ hu => ⟨pow_nonneg hu.1 D, pow_le_one₀ hu.1 hu.2⟩)

theorem contOn_Qfun_pow (D : ℕ) : ContinuousOn (fun u : ℝ => Qfun (u ^ D)) (Icc 0 1) :=
  Qfun_continuousOn.comp (continuous_pow D).continuousOn
    (fun _ hu => ⟨pow_nonneg hu.1 D, pow_le_one₀ hu.1 hu.2⟩)

theorem contOn_one_sub_pow (D : ℕ) : ContinuousOn (fun u : ℝ => 1 - u ^ D) (Icc 0 1) :=
  (continuous_const.sub (continuous_pow D)).continuousOn

theorem contOn_g_pow (D : ℕ) :
    ContinuousOn (fun u : ℝ => Qfun (u ^ D) - (1 - u ^ D)) (Icc 0 1) :=
  (contOn_Qfun_pow D).sub (contOn_one_sub_pow D)

theorem contOn_blockE_pow {T : Set ℕ} (hT : ∀ t ∈ T, 1 ≤ t) (D : ℕ) :
    ContinuousOn (fun u : ℝ => blockESet T (u ^ D)) (Icc 0 1) :=
  (contOn_qProdSet_pow hT D).sub (contOn_one_sub_pow D)

section Weight

variable {w : ℝ → ℝ}

theorem ii_w_mul (hw : IntervalIntegrable w volume 0 1) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => w u * f u) volume a b := by
  have hsub : uIcc a b ⊆ Icc 0 1 := uIcc_subset_Icc ha hb
  refine (hw.mono_set ?_).mul_continuousOn (hf.mono hsub)
  rwa [uIcc_of_le zero_le_one]

/-- Monotonicity of `∫ₐᵇ w f` in `f` for `w ≥ 0` a.e. on `(0,1)`. -/
theorem integral_w_mono (hw : IntervalIntegrable w volume 0 1)
    (hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (hle : ∀ u ∈ Ioo a b, f u ≤ g u) :
    ∫ u in a..b, w u * f u ≤ ∫ u in a..b, w u * g u := by
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha0, hab.trans hb1⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hab, hb1⟩
  apply intervalIntegral.integral_mono_ae_restrict hab (ii_w_mul hw hf haI hbI)
    (ii_w_mul hw hg haI hbI)
  have h1 : ∀ᵐ u ∂(volume.restrict (Icc a b)), u ∈ Icc a b := ae_restrict_mem measurableSet_Icc
  have h2 : ∀ᵐ u ∂(volume.restrict (Icc a b)), u ≠ a := ae_restrict_of_ae (Measure.ae_ne volume a)
  have h3 : ∀ᵐ u ∂(volume.restrict (Icc a b)), u ≠ b := ae_restrict_of_ae (Measure.ae_ne volume b)
  filter_upwards [h1, h2, h3, ae_restrict_of_ae hw0] with u hu hua hub hwu
  have huo : u ∈ Ioo a b := ⟨lt_of_le_of_ne hu.1 (Ne.symm hua), lt_of_le_of_ne hu.2 hub⟩
  have hw' : 0 ≤ w u := hwu ⟨lt_of_le_of_lt ha0 huo.1, lt_of_lt_of_le huo.2 hb1⟩
  exact mul_le_mul_of_nonneg_left (hle u huo) hw'

/-- Positivity of an integral from a.e. positivity on `(0,c)`. -/
theorem integral_pos_of_ae_pos {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : IntervalIntegrable f volume 0 c) (hpos : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) c → 0 < f u) :
    0 < ∫ u in (0 : ℝ)..c, f u := by
  have hnn : 0 ≤ᵐ[volume.restrict (uIoc 0 c)] f := by
    rw [uIoc_of_le hc.le]
    have h1 : ∀ᵐ u ∂(volume.restrict (Ioc 0 c)), u ∈ Ioc 0 c := ae_restrict_mem measurableSet_Ioc
    have h3 : ∀ᵐ u ∂(volume.restrict (Ioc 0 c)), u ≠ c :=
      ae_restrict_of_ae (Measure.ae_ne volume c)
    filter_upwards [h1, h3, ae_restrict_of_ae hpos] with u hu huc hp
    exact (hp ⟨hu.1, lt_of_le_of_ne hu.2 huc⟩).le
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnn hf]
  refine ⟨hc, ?_⟩
  have hle : volume (Ioo (0 : ℝ) c) ≤ volume (Function.support f ∩ Ioc 0 c) := by
    apply measure_mono_ae
    filter_upwards [hpos] with u hu hmem
    exact ⟨(hu hmem).ne', Ioo_subset_Ioc_self hmem⟩
  rw [Real.volume_Ioo] at hle
  exact lt_of_lt_of_le (by simpa using hc) hle

theorem integral_w_sub (hw : IntervalIntegrable w volume 0 1) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..y, w u * (f u - g u) =
      (∫ u in (0 : ℝ)..y, w u * f u) - ∫ u in (0 : ℝ)..y, w u * g u := by
  rw [← intervalIntegral.integral_sub (ii_w_mul hw hf ⟨le_rfl, zero_le_one⟩ hy)
    (ii_w_mul hw hg ⟨le_rfl, zero_le_one⟩ hy)]
  congr 1
  funext u
  ring

theorem integral_w_blockE (hw : IntervalIntegrable w volume 0 1) {T : Set ℕ}
    (hT : ∀ t ∈ T, 1 ≤ t) (E : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..y, w u * blockESet T (u ^ E) =
      FwD w E y T - ∫ u in (0 : ℝ)..y, w u * (1 - u ^ E) :=
  integral_w_sub hw (contOn_qProdSet_pow hT E) (contOn_one_sub_pow E) hy

theorem integral_w_g (hw : IntervalIntegrable w volume 0 1) (E : ℕ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..y, w u * (Qfun (u ^ E) - (1 - u ^ E)) =
      FwD w E y Primes - ∫ u in (0 : ℝ)..y, w u * (1 - u ^ E) :=
  integral_w_sub hw (contOn_Qfun_pow E) (contOn_one_sub_pow E) hy

/-- More exponents give a smaller functional. -/
theorem FwD_antitone (hw : IntervalIntegrable w volume 0 1)
    (hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u) {S T : Set ℕ} (hST : S ⊆ T)
    (hT : ∀ n ∈ T, 1 ≤ n) (D : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    FwD w D z T ≤ FwD w D z S := by
  have hS : ∀ n ∈ S, 1 ≤ n := fun n hn => hT n (hST hn)
  refine integral_w_mono hw hw0 (contOn_qProdSet_pow hT D) (contOn_qProdSet_pow hS D) le_rfl hz.1
    hz.2 fun u hu => ?_
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le hz.2⟩
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp only [pow_zero]
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · subst hSe
      rw [qProdSet_empty]
      rcases T.eq_empty_or_nonempty with hTe | hTne
      · subst hTe; rw [qProdSet_empty]
      · rw [qProdSet_one_of_nonempty hTne]; norm_num
    · rw [qProdSet_one_of_nonempty hSne, qProdSet_one_of_nonempty (hSne.mono hST)]
  · exact qProdSet_antitone hST (pow_nonneg hu'.1.le D) (pow_lt_one₀ hu'.1.le hu'.2 (by omega))

/-- Dominated convergence along truncations, `A_N = A ∩ [0,N]`. -/
theorem tendsto_FwD_trunc (hw : IntervalIntegrable w volume 0 1) (A : Set ℕ) {D : ℕ}
    (hD : 1 ≤ D) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun N => FwD w D z ↑((Finset.range (N + 1)).filter (· ∈ A))) atTop
      (𝓝 (FwD w D z A)) := by
  unfold FwD
  simp only [qProdSet_coe, intervalIntegral.integral_of_le hz.1]
  have hwz : IntervalIntegrable w volume 0 z := hw.mono_set (by
    rw [uIcc_of_le hz.1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hz.2)
  have hwI : IntegrableOn w (Ioc 0 z) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.1).mp hwz
  apply tendsto_integral_of_dominated_convergence (bound := fun u => ‖w u‖)
  · exact fun N => hwI.1.mul
      (((qProd_continuous _).comp (continuous_pow D)).aestronglyMeasurable.restrict)
  · exact hwI.norm
  · intro N
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : u ^ D ∈ Icc (0 : ℝ) 1 :=
      ⟨pow_nonneg hu.1.le D, pow_le_one₀ hu.1.le (hu.2.trans hz.2)⟩
    rw [norm_mul]
    calc ‖w u‖ * ‖qProd ((Finset.range (N + 1)).filter (· ∈ A)) (u ^ D)‖ ≤ ‖w u‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg (qProd_nonneg _ hu')]
          exact qProd_le_one _ hu'
      _ = ‖w u‖ := mul_one _
  · have hmem : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) z)), u ∈ Ioc (0 : ℝ) z :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hmem, ae_restrict_ne_one (Ioc (0 : ℝ) z)] with u hu hu1
    have h1 : u < 1 := lt_of_le_of_ne (hu.2.trans hz.2) hu1
    exact tendsto_const_nhds.mul
      (qProdSet_eq_lim A (pow_nonneg hu.1.le D) (pow_lt_one₀ hu.1.le h1 (by omega)))

/-! ## The key fact (b′): running integrals of `w(u) g(u^E)` -/

/-- Under (b), `∫₀ᶻ w(u) g(u^E) du ≥ 0` for every `E ≥ 2` and `z ∈ [0,1]`. -/
theorem run_g_nonneg (hw : IntervalIntegrable w volume 0 1)
    (hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u)
    (hb : ∀ D : ℕ, 2 ≤ D → 0 ≤ ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)))
    {E : ℕ} (hE : 2 ≤ E) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ ∫ u in (0 : ℝ)..z, w u * (Qfun (u ^ E) - (1 - u ^ E)) := by
  obtain ⟨xs, hxs, hposo, hnego⟩ := Qfun_single_crossing
  have hE0 : E ≠ 0 := by omega
  have hgc := contOn_g_pow E
  rcases le_or_gt (z ^ E) xs with hzx | hzx
  · have h := integral_w_mono hw hw0 (f := fun _ => (0 : ℝ)) continuousOn_const hgc le_rfl hz.1
      hz.2 (fun u hu => by
        have hv0 : 0 < u ^ E := pow_pos hu.1 E
        have hvz : u ^ E < z ^ E := pow_lt_pow_left₀ hu.2 hu.1.le hE0
        have := hposo (u ^ E) ⟨hv0, lt_of_lt_of_le hvz hzx⟩
        show (0 : ℝ) ≤ Qfun (u ^ E) - (1 - u ^ E)
        linarith)
    simpa using h
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (ii_w_mul hw hgc ⟨le_rfl, zero_le_one⟩ hz) (ii_w_mul hw hgc hz ⟨zero_le_one, le_rfl⟩)
    have htail : ∫ u in z..1, w u * (Qfun (u ^ E) - (1 - u ^ E)) ≤ 0 := by
      have h := integral_w_mono hw hw0 (g := fun _ => (0 : ℝ)) hgc continuousOn_const hz.1 hz.2
        le_rfl (fun u hu => by
          have hz0 : 0 ≤ z := hz.1
          have hvz : z ^ E < u ^ E := pow_lt_pow_left₀ hu.1 hz0 hE0
          have hv1 : u ^ E < 1 := pow_lt_one₀ (hz0.trans hu.1.le) hu.2 hE0
          have := hnego (u ^ E) ⟨lt_trans hzx hvz, hv1⟩
          show Qfun (u ^ E) - (1 - u ^ E) ≤ 0
          linarith)
      simpa using h
    have := hb E hE
    linarith

/-- Under strict (b) and `w > 0` a.e., `∫₀ᶻ w(u) g(u^E) du > 0` for `E ≥ 2`, `z ∈ (0,1]`. -/
theorem run_g_pos (hw : IntervalIntegrable w volume 0 1)
    (hwpos : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 < w u)
    (hbs : ∀ D : ℕ, 2 ≤ D → 0 < ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)))
    {E : ℕ} (hE : 2 ≤ E) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..z, w u * (Qfun (u ^ E) - (1 - u ^ E)) := by
  have hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u := hwpos.mono fun u h hu => (h hu).le
  have hzI : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2⟩
  obtain ⟨xs, hxs, hposo, hnego⟩ := Qfun_single_crossing
  have hE0 : E ≠ 0 := by omega
  have hgc := contOn_g_pow E
  rcases le_or_gt (z ^ E) xs with hzx | hzx
  · refine integral_pos_of_ae_pos hz.1 (ii_w_mul hw hgc ⟨le_rfl, zero_le_one⟩ hzI) ?_
    filter_upwards [hwpos] with u hu hmem
    have hv0 : 0 < u ^ E := pow_pos hmem.1 E
    have hvz : u ^ E < z ^ E := pow_lt_pow_left₀ hmem.2 hmem.1.le hE0
    have := hposo (u ^ E) ⟨hv0, lt_of_lt_of_le hvz hzx⟩
    exact mul_pos (hu ⟨hmem.1, hmem.2.trans_le hz.2⟩) (by linarith)
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (ii_w_mul hw hgc ⟨le_rfl, zero_le_one⟩ hzI) (ii_w_mul hw hgc hzI ⟨zero_le_one, le_rfl⟩)
    have htail : ∫ u in z..1, w u * (Qfun (u ^ E) - (1 - u ^ E)) ≤ 0 := by
      have h := integral_w_mono hw hw0 (g := fun _ => (0 : ℝ)) hgc continuousOn_const hzI.1 hz.2
        le_rfl (fun u hu => by
          have hz0 : 0 ≤ z := hzI.1
          have hvz : z ^ E < u ^ E := pow_lt_pow_left₀ hu.1 hz0 hE0
          have hv1 : u ^ E < 1 := pow_lt_one₀ (hz0.trans hu.1.le) hu.2 hE0
          have := hnego (u ^ E) ⟨lt_trans hzx hvz, hv1⟩
          show Qfun (u ^ E) - (1 - u ^ E) ≤ 0
          linarith)
      simpa using h
    have := hbs E hE
    linarith

/-! ## The compression identity with index `D` -/

theorem quot_ge_one {A : Set ℕ} (hA1 : ∀ a ∈ A, 1 ≤ a) {d : ℕ} (hd : 0 < d) :
    ∀ t ∈ (fun a => a / d) '' {a ∈ A | d ∣ a}, 1 ≤ t := by
  rintro t ⟨a, ⟨ha, hda⟩, rfl⟩
  exact Nat.div_pos (Nat.le_of_dvd (hA1 a ha) hda) hd

/-- `F(A) - F(C_d A) = ∫₀ᶻ P_B(u^D) · w(u) E_T(u^{Dd}) du` with `P_B(u^D) = P_{DB}(u)`. -/
theorem FwD_sub_compress (hw : IntervalIntegrable w volume 0 1) {A : Set ℕ}
    (hA1 : ∀ a ∈ A, 1 ≤ a) {d D : ℕ} (hd : 0 < d) (hD : 1 ≤ D) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) :
    FwD w D z A - FwD w D z (compressAtSet d A) =
      ∫ u in (0 : ℝ)..z, qProdSet ((· * D) '' {a ∈ A | ¬ d ∣ a}) u *
        (w u * blockESet ((fun a => a / d) '' {a ∈ A | d ∣ a}) (u ^ (D * d))) := by
  have hC1 : ∀ a ∈ compressAtSet d A, 1 ≤ a := by
    rintro a (rfl | ⟨ha, _⟩)
    · exact hd
    · exact hA1 a ha
  unfold FwD
  rw [← intervalIntegral.integral_sub
    (ii_w_mul hw (contOn_qProdSet_pow hA1 D) ⟨le_rfl, zero_le_one⟩ hz)
    (ii_w_mul hw (contOn_qProdSet_pow hC1 D) ⟨le_rfl, zero_le_one⟩ hz)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume 1] with u hu1 hu
  rw [uIoc_of_le hz.1] at hu
  have h0 : 0 ≤ u ^ D := pow_nonneg hu.1.le D
  have h1 : u ^ D < 1 :=
    pow_lt_one₀ hu.1.le (lt_of_le_of_ne (hu.2.trans hz.2) hu1) (by omega)
  have hpB : d ∉ {a ∈ A | ¬ d ∣ a} := fun h => h.2 (dvd_refl d)
  have hdec := qProdSet_blockStep_diff hd (disjoint_nonMultiples_block_set d A) hpB h0 h1
  rw [← block_decomp_set d A] at hdec
  have hC : compressAtSet d A = insert d {a ∈ A | ¬ d ∣ a} := rfl
  rw [hC, qProdSet_image_mul _ hD u, pow_mul, ← mul_sub, hdec]
  ring

/-- A compression step lowers the functional once the running integrals of the compression
integrand are nonnegative. -/
theorem FwD_compress_le (hw : IntervalIntegrable w volume 0 1) {A : Set ℕ}
    (hA1 : ∀ a ∈ A, 1 ≤ a) {d D : ℕ} (hd : 0 < d) (hD : 1 ≤ D) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1)
    (hrun : ∀ y ∈ Icc (0 : ℝ) z, 0 ≤ ∫ u in (0 : ℝ)..y,
      w u * blockESet ((fun a => a / d) '' {a ∈ A | d ∣ a}) (u ^ (D * d))) :
    FwD w D z (compressAtSet d A) ≤ FwD w D z A := by
  have h := FwD_sub_compress hw hA1 hd hD hz
  have hnn := integral_qProdSet_mul_nonneg_L1 ((· * D) '' {a ∈ A | ¬ d ∣ a}) hz
    (ii_w_mul hw (contOn_blockE_pow (quot_ge_one hA1 hd) _) ⟨le_rfl, zero_le_one⟩ hz) hrun
  linarith

/-! ## Minimal elements of truncations -/

theorem minElems_trunc {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) (N : ℕ) :
    minElems {u ∈ U | u ≤ N} = {m ∈ minElems U | m ≤ N} := by
  ext m
  constructor
  · rintro ⟨⟨hmU, hmN⟩, hmin⟩
    refine ⟨⟨hmU, fun d hdU hdm => hmin d ⟨hdU, ?_⟩ hdm⟩, hmN⟩
    exact (Nat.le_of_dvd (by have := hU m hmU; omega) hdm).trans hmN
  · rintro ⟨⟨hmU, hmin⟩, hmN⟩
    exact ⟨⟨hmU, hmN⟩, fun d hd hdm => hmin d hd.1 hdm⟩

theorem coe_quotients (d : ℕ) (A : Finset ℕ) :
    ((quotients d A : Finset ℕ) : Set ℕ) = (fun a => a / d) '' {a ∈ (A : Set ℕ) | d ∣ a} := by
  simp [quotients, Finset.coe_image, Finset.coe_filter]

/-! ## The finite claim `C(N)` -/

/-- **Claim `C(N)`.** Under (b): for every index `D ≥ 1`, `z ∈ [0,1]`, `U ⊆ [2,N]` and
finite primitive `A ⊆ U`: `∫₀ᶻ w P_{Min U}(u^D) ≤ ∫₀ᶻ w P_A(u^D)`. -/
theorem FwD_minElems_le_fin (hw : IntervalIntegrable w volume 0 1)
    (hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u)
    (hb : ∀ D : ℕ, 2 ≤ D → 0 ≤ ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)))
    (N : ℕ) : ∀ D : ℕ, 1 ≤ D → ∀ z ∈ Icc (0 : ℝ) 1, ∀ U : Set ℕ,
      (∀ u ∈ U, 2 ≤ u ∧ u ≤ N) → ∀ A : Finset ℕ, IsPrimitiveFin A → (↑A : Set ℕ) ⊆ U →
        FwD w D z (minElems U) ≤ FwD w D z ↑A := by
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro D hD z hz U hU
  have hU2 : ∀ u ∈ U, 2 ≤ u := fun u hu => (hU u hu).1
  have hMin1 : ∀ n ∈ minElems U, 1 ≤ n := fun n hn => le_trans (by norm_num) (hU2 n hn.1)
  suffices H : ∀ (s : ℕ) (A : Finset ℕ), A.sum id ≤ s → IsPrimitiveFin A → (↑A : Set ℕ) ⊆ U →
      FwD w D z (minElems U) ≤ FwD w D z ↑A from fun A hA hAU => H _ A le_rfl hA hAU
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  intro A hsum hA hAU
  by_cases hall : ∀ a ∈ A, a ∈ minElems U
  · exact FwD_antitone hw hw0 (fun a ha => hall a (Finset.mem_coe.mp ha)) hMin1 D hz
  · obtain ⟨a, haA, hna⟩ : ∃ a ∈ A, a ∉ minElems U := by
      by_contra h
      push Not at h
      exact hall h
    obtain ⟨d, hdU, hda, hdA, hnd⟩ :=
      exists_divisor_of_not_minElems hA (Finset.mem_coe.mpr haA) (hAU haA) hna
    have hd2 : 2 ≤ d := hU2 d hdU
    have hd0 : 0 < d := by omega
    have hmult : ∃ a ∈ A, d ∣ a := ⟨a, haA, hda⟩
    have hA1 : ∀ x ∈ (↑A : Set ℕ), 1 ≤ x := fun x hx => le_trans (by norm_num) (hA.1 x hx)
    -- the running integrals of the compression integrand
    have hrun : ∀ y ∈ Icc (0 : ℝ) z, 0 ≤ ∫ u in (0 : ℝ)..y,
        w u * blockESet ((fun a => a / d) '' {a ∈ (↑A : Set ℕ) | d ∣ a}) (u ^ (D * d)) := by
      intro y hy
      have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans hz.2⟩
      have hE : 2 ≤ D * d := by nlinarith
      set M := N / d with hMdef
      have haN : a ≤ N := (hU a (hAU haA)).2
      have hNpos : 0 < N := by have := hA.1 a haA; omega
      have hMN : M < N := Nat.div_lt_self hNpos (by omega)
      set U' : Set ℕ := {u ∈ {n : ℕ | 2 ≤ n} | u ≤ M} with hU'def
      have hU' : ∀ u ∈ U', 2 ≤ u ∧ u ≤ M := fun u hu => ⟨hu.1, hu.2⟩
      have hTp : IsPrimitiveFin (quotients d A) := by
        unfold IsPrimitiveFin
        rw [coe_quotients]
        exact quotients_set_isPrimitive hA hdA
      have hTU' : (↑(quotients d A) : Set ℕ) ⊆ U' := by
        rw [coe_quotients]
        rintro t ⟨b, ⟨hb, hdb⟩, rfl⟩
        refine ⟨quotients_set_ge_two_of_not_mem hA.1 hdA _ ⟨b, ⟨hb, hdb⟩, rfl⟩, ?_⟩
        exact Nat.div_le_div_right (hU b (hAU hb)).2
      have hC := ihN M hMN (D * d) (by omega) y hy1 U' hU' (quotients d A) hTp hTU'
      rw [coe_quotients, hU'def, minElems_trunc (U := {n : ℕ | 2 ≤ n}) (fun u hu => hu) M, minElems_ge_two] at hC
      have hT1 := quot_ge_one hA1 hd0
      rw [integral_w_blockE hw hT1 (D * d) hy1]
      have hg := run_g_nonneg hw hw0 hb hE hy1
      rw [integral_w_g hw (D * d) hy1] at hg
      have hPM : FwD w (D * d) y Primes ≤ FwD w (D * d) y {m ∈ Primes | m ≤ M} :=
        FwD_antitone hw hw0 (fun m hm => hm.1) (fun n hn => (Nat.Prime.one_le hn)) _ hy1
      linarith
    have hstep := FwD_compress_le hw hA1 hd0 hD hz hrun
    have hA' : IsPrimitiveFin (compressAt d A) := compressAt_isPrimitiveFin_of hA hd2 hnd
    have hAU' : (↑(compressAt d A) : Set ℕ) ⊆ U := by
      intro x hx
      rcases mem_compressAt.mp (Finset.mem_coe.mp hx) with rfl | ⟨hxA, _⟩
      · exact hdU
      · exact hAU hxA
    have hsum' : (compressAt d A).sum id < A.sum id := sum_compressAt_lt hd2 hA hdA hmult
    have hih := ihs _ (lt_of_lt_of_le hsum' hsum) (compressAt d A) le_rfl hA' hAU'
    rw [coe_compressAt] at hih
    linarith

/-- **Lower bound with index `D`, arbitrary sets.** Under (b): for every `D ≥ 1`, `z ∈ [0,1]`,
`U ⊆ {2,3,…}` and primitive `A ⊆ U`: `∫₀ᶻ w P_{Min U}(u^D) ≤ ∫₀ᶻ w P_A(u^D)`. -/
theorem FwD_minElems_le (hw : IntervalIntegrable w volume 0 1)
    (hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u)
    (hb : ∀ D : ℕ, 2 ≤ D → 0 ≤ ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)))
    {D : ℕ} (hD : 1 ≤ D) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) {U : Set ℕ}
    (hU : ∀ u ∈ U, 2 ≤ u) {A : Set ℕ} (hA : IsPrimitive A) (hAU : A ⊆ U) :
    FwD w D z (minElems U) ≤ FwD w D z A := by
  refine le_of_tendsto_of_tendsto' (tendsto_FwD_trunc hw (minElems U) hD hz)
    (tendsto_FwD_trunc hw A hD hz) fun N => ?_
  have hEq : (↑((Finset.range (N + 1)).filter (· ∈ minElems U)) : Set ℕ)
      = minElems {u ∈ U | u ≤ N} := by
    rw [minElems_trunc hU N]
    ext m
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
  rw [hEq]
  refine FwD_minElems_le_fin hw hw0 hb N D hD z hz {u ∈ U | u ≤ N}
    (fun u hu => ⟨hU u hu.1, hu.2⟩) _ (truncation_isPrimitiveFin hA N) ?_
  intro x hx
  have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
  exact ⟨hAU hx'.2, truncation_bounded A N x (Finset.mem_coe.mp hx)⟩

/-! ## Strict steps -/

theorem Fw_insert_lt (hw : IntervalIntegrable w volume 0 1)
    (hwpos : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 < w u) {A : Set ℕ} {q : ℕ} (hq : q ∉ A)
    (hq1 : 1 ≤ q) (hA1 : ∀ n ∈ A, 1 ≤ n) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fw w c (insert q A) < Fw w c A := by
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hqA1 : ∀ n ∈ insert q A, 1 ≤ n := by
    rintro n (rfl | hn)
    · exact hq1
    · exact hA1 n hn
  have hI1 := ii_w_mul hw (qProdSet_continuousOn_Icc hqA1) ⟨le_rfl, zero_le_one⟩ hcI
  have hI2 := ii_w_mul hw (qProdSet_continuousOn_Icc hA1) ⟨le_rfl, zero_le_one⟩ hcI
  rw [← sub_pos]
  unfold Fw
  rw [← intervalIntegral.integral_sub hI2 hI1]
  apply integral_pos_of_ae_pos hc.1 (hI2.sub hI1)
  filter_upwards [hwpos] with u hu hmem
  have hu1 : u < 1 := hmem.2.trans_le hc.2
  rw [qProdSet_insert hq hmem.1.le hu1]
  have hP := qProdSet_pos_of_one_le A hA1 hmem.1.le hu1
  have hwu := hu ⟨hmem.1, hu1⟩
  have hpow := pow_pos hmem.1 q
  have e : w u * qProdSet A u - w u * ((1 - u ^ q) * qProdSet A u)
      = w u * u ^ q * qProdSet A u := by ring
  rw [e]
  exact mul_pos (mul_pos hwu hpow) hP

/-- **Strict compression** under strict (b) and `w > 0` a.e. -/
theorem Fw_compress_lt (hw : IntervalIntegrable w volume 0 1)
    (hwpos : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 < w u)
    (hbs : ∀ D : ℕ, 2 ≤ D → 0 < ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)))
    {A : Set ℕ} (hA : IsPrimitive A) {d : ℕ} (hd2 : 2 ≤ d) (hdA : d ∉ A)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fw w c (compressAtSet d A) < Fw w c A := by
  have hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u := hwpos.mono fun u h hu => (h hu).le
  have hb : ∀ D : ℕ, 2 ≤ D → 0 ≤ ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)) :=
    fun D hD => (hbs D hD).le
  have hA1 : ∀ a ∈ A, 1 ≤ a := fun a ha => le_trans (by norm_num) (hA.1 a ha)
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hd0 : 0 < d := by omega
  have hTp := quotients_set_isPrimitive hA hdA
  have hT1 := quot_ge_one hA1 hd0
  have h := FwD_sub_compress hw hA1 hd0 le_rfl hcI
  rw [FwD_one, FwD_one] at h
  have hS : ∀ n ∈ (· * 1) '' {a ∈ A | ¬ d ∣ a}, 2 ≤ n := by
    rintro n ⟨b, hb, rfl⟩
    simpa using hA.1 b hb.1
  have hkey : ∀ y ∈ Icc (0 : ℝ) 1,
      ∫ u in (0 : ℝ)..y, w u * (Qfun (u ^ (1 * d)) - (1 - u ^ (1 * d))) ≤
      ∫ u in (0 : ℝ)..y, w u * blockESet ((fun a => a / d) '' {a ∈ A | d ∣ a}) (u ^ (1 * d)) := by
    intro y hy
    rw [integral_w_blockE hw hT1 _ hy, integral_w_g hw _ hy]
    have := FwD_minElems_le hw hw0 hb (D := 1 * d) (by omega) hy (U := {n | 2 ≤ n})
      (fun u hu => hu) hTp (fun t ht => hTp.1 t ht)
    rw [minElems_ge_two] at this
    linarith
  have hE : 2 ≤ 1 * d := by omega
  have hpos := integral_qProdSet_mul_pos_L1 hS hc
    (ii_w_mul hw (contOn_blockE_pow hT1 _) ⟨le_rfl, zero_le_one⟩ hcI)
    (fun y hy => (run_g_nonneg hw hw0 hb hE ⟨hy.1, hy.2.trans hc.2⟩).trans
      (hkey y ⟨hy.1, hy.2.trans hc.2⟩))
    (fun y hy => (run_g_pos hw hwpos hbs hE ⟨hy.1, hy.2.trans hc.2⟩).trans_le
      (hkey y ⟨hy.1.le, hy.2.trans hc.2⟩))
  linarith

/-! ## (a) ⇒ (b) -/

theorem cond_of_relative (hw : IntervalIntegrable w volume 0 1)
    (ha : ∀ U : Finset ℕ, (∀ u ∈ U, 2 ≤ u) → ∀ A : Set ℕ, IsPrimitive A → A ⊆ ↑U →
      Fw w 1 (minElems ↑U) ≤ Fw w 1 A)
    {D : ℕ} (hD : 2 ≤ D) :
    0 ≤ ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)) := by
  have hD0 : 0 < D := by omega
  have hstep : ∀ M : ℕ,
      ∫ u in (0 : ℝ)..1, w u * (1 - u ^ D) ≤ FwD w D 1 ↑(primesLE M) := by
    intro M
    set A : Finset ℕ := (primesLE M).image (· * D) with hAdef
    have hAmem : ∀ x ∈ A, ∃ p, Nat.Prime p ∧ x = p * D := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨p, (mem_primesLE.mp hp).1, rfl⟩
    have hU : ∀ u ∈ insert D A, 2 ≤ u := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hD
      · obtain ⟨p, hp, rfl⟩ := hAmem u hu
        nlinarith [hp.two_le]
    have hAp : IsPrimitive (↑A : Set ℕ) := by
      refine ⟨fun x hx => hU x (Finset.mem_insert_of_mem hx), fun x hx y hy hxy => ?_⟩
      obtain ⟨p, hp, rfl⟩ := hAmem x hx
      obtain ⟨q, hq, rfl⟩ := hAmem y hy
      have hpq : p ∣ q := Nat.dvd_of_mul_dvd_mul_right hD0 hxy
      rw [(Nat.prime_dvd_prime_iff_eq hp hq).mp hpq]
    have hmin : minElems (↑(insert D A) : Set ℕ) = {D} := by
      ext m
      simp only [minElems, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
        Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hmU, hmin⟩
        rcases hmU with rfl | hmA
        · rfl
        · obtain ⟨p, hp, rfl⟩ := hAmem m hmA
          have := hmin D (Or.inl rfl) (dvd_mul_left D p)
          nlinarith [hp.two_le]
      · rintro rfl
        refine ⟨Or.inl rfl, fun x hx hxD => ?_⟩
        rcases hx with rfl | hxA
        · rfl
        · obtain ⟨p, hp, rfl⟩ := hAmem x hxA
          have h1 := Nat.le_of_dvd hD0 hxD
          nlinarith [hp.two_le]
    have h := ha (insert D A) hU ↑A hAp (by simp)
    rw [hmin] at h
    have e1 : Fw w 1 {D} = ∫ u in (0 : ℝ)..1, w u * (1 - u ^ D) := by
      unfold Fw
      simp_rw [qProdSet_singleton]
    have e2 : Fw w 1 ↑A = FwD w D 1 ↑(primesLE M) := by
      unfold Fw FwD
      rw [hAdef, Finset.coe_image]
      simp_rw [qProdSet_image_mul _ hD0]
    linarith
  have hlim := tendsto_FwD_trunc hw Primes (by omega : 1 ≤ D) ⟨zero_le_one, le_rfl⟩
  simp only [primes_truncation] at hlim
  have hle : ∫ u in (0 : ℝ)..1, w u * (1 - u ^ D) ≤ FwD w D 1 Primes :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hstep)
  rw [integral_w_g hw D ⟨zero_le_one, le_rfl⟩]
  linarith

end Weight

/-! ## Main theorems -/

/-- **Relative cone, lower bound.** Let `w ∈ L¹(0,1)` with `w ≥ 0` a.e. on `(0,1)`, and assume
`∫₀¹ w(u) [Q(u^D) - (1 - u^D)] du ≥ 0` for every integer `D ≥ 2`. Then for every `c ∈ (0,1]`,
every `U ⊆ {2,3,…}` and every primitive `A ⊆ U` (finite or infinite):
`F_{w,c}(Min U) ≤ F_{w,c}(A)`. -/
theorem relative_cone_le {w : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1)
    (hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u)
    (hb : ∀ D : ℕ, 2 ≤ D → 0 ≤ ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)))
    {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) {A : Set ℕ} (hA : IsPrimitive A) (hAU : A ⊆ U)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fw w c (minElems U) ≤ Fw w c A := by
  have := FwD_minElems_le hw hw0 hb le_rfl ⟨hc.1.le, hc.2⟩ hU hA hAU
  rwa [FwD_one, FwD_one] at this

/-- **Relative cone, unique attainment.** If moreover `w > 0` a.e. on `(0,1)` and the
inequalities `∫₀¹ w(u) [Q(u^D) - (1 - u^D)] du > 0` are strict for every `D ≥ 2`, then
`F_{w,c}(Min U) < F_{w,c}(A)` for every primitive `A ⊆ U` with `A ≠ Min U`. -/
theorem relative_cone_lt {w : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1)
    (hwpos : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 < w u)
    (hbs : ∀ D : ℕ, 2 ≤ D → 0 < ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)))
    {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) {A : Set ℕ} (hA : IsPrimitive A) (hAU : A ⊆ U)
    (hne : A ≠ minElems U) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fw w c (minElems U) < Fw w c A := by
  have hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u := hwpos.mono fun u h hu => (h hu).le
  have hb : ∀ D : ℕ, 2 ≤ D → 0 ≤ ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)) :=
    fun D hD => (hbs D hD).le
  by_cases hall : A ⊆ minElems U
  · obtain ⟨q, hqM, hqA⟩ : ∃ q ∈ minElems U, q ∉ A := by
      by_contra h
      push Not at h
      exact hne (Set.Subset.antisymm hall h)
    have hsub : insert q A ⊆ minElems U := Set.insert_subset hqM hall
    have hA' : IsPrimitive (insert q A) := isPrimitive_mono (minElems_isPrimitive hU) hsub
    exact lt_of_le_of_lt
      (relative_cone_le hw hw0 hb hU hA' (hsub.trans fun _ h => h.1) hc)
      (Fw_insert_lt hw hwpos hqA (le_trans (by norm_num) (hU q hqM.1))
        (fun n hn => le_trans (by norm_num) (hA.1 n hn)) hc)
  · obtain ⟨a, haA, hna⟩ : ∃ a ∈ A, a ∉ minElems U := by
      by_contra h
      push Not at h
      exact hall h
    obtain ⟨d, hdU, hda, hdA, hnd⟩ := exists_divisor_of_not_minElems hA haA (hAU haA) hna
    have hd2 : 2 ≤ d := hU d hdU
    have hstep := Fw_compress_lt hw hwpos hbs hA hd2 hdA hc
    have hC : IsPrimitive (compressAtSet d A) := compressAtSet_isPrimitive_of hA hd2 hnd
    have hCU : compressAtSet d A ⊆ U := by
      rintro x (rfl | ⟨hxA, _⟩)
      · exact hdU
      · exact hAU hxA
    exact lt_of_le_of_lt (relative_cone_le hw hw0 hb hU hC hCU hc) hstep

/-- **Theorem (relative cone).** For `w ∈ L¹(0,1)` with `w ≥ 0` a.e. on `(0,1)`, the following
are equivalent:
(a) `F_{w,1}(Min U) ≤ F_{w,1}(A)` for every finite `U ⊆ {2,3,…}` and every primitive `A ⊆ U`;
(b) `∫₀¹ w(u) [Q(u^D) - (1 - u^D)] du ≥ 0` for every integer `D ≥ 2`. -/
theorem relative_cone_iff {w : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1)
    (hw0 : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → 0 ≤ w u) :
    (∀ U : Finset ℕ, (∀ u ∈ U, 2 ≤ u) → ∀ A : Set ℕ, IsPrimitive A → A ⊆ ↑U →
        Fw w 1 (minElems ↑U) ≤ Fw w 1 A) ↔
      ∀ D : ℕ, 2 ≤ D → 0 ≤ ∫ u in (0 : ℝ)..1, w u * (Qfun (u ^ D) - (1 - u ^ D)) := by
  constructor
  · intro ha D hD
    exact cond_of_relative hw ha hD
  · intro hb U hU A hA hAU
    exact relative_cone_le hw hw0 hb (fun u hu => hU u hu) hA hAU ⟨zero_lt_one, le_rfl⟩

end RntPaper
