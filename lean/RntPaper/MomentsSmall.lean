import RntPaper.MomentsReal

/-!
# Moments `𝔼 Z_A^k` for `0 < k < 1`

For `0 < k ≤ 1` the weight `k u^{k-1}` is nonincreasing, so moment minimality follows
from the truncated-integral theorems (`k = 1`) by one integration by parts:
with `D = P_A - P_{A'}` and `F(y) = ∫₀ʸ D`,
`∫₀ᶜ k u^{k-1} D = k c^{k-1} F(c) + k(1-k) ∫₀ᶜ u^{k-2} F(u) du`,
both terms being nonnegative when `F ≥ 0`, the first positive when `F(c) > 0`.
The boundary term at `0` vanishes because `|F(ε)| ≤ ε`.
(This is the increasing-concave argument of Corollary 1.5 for `φ(x) = min(x, c)^k`.)
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set Filter Topology

theorem intervalIntegrable_MSet_of_pos {A : Set ℕ} (hA : ∀ n ∈ A, 1 ≤ n) {k : ℝ}
    (hk : 0 < k) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => k * u ^ (k - 1) * qProdSet A u) volume 0 c := by
  have hw : IntervalIntegrable (fun u : ℝ => k * u ^ (k - 1)) volume 0 c :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul k
  exact hw.mul_continuousOn ((qProdSet_continuousOn_Icc hA).mono
    (uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ hc))

/-- **The singular-weight comparison.** Let `D` be continuous on `[0,1]` with `|D| ≤ 1`,
`F(y) = ∫₀ʸ D ≥ 0` on `[0,1]` and `F(c) > 0`. Then `∫₀ᶜ k u^{k-1} D(u) du > 0`
for `0 < k ≤ 1`. -/
theorem integral_rpow_weight_pos {D : ℝ → ℝ} (hD : Continuous D)
    (hDb : ∀ u ∈ Icc (0 : ℝ) 1, |D u| ≤ 1)
    (hF0 : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ ∫ u in (0 : ℝ)..y, D u)
    {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1)
    (hFc : 0 < ∫ u in (0 : ℝ)..c, D u) :
    0 < ∫ u in (0 : ℝ)..c, k * u ^ (k - 1) * D u := by
  set F : ℝ → ℝ := runInt D with hFdef
  have hFderiv : ∀ x, HasDerivAt F (D x) x := fun x => hasDerivAt_runInt hD x
  have hFbound : ∀ ε ∈ Icc (0 : ℝ) 1, |F ε| ≤ ε := by
    intro ε hε
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := ε) (C := 1)
      (f := D) (by
        intro v hv
        rw [uIoc_of_le hε.1] at hv
        simpa [Real.norm_eq_abs] using hDb v ⟨hv.1.le, hv.2.trans hε.2⟩)
    simpa [hFdef, runInt, Real.norm_eq_abs, abs_of_nonneg hε.1] using this
  -- weight and its derivative on `(0, ∞)`
  set w : ℝ → ℝ := fun u => k * u ^ (k - 1) with hw
  set w' : ℝ → ℝ := fun u => k * ((k - 1) * u ^ (k - 1 - 1)) with hw'
  have hwderiv : ∀ x : ℝ, x ≠ 0 → HasDerivAt w (w' x) x := fun x hx =>
    (Real.hasDerivAt_rpow_const (p := k - 1) (Or.inl hx)).const_mul k
  have hwint : ∀ a b : ℝ, IntervalIntegrable w volume a b := fun a b =>
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul k
  have hgint : ∀ a b : ℝ, IntervalIntegrable (fun u => w u * D u) volume a b := fun a b =>
    (hwint a b).mul_continuousOn hD.continuousOn
  -- integration by parts on `[ε, c]`
  have hstep : ∀ ε : ℝ, 0 < ε → ε < c →
      w c * F c - w ε * F ε ≤ ∫ u in ε..c, w u * D u := by
    intro ε hε hεc
    have hmem : ∀ x ∈ Set.uIcc ε c, x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hεc.le] at hx
      exact ne_of_gt (lt_of_lt_of_le hε hx.1)
    have hw'cont : ContinuousOn w' (Set.uIcc ε c) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      left
      exact hmem x hx
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := c)
      (u := w) (v := F) (u' := w') (v' := D) (fun x hx => hwderiv x (hmem x hx))
      (fun x _ => hFderiv x) hw'cont.intervalIntegrable (hD.intervalIntegrable ε c)
    have htail : (∫ x in ε..c, w' x * F x) ≤ 0 := by
      have hle : (∫ x in ε..c, w' x * F x) ≤ ∫ _ in ε..c, (0 : ℝ) := by
        apply intervalIntegral.integral_mono_on hεc.le
        · exact hw'cont.intervalIntegrable.mul_continuousOn
            (continuous_runInt hD).continuousOn
        · exact _root_.intervalIntegrable_const
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
          have hFx : 0 ≤ F x := hF0 x ⟨hx0.le, hx.2.trans hc.2⟩
          have hw'x : w' x ≤ 0 := by
            simp only [hw']
            have : (k - 1) * x ^ (k - 1 - 1) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg hx0.le _)
            nlinarith
          exact mul_nonpos_of_nonpos_of_nonneg hw'x hFx
      simpa using hle
    linarith
  -- the boundary term `w(ε) F(ε) → 0`
  have hbdry : Tendsto (fun ε => w ε * F ε) (𝓝[>] 0) (𝓝 0) := by
    have hbound : ∀ ε ∈ Ioo (0 : ℝ) 1, |w ε * F ε| ≤ k * ε ^ k := by
      intro ε hε
      have hwε : 0 ≤ w ε := by simp only [hw]; exact mul_nonneg hk0.le (Real.rpow_nonneg hε.1.le _)
      rw [abs_mul, abs_of_nonneg hwε]
      calc w ε * |F ε| ≤ w ε * ε := mul_le_mul_of_nonneg_left (hFbound ε ⟨hε.1.le, hε.2.le⟩) hwε
        _ = k * ε ^ k := by
          simp only [hw]
          rw [mul_assoc, ← Real.rpow_add_one hε.1.ne']
          ring_nf
    have hlim : Tendsto (fun ε : ℝ => k * ε ^ k) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => k * ε ^ k) (𝓝 0) (𝓝 (k * 0 ^ k)) :=
        ((Real.continuous_rpow_const hk0.le).const_mul k).tendsto 0
      rw [Real.zero_rpow hk0.ne', mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    simpa [Real.norm_eq_abs] using hbound ε hε
  -- the small piece `∫₀^ε → 0`
  have hsmall : Tendsto (fun ε => ∫ u in (0 : ℝ)..ε, w u * D u) (𝓝[>] 0) (𝓝 0) := by
    have hbound : ∀ ε ∈ Ioo (0 : ℝ) 1, |∫ u in (0 : ℝ)..ε, w u * D u| ≤ ε ^ k := by
      intro ε hε
      have h1 : |∫ u in (0 : ℝ)..ε, w u * D u| ≤ ∫ u in (0 : ℝ)..ε, w u := by
        refine (intervalIntegral.abs_integral_le_integral_abs hε.1.le).trans ?_
        apply intervalIntegral.integral_mono_on hε.1.le (hgint 0 ε).abs (hwint 0 ε)
        intro u hu
        have hwu : 0 ≤ w u := by
          simp only [hw]; exact mul_nonneg hk0.le (Real.rpow_nonneg hu.1 _)
        rw [abs_mul, abs_of_nonneg hwu]
        exact mul_le_of_le_one_right hwu (hDb u ⟨hu.1, hu.2.trans hε.2.le⟩)
      have h2 : (∫ u in (0 : ℝ)..ε, w u) = ε ^ k := by
        simp only [hw]
        rw [intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith : (-1 : ℝ) < k - 1))]
        rw [show k - 1 + 1 = k by ring, Real.zero_rpow hk0.ne', sub_zero]
        field_simp
      linarith
    have hlim : Tendsto (fun ε : ℝ => ε ^ k) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => ε ^ k) (𝓝 0) (𝓝 (0 ^ k)) :=
        (Real.continuous_rpow_const hk0.le).tendsto 0
      rw [Real.zero_rpow hk0.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    simpa [Real.norm_eq_abs] using hbound ε hε
  -- assemble: `∫₀ᶜ wD ≥ w(c)F(c) > 0`
  have hlimit : Tendsto (fun ε => w c * F c - w ε * F ε + ∫ u in (0 : ℝ)..ε, w u * D u)
      (𝓝[>] 0) (𝓝 (w c * F c)) := by
    have := ((tendsto_const_nhds (x := w c * F c)).sub hbdry).add hsmall
    simpa using this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      w c * F c - w ε * F ε + ∫ u in (0 : ℝ)..ε, w u * D u ≤ ∫ u in (0 : ℝ)..c, w u * D u := by
    filter_upwards [Ioo_mem_nhdsGT hc.1] with ε hε
    have hsplit : (∫ u in (0 : ℝ)..c, w u * D u)
        = (∫ u in (0 : ℝ)..ε, w u * D u) + ∫ u in ε..c, w u * D u :=
      (intervalIntegral.integral_add_adjacent_intervals (hgint 0 ε) (hgint ε c)).symm
    linarith [hstep ε hε.1 hε.2]
  have hge := le_of_tendsto hlimit hev
  have hwc : 0 < w c := by simp only [hw]; exact mul_pos hk0 (Real.rpow_pos_of_pos hc.1 _)
  have hpos : 0 < w c * F c := mul_pos hwc hFc
  exact lt_of_lt_of_le hpos hge

/-- Comparison of two product weights through their truncated integrals, `0 < k ≤ 1`. -/
theorem MSet_lt_of_FcSet {A A' : Set ℕ} (hA : ∀ n ∈ A, 1 ≤ n) (hA' : ∀ n ∈ A', 1 ≤ n)
    (hle : ∀ y ∈ Ioc (0 : ℝ) 1, FcSet y A' ≤ FcSet y A) {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) (hlt : FcSet c A' < FcSet c A) :
    MSet k c A' < MSet k c A := by
  set D : ℝ → ℝ := fun u => qProdSet A (clampI u) - qProdSet A' (clampI u) with hDdef
  have hDc : Continuous D :=
    ((qProdSet_continuousOn_Icc hA).comp_continuous continuous_clampI clampI_mem).sub
      ((qProdSet_continuousOn_Icc hA').comp_continuous continuous_clampI clampI_mem)
  have hDon : ∀ u ∈ Icc (0 : ℝ) 1, D u = qProdSet A u - qProdSet A' u := by
    intro u hu; simp only [hDdef, clampI_of_mem hu]
  have hFeq : ∀ y ∈ Icc (0 : ℝ) 1, (∫ u in (0 : ℝ)..y, D u) = FcSet y A - FcSet y A' := by
    intro y hy
    unfold FcSet
    rw [← intervalIntegral.integral_sub (intervalIntegrable_qProdSet A hy)
      (intervalIntegrable_qProdSet A' hy)]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hy.1] at hu
    exact hDon u ⟨hu.1, hu.2.trans hy.2⟩
  have hDb : ∀ u ∈ Icc (0 : ℝ) 1, |D u| ≤ 1 := by
    intro u hu
    rw [hDon u hu, abs_le]
    have h1 := qProdSet_nonneg A hu
    have h2 := qProdSet_nonneg A' hu
    rcases eq_or_lt_of_le hu.2 with h | h
    · subst h
      have h3 : qProdSet A 1 ≤ 1 := by
        by_cases hAe : A.Nonempty
        · rw [qProdSet_one_of_nonempty hAe]; norm_num
        · rw [Set.not_nonempty_iff_eq_empty.mp hAe]; simp [qProdSet]
      have h4 : qProdSet A' 1 ≤ 1 := by
        by_cases hAe : A'.Nonempty
        · rw [qProdSet_one_of_nonempty hAe]; norm_num
        · rw [Set.not_nonempty_iff_eq_empty.mp hAe]; simp [qProdSet]
      constructor <;> linarith
    · have h3 := qProdSet_le_one A hu.1 h
      have h4 := qProdSet_le_one A' hu.1 h
      constructor <;> linarith
  have hF0 : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ ∫ u in (0 : ℝ)..y, D u := by
    intro y hy
    rw [hFeq y hy]
    rcases eq_or_lt_of_le hy.1 with h | h
    · subst h; simp [FcSet]
    · linarith [hle y ⟨h, hy.2⟩]
  have hFc : 0 < ∫ u in (0 : ℝ)..c, D u := by
    rw [hFeq c ⟨hc.1.le, hc.2⟩]; linarith
  have hpos := integral_rpow_weight_pos hDc hDb hF0 hk0 hk1 hc hFc
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  rw [← sub_pos]
  unfold MSet
  rw [← intervalIntegral.integral_sub (intervalIntegrable_MSet_of_pos hA hk0 hcI)
    (intervalIntegrable_MSet_of_pos hA' hk0 hcI)]
  convert hpos using 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hc.1.le] at hu
  simp only [hDon u ⟨hu.1, hu.2.trans hc.2⟩]
  ring

/-- **Moments with `0 < k ≤ 1`, all primitive sets.** -/
theorem MSet_primes_lt_small {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {A : Set ℕ}
    (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A :=
  MSet_lt_of_FcSet (A := A) (A' := Primes) (fun n hn => le_trans (by norm_num) (hA.1 n hn))
    (fun n hn => Nat.Prime.one_le hn)
    (fun y hy => by rw [FcSet_primes]; exact Lfun_le_FcSet hA hy) hk0 hk1 hc
    (by rw [FcSet_primes]; exact Lfun_lt_FcSet hA hne hc)

/-- **Moments with `0 < k ≤ 1`, finite sets.** -/
theorem MSet_primesLE_lt_small {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) :=
  MSet_lt_of_FcSet (A := (A : Set ℕ)) (A' := (primesLE N : Set ℕ))
    (fun n hn => le_trans (by norm_num) (hA.1 n hn))
    (fun n hn => (mem_primesLE.mp (Finset.mem_coe.mp hn)).1.one_le)
    (fun y hy => by rw [FcSet_coe, FcSet_coe]; exact Fc_primesLE_le hA hAN hy) hk0 hk1 hc
    (by rw [FcSet_coe, FcSet_coe]; exact Fc_primesLE_lt hA hAN hne hc)

/-! ## The full range `0 < k ≤ 17/4` -/

/-- **Proposition 5.2 (finite form), `0 < k ≤ 17/4`.** -/
theorem moment_primesLE_lt {k : ℝ} (hk0 : 0 < k) (hk : k ≤ 17 / 4) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) := by
  rcases le_or_gt k 1 with h | h
  · exact MSet_primesLE_lt_small hk0 h hA hAN hne hc
  · exact MSet_primesLE_lt h.le hk hA hAN hne hc

/-- **Proposition 5.2 (all primitive sets), `0 < k ≤ 17/4`.** -/
theorem moment_primes_lt {k : ℝ} (hk0 : 0 < k) (hk : k ≤ 17 / 4) {A : Set ℕ}
    (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A := by
  rcases le_or_gt k 1 with h | h
  · exact MSet_primes_lt_small hk0 h hA hne hc
  · exact MSet_primes_lt h.le hk hA hne hc

/-! ## The general threshold: every `b` with `J_b(1) > 0`

The certificate `moment_cert` is used only through `J_{17/8}(1) > 0`. The same bootstrap
works for any `b` with `J_b(1) > 0`, giving prime minimality for all `0 < k ≤ 2b`; hence
for every `k < 2α₀`, where `α₀` is the root of `J_α(1) = 0`. Such `b` satisfy `b < 3`
because `J_3(1) < 0` (`moment_three_neg`). -/

/-- Any `b` with `J_b(1) > 0` is `< 3`. -/
theorem lt_three_of_Jw_pos {b : ℝ} (hb : 0 < Jw b 1) : b < 3 := by
  by_contra h
  push Not at h
  have h3 : 0 < Jw 3 1 := Jw_pos_of (by norm_num) h hb ⟨by norm_num, le_rfl⟩
  have hneg := moment_three_neg
  unfold Jw at h3
  norm_num at h3 hneg
  linarith

/-- `run_pos_of_lt` with an arbitrary endpoint certificate `J_b(1) > 0`. -/
theorem run_pos_of_lt_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {T : Set ℕ} (hTp : IsPrimitive T)
    {p : ℕ} (hp : 1 ≤ p) {k : ℝ} (hpk : (p : ℝ) ≤ k) (hs : k / p ≤ b) (hgood : GoodAt (k / p))
    {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * ESetExt T (u ^ p) := by
  have hT1 : ∀ t ∈ T, 1 ≤ t := fun t ht => le_trans (by norm_num) (hTp.1 t ht)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hs1 : 1 ≤ k / p := by rw [le_div_iff₀ hpR]; linarith
  rw [integral_rpow_mul_comp_pow (continuousOn_ESetExt_Icc hT1) hp hpk ⟨hy.1.le, hy.2⟩]
  have hz : y ^ p ∈ Ioc (0 : ℝ) 1 := ⟨pow_pos hy.1 p, pow_le_one₀ hy.1.le hy.2⟩
  rw [integral_rpow_ESetExt_eq hs1 ⟨hz.1.le, hz.2⟩]
  have hM : 0 ≤ (MSet (k / p) (y ^ p) T - MSet (k / p) (y ^ p) Primes) / (k / p) :=
    div_nonneg (sub_nonneg.mpr (hgood T hTp _ hz)) (by linarith)
  have hJ : 0 < Jw (k / p) (y ^ p) := Jw_pos_of hs1 hs hb hz
  have : 0 < 1 / (p : ℝ) := by positivity
  nlinarith

theorem admissible_of_good_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {K : ℝ}
    (hK : ∀ s, 1 ≤ s → s ≤ K → GoodAt s) {k : ℝ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * K)
    (hk : k ≤ 2 * b) : Admissible k := by
  intro p hp T hT y hy
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rcases le_or_gt k p with hkp | hpk
  · exact run_pos_of_le hT.1 hp.one_le hk1 hkp hy
  · have hpR : (0 : ℝ) < p := by linarith
    have hs1 : 1 ≤ k / p := by rw [le_div_iff₀ hpR]; linarith
    have hsK : k / p ≤ K := by rw [div_le_iff₀ hpR]; nlinarith
    have hs : k / p ≤ b := by rw [div_le_iff₀ hpR]; nlinarith
    exact run_pos_of_lt_of_Jw hb hT hp.one_le hpk.le hs (hK _ hs1 hsK) hy

/-- Every `k ∈ [1, 2b]` is admissible when `J_b(1) > 0`. -/
theorem admissible_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * b) :
    Admissible k := by
  have hb3 := lt_three_of_Jw_pos hb
  -- round 2: `[1, min 4 (2b)]`
  have hgood2 : ∀ s, 1 ≤ s → s ≤ min 4 (2 * b) → GoodAt s := fun s hs1 hs =>
    goodAt_of_admissible hs1 (admissible_of_good_of_Jw hb (K := 2)
      (fun t ht1 ht => goodAt_le_two ht1 ht) hs1 (by linarith [min_le_left 4 (2 * b)])
      (by linarith [min_le_right 4 (2 * b)]))
  -- round 3: `[1, 2b]`, since `2b ≤ 2·min 4 (2b)` for `b < 3`
  refine admissible_of_good_of_Jw hb hgood2 hk1 ?_ hk
  rcases le_total 4 (2 * b) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; nlinarith [show (0 : ℝ) ≤ 2 * b by linarith]

/-- **Moment minimality up to `2b`, all primitive sets.** If `J_b(1) > 0` then for every
`0 < k ≤ 2b`, every primitive `A ≠ 𝒫` and `c ∈ (0,1]`: `𝓜ₖ,c(𝒫) < 𝓜ₖ,c(A)`. -/
theorem moment_primes_lt_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {k : ℝ} (hk0 : 0 < k)
    (hk : k ≤ 2 * b) {A : Set ℕ} (hA : IsPrimitive A) (hne : A ≠ Primes)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c Primes < MSet k c A := by
  rcases le_or_gt k 1 with h | h
  · exact MSet_primes_lt_small hk0 h hA hne hc
  · exact MSet_primes_lt_of_admissible h.le (admissible_of_Jw hb h.le hk) hA hne hc

/-- **Moment minimality up to `2b`, finite sets.** -/
theorem moment_primesLE_lt_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {k : ℝ} (hk0 : 0 < k)
    (hk : k ≤ 2 * b) {N : ℕ} {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N)
    (hne : A ≠ primesLE N) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) := by
  rcases le_or_gt k 1 with h | h
  · exact MSet_primesLE_lt_small hk0 h hA hAN hne hc
  · exact MSet_primesLE_lt_of_admissible h.le (admissible_of_Jw hb h.le hk) hA hAN hne hc

/-- The exact certificate: `J_{17/8}(1) > 0`. -/
theorem Jw_seventeen_eighths : 0 < Jw (17 / 8) 1 := moment_cert

/-- `J_3(1) < 0`, so the threshold `α₀` (the root of `J_α(1) = 0`) lies in `(17/8, 3)`. -/
theorem Jw_three_neg : Jw 3 1 < 0 := by
  have := moment_three_neg
  unfold Jw
  norm_num at this ⊢
  linarith

end RntPaper
