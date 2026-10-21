import RntPaper.Transport

/-!
# Analytic engine for real moment exponents

Generic lemmas behind the moment theorem for real exponents `k` (paper Proposition 5.2):

* `integral_qProdSet_mul_pos`, `integral_qProdSet_mul_nonneg` — for a continuous `g`
  whose running integrals `∫₀ʸ g` are positive (resp. nonnegative) on `(0,1]`, the
  weighted integral `∫₀ᶜ P_B(u) g(u) du` is positive (resp. nonnegative) for every set
  `B ⊆ {2,3,…}`, finite or infinite. This is the uniform `κ` argument of
  `block_exchange_lt_set`, abstracted from the particular integrand `E_H(uᵖ)`.
* `running_pos_rpow_comp_pow` — power substitution with a real weight: if `e` is
  continuous with positive running integrals, then `∫₀ᶜ u^{k-1} e(uᵖ) du > 0` for real
  `1 ≤ k ≤ p` (paper Lemma 3.1 with the weight `v^{k/p-1}`).
* `integral_rpow_mul_comp_pow` — the substitution `v = uᵖ`:
  `∫₀ʸ u^{k-1} f(uᵖ) du = (1/p) ∫₀^{yᵖ} v^{k/p-1} f(v) dv`.
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set Filter Topology

/-! ## Positivity against the product weights `P_B` -/

/-- The uniform lower bound `κ = ∫₀ᶜ b u^{b-1} H(u) G(u) du` for a running integral `G`. -/
noncomputable def kappaG (b : ℕ) (G : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..c, (b : ℝ) * u ^ (b - 1) * HfunExt u * G u

theorem continuous_kappaG_integrand (b : ℕ) {G : ℝ → ℝ} (hG : Continuous G) :
    Continuous fun u : ℝ => (b : ℝ) * u ^ (b - 1) * HfunExt u * G u :=
  ((continuous_const.mul (continuous_pow _)).mul continuous_HfunExt).mul hG

theorem kappaG_pos {b : ℕ} (hb : 1 ≤ b) {G : ℝ → ℝ} (hGc : Continuous G)
    (hG0 : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ G y) (hGpos : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < G y)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : 0 < kappaG b G c := by
  unfold kappaG
  have h := integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun _ => (0 : ℝ))
    hc.1 continuousOn_const (continuous_kappaG_integrand b hGc).continuousOn ?_ ?_
  · simpa using h
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans hc.2⟩
    have h1 : 0 ≤ (b : ℝ) * x ^ (b - 1) := mul_nonneg (by positivity) (pow_nonneg hx.1.le _)
    have h2 : 0 ≤ HfunExt x := by rw [HfunExt_of_mem hx']; exact Hfun_nonneg hx'
    exact mul_nonneg (mul_nonneg h1 h2) (hG0 x hx')
  · refine ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.1]⟩, ?_⟩
    have hmem : c / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have h1 : 0 < (b : ℝ) * (c / 2) ^ (b - 1) := mul_pos hbR (pow_pos (by linarith [hc.1]) _)
    have h2 : 0 < HfunExt (c / 2) := by
      rw [HfunExt_of_mem hmem]
      exact Hfun_pos_of_lt hmem.1 (by linarith [hc.2])
    have h3 : 0 < G (c / 2) := hGpos _ ⟨by linarith [hc.1], by linarith [hc.2]⟩
    exact mul_pos (mul_pos h1 h2) h3

/-- Finite weights: `∫₀ᶜ P_S g ≥ κ` whenever `b ∈ S ⊆ {2,3,…}` and `∫₀ʸ g ≥ 0` on `[0,1]`. -/
theorem kappaG_le_integral_qProd_mul {S : Finset ℕ} (hS : ∀ n ∈ S, 2 ≤ n) {b : ℕ}
    (hb : b ∈ S) {g : ℝ → ℝ} (hg : Continuous g)
    (hG0 : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ runInt g y) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    kappaG b (runInt g) c ≤ ∫ u in (0 : ℝ)..c, qProd S u * g u := by
  rw [integral_weight_mul_eq_ibp hg (fun x _ => hasDerivAt_qProd S x) (continuous_qProd' S)]
  have hbdry : 0 ≤ qProd S c * runInt g c :=
    mul_nonneg (qProd_nonneg S ⟨hc.1.le, hc.2⟩) (hG0 c ⟨hc.1.le, hc.2⟩)
  have htail : kappaG b (runInt g) c ≤ -∫ u in (0 : ℝ)..c, qProd' S u * runInt g u := by
    unfold kappaG
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on hc.1.le
    · exact (continuous_kappaG_integrand b (continuous_runInt hg)).intervalIntegrable 0 c
    · exact (((continuous_qProd' S).mul (continuous_runInt hg)).neg).intervalIntegrable 0 c
    · intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hc.2⟩
      have := mul_le_mul_of_nonneg_right (le_neg_qProd' hS hb hu') (hG0 u hu')
      linarith
  linarith

/-- Finite weights, nonnegative version: `∫₀ᶜ P_S g ≥ 0` when `∫₀ʸ g ≥ 0` on `[0,1]`. -/
theorem integral_qProd_mul_nonneg (S : Finset ℕ) {g : ℝ → ℝ} (hg : Continuous g)
    (hG0 : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ runInt g y) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    0 ≤ ∫ u in (0 : ℝ)..c, qProd S u * g u := by
  rw [integral_weight_mul_eq_ibp hg (fun x _ => hasDerivAt_qProd S x) (continuous_qProd' S)]
  have hbdry : 0 ≤ qProd S c * runInt g c := mul_nonneg (qProd_nonneg S hc) (hG0 c hc)
  have htail : (∫ u in (0 : ℝ)..c, qProd' S u * runInt g u) ≤ 0 := by
    have hle : (∫ u in (0 : ℝ)..c, qProd' S u * runInt g u) ≤ ∫ _ in (0 : ℝ)..c, (0 : ℝ) := by
      apply intervalIntegral.integral_mono_on hc.1
      · exact ((continuous_qProd' S).mul (continuous_runInt hg)).intervalIntegrable 0 c
      · exact _root_.intervalIntegrable_const
      · intro u hu
        have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hc.2⟩
        exact mul_nonpos_of_nonpos_of_nonneg (qProd'_nonpos S hu') (hG0 u hu')
    simpa using hle
  linarith

/-- **Weighted positivity, arbitrary `B ⊆ {2,3,…}`.** If `g` is continuous and
`∫₀ʸ g > 0` for every `y ∈ (0,1]`, then `∫₀ᶜ P_B(u) g(u) du > 0` for every `c ∈ (0,1]`. -/
theorem integral_qProdSet_mul_pos {B : Set ℕ} (hB : ∀ n ∈ B, 2 ≤ n) {g : ℝ → ℝ}
    (hg : Continuous g) (hG : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y, g u)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : 0 < ∫ u in (0 : ℝ)..c, qProdSet B u * g u := by
  classical
  have hG0 : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ runInt g y := fun y hy => runInt_nonneg hG hy
  rcases B.eq_empty_or_nonempty with hBe | ⟨b, hb⟩
  · subst hBe
    have hone : (∫ u in (0 : ℝ)..c, qProdSet ∅ u * g u) = ∫ u in (0 : ℝ)..c, g u := by
      apply intervalIntegral.integral_congr
      intro u _
      simp [qProdSet]
    rw [hone]
    exact hG c hc
  · have hb1 : 1 ≤ b := le_trans (by norm_num) (hB b hb)
    have hκ := kappaG_pos hb1 (continuous_runInt hg) hG0 (fun y hy => hG y hy) hc
    have hlim : kappaG b (runInt g) c ≤ ∫ u in (0 : ℝ)..c, qProdSet B u * g u := by
      refine ge_of_tendsto (tendsto_integral_qProd_truncation_mul B ⟨hc.1.le, hc.2⟩ hg) ?_
      filter_upwards [Filter.eventually_ge_atTop b] with N hN
      apply kappaG_le_integral_qProd_mul _ _ hg hG0 hc
      · intro n hn
        exact hB n (Finset.mem_filter.mp hn).2
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩
    linarith

/-- **Weighted nonnegativity, arbitrary `B`.** If `g` is continuous and `∫₀ʸ g ≥ 0` for
every `y ∈ [0,1]`, then `∫₀ᶜ P_B(u) g(u) du ≥ 0` for every `c ∈ [0,1]`. -/
theorem integral_qProdSet_mul_nonneg (B : Set ℕ) {g : ℝ → ℝ} (hg : Continuous g)
    (hG0 : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ ∫ u in (0 : ℝ)..y, g u)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) : 0 ≤ ∫ u in (0 : ℝ)..c, qProdSet B u * g u := by
  classical
  refine ge_of_tendsto (tendsto_integral_qProd_truncation_mul B hc hg)
    (Filter.Eventually.of_forall fun N => ?_)
  exact integral_qProd_mul_nonneg _ hg hG0 hc

/-! ## Power substitution with a real weight -/

section RealPowerSubstitution

variable {e : ℝ → ℝ}

/-- The weight `φ(u) = u^{k-p}/p`. -/
private noncomputable def rjac (k : ℝ) (p : ℕ) (u : ℝ) : ℝ := u ^ (k - p) / p

/-- `φ'(u) = (k-p)/p · u^{k-p-1}`. -/
private noncomputable def rjac' (k : ℝ) (p : ℕ) (u : ℝ) : ℝ := (k - p) / p * u ^ (k - p - 1)

private theorem hasDerivAt_rjac (k : ℝ) (p : ℕ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (rjac k p) (rjac' k p u) u := by
  unfold rjac rjac'
  have h := (Real.hasDerivAt_rpow_const (p := k - p) (Or.inl hu)).div_const (p : ℝ)
  convert h using 1
  ring

private theorem hasDerivAt_runInt_pow' (he : Continuous e) (p : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => runInt e (x ^ p)) (e (u ^ p) * ((p : ℝ) * u ^ (p - 1))) u := by
  have hout : HasDerivAt (runInt e) (e (u ^ p)) (u ^ p) := hasDerivAt_runInt he (u ^ p)
  have hin : HasDerivAt (fun x : ℝ => x ^ p) ((p : ℝ) * u ^ (p - 1)) u := by
    simpa using hasDerivAt_pow p u
  exact hout.comp u hin

/-- `u^{p-1} = u^{(p:ℝ)-1}` for `p ≥ 1`. -/
theorem pow_pred_eq_rpow {p : ℕ} (hp : 1 ≤ p) (u : ℝ) : u ^ (p - 1) = u ^ ((p : ℝ) - 1) := by
  rw [← Real.rpow_natCast u (p - 1)]
  congr 1
  push_cast [Nat.cast_sub hp]
  ring

/-- Cancellation `φ(u)·(e(uᵖ)·p·u^{p-1}) = u^{k-1} e(uᵖ)` for `u > 0`. -/
private theorem rjac_mul_cancel (k : ℝ) {p : ℕ} (hp : 1 ≤ p) (e : ℝ → ℝ)
    {u : ℝ} (hu : 0 < u) :
    rjac k p u * (e (u ^ p) * ((p : ℝ) * u ^ (p - 1))) = u ^ (k - 1) * e (u ^ p) := by
  unfold rjac
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := by positivity
  rw [pow_pred_eq_rpow hp]
  have hcomb : u ^ (k - p) * u ^ ((p : ℝ) - 1) = u ^ (k - 1) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  set A := u ^ (k - p)
  set B := u ^ ((p : ℝ) - 1)
  rw [← hcomb]
  field_simp

/-- **Boundary lower bound** for `1 ≤ k ≤ p`, `p ≥ 1`:
`φ(c)·∫₀^{cᵖ} e ≤ ∫₀ᶜ u^{k-1} e(uᵖ)`. -/
private theorem bdry_le_running_rpow (he : Continuous e)
    (hrun : ∀ d ∈ Ioc (0 : ℝ) 1, 0 < ∫ v in (0 : ℝ)..d, e v) {k : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hk1 : 1 ≤ k) (hkp : k ≤ p) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hc0 : 0 < c) :
    rjac k p c * runInt e (c ^ p) ≤ ∫ u in (0 : ℝ)..c, u ^ (k - 1) * e (u ^ p) := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  set g : ℝ → ℝ := fun u => u ^ (k - 1) * e (u ^ p) with hgdef
  have hgcont : Continuous g :=
    (Real.continuous_rpow_const (by linarith)).mul (he.comp (continuous_pow p))
  have hstep : ∀ ε : ℝ, 0 < ε → ε < c →
      rjac k p c * runInt e (c ^ p) - rjac k p ε * runInt e (ε ^ p)
        ≤ ∫ u in ε..c, g u := by
    intro ε hε hεc
    have hεc' : ε ≤ c := hεc.le
    have hmem : ∀ x ∈ Set.uIcc ε c, x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hεc'] at hx
      exact ne_of_gt (lt_of_lt_of_le hε hx.1)
    have hφderiv : ∀ x ∈ Set.uIcc ε c, HasDerivAt (rjac k p) (rjac' k p x) x :=
      fun x hx => hasDerivAt_rjac k p (hmem x hx)
    have hAderiv : ∀ x ∈ Set.uIcc ε c,
        HasDerivAt (fun x : ℝ => runInt e (x ^ p)) (e (x ^ p) * ((p : ℝ) * x ^ (p - 1))) x :=
      fun x _ => hasDerivAt_runInt_pow' he p x
    have hφ'cont : ContinuousOn (rjac' k p) (Set.uIcc ε c) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      left
      exact hmem x hx
    have hφ'int : IntervalIntegrable (rjac' k p) volume ε c := hφ'cont.intervalIntegrable
    have hA'int : IntervalIntegrable
        (fun x => e (x ^ p) * ((p : ℝ) * x ^ (p - 1))) volume ε c := by
      apply Continuous.intervalIntegrable
      exact (he.comp (continuous_pow p)).mul (continuous_const.mul (continuous_pow _))
    have hIBP :
        (∫ x in ε..c, rjac k p x * (e (x ^ p) * ((p : ℝ) * x ^ (p - 1))))
          = rjac k p c * runInt e (c ^ p) - rjac k p ε * runInt e (ε ^ p)
            - ∫ x in ε..c, rjac' k p x * runInt e (x ^ p) :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := rjac k p) (v := fun x : ℝ => runInt e (x ^ p)) (u' := rjac' k p)
        (v' := fun x => e (x ^ p) * ((p : ℝ) * x ^ (p - 1)))
        hφderiv hAderiv hφ'int hA'int
    have hlhs : (∫ x in ε..c, rjac k p x * (e (x ^ p) * ((p : ℝ) * x ^ (p - 1))))
        = ∫ x in ε..c, g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hεc'] at hx
      exact rjac_mul_cancel k hp e (lt_of_lt_of_le hε hx.1)
    have htail_nonpos : (∫ x in ε..c, rjac' k p x * runInt e (x ^ p)) ≤ 0 := by
      have hle : (∫ x in ε..c, rjac' k p x * runInt e (x ^ p)) ≤ ∫ _ in ε..c, (0 : ℝ) := by
        apply intervalIntegral.integral_mono_on hεc'
        · exact hφ'int.mul_continuousOn
            ((continuous_runInt he).comp (continuous_pow p)).continuousOn
        · exact _root_.intervalIntegrable_const
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
          have hxIcc : x ^ p ∈ Icc (0 : ℝ) 1 :=
            ⟨by positivity, pow_le_one₀ hx0.le (le_trans hx.2 hc.2)⟩
          have hAx : 0 ≤ runInt e (x ^ p) := runInt_nonneg hrun hxIcc
          have hφ'x : rjac' k p x ≤ 0 := by
            unfold rjac'
            have h1 : (k - p) / p ≤ 0 :=
              div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
            exact mul_nonpos_of_nonpos_of_nonneg h1 (Real.rpow_nonneg hx0.le _)
          exact mul_nonpos_of_nonpos_of_nonneg hφ'x hAx
      simpa using hle
    rw [hlhs] at hIBP
    linarith [hIBP, htail_nonpos]
  -- `φ(ε)·A(ε) → 0` as `ε ↓ 0`.
  obtain ⟨M, hM0, hMbound⟩ := abs_runInt_le he
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |rjac k p ε * runInt e (ε ^ p)| ≤ (M / p) * ε := by
    intro ε hε hε1
    have hεp_mem : ε ^ p ∈ Icc (0 : ℝ) 1 := ⟨by positivity, pow_le_one₀ hε.le hε1⟩
    have hAbound : |runInt e (ε ^ p)| ≤ M * ε ^ p := hMbound _ hεp_mem
    have hφnn : 0 ≤ ε ^ (k - p) / p := by
      have : 0 ≤ ε ^ (k - p) := Real.rpow_nonneg hε.le _
      positivity
    unfold rjac
    rw [abs_mul, abs_of_nonneg hφnn]
    have hεpR : (ε : ℝ) ^ p = ε ^ (p : ℝ) := (Real.rpow_natCast ε p).symm
    have hmul : ε ^ (k - p) * ε ^ (p : ℝ) = ε ^ k := by
      rw [← Real.rpow_add hε]; ring_nf
    have hεk : ε ^ k ≤ ε := by
      calc ε ^ k ≤ ε ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hk1
        _ = ε := Real.rpow_one ε
    have hpne : (0 : ℝ) < p := by linarith
    calc ε ^ (k - p) / p * |runInt e (ε ^ p)|
        ≤ ε ^ (k - p) / p * (M * ε ^ p) := mul_le_mul_of_nonneg_left hAbound hφnn
      _ = (M / p) * (ε ^ (k - p) * ε ^ (p : ℝ)) := by rw [hεpR]; ring
      _ = (M / p) * ε ^ k := by rw [hmul]
      _ ≤ (M / p) * ε := mul_le_mul_of_nonneg_left hεk (by positivity)
  change rjac k p c * runInt e (c ^ p) ≤ ∫ u in (0 : ℝ)..c, g u
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hgcont.intervalIntegrable a b
  have hprim0 : Filter.Tendsto (fun ε : ℝ => ∫ u in (0 : ℝ)..ε, g u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hcontprim : ContinuousAt (fun ε : ℝ => ∫ u in (0 : ℝ)..ε, g u) 0 :=
      (intervalIntegral.integral_hasDerivAt_right (hgint 0 0)
        (hgcont.stronglyMeasurableAtFilter _ _) hgcont.continuousAt).continuousAt
    have : Filter.Tendsto (fun ε : ℝ => ∫ u in (0 : ℝ)..ε, g u)
        (nhds 0) (nhds (∫ u in (0 : ℝ)..(0 : ℝ), g u)) := hcontprim.tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hφA_tendsto : Filter.Tendsto (fun ε : ℝ => rjac k p ε * runInt e (ε ^ p))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro δ hδ
    have hpne : (0 : ℝ) < p := by linarith
    refine ⟨min 1 (δ / (M / p + 1)), by positivity, ?_⟩
    intro ε hεIoi hεlt
    have hε : 0 < ε := hεIoi
    have hεlt' : ε < min 1 (δ / (M / p + 1)) := by
      rwa [Real.dist_eq, sub_zero, abs_of_pos hε] at hεlt
    have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hεlt' (min_le_left _ _))
    have hb := hbound ε hε hε1
    rw [Real.dist_eq, sub_zero]
    have hεlt2 : ε < δ / (M / p + 1) := lt_of_lt_of_le hεlt' (min_le_right _ _)
    have hMp1 : 0 < M / p + 1 := by positivity
    calc |rjac k p ε * runInt e (ε ^ p)| ≤ (M / p) * ε := hb
      _ ≤ (M / p + 1) * ε := by nlinarith [hε.le]
      _ < (M / p + 1) * (δ / (M / p + 1)) := mul_lt_mul_of_pos_left hεlt2 hMp1
      _ = δ := by field_simp
  have hlimit : Filter.Tendsto
      (fun ε : ℝ => rjac k p c * runInt e (c ^ p)
        - rjac k p ε * runInt e (ε ^ p) + ∫ u in (0 : ℝ)..ε, g u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (rjac k p c * runInt e (c ^ p))) := by
    have := ((tendsto_const_nhds (x := rjac k p c * runInt e (c ^ p))).sub
      hφA_tendsto).add hprim0
    simpa using this
  have hev : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      rjac k p c * runInt e (c ^ p) - rjac k p ε * runInt e (ε ^ p)
        + ∫ u in (0 : ℝ)..ε, g u ≤ ∫ u in (0 : ℝ)..c, g u := by
    have hIoo : Set.Ioo (0 : ℝ) c ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT hc0
    filter_upwards [hIoo] with ε hε
    have hsplit : (∫ u in (0 : ℝ)..c, g u) = (∫ u in (0 : ℝ)..ε, g u) + ∫ u in ε..c, g u :=
      (intervalIntegral.integral_add_adjacent_intervals (hgint 0 ε) (hgint ε c)).symm
    have hs := hstep ε hε.1 hε.2
    rw [hsplit]
    linarith [hs]
  exact le_of_tendsto hlimit hev

/-- **Power substitution with a real weight.** If `e` is continuous with `∫₀ᵈ e > 0` for
all `d ∈ (0,1]`, then `∫₀ᶜ u^{k-1} e(uᵖ) du > 0` for `c ∈ (0,1]`, integer `p ≥ 1` and real
`1 ≤ k ≤ p`. -/
theorem running_pos_rpow_comp_pow (he : Continuous e)
    (hrun : ∀ d ∈ Ioc (0 : ℝ) 1, 0 < ∫ v in (0 : ℝ)..d, e v) {p : ℕ} (hp : 1 ≤ p)
    {k : ℝ} (hk1 : 1 ≤ k) (hkp : k ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..c, u ^ (k - 1) * e (u ^ p) := by
  refine lt_of_lt_of_le ?_ (bdry_le_running_rpow he hrun hp hk1 hkp ⟨hc.1.le, hc.2⟩ hc.1)
  have hcp_mem : c ^ p ∈ Ioc (0 : ℝ) 1 := ⟨by have := hc.1; positivity, pow_le_one₀ hc.1.le hc.2⟩
  have hAc_pos : 0 < runInt e (c ^ p) := hrun _ hcp_mem
  have hφc_pos : 0 < rjac k p c := by
    unfold rjac
    have : 0 < c ^ (k - p) := Real.rpow_pos_of_pos hc.1 _
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  exact mul_pos hφc_pos hAc_pos

end RealPowerSubstitution

/-! ## The substitution `v = uᵖ` -/

/-- `(uᵖ)^{k/p-1} · u^{p-1} = u^{k-1}` for `u > 0`, `p ≥ 1`. -/
theorem rpow_comp_pow_mul_pow_pred {p : ℕ} (hp : 1 ≤ p) (k : ℝ) {u : ℝ} (hu : 0 < u) :
    (u ^ p) ^ (k / p - 1) * u ^ (p - 1) = u ^ (k - 1) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpR : (p : ℝ) ≠ 0 := by positivity
  rw [pow_pred_eq_rpow hp, ← Real.rpow_natCast u p, ← Real.rpow_mul hu.le,
    ← Real.rpow_add hu]
  congr 1
  field_simp
  ring

/-- **Substitution `v = uᵖ`.** For `f` continuous on `[0,1]`, `p ≥ 1`, real `k ≥ p` and
`y ∈ [0,1]`: `∫₀ʸ u^{k-1} f(uᵖ) du = (1/p)·∫₀^{yᵖ} v^{k/p-1} f(v) dv`. -/
theorem integral_rpow_mul_comp_pow {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) {p : ℕ}
    (hp : 1 ≤ p) {k : ℝ} (hkp : (p : ℝ) ≤ k) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    (∫ u in (0 : ℝ)..y, u ^ (k - 1) * f (u ^ p))
      = (1 / p) * ∫ v in (0 : ℝ)..y ^ p, v ^ (k / p - 1) * f v := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : 0 ≤ k / p - 1 := by
    rw [sub_nonneg, le_div_iff₀ hpR]; linarith
  -- the outer function on `[0,1]`
  set F : ℝ → ℝ := fun v => v ^ (k / p - 1) * f v with hF
  have hFc : ContinuousOn F (Icc 0 1) :=
    ((Real.continuous_rpow_const hs).continuousOn).mul hf
  have himg : (fun u : ℝ => u ^ p) '' uIcc 0 y ⊆ Icc 0 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [uIcc_of_le hy.1] at hu
    exact ⟨pow_nonneg hu.1 p, pow_le_one₀ hu.1 (hu.2.trans hy.2)⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := y)
    (f := fun u : ℝ => u ^ p) (f' := fun u => (p : ℝ) * u ^ (p - 1)) (g := F)
    (fun x _ => by simpa using hasDerivAt_pow p x)
    ((continuous_const.mul (continuous_pow _)).continuousOn) (hFc.mono himg)
  simp only [Function.comp, zero_pow (by omega : p ≠ 0)] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := Measure.ae_ne volume 0
  filter_upwards [hne] with u hu0 hu
  rw [uIoc_of_le hy.1] at hu
  have hu' : 0 < u := hu.1
  rw [hF]
  have hcancel := rpow_comp_pow_mul_pow_pred hp k hu'
  have hpne : (p : ℝ) ≠ 0 := hpR.ne'
  show u ^ (k - 1) * f (u ^ p) = 1 / p * ((u ^ p) ^ (k / p - 1) * f (u ^ p) * (p * u ^ (p - 1)))
  rw [← hcancel]
  set A := (u ^ p) ^ (k / p - 1)
  set B := u ^ (p - 1)
  field_simp

end RntPaper
