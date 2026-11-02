import RntPaper.K9Tight
import RntPaper.MomentsReal

/-!
# From the case checks to the analytic certificates of the `k₉` descent

Assuming the Boolean checks (proved by computation in `K9All`), every block and every set that
can occur in the descent satisfies its running-integral condition:

* `single_cert`: for `11 ≤ p ≤ 59` and every primitive set `T` of `p`-smooth numbers there is a
  finite set `Q` of primes in `(p, p·t]` (`t ∈ T`) with
  `RunPos (u ↦ ∏_{q∈Q}(1-u^q) E_T(u^p)) 126` (condition (3.2) of the notes);
* `merged_cert`: for every primitive set `S` of `7`-smooth numbers covering `2,3,5,7`,
  `S ≠ {2,3,5,7}`, there is a finite set `Q` of primes `11 ≤ q ≤ s` (`s ∈ S`) such that the
  running integrals of `u^{k-1} ∏_{q∈Q}(1-u^q)(P_S - P_{2,3,5,7})` are `≥ 0` for `1 ≤ k ≤ k₉`
  and `> 0` for `k < k₉` (condition (3.3));
* `small_cert`: the case `N ≤ 6`.
-/

namespace RntPaper.K9

open MeasureTheory intervalIntegral Set CP QProduct

/-! ## Transfer lemmas -/

theorem intervalIntegrable_rpow_mul_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1))
    {k : ℝ} (hk : 1 ≤ k) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => u ^ (k - 1) * g u) volume 0 y := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hy.1]
  exact ((Real.continuous_rpow_const (by linarith)).continuousOn).mul
    (hg.mono (Icc_subset_Icc le_rfl hy.2))

theorem runPos_mono {g g' : ℝ → ℝ} {K : ℝ} (hg : RunPos g K) (hc : Continuous g)
    (hc' : ContinuousOn g' (Icc 0 1)) (hle : ∀ u ∈ Ico (0 : ℝ) 1, g u ≤ g' u) : RunPos g' K := by
  intro k hk hkK y hy
  refine lt_of_lt_of_le (hg k hk hkK y hy) ?_
  apply intervalIntegral.integral_mono_ae_restrict hy.1.le
    ((continuous_rpow_mul hc hk).intervalIntegrable 0 y)
    (intervalIntegrable_rpow_mul_of_continuousOn hc' hk ⟨hy.1.le, hy.2⟩)
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with u hu hu1
  exact mul_le_mul_of_nonneg_left (hle u ⟨hu.1, lt_of_le_of_ne (hu.2.trans hy.2) hu1⟩)
    (Real.rpow_nonneg hu.1 _)

theorem runPos_congr {g g' : ℝ → ℝ} {K : ℝ} (hg : RunPos g K)
    (heq : ∀ u ∈ Ico (0 : ℝ) 1, g u = g' u) : RunPos g' K := by
  intro k hk hkK y hy
  rw [← show (∫ u in (0 : ℝ)..y, u ^ (k - 1) * g u) = ∫ u in (0 : ℝ)..y, u ^ (k - 1) * g' u from ?_]
  · exact hg k hk hkK y hy
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with u hu1 hu
  rw [uIoc_of_le hy.1.le] at hu
  rw [heq u ⟨hu.1.le, lt_of_le_of_ne (hu.2.trans hy.2) hu1⟩]

/-- `∏_{n ≥ B}(1 - xⁿ) ≥ 1 - x^B/(1-x)` on `[0,1)`. -/
theorem qProdSet_tail_ge' (B : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    1 - x ^ B / (1 - x) ≤ qProdSet {n | B ≤ n} x := by
  classical
  refine ge_of_tendsto (qProdSet_eq_lim _ h0 h1) (Filter.Eventually.of_forall fun N => ?_)
  set F := (Finset.range (N + 1)).filter (· ∈ {n : ℕ | B ≤ n})
  have hW := one_sub_prod_one_sub_le_sum F (fun n => x ^ n) (fun _ _ => pow_nonneg h0 _)
    (fun _ _ => pow_le_one₀ h0 h1.le)
  have hsub : F ⊆ Finset.Ico B (N + 1) := by
    intro n hn
    simp only [F, Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    exact Finset.mem_Ico.mpr ⟨hn.2, hn.1⟩
  have hS : ∑ n ∈ F, x ^ n ≤ x ^ B / (1 - x) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg h0 _).trans
      (geom_sum_Ico_le_of_lt_one h0 h1)
  unfold qProd
  linarith

/-- **Envelope bound.** If `T ⊆ M ∪ [B, ∞)` with `M` a duplicate-free list below `B`, then
`P_T(x) ≥ ∏_{m∈M}(1-x^m) (1 - x^B/(1-x))` on `[0,1)`. -/
theorem envelope_ge {T : Set ℕ} {M : List ℕ} {B : ℕ} (hnd : M.Nodup) (hMB : ∀ m ∈ M, m < B)
    (hT : T ⊆ (M.toFinset : Set ℕ) ∪ {n | B ≤ n}) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    (M.map fun m => 1 - x ^ m).prod * (1 - x ^ B / (1 - x)) ≤ qProdSet T x := by
  have hdisj : Disjoint (M.toFinset : Set ℕ) {n | B ≤ n} := by
    rw [Set.disjoint_left]
    intro n hn h
    simp only [Finset.mem_coe, List.mem_toFinset] at hn
    have := hMB n hn
    simp only [Set.mem_ofPred_eq] at h
    omega
  calc (M.map fun m => 1 - x ^ m).prod * (1 - x ^ B / (1 - x))
      ≤ qProd M.toFinset x * qProdSet {n | B ≤ n} x := by
        rw [qProd_toFinset hnd, ev_prodOneSub]
        exact mul_le_mul_of_nonneg_left (qProdSet_tail_ge' B h0 h1)
          (prod_one_sub_pow_nonneg M h0 h1.le)
    _ = qProdSet ((M.toFinset : Set ℕ) ∪ {n | B ≤ n}) x := by
        rw [qProdSet_union hdisj h0 h1, qProdSet_coe]
    _ ≤ qProdSet T x := qProdSet_antitone hT h0 h1

theorem ev_one_sub_lin (v : ℝ) : ev [1, -1] v = 1 - v := by simp; ring

theorem ev_prodOneSub_primes_pos {lo hi : ℕ} (hlo : 1 ≤ lo) :
    (∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ ev (prodOneSub (primesIn lo hi)) u) ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, 0 < ev (prodOneSub (primesIn lo hi)) u :=
  ⟨fun u hu => ev_prodOneSub_nonneg _ hu,
   fun u hu => ev_prodOneSub_pos (fun n hn => by have := (mem_primesIn.mp hn).2.1; omega) hu⟩

theorem finite_of_bounded {S : Set ℕ} {m : ℕ} (h : ∀ s ∈ S, s < m) :
    ∃ Sf : Finset ℕ, (Sf : Set ℕ) = S := by
  classical
  refine ⟨(Finset.range m).filter (· ∈ S), ?_⟩
  ext s
  simp only [Finset.coe_filter, Finset.mem_range]
  constructor
  · intro hs; exact hs.2
  · intro hs; exact ⟨h s hs, hs⟩

theorem isAC_of_primitive {S : Finset ℕ} (h : IsPrimitive (S : Set ℕ)) : IsAC S :=
  fun a ha b hb hab => h.2 a ha b hb hab

/-! ## Single-prime compressions -/

/-- All explicit blocks pass. -/
def SingleOKAll (p m : ℕ) : Prop := ∀ l ∈ antichains (Xs p 2 m) [], singleOK p m l = true

/-- All tail envelopes pass. -/
def SingleTailOKAll (p m B : ℕ) : Prop :=
  ∀ l ∈ antichains (Xs p 2 B) [], singleTailOK p m B l = true

theorem single_cert {p m B : ℕ} (hp : p.Prime) (hE : SingleOKAll p m)
    (hTl : SingleTailOKAll p m B) {T : Set ℕ} (hTp : IsPrimitive T)
    (hsm : ∀ t ∈ T, ∀ q, q.Prime → q ∣ t → q ≤ p) (hne : T.Nonempty) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ p < q ∧ ∃ t ∈ T, q ≤ p * t) ∧
      RunPos (fun u => qProd Q u * ESetExt T (u ^ p)) 126 := by
  classical
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hT1 : ∀ n ∈ T, 1 ≤ n := fun n hn => le_trans (by norm_num) (hTp.1 n hn)
  have hgc : ∀ Q : Finset ℕ, Continuous fun u => qProd Q u * ESetExt T (u ^ p) := fun Q =>
    (by unfold qProd; fun_prop : Continuous (qProd Q)).mul
      ((continuous_ESetExt hT1).comp (continuous_pow p))
  have hsmB : ∀ t ∈ T, smoothB p t = true := fun t ht =>
    (smoothB_iff (by have := hTp.1 t ht; omega)).mpr (hsm t ht)
  by_cases hsmall : ∀ t ∈ T, t < m
  · -- explicit block
    obtain ⟨Tf, hTf⟩ := finite_of_bounded hsmall
    subst hTf
    have hTfne : Tf.Nonempty := by simpa using hne
    set mx := Tf.max' hTfne
    set X' := (Xs p 2 m).toFinset.filter (· ≤ mx)
    have hsub : Tf ⊆ X' := fun t ht => by
      simp only [X', Finset.mem_filter, List.mem_toFinset, mem_Xs]
      exact ⟨⟨hsmall t ht, hTp.1 t ht, hsmB t ht⟩, Tf.le_max' t ht⟩
    obtain ⟨S', hTS, hSX, hSac, hSmax⟩ := exists_maximal_ext' hsub (isAC_of_primitive hTp)
    obtain ⟨l, hl, hlS, hlnd⟩ := mem_antichains (Xs_pairwise p 2 m) (Xs_pos (by norm_num))
      (S := S') (fun s hs => by
        have := hSX hs; simp only [X', Finset.mem_filter, List.mem_toFinset] at this
        exact this.1) hSac
    have hmxT : mx ∈ Tf := Tf.max'_mem hTfne
    have hlne : l ≠ [] := by
      intro h; rw [h] at hlS; simp at hlS; rw [← hlS] at hTS; exact absurd (hTS hmxT) (by simp)
    have hlmax : lmax l = mx := by
      apply le_antisymm
      · have := hSX (hlS ▸ List.mem_toFinset.mpr (lmax_mem hlne))
        simp only [X', Finset.mem_filter] at this; exact this.2
      · exact lmax_ge (List.mem_toFinset.mp (hlS ▸ hTS hmxT))
    have hok := hE l hl
    have hmaxb : isMaxBelow (Xs p 2 m) l = true := by
      rw [isMaxBelow_iff]
      intro x hx hxl
      have hxX : x ∈ X' := by
        simp only [X', Finset.mem_filter, List.mem_toFinset]; exact ⟨hx, hlmax ▸ hxl⟩
      by_cases hxS : x ∈ S'
      · exact Or.inl (List.mem_toFinset.mp (hlS ▸ hxS))
      · obtain ⟨s, hs, hsx⟩ := hSmax x hxX hxS
        exact Or.inr ⟨s, List.mem_toFinset.mp (hlS ▸ hs), hsx⟩
    simp only [singleOK, hmaxb, Bool.and_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_not, List.any_eq_true] at hok
    rcases hok with hok | ⟨cap, _, hcap⟩
    · exact absurd hok hlne
    set Ql := primesIn (p + 1) (min (p * lmax l) cap)
    obtain ⟨hW0, hW⟩ := ev_prodOneSub_primes_pos (lo := p + 1) (hi := min (p * lmax l) cap)
      (by omega)
    have hrun := scCheckZ_sound hp1 (by norm_num : (0 : ℚ) < 126) hW0 hW hcap
    refine ⟨Ql.toFinset, fun q hq => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := mem_primesIn.mp (List.mem_toFinset.mp hq)
      refine ⟨h3, by omega, mx, hmxT, ?_⟩
      rw [← hlmax]; exact h1.trans (min_le_left _ _)
    · have hrun' : RunPos (fun u => ev (prodOneSub Ql) u * ev (singleD l) (u ^ p)) 126 := by
        simpa using hrun
      refine runPos_mono hrun' ((continuous_ev _).mul ((continuous_ev _).comp (continuous_pow p)))
        (hgc _).continuousOn fun u hu => ?_
      rw [qProd_toFinset (primesIn_nodup _ _)]
      apply mul_le_mul_of_nonneg_left _ (ev_prodOneSub_nonneg _ ⟨hu.1, hu.2.le⟩)
      have hv : u ^ p ∈ Icc (0 : ℝ) 1 := ⟨pow_nonneg hu.1 _, pow_le_one₀ hu.1 hu.2.le⟩
      have hv1 : u ^ p < 1 := pow_lt_one₀ hu.1 hu.2 (by omega)
      rw [ESetExt_of_mem _ hv, blockESet, singleD, ev_sub, ev_one_sub_lin,
        ← qProd_toFinset hlnd, hlS, ← qProdSet_coe]
      have := qProdSet_antitone (S := (Tf : Set ℕ)) (T := (S' : Set ℕ))
        (by exact_mod_cast hTS) hv.1 hv1
      linarith
  · -- tail: an element `t₀ ≥ m`
    push Not at hsmall
    obtain ⟨t0, ht0, hmt0⟩ := hsmall
    obtain ⟨T0, hT0⟩ := finite_of_bounded (S := {t ∈ T | t < B}) (m := B) fun t ht => ht.2
    have hsub : T0 ⊆ (Xs p 2 B).toFinset := fun t ht => by
      have ht' : t ∈ ({t ∈ T | t < B} : Set ℕ) := by rw [← hT0]; exact_mod_cast ht
      simp only [List.mem_toFinset, mem_Xs]
      exact ⟨ht'.2, hTp.1 t ht'.1, hsmB t ht'.1⟩
    have hT0ac : IsAC T0 := fun a ha b hb hab => by
      have ha' : a ∈ ({t ∈ T | t < B} : Set ℕ) := by rw [← hT0]; exact_mod_cast ha
      have hb' : b ∈ ({t ∈ T | t < B} : Set ℕ) := by rw [← hT0]; exact_mod_cast hb
      exact hTp.2 a ha'.1 b hb'.1 hab
    obtain ⟨M, hTM, hMX, hMac, hMmax⟩ := exists_maximal_ext' hsub hT0ac
    obtain ⟨l, hl, hlM, hlnd⟩ := mem_antichains (Xs_pairwise p 2 B) (Xs_pos (by norm_num))
      (S := M) (fun s hs => List.mem_toFinset.mp (hMX hs)) hMac
    have hmaxin : isMaxIn (Xs p 2 B) l = true := by
      rw [isMaxIn_iff]
      intro x hx
      by_cases hxM : x ∈ M
      · exact Or.inl (List.mem_toFinset.mp (hlM ▸ hxM))
      · obtain ⟨s, hs, hsx⟩ := hMmax x (List.mem_toFinset.mpr hx) hxM
        exact Or.inr ⟨s, List.mem_toFinset.mp (hlM ▸ hs), hsx⟩
    have hok := hTl l hl
    simp only [singleTailOK, hmaxin, Bool.not_true, Bool.false_or] at hok
    cases hlk : singleTailTbl.lookup (p, l) with
    | none => rw [hlk] at hok; simp at hok
    | some prm =>
      obtain ⟨cap, u1, u0⟩ := prm
      rw [hlk] at hok
      simp only [singleTailCert] at hok
      set Ql := primesIn (p + 1) (min (p * m) cap)
      obtain ⟨hW0, hW⟩ := ev_prodOneSub_primes_pos (lo := p + 1) (hi := min (p * m) cap) (by omega)
      set E : ℝ → ℝ := fun u => qProdSet T (clampI (u ^ p))
      have hEc : Continuous E :=
        (qProdSet_continuousOn_Icc hT1).comp_continuous (continuous_clampI.comp (continuous_pow p))
          (fun u => clampI_mem _)
      have hlB : ∀ x ∈ l, x < B := fun x hx => (mem_Xs.mp (List.mem_toFinset.mp
        (hMX (hlM ▸ List.mem_toFinset.mpr hx)))).1
      have hrun := v1Check_sound hp1 (by norm_num) hW0 hW hok hEc
        (fun u hu => qProdSet_nonneg T (clampI_mem _))
        (fun u hu => by
          have hv : u ^ p ∈ Icc (0 : ℝ) 1 := ⟨pow_nonneg hu.1 _, pow_le_one₀ hu.1 hu.2.le⟩
          simp only [E, clampI_of_mem hv]
          refine envelope_ge hlnd hlB (fun t ht => ?_) hv.1 (pow_lt_one₀ hu.1 hu.2 (by omega))
          by_cases htB : t < B
          · left
            have : t ∈ T0 := by
              have h' : t ∈ ({t ∈ T | t < B} : Set ℕ) := ⟨ht, htB⟩
              rw [← hT0] at h'; exact_mod_cast h'
            simp only [Finset.mem_coe, List.mem_toFinset]
            exact List.mem_toFinset.mp (hlM ▸ hTM this)
          · right; simp only [Set.mem_ofPred_eq]; omega)
      refine ⟨Ql.toFinset, fun q hq => ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := mem_primesIn.mp (List.mem_toFinset.mp hq)
        refine ⟨h3, by omega, t0, ht0, ?_⟩
        exact h1.trans ((min_le_left _ _).trans (Nat.mul_le_mul_left p hmt0))
      · refine runPos_congr hrun fun u hu => ?_
        have hv : u ^ p ∈ Icc (0 : ℝ) 1 := ⟨pow_nonneg hu.1 _, pow_le_one₀ hu.1 hu.2.le⟩
        simp only [E, ESetExt, clampI_of_mem hv, qProd_toFinset (primesIn_nodup _ _), ev_prodOneSub,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Ql]

/-! ## The merged comparison of the `7`-smooth part -/

def MergedOKAll : Prop := ∀ l ∈ antichains X7 [], mergedOK l = true

def MergedTailOKAll (Rp : List ℕ) : Prop :=
  ∀ l ∈ antichains (compositesR Rp 4 24) [], mergedTailOK Rp l = true

theorem R4f_eq : (R4f : Set ℕ) = {2, 3, 5, 7} := by ext; simp [R4f]

theorem rp_mem_RpList : ∀ L ∈ R4.sublists, L ≠ [] → L ∈ RpList := by decide

/-- A `7`-smooth number not in `{2,3,5,7}` that is `≥ 2` is composite, hence `≥ 4`. -/
theorem seven_smooth_cases {s : ℕ} (hs2 : 2 ≤ s) (hsm : ∀ q, q.Prime → q ∣ s → q ≤ 7) :
    s ∈ R4 ∨ ¬ s.Prime := by
  by_cases hp : s.Prime
  · left
    have := hsm s hp dvd_rfl
    interval_cases s <;> simp_all [R4] <;> norm_num at hp
  · right; exact hp

theorem merged_cert (hE : MergedOKAll) (hT : ∀ Rp ∈ RpList, MergedTailOKAll Rp)
    {S : Set ℕ} (hSp : IsPrimitive S) (hsm : ∀ s ∈ S, ∀ q, q.Prime → q ∣ s → q ≤ 7)
    (hcov : ∀ r ∈ R4, ∃ s ∈ S, r ∣ s) (hne : S ≠ (R4f : Set ℕ)) :
    ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ 11 ≤ q ∧ ∃ s ∈ S, q ≤ s) ∧
      ∀ k : ℝ, 1 ≤ k → k ≤ k9 → ∀ y ∈ Ioc (0 : ℝ) 1,
        0 ≤ ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd Q u * (qProdSet S u - qProd R4f u)) ∧
        (k < k9 → 0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd Q u * (qProdSet S u - qProd R4f u))) := by
  classical
  have hS1 : ∀ n ∈ S, 1 ≤ n := fun n hn => le_trans (by norm_num) (hSp.1 n hn)
  have hgc : ∀ Q : Finset ℕ, ContinuousOn (fun u => qProd Q u * (qProdSet S u - qProd R4f u))
      (Icc 0 1) := fun Q =>
    (by unfold qProd; fun_prop : Continuous (qProd Q)).continuousOn.mul
      ((qProdSet_continuousOn_Icc hS1).sub
        (by unfold qProd; fun_prop : Continuous (qProd R4f)).continuousOn)
  -- from `RunPos … 126` to the two clauses
  have fromRun : ∀ Q : Finset ℕ,
      RunPos (fun u => qProd Q u * (qProdSet S u - qProd R4f u)) 126 →
      ∀ k : ℝ, 1 ≤ k → k ≤ k9 → ∀ y ∈ Ioc (0 : ℝ) 1,
        0 ≤ ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd Q u * (qProdSet S u - qProd R4f u)) ∧
        (k < k9 → 0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd Q u * (qProdSet S u - qProd R4f u))) := by
    intro Q h k hk hkk y hy
    have := h k hk (hkk.trans k9_lt_126.le) y hy
    exact ⟨this.le, fun _ => this⟩
  have hsmB : ∀ s ∈ S, smoothB 7 s = true := fun s hs =>
    (smoothB_iff (by have := hSp.1 s hs; omega)).mpr (hsm s hs)
  by_cases hsmall : ∀ s ∈ S, s < 64
  · -- explicit
    obtain ⟨Sf, hSf⟩ := finite_of_bounded hsmall
    subst hSf
    have hSfne : Sf.Nonempty := by
      obtain ⟨s, hs, _⟩ := hcov 2 (by simp [R4]); exact ⟨s, hs⟩
    set mx := Sf.max' hSfne
    set X' := X7.toFinset.filter (· ≤ mx)
    have hsub : Sf ⊆ X' := fun t ht => by
      simp only [X', Finset.mem_filter, List.mem_toFinset, X7, mem_Xs]
      exact ⟨⟨hsmall t ht, hSp.1 t ht, hsmB t ht⟩, Sf.le_max' t ht⟩
    obtain ⟨S', hSS, hSX, hSac, hSmax⟩ := exists_maximal_ext' hsub (isAC_of_primitive hSp)
    obtain ⟨l, hl, hlS, hlnd⟩ := mem_antichains (Xs_pairwise 7 2 64) (Xs_pos (by norm_num))
      (S := S') (fun s hs => by
        have := hSX hs; simp only [X', Finset.mem_filter, List.mem_toFinset] at this
        exact this.1) hSac
    have hmxS : mx ∈ Sf := Sf.max'_mem hSfne
    have hlne : l ≠ [] := by
      intro h; rw [h] at hlS; simp at hlS; rw [← hlS] at hSS; exact absurd (hSS hmxS) (by simp)
    have hlmax : lmax l = mx := by
      apply le_antisymm
      · have := hSX (hlS ▸ List.mem_toFinset.mpr (lmax_mem hlne))
        simp only [X', Finset.mem_filter] at this; exact this.2
      · exact lmax_ge (List.mem_toFinset.mp (hlS ▸ hSS hmxS))
    have hmaxb : isMaxBelow X7 l = true := by
      rw [isMaxBelow_iff]
      intro x hx hxl
      have hxX : x ∈ X' := by
        simp only [X', Finset.mem_filter, List.mem_toFinset]; exact ⟨hx, hlmax ▸ hxl⟩
      by_cases hxS : x ∈ S'
      · exact Or.inl (List.mem_toFinset.mp (hlS ▸ hxS))
      · obtain ⟨s, hs, hsx⟩ := hSmax x hxX hxS
        exact Or.inr ⟨s, List.mem_toFinset.mp (hlS ▸ hs), hsx⟩
    have hcovl : covers l = true := by
      rw [covers_iff]
      intro r hr
      obtain ⟨s, hs, hrs⟩ := hcov r hr
      exact ⟨s, List.mem_toFinset.mp (hlS ▸ hSS hs), hrs⟩
    have hok := hE l hl
    simp only [mergedOK, hmaxb, hcovl, Bool.and_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_not, beq_iff_eq] at hok
    rcases hok with ((hok | hok) | hok) | hok
    · exact absurd hok hlne
    · -- `l = R4`: impossible
      exfalso
      apply hne
      have hS'R : S' = R4f := by rw [← hlS, hok]; rfl
      apply Set.Subset.antisymm
      · intro s hs; have := hSS hs; rw [hS'R] at this; exact_mod_cast this
      · intro r hr
        have hr' : r ∈ R4 := by simpa [R4f, R4] using hr
        obtain ⟨s, hs, hrs⟩ := hcov r hr'
        have hsR : s ∈ R4f := hS'R ▸ hSS hs
        have : r = s := by
          simp only [R4f, Finset.mem_insert, Finset.mem_singleton] at hsR
          simp only [R4, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl | rfl | rfl <;> rcases hsR with rfl | rfl | rfl | rfl <;>
            first | rfl | (exfalso; revert hrs; decide)
        rw [this]; exact_mod_cast hs
    · -- `l = A₉`: compare with `A₉` (no weight needed)
      have hS'A : S' = A9f := by rw [← hlS, hok]; rfl
      refine ⟨∅, fun q hq => absurd hq (Finset.notMem_empty q), fun k hk hkk y hy => ?_⟩
      have hA := runA9 hk hkk hy
      have hmono : (∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd A9f u - qProd R4f u))
          ≤ ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd ∅ u * (qProdSet (Sf : Set ℕ) u - qProd R4f u)) := by
        apply intervalIntegral.integral_mono_ae_restrict hy.1.le
          ((continuous_rpow_mul gA9_cont hk).intervalIntegrable 0 y)
          (intervalIntegrable_rpow_mul_of_continuousOn (hgc ∅) hk ⟨hy.1.le, hy.2⟩)
        filter_upwards [ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with u hu hu1
        have hu1' : u < 1 := lt_of_le_of_ne (hu.2.trans hy.2) hu1
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.1 _)
        have : qProd A9f u ≤ qProdSet (Sf : Set ℕ) u := by
          rw [← qProdSet_coe]
          exact qProdSet_antitone (by rw [← hS'A]; exact_mod_cast hSS) hu.1 hu1'
        simp only [qProd, Finset.prod_empty, one_mul]
        unfold qProd at this
        linarith
      exact ⟨hA.1.trans hmono, fun hlt => (hA.2 hlt).trans_le hmono⟩
    · -- the SC certificate at `126`
      obtain ⟨hW0, hW⟩ := ev_prodOneSub_primes_pos (lo := 11) (hi := lmax l) (by norm_num)
      have hrun := scCheckZ_sound (le_refl 1) (by norm_num : (0 : ℚ) < 126) hW0 hW hok
      set Ql := primesIn 11 (lmax l)
      refine ⟨Ql.toFinset, fun q hq => ?_, fromRun _ ?_⟩
      · obtain ⟨h1, h2, h3⟩ := mem_primesIn.mp (List.mem_toFinset.mp hq)
        exact ⟨h3, h2, mx, hmxS, hlmax ▸ h1⟩
      · have hrun' : RunPos (fun u => ev (prodOneSub Ql) u * ev (mergedD l) u) 126 := by
          simpa using hrun
        refine runPos_mono hrun' ((continuous_ev _).mul (continuous_ev _)) (hgc _) fun u hu => ?_
        rw [qProd_toFinset (primesIn_nodup _ _)]
        apply mul_le_mul_of_nonneg_left _ (ev_prodOneSub_nonneg _ ⟨hu.1, hu.2.le⟩)
        rw [mergedD, ev_sub, ← qProd_toFinset hlnd, hlS]
        have hR : ev (prodOneSub R4) u = qProd R4f u := by
          rw [← qProd_toFinset (by decide)]; rfl
        rw [hR, ← qProdSet_coe]
        have := qProdSet_antitone (S := (Sf : Set ℕ)) (T := (S' : Set ℕ))
          (by exact_mod_cast hSS) hu.1 hu.2
        linarith
  · -- tail: an element `s₀ ≥ 64`
    push Not at hsmall
    obtain ⟨s0, hs0, hs064⟩ := hsmall
    set Rp := R4.filter fun r => r ∉ S
    set R0 := R4.filter fun r => r ∈ S
    have hRpne : Rp ≠ [] := by
      intro h
      have hall : ∀ r ∈ R4, r ∈ S := fun r hr => by
        by_contra hrS
        have : r ∈ Rp := List.mem_filter.mpr ⟨hr, by simpa using hrS⟩
        rw [h] at this; simp at this
      obtain ⟨q, hq, hqs⟩ := Nat.exists_prime_and_dvd (show s0 ≠ 1 by omega)
      have hq7 := hsm s0 hs0 q hq hqs
      have hqR : q ∈ R4 := by
        have := hq.two_le
        interval_cases q <;> simp_all [R4] <;> norm_num at hq
      have := hSp.2 q (hall q hqR) s0 hs0 hqs
      omega
    have hRp : Rp ∈ RpList := rp_mem_RpList Rp (List.mem_sublists.mpr (List.filter_sublist)) hRpne
    set S' : Set ℕ := {s ∈ S | s ∉ R4}
    -- elements of `S'` are composites of `⟨R'⟩`
    have hS'comp : ∀ s ∈ S', 4 ≤ s ∧ smoothIn Rp s = true ∧ s ∉ Rp := by
      intro s hs
      have hs2 := hSp.1 s hs.1
      rcases seven_smooth_cases hs2 (hsm s hs.1) with h | h
      · exact absurd h hs.2
      refine ⟨?_, (smoothIn_iff (by omega)).mpr fun q hq hqs => ?_, fun h' => hs.2 (List.mem_of_mem_filter h')⟩
      · by_contra h4
        interval_cases s <;> norm_num at h
      · have hq7 := hsm s hs.1 q hq hqs
        have hqR : q ∈ R4 := by
          have := hq.two_le
          interval_cases q <;> simp_all [R4] <;> norm_num at hq
        refine List.mem_filter.mpr ⟨hqR, ?_⟩
        simp only [decide_eq_true_eq]
        intro hqS
        have := hSp.2 q hqS s hs.1 hqs
        exact hs.2 (this ▸ hqR)
    obtain ⟨A0, hA0⟩ := finite_of_bounded (S := {s ∈ S' | s < 24}) (m := 24) fun s hs => hs.2
    have hA0mem : ∀ a ∈ A0, a ∈ S' ∧ a < 24 := fun a ha => by
      have : a ∈ ({s ∈ S' | s < 24} : Set ℕ) := by rw [← hA0]; exact_mod_cast ha
      exact this
    obtain ⟨l, hl, hlA, hlnd⟩ := mem_antichains (compositesR_pairwise Rp 4 24)
      (fun x hx => by have := (mem_compositesR.mp hx).2.1; omega) (S := A0)
      (fun s hs => by
        obtain ⟨h1, h2⟩ := hA0mem s hs
        obtain ⟨h3, h4, h5⟩ := hS'comp s h1
        exact mem_compositesR.mpr ⟨h2, h3, h4, h5⟩)
      (fun a ha b hb hab => hSp.2 a (hA0mem a ha).1.1 b (hA0mem b hb).1.1 hab)
    have hok := hT Rp hRp l hl
    simp only [mergedTailOK] at hok
    cases hlk : mergedTailTbl.lookup (Rp, l) with
    | none => rw [hlk] at hok; simp at hok
    | some prm =>
      obtain ⟨u1, u0⟩ := prm
      rw [hlk] at hok
      simp only [mergedTailCert] at hok
      set Cl := tailCl Rp l
      set Wl := primesIn 11 64 ++ R0of Rp
      have hWl1 : ∀ n ∈ Wl, 1 ≤ n := fun n hn => by
        rcases List.mem_append.mp hn with h | h
        · have := (mem_primesIn.mp h).2.1; omega
        · have : n ∈ R4 := List.mem_of_mem_filter h
          simp [R4] at this; omega
      have hW0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ ev (prodOneSub Wl) u := fun u hu => ev_prodOneSub_nonneg _ hu
      have hW : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < ev (prodOneSub Wl) u := fun u hu => ev_prodOneSub_pos hWl1 hu
      have hS'1 : ∀ n ∈ S', 1 ≤ n := fun n hn => hS1 n hn.1
      set E : ℝ → ℝ := fun u => qProdSet S' (clampI u)
      have hEc : Continuous E :=
        (qProdSet_continuousOn_Icc hS'1).comp_continuous continuous_clampI clampI_mem
      have hla : ∀ a ∈ l, a < 24 := fun a ha =>
        (hA0mem a (by rw [← hlA]; exact List.mem_toFinset.mpr ha)).2
      have hlS' : ∀ a ∈ l, a ∈ S' := fun a ha =>
        (hA0mem a (by rw [← hlA]; exact List.mem_toFinset.mpr ha)).1
      have hCb : ∀ b ∈ Cl, 24 ≤ b ∧ b < 120 := fun b hb => by
        have := mem_compositesR.mp (List.mem_of_mem_filter hb); exact ⟨this.2.1, this.1⟩
      have hClnd : Cl.Nodup := by
        simp only [Cl, tailCl, compositesR]; exact (List.nodup_range.filter _).filter _
      have hMnd : (l ++ Cl).Nodup := by
        rw [List.nodup_append]
        refine ⟨hlnd, hClnd, ?_⟩
        intro a ha b hb hab
        have := hla a ha; have := (hCb b hb).1; omega
      have hMB : ∀ m ∈ l ++ Cl, m < 120 := fun m hm => by
        rcases List.mem_append.mp hm with h | h
        · have := hla m h; omega
        · exact (hCb m h).2
      have hEnv : S' ⊆ ((l ++ Cl).toFinset : Set ℕ) ∪ {n | 120 ≤ n} := by
        intro s hs
        by_cases h24 : s < 24
        · left
          have : s ∈ A0 := by
            have h' : s ∈ ({s ∈ S' | s < 24} : Set ℕ) := ⟨hs, h24⟩
            rw [← hA0] at h'; exact_mod_cast h'
          simp only [Finset.mem_coe, List.mem_toFinset, List.mem_append]
          exact Or.inl (List.mem_toFinset.mp (by rw [hlA]; exact this))
        · by_cases h120 : s < 120
          · left
            simp only [Finset.mem_coe, List.mem_toFinset, List.mem_append]
            right
            obtain ⟨h4, hsmR, hnR⟩ := hS'comp s hs
            refine List.mem_filter.mpr ⟨mem_compositesR.mpr ⟨h120, by omega, hsmR, hnR⟩, ?_⟩
            simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero]
            intro a ha hdvd
            have := hSp.2 a (hlS' a ha).1 s hs.1 hdvd
            have := hla a ha
            omega
          · right; simp only [Set.mem_ofPred_eq]; omega
      have hrun := v1Check_sound (p := 1) (le_refl 1) (by norm_num) hW0 hW hok hEc
        (fun u hu => qProdSet_nonneg S' (clampI_mem _))
        (fun u hu => by
          simp only [pow_one, E, clampI_of_mem ⟨hu.1, hu.2.le⟩]
          exact envelope_ge hMnd hMB hEnv hu.1 hu.2)
      -- the factorizations `P_S = P_{R₀} P_{S'}`, `P_{2,3,5,7} = P_{R₀} P_{R'}`
      have hR0mem : ∀ r, r ∈ R0of Rp ↔ r ∈ R4 ∧ r ∈ S := by
        intro r
        simp only [R0of, Rp, List.mem_filter, Bool.not_eq_true', List.contains_eq_any_beq,
          List.any_eq_false, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          by_contra hrS
          exact h2 r ⟨h1, hrS⟩ rfl
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun x hx hxr => hx.2 (hxr ▸ h2)⟩
      have hSsplit : S = ((R0of Rp).toFinset : Set ℕ) ∪ S' := by
        ext x
        simp only [Set.mem_union, Finset.mem_coe, List.mem_toFinset, hR0mem, S', Set.mem_ofPred_eq]
        constructor
        · intro hx; by_cases hxR : x ∈ R4
          · exact Or.inl ⟨hxR, hx⟩
          · exact Or.inr ⟨hx, hxR⟩
        · rintro (⟨_, hx⟩ | ⟨hx, _⟩) <;> exact hx
      have hSdisj : Disjoint ((R0of Rp).toFinset : Set ℕ) S' := by
        rw [Set.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_coe, List.mem_toFinset, hR0mem] at hx
        exact hx'.2 hx.1
      have hR4split : R4f = (R0of Rp).toFinset ∪ Rp.toFinset := by
        ext r
        simp only [Finset.mem_union, List.mem_toFinset, hR0mem]
        constructor
        · intro hr
          have hr' : r ∈ R4 := by simpa [R4f, R4] using hr
          by_cases hrS : r ∈ S
          · exact Or.inl ⟨hr', hrS⟩
          · exact Or.inr (List.mem_filter.mpr ⟨hr', by simpa using hrS⟩)
        · rintro (⟨hr, _⟩ | hr)
          · simpa [R4f, R4] using hr
          · have := List.mem_of_mem_filter hr; simpa [R4f, R4] using this
      have hR4disj : Disjoint (R0of Rp).toFinset Rp.toFinset := by
        rw [Finset.disjoint_left]
        intro r hr hr'
        simp only [List.mem_toFinset, hR0mem] at hr
        have := (List.mem_filter.mp (List.mem_toFinset.mp hr')).2
        simp only [decide_eq_true_eq] at this
        exact this hr.2
      have hRpnd : Rp.Nodup := (by decide : R4.Nodup).filter _
      have hR0nd : (R0of Rp).Nodup := (by decide : R4.Nodup).filter _
      refine ⟨(primesIn 11 64).toFinset, fun q hq => ?_, fromRun _ ?_⟩
      · obtain ⟨h1, h2, h3⟩ := mem_primesIn.mp (List.mem_toFinset.mp hq)
        exact ⟨h3, h2, s0, hs0, by omega⟩
      · refine runPos_congr hrun fun u hu => ?_
        simp only [E, clampI_of_mem ⟨hu.1, hu.2.le⟩]
        have hW' : ev (prodOneSub Wl) u = qProd (primesIn 11 64).toFinset u * qProd (R0of Rp).toFinset u := by
          rw [qProd_toFinset (primesIn_nodup _ _), qProd_toFinset hR0nd]
          simp [Wl, ev_prodOneSub, List.map_append, List.prod_append]
        have hS' : qProdSet S u = qProd (R0of Rp).toFinset u * qProdSet S' u := by
          conv_lhs => rw [hSsplit]
          rw [qProdSet_union hSdisj hu.1 hu.2, qProdSet_coe]
        have hR' : qProd R4f u = qProd (R0of Rp).toFinset u * ev (prodOneSub Rp) u := by
          rw [hR4split, qProd, Finset.prod_union hR4disj, ← qProd_toFinset hRpnd]; rfl
        rw [hW', hS', hR']
        ring

/-! ## Small `N` -/

def SmallOKAll (N : ℕ) : Prop := ∀ l ∈ antichains (List.range' 2 (N - 1)) [], smallOK N l = true

theorem primesIn_toFinset (N : ℕ) : (primesIn 2 N).toFinset = primesLE N := by
  ext q
  simp only [List.mem_toFinset, mem_primesIn, mem_primesLE]
  constructor
  · rintro ⟨h1, _, h3⟩; exact ⟨h3, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1.two_le, h1⟩

theorem small_cert {N : ℕ} (h : SmallOKAll N) {A : Finset ℕ} (hA : IsPrimitiveFin A)
    (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N) :
    RunPos (fun u => qProd A u - qProd (primesLE N) u) 126 := by
  have hsort : (List.range' 2 (N - 1)).Pairwise (· < ·) := List.pairwise_lt_range' 1
  obtain ⟨l, hl, hlA, hlnd⟩ := mem_antichains hsort
    (fun x hx => by have := (List.mem_range'_1.mp hx).1; omega) (S := A)
    (fun s hs => by
      have h2 := hA.1 s hs; have hN := hAN s hs
      exact List.mem_range'_1.mpr ⟨h2, by omega⟩)
    (isAC_of_primitive hA)
  have hok := h l hl
  simp only [smallOK, Bool.or_eq_true, beq_iff_eq] at hok
  rcases hok with hok | hok
  · exact absurd (by rw [← hlA, hok, primesIn_toFinset]) hne
  · have hrun := scCheckZ_sound (W := [1]) (le_refl 1) (by norm_num : (0 : ℚ) < 126)
      (fun u _ => by simp) (fun u _ => by simp) hok
    refine runPos_congr hrun fun u _ => ?_
    simp only [ev_cons, ev_nil, mul_zero, add_zero, Rat.cast_one, one_mul, pow_one, smallD, ev_sub]
    rw [← qProd_toFinset hlnd, hlA, ← qProd_toFinset (primesIn_nodup _ _), primesIn_toFinset]

end RntPaper.K9
