import RntPaper.K9Sound
import RntPaper.MomentsOdd

/-!
# The weighted ordered descent up to `k₉` (notes, Theorem 3.8)

Given the case checks (bundled in `K9Certs`), for every `1 ≤ k ≤ k₉` and `c ∈ (0,1]`:

* `k9_descent`: `𝓜ₖ,c(𝒫_N) ≤ 𝓜ₖ,c(A)` for primitive `A ⊆ [2,N]`, strictly if `k < k₉` and
  `A ≠ 𝒫_N`;
* `k9_primes_le`, `k9_primes_lt`: the same for arbitrary primitive `A` and `𝒫`.

Steps, measured by the sum of the composite elements:

1. a composite with a prime factor `p ≥ 61`: compress at `p` (`k ≤ p`, or `k/p ≤ k₉/61 < 17/8`);
2. otherwise let `p ∈ [11,59]` be the largest prime dividing a composite: add the missing primes
   in `(p, N]` and compress at `p` with the weight `∏_{q ∈ Q}(1-u^q)` (`single_cert`);
3. otherwise every composite is `7`-smooth: add the missing primes in `[11,N]` and the primes
   `r ≤ 7` dividing no element, and compare the `7`-smooth part `S` with `{2,3,5,7}` under the
   weight of the primes `≥ 11` (`merged_cert`); for `N ≤ 6` compare directly (`small_cert`).
-/

namespace RntPaper.K9

open MeasureTheory intervalIntegral Set CP QProduct

/-- All the computational facts used by the descent. -/
structure K9Certs : Prop where
  merged : MergedOKAll
  mtail : ∀ Rp ∈ RpList, MergedTailOKAll Rp
  single : ∀ p m B : ℕ, (p, m, B) ∈ singleParams → SingleOKAll p m ∧ SingleTailOKAll p m B
  small : ∀ N : ℕ, 2 ≤ N → N ≤ 6 → SmallOKAll N

/-! ## Elementary facts about `MSet` -/

theorem MSet_anti {A A' : Set ℕ} (h : A ⊆ A') (hA : ∀ n ∈ A, 1 ≤ n) (hA' : ∀ n ∈ A', 1 ≤ n)
    {k : ℝ} (hk : 1 ≤ k) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c A' ≤ MSet k c A := by
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  unfold MSet
  apply intervalIntegral.integral_mono_ae_restrict hc.1.le (intervalIntegrable_MSet _ hk hcI)
    (intervalIntegrable_MSet _ hk hcI)
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with u hu hu1
  have hu1' : u < 1 := lt_of_le_of_ne (hu.2.trans hc.2) hu1
  have hw : 0 ≤ k * u ^ (k - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg hu.1 _)
  exact mul_le_mul_of_nonneg_left (qProdSet_antitone h hu.1 hu1') hw

/-- `GoodAt s` for `1 ≤ s ≤ 17/4`. -/
theorem goodAt_small {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 17 / 4) : GoodAt s :=
  goodAt_of_admissible h1 (admissible_le_seventeen_quarters h1 h2)

/-! ## The three kinds of steps -/

/-- **Weighted exchange** (notes, Lemma 3.9), strict form. -/
theorem MSet_weighted_exchange_lt {B T : Set ℕ} {p : ℕ} (hp : 0 < p) (hB : ∀ b ∈ B, 2 ≤ b)
    (hT : ∀ t ∈ T, 2 ≤ t) (hdisj : Disjoint B ((· * p) '' T)) (hpB : p ∉ B) {Q : Finset ℕ}
    (hQB : (Q : Set ℕ) ⊆ B) {k : ℝ} (hk : 1 ≤ k) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1)
    (hrun : ∀ y ∈ Ioc (0 : ℝ) 1,
      0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd Q u * ESetExt T (u ^ p))) :
    MSet k c (insert p B) < MSet k c (B ∪ (· * p) '' T) := by
  have hcIcc : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hT1 : ∀ t ∈ T, 1 ≤ t := fun t ht => le_trans (by norm_num) (hT t ht)
  set g : ℝ → ℝ := fun u => k * u ^ (k - 1) * (qProd Q u * ESetExt T (u ^ p)) with hgdef
  have hgc : Continuous g :=
    (continuous_rpow_weight hk).mul ((by unfold qProd; fun_prop : Continuous (qProd Q)).mul
      ((continuous_ESetExt hT1).comp (continuous_pow p)))
  have hG : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y, g u := by
    intro y hy
    have : (∫ u in (0 : ℝ)..y, g u)
        = k * ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd Q u * ESetExt T (u ^ p)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr; intro u _; simp only [hgdef]; ring
    rw [this]; exact mul_pos (by linarith) (hrun y hy)
  have hBQ : ∀ b ∈ B \ (Q : Set ℕ), 2 ≤ b := fun b hb => hB b hb.1
  have hpos := integral_qProdSet_mul_pos hBQ hgc hG hc
  rw [← sub_pos]
  unfold MSet
  rw [← intervalIntegral.integral_sub (intervalIntegrable_MSet _ hk hcIcc)
    (intervalIntegrable_MSet _ hk hcIcc)]
  convert hpos using 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with u hu1 hu
  rw [uIoc_of_le hc.1.le] at hu
  have hu1' : u < 1 := lt_of_le_of_ne (hu.2.trans hc.2) hu1
  have hdiff := qProdSet_blockStep_diff hp hdisj hpB hu.1.le hu1'
  have hEu : ESetExt T (u ^ p) = blockESet T (u ^ p) :=
    ESetExt_of_mem T ⟨pow_nonneg hu.1.le p, pow_le_one₀ hu.1.le hu1'.le⟩
  have hsplitB : qProdSet B u = qProd Q u * qProdSet (B \ (Q : Set ℕ)) u := by
    conv_lhs => rw [show B = (Q : Set ℕ) ∪ (B \ (Q : Set ℕ)) from (Set.union_diff_cancel hQB).symm]
    rw [qProdSet_union Set.disjoint_sdiff_right hu.1.le hu1', qProdSet_coe]
  simp only [hgdef, hEu]
  rw [← mul_sub, hdiff, hsplitB]
  ring

/-- **Large primes.** For `p ≥ 61` and `1 ≤ k ≤ k₉` every compression at `p` is strict. -/
theorem large_step {A : Set ℕ} {p : ℕ} (hp : p.Prime) (hp61 : 61 ≤ p) (hA : IsPrimitive A)
    (hpA : p ∉ A) {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ k9) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (compressAtSet p A) < MSet k c A := by
  have hB : ∀ b ∈ {a ∈ A | ¬ p ∣ a}, 2 ≤ b := fun b hb => hA.1 b hb.1
  have hTp := quotients_set_isPrimitive hA hpA
  have hpB : p ∉ {a ∈ A | ¬ p ∣ a} := fun h => h.2 (dvd_refl p)
  have hrun : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y,
      u ^ (k - 1) * ESetExt ((fun a => a / p) '' {a ∈ A | p ∣ a}) (u ^ p) := by
    intro y hy
    rcases le_or_gt k p with hkp | hpk
    · exact run_pos_of_le hTp.1 hp.one_le hk1 hkp hy
    · have hpR : (61 : ℝ) ≤ p := by exact_mod_cast hp61
      have hs1 : 1 ≤ k / p := by rw [le_div_iff₀ (by linarith)]; linarith
      have hs : k / p ≤ 17 / 8 := by
        rw [div_le_iff₀ (by linarith)]
        have := k9_lt_126
        nlinarith
      exact run_pos_of_lt hTp hp.one_le hpk.le hs (goodAt_small hs1 (by linarith)) hy
  have h := MSet_block_exchange_lt hp.pos hB hTp.1 (disjoint_nonMultiples_block_set p A) hpB
    hk1 hrun hc
  rw [← block_decomp_set p A] at h
  exact h

/-- **Weighted single-prime step** (`11 ≤ p ≤ 59`). `A` must contain every prime `q > p` that is
at most some multiple of `p` in `A`, and every multiple of `p` in `A` must be `p`-smooth. -/
theorem single_step (hC : K9Certs) {p m B : ℕ} (hpmB : (p, m, B) ∈ singleParams)
    {A : Set ℕ} (hA : IsPrimitive A) (hpA : p ∉ A) (hmult : ∃ a ∈ A, p ∣ a)
    (hsm : ∀ a ∈ A, p ∣ a → ∀ q, q.Prime → q ∣ a → q ≤ p)
    (hbig : ∀ q, q.Prime → p < q → (∃ a ∈ A, p ∣ a ∧ q ≤ a) → q ∈ A)
    {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 126) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (compressAtSet p A) < MSet k c A := by
  have hp : p.Prime := by
    simp only [singleParams, List.mem_cons, List.mem_singleton, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hpmB
    rcases hpmB with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h.1] <;> norm_num
  obtain ⟨hE, hTl⟩ := hC.single p m B hpmB
  set T := (fun a => a / p) '' {a ∈ A | p ∣ a}
  have hTp := quotients_set_isPrimitive hA hpA
  have hTne : T.Nonempty := by
    obtain ⟨a, ha, hpa⟩ := hmult; exact ⟨a / p, a, ⟨ha, hpa⟩, rfl⟩
  have hTsm : ∀ t ∈ T, ∀ q, q.Prime → q ∣ t → q ≤ p := by
    rintro t ⟨a, ⟨ha, hpa⟩, rfl⟩ q hq hqt
    exact hsm a ha hpa q hq (hqt.trans (Nat.div_dvd_of_dvd hpa))
  obtain ⟨Q, hQ, hrun⟩ := single_cert hp hE hTl hTp hTsm hTne
  have hB : ∀ b ∈ {a ∈ A | ¬ p ∣ a}, 2 ≤ b := fun b hb => hA.1 b hb.1
  have hpB : p ∉ {a ∈ A | ¬ p ∣ a} := fun h => h.2 (dvd_refl p)
  have hQB : (Q : Set ℕ) ⊆ {a ∈ A | ¬ p ∣ a} := by
    intro q hq
    obtain ⟨hqp, hpq, t, ⟨a, ⟨ha, hpa⟩, rfl⟩, hqt⟩ := hQ q hq
    refine ⟨hbig q hqp hpq ⟨a, ha, hpa, ?_⟩, fun hdvd => ?_⟩
    · rwa [Nat.mul_div_cancel' hpa] at hqt
    · have := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hdvd; omega
  have h := MSet_weighted_exchange_lt hp.pos hB hTp.1 (disjoint_nonMultiples_block_set p A) hpB
    hQB hk1 hc (fun y hy => hrun k hk1 hk y hy)
  rw [← block_decomp_set p A] at h
  exact h

/-- **The merged comparison.** `Pb` is a set of primes `≥ 11` containing every prime `q ≥ 11` that
is at most some element of `S`. -/
theorem merged_step (hC : K9Certs) {S Pb : Set ℕ} (hSp : IsPrimitive S)
    (hsm : ∀ s ∈ S, ∀ q, q.Prime → q ∣ s → q ≤ 7) (hcov : ∀ r ∈ R4, ∃ s ∈ S, r ∣ s)
    (hne : S ≠ (R4f : Set ℕ)) (hPb : ∀ q ∈ Pb, q.Prime ∧ 11 ≤ q)
    (hPbS : ∀ q, q.Prime → 11 ≤ q → (∃ s ∈ S, q ≤ s) → q ∈ Pb)
    {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ k9) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (Pb ∪ (R4f : Set ℕ)) ≤ MSet k c (Pb ∪ S) ∧
      (k < k9 → MSet k c (Pb ∪ (R4f : Set ℕ)) < MSet k c (Pb ∪ S)) := by
  obtain ⟨Q, hQ, hrun⟩ := merged_cert hC.merged hC.mtail hSp hsm hcov hne
  have hcIcc : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hS1 : ∀ n ∈ S, 1 ≤ n := fun n hn => le_trans (by norm_num) (hSp.1 n hn)
  have hQPb : (Q : Set ℕ) ⊆ Pb := fun q hq => by
    obtain ⟨h1, h2, h3⟩ := hQ q hq; exact hPbS q h1 h2 h3
  have hPbS' : Disjoint Pb S := by
    rw [Set.disjoint_left]
    intro q hq hqS
    have := hsm q hqS q (hPb q hq).1 dvd_rfl
    have := (hPb q hq).2
    omega
  have hPbR : Disjoint Pb (R4f : Set ℕ) := by
    rw [Set.disjoint_left]
    intro q hq hqR
    have := (hPb q hq).2
    simp [R4f] at hqR
    omega
  set g : ℝ → ℝ := fun u => k * u ^ (k - 1) *
    (qProd Q u * (qProdSet S (clampI u) - qProd R4f u)) with hgdef
  have hgc : Continuous g :=
    (continuous_rpow_weight hk1).mul ((by unfold qProd; fun_prop : Continuous (qProd Q)).mul
      (((qProdSet_continuousOn_Icc hS1).comp_continuous continuous_clampI clampI_mem).sub
        (by unfold qProd; fun_prop : Continuous (qProd R4f))))
  have hGeq : ∀ y ∈ Icc (0 : ℝ) 1, (∫ u in (0 : ℝ)..y, g u) = k * ∫ u in (0 : ℝ)..y,
      u ^ (k - 1) * (qProd Q u * (qProdSet S u - qProd R4f u)) := by
    intro y hy
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hy.1] at hu
    simp only [hgdef, clampI_of_mem ⟨hu.1, hu.2.trans hy.2⟩]
    ring
  have hdiff : MSet k c (Pb ∪ S) - MSet k c (Pb ∪ (R4f : Set ℕ))
      = ∫ u in (0 : ℝ)..c, qProdSet (Pb \ (Q : Set ℕ)) u * g u := by
    unfold MSet
    rw [← intervalIntegral.integral_sub (intervalIntegrable_MSet _ hk1 hcIcc)
      (intervalIntegrable_MSet _ hk1 hcIcc)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with u hu1 hu
    rw [uIoc_of_le hc.1.le] at hu
    have hu1' : u < 1 := lt_of_le_of_ne (hu.2.trans hc.2) hu1
    have hsplitPb : qProdSet Pb u = qProd Q u * qProdSet (Pb \ (Q : Set ℕ)) u := by
      conv_lhs => rw [show Pb = (Q : Set ℕ) ∪ (Pb \ (Q : Set ℕ)) from
        (Set.union_diff_cancel hQPb).symm]
      rw [qProdSet_union Set.disjoint_sdiff_right hu.1.le hu1', qProdSet_coe]
    rw [qProdSet_union hPbS' hu.1.le hu1', qProdSet_union hPbR hu.1.le hu1', qProdSet_coe,
      hsplitPb]
    simp only [hgdef, clampI_of_mem ⟨hu.1.le, hu1'.le⟩]
    ring
  have hB2 : ∀ b ∈ Pb \ (Q : Set ℕ), 2 ≤ b := fun b hb => (hPb b hb.1).1.two_le
  refine ⟨?_, fun hlt => ?_⟩
  · have hnn := integral_qProdSet_mul_nonneg (Pb \ (Q : Set ℕ)) hgc (fun y hy => by
      rcases eq_or_lt_of_le hy.1 with h0 | h0
      · rw [← h0]; simp
      · rw [hGeq y hy]
        exact mul_nonneg (by linarith) ((hrun k hk1 hk y ⟨h0, hy.2⟩).1)) hcIcc
    linarith
  · have hp := integral_qProdSet_mul_pos hB2 hgc (fun y hy => by
      rw [hGeq y ⟨hy.1.le, hy.2⟩]
      exact mul_pos (by linarith) ((hrun k hk1 hk y hy).2 hlt)) hc
    linarith

end RntPaper.K9
