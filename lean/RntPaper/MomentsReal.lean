import RntPaper.MomentsWeight
import RntPaper.PrimeCrossing
import RntPaper.MomentCert
import RntPaper.Consequences

/-!
# Prime minimality of the moments `𝔼 Z_A^k` for real `1 ≤ k ≤ 17/4`
(paper Proposition 5.2)

For real `k > 0` and `0 < c ≤ 1` put `𝓜ₖ,c(A) = ∫₀ᶜ k u^{k-1} P_A(u) du`
(`= 𝔼 min(Z_A^k, c^k)`). The primes minimize `𝓜ₖ,c` over primitive sets, uniquely,
for every `1 ≤ k ≤ 17/4`, finite (`MSet_primesLE_lt`) and infinite (`MSet_primes_lt`).

The proof bootstraps the compression argument. Compressing `A` at a prime `p` changes
`𝓜ₖ,c` by `∫₀ᶜ k u^{k-1} P_B(u) E_T(uᵖ) du`, where the quotient block `T` is itself
**primitive**. The weighted running integrals of `u^{k-1}E_T(uᵖ)` are positive:

* if `k ≤ p`, by the power substitution with the singular weight `v^{k/p-1}` against the
  continuous envelope `E_H ≤ E_T` (`running_pos_rpow_comp_pow`);
* if `p < k`, by the substitution `v = uᵖ` (exponent `s = k/p`), the already established
  minimality at exponent `s` applied to the primitive set `T`, and the positivity of
  `J_s(z) = ∫₀ᶻ v^{s-1}(Q(v) - (1-v)) dv` for `s ≤ 17/8` (single crossing of `Q - (1-x)`,
  `Jw_pos_of`, plus the exact certificate `moment_cert`).

Every prime `p < k ≤ 17/4` has `s = k/p ≤ 17/8`, so the ranges `[1,2] → [1,4] → [1,17/4]`
are reached in three rounds (`admissible_of_good`).
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set Filter Topology

/-! ## Definitions -/

/-- `𝓜ₖ,c(A) = ∫₀ᶜ k u^{k-1} P_A(u) du` for a real exponent `k`. -/
noncomputable def MSet (k c : ℝ) (A : Set ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..c, k * u ^ (k - 1) * qProdSet A u

theorem continuous_rpow_weight {k : ℝ} (hk : 1 ≤ k) : Continuous fun u : ℝ => k * u ^ (k - 1) :=
  continuous_const.mul (Real.continuous_rpow_const (by linarith))

theorem intervalIntegrable_MSet (A : Set ℕ) {k : ℝ} (hk : 1 ≤ k) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => k * u ^ (k - 1) * qProdSet A u) volume 0 c :=
  (intervalIntegrable_qProdSet A hc).continuousOn_mul (continuous_rpow_weight hk).continuousOn

/-- `𝓜₁,c = F_c`. -/
theorem MSet_one (c : ℝ) (A : Set ℕ) : MSet 1 c A = FcSet c A := by
  unfold MSet FcSet
  apply intervalIntegral.integral_congr
  intro u _
  simp

/-- A continuous clamp to `[0,1]`. -/
noncomputable def clampI (v : ℝ) : ℝ := max 0 (min v 1)

theorem continuous_clampI : Continuous clampI :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampI_mem (v : ℝ) : clampI v ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clampI_of_mem {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : clampI v = v := by
  unfold clampI
  rw [min_eq_left hv.2, max_eq_right hv.1]

/-- `E_T(v) = P_T(v) - (1 - v)`, extended continuously from `[0,1]` to `ℝ`. -/
noncomputable def ESetExt (T : Set ℕ) (v : ℝ) : ℝ := qProdSet T (clampI v) - (1 - clampI v)

theorem continuous_ESetExt {T : Set ℕ} (hT : ∀ n ∈ T, 1 ≤ n) : Continuous (ESetExt T) :=
  ((qProdSet_continuousOn_Icc hT).comp_continuous continuous_clampI clampI_mem).sub
    (continuous_const.sub continuous_clampI)

theorem ESetExt_of_mem (T : Set ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ESetExt T v = blockESet T v := by
  unfold ESetExt blockESet
  rw [clampI_of_mem hv]

theorem continuousOn_ESetExt_Icc {T : Set ℕ} (hT : ∀ n ∈ T, 1 ≤ n) :
    ContinuousOn (ESetExt T) (Icc 0 1) :=
  (continuous_ESetExt hT).continuousOn

/-! ## The block exchange at exponent `k` -/

/-- **Strict block exchange for `𝓜ₖ`.** If the running integrals of `u^{k-1} E_T(uᵖ)` are
positive on `(0,1]`, then `𝓜ₖ,c(B ∪ {p}) < 𝓜ₖ,c(B ∪ pT)`. -/
theorem MSet_block_exchange_lt {B T : Set ℕ} {p : ℕ} (hp : 0 < p)
    (hB : ∀ b ∈ B, 2 ≤ b) (hT : ∀ t ∈ T, 2 ≤ t)
    (hdisj : Disjoint B ((· * p) '' T)) (hpB : p ∉ B) {k : ℝ} (hk : 1 ≤ k)
    (hrun : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * ESetExt T (u ^ p))
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (insert p B) < MSet k c (B ∪ (· * p) '' T) := by
  have hcIcc : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hT1 : ∀ t ∈ T, 1 ≤ t := fun t ht => le_trans (by norm_num) (hT t ht)
  set g : ℝ → ℝ := fun u => k * u ^ (k - 1) * ESetExt T (u ^ p) with hgdef
  have hgc : Continuous g :=
    (continuous_rpow_weight hk).mul ((continuous_ESetExt hT1).comp (continuous_pow p))
  have hG : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y, g u := by
    intro y hy
    have : (∫ u in (0 : ℝ)..y, g u) = k * ∫ u in (0 : ℝ)..y, u ^ (k - 1) * ESetExt T (u ^ p) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      simp only [hgdef]
      ring
    rw [this]
    exact mul_pos (by linarith) (hrun y hy)
  have hpos := integral_qProdSet_mul_pos hB hgc hG hc
  rw [← sub_pos]
  unfold MSet
  rw [← intervalIntegral.integral_sub (intervalIntegrable_MSet _ hk hcIcc)
    (intervalIntegrable_MSet _ hk hcIcc)]
  convert hpos using 1
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := Measure.ae_ne volume 1
  filter_upwards [hne] with u hu1 hu
  rw [uIoc_of_le hc.1.le] at hu
  have hu1' : u < 1 := lt_of_le_of_ne (hu.2.trans hc.2) hu1
  have hdiff := qProdSet_blockStep_diff hp hdisj hpB hu.1.le hu1'
  have hEu : ESetExt T (u ^ p) = blockESet T (u ^ p) :=
    ESetExt_of_mem T ⟨pow_nonneg hu.1.le p, pow_le_one₀ hu.1.le hu1'.le⟩
  simp only [hgdef, hEu]
  rw [← mul_sub, hdiff]
  ring

/-! ## Running positivity of `u^{k-1} E_T(uᵖ)` -/

/-- **Case `k ≤ p`**: from the continuous envelope `E_H ≤ E_T` and the power substitution. -/
theorem run_pos_of_le {T : Set ℕ} (hT : ∀ t ∈ T, 2 ≤ t) {p : ℕ} (hp : 1 ≤ p) {k : ℝ}
    (hk : 1 ≤ k) (hkp : k ≤ p) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * ESetExt T (u ^ p) := by
  have hT1 : ∀ t ∈ T, 1 ≤ t := fun t ht => le_trans (by norm_num) (hT t ht)
  have hH := running_pos_rpow_comp_pow continuous_blockEH
    (fun d hd => blockEH_partial_pos hd) hp hk hkp hy
  refine lt_of_lt_of_le hH ?_
  apply intervalIntegral.integral_mono_on hy.1.le
  · exact ((Real.continuous_rpow_const (by linarith)).mul
      (continuous_blockEH.comp (continuous_pow p))).intervalIntegrable 0 y
  · exact ((Real.continuous_rpow_const (by linarith)).mul
      ((continuous_ESetExt hT1).comp (continuous_pow p))).intervalIntegrable 0 y
  · intro u hu
    have hu' : u ^ p ∈ Icc (0 : ℝ) 1 :=
      ⟨pow_nonneg hu.1 p, pow_le_one₀ hu.1 (hu.2.trans hy.2)⟩
    rw [ESetExt_of_mem T hu']
    exact mul_le_mul_of_nonneg_left (blockEH_le_blockESet hT hu') (Real.rpow_nonneg hu.1 _)

/-- The defining identity for `J_s`: `∫₀ᶻ v^{s-1}E_T(v) = (𝓜ₛ,z(T) - 𝓜ₛ,z(𝒫))/s + J_s(z)`. -/
theorem integral_rpow_ESetExt_eq {T : Set ℕ} {s : ℝ} (hs : 1 ≤ s) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) :
    (∫ v in (0 : ℝ)..z, v ^ (s - 1) * ESetExt T v)
      = (MSet s z T - MSet s z Primes) / s + Jw s z := by
  have hs0 : s ≠ 0 := by positivity
  have hI1 := intervalIntegrable_MSet T hs hz
  have hI2 := intervalIntegrable_MSet Primes hs hz
  have hJ : IntervalIntegrable (fun x => x ^ (s - 1) * (Qfun x - (1 - x))) volume 0 z :=
    ((continuousOn_Jw_integrand hs).mono (uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ hz)).intervalIntegrable
  unfold MSet Jw
  rw [← intervalIntegral.integral_sub hI1 hI2, ← intervalIntegral.integral_div,
    ← intervalIntegral.integral_add (hI1.sub hI2 |>.div_const s) hJ]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := Measure.ae_ne volume 1
  filter_upwards [hne] with v hv1 hv
  rw [uIoc_of_le hz.1] at hv
  have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.trans hz.2⟩
  rw [ESetExt_of_mem T hvI]
  unfold blockESet Qfun
  field_simp
  ring

/-- `∫₀ᶻ v^{s-1}(P_T(v) - Q(v)) dv ≥ 0` is the statement `𝓜ₛ,z(𝒫) ≤ 𝓜ₛ,z(T)`. -/
def GoodAt (s : ℝ) : Prop :=
  ∀ T : Set ℕ, IsPrimitive T → ∀ z ∈ Ioc (0 : ℝ) 1, MSet s z Primes ≤ MSet s z T

/-- **Case `p < k`**: from minimality at the exponent `s = k/p ≤ 17/8` applied to the
primitive set `T`, and `J_s > 0`. -/
theorem run_pos_of_lt {T : Set ℕ} (hTp : IsPrimitive T) {p : ℕ} (hp : 1 ≤ p) {k : ℝ}
    (hpk : (p : ℝ) ≤ k) (hs : k / p ≤ 17 / 8) (hgood : GoodAt (k / p))
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
  have hJ : 0 < Jw (k / p) (y ^ p) := Jw_pos_of hs1 hs moment_cert hz
  have : 0 < 1 / (p : ℝ) := by positivity
  nlinarith

/-! ## Compression and insertion at exponent `k` -/

/-- The quotient block of a primitive set is primitive. -/
theorem quotients_set_isPrimitive {A : Set ℕ} {p : ℕ} (hA : IsPrimitive A) (hpA : p ∉ A) :
    IsPrimitive ((fun a => a / p) '' {a ∈ A | p ∣ a}) := by
  refine ⟨quotients_set_ge_two_of_not_mem hA.1 hpA, ?_⟩
  rintro _ ⟨a, ⟨haA, hpa⟩, rfl⟩ _ ⟨b, ⟨hbA, hpb⟩, rfl⟩ hab
  have hdiv : a ∣ b := by
    rw [← Nat.div_mul_cancel hpa, ← Nat.div_mul_cancel hpb]
    exact Nat.mul_dvd_mul_right hab p
  rw [hA.2 a haA b hbA hdiv]

/-- Exponents `k` at which every prime compression strictly lowers `𝓜ₖ`: for every prime
`p` and primitive `T`, the running integrals of `u^{k-1}E_T(uᵖ)` are positive. -/
def Admissible (k : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ T : Set ℕ, IsPrimitive T →
    ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * ESetExt T (u ^ p)

theorem MSet_compressAtSet_lt {k : ℝ} (hk : 1 ≤ k) (hadm : Admissible k) {A : Set ℕ}
    {p : ℕ} (hp : p.Prime) (hA : IsPrimitive A) (hpA : p ∉ A) (_hmult : ∃ a ∈ A, p ∣ a)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c (compressAtSet p A) < MSet k c A := by
  have hB : ∀ b ∈ {a ∈ A | ¬ p ∣ a}, 2 ≤ b := fun b hb => hA.1 b hb.1
  have hTp := quotients_set_isPrimitive hA hpA
  have hpB : p ∉ {a ∈ A | ¬ p ∣ a} := fun h => h.2 (dvd_refl p)
  have h := MSet_block_exchange_lt hp.pos hB hTp.1 (disjoint_nonMultiples_block_set p A) hpB
    hk (hadm p hp _ hTp) hc
  rw [← block_decomp_set p A] at h
  exact h

/-- Adding a missing exponent strictly lowers `𝓜ₖ,c`. -/
theorem MSet_insert_lt {A : Set ℕ} {q : ℕ} (hq : q ∉ A) (hA1 : ∀ n ∈ A, 1 ≤ n) {k : ℝ}
    (hk : 1 ≤ k) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c (insert q A) < MSet k c A := by
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hI1 := intervalIntegrable_MSet (insert q A) hk hcI
  have hI2 := intervalIntegrable_MSet A hk hcI
  have hpos : 0 < ∫ u in (0 : ℝ)..c,
      (k * u ^ (k - 1) * qProdSet A u - k * u ^ (k - 1) * qProdSet (insert q A) u) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hI2.sub hI1) ?_ hc.1
    intro u hu
    have hu1 : u < 1 := hu.2.trans_le hc.2
    rw [qProdSet_insert hq hu.1.le hu1]
    have hP : 0 < qProdSet A u := qProdSet_pos_of_one_le A hA1 hu.1.le hu1
    have hpow : 0 < u ^ q := pow_pos hu.1 q
    have hw : 0 < k * u ^ (k - 1) := mul_pos (by linarith) (Real.rpow_pos_of_pos hu.1 _)
    have : k * u ^ (k - 1) * qProdSet A u - k * u ^ (k - 1) * ((1 - u ^ q) * qProdSet A u)
        = k * u ^ (k - 1) * (u ^ q * qProdSet A u) := by ring
    rw [this]
    positivity
  rw [intervalIntegral.integral_sub hI2 hI1] at hpos
  unfold MSet
  linarith

/-! ## Finite sets -/

theorem coe_compressAt (p : ℕ) (A : Finset ℕ) :
    ((compressAt p A : Finset ℕ) : Set ℕ) = compressAtSet p (A : Set ℕ) := by
  ext a
  simp [compressAt, compressAtSet]

/-- **Finite minimality at an admissible exponent.** -/
theorem MSet_primesLE_lt_of_admissible {k : ℝ} (hk : 1 ≤ k) (hadm : Admissible k) {N : ℕ}
    {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) := by
  refine descent_lt (J := fun S => MSet k c (S : Set ℕ)) ?_ ?_ hA hAN hne
  · intro A p hA hp hpA hmult
    simp only [coe_compressAt]
    exact MSet_compressAtSet_lt hk hadm hp hA hpA hmult hc
  · intro R q hq hR
    simp only [Finset.coe_insert]
    exact MSet_insert_lt (by simpa using hq) (fun n hn => hR n hn) hk hc

/-! ## Arbitrary sets -/

theorem tendsto_MSet_truncation (A : Set ℕ) [DecidablePred (· ∈ A)] {k : ℝ} (hk : 1 ≤ k)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun N => MSet k c (((Finset.range (N + 1)).filter (· ∈ A) : Finset ℕ) : Set ℕ))
      atTop (𝓝 (MSet k c A)) := by
  have h := tendsto_integral_qProd_truncation_mul A hc (continuous_rpow_weight hk)
  unfold MSet
  simp only [qProdSet_coe]
  convert h using 2
  · apply intervalIntegral.integral_congr; intro u _; ring
  · apply intervalIntegral.integral_congr; intro u _; ring

theorem primes_truncation [DecidablePred (· ∈ Primes)] (N : ℕ) :
    ((Finset.range (N + 1)).filter (· ∈ Primes) : Finset ℕ) = primesLE N := by
  ext a
  rw [Finset.mem_filter, primesLE, Finset.mem_filter]
  exact Iff.rfl

/-- **Lower bound at an admissible exponent:** `𝓜ₖ,c(𝒫) ≤ 𝓜ₖ,c(A)` for all primitive `A`. -/
theorem goodAt_of_admissible {k : ℝ} (hk : 1 ≤ k) (hadm : Admissible k) : GoodAt k := by
  classical
  intro A hA c hc
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hP := tendsto_MSet_truncation Primes hk hcI
  simp only [primes_truncation] at hP
  refine le_of_tendsto_of_tendsto' hP (tendsto_MSet_truncation A hk hcI) fun N => ?_
  by_cases h : (Finset.range (N + 1)).filter (· ∈ A) = primesLE N
  · rw [h]
  · exact (MSet_primesLE_lt_of_admissible hk hadm (truncation_isPrimitiveFin hA N)
      (truncation_bounded A N) h hc).le

/-- **Unique attainment at an admissible exponent.** -/
theorem MSet_primes_lt_of_admissible {k : ℝ} (hk : 1 ≤ k) (hadm : Admissible k) {A : Set ℕ}
    (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A := by
  have hgood := goodAt_of_admissible hk hadm
  by_cases hall : ∀ a ∈ A, Nat.Prime a
  · have hsub : A ⊆ Primes := fun a ha => hall a ha
    obtain ⟨q, hqP, hqA⟩ : ∃ q ∈ Primes, q ∉ A := by
      by_contra h
      push Not at h
      exact hne (Set.Subset.antisymm hsub h)
    have hall' : ∀ a ∈ insert q A, Nat.Prime a := by
      rintro a (rfl | ha)
      · exact hqP
      · exact hall a ha
    have hA' : IsPrimitive (insert q A) :=
      ⟨fun a ha => (hall' a ha).two_le,
       fun a ha b hb hab => (Nat.prime_dvd_prime_iff_eq (hall' a ha) (hall' b hb)).mp hab⟩
    exact lt_of_le_of_lt (hgood _ hA' c hc)
      (MSet_insert_lt hqA (fun n hn => (hall n hn).one_le) hk hc)
  · obtain ⟨m, hmA, hm_not_prime⟩ : ∃ m ∈ A, ¬ Nat.Prime m := by
      by_contra h
      push Not at h
      exact hall h
    obtain ⟨p, hp, hpm, hpA⟩ := exists_prime_factor_not_mem_set hA hmA hm_not_prime
    have hstep := MSet_compressAtSet_lt hk hadm hp hA hpA ⟨m, hmA, hpm⟩ hc
    exact lt_of_le_of_lt (hgood _ (compressAtSet_isPrimitive hA hp) c hc) hstep

/-! ## The bootstrap -/

/-- If minimality holds at every exponent in `[1, K]`, every `k ∈ [1, min(2K, 17/4)]` is
admissible: a prime `p < k` has `1 ≤ k/p ≤ k/2 ≤ K` and `k/p ≤ 17/8`. -/
theorem admissible_of_good {K : ℝ} (hK : ∀ s, 1 ≤ s → s ≤ K → GoodAt s) {k : ℝ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * K) (hk : k ≤ 17 / 4) : Admissible k := by
  intro p hp T hT y hy
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rcases le_or_gt k p with hkp | hpk
  · exact run_pos_of_le hT.1 hp.one_le hk1 hkp hy
  · have hpR : (0 : ℝ) < p := by linarith
    have hs1 : 1 ≤ k / p := by rw [le_div_iff₀ hpR]; linarith
    have hsK : k / p ≤ K := by
      rw [div_le_iff₀ hpR]; nlinarith
    have hs : k / p ≤ 17 / 8 := by
      rw [div_le_iff₀ hpR]; nlinarith
    exact run_pos_of_lt hT hp.one_le hpk.le hs (hK _ hs1 hsK) hy

theorem admissible_le_two {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 2) : Admissible k :=
  admissible_of_good (K := 1) (fun s hs1 hs => by
    intro T hT z hz
    have : s = 1 := le_antisymm hs hs1
    subst this
    rw [MSet_one, MSet_one]
    exact Lfun_le_FcSet hT hz) hk1 (by linarith) (by linarith)

theorem goodAt_le_two {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 2) : GoodAt k :=
  goodAt_of_admissible hk1 (admissible_le_two hk1 hk)

theorem goodAt_le_four {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 4) : GoodAt k :=
  goodAt_of_admissible hk1 (admissible_of_good (K := 2) (fun s hs1 hs => goodAt_le_two hs1 hs)
    hk1 (by linarith) (by linarith))

/-- **Every `k ∈ [1, 17/4]` is admissible.** -/
theorem admissible_le_seventeen_quarters {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 17 / 4) :
    Admissible k :=
  admissible_of_good (K := 4) (fun s hs1 hs => goodAt_le_four hs1 hs) hk1 (by linarith) hk

/-! ## Main theorems -/

/-- **Proposition 5.2 (finite form), `1 ≤ k ≤ 17/4`.** For real `1 ≤ k ≤ 17/4`, every primitive
`A ⊆ {2,…,N}` with `A ≠ 𝒫_N` and every `c ∈ (0,1]`:
`∫₀ᶜ k u^{k-1} P_{𝒫_N} < ∫₀ᶜ k u^{k-1} P_A`, i.e. `𝔼 min(Z_{𝒫_N}^k, c^k) < 𝔼 min(Z_A^k, c^k)`. -/
theorem MSet_primesLE_lt {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 17 / 4) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) :=
  MSet_primesLE_lt_of_admissible hk1 (admissible_le_seventeen_quarters hk1 hk) hA hAN hne hc

/-- **Proposition 5.2 (all primitive sets), `1 ≤ k ≤ 17/4`.** For real `1 ≤ k ≤ 17/4`, every
primitive `A ≠ 𝒫`, finite or infinite, and every `c ∈ (0,1]`: `𝓜ₖ,c(𝒫) < 𝓜ₖ,c(A)`. -/
theorem MSet_primes_lt {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 17 / 4) {A : Set ℕ}
    (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A :=
  MSet_primes_lt_of_admissible hk1 (admissible_le_seventeen_quarters hk1 hk) hA hne hc

end RntPaper
