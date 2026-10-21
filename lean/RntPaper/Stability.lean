import RntPaper.Ambient
import RntPaper.Qfun
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-!
# Stability of `Λ`: omitting a prime

For a prime `p` let `B_p = (𝒫 ∖ {p}) ∪ {p²}` (`omitSet p`).

* `minElems_omit`: `B_p` is the set of divisibility-minimal elements of `{2,3,…} ∖ {p}`;
  by Theorem 4.1 (`FcSet_minElems_le/lt`), `B_p` is the unique minimizer of `F_c` among
  primitive sets avoiding `p` (`FcSet_omitSet_le`, `FcSet_omitSet_lt`).
* `FcSet_omitSet_eq`: `F_c(B_p) = 𝓛(c) + D_c(p)` with the cost
  `D_c(p) = ∑_{j=1}^{p-1} ∫₀ᶜ x^{jp} Q(x) dx` (`omitCost`), since
  `P_{B_p} = Q · (1 - x^{p²})/(1 - xᵖ) = Q · ∑_{j<p} x^{jp}` on `[0,1)`.
* `D_c(p) ≥ Δ_c(p) = ∫₀ᶜ xᵖ Q(x) dx > 0` (`omitMoment`), with equality at `p = 2`;
  `Δ_c` is antitone in `p`.
* Consequences: a primitive `A` with `F_1(A) - Λ < Δ_1(p)` for all primes `p ≤ R` agrees
  with the primes on `[0,R]` (`eq_primes_of_lt`), and `F_1(A_j) → Λ` iff every prime
  eventually lies in `A_j` (`tendsto_FcSet_iff`).
-/

namespace RntPaper

open QProduct MeasureTheory Filter Topology Set

/-! ## The minimizer avoiding a prime -/

/-- `B_p = (𝒫 ∖ {p}) ∪ {p²}`. -/
def omitSet (p : ℕ) : Set ℕ := insert (p ^ 2) (Primes \ {p})

/-- The divisibility-minimal elements of `{2,3,…} ∖ {p}` are `B_p`. -/
theorem minElems_omit {p : ℕ} (hp : p.Prime) : minElems ({n | 2 ≤ n} \ {p}) = omitSet p := by
  have hp2 := hp.two_le
  have hsqU : 2 ≤ p ^ 2 ∧ p ^ 2 ≠ p := by
    refine ⟨by nlinarith, fun h => ?_⟩
    rw [pow_two] at h
    nlinarith
  ext u
  simp only [minElems, omitSet, Primes, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨⟨hu2, hup⟩, hmin⟩
    by_cases hu : u.Prime
    · exact Or.inr ⟨hu, hup⟩
    · left
      obtain ⟨q, hq, hqu⟩ := Nat.exists_prime_and_dvd (show u ≠ 1 by omega)
      have hqne : q ≠ u := fun h => hu (h ▸ hq)
      have hqp : q = p := by
        by_contra hqp
        exact hqne (hmin q ⟨hq.two_le, hqp⟩ hqu)
      subst hqp
      obtain ⟨m, rfl⟩ := hqu
      have hm2 : 2 ≤ m := by
        rcases m with _ | _ | m
        · simp at hu2
        · simp at hup
        · omega
      obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
      have hru : r ∣ q * m := Dvd.dvd.mul_left hrm q
      have hrne : r ≠ q * m := fun h => hu (h ▸ hr)
      have hrq : r = q := by
        by_contra h
        exact hrne (hmin r ⟨hr.two_le, h⟩ hru)
      subst hrq
      have hsq : r ^ 2 ∣ r * m := by rw [pow_two]; exact Nat.mul_dvd_mul_left r hrm
      exact (hmin _ hsqU hsq).symm
  · rintro (rfl | ⟨hu, hup⟩)
    · refine ⟨hsqU, fun d ⟨hd2, hdp⟩ hd => ?_⟩
      obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
      interval_cases k
      · simp at hd2
      · simp at hdp
      · rfl
    · refine ⟨⟨hu.two_le, hup⟩, fun d ⟨hd2, _⟩ hd => ?_⟩
      rcases (Nat.dvd_prime hu).mp hd with rfl | h
      · omega
      · exact h

theorem omit_ge_two {p : ℕ} : ∀ u ∈ ({n | 2 ≤ n} \ {p} : Set ℕ), 2 ≤ u :=
  fun _ hu => hu.1

theorem omitSet_isPrimitive {p : ℕ} (hp : p.Prime) : IsPrimitive (omitSet p) := by
  rw [← minElems_omit hp]
  exact minElems_isPrimitive omit_ge_two

theorem subset_omit_of_not_mem {p : ℕ} {A : Set ℕ} (hA : IsPrimitive A) (hpA : p ∉ A) :
    A ⊆ {n | 2 ≤ n} \ {p} :=
  fun a ha => ⟨hA.1 a ha, fun h => hpA (Set.mem_singleton_iff.mp h ▸ ha)⟩

/-- `B_p` minimizes `F_c` among primitive sets avoiding `p`. -/
theorem FcSet_omitSet_le {p : ℕ} (hp : p.Prime) {A : Set ℕ} (hA : IsPrimitive A) (hpA : p ∉ A)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : FcSet c (omitSet p) ≤ FcSet c A := by
  rw [← minElems_omit hp]
  exact FcSet_minElems_le omit_ge_two hA (subset_omit_of_not_mem hA hpA) hc

/-- `B_p` is the unique minimizer of `F_c` among primitive sets avoiding `p`. -/
theorem FcSet_omitSet_lt {p : ℕ} (hp : p.Prime) {A : Set ℕ} (hA : IsPrimitive A) (hpA : p ∉ A)
    (hne : A ≠ omitSet p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    FcSet c (omitSet p) < FcSet c A := by
  rw [← minElems_omit hp] at hne ⊢
  exact FcSet_minElems_lt omit_ge_two hA (subset_omit_of_not_mem hA hpA) hne hc

/-! ## The cost of omitting `p` -/

/-- `Δ_c(p) = ∫₀ᶜ xᵖ Q(x) dx`. -/
noncomputable def omitMoment (p : ℕ) (c : ℝ) : ℝ := ∫ u in (0 : ℝ)..c, u ^ p * Qfun u

/-- `D_c(p) = ∑_{j=1}^{p-1} ∫₀ᶜ x^{jp} Q(x) dx`. -/
noncomputable def omitCost (p : ℕ) (c : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 p, ∫ u in (0 : ℝ)..c, u ^ (j * p) * Qfun u

theorem intervalIntegrable_pow_mul_Qfun (k : ℕ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => u ^ k * Qfun u) volume 0 c :=
  (intervalIntegrable_qProdSet Primes hc).continuousOn_mul (continuous_pow k).continuousOn

theorem Qfun_pos {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : 0 < Qfun u :=
  qProdSet_pos_of_one_le Primes (fun _ hn => (show Nat.Prime _ from hn).one_le) h0 h1

theorem Qfun_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : 0 ≤ Qfun u :=
  qProdSet_nonneg Primes hu

/-- `P_{B_p} = Q · ∑_{j<p} x^{jp}` on `[0,1)`. -/
theorem qProdSet_omitSet {p : ℕ} (hp : p.Prime) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    qProdSet (omitSet p) u = Qfun u + ∑ j ∈ Finset.Ico 1 p, u ^ (j * p) * Qfun u := by
  have hsq : p ^ 2 ∉ Primes \ {p} := fun h => Nat.Prime.not_prime_pow (le_refl 2) h.1
  have hpP : p ∉ Primes \ {p} := fun h => h.2 rfl
  have hQ : Qfun u = (1 - u ^ p) * qProdSet (Primes \ {p}) u := by
    unfold Qfun
    rw [← qProdSet_insert hpP h0 h1, Set.insert_sdiff_singleton,
      Set.insert_eq_of_mem (show p ∈ Primes from hp)]
  unfold omitSet
  rw [qProdSet_insert hsq h0 h1, ← Finset.sum_mul, hQ]
  have hgeom := geom_sum_mul (u ^ p) p
  have hsum : ∑ i ∈ Finset.range p, (u ^ p) ^ i = 1 + ∑ j ∈ Finset.Ico 1 p, u ^ (j * p) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
    simp only [pow_zero, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_comm]
  have hpow : (u ^ p) ^ p = u ^ (p ^ 2) := by rw [← pow_mul, pow_two]
  rw [hsum, hpow] at hgeom
  linear_combination (qProdSet (Primes \ {p}) u) * hgeom

theorem ae_ne_one : ∀ᵐ u : ℝ ∂volume, u ≠ (1 : ℝ) := by
  have hz : volume ({(1:ℝ)} : Set ℝ) = 0 := measure_singleton _
  exact (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hz).mono fun u hu => by simpa using hu

/-- **Cost formula.** `F_c(B_p) = 𝓛(c) + D_c(p)`. -/
theorem FcSet_omitSet_eq {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    FcSet c (omitSet p) = Lfun c + omitCost p c := by
  have hcongr : FcSet c (omitSet p) =
      ∫ u in (0 : ℝ)..c, (Qfun u + ∑ j ∈ Finset.Ico 1 p, u ^ (j * p) * Qfun u) := by
    unfold FcSet
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_one] with u hu1 hu
    rw [Set.uIoc_of_le hc.1] at hu
    exact qProdSet_omitSet hp hu.1.le (lt_of_le_of_ne (hu.2.trans hc.2) hu1)
  have h1 : IntervalIntegrable Qfun volume 0 c := intervalIntegrable_qProdSet Primes hc
  have h2 : IntervalIntegrable (fun u => ∑ j ∈ Finset.Ico 1 p, u ^ (j * p) * Qfun u)
      volume 0 c := by
    have := IntervalIntegrable.sum (Finset.Ico 1 p)
      (fun j _ => intervalIntegrable_pow_mul_Qfun (j * p) hc)
    convert this using 1
    funext u
    simp [Finset.sum_apply]
  rw [hcongr, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_finsetSum (fun j _ => intervalIntegrable_pow_mul_Qfun _ hc),
    Lfun_eq_integral_Qfun]
  rfl

theorem omitMoment_pos {p : ℕ} {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : 0 < omitMoment p c := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_pow_mul_Qfun p ⟨hc.1.le, hc.2⟩) (fun u hu => ?_) hc.1
  exact mul_pos (pow_pos hu.1 p) (Qfun_pos hu.1.le (hu.2.trans_le hc.2))

theorem integral_pow_mul_Qfun_nonneg (k : ℕ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    0 ≤ ∫ u in (0 : ℝ)..c, u ^ k * Qfun u :=
  intervalIntegral.integral_nonneg hc.1 fun _ hu =>
    mul_nonneg (pow_nonneg hu.1 k) (Qfun_nonneg ⟨hu.1, hu.2.trans hc.2⟩)

theorem omitMoment_le_omitCost {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    omitMoment p c ≤ omitCost p c := by
  unfold omitCost
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨le_rfl, hp.one_lt⟩
  have := Finset.single_le_sum (f := fun j => ∫ u in (0 : ℝ)..c, u ^ (j * p) * Qfun u)
    (fun j _ => integral_pow_mul_Qfun_nonneg _ hc) h1
  simpa [omitMoment] using this

theorem omitCost_two (c : ℝ) : omitCost 2 c = omitMoment 2 c := by
  simp [omitCost, omitMoment]

theorem omitMoment_antitone {p q : ℕ} (hpq : p ≤ q) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    omitMoment q c ≤ omitMoment p c :=
  intervalIntegral.integral_mono_on hc.1 (intervalIntegrable_pow_mul_Qfun q hc)
    (intervalIntegrable_pow_mul_Qfun p hc) fun _ hu =>
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hu.1 (hu.2.trans hc.2) hpq)
        (Qfun_nonneg ⟨hu.1, hu.2.trans hc.2⟩)

/-- Omitting `p` costs at least `D_c(p)`. -/
theorem omitCost_le_FcSet_sub {p : ℕ} (hp : p.Prime) {A : Set ℕ} (hA : IsPrimitive A)
    (hpA : p ∉ A) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : omitCost p c ≤ FcSet c A - Lfun c := by
  have h := FcSet_omitSet_le hp hA hpA hc
  rw [FcSet_omitSet_eq hp ⟨hc.1.le, hc.2⟩] at h
  linarith

theorem omitMoment_le_FcSet_sub {p : ℕ} (hp : p.Prime) {A : Set ℕ} (hA : IsPrimitive A)
    (hpA : p ∉ A) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : omitMoment p c ≤ FcSet c A - Lfun c :=
  (omitMoment_le_omitCost hp ⟨hc.1.le, hc.2⟩).trans (omitCost_le_FcSet_sub hp hA hpA hc)

/-! ## Consequences -/

/-- **Threshold.** If `F_1(A) - Λ < Δ_1(p)` for every prime `p ≤ R`, then
`A ∩ [0,R]` is exactly the set of primes `≤ R`. -/
theorem eq_primes_of_lt {A : Set ℕ} (hA : IsPrimitive A) {R : ℕ}
    (h : ∀ p, p.Prime → p ≤ R → FcSet 1 A - Lfun 1 < omitMoment p 1) :
    ∀ n ≤ R, (n ∈ A ↔ n.Prime) := by
  have hc : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  have hprime : ∀ p, p.Prime → p ≤ R → p ∈ A := by
    intro p hp hpR
    by_contra hpA
    exact absurd (omitMoment_le_FcSet_sub hp hA hpA hc) (not_le.mpr (h p hp hpR))
  intro n hnR
  refine ⟨fun hnA => ?_, fun hn => hprime n hn hnR⟩
  by_contra hn
  obtain ⟨q, hq, hqn, hqA⟩ := exists_prime_factor_not_mem_set hA hnA hn
  exact hqA (hprime q hq ((Nat.le_of_dvd (by have := hA.1 n hnA; omega) hqn).trans hnR))

/-- Pointwise convergence of the products when membership converges pointwise. -/
theorem tendsto_qProdSet_of_eventually {ι : Type*} {l : Filter ι} (A : ι → Set ℕ) (B : Set ℕ)
    (hev : ∀ n, ∀ᶠ j in l, (n ∈ A j ↔ n ∈ B)) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Tendsto (fun j => qProdSet (A j) u) l (𝓝 (qProdSet B u)) := by
  simp only [qProdSet_eq_tprod_mulIndicator, mulIndicator_eq_one_add_indicator]
  refine tendsto_tprod_one_add_of_dominated_convergence (bound := fun n => u ^ n)
    (summable_geometric_of_lt_one h0 h1) (fun n => ?_) (Eventually.of_forall fun j n => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev n] with j hj
    by_cases hn : n ∈ B
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem (hj.mpr hn)]
    · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem (fun h => hn (hj.mp h))]
  · by_cases hn : n ∈ A j
    · rw [Set.indicator_of_mem hn, norm_neg, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 n)]
    · rw [Set.indicator_of_notMem hn, norm_zero]
      exact pow_nonneg h0 n

/-- **Convergence criterion.** For primitive `A_j`, `F_1(A_j) → Λ` iff every prime eventually
lies in `A_j`. -/
theorem tendsto_FcSet_iff (A : ℕ → Set ℕ) (hA : ∀ j, IsPrimitive (A j)) :
    Tendsto (fun j => FcSet 1 (A j)) atTop (𝓝 (Lfun 1)) ↔
      ∀ p, p.Prime → ∀ᶠ j in atTop, p ∈ A j := by
  have hc : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  constructor
  · intro h p hp
    by_contra hfreq
    rw [Filter.not_eventually] at hfreq
    have hev := h.eventually
      (gt_mem_nhds (lt_add_of_pos_right (Lfun 1) (omitMoment_pos (p := p) hc)))
    obtain ⟨j, hj, hjlt⟩ := (hfreq.and_eventually hev).exists
    have := omitMoment_le_FcSet_sub hp (hA j) hj hc
    linarith
  · intro h
    have hev : ∀ n : ℕ, ∀ᶠ j in atTop, (n ∈ A j ↔ n ∈ Primes) := by
      intro n
      by_cases hn : n.Prime
      · filter_upwards [h n hn] with j hj
        exact ⟨fun _ => hn, fun _ => hj⟩
      · refine (show ∀ᶠ j in atTop, n ∉ A j from ?_).mono fun j hj =>
          ⟨fun h' => absurd h' hj, fun h' => absurd h' hn⟩
        by_cases hn2 : n < 2
        · exact Eventually.of_forall fun j h' => absurd ((hA j).1 n h') (by omega)
        · obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
          filter_upwards [h q hq] with j hj hnA
          exact hn ((hA j).2 q hj n hnA hqn ▸ hq)
    rw [← FcSet_primes]
    unfold FcSet
    simp only [intervalIntegral.integral_of_le zero_le_one]
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun _ => (1 : ℝ))
      (fun j => aestronglyMeasurable_qProdSet_restrict (A j) le_rfl)
      (MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne) (fun j => ?_) ?_
    · have hmem : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ∈ Set.Ioc (0:ℝ) 1 :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hmem, ae_restrict_ne_one (Set.Ioc (0:ℝ) 1)] with u hu hu1
      have h1 : u < 1 := lt_of_le_of_ne hu.2 hu1
      rw [Real.norm_eq_abs, abs_of_nonneg (qProdSet_nonneg _ ⟨hu.1.le, h1.le⟩)]
      exact qProdSet_le_one _ hu.1.le h1
    · have hmem : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ∈ Set.Ioc (0:ℝ) 1 :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hmem, ae_restrict_ne_one (Set.Ioc (0:ℝ) 1)] with u hu hu1
      exact tendsto_qProdSet_of_eventually A Primes hev hu.1.le (lt_of_le_of_ne hu.2 hu1)

end RntPaper
