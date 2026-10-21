import RntPaper.Transport

/-!
# The extremality theorems (paper §4)

Finite case: port of productinvariants `Finite/Antichain.lean`
(`compressAt`, descent by element sum, `antichain_descends_to_allPrime`),
now carrying the truncation level `c` and the strictness of the first step.

Infinite case: lower bound by truncation + dominated convergence (the
general-predicate bridge `sInf_F_filter_eq_integral_tprod` in LeanCert is the
`c = 1` instance), uniqueness by one strict exchange followed by the lower bound.
-/

namespace RntPaper

open QProduct MeasureTheory Filter Topology Set

/-! ## Combinatorics of `compressAt` and `quotients` (port of `Antichain.lean`) -/

theorem mem_compressAt {p a : ℕ} {A : Finset ℕ} :
    a ∈ compressAt p A ↔ a = p ∨ (a ∈ A ∧ ¬ p ∣ a) := by
  unfold compressAt
  rw [Finset.mem_insert, Finset.mem_filter]

theorem mem_quotients {p t : ℕ} {A : Finset ℕ} :
    t ∈ quotients p A ↔ ∃ a ∈ A, p ∣ a ∧ a / p = t := by
  unfold quotients
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨haA, hpa⟩, rfl⟩; exact ⟨a, haA, hpa, rfl⟩
  · rintro ⟨a, haA, hpa, rfl⟩; exact ⟨a, ⟨haA, hpa⟩, rfl⟩

/-- The multiples of `p` in `A` are the `p`-scalings of the quotients. -/
theorem multiples_eq_image_quotients (p : ℕ) (A : Finset ℕ) :
    A.filter (fun a => p ∣ a) = (quotients p A).image (· * p) := by
  unfold quotients
  ext a
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨haA, hpa⟩
    exact ⟨a / p, ⟨a, ⟨haA, hpa⟩, rfl⟩, Nat.div_mul_cancel hpa⟩
  · rintro ⟨q, ⟨b, ⟨hbA, hpb⟩, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rwa [Nat.div_mul_cancel hpb]
    · rw [Nat.div_mul_cancel hpb]; exact hpb

/-- `A` splits as its non-multiples of `p` together with the scaled quotient block. -/
theorem block_decomp (p : ℕ) (A : Finset ℕ) :
    A = A.filter (fun a => ¬ p ∣ a) ∪ (quotients p A).image (· * p) := by
  rw [← multiples_eq_image_quotients, Finset.union_comm,
    Finset.filter_union_filter_not_eq (fun a => p ∣ a) A]

theorem disjoint_nonMultiples_block (p : ℕ) (A : Finset ℕ) :
    Disjoint (A.filter (fun a => ¬ p ∣ a)) ((quotients p A).image (· * p)) := by
  rw [← multiples_eq_image_quotients]
  exact (Finset.disjoint_filter_filter_not A A (fun a => p ∣ a)).symm

theorem prime_not_mem_nonMultiples (p : ℕ) (A : Finset ℕ) :
    p ∉ A.filter (fun a => ¬ p ∣ a) := by
  rw [Finset.mem_filter]; rintro ⟨_, h⟩; exact h (dvd_refl p)

/-- If every element of `A` is `≥ 2` and `p ∉ A`, every quotient `a/p` is `≥ 2`. -/
theorem quotients_ge_two_of_not_mem {p : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hp_not_mem : p ∉ A) :
    ∀ t ∈ quotients p A, 2 ≤ t := by
  intro t ht
  obtain ⟨a, haA, hpa, rfl⟩ := mem_quotients.mp ht
  have ha2 : 2 ≤ a := hpos a haA
  have hane : a ≠ p := fun h => hp_not_mem (h ▸ haA)
  have hrec : a / p * p = a := Nat.div_mul_cancel hpa
  by_contra hlt
  rw [not_le] at hlt
  interval_cases h : (a / p) <;> omega

/-! ## Compression preserves primitivity and lowers `F_c` -/

theorem compressAt_isPrimitiveFin {A : Finset ℕ} {p : ℕ} (hA : IsPrimitiveFin A)
    (hp : Nat.Prime p) (_hmult : ∃ a ∈ A, p ∣ a) :
    IsPrimitiveFin (compressAt p A) := by
  obtain ⟨h2, hac⟩ := hA
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · rcases mem_compressAt.mp (Finset.mem_coe.mp ha) with rfl | ⟨haA, _⟩
    · exact hp.two_le
    · exact h2 a haA
  · rcases mem_compressAt.mp (Finset.mem_coe.mp ha) with rfl | ⟨haA, hpa⟩ <;>
      rcases mem_compressAt.mp (Finset.mem_coe.mp hb) with rfl | ⟨hbA, hpb⟩
    · rfl
    · exact absurd hab hpb
    · rcases (Nat.dvd_prime hp).mp hab with h1 | h
      · have := h2 a haA; omega
      · exact h
    · exact hac a haA b hbA hab

theorem compressAt_bounded {A : Finset ℕ} {N p : ℕ} (hA : IsPrimitiveFin A)
    (hAN : ∀ a ∈ A, a ≤ N)
    (hmult : ∃ a ∈ A, p ∣ a) : ∀ a ∈ compressAt p A, a ≤ N := by
  intro a ha
  obtain ⟨m, hmA, hpm⟩ := hmult
  have hm2 : 2 ≤ m := hA.1 m hmA
  have hpm' : p ≤ m := Nat.le_of_dvd (by omega) hpm
  rcases mem_compressAt.mp ha with rfl | ⟨haA, _⟩
  · exact hpm'.trans (hAN m hmA)
  · exact hAN a haA

/-- The compression strictly lowers the element sum (termination measure). -/
theorem sum_compressAt_lt {A : Finset ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hA : IsPrimitiveFin A) (hpA : p ∉ A) (hmult : ∃ a ∈ A, p ∣ a) :
    (compressAt p A).sum id < A.sum id := by
  classical
  obtain ⟨m, hmA, hpm⟩ := hmult
  have hp2 : 2 ≤ p := hp
  have hm2 : 2 ≤ m := hA.1 m hmA
  have hmne : m ≠ p := fun h => hpA (h ▸ hmA)
  have hm2p : 2 * p ≤ m := by
    obtain ⟨t, rfl⟩ := hpm
    have ht2 : 2 ≤ t := by
      by_contra h
      push Not at h
      interval_cases t <;> omega
    nlinarith
  have hcomp : (compressAt p A).sum id = p + (A.filter (fun a => ¬ p ∣ a)).sum id := by
    unfold compressAt
    rw [Finset.sum_insert (prime_not_mem_nonMultiples p A)]
    rfl
  have hsplit : A.sum id
      = (A.filter (fun a => p ∣ a)).sum id + (A.filter (fun a => ¬ p ∣ a)).sum id :=
    (Finset.sum_filter_add_sum_filter_not A (fun a => p ∣ a) id).symm
  have hblock : m ≤ (A.filter (fun a => p ∣ a)).sum id :=
    Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i)
      (Finset.mem_filter.mpr ⟨hmA, hpm⟩)
  rw [hcomp, hsplit]
  omega

/-- Strict compression (Proposition 3.4 applied to `B = {a ∈ A : p ∤ a}`,
`T = quotients p A`), for any positive integer `p`. -/
theorem Fc_compressAt_lt {A : Finset ℕ} {p : ℕ} (hp : 0 < p)
    (hA : IsPrimitiveFin A) (hpA : p ∉ A) (hmult : ∃ a ∈ A, p ∣ a)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fc c (compressAt p A) < Fc c A := by
  have hB : ∀ b ∈ A.filter (fun a => ¬ p ∣ a), 2 ≤ b :=
    fun b hb => hA.1 b (Finset.mem_filter.mp hb).1
  have hT : ∀ t ∈ quotients p A, 2 ≤ t := quotients_ge_two_of_not_mem hA.1 hpA
  have hTne : (quotients p A).Nonempty := by
    obtain ⟨m, hmA, hpm⟩ := hmult
    exact ⟨m / p, mem_quotients.mpr ⟨m, hmA, hpm, rfl⟩⟩
  have h := block_exchange_lt hp hB hT hTne (disjoint_nonMultiples_block p A)
    (prime_not_mem_nonMultiples p A) hc
  rw [← block_decomp p A] at h
  exact h

/-- Adding a missing prime strictly lowers `F_c`. -/
theorem Fc_insert_lt {R : Finset ℕ} {q : ℕ} (hq : q ∉ R) (hR : ∀ n ∈ R, 1 ≤ n)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fc c (insert q R) < Fc c R := by
  unfold Fc
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hc.1
    (qProd_continuous _).continuousOn (qProd_continuous _).continuousOn ?_ ?_
  · intro u hu
    exact qProd_antitone_pointwise (Finset.subset_insert q R) ⟨hu.1.le, hu.2.trans hc.2⟩
  · refine ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.1]⟩, ?_⟩
    have hu : c / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.1, hc.2]⟩
    rw [qProd_insert hq]
    have hP : 0 < qProd R (c / 2) := qProd_pos_of_mem_Ioo hR hu
    have hfac : 1 - (c / 2) ^ q < 1 := by
      have hpow : (0 : ℝ) < (c / 2) ^ q := pow_pos hu.1 q
      linarith
    calc (1 - (c / 2) ^ q) * qProd R (c / 2)
        < 1 * qProd R (c / 2) := mul_lt_mul_of_pos_right hfac hP
      _ = qProd R (c / 2) := one_mul _

/-! ## Theorem 1.1 -/

/-- A composite element `m` of a primitive set has a prime factor `p ∉ A`. -/
theorem exists_prime_factor_not_mem {A : Finset ℕ} (hA : IsPrimitiveFin A)
    {m : ℕ} (hmA : m ∈ A) (hm_not_prime : ¬ Nat.Prime m) :
    ∃ p, Nat.Prime p ∧ p ∣ m ∧ p ∉ A := by
  have hm2 : 2 ≤ m := hA.1 m hmA
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hpne : p ≠ m := by rintro rfl; exact hm_not_prime hp
  exact ⟨p, hp, hpm, fun hpA => hpne (hA.2 p hpA m hmA hpm)⟩

/-- An all-prime set bounded by `N` is contained in `primesLE N`. -/
theorem allPrime_subset_primesLE {N : ℕ} {A : Finset ℕ} (hall : ∀ a ∈ A, Nat.Prime a)
    (hAN : ∀ a ∈ A, a ≤ N) : A ⊆ primesLE N :=
  fun a ha => mem_primesLE.mpr ⟨hall a ha, hAN a ha⟩

/-- Descent (sum-measure form): strong induction on the element sum. -/
theorem Fc_primesLE_lt_aux (N : ℕ) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    ∀ (s : ℕ) (A : Finset ℕ), A.sum id ≤ s → IsPrimitiveFin A → (∀ a ∈ A, a ≤ N) →
      A ≠ primesLE N → Fc c (primesLE N) < Fc c A := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro A hsum hA hAN hne
    by_cases hall : ∀ a ∈ A, Nat.Prime a
    · -- all-prime: `A ⊊ primesLE N`; insert one missing prime and use antitonicity.
      have hsub : A ⊆ primesLE N := allPrime_subset_primesLE hall hAN
      obtain ⟨q, hqP, hqA⟩ : ∃ q ∈ primesLE N, q ∉ A := by
        by_contra h
        push Not at h
        exact hne (Finset.Subset.antisymm hsub h)
      have h1 : Fc c (primesLE N) ≤ Fc c (insert q A) :=
        Fc_antitone ⟨hc.1.le, hc.2⟩ (Finset.insert_subset hqP hsub)
      have h2 : Fc c (insert q A) < Fc c A :=
        Fc_insert_lt hqA (fun n hn => (hall n hn).one_le) hc
      exact lt_of_le_of_lt h1 h2
    · -- composite element `m`, prime factor `p ∉ A`: compress and recurse.
      obtain ⟨m, hmA, hm_not_prime⟩ : ∃ m ∈ A, ¬ Nat.Prime m := by
        by_contra h
        push Not at h
        exact hall h
      obtain ⟨p, hp, hpm, hpA⟩ := exists_prime_factor_not_mem hA hmA hm_not_prime
      have hmult : ∃ a ∈ A, p ∣ a := ⟨m, hmA, hpm⟩
      have hstep : Fc c (compressAt p A) < Fc c A := Fc_compressAt_lt hp.pos hA hpA hmult hc
      by_cases hCeq : compressAt p A = primesLE N
      · rw [← hCeq]; exact hstep
      · have hA' : IsPrimitiveFin (compressAt p A) := compressAt_isPrimitiveFin hA hp hmult
        have hAN' : ∀ a ∈ compressAt p A, a ≤ N := compressAt_bounded hA hAN hmult
        have hsum' : (compressAt p A).sum id < A.sum id :=
          sum_compressAt_lt hp.two_le hA hpA hmult
        have hbound : (compressAt p A).sum id < s := lt_of_lt_of_le hsum' hsum
        exact lt_trans (ih _ hbound (compressAt p A) le_rfl hA' hAN' hCeq) hstep

/-- **Theorem 1.1 (unique finite minimizer).** For primitive `A ⊆ {2,…,N}`,
`A ≠ 𝒫_N`, and every `c ∈ (0,1]`: `F_c(𝒫_N) < F_c(A)`. -/
theorem Fc_primesLE_lt {N : ℕ} {A : Finset ℕ} (hA : IsPrimitiveFin A)
    (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fc c (primesLE N) < Fc c A :=
  Fc_primesLE_lt_aux N hc (A.sum id) A le_rfl hA hAN hne

theorem Fc_primesLE_le {N : ℕ} {A : Finset ℕ} (hA : IsPrimitiveFin A)
    (hAN : ∀ a ∈ A, a ≤ N) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fc c (primesLE N) ≤ Fc c A := by
  by_cases h : A = primesLE N
  · rw [h]
  · exact (Fc_primesLE_lt hA hAN h hc).le

/-! ## Theorem 1.2 -/

/-- The truncations of a primitive set are finite primitive sets. -/
theorem truncation_isPrimitiveFin {A : Set ℕ} [DecidablePred (· ∈ A)] (hA : IsPrimitive A)
    (N : ℕ) : IsPrimitiveFin ((Finset.range (N + 1)).filter (· ∈ A)) := by
  refine ⟨fun a ha => hA.1 a ?_, fun a ha b hb hab => hA.2 a ?_ b ?_ hab⟩
  · exact (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
  · exact (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
  · exact (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2

theorem truncation_bounded (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    ∀ a ∈ (Finset.range (N + 1)).filter (· ∈ A), a ≤ N := by
  intro a ha
  have := (Finset.mem_filter.mp ha).1
  rw [Finset.mem_range] at this
  omega

/-- **Theorem 1.2, lower bound.** `𝓛(c) ≤ F_c(A)` for every primitive `A`. -/
theorem Lfun_le_FcSet {A : Set ℕ} (hA : IsPrimitive A) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) : Lfun c ≤ FcSet c A := by
  classical
  refine le_of_tendsto_of_tendsto' (tendsto_Fc_primesLE ⟨hc.1.le, hc.2⟩)
    (tendsto_Fc_truncation A ⟨hc.1.le, hc.2⟩) fun N => ?_
  exact Fc_primesLE_le (truncation_isPrimitiveFin hA N) (truncation_bounded A N) hc

/-! ### Inserting a missing exponent (set version of `Fc_insert_lt`) -/

/-- Adding a missing exponent strictly lowers `F_c` (arbitrary sets). -/
theorem FcSet_insert_lt {A : Set ℕ} {q : ℕ} (hq : q ∉ A) (hA1 : ∀ n ∈ A, 1 ≤ n)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : FcSet c (insert q A) < FcSet c A := by
  have hI1 := intervalIntegrable_qProdSet (insert q A) ⟨hc.1.le, hc.2⟩
  have hI2 := intervalIntegrable_qProdSet A ⟨hc.1.le, hc.2⟩
  have hpos : 0 < ∫ u in (0:ℝ)..c, (qProdSet A u - qProdSet (insert q A) u) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hI2.sub hI1) ?_ hc.1
    intro u hu
    have hu1 : u < 1 := hu.2.trans_le hc.2
    rw [qProdSet_insert hq hu.1.le hu1]
    have hP : 0 < qProdSet A u := qProdSet_pos_of_one_le A hA1 hu.1.le hu1
    have hpow : 0 < u ^ q := pow_pos hu.1 q
    nlinarith
  rw [intervalIntegral.integral_sub hI2 hI1] at hpos
  unfold FcSet
  linarith

/-! ### Set-level compression combinatorics -/

/-- A composite element `m` of a primitive set has a prime factor `p ∉ A`. -/
theorem exists_prime_factor_not_mem_set {A : Set ℕ} (hA : IsPrimitive A)
    {m : ℕ} (hmA : m ∈ A) (hm_not_prime : ¬ Nat.Prime m) :
    ∃ p, Nat.Prime p ∧ p ∣ m ∧ p ∉ A := by
  have hm2 : 2 ≤ m := hA.1 m hmA
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hpne : p ≠ m := by rintro rfl; exact hm_not_prime hp
  exact ⟨p, hp, hpm, fun hpA => hpne (hA.2 p hpA m hmA hpm)⟩

theorem compressAtSet_isPrimitive {A : Set ℕ} {p : ℕ} (hA : IsPrimitive A)
    (hp : Nat.Prime p) : IsPrimitive (compressAtSet p A) := by
  obtain ⟨h2, hac⟩ := hA
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · rcases ha with rfl | ⟨haA, _⟩
    · exact hp.two_le
    · exact h2 a haA
  · rcases ha with rfl | ⟨haA, hpa⟩ <;> rcases hb with rfl | ⟨hbA, hpb⟩
    · rfl
    · exact absurd hab hpb
    · rcases (Nat.dvd_prime hp).mp hab with h1 | h
      · have := h2 a haA; omega
      · exact h
    · exact hac a haA b hbA hab

/-- `A` splits as its non-multiples of `p` together with the scaled quotients. -/
theorem block_decomp_set (p : ℕ) (A : Set ℕ) :
    A = {a ∈ A | ¬ p ∣ a} ∪ (· * p) '' ((fun a => a / p) '' {a ∈ A | p ∣ a}) := by
  ext a
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image, exists_exists_and_eq_and]
  constructor
  · intro haA
    by_cases hpa : p ∣ a
    · exact Or.inr ⟨a, ⟨haA, hpa⟩, Nat.div_mul_cancel hpa⟩
    · exact Or.inl ⟨haA, hpa⟩
  · rintro (⟨haA, _⟩ | ⟨b, ⟨hbA, hpb⟩, rfl⟩)
    · exact haA
    · rwa [Nat.div_mul_cancel hpb]

theorem disjoint_nonMultiples_block_set (p : ℕ) (A : Set ℕ) :
    Disjoint {a ∈ A | ¬ p ∣ a} ((· * p) '' ((fun a => a / p) '' {a ∈ A | p ∣ a})) := by
  rw [Set.disjoint_left]
  rintro b ⟨_, hpb⟩ ⟨t, _, rfl⟩
  exact hpb (dvd_mul_left p t)

/-- If every element of `A` is `≥ 2` and `p ∉ A`, every quotient `a/p` is `≥ 2`. -/
theorem quotients_set_ge_two_of_not_mem {p : ℕ} {A : Set ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hp_not_mem : p ∉ A) :
    ∀ t ∈ (fun a => a / p) '' {a ∈ A | p ∣ a}, 2 ≤ t := by
  rintro t ⟨a, ⟨haA, hpa⟩, rfl⟩
  show 2 ≤ a / p
  have ha2 : 2 ≤ a := hpos a haA
  have hane : a ≠ p := fun h => hp_not_mem (h ▸ haA)
  have hrec : a / p * p = a := Nat.div_mul_cancel hpa
  by_contra hlt
  rw [not_le] at hlt
  interval_cases h : (a / p) <;> omega

/-- Strict compression for arbitrary primitive sets (Proposition 3.4, set form),
for any positive integer `p`. -/
theorem FcSet_compressAtSet_lt {A : Set ℕ} {p : ℕ} (hp : 0 < p)
    (hA : IsPrimitive A) (hpA : p ∉ A) (hmult : ∃ a ∈ A, p ∣ a)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    FcSet c (compressAtSet p A) < FcSet c A := by
  have hB : ∀ b ∈ {a ∈ A | ¬ p ∣ a}, 2 ≤ b := fun b hb => hA.1 b hb.1
  have hT := quotients_set_ge_two_of_not_mem hA.1 hpA
  have hTne : ((fun a => a / p) '' {a ∈ A | p ∣ a}).Nonempty := by
    obtain ⟨m, hmA, hpm⟩ := hmult
    exact ⟨m / p, m, ⟨hmA, hpm⟩, rfl⟩
  have hpB : p ∉ {a ∈ A | ¬ p ∣ a} := fun h => h.2 (dvd_refl p)
  have h := block_exchange_lt_set hp hB hT hTne (disjoint_nonMultiples_block_set p A) hpB hc
  rw [← block_decomp_set p A] at h
  exact h

/-- **Theorem 1.2, unique attainment.** `𝓛(c) < F_c(A)` for primitive `A ≠ 𝒫`. -/
theorem Lfun_lt_FcSet {A : Set ℕ} (hA : IsPrimitive A) (hne : A ≠ Primes)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : Lfun c < FcSet c A := by
  by_cases hall : ∀ a ∈ A, Nat.Prime a
  · -- all-prime: `A ⊊ 𝒫`; insert one missing prime.
    have hsub : A ⊆ Primes := fun a ha => hall a ha
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
    exact lt_of_le_of_lt (Lfun_le_FcSet hA' hc)
      (FcSet_insert_lt hqA (fun n hn => (hall n hn).one_le) hc)
  · -- composite element `m`, prime factor `p ∉ A`: one strict compression.
    obtain ⟨m, hmA, hm_not_prime⟩ : ∃ m ∈ A, ¬ Nat.Prime m := by
      by_contra h
      push Not at h
      exact hall h
    obtain ⟨p, hp, hpm, hpA⟩ := exists_prime_factor_not_mem_set hA hmA hm_not_prime
    have hstep := FcSet_compressAtSet_lt hp.pos hA hpA ⟨m, hmA, hpm⟩ hc
    exact lt_of_le_of_lt (Lfun_le_FcSet (compressAtSet_isPrimitive hA hp) hc) hstep

/-- Non-attainment by finite sets. -/
theorem Lfun_lt_Fc_finite {A : Finset ℕ} (hA : IsPrimitiveFin A) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) : Lfun c < Fc c A := by
  have hne : (A : Set ℕ) ≠ Primes := by
    intro h
    have hfin : (Primes).Finite := h ▸ A.finite_toSet
    exact Nat.infinite_setOfPred_prime hfin
  simpa [FcSet_coe] using Lfun_lt_FcSet hA hne hc

end RntPaper
