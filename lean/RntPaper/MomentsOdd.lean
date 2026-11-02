import RntPaper.MomentsSmall

/-!
# Moments beyond `17/4`: compress at odd primes first

The bootstrap of `MomentsReal` and `MomentsSmall` compresses at any prime `p` dividing a
composite. At `p = 2` with a prime-like quotient block this costs `J_{k/2} > 0`, that is
`k ≤ 2α₀`. That cost is intrinsic to compressions at `2` (paper open problem 2): it is
exactly the threshold of the relative statement for `U = 2ℕ`, where `{2}` competes with
`2𝒫`. In the absolute problem it can be avoided by ordering the compressions.

* While some composite of `A` has an odd prime factor `p`, compress at `p`. The quotient
  block is an arbitrary primitive set, and the step costs only `J_{k/p} > 0` with
  `p ≥ 3`.
* Afterwards every composite of `A` is a power of `2`. A primitive set contains at most
  one, so the compression at `2` has the **singleton** quotient block `{m}`, and
  `E_{{m}}(v) = v - vᵐ > 0` pointwise: no condition at all.

Hence every `0 < k ≤ 3b` with `J_b(1) > 0` works (`moment_primes_lt_odd_of_Jw`), and the
existing certificate `J_{17/8}(1) > 0` gives the range `0 < k ≤ 51/8`
(`moment_primes_lt_odd`, `moment_primesLE_lt_odd`), up from `17/4`.

* `AdmissibleOdd`, `admissibleOdd_of_good_of_Jw`, `admissibleOdd_of_Jw`: every odd-prime
  compression strictly lowers `𝓜ₖ` for `1 ≤ k ≤ 3b`.
* `run_pos_two_singleton`, `MSet_compressAtSet_two_lt`: the compression at `2` with a single
  even element.
* `descent_lt_odd`: the ordered descent for finite sets.
* `MSet_primesLE_lt_of_admissibleOdd`, `goodAt_of_admissibleOdd`,
  `MSet_primes_lt_of_admissibleOdd`: finite and arbitrary primitive sets.
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set Filter Topology

/-! ## Compressions at odd primes -/

/-- Exponents at which every compression at an **odd** prime strictly lowers `𝓜ₖ`: for
every prime `p ≥ 3` and primitive `T`, the running integrals of `u^{k-1}E_T(uᵖ)` are
positive. -/
def AdmissibleOdd (k : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ T : Set ℕ, IsPrimitive T →
    ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * ESetExt T (u ^ p)

/-- If minimality holds on `[1, K]` and `J_b(1) > 0`, every `k ∈ [1, min(3K, 3b)]` is
odd-admissible: an odd prime `p < k` has `1 ≤ k/p ≤ k/3`. -/
theorem admissibleOdd_of_good_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {K : ℝ}
    (hK : ∀ s, 1 ≤ s → s ≤ K → GoodAt s) {k : ℝ} (hk1 : 1 ≤ k) (hk2 : k ≤ 3 * K)
    (hk : k ≤ 3 * b) : AdmissibleOdd k := by
  intro p hp hp3 T hT y hy
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  rcases le_or_gt k p with hkp | hpk
  · exact run_pos_of_le hT.1 hp.one_le hk1 hkp hy
  · have hpR : (0 : ℝ) < p := by linarith
    have hs1 : 1 ≤ k / p := by rw [le_div_iff₀ hpR]; linarith
    have hK0 : 0 ≤ K := by linarith
    have hb0 : 0 ≤ b := by linarith
    have hsK : k / p ≤ K := by
      rw [div_le_iff₀ hpR]; nlinarith [mul_le_mul_of_nonneg_left hp3R hK0]
    have hs : k / p ≤ b := by
      rw [div_le_iff₀ hpR]; nlinarith [mul_le_mul_of_nonneg_left hp3R hb0]
    exact run_pos_of_lt_of_Jw hb hT hp.one_le hpk.le hs (hK _ hs1 hsK) hy

/-- **Every `k ∈ [1, 3b]` is odd-admissible when `J_b(1) > 0`.** Minimality on `[1, 2b]`
comes from `admissible_of_Jw`. -/
theorem admissibleOdd_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {k : ℝ} (hk1 : 1 ≤ k)
    (hk : k ≤ 3 * b) : AdmissibleOdd k := by
  have hgood : ∀ s, 1 ≤ s → s ≤ 2 * b → GoodAt s := fun s hs1 hs =>
    goodAt_of_admissible hs1 (admissible_of_Jw hb hs1 hs)
  exact admissibleOdd_of_good_of_Jw hb hgood hk1 (by linarith) hk

theorem MSet_compressAtSet_lt_odd {k : ℝ} (hk : 1 ≤ k) (hadm : AdmissibleOdd k) {A : Set ℕ}
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hA : IsPrimitive A) (hpA : p ∉ A)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c (compressAtSet p A) < MSet k c A := by
  have hB : ∀ b ∈ {a ∈ A | ¬ p ∣ a}, 2 ≤ b := fun b hb => hA.1 b hb.1
  have hTp := quotients_set_isPrimitive hA hpA
  have hpB : p ∉ {a ∈ A | ¬ p ∣ a} := fun h => h.2 (dvd_refl p)
  have h := MSet_block_exchange_lt hp.pos hB hTp.1 (disjoint_nonMultiples_block_set p A) hpB
    hk (hadm p hp hp3 _ hTp) hc
  rw [← block_decomp_set p A] at h
  exact h

/-! ## The compression at `2` with a single even element -/

/-- **The singleton block at `p = 2`**: `E_{{m}}(u²) = u² - u^{2m} > 0` on `(0,1)`, so the
running integrals are positive for every `k ≥ 1`. -/
theorem run_pos_two_singleton {m : ℕ} (hm : 2 ≤ m) {k : ℝ} (hk : 1 ≤ k) {y : ℝ}
    (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * ESetExt {m} (u ^ 2) := by
  have hT1 : ∀ n ∈ ({m} : Set ℕ), 1 ≤ n := by
    intro n hn
    rw [Set.mem_singleton_iff] at hn
    omega
  have hcont : Continuous fun u : ℝ => u ^ (k - 1) * ESetExt {m} (u ^ 2) :=
    (Real.continuous_rpow_const (by linarith)).mul
      ((continuous_ESetExt hT1).comp (continuous_pow 2))
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable 0 y) ?_ hy.1
  intro u hu
  have hu1 : u < 1 := hu.2.trans_le hy.2
  have hu2 : u ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨(pow_pos hu.1 2).le, pow_le_one₀ hu.1.le hu1.le⟩
  rw [ESetExt_of_mem _ hu2]
  unfold blockESet
  rw [qProdSet_singleton]
  have h0 : 0 < u ^ 2 := pow_pos hu.1 2
  have h1 : u ^ 2 < 1 := by nlinarith [hu.1]
  have hpow : (u ^ 2) ^ m < u ^ 2 := by
    calc (u ^ 2) ^ m < (u ^ 2) ^ 1 := pow_lt_pow_right_of_lt_one₀ h0 h1 (by omega)
      _ = u ^ 2 := pow_one _
  have hw : 0 < u ^ (k - 1) := Real.rpow_pos_of_pos hu.1 _
  have hd : 0 < (1 - (u ^ 2) ^ m) - (1 - u ^ 2) := by linarith
  exact mul_pos hw hd

/-- If the even elements of `A` are a single `a₀`, the quotient block at `2` is `{a₀ / 2}`. -/
theorem quotients_two_eq_singleton {A : Set ℕ} {a₀ : ℕ} (ha₀ : a₀ ∈ A) (h2 : 2 ∣ a₀)
    (huniq : ∀ a ∈ A, 2 ∣ a → a = a₀) :
    (fun a => a / 2) '' {a ∈ A | 2 ∣ a} = {a₀ / 2} := by
  ext t
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ⟨haA, h2a⟩, rfl⟩
    rw [huniq a haA h2a]
  · rintro rfl
    exact ⟨a₀, ⟨ha₀, h2⟩, rfl⟩

/-- **Compression at `2` with a single even element strictly lowers `𝓜ₖ`, for every
`k ≥ 1`.** -/
theorem MSet_compressAtSet_two_lt {k : ℝ} (hk : 1 ≤ k) {A : Set ℕ} (hA : IsPrimitive A)
    (h2A : 2 ∉ A) {a₀ : ℕ} (ha₀ : a₀ ∈ A) (h2 : 2 ∣ a₀) (huniq : ∀ a ∈ A, 2 ∣ a → a = a₀)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c (compressAtSet 2 A) < MSet k c A := by
  have hB : ∀ b ∈ {a ∈ A | ¬ 2 ∣ a}, 2 ≤ b := fun b hb => hA.1 b hb.1
  have hTp := quotients_set_isPrimitive hA h2A
  have h2B : 2 ∉ {a ∈ A | ¬ 2 ∣ a} := fun h => h.2 (dvd_refl 2)
  have hT := quotients_two_eq_singleton ha₀ h2 huniq
  have hm : 2 ≤ a₀ / 2 := hTp.1 _ (by rw [hT]; exact Set.mem_singleton _)
  have hrun : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y,
      u ^ (k - 1) * ESetExt ((fun a => a / 2) '' {a ∈ A | 2 ∣ a}) (u ^ 2) := by
    intro y hy
    rw [hT]
    exact run_pos_two_singleton hm hk hy
  have h := MSet_block_exchange_lt (by norm_num : 0 < 2) hB hTp.1
    (disjoint_nonMultiples_block_set 2 A) h2B hk hrun hc
  rw [← block_decomp_set 2 A] at h
  exact h

/-! ## Choosing the compression -/

/-- A number `≥ 1` whose prime factors are all `2` is a power of `2`. -/
theorem eq_two_pow_of_prime_dvd {n : ℕ} (hn : n ≠ 0) (h : ∀ q, Nat.Prime q → q ∣ n → q = 2) :
    n = 2 ^ n.primeFactorsList.length :=
  Nat.eq_prime_pow_of_unique_prime_dvd hn (fun {d} hd hdn => h d hd hdn)

/-- In a primitive set whose composites have no odd prime factor, a composite `a` is even,
`2 ∉ A`, and `a` is the only even element. -/
theorem even_unique_of_no_odd {A : Set ℕ} (hA : IsPrimitive A)
    (hno : ∀ a ∈ A, ¬ Nat.Prime a → ∀ q, Nat.Prime q → q ∣ a → q = 2)
    {a : ℕ} (haA : a ∈ A) (hnp : ¬ Nat.Prime a) :
    2 ∣ a ∧ 2 ∉ A ∧ ∀ b ∈ A, 2 ∣ b → b = a := by
  have ha2 : 2 ≤ a := hA.1 a haA
  obtain ⟨q, hq, hqa⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  have hq2 : q = 2 := hno a haA hnp q hq hqa
  subst hq2
  have h2A : 2 ∉ A := fun h2A => hnp (hA.2 2 h2A a haA hqa ▸ Nat.prime_two)
  refine ⟨hqa, h2A, fun b hbA h2b => ?_⟩
  have hbnp : ¬ Nat.Prime b := by
    intro hb
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hb).mp h2b
    exact h2A (this ▸ hbA)
  have hb0 : b ≠ 0 := by have := hA.1 b hbA; omega
  have ha0 : a ≠ 0 := by omega
  have hbpow := eq_two_pow_of_prime_dvd hb0 (hno b hbA hbnp)
  have hapow := eq_two_pow_of_prime_dvd ha0 (hno a haA hnp)
  rcases le_total b.primeFactorsList.length a.primeFactorsList.length with hle | hle
  · have hdvd : b ∣ a := by
      rw [hbpow, hapow]; exact Nat.pow_dvd_pow 2 hle
    exact hA.2 b hbA a haA hdvd
  · have hdvd : a ∣ b := by
      rw [hbpow, hapow]; exact Nat.pow_dvd_pow 2 hle
    exact (hA.2 a haA b hbA hdvd).symm

/-! ## The ordered descent, finite sets -/

/-- **Ordered descent.** If every compression at an odd prime and every compression at `2`
with a single even element strictly lowers `J`, and inserting a missing element lowers `J`,
then `J(𝒫_N) < J(A)` for every primitive `A ⊆ [2,N]`, `A ≠ 𝒫_N`. -/
theorem descent_lt_odd {J : Finset ℕ → ℝ} {N : ℕ}
    (hodd : ∀ (A : Finset ℕ) (p : ℕ), IsPrimitiveFin A → Nat.Prime p → 3 ≤ p → p ∉ A →
      (∃ a ∈ A, p ∣ a) → J (compressAt p A) < J A)
    (htwo : ∀ (A : Finset ℕ) (a₀ : ℕ), IsPrimitiveFin A → 2 ∉ A → a₀ ∈ A → 2 ∣ a₀ →
      (∀ a ∈ A, 2 ∣ a → a = a₀) → J (compressAt 2 A) < J A)
    (hins : ∀ (R : Finset ℕ) (q : ℕ), q ∉ R → (∀ n ∈ R, 1 ≤ n) → J (insert q R) < J R)
    {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N) :
    J (primesLE N) < J A := by
  classical
  -- all-prime sets: insert the missing primes one at a time
  have hprime : ∀ (n : ℕ) (R : Finset ℕ), (primesLE N \ R).card = n → R ⊆ primesLE N →
      R ≠ primesLE N → J (primesLE N) < J R := by
    intro n
    induction n with
    | zero =>
      intro R hcard hsub hne
      have h := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard)
      exact absurd (Finset.Subset.antisymm hsub h) hne
    | succ n ih =>
      intro R hcard hsub hne
      obtain ⟨q, hq⟩ : (primesLE N \ R).Nonempty := by
        rw [← Finset.card_pos]; omega
      have hq' := Finset.mem_sdiff.mp hq
      have hR1 : ∀ x ∈ R, 1 ≤ x := fun x hx => (mem_primesLE.mp (hsub hx)).1.one_lt.le
      have hlt := hins R q hq'.2 hR1
      have hsub' : insert q R ⊆ primesLE N := Finset.insert_subset hq'.1 hsub
      by_cases heq : insert q R = primesLE N
      · rw [← heq]; exact hlt
      · have hcard' : (primesLE N \ insert q R).card = n := by
          rw [Finset.sdiff_insert, Finset.card_erase_of_mem hq, hcard]
          rfl
        exact (ih _ hcard' hsub' heq).trans hlt
  -- general sets: strong induction on the element sum
  have main : ∀ (n : ℕ) (A : Finset ℕ), A.sum id = n → IsPrimitiveFin A →
      (∀ a ∈ A, a ≤ N) → A ≠ primesLE N → J (primesLE N) < J A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hsum hA hAN hne
      by_cases hall : ∀ a ∈ A, Nat.Prime a
      · exact hprime _ A rfl (fun a ha => mem_primesLE.mpr ⟨hall a ha, hAN a ha⟩) hne
      · push Not at hall
        obtain ⟨a, haA, hnp⟩ := hall
        -- one compression step, then the induction hypothesis
        have step : ∀ p, Nat.Prime p → p ∉ A → (∃ a ∈ A, p ∣ a) →
            J (compressAt p A) < J A → J (primesLE N) < J A := by
          intro p hp hpA hmult hstep
          have hA' := compressAt_isPrimitiveFin hA hp hmult
          have hAN' := compressAt_bounded hA hAN hmult
          have hlt := sum_compressAt_lt' hpA hA hmult
          by_cases heq : compressAt p A = primesLE N
          · rw [← heq]; exact hstep
          · exact (ih _ (hsum ▸ hlt) _ rfl hA' hAN' heq).trans hstep
        by_cases hodd' : ∃ b ∈ A, ¬ Nat.Prime b ∧ ∃ q, Nat.Prime q ∧ 3 ≤ q ∧ q ∣ b
        · -- a composite with an odd prime factor: compress there
          obtain ⟨b, hbA, hbnp, q, hq, hq3, hqb⟩ := hodd'
          have hqne : q ≠ b := fun h => hbnp (h ▸ hq)
          have hqA : q ∉ A := fun hqA => hqne (hA.2 q hqA b hbA hqb)
          exact step q hq hqA ⟨b, hbA, hqb⟩ (hodd A q hA hq hq3 hqA ⟨b, hbA, hqb⟩)
        · -- every composite is a power of `2`: compress at `2`, singleton block
          push Not at hodd'
          have hno : ∀ b ∈ (A : Set ℕ), ¬ Nat.Prime b → ∀ q, Nat.Prime q → q ∣ b → q = 2 := by
            intro b hb hbnp q hq hqb
            by_contra hq2
            have hq3 : 3 ≤ q := by
              have := hq.two_le
              omega
            exact hodd' b hb hbnp q hq hq3 hqb
          obtain ⟨h2a, h2A, huniq⟩ := even_unique_of_no_odd hA hno haA hnp
          exact step 2 Nat.prime_two h2A ⟨a, haA, h2a⟩ (htwo A a hA h2A haA h2a huniq)
  exact main _ A rfl hA hAN hne

/-! ## Minimality at an odd-admissible exponent -/

/-- **Finite minimality at an odd-admissible exponent.** -/
theorem MSet_primesLE_lt_of_admissibleOdd {k : ℝ} (hk : 1 ≤ k) (hadm : AdmissibleOdd k)
    {N : ℕ} {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N)
    (hne : A ≠ primesLE N) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) := by
  refine descent_lt_odd (J := fun S => MSet k c (S : Set ℕ)) ?_ ?_ ?_ hA hAN hne
  · intro A p hA hp hp3 hpA _
    simp only [coe_compressAt]
    exact MSet_compressAtSet_lt_odd hk hadm hp hp3 hA (by simpa using hpA) hc
  · intro A a₀ hA h2A ha₀ h2 huniq
    simp only [coe_compressAt]
    exact MSet_compressAtSet_two_lt hk hA (by simpa using h2A) (by simpa using ha₀) h2
      (fun a ha h2a => huniq a (by simpa using ha) h2a) hc
  · intro R q hq hR
    simp only [Finset.coe_insert]
    exact MSet_insert_lt (by simpa using hq) (fun n hn => hR n hn) hk hc

/-- **Lower bound at an odd-admissible exponent:** `𝓜ₖ,c(𝒫) ≤ 𝓜ₖ,c(A)` for all primitive `A`. -/
theorem goodAt_of_admissibleOdd {k : ℝ} (hk : 1 ≤ k) (hadm : AdmissibleOdd k) : GoodAt k := by
  classical
  intro A hA c hc
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hP := tendsto_MSet_truncation Primes hk hcI
  simp only [primes_truncation] at hP
  refine le_of_tendsto_of_tendsto' hP (tendsto_MSet_truncation A hk hcI) fun N => ?_
  by_cases h : (Finset.range (N + 1)).filter (· ∈ A) = primesLE N
  · rw [h]
  · exact (MSet_primesLE_lt_of_admissibleOdd hk hadm (truncation_isPrimitiveFin hA N)
      (truncation_bounded A N) h hc).le

/-- **Unique attainment at an odd-admissible exponent.** -/
theorem MSet_primes_lt_of_admissibleOdd {k : ℝ} (hk : 1 ≤ k) (hadm : AdmissibleOdd k)
    {A : Set ℕ} (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A := by
  have hgood := goodAt_of_admissibleOdd hk hadm
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
  · push Not at hall
    obtain ⟨m, hmA, hmnp⟩ := hall
    by_cases hodd' : ∃ b ∈ A, ¬ Nat.Prime b ∧ ∃ q, Nat.Prime q ∧ 3 ≤ q ∧ q ∣ b
    · obtain ⟨b, hbA, hbnp, q, hq, hq3, hqb⟩ := hodd'
      have hqne : q ≠ b := fun h => hbnp (h ▸ hq)
      have hqA : q ∉ A := fun hqA => hqne (hA.2 q hqA b hbA hqb)
      have hstep := MSet_compressAtSet_lt_odd hk hadm hq hq3 hA hqA hc
      exact lt_of_le_of_lt (hgood _ (compressAtSet_isPrimitive hA hq) c hc) hstep
    · push Not at hodd'
      have hno : ∀ b ∈ A, ¬ Nat.Prime b → ∀ q, Nat.Prime q → q ∣ b → q = 2 := by
        intro b hb hbnp q hq hqb
        by_contra hq2
        have hq3 : 3 ≤ q := by
          have := hq.two_le
          omega
        exact hodd' b hb hbnp q hq hq3 hqb
      obtain ⟨h2m, h2A, huniq⟩ := even_unique_of_no_odd hA hno hmA hmnp
      have hstep := MSet_compressAtSet_two_lt hk hA h2A hmA h2m huniq hc
      exact lt_of_le_of_lt (hgood _ (compressAtSet_isPrimitive hA Nat.prime_two) c hc) hstep

/-! ## Main theorems -/

/-- **Moment minimality up to `3b`, all primitive sets.** If `J_b(1) > 0` then for every
`0 < k ≤ 3b`, every primitive `A ≠ 𝒫` and `c ∈ (0,1]`: `𝓜ₖ,c(𝒫) < 𝓜ₖ,c(A)`. -/
theorem moment_primes_lt_odd_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {k : ℝ} (hk0 : 0 < k)
    (hk : k ≤ 3 * b) {A : Set ℕ} (hA : IsPrimitive A) (hne : A ≠ Primes)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c Primes < MSet k c A := by
  rcases le_or_gt k 1 with h | h
  · exact MSet_primes_lt_small hk0 h hA hne hc
  · exact MSet_primes_lt_of_admissibleOdd h.le (admissibleOdd_of_Jw hb h.le hk) hA hne hc

/-- **Moment minimality up to `3b`, finite sets.** -/
theorem moment_primesLE_lt_odd_of_Jw {b : ℝ} (hb : 0 < Jw b 1) {k : ℝ} (hk0 : 0 < k)
    (hk : k ≤ 3 * b) {N : ℕ} {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N)
    (hne : A ≠ primesLE N) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) := by
  rcases le_or_gt k 1 with h | h
  · exact MSet_primesLE_lt_small hk0 h hA hAN hne hc
  · exact MSet_primesLE_lt_of_admissibleOdd h.le (admissibleOdd_of_Jw hb h.le hk) hA hAN hne hc

/-- **Moments for `0 < k ≤ 51/8`, all primitive sets** (from `J_{17/8}(1) > 0`). For every
primitive `A ≠ 𝒫`, finite or infinite, and every `c ∈ (0,1]`:
`𝔼 min(Z_𝒫^k, c^k) < 𝔼 min(Z_A^k, c^k)`. -/
theorem moment_primes_lt_odd {k : ℝ} (hk0 : 0 < k) (hk : k ≤ 51 / 8) {A : Set ℕ}
    (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A :=
  moment_primes_lt_odd_of_Jw Jw_seventeen_eighths hk0 (by linarith) hA hne hc

/-- **Moments for `0 < k ≤ 51/8`, finite sets.** For every primitive `A ⊆ {2,…,N}`,
`A ≠ 𝒫_N`, and every `c ∈ (0,1]`: `𝔼 min(Z_{𝒫_N}^k, c^k) < 𝔼 min(Z_A^k, c^k)`. -/
theorem moment_primesLE_lt_odd {k : ℝ} (hk0 : 0 < k) (hk : k ≤ 51 / 8) {N : ℕ}
    {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) :=
  moment_primesLE_lt_odd_of_Jw Jw_seventeen_eighths hk0 (by linarith) hA hAN hne hc

end RntPaper
