import RntPaper.Extremal

/-!
# Extremality over an ambient set (paper §4.1, Theorem 4.1)

For `U ⊆ {2,3,…}` let `Min(U)` be the set of divisibility-minimal elements of `U`,
the elements with no proper divisor in `U`. Among primitive subsets of `U`, `Min(U)`
is the unique minimizer of every `F_c`, `0 < c ≤ 1`, for finite and infinite sets alike.

The proof is the proof of Theorems 1.1–1.2 with compression at an arbitrary divisor
`d ∈ U`: Proposition 3.4 holds for every positive integer, not only for primes. The
case `U = {2,3,…}` gives back the primes (`minElems_ge_two`).
-/

namespace RntPaper

open QProduct MeasureTheory Filter Topology Set
open scoped Classical

/-- The divisibility-minimal elements of `U`. -/
def minElems (U : Set ℕ) : Set ℕ := {u ∈ U | ∀ d ∈ U, d ∣ u → d = u}

/-- The minimal elements of `U` up to `N`. -/
noncomputable def minLE (U : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (· ∈ minElems U)

theorem mem_minLE {U : Set ℕ} {N a : ℕ} : a ∈ minLE U N ↔ a ∈ minElems U ∧ a ≤ N := by
  simp only [minLE, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

theorem isPrimitive_mono {A B : Set ℕ} (hB : IsPrimitive B) (h : A ⊆ B) : IsPrimitive A :=
  ⟨fun a ha => hB.1 a (h ha), fun a ha b hb hab => hB.2 a (h ha) b (h hb) hab⟩

theorem minElems_isPrimitive {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) :
    IsPrimitive (minElems U) :=
  ⟨fun a ha => hU a ha.1, fun a ha _b hb hab => hb.2 a ha.1 hab⟩

/-- A non-minimal element `a` of a primitive `A ⊆ U` has a proper divisor `d ∈ U`
with `d ∉ A`, and no element of `A` divides `d`. -/
theorem exists_divisor_of_not_minElems {U A : Set ℕ} (hA : IsPrimitive A)
    {a : ℕ} (haA : a ∈ A) (haU : a ∈ U) (hna : a ∉ minElems U) :
    ∃ d ∈ U, d ∣ a ∧ d ∉ A ∧ ∀ b ∈ A, ¬ b ∣ d := by
  obtain ⟨d, hdU, hda, hne⟩ : ∃ d ∈ U, d ∣ a ∧ d ≠ a := by
    by_contra h
    push Not at h
    exact hna ⟨haU, h⟩
  refine ⟨d, hdU, hda, fun hdA => hne (hA.2 d hdA a haA hda), fun b hbA hbd => ?_⟩
  have hba : b = a := hA.2 b hbA a haA (hbd.trans hda)
  subst hba
  exact hne (Nat.dvd_antisymm hda hbd)

/-- Compression at `d` preserves primitivity when no element of `A` divides `d`. -/
theorem compressAtSet_isPrimitive_of {A : Set ℕ} {d : ℕ} (hA : IsPrimitive A)
    (hd2 : 2 ≤ d) (hnd : ∀ b ∈ A, ¬ b ∣ d) : IsPrimitive (compressAtSet d A) := by
  obtain ⟨h2, hac⟩ := hA
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · rcases ha with rfl | ⟨haA, _⟩
    · exact hd2
    · exact h2 a haA
  · rcases ha with rfl | ⟨haA, hpa⟩ <;> rcases hb with rfl | ⟨hbA, hpb⟩
    · rfl
    · exact absurd hab hpb
    · exact absurd hab (hnd a haA)
    · exact hac a haA b hbA hab

theorem compressAt_isPrimitiveFin_of {A : Finset ℕ} {d : ℕ} (hA : IsPrimitiveFin A)
    (hd2 : 2 ≤ d) (hnd : ∀ b ∈ A, ¬ b ∣ d) : IsPrimitiveFin (compressAt d A) := by
  obtain ⟨h2, hac⟩ := hA
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · rcases mem_compressAt.mp (Finset.mem_coe.mp ha) with rfl | ⟨haA, _⟩
    · exact hd2
    · exact h2 a haA
  · rcases mem_compressAt.mp (Finset.mem_coe.mp ha) with rfl | ⟨haA, hpa⟩ <;>
      rcases mem_compressAt.mp (Finset.mem_coe.mp hb) with rfl | ⟨hbA, hpb⟩
    · rfl
    · exact absurd hab hpb
    · exact absurd hab (hnd a haA)
    · exact hac a haA b hbA hab

/-! ## Finite sets -/

/-- Descent on the element sum, as in `Fc_primesLE_lt_aux`. -/
theorem Fc_minLE_lt_aux {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) (N : ℕ) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) :
    ∀ (s : ℕ) (A : Finset ℕ), A.sum id ≤ s → IsPrimitiveFin A → (↑A : Set ℕ) ⊆ U →
      (∀ a ∈ A, a ≤ N) → A ≠ minLE U N → Fc c (minLE U N) < Fc c A := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro A hsum hA hAU hAN hne
    by_cases hall : ∀ a ∈ A, a ∈ minElems U
    · -- `A ⊊ Min(U) ∩ [2,N]`: insert a missing minimal element.
      have hsub : A ⊆ minLE U N := fun a ha => mem_minLE.mpr ⟨hall a ha, hAN a ha⟩
      obtain ⟨q, hqM, hqA⟩ : ∃ q ∈ minLE U N, q ∉ A := by
        by_contra h
        push Not at h
        exact hne (Finset.Subset.antisymm hsub h)
      have h1 : Fc c (minLE U N) ≤ Fc c (insert q A) :=
        Fc_antitone ⟨hc.1.le, hc.2⟩ (Finset.insert_subset hqM hsub)
      have h2 : Fc c (insert q A) < Fc c A :=
        Fc_insert_lt hqA (fun n hn => le_trans (by norm_num) (hA.1 n hn)) hc
      exact lt_of_le_of_lt h1 h2
    · -- a non-minimal element: compress at one of its proper divisors in `U`.
      obtain ⟨a, haA, hna⟩ : ∃ a ∈ A, a ∉ minElems U := by
        by_contra h
        push Not at h
        exact hall h
      obtain ⟨d, hdU, hda, hdA, hnd⟩ :=
        exists_divisor_of_not_minElems hA (Finset.mem_coe.mpr haA) (hAU haA) hna
      have hd2 : 2 ≤ d := hU d hdU
      have hmult : ∃ a ∈ A, d ∣ a := ⟨a, haA, hda⟩
      have hstep : Fc c (compressAt d A) < Fc c A :=
        Fc_compressAt_lt (by omega) hA hdA hmult hc
      by_cases hCeq : compressAt d A = minLE U N
      · rw [← hCeq]; exact hstep
      · have hA' : IsPrimitiveFin (compressAt d A) :=
          compressAt_isPrimitiveFin_of hA hd2 (fun b hb => hnd b hb)
        have hAU' : (↑(compressAt d A) : Set ℕ) ⊆ U := by
          intro x hx
          rcases mem_compressAt.mp (Finset.mem_coe.mp hx) with rfl | ⟨hxA, _⟩
          · exact hdU
          · exact hAU hxA
        have hAN' : ∀ a ∈ compressAt d A, a ≤ N := compressAt_bounded hA hAN hmult
        have hsum' : (compressAt d A).sum id < A.sum id := sum_compressAt_lt hd2 hA hdA hmult
        exact lt_trans (ih _ (lt_of_lt_of_le hsum' hsum) (compressAt d A) le_rfl hA' hAU'
          hAN' hCeq) hstep

/-- **Theorem 4.1, finite form.** For primitive `A ⊆ U ∩ [2,N]` with `A ≠ Min(U) ∩ [2,N]`
and every `c ∈ (0,1]`: `F_c(Min(U) ∩ [2,N]) < F_c(A)`. -/
theorem Fc_minLE_lt {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAU : (↑A : Set ℕ) ⊆ U) (hAN : ∀ a ∈ A, a ≤ N)
    (hne : A ≠ minLE U N) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fc c (minLE U N) < Fc c A :=
  Fc_minLE_lt_aux hU N hc (A.sum id) A le_rfl hA hAU hAN hne

theorem Fc_minLE_le {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAU : (↑A : Set ℕ) ⊆ U) (hAN : ∀ a ∈ A, a ≤ N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : Fc c (minLE U N) ≤ Fc c A := by
  by_cases h : A = minLE U N
  · rw [h]
  · exact (Fc_minLE_lt hU hA hAU hAN h hc).le

/-! ## Arbitrary sets -/

/-- **Theorem 4.1, lower bound.** `F_c(Min(U)) ≤ F_c(A)` for every primitive `A ⊆ U`. -/
theorem FcSet_minElems_le {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) {A : Set ℕ}
    (hA : IsPrimitive A) (hAU : A ⊆ U) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    FcSet c (minElems U) ≤ FcSet c A := by
  refine le_of_tendsto_of_tendsto' (tendsto_Fc_truncation (minElems U) ⟨hc.1.le, hc.2⟩)
    (tendsto_Fc_truncation A ⟨hc.1.le, hc.2⟩) fun N => ?_
  have hsub : (↑((Finset.range (N + 1)).filter (· ∈ A)) : Set ℕ) ⊆ U := fun x hx =>
    hAU (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
  exact Fc_minLE_le hU (truncation_isPrimitiveFin hA N) hsub (truncation_bounded A N) hc

/-- **Theorem 4.1, unique attainment.** `F_c(Min(U)) < F_c(A)` for every primitive
`A ⊆ U` with `A ≠ Min(U)`, finite or infinite. -/
theorem FcSet_minElems_lt {U : Set ℕ} (hU : ∀ u ∈ U, 2 ≤ u) {A : Set ℕ}
    (hA : IsPrimitive A) (hAU : A ⊆ U) (hne : A ≠ minElems U)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : FcSet c (minElems U) < FcSet c A := by
  by_cases hall : A ⊆ minElems U
  · obtain ⟨q, hqM, hqA⟩ : ∃ q ∈ minElems U, q ∉ A := by
      by_contra h
      push Not at h
      exact hne (Set.Subset.antisymm hall h)
    have hsub : insert q A ⊆ minElems U := Set.insert_subset hqM hall
    have hA' : IsPrimitive (insert q A) := isPrimitive_mono (minElems_isPrimitive hU) hsub
    exact lt_of_le_of_lt
      (FcSet_minElems_le hU hA' (hsub.trans fun _ h => h.1) hc)
      (FcSet_insert_lt hqA (fun n hn => le_trans (by norm_num) (hA.1 n hn)) hc)
  · obtain ⟨a, haA, hna⟩ : ∃ a ∈ A, a ∉ minElems U := by
      by_contra h
      push Not at h
      exact hall h
    obtain ⟨d, hdU, hda, hdA, hnd⟩ := exists_divisor_of_not_minElems hA haA (hAU haA) hna
    have hd2 : 2 ≤ d := hU d hdU
    have hstep := FcSet_compressAtSet_lt (by omega) hA hdA ⟨a, haA, hda⟩ hc
    have hC : IsPrimitive (compressAtSet d A) := compressAtSet_isPrimitive_of hA hd2 hnd
    have hCU : compressAtSet d A ⊆ U := by
      rintro x (rfl | ⟨hxA, _⟩)
      · exact hdU
      · exact hAU hxA
    exact lt_of_le_of_lt (FcSet_minElems_le hU hC hCU hc) hstep

/-! ## The prime instance -/

/-- With `U = {2,3,…}` the minimal elements are the primes. -/
theorem minElems_ge_two : minElems {n | 2 ≤ n} = Primes := by
  ext p
  constructor
  · rintro ⟨hp2, hmin⟩
    refine Nat.prime_def.mpr ⟨hp2, fun m hm => ?_⟩
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · exact absurd (Nat.eq_zero_of_zero_dvd hm) (by simp at hp2; omega)
      · exact Or.inl rfl
    · exact Or.inr (hmin m hm2 hm)
  · intro hp
    refine ⟨hp.two_le, fun d hd hdp => ?_⟩
    rcases (Nat.dvd_prime hp).mp hdp with rfl | h
    · exact absurd hd (by simp)
    · exact h

end RntPaper
