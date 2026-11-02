import RntPaper.K9Defs

/-!
# Completeness of the case enumeration

* `antichains_complete`: every divisibility antichain contained in an increasing list `xs` of
  positive integers is (as a finset) a member of `antichains xs []`, as a duplicate-free list.
* `exists_maximal_ext`: an antichain inside a finite set `X` extends to a maximal one.
* the meaning of the Boolean predicates `smoothB`, `smoothIn`, `Xs`, `compositesR`,
  `primesIn`, `isMaxBelow`, `isMaxIn`, `covers`, `lmax`.
-/

namespace RntPaper.K9

/-- A finite divisibility antichain. -/
def IsAC (S : Finset ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b

theorem antichains_complete :
    ∀ (xs : List ℕ), xs.Pairwise (· < ·) → (∀ x ∈ xs, 0 < x) →
    ∀ (ch : List ℕ) (S : Finset ℕ), (∀ s ∈ S, s ∈ xs) → (∀ a ∈ ch, ∀ x ∈ xs, a < x) →
      ch.Nodup → IsAC (S ∪ ch.toFinset) →
      ∃ l ∈ antichains xs ch, l.toFinset = S ∪ ch.toFinset ∧ l.Nodup := by
  intro xs
  induction xs with
  | nil =>
    intro _ _ ch S hS _ hnd _
    have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun s hs => by simpa using hS s hs
    refine ⟨ch.reverse, by simp [antichains], ?_, List.nodup_reverse.mpr hnd⟩
    rw [hS0]; ext; simp
  | cons x xs ih =>
    intro hsort hpos ch S hS hch hnd hac
    have hsort' : xs.Pairwise (· < ·) := (List.pairwise_cons.mp hsort).2
    have hxlt : ∀ y ∈ xs, x < y := (List.pairwise_cons.mp hsort).1
    have hpos' : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    by_cases hx : x ∈ S
    · -- take `x`
      have hxch : x ∉ ch := fun h => lt_irrefl x (hch x h x (List.mem_cons_self ..))
      have hcond : (ch.all fun a => x % a != 0) = true := by
        rw [List.all_eq_true]
        intro a ha
        simp only [bne_iff_ne, ne_eq]
        intro hmod
        have hdvd : a ∣ x := Nat.dvd_of_mod_eq_zero hmod
        have := hac a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha)) x
          (Finset.mem_union_left _ hx) hdvd
        exact lt_irrefl x (this ▸ hch a ha x (List.mem_cons_self ..))
      obtain ⟨l, hl, hlS, hlnd⟩ := ih hsort' hpos' (x :: ch) (S.erase x)
        (fun s hs => by
          have h1 := hS s (Finset.mem_of_mem_erase hs)
          rcases List.mem_cons.mp h1 with h | h
          · exact absurd h (Finset.ne_of_mem_erase hs)
          · exact h)
        (fun a ha y hy => by
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hxlt y hy
          · exact hch a ha y (List.mem_cons_of_mem _ hy))
        (List.nodup_cons.mpr ⟨hxch, hnd⟩)
        (by
          have : S.erase x ∪ (x :: ch).toFinset = S ∪ ch.toFinset := by
            ext y; simp only [Finset.mem_union, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
            constructor
            · rintro (⟨_, h⟩ | rfl | h) <;> simp_all
            · rintro (h | h)
              · by_cases hy : y = x
                · exact Or.inr (Or.inl hy)
                · exact Or.inl ⟨hy, h⟩
              · exact Or.inr (Or.inr h)
          rw [this]; exact hac)
      refine ⟨l, ?_, ?_, hlnd⟩
      · simp only [antichains, hcond, if_true, List.mem_append]
        exact Or.inl hl
      · rw [hlS]
        ext y; simp only [Finset.mem_union, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
        constructor
        · rintro (⟨_, h⟩ | rfl | h) <;> simp_all
        · rintro (h | h)
          · by_cases hy : y = x
            · exact Or.inr (Or.inl hy)
            · exact Or.inl ⟨hy, h⟩
          · exact Or.inr (Or.inr h)
    · -- skip `x`
      obtain ⟨l, hl, hlS, hlnd⟩ := ih hsort' hpos' ch S
        (fun s hs => by
          rcases List.mem_cons.mp (hS s hs) with h | h
          · exact absurd (h ▸ hs) hx
          · exact h)
        (fun a ha y hy => hch a ha y (List.mem_cons_of_mem _ hy)) hnd hac
      refine ⟨l, ?_, hlS, hlnd⟩
      simp only [antichains, List.mem_append]
      exact Or.inr hl

/-- **Completeness**, from the empty start. -/
theorem mem_antichains {xs : List ℕ} (hsort : xs.Pairwise (· < ·)) (hpos : ∀ x ∈ xs, 0 < x)
    {S : Finset ℕ} (hS : ∀ s ∈ S, s ∈ xs) (hac : IsAC S) :
    ∃ l ∈ antichains xs [], l.toFinset = S ∧ l.Nodup := by
  obtain ⟨l, hl, h1, h2⟩ := antichains_complete xs hsort hpos [] S hS (by simp) List.nodup_nil
    (by simpa using hac)
  exact ⟨l, hl, by simpa using h1, h2⟩

/-- **Maximal extensions.** -/
theorem exists_maximal_ext (X : Finset ℕ) :
    ∀ (n : ℕ) (S : Finset ℕ), (X \ S).card = n → S ⊆ X → IsAC S →
      ∃ S', S ⊆ S' ∧ S' ⊆ X ∧ IsAC S' ∧ ∀ x ∈ X, x ∉ S' → ∃ s ∈ S', s ∣ x ∨ x ∣ s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hSX hS
    by_cases hmax : ∀ x ∈ X, x ∉ S → ∃ s ∈ S, s ∣ x ∨ x ∣ s
    · exact ⟨S, le_rfl, hSX, hS, hmax⟩
    · push Not at hmax
      obtain ⟨x, hxX, hxS, hx⟩ := hmax
      have hS' : IsAC (insert x S) := by
        intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with h1 | h1 <;> rcases Finset.mem_insert.mp hb with h2 | h2
        · rw [h1, h2]
        · subst h1; exact absurd hab (hx b h2).2
        · subst h2; exact absurd hab (hx a h1).1
        · exact hS a h1 b h2 hab
      have hlt : (X \ insert x S).card < n := by
        rw [← hcard]
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset_sdiff le_rfl (Finset.subset_insert _ _), ?_⟩
        intro h
        have := h (Finset.mem_sdiff.mpr ⟨hxX, hxS⟩)
        simp at this
      obtain ⟨S', h1, h2, h3, h4⟩ := ih _ hlt (insert x S) rfl (Finset.insert_subset hxX hSX) hS'
      exact ⟨S', (Finset.subset_insert _ _).trans h1, h2, h3, h4⟩

theorem exists_maximal_ext' {X S : Finset ℕ} (hSX : S ⊆ X) (hS : IsAC S) :
    ∃ S', S ⊆ S' ∧ S' ⊆ X ∧ IsAC S' ∧ ∀ x ∈ X, x ∉ S' → ∃ s ∈ S', s ∣ x ∨ x ∣ s :=
  exists_maximal_ext X _ S rfl hSX hS

/-! ## Meaning of the Boolean predicates -/

theorem smoothB_iff {p n : ℕ} (hn : n ≠ 0) :
    smoothB p n = true ↔ ∀ q, q.Prime → q ∣ n → q ≤ p := by
  simp only [smoothB, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h q hq hqn
    exact h q ((Nat.mem_primeFactorsList hn).mpr ⟨hq, hqn⟩)
  · intro h q hq
    obtain ⟨h1, h2⟩ := (Nat.mem_primeFactorsList hn).mp hq
    exact h q h1 h2

theorem smoothIn_iff {ps : List ℕ} {n : ℕ} (hn : n ≠ 0) :
    smoothIn ps n = true ↔ ∀ q, q.Prime → q ∣ n → q ∈ ps := by
  simp only [smoothIn, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h q hq hqn
    exact h q ((Nat.mem_primeFactorsList hn).mpr ⟨hq, hqn⟩)
  · intro h q hq
    obtain ⟨h1, h2⟩ := (Nat.mem_primeFactorsList hn).mp hq
    exact h q h1 h2

theorem mem_Xs {p lo hi n : ℕ} : n ∈ Xs p lo hi ↔ n < hi ∧ lo ≤ n ∧ smoothB p n = true := by
  simp [Xs, List.mem_filter, List.mem_range]

theorem Xs_pairwise (p lo hi : ℕ) : (Xs p lo hi).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem Xs_pos {p lo hi : ℕ} (hlo : 1 ≤ lo) : ∀ x ∈ Xs p lo hi, 0 < x := fun x hx => by
  have := (mem_Xs.mp hx).2.1; omega

theorem mem_compositesR {Rp : List ℕ} {lo hi n : ℕ} :
    n ∈ compositesR Rp lo hi ↔ n < hi ∧ lo ≤ n ∧ smoothIn Rp n = true ∧ n ∉ Rp := by
  simp [compositesR, List.mem_filter, List.mem_range, and_assoc]

theorem compositesR_pairwise (Rp : List ℕ) (lo hi : ℕ) : (compositesR Rp lo hi).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem mem_primesIn {lo hi q : ℕ} : q ∈ primesIn lo hi ↔ q ≤ hi ∧ lo ≤ q ∧ q.Prime := by
  simp only [primesIn, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩

theorem primesIn_nodup (lo hi : ℕ) : (primesIn lo hi).Nodup :=
  (List.nodup_range).filter _

theorem lmax_ge {l : List ℕ} {a : ℕ} (ha : a ∈ l) : a ≤ lmax l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [lmax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

theorem lmax_mem {l : List ℕ} (hl : l ≠ []) : lmax l ∈ l := by
  induction l with
  | nil => exact absurd rfl hl
  | cons b l ih =>
    simp only [lmax, List.foldr_cons]
    by_cases hl' : l = []
    · subst hl'; simp
    · rcases le_total b (List.foldr max 0 l) with h | h
      · rw [max_eq_right h]; exact List.mem_cons_of_mem _ (ih hl')
      · rw [max_eq_left h]; exact List.mem_cons_self ..

theorem isMaxBelow_iff {X l : List ℕ} :
    isMaxBelow X l = true ↔ ∀ x ∈ X, x ≤ lmax l → x ∈ l ∨ ∃ s ∈ l, s ∣ x ∨ x ∣ s := by
  simp only [isMaxBelow, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem,
    List.any_eq_true, beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h x hx hxl
    rcases h x hx with (h1 | h1) | h1
    · omega
    · exact Or.inl h1
    · exact Or.inr h1
  · intro h x hx
    by_cases hxl : lmax l < x
    · exact Or.inl (Or.inl hxl)
    · rcases h x hx (by omega) with h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1

theorem isMaxIn_iff {X l : List ℕ} :
    isMaxIn X l = true ↔ ∀ x ∈ X, x ∈ l ∨ ∃ s ∈ l, s ∣ x ∨ x ∣ s := by
  simp only [isMaxIn, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
    beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero]

theorem covers_iff {l : List ℕ} : covers l = true ↔ ∀ r ∈ R4, ∃ s ∈ l, r ∣ s := by
  simp only [covers, List.all_eq_true, List.any_eq_true, beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero]

/-! ## Products over enumerated lists -/

open QProduct in
theorem qProd_toFinset {l : List ℕ} (hl : l.Nodup) (u : ℝ) :
    qProd l.toFinset u = CP.ev (CP.prodOneSub l) u := by
  rw [CP.ev_prodOneSub, qProd, List.prod_toFinset _ hl]

end RntPaper.K9
