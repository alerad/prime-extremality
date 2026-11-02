import RntPaper.K9Descent

/-!
# Theorem 3.8 from the case checks

`k9_primesLE_of` and `k9_primes_of`: assuming `K9Certs`, for `0 < k ≤ k₉` the primes minimize
`𝓜ₖ,c` (finite and arbitrary primitive sets), strictly for `k < k₉`.
-/

namespace RntPaper.K9

open MeasureTheory intervalIntegral Set CP QProduct

/-! ## Bookkeeping -/

/-- Sum of the composite elements up to `N`. -/
noncomputable def compSum (N : ℕ) (A : Set ℕ) : ℕ := by
  classical exact ((Finset.range (N + 1)).filter fun a => a ∈ A ∧ ¬ a.Prime).sum id

theorem compSum_compress {N p : ℕ} {A : Set ℕ} (hp : p.Prime) (hAN : ∀ a ∈ A, a ≤ N)
    (hA2 : ∀ a ∈ A, 2 ≤ a) {a0 : ℕ} (ha0 : a0 ∈ A) (ha0p : ¬ a0.Prime) (hpa0 : p ∣ a0) :
    compSum N (compressAtSet p A) < compSum N A := by
  classical
  unfold compSum
  apply Finset.sum_lt_sum_of_subset
  · intro a ha
    simp only [Finset.mem_filter, compressAtSet, Set.mem_insert_iff, Set.mem_ofPred_eq] at ha ⊢
    refine ⟨ha.1, ?_, ha.2.2⟩
    rcases ha.2.1 with rfl | ⟨haA, _⟩
    · exact absurd hp ha.2.2
    · exact haA
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hAN a0 ha0; omega, ha0, ha0p⟩
  · simp only [Finset.mem_filter, compressAtSet, Set.mem_insert_iff, Set.mem_ofPred_eq, not_and]
    intro _ h
    rcases h with rfl | ⟨_, h⟩
    · exact fun h' => h' hp
    · exact absurd hpa0 h
  · have := hA2 a0 ha0
    simp only [id]; omega
  · intro _ _ _; exact Nat.zero_le _

theorem compSum_union_primes {N : ℕ} {A P : Set ℕ} (hP : ∀ q ∈ P, q.Prime) :
    compSum N (A ∪ P) = compSum N A := by
  classical
  unfold compSum
  congr 1
  ext a
  simp only [Finset.mem_filter, Set.mem_union]
  constructor
  · rintro ⟨h1, h2 | h2, h3⟩
    · exact ⟨h1, h2, h3⟩
    · exact absurd (hP a h2) h3
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, Or.inl h2, h3⟩

theorem exists_singleParam {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h59 : p ≤ 59) :
    ∃ m B, (p, m, B) ∈ singleParams := by
  interval_cases p <;> simp_all [singleParams] <;> norm_num at hp

theorem exists_max_prime {A : Set ℕ}
    (h61 : ∀ a ∈ A, ¬ a.Prime → ∀ q, q.Prime → q ∣ a → q < 61)
    (h11 : ∃ a ∈ A, ¬ a.Prime ∧ ∃ q, q.Prime ∧ 11 ≤ q ∧ q ∣ a) :
    ∃ p, p.Prime ∧ 11 ≤ p ∧ p ≤ 59 ∧ (∃ a ∈ A, ¬ a.Prime ∧ p ∣ a) ∧
      ∀ a ∈ A, ¬ a.Prime → ∀ q, q.Prime → q ∣ a → q ≤ p := by
  classical
  set F := (Finset.range 61).filter fun q => q.Prime ∧ 11 ≤ q ∧ ∃ a ∈ A, ¬ a.Prime ∧ q ∣ a
  have hF : F.Nonempty := by
    obtain ⟨a, ha, hap, q, hq, hq11, hqa⟩ := h11
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (h61 a ha hap q hq hqa), hq, hq11,
      a, ha, hap, hqa⟩⟩
  set p := F.max' hF
  obtain ⟨hp61, hp, hp11, hpa⟩ := Finset.mem_filter.mp (F.max'_mem hF)
  rw [Finset.mem_range] at hp61
  refine ⟨p, hp, hp11, ?_, hpa, fun a ha hap q hq hqa => ?_⟩
  · by_contra h
    have h' : ¬ F.max' hF ≤ 59 := h
    have h60 : F.max' hF = 60 := by omega
    rw [h60] at hp; norm_num at hp
  · by_cases hq11 : 11 ≤ q
    · exact F.le_max' q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (h61 a ha hap q hq hqa),
        hq, hq11, a, ha, hap, hqa⟩)
    · omega

theorem prime_le7_or_ge11 {q : ℕ} (hq : q.Prime) : q ≤ 7 ∨ 11 ≤ q := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  interval_cases q <;> norm_num at hq

theorem mem_R4f_iff {r : ℕ} : r ∈ (R4f : Set ℕ) ↔ r ∈ R4 := by simp [R4f, R4]

theorem prime_in_R4 {q : ℕ} (hq : q.Prime) (h7 : q ≤ 7) : q ∈ R4 := by
  interval_cases q <;> simp_all [R4] <;> norm_num at hq

/-! ## Adding primes keeps primitivity -/

/-- Adding primes that divide no element and are not in `A` keeps `A` primitive. -/
theorem isPrimitive_union_primes {A P : Set ℕ} (hA : IsPrimitive A) (hP : ∀ q ∈ P, q.Prime)
    (hPA : ∀ q ∈ P, ∀ a ∈ A, q ∣ a → q = a) : IsPrimitive (A ∪ P) := by
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · rcases ha with ha | ha
    · exact hA.1 a ha
    · exact (hP a ha).two_le
  · rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hA.2 a ha b hb hab
    · rcases (Nat.dvd_prime (hP b hb)).mp hab with h | h
      · have := hA.1 a ha; omega
      · exact h
    · exact hPA a ha b hb hab
    · exact (Nat.prime_dvd_prime_iff_eq (hP a ha) (hP b hb)).mp hab

/-! ## The finite descent -/

theorem k9_fin_aux (hC : K9Certs) {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ k9) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) (N : ℕ) :
    ∀ (n : ℕ) (A : Set ℕ), compSum N A = n → IsPrimitive A → (∀ a ∈ A, a ≤ N) →
      MSet k c (primesLE N : Set ℕ) ≤ MSet k c A ∧
        (k < k9 → A ≠ (primesLE N : Set ℕ) → MSet k c (primesLE N : Set ℕ) < MSet k c A) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hA hAN
    have hA1 : ∀ x ∈ A, 1 ≤ x := fun x hx => le_trans (by norm_num) (hA.1 x hx)
    have hPN1 : ∀ x ∈ (primesLE N : Set ℕ), 1 ≤ x := fun x hx =>
      (mem_primesLE.mp (Finset.mem_coe.mp hx)).1.one_lt.le
    -- a strict step `M(C) < M(A)` to a set handled by the induction hypothesis
    have finish : ∀ C : Set ℕ, compSum N C < n → IsPrimitive C → (∀ a ∈ C, a ≤ N) →
        MSet k c C < MSet k c A →
        MSet k c (primesLE N : Set ℕ) ≤ MSet k c A ∧
          (k < k9 → A ≠ (primesLE N : Set ℕ) → MSet k c (primesLE N : Set ℕ) < MSet k c A) := by
      intro C hCn hCp hCN hlt
      have := (ih _ hCn C rfl hCp hCN).1
      exact ⟨(this.trans_lt hlt).le, fun _ _ => this.trans_lt hlt⟩
    by_cases hall : ∀ a ∈ A, a.Prime
    · -- all prime
      have hsub : A ⊆ (primesLE N : Set ℕ) := fun a ha =>
        Finset.mem_coe.mpr (mem_primesLE.mpr ⟨hall a ha, hAN a ha⟩)
      refine ⟨MSet_anti hsub hA1 hPN1 hk1 hc, fun _ hne => ?_⟩
      obtain ⟨q, hqP, hqA⟩ : ∃ q ∈ (primesLE N : Set ℕ), q ∉ A := by
        by_contra h; push Not at h; exact hne (Set.Subset.antisymm hsub h)
      have h1 := MSet_anti (Set.insert_subset hqP hsub) (fun x hx => by
        rcases hx with rfl | hx
        · exact hPN1 _ hqP
        · exact hA1 x hx) hPN1 hk1 hc
      exact h1.trans_lt (MSet_insert_lt hqA hA1 hk1 hc)
    push Not at hall
    obtain ⟨a0, ha0, ha0p⟩ := hall
    by_cases h61 : ∃ a ∈ A, ¬ a.Prime ∧ ∃ q, q.Prime ∧ 61 ≤ q ∧ q ∣ a
    · -- (1) a large prime factor
      obtain ⟨a, ha, hap, p, hp, hp61, hpa⟩ := h61
      have hpA : p ∉ A := fun h => hap ((hA.2 p h a ha hpa) ▸ hp)
      refine finish _ (hn ▸ compSum_compress hp hAN hA.1 ha hap hpa) (compressAtSet_isPrimitive hA hp)
        ?_ (large_step hp hp61 hA hpA hk1 hk hc)
      rintro x (rfl | ⟨hx, _⟩)
      · exact (Nat.le_of_dvd (by have := hA.1 a ha; omega) hpa).trans (hAN a ha)
      · exact hAN x hx
    push Not at h61
    have h61' : ∀ a ∈ A, ¬ a.Prime → ∀ q, q.Prime → q ∣ a → q < 61 := fun a ha hap q hq hqa => by
      by_contra h; exact h61 a ha hap q hq (by omega) hqa
    by_cases h11 : ∃ a ∈ A, ¬ a.Prime ∧ ∃ q, q.Prime ∧ 11 ≤ q ∧ q ∣ a
    · -- (2) the largest prime `p ∈ [11,59]` dividing a composite
      obtain ⟨p, hp, hp11, hp59, ⟨a, ha, hap, hpa⟩, hmax⟩ := exists_max_prime h61' h11
      obtain ⟨m, B, hpmB⟩ := exists_singleParam hp hp11 hp59
      set P : Set ℕ := {q | q.Prime ∧ p < q ∧ q ≤ N}
      have hP : ∀ q ∈ P, q.Prime := fun q hq => hq.1
      have hPA : ∀ q ∈ P, ∀ b ∈ A, q ∣ b → q = b := by
        intro q hq b hb hqb
        by_cases hbp : b.Prime
        · exact (Nat.prime_dvd_prime_iff_eq hq.1 hbp).mp hqb
        · have := hmax b hb hbp q hq.1 hqb; have := hq.2.1; omega
      set A' := A ∪ P
      have hA' : IsPrimitive A' := isPrimitive_union_primes hA hP hPA
      have hA'1 : ∀ x ∈ A', 1 ≤ x := fun x hx => le_trans (by norm_num) (hA'.1 x hx)
      have hpA : p ∉ A := fun h => hap ((hA.2 p h a ha hpa) ▸ hp)
      have hpA' : p ∉ A' := by
        rintro (h | h)
        · exact hpA h
        · exact lt_irrefl p h.2.1
      have hmultA : ∀ b ∈ A', p ∣ b → b ∈ A ∧ ¬ b.Prime := by
        intro b hb hpb
        rcases hb with hb | hb
        · refine ⟨hb, fun hbp => ?_⟩
          have := (Nat.prime_dvd_prime_iff_eq hp hbp).mp hpb
          exact hpA (this ▸ hb)
        · have := (Nat.prime_dvd_prime_iff_eq hp hb.1).mp hpb
          exact absurd hb.2.1 (by omega)
      have hstep := single_step hC hpmB hA' hpA' ⟨a, Or.inl ha, hpa⟩
        (fun b hb hpb q hq hqb => hmax b (hmultA b hb hpb).1 (hmultA b hb hpb).2 q hq hqb)
        (fun q hq hpq ⟨b, hb, hpb, hqb⟩ =>
          Or.inr ⟨hq, hpq, hqb.trans (hAN b (hmultA b hb hpb).1)⟩)
        hk1 (hk.trans k9_lt_126.le) hc
      have hle : MSet k c A' ≤ MSet k c A := MSet_anti Set.subset_union_left hA1 hA'1 hk1 hc
      have hA'N : ∀ x ∈ A', x ≤ N := by
        rintro x (hx | hx)
        · exact hAN x hx
        · exact hx.2.2
      refine finish (compressAtSet p A') ?_ (compressAtSet_isPrimitive hA' hp) ?_
        (hstep.trans_le hle)
      · rw [← hn, ← compSum_union_primes (N := N) (A := A) hP]
        exact compSum_compress hp hA'N hA'.1 (Or.inl ha) hap hpa
      · rintro x (rfl | ⟨hx, _⟩)
        · exact (Nat.le_of_dvd (by have := hA.1 a ha; omega) hpa).trans (hAN a ha)
        · exact hA'N x hx
    · -- (3) every composite is `7`-smooth
      push Not at h11
      have hsm7 : ∀ a ∈ A, ¬ a.Prime → ∀ q, q.Prime → q ∣ a → q ≤ 7 := fun a ha hap q hq hqa => by
        rcases prime_le7_or_ge11 hq with h | h
        · exact h
        · exact absurd hqa (h11 a ha hap q hq h)
      have ha04 : 4 ≤ a0 := by
        have := hA.1 a0 ha0
        by_contra h
        interval_cases a0 <;> norm_num at ha0p
      have hN4 : 4 ≤ N := ha04.trans (hAN a0 ha0)
      by_cases hN6 : N ≤ 6
      · -- small `N`: direct comparison
        obtain ⟨Af, hAf⟩ := finite_of_bounded (S := A) (m := N + 1) fun a ha => by
          have := hAN a ha; omega
        subst hAf
        have hne : Af ≠ primesLE N := by
          intro h
          have := Finset.mem_coe.mp ha0
          rw [h] at this
          exact ha0p (mem_primesLE.mp this).1
        have hrun := small_cert (hC.small N (by omega) hN6) hA hAN hne
        have hpos := hrun k hk1 (hk.trans k9_lt_126.le) c hc
        have hcIcc : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
        have hdiff : MSet k c (Af : Set ℕ) - MSet k c (primesLE N : Set ℕ)
            = k * ∫ u in (0 : ℝ)..c, u ^ (k - 1) * (qProd Af u - qProd (primesLE N) u) := by
          unfold MSet
          rw [← intervalIntegral.integral_sub (intervalIntegrable_MSet _ hk1 hcIcc)
            (intervalIntegrable_MSet _ hk1 hcIcc), ← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro u _
          simp only [qProdSet_coe]
          ring
        have : 0 < MSet k c (Af : Set ℕ) - MSet k c (primesLE N : Set ℕ) := by
          rw [hdiff]; exact mul_pos (by linarith) hpos
        exact ⟨by linarith, fun _ _ => by linarith⟩
      · push Not at hN6
        -- `A'' = A ∪ (primes in [11,N]) ∪ (primes r ≤ 7 dividing no element)`
        set Pb : Set ℕ := {q | q.Prime ∧ 11 ≤ q ∧ q ≤ N}
        set Ra : Set ℕ := {r | r ∈ R4 ∧ ∀ a ∈ A, ¬ r ∣ a}
        set P : Set ℕ := Pb ∪ Ra
        have hP : ∀ q ∈ P, q.Prime := by
          rintro q (hq | hq)
          · exact hq.1
          · have := hq.1; simp [R4] at this; rcases this with rfl | rfl | rfl | rfl <;> norm_num
        have hPA : ∀ q ∈ P, ∀ b ∈ A, q ∣ b → q = b := by
          rintro q hq b hb hqb
          rcases hq with hq | hq
          · by_cases hbp : b.Prime
            · exact (Nat.prime_dvd_prime_iff_eq hq.1 hbp).mp hqb
            · have := hsm7 b hb hbp q hq.1 hqb; have := hq.2.1; omega
          · exact absurd hqb (hq.2 b hb)
        set A'' := A ∪ P
        have hA'' : IsPrimitive A'' := isPrimitive_union_primes hA hP hPA
        have hA''1 : ∀ x ∈ A'', 1 ≤ x := fun x hx => le_trans (by norm_num) (hA''.1 x hx)
        have hle : MSet k c A'' ≤ MSet k c A := MSet_anti Set.subset_union_left hA1 hA''1 hk1 hc
        set S : Set ℕ := {a ∈ A'' | ∀ q, q.Prime → q ∣ a → q ≤ 7}
        have hS : IsPrimitive S :=
          ⟨fun x hx => hA''.1 x hx.1, fun x hx y hy hxy => hA''.2 x hx.1 y hy.1 hxy⟩
        have hA''N : ∀ x ∈ A'', x ≤ N := by
          rintro x (hx | (hx | hx))
          · exact hAN x hx
          · exact hx.2.2
          · have := hx.1; simp [R4] at this; omega
        have hsplit : A'' = Pb ∪ S := by
          ext x
          constructor
          · intro hx
            by_cases hxPb : x ∈ Pb
            · exact Or.inl hxPb
            · right
              refine ⟨hx, fun q hq hqx => ?_⟩
              rcases hx with hx | (hx | hx)
              · by_cases hxp : x.Prime
                · have hqx' := (Nat.prime_dvd_prime_iff_eq hq hxp).mp hqx
                  subst hqx'
                  rcases prime_le7_or_ge11 hxp with h | h
                  · exact h
                  · exact absurd ⟨hxp, h, hAN q hx⟩ hxPb
                · exact hsm7 x hx hxp q hq hqx
              · exact absurd hx hxPb
              · have h1 := hx.1
                simp [R4] at h1
                have := Nat.le_of_dvd (by omega) hqx
                omega
          · rintro (hx | hx)
            · exact Or.inr (Or.inl hx)
            · exact hx.1
        have hcov : ∀ r ∈ R4, ∃ s ∈ S, r ∣ s := by
          intro r hr
          have hrp : r.Prime := by simp [R4] at hr; rcases hr with rfl | rfl | rfl | rfl <;> norm_num
          have hr7 : r ≤ 7 := by simp [R4] at hr; omega
          by_cases hex : ∃ a ∈ A, r ∣ a
          · obtain ⟨a, ha, hra⟩ := hex
            refine ⟨a, ⟨Or.inl ha, fun q hq hqa => ?_⟩, hra⟩
            by_cases hap : a.Prime
            · have := (Nat.prime_dvd_prime_iff_eq hrp hap).mp hra
              subst this
              have := (Nat.prime_dvd_prime_iff_eq hq hrp).mp hqa
              omega
            · exact hsm7 a ha hap q hq hqa
          · push Not at hex
            refine ⟨r, ⟨Or.inr (Or.inr ⟨hr, hex⟩), fun q hq hqr => ?_⟩, dvd_rfl⟩
            have := (Nat.prime_dvd_prime_iff_eq hq hrp).mp hqr
            omega
        have hSne : S ≠ (R4f : Set ℕ) := by
          intro h
          have : a0 ∈ S := ⟨Or.inl ha0, hsm7 a0 ha0 ha0p⟩
          rw [h, mem_R4f_iff] at this
          simp [R4] at this
          rcases this with rfl | rfl | rfl | rfl <;> norm_num at ha0p
        have hst := merged_step (S := S) (Pb := Pb) hC hS (fun s hs => hs.2) hcov hSne
          (fun q hq => ⟨hq.1, hq.2.1⟩)
          (fun q hq h11q ⟨s, hs, hqs⟩ => ⟨hq, h11q, hqs.trans (hA''N s hs.1)⟩) hk1 hk hc
        have hPN : (primesLE N : Set ℕ) = Pb ∪ (R4f : Set ℕ) := by
          ext q
          simp only [Finset.mem_coe, mem_primesLE, Set.mem_union]
          constructor
          · rintro ⟨hq, hqN⟩
            rcases prime_le7_or_ge11 hq with h | h
            · exact Or.inr (mem_R4f_iff.mpr (prime_in_R4 hq h))
            · exact Or.inl ⟨hq, h, hqN⟩
          · rintro (hq | hq)
            · exact ⟨hq.1, hq.2.2⟩
            · have hq' : q ∈ R4 := mem_R4f_iff.mp hq
              refine ⟨?_, ?_⟩
              · simp [R4] at hq'; rcases hq' with rfl | rfl | rfl | rfl <;> norm_num
              · simp [R4] at hq'; omega
        rw [hPN]
        rw [← hsplit] at hst
        exact ⟨hst.1.trans hle, fun hlt _ => (hst.2 hlt).trans_le hle⟩

/-- **Theorem 3.8, finite sets** (from the case checks). -/
theorem k9_primesLE_of (hC : K9Certs) {k : ℝ} (hk0 : 0 < k) (hk : k ≤ k9) {N : ℕ}
    {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) ≤ MSet k c (A : Set ℕ) ∧
      (k < k9 → A ≠ primesLE N → MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ)) := by
  rcases le_or_gt k 1 with h1 | h1
  · have hlt : A ≠ primesLE N → MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) :=
      fun hne => MSet_primesLE_lt_small hk0 h1 hA hAN hne hc
    refine ⟨?_, fun _ => hlt⟩
    by_cases h : A = primesLE N
    · rw [h]
    · exact (hlt h).le
  · obtain ⟨h1', h2'⟩ := k9_fin_aux hC h1.le hk hc N _ (A : Set ℕ) rfl hA (fun a ha => hAN a ha)
    exact ⟨h1', fun hlt hne => h2' hlt (fun h => hne (by exact_mod_cast h))⟩

end RntPaper.K9

namespace RntPaper.K9

open MeasureTheory intervalIntegral Set CP QProduct

/-! ## Arbitrary primitive sets -/

theorem k9_primes_le_aux (hC : K9Certs) {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ k9) {A : Set ℕ}
    (hA : IsPrimitive A) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c Primes ≤ MSet k c A := by
  classical
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hP := tendsto_MSet_truncation Primes hk1 hcI
  simp only [primes_truncation] at hP
  refine le_of_tendsto_of_tendsto' hP (tendsto_MSet_truncation A hk1 hcI) fun N => ?_
  exact (k9_fin_aux hC hk1 hk hc N _ _ rfl (truncation_isPrimitiveFin hA N)
    (fun a ha => truncation_bounded A N a (by exact_mod_cast ha))).1

theorem k9_primes_lt_aux (hC : K9Certs) {k : ℝ} (hk1 : 1 ≤ k) (hk : k < k9) {A : Set ℕ}
    (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A := by
  classical
  have hA1 : ∀ x ∈ A, 1 ≤ x := fun x hx => le_trans (by norm_num) (hA.1 x hx)
  have hlow : ∀ C : Set ℕ, IsPrimitive C → MSet k c Primes ≤ MSet k c C := fun C hC' =>
    k9_primes_le_aux hC hk1 hk.le hC' hc
  by_cases hall : ∀ a ∈ A, a.Prime
  · have hsub : A ⊆ Primes := fun a ha => hall a ha
    obtain ⟨q, hqP, hqA⟩ : ∃ q ∈ Primes, q ∉ A := by
      by_contra h; push Not at h; exact hne (Set.Subset.antisymm hsub h)
    have hA' : IsPrimitive (insert q A) := by
      refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
      · rcases ha with rfl | ha
        · exact Nat.Prime.two_le hqP
        · exact hA.1 a ha
      · have hpa : a.Prime := by rcases ha with rfl | ha; exacts [hqP, hall a ha]
        have hpb : b.Prime := by rcases hb with rfl | hb; exacts [hqP, hall b hb]
        exact (Nat.prime_dvd_prime_iff_eq hpa hpb).mp hab
    exact (hlow _ hA').trans_lt (MSet_insert_lt hqA hA1 hk1 hc)
  push Not at hall
  obtain ⟨a0, ha0, ha0p⟩ := hall
  by_cases h61 : ∃ a ∈ A, ¬ a.Prime ∧ ∃ q, q.Prime ∧ 61 ≤ q ∧ q ∣ a
  · obtain ⟨a, ha, hap, p, hp, hp61, hpa⟩ := h61
    have hpA : p ∉ A := fun h => hap ((hA.2 p h a ha hpa) ▸ hp)
    exact (hlow _ (compressAtSet_isPrimitive hA hp)).trans_lt
      (large_step hp hp61 hA hpA hk1 hk.le hc)
  push Not at h61
  have h61' : ∀ a ∈ A, ¬ a.Prime → ∀ q, q.Prime → q ∣ a → q < 61 := fun a ha hap q hq hqa => by
    by_contra h; exact h61 a ha hap q hq (by omega) hqa
  by_cases h11 : ∃ a ∈ A, ¬ a.Prime ∧ ∃ q, q.Prime ∧ 11 ≤ q ∧ q ∣ a
  · obtain ⟨p, hp, hp11, hp59, ⟨a, ha, hap, hpa⟩, hmax⟩ := exists_max_prime h61' h11
    obtain ⟨m, B, hpmB⟩ := exists_singleParam hp hp11 hp59
    set P : Set ℕ := {q | q.Prime ∧ p < q}
    have hP : ∀ q ∈ P, q.Prime := fun q hq => hq.1
    have hPA : ∀ q ∈ P, ∀ b ∈ A, q ∣ b → q = b := by
      intro q hq b hb hqb
      by_cases hbp : b.Prime
      · exact (Nat.prime_dvd_prime_iff_eq hq.1 hbp).mp hqb
      · have := hmax b hb hbp q hq.1 hqb; have := hq.2; omega
    set A' := A ∪ P
    have hA' : IsPrimitive A' := isPrimitive_union_primes hA hP hPA
    have hA'1 : ∀ x ∈ A', 1 ≤ x := fun x hx => le_trans (by norm_num) (hA'.1 x hx)
    have hpA : p ∉ A := fun h => hap ((hA.2 p h a ha hpa) ▸ hp)
    have hpA' : p ∉ A' := by
      rintro (h | h)
      · exact hpA h
      · exact lt_irrefl p h.2
    have hmultA : ∀ b ∈ A', p ∣ b → b ∈ A ∧ ¬ b.Prime := by
      intro b hb hpb
      rcases hb with hb | hb
      · refine ⟨hb, fun hbp => ?_⟩
        have := (Nat.prime_dvd_prime_iff_eq hp hbp).mp hpb
        exact hpA (this ▸ hb)
      · have := (Nat.prime_dvd_prime_iff_eq hp hb.1).mp hpb
        exact absurd hb.2 (by omega)
    have hstep := single_step hC hpmB hA' hpA' ⟨a, Or.inl ha, hpa⟩
      (fun b hb hpb q hq hqb => hmax b (hmultA b hb hpb).1 (hmultA b hb hpb).2 q hq hqb)
      (fun q hq hpq _ => Or.inr ⟨hq, hpq⟩) hk1 (hk.le.trans k9_lt_126.le) hc
    have hle : MSet k c A' ≤ MSet k c A := MSet_anti Set.subset_union_left hA1 hA'1 hk1 hc
    exact (hlow _ (compressAtSet_isPrimitive hA' hp)).trans_lt (hstep.trans_le hle)
  · push Not at h11
    have hsm7 : ∀ a ∈ A, ¬ a.Prime → ∀ q, q.Prime → q ∣ a → q ≤ 7 := fun a ha hap q hq hqa => by
      rcases prime_le7_or_ge11 hq with h | h
      · exact h
      · exact absurd hqa (h11 a ha hap q hq h)
    set Pb : Set ℕ := {q | q.Prime ∧ 11 ≤ q}
    set Ra : Set ℕ := {r | r ∈ R4 ∧ ∀ a ∈ A, ¬ r ∣ a}
    set P : Set ℕ := Pb ∪ Ra
    have hP : ∀ q ∈ P, q.Prime := by
      rintro q (hq | hq)
      · exact hq.1
      · have := hq.1; simp [R4] at this; rcases this with rfl | rfl | rfl | rfl <;> norm_num
    have hPA : ∀ q ∈ P, ∀ b ∈ A, q ∣ b → q = b := by
      rintro q hq b hb hqb
      rcases hq with hq | hq
      · by_cases hbp : b.Prime
        · exact (Nat.prime_dvd_prime_iff_eq hq.1 hbp).mp hqb
        · have := hsm7 b hb hbp q hq.1 hqb; have := hq.2; omega
      · exact absurd hqb (hq.2 b hb)
    set A'' := A ∪ P
    have hA'' : IsPrimitive A'' := isPrimitive_union_primes hA hP hPA
    have hA''1 : ∀ x ∈ A'', 1 ≤ x := fun x hx => le_trans (by norm_num) (hA''.1 x hx)
    have hle : MSet k c A'' ≤ MSet k c A := MSet_anti Set.subset_union_left hA1 hA''1 hk1 hc
    set S : Set ℕ := {a ∈ A'' | ∀ q, q.Prime → q ∣ a → q ≤ 7}
    have hS : IsPrimitive S :=
      ⟨fun x hx => hA''.1 x hx.1, fun x hx y hy hxy => hA''.2 x hx.1 y hy.1 hxy⟩
    have hsplit : A'' = Pb ∪ S := by
      ext x
      constructor
      · intro hx
        by_cases hxPb : x ∈ Pb
        · exact Or.inl hxPb
        · right
          refine ⟨hx, fun q hq hqx => ?_⟩
          rcases hx with hx | (hx | hx)
          · by_cases hxp : x.Prime
            · have hqx' := (Nat.prime_dvd_prime_iff_eq hq hxp).mp hqx
              subst hqx'
              rcases prime_le7_or_ge11 hxp with h | h
              · exact h
              · exact absurd ⟨hxp, h⟩ hxPb
            · exact hsm7 x hx hxp q hq hqx
          · exact absurd hx hxPb
          · have h1 := hx.1
            simp [R4] at h1
            have := Nat.le_of_dvd (by omega) hqx
            omega
      · rintro (hx | hx)
        · exact Or.inr (Or.inl hx)
        · exact hx.1
    have hcov : ∀ r ∈ R4, ∃ s ∈ S, r ∣ s := by
      intro r hr
      have hrp : r.Prime := by simp [R4] at hr; rcases hr with rfl | rfl | rfl | rfl <;> norm_num
      by_cases hex : ∃ a ∈ A, r ∣ a
      · obtain ⟨a, ha, hra⟩ := hex
        refine ⟨a, ⟨Or.inl ha, fun q hq hqa => ?_⟩, hra⟩
        by_cases hap : a.Prime
        · have := (Nat.prime_dvd_prime_iff_eq hrp hap).mp hra
          subst this
          have := (Nat.prime_dvd_prime_iff_eq hq hrp).mp hqa
          have hr7 : r ≤ 7 := by simp [R4] at hr; omega
          omega
        · exact hsm7 a ha hap q hq hqa
      · push Not at hex
        refine ⟨r, ⟨Or.inr (Or.inr ⟨hr, hex⟩), fun q hq hqr => ?_⟩, dvd_rfl⟩
        have := (Nat.prime_dvd_prime_iff_eq hq hrp).mp hqr
        have hr7 : r ≤ 7 := by simp [R4] at hr; omega
        omega
    have hSne : S ≠ (R4f : Set ℕ) := by
      intro h
      have : a0 ∈ S := ⟨Or.inl ha0, hsm7 a0 ha0 ha0p⟩
      rw [h, mem_R4f_iff] at this
      simp [R4] at this
      rcases this with rfl | rfl | rfl | rfl <;> norm_num at ha0p
    have hst := merged_step (S := S) (Pb := Pb) hC hS (fun s hs => hs.2) hcov hSne
      (fun q hq => ⟨hq.1, hq.2⟩) (fun q hq h11q _ => ⟨hq, h11q⟩) hk1 hk.le hc
    have hPrimes : Primes = Pb ∪ (R4f : Set ℕ) := by
      ext q
      simp only [Primes, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · intro hq
        rcases prime_le7_or_ge11 hq with h | h
        · exact Or.inr (mem_R4f_iff.mpr (prime_in_R4 hq h))
        · exact Or.inl ⟨hq, h⟩
      · rintro (hq | hq)
        · exact hq.1
        · have hq' : q ∈ R4 := mem_R4f_iff.mp hq
          simp [R4] at hq'; rcases hq' with rfl | rfl | rfl | rfl <;> norm_num
    rw [hPrimes]
    rw [← hsplit] at hst
    exact (hst.2 hk).trans_le hle

/-- **Theorem 3.8, arbitrary primitive sets** (from the case checks). -/
theorem k9_primes_of (hC : K9Certs) {k : ℝ} (hk0 : 0 < k) (hk : k ≤ k9) {A : Set ℕ}
    (hA : IsPrimitive A) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes ≤ MSet k c A ∧ (k < k9 → A ≠ Primes → MSet k c Primes < MSet k c A) := by
  rcases le_or_gt k 1 with h1 | h1
  · have hlt : A ≠ Primes → MSet k c Primes < MSet k c A :=
      fun hne => MSet_primes_lt_small hk0 h1 hA hne hc
    refine ⟨?_, fun _ => hlt⟩
    by_cases h : A = Primes
    · rw [h]
    · exact (hlt h).le
  · exact ⟨k9_primes_le_aux hC h1.le hk hA hc, fun hlt hne => k9_primes_lt_aux hC h1.le hlt hA hne hc⟩

end RntPaper.K9
