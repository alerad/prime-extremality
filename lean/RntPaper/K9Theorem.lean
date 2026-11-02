import RntPaper.K9Main
import RntPaper.K9Cert.MTail2357_0
import RntPaper.K9Cert.MTail2357_1
import RntPaper.K9Cert.MTail2357_2
import RntPaper.K9Cert.MTail2357_3
import RntPaper.K9Cert.MTail2357_4
import RntPaper.K9Cert.MTail2357_5
import RntPaper.K9Cert.MTail235_0
import RntPaper.K9Cert.MTail235_1
import RntPaper.K9Cert.MTail235_2
import RntPaper.K9Cert.MTail235_3
import RntPaper.K9Cert.MTail235_4
import RntPaper.K9Cert.MTail235_5
import RntPaper.K9Cert.MTail237_0
import RntPaper.K9Cert.MTail237_1
import RntPaper.K9Cert.MTail237_2
import RntPaper.K9Cert.MTail237_3
import RntPaper.K9Cert.MTail237_4
import RntPaper.K9Cert.MTail237_5
import RntPaper.K9Cert.MTail23_0
import RntPaper.K9Cert.MTail23_1
import RntPaper.K9Cert.MTail257_0
import RntPaper.K9Cert.MTail257_1
import RntPaper.K9Cert.MTail257_2
import RntPaper.K9Cert.MTail257_3
import RntPaper.K9Cert.MTail257_4
import RntPaper.K9Cert.MTail257_5
import RntPaper.K9Cert.MTail25_0
import RntPaper.K9Cert.MTail25_1
import RntPaper.K9Cert.MTail27_0
import RntPaper.K9Cert.MTail27_1
import RntPaper.K9Cert.MTail2_0
import RntPaper.K9Cert.MTail357_0
import RntPaper.K9Cert.MTail357_1
import RntPaper.K9Cert.MTail357_2
import RntPaper.K9Cert.MTail357_3
import RntPaper.K9Cert.MTail357_4
import RntPaper.K9Cert.MTail357_5
import RntPaper.K9Cert.MTail35_0
import RntPaper.K9Cert.MTail35_1
import RntPaper.K9Cert.MTail37_0
import RntPaper.K9Cert.MTail37_1
import RntPaper.K9Cert.MTail3_0
import RntPaper.K9Cert.MTail57_0
import RntPaper.K9Cert.MTail57_1
import RntPaper.K9Cert.MTail5_0
import RntPaper.K9Cert.MTail7_0
import RntPaper.K9Cert.Merged0
import RntPaper.K9Cert.Merged1
import RntPaper.K9Cert.Merged10
import RntPaper.K9Cert.Merged11
import RntPaper.K9Cert.Merged12
import RntPaper.K9Cert.Merged13
import RntPaper.K9Cert.Merged14
import RntPaper.K9Cert.Merged15
import RntPaper.K9Cert.Merged2
import RntPaper.K9Cert.Merged3
import RntPaper.K9Cert.Merged4
import RntPaper.K9Cert.Merged5
import RntPaper.K9Cert.Merged6
import RntPaper.K9Cert.Merged7
import RntPaper.K9Cert.Merged8
import RntPaper.K9Cert.Merged9
import RntPaper.K9Cert.Single11_0
import RntPaper.K9Cert.Single11_1
import RntPaper.K9Cert.Single11_10
import RntPaper.K9Cert.Single11_11
import RntPaper.K9Cert.Single11_2
import RntPaper.K9Cert.Single11_3
import RntPaper.K9Cert.Single11_4
import RntPaper.K9Cert.Single11_5
import RntPaper.K9Cert.Single11_6
import RntPaper.K9Cert.Single11_7
import RntPaper.K9Cert.Single11_8
import RntPaper.K9Cert.Single11_9
import RntPaper.K9Cert.Single13_0
import RntPaper.K9Cert.Single13_1
import RntPaper.K9Cert.Single13_2
import RntPaper.K9Cert.Single13_3
import RntPaper.K9Cert.Single13_4
import RntPaper.K9Cert.Single13_5
import RntPaper.K9Cert.Single17_0
import RntPaper.K9Cert.Single17_1
import RntPaper.K9Cert.Single17_2
import RntPaper.K9Cert.Single19_0
import RntPaper.K9Cert.Single19_1
import RntPaper.K9Cert.Single23_0
import RntPaper.K9Cert.Single29_0
import RntPaper.K9Cert.Single31_0
import RntPaper.K9Cert.Single37_0
import RntPaper.K9Cert.Single41_0
import RntPaper.K9Cert.Single43_0
import RntPaper.K9Cert.Single47_0
import RntPaper.K9Cert.Single53_0
import RntPaper.K9Cert.Single59_0
import RntPaper.K9Cert.Small
import RntPaper.K9Cert.Tail11_0
import RntPaper.K9Cert.Tail11_1
import RntPaper.K9Cert.Tail11_2
import RntPaper.K9Cert.Tail11_3
import RntPaper.K9Cert.Tail13_0
import RntPaper.K9Cert.Tail13_1
import RntPaper.K9Cert.Tail13_2
import RntPaper.K9Cert.Tail13_3
import RntPaper.K9Cert.Tail17_0
import RntPaper.K9Cert.Tail19_0
import RntPaper.K9Cert.Tail23_0
import RntPaper.K9Cert.Tail29_0
import RntPaper.K9Cert.Tail31_0
import RntPaper.K9Cert.Tail37_0
import RntPaper.K9Cert.Tail41_0
import RntPaper.K9Cert.Tail43_0
import RntPaper.K9Cert.Tail47_0
import RntPaper.K9Cert.Tail53_0
import RntPaper.K9Cert.Tail59_0

/-!
# Theorem 3.8 of the notes: the exact moment threshold `k₉`

The case checks of `K9Cert/*` (by `native_decide`) give `K9Certs`; with `K9Main` this proves
that the primes minimize `𝔼 min(Z_A^k, c^k)` over primitive sets for every `0 < k ≤ k₉`,
strictly for `k < k₉`, and that `A₉ = {4,5,6,7,9}` beats `𝒫₉` for every `k > k₉`.
-/

namespace RntPaper.K9

open MeasureTheory Set QProduct

theorem all_of_parts {α : Type} (L : List α) (key : α → ℕ) (P : α → Bool) (q : ℕ) (hq : 0 < q)
    (h : ∀ j < q, (L.all fun x => key x % q != j || P x) = true) : ∀ x ∈ L, P x = true := by
  intro x hx
  have h1 := h (key x % q) (Nat.mod_lt _ hq)
  rw [List.all_eq_true] at h1
  simpa using h1 x hx

theorem merged_all : MergedOKAll := by
  intro l hl
  refine all_of_parts _ List.sum mergedOK 16 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [merged_part_0, merged_part_1, merged_part_2, merged_part_3, merged_part_4, merged_part_5, merged_part_6, merged_part_7, merged_part_8, merged_part_9, merged_part_10, merged_part_11, merged_part_12, merged_part_13, merged_part_14, merged_part_15]

theorem single_ok_11 : SingleOKAll 11 30 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 11 30) 12 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [single_11_part_0, single_11_part_1, single_11_part_2, single_11_part_3, single_11_part_4, single_11_part_5, single_11_part_6, single_11_part_7, single_11_part_8, single_11_part_9, single_11_part_10, single_11_part_11]

theorem tail_ok_11 : SingleTailOKAll 11 30 24 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 11 30 24) 4 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [tail_11_part_0, tail_11_part_1, tail_11_part_2, tail_11_part_3]

theorem single_ok_13 : SingleOKAll 13 24 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 13 24) 6 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [single_13_part_0, single_13_part_1, single_13_part_2, single_13_part_3, single_13_part_4, single_13_part_5]

theorem tail_ok_13 : SingleTailOKAll 13 24 20 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 13 24 20) 4 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [tail_13_part_0, tail_13_part_1, tail_13_part_2, tail_13_part_3]

theorem single_ok_17 : SingleOKAll 17 20 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 17 20) 3 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [single_17_part_0, single_17_part_1, single_17_part_2]

theorem tail_ok_17 : SingleTailOKAll 17 20 16 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 17 20 16) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_17_part_0

theorem single_ok_19 : SingleOKAll 19 16 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 19 16) 2 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [single_19_part_0, single_19_part_1]

theorem tail_ok_19 : SingleTailOKAll 19 16 14 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 19 16 14) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_19_part_0

theorem single_ok_23 : SingleOKAll 23 14 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 23 14) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_23_part_0

theorem tail_ok_23 : SingleTailOKAll 23 14 12 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 23 14 12) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_23_part_0

theorem single_ok_29 : SingleOKAll 29 12 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 29 12) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_29_part_0

theorem tail_ok_29 : SingleTailOKAll 29 12 10 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 29 12 10) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_29_part_0

theorem single_ok_31 : SingleOKAll 31 10 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 31 10) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_31_part_0

theorem tail_ok_31 : SingleTailOKAll 31 10 9 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 31 10 9) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_31_part_0

theorem single_ok_37 : SingleOKAll 37 9 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 37 9) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_37_part_0

theorem tail_ok_37 : SingleTailOKAll 37 9 8 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 37 9 8) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_37_part_0

theorem single_ok_41 : SingleOKAll 41 8 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 41 8) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_41_part_0

theorem tail_ok_41 : SingleTailOKAll 41 8 7 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 41 8 7) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_41_part_0

theorem single_ok_43 : SingleOKAll 43 8 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 43 8) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_43_part_0

theorem tail_ok_43 : SingleTailOKAll 43 8 7 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 43 8 7) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_43_part_0

theorem single_ok_47 : SingleOKAll 47 6 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 47 6) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_47_part_0

theorem tail_ok_47 : SingleTailOKAll 47 6 6 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 47 6 6) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_47_part_0

theorem single_ok_53 : SingleOKAll 53 6 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 53 6) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_53_part_0

theorem tail_ok_53 : SingleTailOKAll 53 6 6 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 53 6 6) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_53_part_0

theorem single_ok_59 : SingleOKAll 59 5 := by
  intro l hl
  refine all_of_parts _ List.sum (singleOK 59 5) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact single_59_part_0

theorem tail_ok_59 : SingleTailOKAll 59 5 5 := by
  intro l hl
  refine all_of_parts _ List.sum (singleTailOK 59 5 5) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact tail_59_part_0

theorem mtail_ok_2 : MergedTailOKAll [2] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [2]) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact mtail_2_part_0

theorem mtail_ok_3 : MergedTailOKAll [3] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [3]) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact mtail_3_part_0

theorem mtail_ok_5 : MergedTailOKAll [5] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [5]) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact mtail_5_part_0

theorem mtail_ok_7 : MergedTailOKAll [7] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [7]) 1 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exact mtail_7_part_0

theorem mtail_ok_23 : MergedTailOKAll [2, 3] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [2, 3]) 2 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_23_part_0, mtail_23_part_1]

theorem mtail_ok_25 : MergedTailOKAll [2, 5] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [2, 5]) 2 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_25_part_0, mtail_25_part_1]

theorem mtail_ok_27 : MergedTailOKAll [2, 7] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [2, 7]) 2 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_27_part_0, mtail_27_part_1]

theorem mtail_ok_35 : MergedTailOKAll [3, 5] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [3, 5]) 2 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_35_part_0, mtail_35_part_1]

theorem mtail_ok_37 : MergedTailOKAll [3, 7] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [3, 7]) 2 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_37_part_0, mtail_37_part_1]

theorem mtail_ok_57 : MergedTailOKAll [5, 7] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [5, 7]) 2 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_57_part_0, mtail_57_part_1]

theorem mtail_ok_235 : MergedTailOKAll [2, 3, 5] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [2, 3, 5]) 6 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_235_part_0, mtail_235_part_1, mtail_235_part_2, mtail_235_part_3, mtail_235_part_4, mtail_235_part_5]

theorem mtail_ok_237 : MergedTailOKAll [2, 3, 7] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [2, 3, 7]) 6 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_237_part_0, mtail_237_part_1, mtail_237_part_2, mtail_237_part_3, mtail_237_part_4, mtail_237_part_5]

theorem mtail_ok_257 : MergedTailOKAll [2, 5, 7] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [2, 5, 7]) 6 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_257_part_0, mtail_257_part_1, mtail_257_part_2, mtail_257_part_3, mtail_257_part_4, mtail_257_part_5]

theorem mtail_ok_357 : MergedTailOKAll [3, 5, 7] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [3, 5, 7]) 6 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_357_part_0, mtail_357_part_1, mtail_357_part_2, mtail_357_part_3, mtail_357_part_4, mtail_357_part_5]

theorem mtail_ok_2357 : MergedTailOKAll [2, 3, 5, 7] := by
  intro l hl
  refine all_of_parts _ List.sum (mergedTailOK [2, 3, 5, 7]) 6 (by norm_num) (fun j hj => ?_) l hl
  interval_cases j
  exacts [mtail_2357_part_0, mtail_2357_part_1, mtail_2357_part_2, mtail_2357_part_3, mtail_2357_part_4, mtail_2357_part_5]

theorem mtail_all : ∀ Rp ∈ RpList, MergedTailOKAll Rp := by
  intro Rp hRp
  simp only [RpList, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hRp
  rcases hRp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [mtail_ok_2, mtail_ok_3, mtail_ok_5, mtail_ok_7, mtail_ok_23, mtail_ok_25, mtail_ok_27, mtail_ok_35, mtail_ok_37, mtail_ok_57, mtail_ok_235, mtail_ok_237, mtail_ok_257, mtail_ok_357, mtail_ok_2357]

theorem single_all : ∀ p m B : ℕ, (p, m, B) ∈ singleParams → SingleOKAll p m ∧ SingleTailOKAll p m B := by
  intro p m B h
  simp only [singleParams, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  exacts [⟨single_ok_11, tail_ok_11⟩, ⟨single_ok_13, tail_ok_13⟩, ⟨single_ok_17, tail_ok_17⟩, ⟨single_ok_19, tail_ok_19⟩, ⟨single_ok_23, tail_ok_23⟩, ⟨single_ok_29, tail_ok_29⟩, ⟨single_ok_31, tail_ok_31⟩, ⟨single_ok_37, tail_ok_37⟩, ⟨single_ok_41, tail_ok_41⟩, ⟨single_ok_43, tail_ok_43⟩, ⟨single_ok_47, tail_ok_47⟩, ⟨single_ok_53, tail_ok_53⟩, ⟨single_ok_59, tail_ok_59⟩]

theorem small_all : ∀ N : ℕ, 2 ≤ N → N ≤ 6 → SmallOKAll N := by
  intro N h2 h6
  interval_cases N
  exacts [fun l hl => List.all_eq_true.mp small_2 l hl, fun l hl => List.all_eq_true.mp small_3 l hl, fun l hl => List.all_eq_true.mp small_4 l hl, fun l hl => List.all_eq_true.mp small_5 l hl, fun l hl => List.all_eq_true.mp small_6 l hl]

/-- All case checks hold. -/
theorem k9Certs : K9Certs := ⟨merged_all, mtail_all, single_all, small_all⟩

/-- **Theorem 3.8, finite sets.** For `0 < k ≤ k₉`, every `N`, every primitive `A ⊆ {2,…,N}`
and every `c ∈ (0,1]`: `𝔼 min(Z_{𝒫_N}^k, c^k) ≤ 𝔼 min(Z_A^k, c^k)`, strictly if `k < k₉` and
`A ≠ 𝒫_N`. -/
theorem moment_primesLE_k9 {k : ℝ} (hk0 : 0 < k) (hk : k ≤ k9) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) ≤ MSet k c (A : Set ℕ) ∧
      (k < k9 → A ≠ primesLE N → MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ)) :=
  k9_primesLE_of k9Certs hk0 hk hA hAN hc

/-- **Theorem 3.8, arbitrary primitive sets.** -/
theorem moment_primes_k9 {k : ℝ} (hk0 : 0 < k) (hk : k ≤ k9) {A : Set ℕ} (hA : IsPrimitive A)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes ≤ MSet k c A ∧ (k < k9 → A ≠ Primes → MSet k c Primes < MSet k c A) :=
  k9_primes_of k9Certs hk0 hk hA hc

theorem primesLE_nine : primesLE 9 = R4f := by decide

theorem A9f_isPrimitive : IsPrimitiveFin A9f := by
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · simp only [A9f, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    omega
  · simp only [A9f, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; revert hab; decide)

/-- `𝔼 Z_{A₉}^k - 𝔼 Z_{𝒫₉}^k = k · fA9 k`. -/
theorem MSet_A9_sub (k : ℝ) (hk : 1 ≤ k) :
    MSet k 1 (A9f : Set ℕ) - MSet k 1 (primesLE 9 : Set ℕ) = k * fA9 k := by
  unfold MSet fA9
  rw [← intervalIntegral.integral_sub (intervalIntegrable_MSet _ hk ⟨zero_le_one, le_rfl⟩)
    (intervalIntegrable_MSet _ hk ⟨zero_le_one, le_rfl⟩), ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [qProdSet_coe, primesLE_nine]
  ring

/-- **Sharpness.** For every `k > k₉` the set `A₉ = {4,5,6,7,9}` beats the primes at `N = 9`,
`c = 1`: `𝔼 Z_{A₉}^k < 𝔼 Z_{𝒫₉}^k`. -/
theorem moment_A9_lt {k : ℝ} (hk : k9 < k) :
    MSet k 1 (A9f : Set ℕ) < MSet k 1 (primesLE 9 : Set ℕ) := by
  have hk1 : 1 ≤ k := (one_lt_k9.trans hk).le
  have h := MSet_A9_sub k hk1
  have := mul_neg_of_pos_of_neg (by linarith : 0 < k) (fA9_neg hk)
  linarith

/-- **The exact threshold.** `k₉` is the largest exponent for which the primes minimize
`𝔼 Z_A^k` over primitive `A ⊆ {2,…,N}` for every `N`. -/
theorem k9_threshold (k : ℝ) (hk0 : 0 < k) :
    (∀ N : ℕ, ∀ A : Finset ℕ, IsPrimitiveFin A → (∀ a ∈ A, a ≤ N) →
      MSet k 1 (primesLE N : Set ℕ) ≤ MSet k 1 (A : Set ℕ)) ↔ k ≤ k9 := by
  constructor
  · intro h
    by_contra hk
    push Not at hk
    have := h 9 A9f A9f_isPrimitive (by decide)
    linarith [moment_A9_lt hk]
  · intro hk N A hA hAN
    exact (moment_primesLE_k9 hk0 hk hA hAN ⟨one_pos, le_rfl⟩).1

end RntPaper.K9

namespace RntPaper.K9

open MeasureTheory Set QProduct

/-- **`k₉` is the unique positive root** of `𝔼 Z_{A₉}^k = 𝔼 Z_{𝒫₉}^k`. -/
theorem k9_unique_root {k : ℝ} (hk0 : 0 < k) :
    MSet k 1 (A9f : Set ℕ) = MSet k 1 (primesLE 9 : Set ℕ) ↔ k = k9 := by
  rcases le_or_gt k 1 with h1 | h1
  · have hne : A9f ≠ primesLE 9 := by rw [primesLE_nine]; decide
    have := MSet_primesLE_lt_small hk0 h1 A9f_isPrimitive (by decide) hne ⟨one_pos, le_rfl⟩
    constructor
    · intro h; linarith
    · intro h; have := one_lt_k9; linarith
  · rw [← sub_eq_zero, MSet_A9_sub k h1.le]
    constructor
    · intro h
      have : fA9 k = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · linarith
        · exact h'
      exact (fA9_eq_zero_iff h1.le).mp this
    · rintro rfl; rw [fA9_k9, mul_zero]

end RntPaper.K9
