import RntPaper.SingleCrossing
import RntPaper.InfiniteProduct

/-!
# The universal product inequality (paper Theorem 1.4)

Two independent routes exist for finite `T`:

* the **elementary route** of `SingleCrossing.lean` plus antitonicity
  `P_T ≥ H` (paper §2), which also covers infinite `T`;
* the **certificate route** already machine-checked in productinvariants
  (`block_partial_pos_of_two_le`, cutoff-16 Bernstein certificate,
  `native_decide`), finite `T` only.  Its uniform error term `Err₁₆(c)` extends
  it to infinite `T` by a limit with a uniform positive margin.
-/

namespace RntPaper

open QProduct MeasureTheory Set

/-- `P_T ≥ H` pointwise for every `T ⊆ {2,3,…}` (paper (2.1)). -/
theorem Hfun_le_qProdSet {T : Set ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : Hfun x ≤ qProdSet T x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, Hfun_one]
    exact qProdSet_nonneg T ⟨zero_le_one, le_rfl⟩
  · exact Hfun_le_qProdSet_of_lt (fun n hn => hT n hn) hx.1 h

theorem Hfun_le_qProd {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : Hfun x ≤ qProd T x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, Hfun_one]
    exact qProd_nonneg T ⟨zero_le_one, le_rfl⟩
  · exact Hfun_le_qProd_of_lt T hT hx.1 h

/-- `∫₀ᵈ (1 - x) dx = d - d²/2`. -/
theorem integral_one_sub_id (d : ℝ) : (∫ x in (0:ℝ)..d, (1 - x)) = d - d ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
  simp

/-- `∫₀ᶜ H ≤ ∫₀ᶜ P_T` for finite `T ⊆ {2,3,…}`, `c ∈ [0,1]`. -/
theorem integral_Hfun_le_Fc {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..c, Hfun x) ≤ Fc c T := by
  unfold Fc
  exact intervalIntegral.integral_mono_on hc.1
    (Hfun_intervalIntegrable ⟨le_rfl, zero_le_one⟩ hc) (intervalIntegrable_qProd T 0 c)
    (fun u hu => Hfun_le_qProd hT ⟨hu.1, hu.2.trans hc.2⟩)

/-- **Theorem 1.4, finite `T`, running-integral form.** -/
theorem running_pos_fin {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) :
    c - c ^ 2 / 2 < ∫ v in (0 : ℝ)..c, qProd T v :=
  (running_pos_Hfun hc).trans_le (integral_Hfun_le_Fc hT ⟨hc.1.le, hc.2⟩)

/-- **Theorem 1.4, finite `T`** (= productinvariants `blockE_partial_pos`). -/
theorem blockE_partial_pos {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..c, blockE T v := by
  unfold blockE
  rw [intervalIntegral.integral_sub (intervalIntegrable_qProd T 0 c)
    (intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_id),
    integral_one_sub_id]
  linarith [running_pos_fin hT hc]

/-- `∫₀ᶜ H ≤ ∫₀ᶜ P_T` for arbitrary `T ⊆ {2,3,…}`, `c ∈ [0,1]`. -/
theorem integral_Hfun_le_FcSet {T : Set ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..c, Hfun x) ≤ FcSet c T := by
  classical
  refine le_FcSet_of_forall_le_Fc T hc fun N => integral_Hfun_le_Fc ?_ hc
  intro n hn
  exact hT n (Finset.mem_filter.mp hn).2

/-- **Theorem 1.4, arbitrary `T`.** -/
theorem running_pos_set {T : Set ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) :
    c - c ^ 2 / 2 < ∫ v in (0 : ℝ)..c, qProdSet T v :=
  (running_pos_Hfun hc).trans_le (integral_Hfun_le_FcSet hT ⟨hc.1.le, hc.2⟩)

/-- `∫₀ᶜ E_T = ∫₀ᶜ P_T - (c - c²/2)` for `c ∈ [0,1]`. -/
theorem integral_blockESet (T : Set ℕ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    (∫ v in (0 : ℝ)..c, blockESet T v) =
      (∫ v in (0 : ℝ)..c, qProdSet T v) - (c - c ^ 2 / 2) := by
  unfold blockESet
  rw [intervalIntegral.integral_sub (intervalIntegrable_qProdSet T hc)
    (intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_id),
    integral_one_sub_id]

theorem blockESet_partial_pos {T : Set ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..c, blockESet T v := by
  rw [integral_blockESet T ⟨hc.1.le, hc.2⟩]
  linarith [running_pos_set hT hc]

/-- **Remark 2.3 (sets versus multisets).** Three copies of the exponent `2`
defeat the inequality at `c = 1`: `∫₀¹(1 - v²)³ = 16/35 < 1/2`. -/
theorem integral_one_sub_sq_cube :
    (∫ v in (0 : ℝ)..1, (1 - v ^ 2) ^ 3) = 16 / 35 := by
  leancert

theorem multiset_counterexample :
    (∫ v in (0 : ℝ)..1, (1 - v ^ 2) ^ 3) < 1 / 2 := by
  rw [integral_one_sub_sq_cube]; norm_num

end RntPaper
