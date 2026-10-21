import RntPaper.Qfun
import RntPaper.Transport

/-!
# Continuity of `qProdSet A` on `[0,1]` and basic facts about `Q`

Generalises the argument of `Endpoint.lean` from `H = ∏_{n≥2}(1 - xⁿ)` to an
arbitrary exponent set `A`: writing `qProdSet A x = ∏'_{n ∈ ℕ} (1 - 1_A(n) xⁿ)`,
the truncations `P_N(x) = ∏_{n<N}(1 - 1_A(n) xⁿ)` satisfy
`P_N (1 - x^N/(1-x)) ≤ qProdSet A x ≤ P_N` on `[0,1)`, hence converge uniformly
on every `[0,r]`, `r < 1`; at `x = 1` we squeeze `0 ≤ qProdSet A x ≤ 1 - x^m`
(`m ∈ A`).  Specialising to `A = 𝒫` gives the facts about `Q` used for the
prime single-crossing lemma.
-/

namespace RntPaper

open QProduct MeasureTheory Set Filter Topology

/-- The `ℕ`-indexed factor `1 - 1_A(n) xⁿ`. -/
noncomputable def indFactor (A : Set ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  1 - Set.indicator A (fun n : ℕ => x ^ n) n

/-- Truncation `P_N(x) = ∏_{n<N}(1 - 1_A(n) xⁿ)`. -/
noncomputable def partialSet (A : Set ℕ) (N : ℕ) (x : ℝ) : ℝ :=
  ∏ n ∈ Finset.range N, indFactor A x n

theorem mulIndicator_eq_indFactor (A : Set ℕ) (x : ℝ) :
    Set.mulIndicator A (fun n : ℕ => 1 - x ^ n) = indFactor A x := by
  funext n
  unfold indFactor
  by_cases hn : n ∈ A <;> simp [hn]

theorem qProdSet_eq_tprod_indFactor (A : Set ℕ) (x : ℝ) :
    qProdSet A x = ∏' n : ℕ, indFactor A x n := by
  rw [qProdSet_eq_tprod_mulIndicator, mulIndicator_eq_indFactor]

theorem indicator_pow_nonneg (A : Set ℕ) {x : ℝ} (h0 : 0 ≤ x) (n : ℕ) :
    0 ≤ Set.indicator A (fun n : ℕ => x ^ n) n :=
  Set.indicator_nonneg (fun _ _ => pow_nonneg h0 _) n

theorem indicator_pow_le (A : Set ℕ) {x : ℝ} (h0 : 0 ≤ x) (n : ℕ) :
    Set.indicator A (fun n : ℕ => x ^ n) n ≤ x ^ n := by
  by_cases hn : n ∈ A <;> simp [hn, pow_nonneg h0]

theorem indFactor_nonneg (A : Set ℕ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (n : ℕ) :
    0 ≤ indFactor A x n := by
  unfold indFactor
  linarith [indicator_pow_le A hx.1 n, pow_le_one₀ (n := n) hx.1 hx.2]

theorem indFactor_le_one (A : Set ℕ) {x : ℝ} (h0 : 0 ≤ x) (n : ℕ) :
    indFactor A x n ≤ 1 := by
  unfold indFactor
  linarith [indicator_pow_nonneg A h0 n]

theorem continuous_partialSet (A : Set ℕ) (N : ℕ) : Continuous (partialSet A N) := by
  unfold partialSet indFactor
  refine continuous_finsetProd _ fun n _ => ?_
  by_cases hn : n ∈ A
  · simp only [Set.indicator_of_mem hn]; fun_prop
  · simp only [Set.indicator_of_notMem hn]; fun_prop

theorem tendsto_partialSet {A : Set ℕ} {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    Tendsto (fun N => partialSet A N x) atTop (𝓝 (qProdSet A x)) := by
  have hm := multipliable_mulIndicator A hx.1 hx.2
  rw [mulIndicator_eq_indFactor] at hm
  rw [qProdSet_eq_tprod_indFactor]
  exact hm.hasProd.tendsto_prod_nat

theorem partialSet_nonneg (A : Set ℕ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (s : Finset ℕ) :
    0 ≤ ∏ n ∈ s, indFactor A x n :=
  Finset.prod_nonneg fun n _ => indFactor_nonneg A hx n

theorem partialSet_le_one (A : Set ℕ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (s : Finset ℕ) :
    ∏ n ∈ s, indFactor A x n ≤ 1 :=
  Finset.prod_le_one₀ (fun n _ => indFactor_nonneg A hx n)
    (fun n _ => indFactor_le_one A hx.1 n)

/-- `qProdSet A ≤ P_N` on `[0,1)`. -/
theorem qProdSet_le_partialSet (A : Set ℕ) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (N : ℕ) :
    qProdSet A x ≤ partialSet A N x := by
  have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx.2.le⟩
  apply le_of_tendsto (tendsto_partialSet hx)
  filter_upwards [eventually_ge_atTop N] with M hM
  unfold partialSet
  rw [← Finset.prod_range_mul_prod_Ico _ hM]
  exact mul_le_of_le_one_right (partialSet_nonneg A hx' _) (partialSet_le_one A hx' _)

/-- Weierstrass bound `P_N (1 - x^N/(1-x)) ≤ qProdSet A` on `[0,1)`. -/
theorem partialSet_mul_le_qProdSet (A : Set ℕ) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (N : ℕ) :
    partialSet A N x * (1 - x ^ N / (1 - x)) ≤ qProdSet A x := by
  have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx.2.le⟩
  apply ge_of_tendsto (tendsto_partialSet hx)
  filter_upwards [eventually_ge_atTop N] with M hM
  unfold partialSet
  rw [← Finset.prod_range_mul_prod_Ico _ hM]
  apply mul_le_mul_of_nonneg_left _ (partialSet_nonneg A hx' _)
  have h1 := one_sub_prod_one_sub_le_sum (Finset.Ico N M)
    (fun n => Set.indicator A (fun n : ℕ => x ^ n) n)
    (fun n _ => indicator_pow_nonneg A hx.1 n)
    (fun n _ => (indicator_pow_le A hx.1 n).trans (pow_le_one₀ hx.1 hx.2.le))
  have h2 : ∑ n ∈ Finset.Ico N M, Set.indicator A (fun n : ℕ => x ^ n) n
      ≤ ∑ n ∈ Finset.Ico N M, x ^ n :=
    Finset.sum_le_sum fun n _ => indicator_pow_le A hx.1 n
  have h3 : ∑ n ∈ Finset.Ico N M, x ^ n ≤ x ^ N / (1 - x) :=
    geom_sum_Ico_le_of_lt_one hx.1 hx.2
  unfold indFactor
  linarith

/-- Uniform convergence of the truncations on `[0,r]`, `r < 1`. -/
theorem tendstoUniformlyOn_partialSet (A : Set ℕ) {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    TendstoUniformlyOn (fun N x => partialSet A N x) (qProdSet A) atTop (Icc 0 r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ => r ^ N / (1 - r)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2).div_const (1 - r)
    simpa using this
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with N hN x hx
  have hx1 : x ∈ Ico (0:ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩
  have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx1.2.le⟩
  have hupper := qProdSet_le_partialSet A hx1 N
  have hlower := partialSet_mul_le_qProdSet A hx1 N
  have hP0 : 0 ≤ partialSet A N x := partialSet_nonneg A hx' (Finset.range N)
  have hP1 : partialSet A N x ≤ 1 := partialSet_le_one A hx' (Finset.range N)
  have hq : x ^ N / (1 - x) ≤ r ^ N / (1 - r) := by
    apply div_le_div₀ (pow_nonneg hr.1 _) (pow_le_pow_left₀ hx.1 hx.2 _)
      (by linarith [hr.2]) (by linarith [hx.2])
  have hq0 : 0 ≤ x ^ N / (1 - x) := div_nonneg (pow_nonneg hx.1 _) (by linarith [hx1.2])
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · linarith
  · nlinarith

theorem qProdSet_continuousOn_Icc_lt (A : Set ℕ) {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    ContinuousOn (qProdSet A) (Icc 0 r) :=
  (tendstoUniformlyOn_partialSet A hr).continuousOn
    (Frequently.of_forall fun N => (continuous_partialSet A N).continuousOn)

/-- A nonempty exponent set kills the product at `u = 1` (a factor `1 - 1ⁿ = 0`). -/
theorem qProdSet_one_of_nonempty {A : Set ℕ} (hA : A.Nonempty) : qProdSet A 1 = 0 := by
  obtain ⟨m, hm⟩ := hA
  unfold qProdSet
  exact tprod_of_exists_eq_zero ⟨⟨m, hm⟩, by simp⟩

theorem qProdSet_empty (u : ℝ) : qProdSet ∅ u = 1 := by
  unfold qProdSet
  simp

/-- `qProdSet A x ≤ 1 - x^m` on `[0,1]` for `m ∈ A`. -/
theorem qProdSet_le_one_sub_pow {A : Set ℕ} {m : ℕ} (hm : m ∈ A) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) : qProdSet A x ≤ 1 - x ^ m := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, qProdSet_one_of_nonempty ⟨m, hm⟩]; simp
  · rw [← qProdSet_singleton]
    exact qProdSet_antitone (Set.singleton_subset_iff.mpr hm) hx.1 h

/-- **Continuity of `∏_{n∈A}(1 - xⁿ)` on `[0,1]`**: locally uniform convergence of
the truncations on `[0,1)` and the squeeze `0 ≤ qProdSet A x ≤ 1 - x^m` at `1`. -/
theorem qProdSet_continuousOn_Icc {A : Set ℕ} (hA : ∀ n ∈ A, 1 ≤ n) :
    ContinuousOn (qProdSet A) (Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst h1
    rcases A.eq_empty_or_nonempty with hE | ⟨m, hm⟩
    · subst hE
      have : qProdSet (∅ : Set ℕ) = fun _ => 1 := funext qProdSet_empty
      rw [this]; exact continuousWithinAt_const
    rw [ContinuousWithinAt, qProdSet_one_of_nonempty ⟨m, hm⟩]
    have hg : Tendsto (fun y : ℝ => 1 - y ^ m) (𝓝[Icc (0:ℝ) 1] 1) (𝓝 0) := by
      have : Tendsto (fun y : ℝ => 1 - y ^ m) (𝓝 1) (𝓝 (1 - 1 ^ m)) :=
        (by fun_prop : Continuous fun y : ℝ => 1 - y ^ m).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · exact eventually_nhdsWithin_of_forall fun y hy => qProdSet_nonneg A hy
    · exact eventually_nhdsWithin_of_forall fun y hy => qProdSet_le_one_sub_pow hm hy
  · set r := (x + 1) / 2 with hr
    have hr' : r ∈ Ico (0:ℝ) 1 := ⟨by rw [hr]; linarith [hx.1], by rw [hr]; linarith⟩
    have hxr : x < r := by rw [hr]; linarith
    have hcont := qProdSet_continuousOn_Icc_lt A hr' x ⟨hx.1, hxr.le⟩
    apply hcont.mono_of_mem_nhdsWithin
    have : Icc (0:ℝ) 1 ∩ Iio r ∈ 𝓝[Icc (0:ℝ) 1] x :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds hxr)
    apply Filter.mem_of_superset this
    rintro y ⟨hy1, hy2⟩
    exact ⟨hy1.1, le_of_lt hy2⟩

/-! ## The prime product `Q` -/

theorem Qfun_continuousOn : ContinuousOn Qfun (Icc 0 1) :=
  qProdSet_continuousOn_Icc fun _ hp => (Nat.Prime.two_le hp).trans' (by norm_num)

theorem Qfun_zero : Qfun 0 = 1 := by
  unfold Qfun qProdSet
  have : ∀ n : Primes, (1 : ℝ) - (0 : ℝ) ^ (n : ℕ) = 1 := fun n => by
    rw [zero_pow (Nat.Prime.ne_zero n.2)]; ring
  simp only [this, tprod_one]

theorem Qfun_one : Qfun 1 = 0 :=
  qProdSet_one_of_nonempty ⟨2, Nat.prime_two⟩

theorem Qfun_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : 0 < Qfun x :=
  qProdSet_pos_of_one_le Primes (fun _ hp => (Nat.Prime.two_le hp).trans' (by norm_num)) h0 h1

theorem Qfun_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ Qfun x :=
  qProdSet_nonneg Primes hx

/-- Q = (1 - x²)·∏_{p odd}(1 - xᵖ) on [0,1). -/
theorem Qfun_eq_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Qfun x = (1 - x ^ 2) * qProdSet (Primes \ {2}) x := by
  have hP : qProdSet Primes x = qProdSet (insert 2 (Primes \ {2})) x := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem (show (2:ℕ) ∈ Primes from Nat.prime_two)]
  unfold Qfun
  rw [hP, qProdSet_insert (by simp) h0 h1]

end RntPaper
