import RntPaper.MomentsOdd
import RntPaper.Moments1339Cert

/-!
# Moments up to `3 + 6√3`: envelopes at the primes `5` and `3`

For every real `0 < k < 3 + 6√3 = 13.39…` and `c ∈ (0,1]` the primes uniquely minimize
`𝓜ₖ,c(A) = 𝔼 min(Z_A^k, c^k)` over primitive sets, finite (`moment_primesLE_lt_1339`) and
arbitrary (`moment_primes_lt_1339`). (Notes, Theorem 3.7.)

For `k ≤ 51/8` this is `MomentsOdd`. For `51/8 < k < 3 + 6√3` the compressions are ordered:

1. at a prime `p ≥ 7` dividing a composite (`k ≤ p`, or `k/p ≤ 17/8` and `J_{17/8}(1) > 0`);
2. at `5`, once every composite is `5`-smooth: the quotient block `T` is a primitive set of
   `5`-smooth numbers, and `P_T` is bounded below by an envelope depending on `T ∩ {2,3,5}`
   (Lemma 3.6); the envelopes are certified at `s = k/5 ≤ 75/28` (`R5_pos`);
3. at `3`, once every composite is `3`-smooth: `T` consists of `3`-smooth numbers; if
   `2 ∈ T` or `3 ∈ T` then `P_T ≥ (1-v²)(1-v³)`, whose endpoint moment is
   `(11 + 2s - s²)/((s+1)(s+2)(s+3)(s+5)) > 0` exactly for `s < 1 + 2√3` (`runPos_23`);
   otherwise `P_T ≥ H₂₃` (`R3_pos`);
4. at `2`, with a single even element (`MSet_compressAtSet_two_lt`).

The infinite envelopes are replaced by `∏_{m ∈ M}(1 - vᵐ) ∏_{n ≥ 61}(1 - vⁿ)` with `M` the
envelope exponents below `61`: the block `T` is contained in `M ∪ [61, ∞)`.
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set Filter Topology

/-! ## Envelopes and running integrals -/

/-- `∏_{n ≥ B}(1 - xⁿ) ≥ 1 - x^B/(1 - x)` on `[0,1)`. -/
theorem qProdSet_tail_ge (B : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    1 - x ^ B / (1 - x) ≤ qProdSet {n | B ≤ n} x := by
  classical
  refine ge_of_tendsto (qProdSet_eq_lim _ h0 h1) (Eventually.of_forall fun N => ?_)
  set F := (Finset.range (N + 1)).filter (· ∈ {n : ℕ | B ≤ n})
  have hW := one_sub_prod_one_sub_le_sum F (fun n => x ^ n) (fun _ _ => pow_nonneg h0 _)
    (fun _ _ => pow_le_one₀ h0 h1.le)
  have hsub : F ⊆ Finset.Ico B (N + 1) := by
    intro n hn
    simp only [F, Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    exact Finset.mem_Ico.mpr ⟨hn.2, hn.1⟩
  have hS : ∑ n ∈ F, x ^ n ≤ x ^ B / (1 - x) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg h0 _).trans
      (geom_sum_Ico_le_of_lt_one h0 h1)
  unfold qProd
  linarith

/-- The envelope `∏_{m ∈ M}(1 - xᵐ) ∏_{n ≥ 61}(1 - xⁿ)` is at least the V1 lower bound. -/
theorem qProdSet_list_tail_ge {M : List ℕ} (hnd : M.Nodup) (hM : ∀ m ∈ M, m < 61) {x : ℝ}
    (h0 : 0 ≤ x) (h1 : x < 1) :
    (M.map fun m => 1 - x ^ m).prod * (1 - x ^ 61 / (1 - x))
      ≤ qProdSet ((M.toFinset : Set ℕ) ∪ {n | 61 ≤ n}) x := by
  have hdisj : Disjoint (M.toFinset : Set ℕ) {n | 61 ≤ n} := by
    rw [Set.disjoint_left]
    intro n hn h
    simp only [Finset.mem_coe, List.mem_toFinset] at hn
    have := hM n hn
    simp only [Set.mem_ofPred_eq] at h
    omega
  rw [qProdSet_union hdisj h0 h1, qProdSet_coe]
  have hq : qProd M.toFinset x = (M.map fun m => 1 - x ^ m).prod := by
    unfold qProd
    exact List.prod_toFinset _ hnd
  have hnn := qProdSet_nonneg (M.toFinset : Set ℕ) ⟨h0, h1.le⟩
  rw [qProdSet_coe, hq] at hnn
  rw [hq]
  exact mul_le_mul_of_nonneg_left (qProdSet_tail_ge 61 h0 h1) hnn

/-- **V1 envelopes.** From the exact check, the running integrals of
`v^{s-1}(E(v) - (1 - v))` are positive for `E = ∏_{m ∈ M}(1 - vᵐ) ∏_{n ≥ 61}(1 - vⁿ)`. -/
theorem runPos_v1 {M : List ℕ} {K : ℕ} (hK : 1 ≤ K) {u1 u0 : ℚ}
    (h : CP.v1Check 12 [1] M 61 [1] 1 K u1 u0 = true) (hnd : M.Nodup)
    (hM : ∀ m ∈ M, 1 ≤ m ∧ m < 61) :
    RunPos (fun v => qProdSet ((M.toFinset : Set ℕ) ∪ {n | 61 ≤ n}) (clampI v) - (1 - v)) K := by
  set S : Set ℕ := (M.toFinset : Set ℕ) ∪ {n | 61 ≤ n} with hSdef
  have hS1 : ∀ n ∈ S, 1 ≤ n := by
    rintro n (hn | hn)
    · simp only [Finset.mem_coe, List.mem_toFinset] at hn; exact (hM n hn).1
    · simp only [Set.mem_ofPred_eq] at hn; omega
  have hEc : Continuous fun v => qProdSet S (clampI v) :=
    (qProdSet_continuousOn_Icc hS1).comp_continuous continuous_clampI clampI_mem
  have key := CP.v1Check_sound (W := [1]) (p := 1) le_rfl hK
    (fun u _ => by simp) (fun u _ => by simp) h hEc
    (fun u _ => qProdSet_nonneg S (clampI_mem u))
    (fun u hu => by
      simp only [pow_one]
      rw [clampI_of_mem ⟨hu.1, hu.2.le⟩]
      exact qProdSet_list_tail_ge hnd (fun m hm => (hM m hm).2) hu.1 hu.2)
  convert key using 1
  funext u
  simp

/-- **SC envelopes.** From the exact check, the running integrals of
`v^{s-1}(∏_{n ∈ l}(1 - vⁿ) - (1 - v))` are positive for `1 ≤ s ≤ K`. -/
theorem runPos_sc {l : List ℕ} {K : ℚ} (hK : 0 < K)
    (h : CP.scCheck 40 (M1339.envD l) (CP.mul [1] (CP.compPow 1 (M1339.envD l))) K = true) :
    RunPos (fun v => (l.map fun n => 1 - v ^ n).prod - (1 - v)) K := by
  have key := CP.scCheck_sound (W := [1]) (p := 1) le_rfl hK (fun u _ => by simp)
    (fun u _ => by simp) h
  convert key using 1
  funext u
  simp [M1339.envD]
  ring

/-- An envelope `G ≤ P_T` with positive running integrals of `v^{s-1}(G - (1 - v))` gives
positive running integrals of `v^{s-1} E_T(v)`. -/
theorem R_pos_of_env {T : Set ℕ} (hT1 : ∀ t ∈ T, 1 ≤ t) {G : ℝ → ℝ} (hG : Continuous G)
    (hGle : ∀ v ∈ Ico (0 : ℝ) 1, G v ≤ qProdSet T v) {K : ℝ}
    (hrun : RunPos (fun v => G v - (1 - v)) K) {s : ℝ} (hs1 : 1 ≤ s) (hsK : s ≤ K)
    {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) : 0 < ∫ v in (0 : ℝ)..z, v ^ (s - 1) * ESetExt T v := by
  refine lt_of_lt_of_le (hrun s hs1 hsK z hz) ?_
  apply intervalIntegral.integral_mono_ae_restrict hz.1.le
  · exact (continuous_rpow_mul (hG.sub (continuous_const.sub continuous_id)) hs1).intervalIntegrable _ _
  · exact (continuous_rpow_mul (continuous_ESetExt hT1) hs1).intervalIntegrable _ _
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with v hv hv1
    have hv' : v < 1 := lt_of_le_of_ne (hv.2.trans hz.2) hv1
    show v ^ (s - 1) * (G v - (1 - v)) ≤ v ^ (s - 1) * ESetExt T v
    rw [ESetExt_of_mem T ⟨hv.1, hv'.le⟩]
    unfold blockESet
    exact mul_le_mul_of_nonneg_left (by linarith [hGle v ⟨hv.1, hv'⟩])
      (Real.rpow_nonneg hv.1 _)

/-- Polynomial envelopes certified by SC. -/
theorem R_pos_of_sc {T : Set ℕ} (hT1 : ∀ t ∈ T, 1 ≤ t) {l : List ℕ}
    (hle : ∀ v ∈ Ico (0 : ℝ) 1, (l.map fun n => 1 - v ^ n).prod ≤ qProdSet T v) {K : ℚ}
    (hK : 0 < K)
    (h : CP.scCheck 40 (M1339.envD l) (CP.mul [1] (CP.compPow 1 (M1339.envD l))) K = true)
    {s : ℝ} (hs1 : 1 ≤ s) (hsK : s ≤ K) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..z, v ^ (s - 1) * ESetExt T v := by
  have hc : Continuous fun v : ℝ => (l.map fun n => 1 - v ^ n).prod := by
    have : (fun v : ℝ => (l.map fun n => 1 - v ^ n).prod) = CP.ev (CP.prodOneSub l) := by
      funext v; simp
    rw [this]; exact CP.continuous_ev _
  exact R_pos_of_env hT1 hc hle (runPos_sc hK h) hs1 hsK hz

/-- Infinite envelopes certified by V1: it suffices that every element of `T` below `61`
lies in `M`. -/
theorem R_pos_of_v1 {T : Set ℕ} (hT1 : ∀ t ∈ T, 1 ≤ t) {M : List ℕ}
    (hTM : ∀ t ∈ T, t < 61 → t ∈ M) (hnd : M.Nodup) (hM : ∀ m ∈ M, 1 ≤ m ∧ m < 61) {K : ℕ}
    (hK : 1 ≤ K) {u1 u0 : ℚ} (h : CP.v1Check 12 [1] M 61 [1] 1 K u1 u0 = true) {s : ℝ}
    (hs1 : 1 ≤ s) (hsK : s ≤ K) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..z, v ^ (s - 1) * ESetExt T v := by
  set S : Set ℕ := (M.toFinset : Set ℕ) ∪ {n | 61 ≤ n} with hSdef
  have hS1 : ∀ n ∈ S, 1 ≤ n := by
    rintro n (hn | hn)
    · simp only [Finset.mem_coe, List.mem_toFinset] at hn; exact (hM n hn).1
    · simp only [Set.mem_ofPred_eq] at hn; omega
  have hEc : Continuous fun v => qProdSet S (clampI v) :=
    (qProdSet_continuousOn_Icc hS1).comp_continuous continuous_clampI clampI_mem
  have hsub : T ⊆ S := by
    intro t ht
    by_cases h61 : t < 61
    · left; simp only [Finset.mem_coe, List.mem_toFinset]; exact hTM t ht h61
    · right; simp only [Set.mem_ofPred_eq]; omega
  refine R_pos_of_env hT1 hEc (fun v hv => ?_) (runPos_v1 hK h hnd hM) hs1 hsK hz
  rw [clampI_of_mem ⟨hv.1, hv.2.le⟩]
  exact qProdSet_antitone hsub hv.1 hv.2

/-- **Substitution `v = uᵖ`.** Positive running integrals of `v^{k/p-1} E_T(v)` give positive
running integrals of `u^{k-1} E_T(uᵖ)`, for `k ≥ p`. -/
theorem run_pos_of_R {T : Set ℕ} (hT1 : ∀ t ∈ T, 1 ≤ t) {p : ℕ} (hp : 1 ≤ p) {k : ℝ}
    (hpk : (p : ℝ) ≤ k)
    (hR : ∀ z ∈ Ioc (0 : ℝ) 1, 0 < ∫ v in (0 : ℝ)..z, v ^ (k / p - 1) * ESetExt T v)
    {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * ESetExt T (u ^ p) := by
  rw [integral_rpow_mul_comp_pow (continuousOn_ESetExt_Icc hT1) hp hpk ⟨hy.1.le, hy.2⟩]
  have hz : y ^ p ∈ Ioc (0 : ℝ) 1 := ⟨pow_pos hy.1 p, pow_le_one₀ hy.1.le hy.2⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  exact mul_pos (by positivity) (hR _ hz)

/-! ## The envelope `(1 - v²)(1 - v³)` at every real `s < 1 + 2√3` -/

theorem integral_rpow_mul_pow_unit {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    ∫ v in (0 : ℝ)..1, v ^ (s - 1) * v ^ n = 1 / (s + n) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcongr : (∫ v in (0 : ℝ)..1, v ^ (s - 1) * v ^ n) = ∫ v in (0 : ℝ)..1, v ^ (s - 1 + n) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with v hv
    rw [uIoc_of_le zero_le_one] at hv
    rw [Real.rpow_add hv.1, Real.rpow_natCast]
  rw [hcongr, integral_rpow (Or.inl (by linarith))]
  have : s - 1 + n + 1 = s + n := by ring
  rw [this, Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

/-- **The bottleneck envelope.** For every real `1 ≤ s < 1 + 2√3` the running integrals of
`v^{s-1}((1-v²)(1-v³) - (1-v))` are positive: one sign change, and the endpoint value is
`(11 + 2s - s²)/((s+1)(s+2)(s+3)(s+5))`. -/
theorem runPos_23 {s : ℝ} (hs1 : 1 ≤ s) (hs : s < 1 + 2 * Real.sqrt 3) :
    RunPos (fun v => (1 - v ^ 2) * (1 - v ^ 3) - (1 - v)) s := by
  set h : ℝ → ℝ := fun v => 1 - v ^ 2 - v ^ 3 with hhdef
  have hc : ContinuousOn h (Icc 0 1) := by
    simp only [hhdef]; exact (by fun_prop : Continuous fun v : ℝ => 1 - v ^ 2 - v ^ 3).continuousOn
  have hmem : (0 : ℝ) ∈ Icc (h 1) (h 0) := ⟨by norm_num [hhdef], by norm_num [hhdef]⟩
  obtain ⟨x0, hx0, hx0z⟩ := intermediate_value_Icc' zero_le_one hc hmem
  simp only [hhdef] at hx0z
  have hx00 : x0 ≠ 0 := by rintro rfl; norm_num at hx0z
  have hx01 : x0 ≠ 1 := by rintro rfl; norm_num at hx0z
  have hx0I : x0 ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx0.1 (Ne.symm hx00), lt_of_le_of_ne hx0.2 hx01⟩
  have hfac : ∀ u : ℝ, (1 - u ^ 2) * (1 - u ^ 3) - (1 - u) = u * (1 - u) * (1 - u ^ 2 - u ^ 3) :=
    fun u => by ring
  refine runPos_of_signChange (by fun_prop) hx0I (fun u hu => ?_) (fun u hu => ?_) ?_
  · have hu1 : u < 1 := hu.2.trans hx0I.2
    show 0 < (1 - u ^ 2) * (1 - u ^ 3) - (1 - u)
    rw [hfac]
    have h2 : u ^ 2 < x0 ^ 2 := pow_lt_pow_left₀ hu.2 hu.1.le (by norm_num)
    have h3 : u ^ 3 < x0 ^ 3 := pow_lt_pow_left₀ hu.2 hu.1.le (by norm_num)
    have : 0 < 1 - u ^ 2 - u ^ 3 := by linarith
    have : 0 < u * (1 - u) := mul_pos hu.1 (by linarith)
    positivity
  · have hu0 : 0 ≤ u := hx0.1.trans hu.1
    show (1 - u ^ 2) * (1 - u ^ 3) - (1 - u) ≤ 0
    rw [hfac]
    have h2 : x0 ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hx0.1 hu.1 2
    have h3 : x0 ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hx0.1 hu.1 3
    have : 1 - u ^ 2 - u ^ 3 ≤ 0 := by linarith
    have : 0 ≤ u * (1 - u) := mul_nonneg hu0 (by linarith [hu.2])
    exact mul_nonpos_of_nonneg_of_nonpos this (by linarith)
  · have e : ∀ u : ℝ, u ^ (s - 1) * ((1 - u ^ 2) * (1 - u ^ 3) - (1 - u))
        = ((u ^ (s - 1) * u ^ 1 - u ^ (s - 1) * u ^ 2) - u ^ (s - 1) * u ^ 3)
          + u ^ (s - 1) * u ^ 5 := fun u => by ring
    have hi : ∀ n : ℕ, IntervalIntegrable (fun u : ℝ => u ^ (s - 1) * u ^ n) volume 0 1 :=
      fun n => (continuous_rpow_mul (continuous_pow n) hs1).intervalIntegrable 0 1
    have hI : (∫ u in (0 : ℝ)..1, u ^ (s - 1) * ((1 - u ^ 2) * (1 - u ^ 3) - (1 - u)))
        = 1 / (s + 1) - 1 / (s + 2) - 1 / (s + 3) + 1 / (s + 5) := by
      rw [intervalIntegral.integral_congr (fun u _ => e u),
        intervalIntegral.integral_add (((hi 1).sub (hi 2)).sub (hi 3)) (hi 5),
        intervalIntegral.integral_sub ((hi 1).sub (hi 2)) (hi 3),
        intervalIntegral.integral_sub (hi 1) (hi 2)]
      simp only [integral_rpow_mul_pow_unit hs1]
      push_cast
      ring
    show 0 < ∫ u in (0 : ℝ)..1, u ^ (s - 1) * ((1 - u ^ 2) * (1 - u ^ 3) - (1 - u))
    rw [hI]
    have hq : 1 / (s + 1) - 1 / (s + 2) - 1 / (s + 3) + 1 / (s + 5)
        = (11 + 2 * s - s ^ 2) / ((s + 1) * (s + 2) * (s + 3) * (s + 5)) := by
      field_simp
      ring
    rw [hq]
    have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have h3' := Real.sqrt_nonneg 3
    have hnum : 0 < 11 + 2 * s - s ^ 2 := by nlinarith
    positivity

/-! ## Smooth numbers and the envelope lemma -/

/-- `n` is `b`-smooth: every prime factor is `≤ b`. -/
def Smooth (b n : ℕ) : Prop := ∀ q, Nat.Prime q → q ∣ n → q ≤ b

theorem prime_le_five {q : ℕ} (hq : q.Prime) (h : q ≤ 5) : q = 2 ∨ q = 3 ∨ q = 5 := by
  have := hq.two_le
  interval_cases q <;> simp_all (config := { decide := true })

theorem eq_pow_of_only {q n : ℕ} (hn : n ≠ 0) (h : ∀ r, Nat.Prime r → r ∣ n → r = q) :
    ∃ j, n = q ^ j :=
  ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn (fun {d} hd hdn => h d hd hdn)⟩

/-- Two elements of a primitive set whose only prime factor is `q` coincide. -/
theorem eq_of_only {T : Set ℕ} (hT : IsPrimitive T) {q a b : ℕ} (ha : a ∈ T) (hb : b ∈ T)
    (hqa : ∀ r, Nat.Prime r → r ∣ a → r = q) (hqb : ∀ r, Nat.Prime r → r ∣ b → r = q) :
    a = b := by
  have ha0 : a ≠ 0 := by have := hT.1 a ha; omega
  have hb0 : b ≠ 0 := by have := hT.1 b hb; omega
  obtain ⟨i, hi⟩ := eq_pow_of_only ha0 hqa
  obtain ⟨j, hj⟩ := eq_pow_of_only hb0 hqb
  rcases le_total i j with h | h
  · exact hT.2 a ha b hb (by rw [hi, hj]; exact Nat.pow_dvd_pow q h)
  · exact (hT.2 b hb a ha (by rw [hi, hj]; exact Nat.pow_dvd_pow q h)).symm

theorem sq_le_of_only {q t : ℕ} (hq : q.Prime) (ht2 : 2 ≤ t) (htq : t ≠ q)
    (h : ∀ r, Nat.Prime r → r ∣ t → r = q) : q ^ 2 ≤ t := by
  obtain ⟨j, rfl⟩ := eq_pow_of_only (by omega) h
  rcases j with _ | _ | j
  · simp at ht2
  · simp at htq
  · exact Nat.pow_le_pow_right hq.pos (by omega)

/-- **One extra element.** If every element of `T` outside `F` has the single prime factor
`q` and is `≥ m`, then `P_T ≥ P_F · (1 - vᵐ)`. -/
theorem env_one_extra {T : Set ℕ} (hT : IsPrimitive T) (F : Finset ℕ) {q m : ℕ}
    (hext : ∀ t ∈ T, t ∉ F → (∀ r, Nat.Prime r → r ∣ t → r = q) ∧ m ≤ t)
    {v : ℝ} (hv : v ∈ Ico (0 : ℝ) 1) : qProd F v * (1 - v ^ m) ≤ qProdSet T v := by
  classical
  have hF0 : 0 ≤ qProd F v := by
    have := qProdSet_nonneg (F : Set ℕ) ⟨hv.1, hv.2.le⟩
    rwa [qProdSet_coe] at this
  have hm1 : v ^ m ≤ 1 := pow_le_one₀ hv.1 hv.2.le
  have hm0 : 0 ≤ v ^ m := pow_nonneg hv.1 m
  by_cases h : ∃ t ∈ T, t ∉ F
  · obtain ⟨t, htT, htF⟩ := h
    have hsub : T ⊆ ((insert t F : Finset ℕ) : Set ℕ) := by
      intro t' ht'
      by_cases ht'F : t' ∈ F
      · simp [ht'F]
      · have := eq_of_only hT ht' htT (hext t' ht' ht'F).1 (hext t htT htF).1
        simp [this]
    have h1 := qProd_le_qProdSet _ hsub hv.1 hv.2
    have hins : qProd (insert t F) v = (1 - v ^ t) * qProd F v := by
      unfold qProd
      exact Finset.prod_insert htF
    rw [hins] at h1
    have ht : v ^ t ≤ v ^ m := pow_le_pow_of_le_one hv.1 hv.2.le (hext t htT htF).2
    calc qProd F v * (1 - v ^ m) ≤ qProd F v * (1 - v ^ t) :=
          mul_le_mul_of_nonneg_left (by linarith) hF0
      _ = (1 - v ^ t) * qProd F v := by ring
      _ ≤ qProdSet T v := h1
  · push Not at h
    have hsub : T ⊆ (F : Set ℕ) := fun t ht => h t ht
    have h1 := qProd_le_qProdSet _ hsub hv.1 hv.2
    calc qProd F v * (1 - v ^ m) ≤ qProd F v := mul_le_of_le_one_right hF0 (by linarith)
      _ ≤ qProdSet T v := h1

/-- The finite envelopes at `5`: two of `2, 3, 5` lie in `T`, the third (`q`) does not. Then
every other element of `T` is a power of `q`, at least `q²`. -/
theorem hext_two_in {T : Set ℕ} (hT : IsPrimitive T) (hsm : ∀ t ∈ T, Smooth 5 t)
    {a b q : ℕ} (hprimes : ∀ r, Nat.Prime r → r ≤ 5 → r = a ∨ r = b ∨ r = q) (ha : a ∈ T)
    (hb : b ∈ T) (hqT : q ∉ T) (hq : q.Prime) :
    ∀ t ∈ T, t ∉ ({a, b} : Finset ℕ) → (∀ r, Nat.Prime r → r ∣ t → r = q) ∧ q ^ 2 ≤ t := by
  intro t ht htF
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htF
  have honly : ∀ r, Nat.Prime r → r ∣ t → r = q := by
    intro r hr hrt
    rcases hprimes r hr (hsm t ht r hr hrt) with rfl | rfl | rfl
    · exact absurd (hT.2 r ha t ht hrt).symm htF.1
    · exact absurd (hT.2 r hb t ht hrt).symm htF.2
    · rfl
  refine ⟨honly, sq_le_of_only hq (hT.1 t ht) (fun h => hqT (h ▸ ht)) honly⟩

/-- `5`-smooth numbers in `[2, 60]`. -/
def L235 : List ℕ :=
  [2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40, 45, 48, 50, 54, 60]

theorem nonsmooth_wit : ∀ t, t < 61 → 2 ≤ t → t ∉ L235 →
    ∃ q ∈ [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59], q ∣ t := by
  decide

theorem mem_L235 {t : ℕ} (h2 : 2 ≤ t) (h61 : t < 61) (hsm : Smooth 5 t) : t ∈ L235 := by
  by_contra hn
  obtain ⟨q, hq, hqt⟩ := nonsmooth_wit t h61 h2 hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact absurd (hsm _ (by norm_num) hqt) (by norm_num)

theorem M23_of : ∀ t ∈ L235, t % 5 ≠ 0 → t ≠ 2 → t ≠ 3 → t ∈ M1339.M23 := by decide
theorem M5two_of : ∀ t ∈ L235, (t = 2 ∨ t % 2 ≠ 0) → t ≠ 3 → t ≠ 5 → t ∈ M1339.M5two := by
  decide
theorem M5three_of : ∀ t ∈ L235, (t = 3 ∨ t % 3 ≠ 0) → t ≠ 2 → t ≠ 5 → t ∈ M1339.M5three := by
  decide
theorem M5five_of : ∀ t ∈ L235, (t = 5 ∨ t % 5 ≠ 0) → t ≠ 2 → t ≠ 3 → t ∈ M1339.M5five := by
  decide
theorem M5none_of : ∀ t ∈ L235, t ≠ 2 → t ≠ 3 → t ≠ 5 → t ∈ M1339.M5none := by decide

theorem M23_ok : M1339.M23.Nodup ∧ ∀ m ∈ M1339.M23, 1 ≤ m ∧ m < 61 := by decide
theorem M5two_ok : M1339.M5two.Nodup ∧ ∀ m ∈ M1339.M5two, 1 ≤ m ∧ m < 61 := by decide
theorem M5three_ok : M1339.M5three.Nodup ∧ ∀ m ∈ M1339.M5three, 1 ≤ m ∧ m < 61 := by decide
theorem M5five_ok : M1339.M5five.Nodup ∧ ∀ m ∈ M1339.M5five, 1 ≤ m ∧ m < 61 := by decide
theorem M5none_ok : M1339.M5none.Nodup ∧ ∀ m ∈ M1339.M5none, 1 ≤ m ∧ m < 61 := by decide

/-- In a primitive set, an element `t` with `r ∈ T`, `r ∣ t` equals `r`. -/
theorem eq_or_mod_ne {T : Set ℕ} (hT : IsPrimitive T) {r t : ℕ} (hr : r ∈ T) (ht : t ∈ T) :
    t = r ∨ t % r ≠ 0 := by
  by_cases hd : t % r = 0
  · exact Or.inl (hT.2 r hr t ht (Nat.dvd_of_mod_eq_zero hd)).symm
  · exact Or.inr hd

theorem ne_of_not_mem {T : Set ℕ} {r t : ℕ} (hr : r ∉ T) (ht : t ∈ T) : t ≠ r :=
  fun h => hr (h ▸ ht)

/-! ## The block conditions at `3` and `5` -/

/-- **Compression at `3`.** For a primitive set `T` of `3`-smooth numbers and every real
`1 ≤ s < 1 + 2√3`, the running integrals of `v^{s-1} E_T(v)` are positive. -/
theorem R3_pos {T : Set ℕ} (hT : IsPrimitive T) (hsm : ∀ t ∈ T, Smooth 3 t) {s : ℝ}
    (hs1 : 1 ≤ s) (hs : s < 1 + 2 * Real.sqrt 3) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..z, v ^ (s - 1) * ESetExt T v := by
  have hT1 : ∀ t ∈ T, 1 ≤ t := fun t ht => le_trans (by norm_num) (hT.1 t ht)
  have hsqrt : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  by_cases h23 : 2 ∈ T ∨ 3 ∈ T
  · refine R_pos_of_env hT1 (G := fun v => (1 - v ^ 2) * (1 - v ^ 3)) (by fun_prop) ?_
      (runPos_23 hs1 hs) hs1 le_rfl hz
    intro v hv
    rcases h23 with h2 | h3
    · have := env_one_extra hT {2} (q := 3) (m := 3) (fun t ht htF => by
        have ht2 : t ≠ 2 := by simpa using htF
        refine ⟨fun r hr hrt => ?_, ?_⟩
        · have hr3 := hsm t ht r hr hrt
          have hr2 : r ≠ 2 := by rintro rfl; exact ht2 (hT.2 2 h2 t ht hrt).symm
          have := hr.two_le; omega
        · have := hT.1 t ht; omega) hv
      simpa [qProd] using this
    · have := env_one_extra hT {3} (q := 2) (m := 2) (fun t ht htF => by
        have ht3 : t ≠ 3 := by simpa using htF
        refine ⟨fun r hr hrt => ?_, hT.1 t ht⟩
        have hr3 := hsm t ht r hr hrt
        have hr3' : r ≠ 3 := by rintro rfl; exact ht3 (hT.2 3 h3 t ht hrt).symm
        have := hr.two_le; omega) hv
      simp only [qProd, Finset.prod_singleton] at this
      linarith
  · push Not at h23
    obtain ⟨h2, h3⟩ := h23
    refine R_pos_of_v1 hT1 (M := M1339.M23) (fun t ht h61 => ?_) M23_ok.1 M23_ok.2
      (K := 5) (by norm_num) M1339.v1_23 hs1 (by push_cast; linarith) hz
    have hsm5 : Smooth 5 t := fun q hq hqt => (hsm t ht q hq hqt).trans (by norm_num)
    refine M23_of t (mem_L235 (hT.1 t ht) h61 hsm5) ?_ (ne_of_not_mem h2 ht) (ne_of_not_mem h3 ht)
    intro h5
    have := hsm t ht 5 Nat.prime_five (Nat.dvd_of_mod_eq_zero h5)
    omega

/-- **Compression at `5`.** For a primitive set `T` of `5`-smooth numbers and every real
`1 ≤ s ≤ 75/28`, the running integrals of `v^{s-1} E_T(v)` are positive. -/
theorem R5_pos {T : Set ℕ} (hT : IsPrimitive T) (hsm : ∀ t ∈ T, Smooth 5 t) {s : ℝ}
    (hs1 : 1 ≤ s) (hs : s ≤ 75 / 28) {z : ℝ} (hz : z ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..z, v ^ (s - 1) * ESetExt T v := by
  have hT1 : ∀ t ∈ T, 1 ≤ t := fun t ht => le_trans (by norm_num) (hT.1 t ht)
  have hs3 : s ≤ ((3 : ℚ) : ℝ) := by push_cast; linarith
  have hs3' : s ≤ ((3 : ℕ) : ℝ) := by push_cast; linarith
  have hP := fun r hr h => prime_le_five (q := r) hr h
  have hL : ∀ t ∈ T, t < 61 → t ∈ L235 := fun t ht h61 => mem_L235 (hT.1 t ht) h61 (hsm t ht)
  by_cases h2 : 2 ∈ T <;> by_cases h3 : 3 ∈ T <;> by_cases h5 : 5 ∈ T
  · -- `R₀ = {2,3,5}`: `T = {2,3,5}`
    refine R_pos_of_sc hT1 (l := [2, 3, 5]) (fun v hv => ?_) (by norm_num) M1339.sc235 hs1
      (by push_cast; linarith) hz
    have hsub : T ⊆ (({2, 3, 5} : Finset ℕ) : Set ℕ) := by
      intro t ht
      obtain ⟨r, hr, hrt⟩ := Nat.exists_prime_and_dvd (by have := hT.1 t ht; omega : t ≠ 1)
      have hrT : r ∈ T := by
        rcases hP r hr (hsm t ht r hr hrt) with rfl | rfl | rfl <;> assumption
      have := hT.2 r hrT t ht hrt
      subst this
      rcases hP r hr (hsm r ht r hr dvd_rfl) with rfl | rfl | rfl <;> simp
    have := qProd_le_qProdSet _ hsub hv.1 hv.2
    simp [qProd] at this
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    linarith
  · -- `R₀ = {2,3}`
    refine R_pos_of_sc hT1 (l := [2, 3, 25]) (fun v hv => ?_) (by norm_num) M1339.sc23 hs1 hs3 hz
    have := env_one_extra hT {2, 3} (hext_two_in hT hsm (a := 2) (b := 3) (q := 5)
      (fun r hr h => by rcases hP r hr h with h | h | h <;> simp [h]) h2 h3 h5 Nat.prime_five) hv
    simp [qProd] at this
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    nlinarith
  · -- `R₀ = {2,5}`
    refine R_pos_of_sc hT1 (l := [2, 5, 9]) (fun v hv => ?_) (by norm_num) M1339.sc25 hs1 hs3 hz
    have := env_one_extra hT {2, 5} (hext_two_in hT hsm (a := 2) (b := 5) (q := 3)
      (fun r hr h => by rcases hP r hr h with h | h | h <;> simp [h]) h2 h5 h3 Nat.prime_three) hv
    simp [qProd] at this
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    nlinarith
  · -- `R₀ = {2}`
    refine R_pos_of_v1 hT1 (M := M1339.M5two) (fun t ht h61 => M5two_of t (hL t ht h61)
      (eq_or_mod_ne hT h2 ht) (ne_of_not_mem h3 ht) (ne_of_not_mem h5 ht)) M5two_ok.1 M5two_ok.2
      (K := 3) (by norm_num) M1339.v1_5two hs1 hs3' hz
  · -- `R₀ = {3,5}`
    refine R_pos_of_sc hT1 (l := [3, 4, 5]) (fun v hv => ?_) (by norm_num) M1339.sc35 hs1 hs3 hz
    have := env_one_extra hT {3, 5} (hext_two_in hT hsm (a := 3) (b := 5) (q := 2)
      (fun r hr h => by rcases hP r hr h with h | h | h <;> simp [h]) h3 h5 h2 Nat.prime_two) hv
    simp [qProd] at this
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    nlinarith
  · -- `R₀ = {3}`
    refine R_pos_of_v1 hT1 (M := M1339.M5three) (fun t ht h61 => M5three_of t (hL t ht h61)
      (eq_or_mod_ne hT h3 ht) (ne_of_not_mem h2 ht) (ne_of_not_mem h5 ht)) M5three_ok.1
      M5three_ok.2 (K := 3) (by norm_num) M1339.v1_5three hs1 hs3' hz
  · -- `R₀ = {5}`
    refine R_pos_of_v1 hT1 (M := M1339.M5five) (fun t ht h61 => M5five_of t (hL t ht h61)
      (eq_or_mod_ne hT h5 ht) (ne_of_not_mem h2 ht) (ne_of_not_mem h3 ht)) M5five_ok.1
      M5five_ok.2 (K := 3) (by norm_num) M1339.v1_5five hs1 hs3' hz
  · -- `R₀ = ∅`
    refine R_pos_of_v1 hT1 (M := M1339.M5none) (fun t ht h61 => M5none_of t (hL t ht h61)
      (ne_of_not_mem h2 ht) (ne_of_not_mem h3 ht) (ne_of_not_mem h5 ht)) M5none_ok.1
      M5none_ok.2 (K := 3) (by norm_num) M1339.v1_5none hs1 hs3' hz

/-! ## Bounds on `3 + 6√3` -/

theorem bound_1339 : 3 + 6 * Real.sqrt 3 < 375 / 28 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3' := Real.sqrt_nonneg 3
  nlinarith

/-! ## The compression steps -/

/-- A compression at `p` is strict once the running integrals for its quotient block are
positive. -/
theorem MSet_compress_of_run {k : ℝ} (hk : 1 ≤ k) {A : Set ℕ} {p : ℕ} (hp : p.Prime)
    (hA : IsPrimitive A) (hpA : p ∉ A)
    (hrun : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < ∫ u in (0 : ℝ)..y,
      u ^ (k - 1) * ESetExt ((fun a => a / p) '' {a ∈ A | p ∣ a}) (u ^ p))
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c (compressAtSet p A) < MSet k c A := by
  have hB : ∀ b ∈ {a ∈ A | ¬ p ∣ a}, 2 ≤ b := fun b hb => hA.1 b hb.1
  have hTp := quotients_set_isPrimitive hA hpA
  have hpB : p ∉ {a ∈ A | ¬ p ∣ a} := fun h => h.2 (dvd_refl p)
  have h := MSet_block_exchange_lt hp.pos hB hTp.1 (disjoint_nonMultiples_block_set p A) hpB
    hk hrun hc
  rw [← block_decomp_set p A] at h
  exact h

/-- If the composites of `A` are `b`-smooth and `p ∉ A`, the quotient block at `p` consists of
`b`-smooth numbers. -/
theorem quot_smooth {A : Set ℕ} {p b : ℕ} (hp : p.Prime) (hpA : p ∉ A)
    (hsm : ∀ a ∈ A, ¬ a.Prime → Smooth b a) :
    ∀ t ∈ (fun a => a / p) '' {a ∈ A | p ∣ a}, Smooth b t := by
  rintro _ ⟨a, ⟨haA, hpa⟩, rfl⟩ q hq hqt
  have hanp : ¬ a.Prime := fun ha => hpA ((Nat.prime_dvd_prime_iff_eq hp ha).mp hpa ▸ haA)
  exact hsm a haA hanp q hq (hqt.trans (Nat.div_dvd_of_dvd hpa))

/-- **Step (i): compression at a prime `p ≥ 7`**, for `1 ≤ k ≤ 119/8`. -/
theorem MSet_compress_big_lt {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 119 / 8) {A : Set ℕ} {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hA : IsPrimitive A) (hpA : p ∉ A) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c (compressAtSet p A) < MSet k c A := by
  refine MSet_compress_of_run hk1 hp hA hpA (fun y hy => ?_) hc
  have hT := quotients_set_isPrimitive hA hpA
  have hp7R : (7 : ℝ) ≤ p := by exact_mod_cast hp7
  rcases le_or_gt k p with hkp | hpk
  · exact run_pos_of_le hT.1 hp.one_le hk1 hkp hy
  · have hpR : (0 : ℝ) < p := by linarith
    have hs1 : 1 ≤ k / p := by rw [le_div_iff₀ hpR]; linarith
    have hs : k / p ≤ 17 / 8 := by rw [div_le_iff₀ hpR]; nlinarith
    exact run_pos_of_lt_of_Jw Jw_seventeen_eighths hT hp.one_le hpk.le hs
      (goodAt_le_four hs1 (by linarith)) hy

/-- **Step (ii): compression at `5`** when every composite is `5`-smooth, `5 ≤ k ≤ 375/28`. -/
theorem MSet_compress_five_lt {k : ℝ} (hk5 : 5 ≤ k) (hk : k ≤ 375 / 28) {A : Set ℕ}
    (hA : IsPrimitive A) (h5A : 5 ∉ A) (hsm : ∀ a ∈ A, ¬ a.Prime → Smooth 5 a) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c (compressAtSet 5 A) < MSet k c A := by
  have hTp := quotients_set_isPrimitive hA h5A
  have hT1 : ∀ t ∈ (fun a => a / 5) '' {a ∈ A | 5 ∣ a}, 1 ≤ t :=
    fun t ht => le_trans (by norm_num) (hTp.1 t ht)
  have hsT := quot_smooth Nat.prime_five h5A hsm
  refine MSet_compress_of_run (by linarith) Nat.prime_five hA h5A (fun y hy => ?_) hc
  refine run_pos_of_R hT1 (by norm_num) (by push_cast; linarith) (fun z hz => ?_) hy
  refine R5_pos hTp hsT ?_ ?_ hz
  · push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
  · push_cast; rw [div_le_iff₀ (by norm_num)]; linarith

/-- **Step (iii): compression at `3`** when every composite is `3`-smooth,
`3 ≤ k < 3 + 6√3`. -/
theorem MSet_compress_three_lt {k : ℝ} (hk3 : 3 ≤ k) (hk : k < 3 + 6 * Real.sqrt 3)
    {A : Set ℕ} (hA : IsPrimitive A) (h3A : 3 ∉ A) (hsm : ∀ a ∈ A, ¬ a.Prime → Smooth 3 a)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) : MSet k c (compressAtSet 3 A) < MSet k c A := by
  have hTp := quotients_set_isPrimitive hA h3A
  have hT1 : ∀ t ∈ (fun a => a / 3) '' {a ∈ A | 3 ∣ a}, 1 ≤ t :=
    fun t ht => le_trans (by norm_num) (hTp.1 t ht)
  have hsT := quot_smooth Nat.prime_three h3A hsm
  refine MSet_compress_of_run (by linarith) Nat.prime_three hA h3A (fun y hy => ?_) hc
  refine run_pos_of_R hT1 (by norm_num) (by push_cast; linarith) (fun z hz => ?_) hy
  refine R3_pos hTp hsT ?_ ?_ hz
  · push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
  · push_cast; rw [div_lt_iff₀ (by norm_num)]; linarith

/-! ## The ordered descent -/

/-- Composites without prime factors `≥ 7` are `5`-smooth. -/
theorem smooth5_of {A : Set ℕ}
    (h : ∀ b ∈ A, ¬ Nat.Prime b → ∀ q, Nat.Prime q → 7 ≤ q → ¬ q ∣ b) :
    ∀ a ∈ A, ¬ a.Prime → Smooth 5 a := fun a ha hanp q hq hqa => by
  by_contra h'
  exact h a ha hanp q hq (by
    rcases (show q = 6 ∨ 7 ≤ q by omega) with h6 | h7
    · subst h6; norm_num at hq
    · exact h7) hqa

/-- `5`-smooth composites not divisible by `5` are `3`-smooth. -/
theorem smooth3_of {A : Set ℕ} (h5 : ∀ a ∈ A, ¬ a.Prime → Smooth 5 a)
    (h : ∀ b ∈ A, ¬ Nat.Prime b → ¬ 5 ∣ b) : ∀ a ∈ A, ¬ a.Prime → Smooth 3 a :=
  fun a ha hanp q hq hqa => by
    rcases prime_le_five hq (h5 a ha hanp q hq hqa) with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact absurd hqa (h a ha hanp)

/-- `3`-smooth composites not divisible by `3` have no odd prime factor. -/
theorem only_two_of {A : Set ℕ} (h3 : ∀ a ∈ A, ¬ a.Prime → Smooth 3 a)
    (h : ∀ b ∈ A, ¬ Nat.Prime b → ¬ 3 ∣ b) :
    ∀ b ∈ A, ¬ Nat.Prime b → ∀ q, Nat.Prime q → q ∣ b → q = 2 := fun b hb hbnp q hq hqb => by
  have h3' := h3 b hb hbnp q hq hqb
  have := hq.two_le
  interval_cases q
  · rfl
  · exact absurd hqb (h b hb hbnp)

/-- **Ordered descent**: compress at primes `≥ 7`, then at `5`, then at `3`, then at `2`
(singleton block), then insert the missing primes. -/
theorem descent_lt_1339 {J : Finset ℕ → ℝ} {N : ℕ}
    (hbig : ∀ (A : Finset ℕ) (p : ℕ), IsPrimitiveFin A → Nat.Prime p → 7 ≤ p → p ∉ A →
      J (compressAt p A) < J A)
    (hfive : ∀ A : Finset ℕ, IsPrimitiveFin A → 5 ∉ A →
      (∀ a ∈ (A : Set ℕ), ¬ a.Prime → Smooth 5 a) → J (compressAt 5 A) < J A)
    (hthree : ∀ A : Finset ℕ, IsPrimitiveFin A → 3 ∉ A →
      (∀ a ∈ (A : Set ℕ), ¬ a.Prime → Smooth 3 a) → J (compressAt 3 A) < J A)
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
        have step : ∀ p, Nat.Prime p → p ∉ A → (∃ a ∈ A, p ∣ a) →
            J (compressAt p A) < J A → J (primesLE N) < J A := by
          intro p hp hpA hmult hstep
          have hA' := compressAt_isPrimitiveFin hA hp hmult
          have hAN' := compressAt_bounded hA hAN hmult
          have hlt := sum_compressAt_lt' hpA hA hmult
          by_cases heq : compressAt p A = primesLE N
          · rw [← heq]; exact hstep
          · exact (ih _ (hsum ▸ hlt) _ rfl hA' hAN' heq).trans hstep
        -- (i) a composite with a prime factor `≥ 7`
        by_cases hbig' : ∃ b ∈ A, ¬ Nat.Prime b ∧ ∃ q, Nat.Prime q ∧ 7 ≤ q ∧ q ∣ b
        · obtain ⟨b, hbA, hbnp, q, hq, hq7, hqb⟩ := hbig'
          have hqne : q ≠ b := fun h => hbnp (h ▸ hq)
          have hqA : q ∉ A := fun hqA => hqne (hA.2 q hqA b hbA hqb)
          exact step q hq hqA ⟨b, hbA, hqb⟩ (hbig A q hA hq hq7 hqA)
        push Not at hbig'
        have hsm5 := smooth5_of (A := (A : Set ℕ)) hbig'
        -- (ii) a composite divisible by `5`
        by_cases hfive' : ∃ b ∈ A, ¬ Nat.Prime b ∧ 5 ∣ b
        · obtain ⟨b, hbA, hbnp, h5b⟩ := hfive'
          have h5A : 5 ∉ A := fun h5A => hbnp (hA.2 5 h5A b hbA h5b ▸ Nat.prime_five)
          exact step 5 Nat.prime_five h5A ⟨b, hbA, h5b⟩ (hfive A hA h5A hsm5)
        push Not at hfive'
        have hsm3 := smooth3_of (A := (A : Set ℕ)) hsm5 hfive'
        -- (iii) a composite divisible by `3`
        by_cases hthree' : ∃ b ∈ A, ¬ Nat.Prime b ∧ 3 ∣ b
        · obtain ⟨b, hbA, hbnp, h3b⟩ := hthree'
          have h3A : 3 ∉ A := fun h3A => hbnp (hA.2 3 h3A b hbA h3b ▸ Nat.prime_three)
          exact step 3 Nat.prime_three h3A ⟨b, hbA, h3b⟩ (hthree A hA h3A hsm3)
        push Not at hthree'
        -- (iv) every composite is a power of `2`
        have hno := only_two_of (A := (A : Set ℕ)) hsm3 hthree'
        obtain ⟨h2a, h2A, huniq⟩ := even_unique_of_no_odd hA hno haA hnp
        exact step 2 Nat.prime_two h2A ⟨a, haA, h2a⟩ (htwo A a hA h2A haA h2a huniq)
  exact main _ A rfl hA hAN hne

/-! ## Minimality for `51/8 < k < 3 + 6√3` -/

theorem MSet_primesLE_lt_1339_aux {k : ℝ} (hk : 51 / 8 < k) (hk' : k < 3 + 6 * Real.sqrt 3)
    {N : ℕ} {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N)
    (hne : A ≠ primesLE N) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) := by
  have hb := bound_1339
  refine descent_lt_1339 (J := fun S => MSet k c (S : Set ℕ)) ?_ ?_ ?_ ?_ ?_ hA hAN hne
  · intro A p hA hp hp7 hpA
    simp only [coe_compressAt]
    exact MSet_compress_big_lt (by linarith) (by linarith) hp hp7 hA (by simpa using hpA) hc
  · intro A hA h5A hsm
    simp only [coe_compressAt]
    exact MSet_compress_five_lt (by linarith) (by linarith) hA (by simpa using h5A) hsm hc
  · intro A hA h3A hsm
    simp only [coe_compressAt]
    exact MSet_compress_three_lt (by linarith) hk' hA (by simpa using h3A) hsm hc
  · intro A a₀ hA h2A ha₀ h2 huniq
    simp only [coe_compressAt]
    exact MSet_compressAtSet_two_lt (by linarith) hA (by simpa using h2A) (by simpa using ha₀) h2
      (fun a ha h2a => huniq a (by simpa using ha) h2a) hc
  · intro R q hq hR
    simp only [Finset.coe_insert]
    exact MSet_insert_lt (by simpa using hq) (fun n hn => hR n hn) (by linarith) hc

theorem goodAt_1339 {k : ℝ} (hk : 51 / 8 < k) (hk' : k < 3 + 6 * Real.sqrt 3) : GoodAt k := by
  classical
  intro A hA c hc
  have hk1 : 1 ≤ k := by linarith
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  have hP := tendsto_MSet_truncation Primes hk1 hcI
  simp only [primes_truncation] at hP
  refine le_of_tendsto_of_tendsto' hP (tendsto_MSet_truncation A hk1 hcI) fun N => ?_
  by_cases h : (Finset.range (N + 1)).filter (· ∈ A) = primesLE N
  · rw [h]
  · exact (MSet_primesLE_lt_1339_aux hk hk' (truncation_isPrimitiveFin hA N)
      (truncation_bounded A N) h hc).le

theorem MSet_primes_lt_1339_aux {k : ℝ} (hk : 51 / 8 < k) (hk' : k < 3 + 6 * Real.sqrt 3)
    {A : Set ℕ} (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A := by
  have hb := bound_1339
  have hk1 : 1 ≤ k := by linarith
  have hgood := goodAt_1339 hk hk'
  have after : ∀ p, Nat.Prime p → MSet k c (compressAtSet p A) < MSet k c A →
      MSet k c Primes < MSet k c A := fun p hp hstep =>
    lt_of_le_of_lt (hgood _ (compressAtSet_isPrimitive hA hp) c hc) hstep
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
      (MSet_insert_lt hqA (fun n hn => (hall n hn).one_le) hk1 hc)
  · push Not at hall
    obtain ⟨m, hmA, hmnp⟩ := hall
    by_cases hbig' : ∃ b ∈ A, ¬ Nat.Prime b ∧ ∃ q, Nat.Prime q ∧ 7 ≤ q ∧ q ∣ b
    · obtain ⟨b, hbA, hbnp, q, hq, hq7, hqb⟩ := hbig'
      have hqne : q ≠ b := fun h => hbnp (h ▸ hq)
      have hqA : q ∉ A := fun hqA => hqne (hA.2 q hqA b hbA hqb)
      exact after q hq (MSet_compress_big_lt hk1 (by linarith) hq hq7 hA hqA hc)
    push Not at hbig'
    have hsm5 := smooth5_of hbig'
    by_cases hfive' : ∃ b ∈ A, ¬ Nat.Prime b ∧ 5 ∣ b
    · obtain ⟨b, hbA, hbnp, h5b⟩ := hfive'
      have h5A : 5 ∉ A := fun h5A => hbnp (hA.2 5 h5A b hbA h5b ▸ Nat.prime_five)
      exact after 5 Nat.prime_five
        (MSet_compress_five_lt (by linarith) (by linarith) hA h5A hsm5 hc)
    push Not at hfive'
    have hsm3 := smooth3_of hsm5 hfive'
    by_cases hthree' : ∃ b ∈ A, ¬ Nat.Prime b ∧ 3 ∣ b
    · obtain ⟨b, hbA, hbnp, h3b⟩ := hthree'
      have h3A : 3 ∉ A := fun h3A => hbnp (hA.2 3 h3A b hbA h3b ▸ Nat.prime_three)
      exact after 3 Nat.prime_three (MSet_compress_three_lt (by linarith) hk' hA h3A hsm3 hc)
    push Not at hthree'
    have hno := only_two_of hsm3 hthree'
    obtain ⟨h2m, h2A, huniq⟩ := even_unique_of_no_odd hA hno hmA hmnp
    exact after 2 Nat.prime_two (MSet_compressAtSet_two_lt hk1 hA h2A hmA h2m huniq hc)

/-! ## Main theorems -/

/-- **Moments for `0 < k < 3 + 6√3`, finite sets** (notes, Theorem 3.7). For every primitive
`A ⊆ {2,…,N}`, `A ≠ 𝒫_N`, and every `c ∈ (0,1]`:
`𝔼 min(Z_{𝒫_N}^k, c^k) < 𝔼 min(Z_A^k, c^k)`. -/
theorem moment_primesLE_lt_1339 {k : ℝ} (hk0 : 0 < k) (hk : k < 3 + 6 * Real.sqrt 3) {N : ℕ}
    {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c (primesLE N : Set ℕ) < MSet k c (A : Set ℕ) := by
  rcases le_or_gt k (51 / 8) with h | h
  · exact moment_primesLE_lt_odd hk0 h hA hAN hne hc
  · exact MSet_primesLE_lt_1339_aux h hk hA hAN hne hc

/-- **Moments for `0 < k < 3 + 6√3`, all primitive sets** (notes, Theorem 3.7). For every
primitive `A ≠ 𝒫`, finite or infinite, and every `c ∈ (0,1]`:
`𝔼 min(Z_𝒫^k, c^k) < 𝔼 min(Z_A^k, c^k)`. -/
theorem moment_primes_lt_1339 {k : ℝ} (hk0 : 0 < k) (hk : k < 3 + 6 * Real.sqrt 3)
    {A : Set ℕ} (hA : IsPrimitive A) (hne : A ≠ Primes) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    MSet k c Primes < MSet k c A := by
  rcases le_or_gt k (51 / 8) with h | h
  · exact moment_primes_lt_odd hk0 h hA hne hc
  · exact MSet_primes_lt_1339_aux h hk hA hne hc

end RntPaper
