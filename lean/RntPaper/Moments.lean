import RntPaper.Consequences

/-!
# Real-order truncated moments (extension of paper Proposition 5.1)

For real `k ≥ 1` and `c ∈ (0,1]`,
`Mk k c S = ∫₀ᶜ k u^{k-1} P_S(u) du = 𝔼 min(Z_Sᵏ, cᵏ)`.

* (L1) `Mk_block_exchange_lt`: the block exchange of Proposition 3.4 lowers
  `Mk k c` whenever the exchange prime `p` (any integer) satisfies `k ≤ p`.
  Engine: `running_pos_rpow_comp_pow_of`, integration by parts against the
  singular weight `w(u) = (k/p)·u^{k-p}` (nonincreasing because `k ≤ p`).
* (L2) `Mk_primesLE_lt`: Proposition 5.1 for every real `k ∈ [1,2]`.
* (L3) `Mk_reduction`: for any real `k ≥ 1` every primitive `A ⊆ {2,…,N}` can be
  replaced, without increasing `Mk k c`, by a primitive `A*` containing all
  primes `p ≤ N` with `p ≥ k` and no proper multiple of such primes.
* (L4) `Mk_one_antitone`: `k ↦ Mk k 1 S` is nonincreasing on `[1,∞)`;
  `primes_minimize_Mk_N9`: for every real `k ∈ [1, 125.84]`, `{2,3,5,7}` is the
  unique minimiser of `Mk k 1` over primitive subsets of `{2,…,9}`.
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set

/-! ## Definition -/

/-- Real-order truncated moment `∫₀ᶜ k u^{k-1} P_S(u) du` (real power `rpow`). -/
noncomputable def Mk (k c : ℝ) (S : Finset ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..c, k * u ^ (k - 1) * qProd S u

/-- For natural `k ≥ 1`, `Mk` agrees with `Mc` of `Consequences.lean`. -/
theorem Mk_natCast {k : ℕ} (hk : 1 ≤ k) (c : ℝ) (S : Finset ℕ) :
    Mk k c S = Mc k c S := by
  unfold Mk Mc
  congr 1
  funext u
  rw [← Real.rpow_natCast u (k - 1), Nat.cast_sub hk, Nat.cast_one]

theorem continuous_rpowWeight {k : ℝ} (hk : 1 ≤ k) :
    Continuous (fun u : ℝ => k * u ^ (k - 1)) :=
  continuous_const.mul (Real.continuous_rpow_const (by linarith))

theorem rpowWeight_nonneg {k : ℝ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ k * u ^ (k - 1) :=
  mul_nonneg (by linarith) (Real.rpow_nonneg hu _)

theorem intervalIntegrable_Mk_integrand {k : ℝ} (hk : 1 ≤ k) (S : Finset ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => k * u ^ (k - 1) * qProd S u) volume a b :=
  ((continuous_rpowWeight hk).mul (qProd_continuous S)).intervalIntegrable _ _

/-! ## (L1) Running positivity with the weight `k u^{k-1}` under `u ↦ uᵖ` -/

/-- **Transport with a real power weight.**  If `e` is continuous with `∫₀ᵈ e > 0`
for `d ∈ (0,1]`, then for real `1 ≤ k ≤ p` (`p` a natural number)
`∫₀ʸ k u^{k-1} e(uᵖ) du > 0` for all `y ∈ (0,1]`.

Integration by parts on `[ε,y]` of `w · A'` with `A(u) = ∫₀^{uᵖ} e`,
`A'(u) = e(uᵖ)·p·u^{p-1}` and `w(u) = (k/p) u^{k-p}` (nonincreasing since
`k ≤ p`), which gives `∫_ε^y ≥ w(y)A(y) − w(ε)A(ε)`, with
`|w(ε)A(ε)| ≤ (k/p)·M·ε^k ≤ (k/p)·M·ε`; the head `∫₀^ε` is `O(ε)`. -/
theorem running_pos_rpow_comp_pow_of {e : ℝ → ℝ} (he : Continuous e)
    (hrun : ∀ d ∈ Ioc (0 : ℝ) 1, 0 < ∫ v in (0 : ℝ)..d, e v)
    {k : ℝ} (hk : 1 ≤ k) {p : ℕ} (hkp : k ≤ p) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..y, k * u ^ (k - 1) * e (u ^ p) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hk0 : 0 < k := by linarith
  have hp1 : 1 ≤ p := by exact_mod_cast (show (1 : ℝ) ≤ p by linarith)
  set f : ℝ → ℝ := fun u => k * u ^ (k - 1) * e (u ^ p) with hf
  have hfc : Continuous f := (continuous_rpowWeight hk).mul (he.comp (continuous_pow p))
  -- bounds on `e` and on its running integral
  obtain ⟨M, hM0, hMb⟩ := abs_runInt_le he
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    he.continuousOn
  set M1' := max M1 0 with hM1'
  have hM1'0 : 0 ≤ M1' := le_max_right _ _
  have he_bd : ∀ v ∈ Icc (0 : ℝ) 1, |e v| ≤ M1' := fun v hv => by
    have h := hM1 v hv
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left M1 0)
  -- the antiderivative `A(u) = runInt e (uᵖ)`
  set A : ℝ → ℝ := fun u => runInt e (u ^ p) with hA
  have hAderiv : ∀ u, HasDerivAt A (e (u ^ p) * ((p : ℝ) * u ^ (p - 1))) u := fun u =>
    (hasDerivAt_runInt he (u ^ p)).comp u (hasDerivAt_pow p u)
  have hApos : ∀ u ∈ Ioc (0 : ℝ) 1, 0 < A u := fun u hu =>
    hrun _ ⟨pow_pos hu.1 _, pow_le_one₀ hu.1.le hu.2⟩
  have hAnn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ A u := fun u hu =>
    runInt_nonneg hrun ⟨pow_nonneg hu.1 _, pow_le_one₀ hu.1 hu.2⟩
  have hAle : ∀ u ∈ Icc (0 : ℝ) 1, |A u| ≤ M * u ^ p := fun u hu =>
    hMb _ ⟨pow_nonneg hu.1 _, pow_le_one₀ hu.1 hu.2⟩
  -- the weight `w(u) = (k/p) u^{k-p}`
  set w : ℝ → ℝ := fun u => k / p * u ^ (k - p) with hw
  set w' : ℝ → ℝ := fun u => k / p * ((k - p) * u ^ (k - p - 1)) with hw'
  have hwderiv : ∀ u : ℝ, u ≠ 0 → HasDerivAt w (w' u) u := fun u hu =>
    (Real.hasDerivAt_rpow_const (p := k - p) (Or.inl hu)).const_mul (k / p)
  have hw'nonpos : ∀ u : ℝ, 0 < u → w' u ≤ 0 := fun u hu => by
    simp only [hw']
    have h1 : 0 ≤ u ^ (k - p - 1) := Real.rpow_nonneg hu.le _
    have h2 : (k - p) * u ^ (k - p - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) h1
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h2
  have hwpos : ∀ u : ℝ, 0 < u → 0 < w u := fun u hu => by
    simp only [hw]
    have := Real.rpow_pos_of_pos hu (k - p)
    positivity
  have hwA : ∀ u : ℝ, 0 < u → w u * (e (u ^ p) * ((p : ℝ) * u ^ (p - 1))) = f u :=
    fun u hu => by
      simp only [hw, hf]
      have hcast : u ^ (p - 1) = u ^ ((p : ℝ) - 1) := by
        rw [← Real.rpow_natCast u (p - 1), Nat.cast_sub hp1, Nat.cast_one]
      rw [hcast]
      have hcomb : u ^ (k - p) * u ^ ((p : ℝ) - 1) = u ^ (k - 1) := by
        rw [← Real.rpow_add hu]
        congr 1
        ring
      have hpne : (p : ℝ) ≠ 0 := hp0.ne'
      calc k / p * u ^ (k - p) * (e (u ^ p) * (p * u ^ ((p : ℝ) - 1)))
          = k * (u ^ (k - p) * u ^ ((p : ℝ) - 1)) * e (u ^ p) := by
            field_simp
        _ = k * u ^ (k - 1) * e (u ^ p) := by rw [hcomb]
  -- the lower bound `L = w(y) A(y) > 0` and the choice of `ε`
  set L := w y * A y with hL
  have hLpos : 0 < L := mul_pos (hwpos y hy.1) (hApos y hy)
  set C := k / p * M + k * M1' + 1 with hC
  have hCpos : 0 < C := by positivity
  set ε := min (y / 2) (L / (2 * C)) with hε
  have hε0 : 0 < ε := lt_min (by linarith [hy.1]) (by positivity)
  have hεy : ε < y := (min_le_left _ _).trans_lt (by linarith [hy.1])
  have hεC : C * ε ≤ L / 2 := by
    have h := min_le_right (y / 2) (L / (2 * C))
    calc C * ε ≤ C * (L / (2 * C)) := mul_le_mul_of_nonneg_left h hCpos.le
      _ = L / 2 := by field_simp
  have hε1 : ε ≤ 1 := by linarith [min_le_left (y / 2) (L / (2 * C)), hy.2]
  -- integration by parts on `[ε, y]`
  have hIcc : uIcc ε y = Icc ε y := uIcc_of_le hεy.le
  have hw'cont : ContinuousOn w' (uIcc ε y) := by
    rw [hIcc]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    exact (hε0.trans_le hx.1).ne'
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := y)
    (u := w) (v := A) (u' := w') (v' := fun u => e (u ^ p) * ((p : ℝ) * u ^ (p - 1)))
    (fun x hx => hwderiv x (by rw [hIcc] at hx; exact (hε0.trans_le hx.1).ne'))
    (fun x _ => hAderiv x) hw'cont.intervalIntegrable
    (((he.comp (continuous_pow _)).mul (continuous_const.mul (continuous_pow _))).intervalIntegrable
      _ _)
  have hcongr : ∫ u in ε..y, f u
      = ∫ u in ε..y, w u * (e (u ^ p) * ((p : ℝ) * u ^ (p - 1))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hIcc] at hx
    exact (hwA x (hε0.trans_le hx.1)).symm
  have htail : ∫ u in ε..y, w' u * A u ≤ 0 := by
    have h := intervalIntegral.integral_nonneg (f := fun u => -(w' u * A u)) (μ := volume)
      hεy.le (fun u hu => by
        have := mul_nonpos_of_nonpos_of_nonneg (hw'nonpos u (hε0.trans_le hu.1))
          (hAnn u ⟨(hε0.trans_le hu.1).le, hu.2.trans hy.2⟩)
        linarith)
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hwεAε : w ε * A ε ≤ k / p * M * ε := by
    have h1 : w ε * A ε ≤ w ε * (M * ε ^ p) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hAle ε ⟨hε0.le, hε1⟩))
        (hwpos ε hε0).le
    have h2 : w ε * (M * ε ^ p) = k / p * M * ε ^ k := by
      simp only [hw]
      rw [← Real.rpow_natCast ε p]
      have : ε ^ (k - p) * ε ^ (p : ℝ) = ε ^ k := by
        rw [← Real.rpow_add hε0]
        congr 1
        ring
      calc k / p * ε ^ (k - p) * (M * ε ^ (p : ℝ))
          = k / p * M * (ε ^ (k - p) * ε ^ (p : ℝ)) := by ring
        _ = k / p * M * ε ^ k := by rw [this]
    have h3 : ε ^ k ≤ ε := by
      have := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hk
      simpa using this
    have h4 : 0 ≤ k / p * M := by positivity
    calc w ε * A ε ≤ w ε * (M * ε ^ p) := h1
      _ = k / p * M * ε ^ k := h2
      _ ≤ k / p * M * ε := mul_le_mul_of_nonneg_left h3 h4
  have hmid : L - k / p * M * ε ≤ ∫ u in ε..y, f u := by
    rw [hcongr, hibp]
    linarith
  -- the initial piece `[0, ε]`
  have hhead : -(k * M1' * ε) ≤ ∫ u in (0 : ℝ)..ε, f u := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ε)
      (C := k * M1') (f := f) (fun x hx => by
        rw [uIoc_of_le hε0.le] at hx
        have hx1 : x ≤ 1 := hx.2.trans hε1
        simp only [hf, Real.norm_eq_abs, abs_mul]
        have h1 : |x ^ (k - 1)| ≤ 1 := by
          rw [abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
          exact Real.rpow_le_one hx.1.le hx1 (by linarith)
        have h2 : |e (x ^ p)| ≤ M1' :=
          he_bd _ ⟨pow_nonneg hx.1.le _, pow_le_one₀ hx.1.le hx1⟩
        rw [abs_of_pos hk0]
        calc k * |x ^ (k - 1)| * |e (x ^ p)| ≤ k * 1 * M1' := by gcongr
          _ = k * M1' := by ring)
    rw [Real.norm_eq_abs, abs_le] at h
    simpa [abs_of_pos hε0] using h.1
  have hsplit : ∫ u in (0 : ℝ)..y, f u = (∫ u in (0 : ℝ)..ε, f u) + ∫ u in ε..y, f u :=
    (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)).symm
  rw [hsplit]
  have hsum : k / p * M * ε + k * M1' * ε ≤ C * ε := by
    have : k / p * M * ε + k * M1' * ε + ε = C * ε := by simp only [hC]; ring
    linarith
  linarith

/-- The block-exchange identity with weight `k u^{k-1}`. -/
theorem Mk_blockStep_diff {B T : Finset ℕ} {p : ℕ} (hp : 0 < p)
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B) {k : ℝ} (hk : 1 ≤ k) (c : ℝ) :
    Mk k c (B ∪ T.image (· * p)) - Mk k c (insert p B)
      = ∫ u in (0 : ℝ)..c, qProd B u * (k * u ^ (k - 1) * blockE T (u ^ p)) := by
  have hinj : Set.InjOn (· * p) (T : Set ℕ) := fun a _ b _ h =>
    Nat.eq_of_mul_eq_mul_right hp h
  unfold Mk
  rw [← intervalIntegral.integral_sub (intervalIntegrable_Mk_integrand hk _ _ _)
    (intervalIntegrable_Mk_integrand hk _ _ _)]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  have := qProd_blockStep_diff hdisj hpB hinj u
  linear_combination (k * u ^ (k - 1)) * this

set_option linter.unusedVariables false in
/-- **(L1) Strict block exchange for real moments.**  For real `k ≥ 1` and an
integer `p` with `k ≤ p`, `B, T` finite, `T ⊆ {2,3,…}` nonempty, `B ⊆ {2,3,…}`
disjoint from `pT`, `p ∉ B`: `Mk k c (B ∪ {p}) < Mk k c (B ∪ pT)` for every
`c ∈ (0,1]`.  (`hTne` is not needed by the proof, as in `block_exchange_lt`.) -/
theorem Mk_block_exchange_lt {B T : Finset ℕ} {p : ℕ} {k : ℝ} (hk : 1 ≤ k) (hkp : k ≤ p)
    (hB : ∀ b ∈ B, 2 ≤ b) (hT : ∀ t ∈ T, 2 ≤ t) (hTne : T.Nonempty)
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mk k c (insert p B) < Mk k c (B ∪ T.image (· * p)) := by
  have hp : 0 < p := by exact_mod_cast (show (0 : ℝ) < p by linarith)
  rw [← sub_pos, Mk_blockStep_diff hp hdisj hpB hk c]
  refine integral_weight_mul_pos_upto (g := fun u => k * u ^ (k - 1) * blockE T (u ^ p))
    (w := qProd B) (w' := qProd' B) hc ?_ (fun x _ => hasDerivAt_qProd B x)
    (continuous_qProd' B) (qProd_nonneg B ⟨hc.1.le, hc.2⟩) ?_ ?_ ?_
  · exact (continuous_rpowWeight hk).mul ((continuous_blockE T).comp (continuous_pow p))
  · intro x hx
    exact qProd'_nonpos B ⟨hx.1, hx.2.trans hc.2⟩
  · intro y hy
    exact running_pos_rpow_comp_pow_of (continuous_blockE T)
      (fun _d hd => blockE_partial_pos hT hd) hk hkp ⟨hy.1, hy.2.trans hc.2⟩
  · rcases B.eq_empty_or_nonempty with hBe | hBne
    · left
      subst hBe
      simp [qProd]
    · right
      refine ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.1]⟩, ?_⟩
      exact qProd'_neg_of_nonempty hBne (fun b hb => le_trans (by norm_num) (hB b hb))
        ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- Strict compression `C_p` for real moments, for any integer `p ≥ k`
(`p ∉ A`, `p` divides some element of `A`). -/
theorem Mk_compressAt_lt {A : Finset ℕ} {p : ℕ} {k : ℝ} (hk : 1 ≤ k) (hkp : k ≤ p)
    (hA : IsPrimitiveFin A) (hpA : p ∉ A) (hmult : ∃ a ∈ A, p ∣ a)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mk k c (compressAt p A) < Mk k c A := by
  have hB : ∀ b ∈ A.filter (fun a => ¬ p ∣ a), 2 ≤ b :=
    fun b hb => hA.1 b (Finset.mem_filter.mp hb).1
  have hT : ∀ t ∈ quotients p A, 2 ≤ t := quotients_ge_two_of_not_mem hA.1 hpA
  have hTne : (quotients p A).Nonempty := by
    obtain ⟨m, hmA, hpm⟩ := hmult
    exact ⟨m / p, mem_quotients.mpr ⟨m, hmA, hpm, rfl⟩⟩
  have h := Mk_block_exchange_lt hk hkp hB hT hTne (disjoint_nonMultiples_block p A)
    (prime_not_mem_nonMultiples p A) hc
  rw [← block_decomp p A] at h
  exact h

/-- Enlarging the exponent set does not increase `Mk`. -/
theorem Mk_antitone {k : ℝ} (hk : 1 ≤ k) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) {S T : Finset ℕ}
    (hST : S ⊆ T) : Mk k c T ≤ Mk k c S := by
  unfold Mk
  refine intervalIntegral.integral_mono_on hc.1 (intervalIntegrable_Mk_integrand hk _ _ _)
    (intervalIntegrable_Mk_integrand hk _ _ _) (fun u hu => ?_)
  exact mul_le_mul_of_nonneg_left (qProd_antitone_pointwise hST ⟨hu.1, hu.2.trans hc.2⟩)
    (rpowWeight_nonneg hk hu.1)

/-- Adding a missing exponent strictly lowers `Mk`. -/
theorem Mk_insert_lt {R : Finset ℕ} {q : ℕ} (hq : q ∉ R) (hR : ∀ n ∈ R, 1 ≤ n)
    {k : ℝ} (hk : 1 ≤ k) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mk k c (insert q R) < Mk k c R := by
  unfold Mk
  have hwc := continuous_rpowWeight hk
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hc.1
    (hwc.mul (qProd_continuous _)).continuousOn (hwc.mul (qProd_continuous _)).continuousOn
    ?_ ?_
  · intro u hu
    exact mul_le_mul_of_nonneg_left
      (qProd_antitone_pointwise (Finset.subset_insert q R) ⟨hu.1.le, hu.2.trans hc.2⟩)
      (rpowWeight_nonneg hk hu.1.le)
  · refine ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.1]⟩, ?_⟩
    have hu : c / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.1, hc.2]⟩
    have hwpos : 0 < k * (c / 2) ^ (k - 1) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hu.1 _)
    refine mul_lt_mul_of_pos_left ?_ hwpos
    rw [qProd_insert hq]
    have hP : 0 < qProd R (c / 2) := qProd_pos_of_mem_Ioo hR hu
    have hfac : 1 - (c / 2) ^ q < 1 := by
      have hpow : (0 : ℝ) < (c / 2) ^ q := pow_pos hu.1 q
      linarith
    calc (1 - (c / 2) ^ q) * qProd R (c / 2)
        < 1 * qProd R (c / 2) := mul_lt_mul_of_pos_right hfac hP
      _ = qProd R (c / 2) := one_mul _

/-! ## (L2) Proposition 5.1 for all real `k ∈ [1,2]` -/

/-- **(L2) Proposition 5.1, real `k ∈ [1,2]`.**  For primitive `A ⊆ {2,…,N}`,
`A ≠ 𝒫_N`, and `c ∈ (0,1]`: `Mk k c 𝒫_N < Mk k c A`. -/
theorem Mk_primesLE_lt {k : ℝ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) (hne : A ≠ primesLE N)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mk k c (primesLE N) < Mk k c A :=
  descent_lt (J := Mk k c)
    (fun _A p hA hp hpA hmult =>
      Mk_compressAt_lt hk1 (hk2.trans (by exact_mod_cast hp.two_le)) hA hpA hmult hc)
    (fun _R _q hq hR => Mk_insert_lt hq hR hk1 hc) hA hAN hne

theorem Mk_primesLE_le {k : ℝ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) {N : ℕ} {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Mk k c (primesLE N) ≤ Mk k c A := by
  by_cases h : A = primesLE N
  · rw [h]
  · exact (Mk_primesLE_lt hk1 hk2 hA hAN h hc).le

/-! ## (L3) Reduction to sets containing every prime `p ≥ k` -/

/-- `A` contains no proper multiple of a prime `p ≥ k`. -/
def NoLargePrimeMultiples (k : ℝ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ p, Nat.Prime p → k ≤ p → p ∣ a → a = p

/-- Phase 2: insert the missing primes `k ≤ p ≤ N`, one at a time. -/
theorem Mk_reduction_insert {k : ℝ} (hk : 1 ≤ k) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) (N : ℕ) :
    ∀ (n : ℕ) (A : Finset ℕ), (primesLE N \ A).card = n → IsPrimitiveFin A →
      (∀ a ∈ A, a ≤ N) → NoLargePrimeMultiples k A →
      ∃ A' : Finset ℕ, IsPrimitiveFin A' ∧ (∀ a ∈ A', a ≤ N) ∧
        NoLargePrimeMultiples k A' ∧ (∀ p, Nat.Prime p → p ≤ N → k ≤ p → p ∈ A') ∧
        (A' = A ∨ Mk k c A' < Mk k c A) := by
  intro n
  induction n with
  | zero =>
    intro A hcard hA hAN hgood
    refine ⟨A, hA, hAN, hgood, fun p hp hpN _ => ?_, Or.inl rfl⟩
    have hsub := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard)
    exact hsub (mem_primesLE.mpr ⟨hp, hpN⟩)
  | succ n ih =>
    intro A hcard hA hAN hgood
    by_cases hall : ∀ p, Nat.Prime p → p ≤ N → k ≤ p → p ∈ A
    · exact ⟨A, hA, hAN, hgood, hall, Or.inl rfl⟩
    push Not at hall
    obtain ⟨q, hq, hqN, hkq, hqA⟩ := hall
    have hA' : IsPrimitiveFin (insert q A) := by
      refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
      · rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha) with rfl | ha
        · exact hq.two_le
        · exact hA.1 a ha
      · rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha) with rfl | ha' <;>
          rcases Finset.mem_insert.mp (Finset.mem_coe.mp hb) with rfl | hb'
        · rfl
        · exact (hgood b hb' a hq hkq hab).symm
        · rcases (Nat.dvd_prime hq).mp hab with h1 | h
          · have := hA.1 a ha'; omega
          · exact h
        · exact hA.2 a ha' b hb' hab
    have hAN' : ∀ a ∈ insert q A, a ≤ N := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hqN
      · exact hAN a ha
    have hgood' : NoLargePrimeMultiples k (insert q A) := by
      intro a ha p hp hkp hpa
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpa).symm
      · exact hgood a ha p hp hkp hpa
    have hqmem : q ∈ primesLE N \ A := Finset.mem_sdiff.mpr ⟨mem_primesLE.mpr ⟨hq, hqN⟩, hqA⟩
    have hcard' : (primesLE N \ insert q A).card = n := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hqmem, hcard]
      rfl
    have hlt : Mk k c (insert q A) < Mk k c A :=
      Mk_insert_lt hqA (fun a ha => (hA.1 a ha).trans' (by norm_num)) hk hc
    obtain ⟨A', h1, h2, h3, h4, h5⟩ := ih (insert q A) hcard' hA' hAN' hgood'
    refine ⟨A', h1, h2, h3, h4, Or.inr ?_⟩
    rcases h5 with rfl | h5
    · exact hlt
    · exact h5.trans hlt

/-- Phase 1: compress at primes `p ≥ k` having proper multiples in `A`
(strong induction on the element sum), then phase 2. -/
theorem Mk_reduction_aux {k : ℝ} (hk : 1 ≤ k) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) (N : ℕ) :
    ∀ (s : ℕ) (A : Finset ℕ), A.sum id = s → IsPrimitiveFin A → (∀ a ∈ A, a ≤ N) →
      ∃ A' : Finset ℕ, IsPrimitiveFin A' ∧ (∀ a ∈ A', a ≤ N) ∧
        NoLargePrimeMultiples k A' ∧ (∀ p, Nat.Prime p → p ≤ N → k ≤ p → p ∈ A') ∧
        (A' = A ∨ Mk k c A' < Mk k c A) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro A hsum hA hAN
    by_cases hgood : NoLargePrimeMultiples k A
    · exact Mk_reduction_insert hk hc N _ A rfl hA hAN hgood
    unfold NoLargePrimeMultiples at hgood
    push Not at hgood
    obtain ⟨a, haA, p, hp, hkp, hpa, hne⟩ := hgood
    have hpA : p ∉ A := fun h => hne (hA.2 p h a haA hpa).symm
    have hmult : ∃ a ∈ A, p ∣ a := ⟨a, haA, hpa⟩
    have hstep : Mk k c (compressAt p A) < Mk k c A :=
      Mk_compressAt_lt hk hkp hA hpA hmult hc
    have hsum' : (compressAt p A).sum id < s :=
      hsum ▸ sum_compressAt_lt hp.two_le hA hpA hmult
    obtain ⟨A', h1, h2, h3, h4, h5⟩ := ih _ hsum' (compressAt p A) rfl
      (compressAt_isPrimitiveFin hA hp hmult) (compressAt_bounded hA hAN hmult)
    refine ⟨A', h1, h2, h3, h4, Or.inr ?_⟩
    rcases h5 with rfl | h5
    · exact hstep
    · exact h5.trans hstep

/-- **(L3) Reduction lemma.**  For real `k ≥ 1`, `c ∈ (0,1]` and primitive
`A ⊆ {2,…,N}` there is a primitive `A* ⊆ {2,…,N}` containing every prime
`p ≤ N` with `p ≥ k`, containing no proper multiple of any prime `p ≥ k`, with
`Mk k c A* ≤ Mk k c A`, strictly if `A* ≠ A`. -/
theorem Mk_reduction {k : ℝ} (hk : 1 ≤ k) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) {N : ℕ}
    {A : Finset ℕ} (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ N) :
    ∃ A' : Finset ℕ, IsPrimitiveFin A' ∧ (∀ a ∈ A', a ≤ N) ∧
      (∀ p, Nat.Prime p → p ≤ N → k ≤ p → p ∈ A') ∧
      (∀ a ∈ A', ∀ p, Nat.Prime p → k ≤ p → p ∣ a → a = p) ∧
      Mk k c A' ≤ Mk k c A ∧ (A' ≠ A → Mk k c A' < Mk k c A) := by
  obtain ⟨A', h1, h2, h3, h4, h5⟩ := Mk_reduction_aux hk hc N _ A rfl hA hAN
  refine ⟨A', h1, h2, h4, h3, ?_, fun hne => ?_⟩
  · rcases h5 with rfl | h5
    · exact le_rfl
    · exact h5.le
  · rcases h5 with h5 | h5
    · exact absurd h5 hne
    · exact h5

/-! ## (L4) Monotonicity in `k` at `c = 1`, and the `N = 9` certificate -/

/-- Integration by parts at `c = 1`: `Mk k 1 S = P_S(1) − ∫₀¹ uᵏ P_S'(u) du`. -/
theorem Mk_one_eq_ibp {k : ℝ} (hk : 1 ≤ k) (S : Finset ℕ) :
    Mk k 1 S = qProd S 1 - ∫ u in (0 : ℝ)..1, u ^ k * qProd' S u := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun x : ℝ => x ^ k) (v := qProd S) (u' := fun x => k * x ^ (k - 1))
    (v' := qProd' S)
    (fun x _ => Real.hasDerivAt_rpow_const (Or.inr hk)) (fun x _ => hasDerivAt_qProd S x)
    ((continuous_rpowWeight hk).intervalIntegrable _ _)
    ((continuous_qProd' S).intervalIntegrable _ _)
  have h0 : (0 : ℝ) ^ k = 0 := Real.zero_rpow (by linarith)
  simp only [Real.one_rpow, h0, one_mul, zero_mul, sub_zero] at h
  unfold Mk
  linarith

theorem rpow_le_rpow_of_exponent_ge_Icc {x a b : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hab : a ≤ b) : x ^ b ≤ x ^ a := by
  rcases hx.1.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (by linarith), Real.zero_rpow ha.ne']
  · exact Real.rpow_le_rpow_of_exponent_ge h hx.2 hab

/-- **(L4a) Monotonicity in `k`.**  `k ↦ Mk k 1 S = 𝔼 Z_Sᵏ` is nonincreasing on
`[1,∞)`. -/
theorem Mk_one_antitone {k k' : ℝ} (hk : 1 ≤ k) (hkk' : k ≤ k') (S : Finset ℕ) :
    Mk k' 1 S ≤ Mk k 1 S := by
  rw [Mk_one_eq_ibp hk, Mk_one_eq_ibp (hk.trans hkk')]
  have hint : ∀ r : ℝ, 0 ≤ r →
      IntervalIntegrable (fun u : ℝ => u ^ r * qProd' S u) volume 0 1 := fun r hr =>
    ((Real.continuous_rpow_const hr).mul (continuous_qProd' S)).intervalIntegrable _ _
  have : ∫ u in (0 : ℝ)..1, u ^ k * qProd' S u ≤ ∫ u in (0 : ℝ)..1, u ^ k' * qProd' S u := by
    refine intervalIntegral.integral_mono_on zero_le_one (hint k (by linarith))
      (hint k' (by linarith)) (fun u hu => ?_)
    exact mul_le_mul_of_nonpos_right (rpow_le_rpow_of_exponent_ge_Icc hu (by linarith) hkk')
      (qProd'_nonpos S hu)
  linarith

/-- Closed form at `c = 1`: `Mk k 1 S = ∑_{T ⊆ S} (-1)^{|T|} k/(k + ΣT)`. -/
theorem Mk_one_eq_sum {k : ℝ} (hk : 1 ≤ k) (S : Finset ℕ) :
    Mk k 1 S = ∑ T ∈ S.powerset, (subsetSign T : ℝ) * (k / (k + subsetWeight T)) := by
  unfold Mk
  have hpt : ∀ u ∈ uIcc (0 : ℝ) 1, k * u ^ (k - 1) * qProd S u
      = ∑ T ∈ S.powerset, (subsetSign T : ℝ) * k * u ^ (k - 1 + (subsetWeight T : ℝ)) := by
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    rw [qProd_powerset_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Real.rpow_add_of_nonneg hu.1 (by linarith) (Nat.cast_nonneg _), Real.rpow_natCast]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun T _ => ?_)
    have hw0 : (0 : ℝ) ≤ subsetWeight T := Nat.cast_nonneg _
    have hpos : 0 < k + (subsetWeight T : ℝ) := by linarith
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    have : k - 1 + (subsetWeight T : ℝ) + 1 = k + subsetWeight T := by ring
    rw [this, Real.one_rpow, Real.zero_rpow hpos.ne', sub_zero]
    field_simp
  · intro T _
    exact (continuous_const.mul (Real.continuous_rpow_const
      (add_nonneg (by linarith) (Nat.cast_nonneg _)))).intervalIntegrable _ _

/-- Exact rational value of `Mk k 1 S` at rational `k`. -/
def momentK (S : Finset ℕ) (k : ℚ) : ℚ :=
  ∑ T ∈ S.powerset, subsetSign T * (k / (k + subsetWeight T))

theorem momentK_cast {k : ℚ} (hk : 1 ≤ k) (S : Finset ℕ) :
    ((momentK S k : ℚ) : ℝ) = Mk k 1 S := by
  rw [Mk_one_eq_sum (by exact_mod_cast hk)]
  unfold momentK
  push_cast
  rfl

/-- The maximal primitive subsets of `{2,…,9}` other than the primes. -/
def others9 : List (Finset ℕ) :=
  [{2, 5, 7, 9}, {3, 4, 5, 7}, {3, 5, 7, 8}, {4, 5, 6, 7, 9}, {5, 6, 7, 8, 9}]

def maxAntichains9 : List (Finset ℕ) := {2, 3, 5, 7} :: others9

/-- Every primitive subset of `{2,…,9}` lies in one of the six maximal antichains. -/
theorem antichain9_cover : ∀ A ∈ (Finset.Icc 2 9).powerset,
    (∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b) → ∃ M ∈ maxAntichains9, A ⊆ M := by
  set_option maxRecDepth 100000 in decide

/-- Certificate on `[a,b]`: `M_a(𝒫_9) < M_b(A)` for the five competitors. -/
def goodInterval (a b : ℚ) : Bool :=
  decide (1 ≤ a) && others9.all (fun M => decide (momentK {2, 3, 5, 7} a < momentK M b))

def chainOK : List ℚ → Bool
  | a :: b :: t => goodInterval a b && chainOK (b :: t)
  | _ => true

theorem goodInterval_spec {a b : ℚ} (h : goodInterval a b = true) {k : ℝ} (hak : (a : ℝ) ≤ k)
    (hkb : k ≤ b) : ∀ M ∈ others9, Mk k 1 {2, 3, 5, 7} < Mk k 1 M := by
  simp only [goodInterval, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨ha1, hM⟩ := h
  intro M hMmem
  have hlt := hM M hMmem
  have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hb1q : (1 : ℚ) ≤ b := by exact_mod_cast ha1'.trans (hak.trans hkb)
  calc Mk k 1 {2, 3, 5, 7} ≤ Mk a 1 {2, 3, 5, 7} := Mk_one_antitone ha1' hak _
    _ = (momentK {2, 3, 5, 7} a : ℝ) := (momentK_cast ha1 _).symm
    _ < (momentK M b : ℝ) := by exact_mod_cast hlt
    _ = Mk b 1 M := momentK_cast hb1q _
    _ ≤ Mk k 1 M := Mk_one_antitone (ha1'.trans hak) hkb _

theorem chain_cover {Q : ℝ → Prop}
    (hgood : ∀ a b : ℚ, goodInterval a b = true → ∀ k : ℝ, (a : ℝ) ≤ k → k ≤ b → Q k) :
    ∀ (l : List ℚ) (a z : ℚ), chainOK l = true → l.head? = some a → l.getLast? = some z →
      ∀ k : ℝ, (a : ℝ) ≤ k → k ≤ z → Q k ∨ k = a := by
  intro l
  induction l with
  | nil => intro a z _ h; simp at h
  | cons x t ih =>
    intro a z hch hh hl k hak hkz
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      right
      exact le_antisymm hkz hak
    | cons y t' =>
      simp only [chainOK, Bool.and_eq_true] at hch
      by_cases hky : k ≤ (y : ℝ)
      · exact Or.inl (hgood x y hch.1 k hak hky)
      · push Not at hky
        rw [List.getLast?_cons_cons] at hl
        rcases ih y z hch.2 rfl hl k hky.le hkz with h | h
        · exact Or.inl h
        · exact absurd h (ne_of_gt hky)

/-- Breakpoints `2 = x₀ < x₁ < ⋯ < x₁₂₄ = 125.84` (generated by a greedy exact
rational search). -/
def breaks9 : List ℚ := [
  (2 : ℚ), (9/4 : ℚ), (11/4 : ℚ), (13/4 : ℚ), (15/4 : ℚ), (17/4 : ℚ), (21/4 : ℚ),
  (25/4 : ℚ), (29/4 : ℚ), (33/4 : ℚ), (37/4 : ℚ), (45/4 : ℚ), (53/4 : ℚ), (65/4 : ℚ),
  (77/4 : ℚ), (93/4 : ℚ), (109/4 : ℚ), (129/4 : ℚ), (153/4 : ℚ), (177/4 : ℚ), (205/4 : ℚ),
  (233/4 : ℚ), (257/4 : ℚ), (281/4 : ℚ), (305/4 : ℚ), (325/4 : ℚ), (345/4 : ℚ), (365/4 : ℚ),
  (381/4 : ℚ), (397/4 : ℚ), (409/4 : ℚ), (421/4 : ℚ), (429/4 : ℚ), (437/4 : ℚ), (445/4 : ℚ),
  (453/4 : ℚ), (457/4 : ℚ), (461/4 : ℚ), (465/4 : ℚ), (469/4 : ℚ), (473/4 : ℚ), (477/4 : ℚ),
  (479/4 : ℚ), (481/4 : ℚ), (483/4 : ℚ), (485/4 : ℚ), (487/4 : ℚ), (489/4 : ℚ), (491/4 : ℚ),
  (123/1 : ℚ), (493/4 : ℚ), (247/2 : ℚ), (495/4 : ℚ), (124/1 : ℚ), (497/4 : ℚ), (995/8 : ℚ),
  (249/2 : ℚ), (997/8 : ℚ), (499/4 : ℚ), (999/8 : ℚ), (125/1 : ℚ), (1001/8 : ℚ),
  (2003/16 : ℚ), (501/4 : ℚ), (2005/16 : ℚ), (1003/8 : ℚ), (2007/16 : ℚ), (4015/32 : ℚ),
  (251/2 : ℚ), (4017/32 : ℚ), (2009/16 : ℚ), (4019/32 : ℚ), (1005/8 : ℚ), (4021/32 : ℚ),
  (8043/64 : ℚ), (2011/16 : ℚ), (8045/64 : ℚ), (4023/32 : ℚ), (8047/64 : ℚ), (503/4 : ℚ),
  (16097/128 : ℚ), (8049/64 : ℚ), (16099/128 : ℚ), (4025/32 : ℚ), (16101/128 : ℚ),
  (8051/64 : ℚ), (32205/256 : ℚ), (16103/128 : ℚ), (32207/256 : ℚ), (2013/16 : ℚ),
  (32209/256 : ℚ), (64419/512 : ℚ), (16105/128 : ℚ), (64421/512 : ℚ), (32211/256 : ℚ),
  (64423/512 : ℚ), (8053/64 : ℚ), (128849/1024 : ℚ), (64425/512 : ℚ), (128851/1024 : ℚ),
  (32213/256 : ℚ), (128853/1024 : ℚ), (64427/512 : ℚ), (128855/1024 : ℚ), (515423/4096 : ℚ),
  (515425/4096 : ℚ), (515427/4096 : ℚ), (515429/4096 : ℚ), (515431/4096 : ℚ), (64429/512 : ℚ),
  (515433/4096 : ℚ), (257717/2048 : ℚ), (515435/4096 : ℚ), (128859/1024 : ℚ),
  (2061747/16384 : ℚ), (1030875/8192 : ℚ), (2061753/16384 : ℚ), (2061755/16384 : ℚ),
  (2061757/16384 : ℚ), (1030879/8192 : ℚ), (2061759/16384 : ℚ), (32215/256 : ℚ),
  (2061761/16384 : ℚ), (1030881/8192 : ℚ), (3146/25 : ℚ)]

theorem breaks9_ok : chainOK breaks9 = true := by native_decide

theorem breaks9_head : breaks9.head? = some 2 := rfl

theorem breaks9_last : breaks9.getLast? = some (3146 / 25) := rfl

/-- **(L4b) Certificate.**  For every real `k ∈ [1, 125.84]` the primes
`{2,3,5,7}` are the unique minimiser of `𝔼 Z_Aᵏ = Mk k 1 A` over primitive
`A ⊆ {2,…,9}`. (`k ≤ 2`: Proposition 5.1 (L2); `k ∈ [2, 125.84]`: monotonicity
in `k` plus exact rational comparisons on 124 intervals.) -/
theorem primes_minimize_Mk_N9 {k : ℝ} (hk1 : 1 ≤ k) (hk2 : k ≤ 3146 / 25) {A : Finset ℕ}
    (hA : IsPrimitiveFin A) (hAN : ∀ a ∈ A, a ≤ 9) (hne : A ≠ primesLE 9) :
    Mk k 1 (primesLE 9) < Mk k 1 A := by
  have hc : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  rcases le_or_gt k 2 with hk2' | hk2'
  · exact Mk_primesLE_lt hk1 hk2' hA hAN hne hc
  have hP : primesLE 9 = {2, 3, 5, 7} := by decide
  have hQ : ∀ M ∈ others9, Mk k 1 {2, 3, 5, 7} < Mk k 1 M := by
    rcases chain_cover (fun a b h k hak hkb => goodInterval_spec h hak hkb) breaks9 2
        (3146 / 25) breaks9_ok breaks9_head breaks9_last k (by push_cast; linarith)
        (by push_cast; linarith) with h | h
    · exact h
    · push_cast at h
      linarith
  have hAmem : A ∈ (Finset.Icc 2 9).powerset :=
    Finset.mem_powerset.mpr (fun a ha => Finset.mem_Icc.mpr ⟨hA.1 a ha, hAN a ha⟩)
  obtain ⟨M, hM, hAM⟩ := antichain9_cover A hAmem (fun a ha b hb hab => hA.2 a ha b hb hab)
  rw [hP] at hne ⊢
  simp only [maxAntichains9, List.mem_cons] at hM
  rcases hM with rfl | hM
  · obtain ⟨q, hqP, hqA⟩ : ∃ q ∈ ({2, 3, 5, 7} : Finset ℕ), q ∉ A := by
      by_contra h
      push Not at h
      exact hne (Finset.Subset.antisymm hAM h)
    calc Mk k 1 {2, 3, 5, 7} ≤ Mk k 1 (insert q A) :=
          Mk_antitone hk1 ⟨zero_le_one, le_rfl⟩ (Finset.insert_subset hqP hAM)
      _ < Mk k 1 A := Mk_insert_lt hqA (fun n hn => (hA.1 n hn).trans' (by norm_num)) hk1 hc
  · exact (hQ M hM).trans_le (Mk_antitone hk1 ⟨zero_le_one, le_rfl⟩ hAM)

end RntPaper
