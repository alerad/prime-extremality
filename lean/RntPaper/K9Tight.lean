import RntPaper.K9Enum

/-!
# The tight case `A₉ = {4,5,6,7,9}` and the constant `k₉`

`fA9 k = ∫₀¹ u^{k-1} (P_{A₉}(u) - P_{2,3,5,7}(u)) du`, so that
`𝔼 Z_{A₉}^k - 𝔼 Z_{𝒫₉}^k = k · fA9 k`. The difference `P_{A₉} - P_{𝒫₉}` changes sign once on
`(0,1)` (exact certificate), so by variation diminishing `fA9` has exactly one zero on
`[1, ∞)`, the constant `k₉ ∈ (125.84, 125.85)`; `fA9 > 0` on `[1, k₉)` and `fA9 < 0` on
`(k₉, ∞)`.
-/

namespace RntPaper.K9

open MeasureTheory intervalIntegral Set CP QProduct

/-! ## Real-exponent moments of a polynomial -/

/-- `∑ cᵢ/(K+i)` for a real `K`. -/
noncomputable def intR : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: q, K => c / K + intR q (K + 1)

theorem integral_eq_intR (p : List ℚ) {K : ℝ} (hK : 0 < K) :
    ∫ u in (0 : ℝ)..1, u ^ (K - 1) * ev p u = intR p K := by
  induction p generalizing K with
  | nil => simp [intR]
  | cons c p ih =>
    have hK1 : 0 < K + 1 := by linarith
    have hcongr : (∫ u in (0 : ℝ)..1, u ^ (K - 1) * ev (c :: p) u)
        = ∫ u in (0 : ℝ)..1, ((c : ℝ) * u ^ (K - 1) + u ^ (K + 1 - 1) * ev p u) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with u hu
      rw [uIoc_of_le zero_le_one] at hu
      simp only [ev_cons]
      rw [show K + 1 - 1 = (K - 1) + 1 by ring, Real.rpow_add_one hu.1.ne']
      ring
    rw [hcongr, intervalIntegral.integral_add ((intervalIntegral.intervalIntegrable_rpow'
      (by linarith)).const_mul _) (intervalIntegrable_rpow_mul_ev hK1 p 0 1)]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), ih hK1]
    rw [show K - 1 + 1 = K by ring, Real.zero_rpow hK.ne', Real.one_rpow, sub_zero]
    simp only [intR]
    ring

theorem continuousOn_intR (p : List ℚ) : ContinuousOn (intR p) (Ioi 0) := by
  induction p with
  | nil => exact continuousOn_const
  | cons c p ih =>
    have h1 : ContinuousOn (fun K : ℝ => (c : ℝ) / K) (Ioi 0) :=
      continuousOn_const.div continuousOn_id fun x hx => (ne_of_gt hx)
    have h2 : ContinuousOn (fun K : ℝ => intR p (K + 1)) (Ioi 0) :=
      ih.comp (continuousOn_id.add continuousOn_const) fun x hx => by
        simp only [mem_Ioi] at hx ⊢; linarith
    exact h1.add h2

theorem intR_cast (p : List ℚ) (K : ℚ) : intR p K = intUnit p K := by
  induction p generalizing K with
  | nil => simp [intR, intUnit]
  | cons c p ih =>
    simp only [intR, intUnit]
    rw [show ((K : ℝ) + 1) = ((K + 1 : ℚ) : ℝ) by push_cast; ring, ih]
    push_cast; ring

/-! ## A sign-change certificate without integrand -/

/-- `D = v^a (1-v)^b h` with `h` changing sign once (bracket verified). -/
def signCheck (n : ℕ) (D : List ℚ) : Bool :=
  let a := (stripA D).1
  let D1 := (stripA D).2
  let b := (stripB 200 D1).1
  let h := (stripB 200 D1).2
  decide (trim (factorPoly a b h) = trim D) &&
    match findCross n h with
    | some (lo, hi) => crossOK n h lo hi
    | none => false

theorem signCheck_sound {n : ℕ} {D : List ℚ} (h : signCheck n D = true) :
    ∃ x₀ ∈ Ioo (0 : ℝ) 1, (∀ u ∈ Ioo 0 x₀, 0 < ev D u) ∧ (∀ u ∈ Icc x₀ 1, ev D u ≤ 0) := by
  simp only [signCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hfac, hsign⟩ := h
  set a := (stripA D).1
  set b := (stripB 200 (stripA D).2).1
  set hh := (stripB 200 (stripA D).2).2
  have hD : ∀ v : ℝ, ev D v = v ^ a * ((1 - v) ^ b * ev hh v) := by
    intro v
    rw [← ev_trim D, ← hfac, ev_trim, ev_factorPoly]
  cases hfc : findCross n hh with
  | none => rw [hfc] at hsign; simp at hsign
  | some lohi =>
    obtain ⟨lo, hi⟩ := lohi
    rw [hfc] at hsign
    obtain ⟨x₀, hx₀, hz, hpos, hneg⟩ := crossOK_sound hsign
    refine ⟨x₀, hx₀, fun u hu => ?_, fun u hu => ?_⟩
    · rw [hD]
      have h1 := hpos u ⟨hu.1.le, hu.2⟩
      have h2 : 0 < u ^ a * (1 - u) ^ b :=
        mul_pos (pow_pos hu.1 _) (pow_pos (by linarith [hu.2, hx₀.2]) _)
      have : u ^ a * ((1 - u) ^ b * ev hh u) = (u ^ a * (1 - u) ^ b) * ev hh u := by ring
      rw [this]; exact mul_pos h2 h1
    · have hu0 : 0 ≤ u := hx₀.1.le.trans hu.1
      have hh0 : ev hh u ≤ 0 := by
        rcases eq_or_lt_of_le hu.1 with he | hlt
        · rw [← he, hz]
        · exact (hneg u ⟨hlt, hu.2⟩).le
      rw [hD]
      have : 0 ≤ u ^ a * (1 - u) ^ b := mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith [hu.2]) _)
      have e : u ^ a * ((1 - u) ^ b * ev hh u) = (u ^ a * (1 - u) ^ b) * ev hh u := by ring
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos this hh0

/-! ## The tight case -/

/-- `P_{A₉} - P_{2,3,5,7}` as a polynomial. -/
def DA9 : List ℚ := mergedD A9

theorem signA9 : signCheckZ fuel DA9 = true := by native_decide

theorem intA9_lo : 0 < intUnit DA9 (12584 / 100) := by native_decide
theorem intA9_hi : intUnit DA9 (12585 / 100) < 0 := by native_decide

def A9f : Finset ℕ := {4, 5, 6, 7, 9}
def R4f : Finset ℕ := {2, 3, 5, 7}

theorem ev_DA9 (u : ℝ) : ev DA9 u = qProd A9f u - qProd R4f u := by
  simp [DA9, mergedD, A9, R4, A9f, R4f, qProd]

/-- `fA9 k = ∫₀¹ u^{k-1} (P_{A₉} - P_{2,3,5,7})`. -/
noncomputable def fA9 (k : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, u ^ (k - 1) * (qProd A9f u - qProd R4f u)

theorem fA9_eq (k : ℝ) (hk : 0 < k) : fA9 k = intR DA9 k := by
  rw [← integral_eq_intR DA9 hk, fA9]
  simp only [ev_DA9]

theorem exists_k9 : ∃ k ∈ Ioo (12584 / 100 : ℝ) (12585 / 100), fA9 k = 0 := by
  have hc : ContinuousOn (intR DA9) (Icc (12584 / 100 : ℝ) (12585 / 100)) :=
    (continuousOn_intR DA9).mono fun x hx => by simp only [mem_Ioi]; linarith [hx.1]
  have hlo : 0 < intR DA9 (12584 / 100) := by
    have := intR_cast DA9 (12584 / 100); push_cast at this; rw [this]; exact_mod_cast intA9_lo
  have hhi : intR DA9 (12585 / 100) < 0 := by
    have := intR_cast DA9 (12585 / 100); push_cast at this; rw [this]; exact_mod_cast intA9_hi
  obtain ⟨k, hk, hz⟩ := intermediate_value_Ioo' (by norm_num) hc ⟨hhi, hlo⟩
  exact ⟨k, hk, by rw [fA9_eq k (by linarith [hk.1]), hz]⟩

/-- **The constant `k₉`**: the root of `𝔼 Z_{A₉}^k = 𝔼 Z_{2,3,5,7}^k` in `(125.84, 125.85)`. -/
noncomputable def k9 : ℝ := Classical.choose exists_k9

theorem k9_mem : k9 ∈ Ioo (12584 / 100 : ℝ) (12585 / 100) := (Classical.choose_spec exists_k9).1
theorem fA9_k9 : fA9 k9 = 0 := (Classical.choose_spec exists_k9).2

theorem one_lt_k9 : 1 < k9 := by linarith [k9_mem.1]
theorem k9_lt_126 : k9 < 126 := by linarith [k9_mem.2]

theorem gA9_cont : Continuous fun u => qProd A9f u - qProd R4f u := by
  have : (fun u => qProd A9f u - qProd R4f u) = ev DA9 := funext fun u => (ev_DA9 u).symm
  rw [this]; exact continuous_ev _

theorem signA9' : ∃ x₀ ∈ Ioo (0 : ℝ) 1, (∀ u ∈ Ioo 0 x₀, 0 < qProd A9f u - qProd R4f u) ∧
    (∀ u ∈ Icc x₀ 1, qProd A9f u - qProd R4f u ≤ 0) := by
  obtain ⟨x₀, hx₀, h1, h2⟩ := signCheckZ_sound signA9
  exact ⟨x₀, hx₀, fun u hu => (ev_DA9 u) ▸ h1 u hu, fun u hu => (ev_DA9 u) ▸ h2 u hu⟩

theorem fA9_pos {k : ℝ} (hk : 1 ≤ k) (hlt : k < k9) : 0 < fA9 k := by
  obtain ⟨x₀, hx₀, h1, h2⟩ := signA9'
  have := (vd_compare gA9_cont hx₀ h1 h2 hk hlt.le).2 hlt
  have h0 : fA9 k9 = 0 := fA9_k9
  unfold fA9 at h0 ⊢
  rw [h0, mul_zero] at this
  exact this

theorem fA9_neg {k : ℝ} (hlt : k9 < k) : fA9 k < 0 := by
  obtain ⟨x₀, hx₀, h1, h2⟩ := signA9'
  have := (vd_compare gA9_cont hx₀ h1 h2 one_lt_k9.le hlt.le).2 hlt
  have h0 : fA9 k9 = 0 := fA9_k9
  unfold fA9 at h0 this ⊢
  rw [h0] at this
  have hx : 0 < x₀ ^ (k9 - k) := Real.rpow_pos_of_pos hx₀.1 _
  by_contra hcon
  push Not at hcon
  linarith [mul_nonneg hx.le hcon]

/-- `k₉` is the only zero of `fA9` on `[1, ∞)`. -/
theorem fA9_eq_zero_iff {k : ℝ} (hk : 1 ≤ k) : fA9 k = 0 ↔ k = k9 := by
  constructor
  · intro h
    rcases lt_trichotomy k k9 with hlt | heq | hgt
    · exact absurd h (fA9_pos hk hlt).ne'
    · exact heq
    · exact absurd h (fA9_neg hgt).ne
  · rintro rfl; exact fA9_k9

/-- The running integrals for `A₉`: `≥ 0` up to `k₉`, `> 0` below it. -/
theorem runA9 {k : ℝ} (hk : 1 ≤ k) (hkk : k ≤ k9) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    0 ≤ ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd A9f u - qProd R4f u) ∧
      (k < k9 → 0 < ∫ u in (0 : ℝ)..y, u ^ (k - 1) * (qProd A9f u - qProd R4f u)) := by
  obtain ⟨x₀, hx₀, h1, h2⟩ := signA9'
  have hI : 0 ≤ ∫ u in (0 : ℝ)..1, u ^ (k9 - 1) * (qProd A9f u - qProd R4f u) := by
    have := fA9_k9; unfold fA9 at this; rw [this]
  have := runNonneg_of_signChange gA9_cont hx₀ h1 h2 hI hk hkk hy
  exact ⟨this.1, fun hlt => this.2 (Or.inl hlt)⟩

end RntPaper.K9
