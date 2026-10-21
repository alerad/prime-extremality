import RntPaper.UniversalInequality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Transport and strict compression (paper §3)

Ports of the productinvariants engine, generalised from the fixed interval
`[0,1]` to `[0,c]`:

* `integral_weight_mul_pos_upto`  ← `integral_weight_mul_pos` (Lemma 3.1/3.3,
  C¹ weight; enough for finite `B`, and for infinite `B` after the truncation
  argument described in the plan),
* `running_pos_comp_pow_pos`      ← `running_pos_comp_pow_pos` (Corollary 3.2),
* `Fc_blockStep_diff`             ← `phaseIntegral_blockStep_diff` (identity (1.2)),
* `block_exchange_lt`             ← `phaseIntegral_substStep_lt` (Proposition 3.4).

Infinite exponent sets (paper Lemma 3.3 / Proposition 3.4 for arbitrary `B`, `T`):

* `running_pos_comp_pow_pos_set` — Corollary 3.2 for arbitrary `T`, via the
  continuous envelope `blockEH = H − (1 − v) ≤ E_T`,
* `qProdSet_union`, `qProdSet_insert`, `qProdSet_image_mul`,
  `qProdSet_blockStep_diff` — block-step product algebra for `tprod`s,
* `kappa_le_integral_qProdSet_mul` — the uniform bound `κ_c` across the
  truncations `B_N` (dominated convergence, no Stieltjes integration by parts),
* `block_exchange_lt_set` — Proposition 3.4 for arbitrary sets.
-/

namespace RntPaper

open QProduct MeasureTheory intervalIntegral Set

/-- **Weighted running positivity on `[0,c]`** (paper Lemmas 3.1 and 3.3 with a
`C¹` weight).  `g` continuous with `∫₀ʸ g > 0` on `(0,c]`, `w ≥ 0` nonincreasing
and `C¹`; then `∫₀ᶜ w g ≥ w(c)·∫₀ᶜ g`, strictly positive if `w(c) > 0` or `w`
strictly decreases somewhere in `(0,c)`. -/
theorem integral_weight_mul_pos_upto {g w w' : ℝ → ℝ} {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1)
    (hg : Continuous g)
    (hw : ∀ x ∈ uIcc (0 : ℝ) c, HasDerivAt w (w' x) x)
    (hw'cont : Continuous w')
    (hwc : 0 ≤ w c)
    (hw'nonpos : ∀ x ∈ Icc (0 : ℝ) c, w' x ≤ 0)
    (hG : ∀ y ∈ Ioc (0 : ℝ) c, 0 < ∫ t in (0 : ℝ)..y, g t)
    (hstrict : 0 < w c ∨ ∃ x₀ ∈ Ioo (0 : ℝ) c, w' x₀ < 0) :
    0 < ∫ u in (0 : ℝ)..c, w u * g u := by
  have hc0 : 0 < c := hc.1
  have huIcc : uIcc (0 : ℝ) c = Icc 0 c := uIcc_of_le hc0.le
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t with hGdef
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hGderiv : ∀ x ∈ uIcc (0 : ℝ) c, HasDerivAt G (g x) x := by
    intro x _hx
    exact intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 x)
      (hg.stronglyMeasurableAtFilter _ _)
      hg.continuousAt
  have hGcont : ContinuousOn G (Icc (0 : ℝ) c) := by
    intro x hx
    exact ((hGderiv x (by rw [huIcc]; exact hx)).continuousAt).continuousWithinAt
  have hGnonneg : ∀ y ∈ Icc (0 : ℝ) c, 0 ≤ G y := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · simp [hGdef, ← h]
    · exact (hG y ⟨h, hy.2⟩).le
  have hgint : IntervalIntegrable g volume 0 c := hg.intervalIntegrable 0 c
  have hw'int : IntervalIntegrable w' volume 0 c := hw'cont.intervalIntegrable 0 c
  have hIBP :
      (∫ u in (0 : ℝ)..c, w u * g u) =
        w c * G c - w 0 * G 0 - ∫ u in (0 : ℝ)..c, w' u * G u := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := w) (v := G) (u' := w') (v' := g) hw hGderiv hw'int hgint
    simpa using h
  rw [hIBP, hG0]
  have hbdry : 0 ≤ w c * G c :=
    mul_nonneg hwc (hGnonneg c ⟨hc0.le, le_rfl⟩)
  -- Tail is `≤ 0` in all cases.
  have htail_int : IntervalIntegrable (fun u => w' u * G u) volume 0 c :=
    hw'int.mul_continuousOn (by rw [huIcc]; exact hGcont)
  have htail : (∫ u in (0 : ℝ)..c, w' u * G u) ≤ 0 := by
    have hle : (∫ u in (0 : ℝ)..c, w' u * G u) ≤ ∫ _ in (0 : ℝ)..c, (0 : ℝ) := by
      apply intervalIntegral.integral_mono_on hc0.le htail_int
        _root_.intervalIntegrable_const
      intro x hx
      exact mul_nonpos_of_nonpos_of_nonneg (hw'nonpos x hx) (hGnonneg x hx)
    simpa using hle
  rcases hstrict with hwc_pos | ⟨x₀, hx₀, hw'x₀⟩
  · have hbdry' : 0 < w c * G c := mul_pos hwc_pos (hG c ⟨hc0, le_rfl⟩)
    simp only [mul_zero, sub_zero]
    linarith
  · have htail' : (∫ u in (0 : ℝ)..c, w' u * G u) < 0 := by
      have hlt : (∫ u in (0 : ℝ)..c, w' u * G u) < ∫ _ in (0 : ℝ)..c, (0 : ℝ) := by
        apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt hc0
          ((hw'cont.continuousOn).mul hGcont) continuousOn_const
        · intro x hx
          have hx' : x ∈ Icc (0 : ℝ) c := Ioc_subset_Icc_self hx
          exact mul_nonpos_of_nonpos_of_nonneg (hw'nonpos x hx') (hGnonneg x hx')
        · refine ⟨x₀, ⟨hx₀.1.le, hx₀.2.le⟩, ?_⟩
          have hGx₀ : 0 < G x₀ := hG x₀ ⟨hx₀.1, hx₀.2.le⟩
          exact mul_neg_of_neg_of_pos hw'x₀ hGx₀
      simpa using hlt
    simp only [mul_zero, sub_zero]
    linarith

/-- Derivative of the finite product weight (port of `phaseProduct'`). -/
noncomputable def qProd' (B : Finset ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ B, (∏ j ∈ B.erase i, (1 - u ^ j)) * (-(i * u ^ (i - 1)))

/-- `1 - u^n` has derivative `-(n·u^{n-1})`. -/
theorem hasDerivAt_one_sub_pow (n : ℕ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => 1 - u ^ n) (-((n : ℝ) * u ^ (n - 1))) u := by
  have h := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow n u)
  rw [zero_sub] at h
  exact h

theorem hasDerivAt_qProd (B : Finset ℕ) (u : ℝ) :
    HasDerivAt (qProd B) (qProd' B u) u := by
  classical
  have h :
      HasDerivAt (fun u : ℝ => ∏ i ∈ B, (1 - u ^ i))
        (∑ i ∈ B, (∏ j ∈ B.erase i, (1 - u ^ j)) • (-((i : ℝ) * u ^ (i - 1)))) u :=
    HasDerivAt.fun_finsetProd (fun i _hi => hasDerivAt_one_sub_pow i u)
  unfold qProd qProd'
  simpa [smul_eq_mul] using h

theorem qProd'_nonpos (B : Finset ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    qProd' B u ≤ 0 := by
  classical
  unfold qProd'
  apply Finset.sum_nonpos
  intro i _hi
  have hprod : 0 ≤ ∏ j ∈ B.erase i, (1 - u ^ j) :=
    Finset.prod_nonneg (fun j _hj => sub_nonneg.mpr (pow_le_one₀ hu.1 hu.2))
  have hpow : 0 ≤ (i : ℝ) * u ^ (i - 1) :=
    mul_nonneg (by positivity) (pow_nonneg hu.1 _)
  have : 0 ≤ (∏ j ∈ B.erase i, (1 - u ^ j)) * ((i : ℝ) * u ^ (i - 1)) :=
    mul_nonneg hprod hpow
  linarith [this]

theorem continuous_qProd' (B : Finset ℕ) : Continuous (qProd' B) := by
  classical
  unfold qProd'
  apply continuous_finsetSum
  intro i _hi
  apply Continuous.mul
  · exact continuous_finsetProd _ (fun j _hj => continuous_const.sub (continuous_pow j))
  · exact (continuous_const.mul (continuous_pow _)).neg

/-- On `(0,1)` every factor `1 - uⁿ` with `n ≥ 1` is strictly positive. -/
theorem one_sub_pow_pos_of_mem_Ioo {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    {n : ℕ} (hn : 1 ≤ n) : 0 < 1 - u ^ n := by
  have hlt : u ^ n < 1 := pow_lt_one₀ hu.1.le hu.2 (Nat.one_le_iff_ne_zero.mp hn)
  linarith

/-- If every exponent of `S` is `≥ 1`, the product weight is strictly positive
on `(0,1)`. -/
theorem qProd_pos_of_mem_Ioo {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < qProd S u := by
  unfold qProd
  exact Finset.prod_pos (fun n hn => one_sub_pow_pos_of_mem_Ioo hu (hS n hn))

theorem qProd'_neg_of_nonempty {B : Finset ℕ} (hB : B.Nonempty) (hB1 : ∀ n ∈ B, 1 ≤ n)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : qProd' B u < 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hB
  unfold qProd'
  -- Every summand is `≤ 0`, and the summand at `i₀` is `< 0`.
  have hterm_nonpos : ∀ i ∈ B,
      (∏ j ∈ B.erase i, (1 - u ^ j)) * (-((i : ℝ) * u ^ (i - 1))) ≤ 0 := by
    intro i _hi
    have hprod : 0 ≤ ∏ j ∈ B.erase i, (1 - u ^ j) :=
      Finset.prod_nonneg (fun j _hj => sub_nonneg.mpr (pow_le_one₀ hu.1.le hu.2.le))
    have hpow : 0 ≤ (i : ℝ) * u ^ (i - 1) :=
      mul_nonneg (by positivity) (pow_nonneg hu.1.le _)
    have := mul_nonneg hprod hpow
    linarith
  have hterm_neg :
      (∏ j ∈ B.erase i₀, (1 - u ^ j)) * (-((i₀ : ℝ) * u ^ (i₀ - 1))) < 0 := by
    have hprod : 0 < ∏ j ∈ B.erase i₀, (1 - u ^ j) :=
      Finset.prod_pos (fun j hj =>
        one_sub_pow_pos_of_mem_Ioo hu (hB1 j (Finset.mem_of_mem_erase hj)))
    have hi₀1 : 1 ≤ i₀ := hB1 i₀ hi₀
    have hpow : 0 < (i₀ : ℝ) * u ^ (i₀ - 1) := by
      have : (0 : ℝ) < (i₀ : ℝ) := by exact_mod_cast hi₀1
      exact mul_pos this (pow_pos hu.1 _)
    have := mul_pos hprod hpow
    linarith
  have := Finset.sum_lt_sum (g := fun _ => (0 : ℝ)) hterm_nonpos ⟨i₀, hi₀, hterm_neg⟩
  simpa using this

theorem continuous_blockE (T : Finset ℕ) : Continuous (blockE T) := by
  unfold blockE
  exact (qProd_continuous T).sub (continuous_const.sub continuous_id)

/-! ## Running positivity under the power substitution `u ↦ uᵖ`

The engine below is stated for an arbitrary continuous integrand `e` with
strictly positive running integrals on `(0,1]`, so that it applies verbatim to
`blockE T` (finite `T`) and, once continuity of `blockESet T` is available, to
`blockESet T`.  It is a port of productinvariants `PowerSubstitution.lean`.

Strategy: with `G(d) = ∫₀ᵈ e` and `A(u) = G(uᵖ)` (so `A' = e(uᵖ)·p·u^{p-1}`),
integrate by parts on `[ε,c]` against `φ(u) = u^{1-p}/p`:
`∫_ε^c e(uᵖ) = [φA]_ε^c − ∫_ε^c φ'A ≥ φ(c)A(c) − φ(ε)A(ε)`, and let `ε ↓ 0`. -/

section PowerSubstitution

variable {e : ℝ → ℝ}

/-- The running integral `∫₀ᵈ e`. -/
noncomputable def runInt (e : ℝ → ℝ) (d : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..d, e v

theorem hasDerivAt_runInt (he : Continuous e) (d : ℝ) :
    HasDerivAt (runInt e) (e d) d := by
  unfold runInt
  exact intervalIntegral.integral_hasDerivAt_right
    (he.intervalIntegrable 0 d)
    (he.stronglyMeasurableAtFilter _ _)
    he.continuousAt

theorem continuous_runInt (he : Continuous e) : Continuous (runInt e) :=
  continuous_iff_continuousAt.mpr (fun d => (hasDerivAt_runInt he d).continuousAt)

@[simp] theorem runInt_zero (e : ℝ → ℝ) : runInt e 0 = 0 := by
  simp [runInt]

theorem runInt_nonneg (hrun : ∀ d ∈ Ioc (0 : ℝ) 1, 0 < ∫ v in (0 : ℝ)..d, e v)
    {d : ℝ} (hd : d ∈ Icc (0 : ℝ) 1) : 0 ≤ runInt e d := by
  rcases eq_or_lt_of_le hd.1 with h | h
  · simp [runInt, ← h]
  · exact (hrun d ⟨h, hd.2⟩).le

/-- A linear bound near `0`: `|runInt e d| ≤ M·d` on `[0,1]`. -/
theorem abs_runInt_le (he : Continuous e) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ d ∈ Icc (0 : ℝ) 1, |runInt e d| ≤ M * d := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    he.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro d hd
  have hbound : ∀ v ∈ Icc (0:ℝ) 1, |e v| ≤ max M 0 := by
    intro v hv; exact (hM v hv).trans (le_max_left _ _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := d) (C := max M 0) (f := e)
    (by
      intro v hv
      have hv' : v ∈ Icc (0:ℝ) 1 := by
        rw [uIoc_of_le hd.1] at hv
        exact ⟨hv.1.le, hv.2.trans hd.2⟩
      simpa [Real.norm_eq_abs] using hbound v hv')
  simpa [runInt, Real.norm_eq_abs, abs_of_nonneg hd.1] using this

/-- The singular weight `φ(u) = u^{1-p}/p`. -/
private noncomputable def jacWeight (p : ℕ) (u : ℝ) : ℝ :=
  u ^ ((1 : ℝ) - p) / p

/-- `φ'(u) = (1-p)/p · u^{-p}`. -/
private noncomputable def jacWeight' (p : ℕ) (u : ℝ) : ℝ :=
  ((1 : ℝ) - p) / p * u ^ ((-p : ℝ))

private theorem hasDerivAt_jacWeight {p : ℕ} {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (jacWeight p) (jacWeight' p u) u := by
  unfold jacWeight jacWeight'
  have hbase : HasDerivAt (fun x : ℝ => x ^ ((1 : ℝ) - p))
      (((1 : ℝ) - p) * u ^ ((1 : ℝ) - p - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu)
  have h := hbase.div_const (p : ℝ)
  have hexp : (1 : ℝ) - p - 1 = (-p : ℝ) := by ring
  rw [hexp] at h
  have : ((1 : ℝ) - p) * u ^ ((-p : ℝ)) / p
      = ((1 : ℝ) - p) / p * u ^ ((-p : ℝ)) := by ring
  rwa [this] at h

/-- Chain rule for `u ↦ runInt e (uᵖ)`. -/
private theorem hasDerivAt_runInt_pow (he : Continuous e) (p : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => runInt e (x ^ p)) (e (u ^ p) * ((p : ℝ) * u ^ (p - 1))) u := by
  have hout : HasDerivAt (runInt e) (e (u ^ p)) (u ^ p) := hasDerivAt_runInt he (u ^ p)
  have hin : HasDerivAt (fun x : ℝ => x ^ p) ((p : ℝ) * u ^ (p - 1)) u := by
    simpa using hasDerivAt_pow p u
  exact hout.comp u hin

/-- Cancellation `φ(u)·(e(uᵖ)·p·u^{p-1}) = e(uᵖ)` for `u > 0`. -/
private theorem jacWeight_mul_cancel {p : ℕ} (hp : 1 ≤ p) (e : ℝ → ℝ)
    {u : ℝ} (hu : 0 < u) :
    jacWeight p u * (e (u ^ p) * ((p : ℝ) * u ^ (p - 1))) = e (u ^ p) := by
  unfold jacWeight
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have hcast : (u : ℝ) ^ (p - 1) = u ^ ((p : ℝ) - 1) := by
    rw [← Real.rpow_natCast u (p - 1)]
    congr 1
    push_cast [Nat.cast_sub hp]
    ring
  rw [hcast]
  have hcomb : u ^ ((1 : ℝ) - p) * u ^ ((p : ℝ) - 1) = 1 := by
    rw [← Real.rpow_add hu]
    norm_num
  have hregroup :
      u ^ ((1 : ℝ) - p) / p * (e (u ^ p) * ((p : ℝ) * u ^ ((p : ℝ) - 1)))
        = e (u ^ p) * (u ^ ((1 : ℝ) - p) * u ^ ((p : ℝ) - 1)) := by
    field_simp
  rw [hregroup, hcomb, mul_one]

/-- **Boundary lower bound** (`p ≥ 2`):
`φ(c)·runInt e (cᵖ) ≤ ∫₀ᶜ e(uᵖ)`. -/
private theorem bdry_le_running_comp_pow (he : Continuous e)
    (hrun : ∀ d ∈ Ioc (0 : ℝ) 1, 0 < ∫ v in (0 : ℝ)..d, e v) {p : ℕ}
    (hp2 : 2 ≤ p) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hc0 : 0 < c) :
    jacWeight p c * runInt e (c ^ p) ≤ ∫ u in (0 : ℝ)..c, e (u ^ p) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp2
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  set g : ℝ → ℝ := fun u => e (u ^ p) with hgdef
  have hgcont : Continuous g := he.comp (continuous_pow p)
  have hstep : ∀ ε : ℝ, 0 < ε → ε < c →
      jacWeight p c * runInt e (c ^ p) - jacWeight p ε * runInt e (ε ^ p)
        ≤ ∫ u in ε..c, g u := by
    intro ε hε hεc
    have hεc' : ε ≤ c := hεc.le
    have hmem : ∀ x ∈ Set.uIcc ε c, x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hεc'] at hx
      exact ne_of_gt (lt_of_lt_of_le hε hx.1)
    have hφderiv : ∀ x ∈ Set.uIcc ε c, HasDerivAt (jacWeight p) (jacWeight' p x) x := by
      intro x hx; exact hasDerivAt_jacWeight (hmem x hx)
    have hAderiv : ∀ x ∈ Set.uIcc ε c,
        HasDerivAt (fun x : ℝ => runInt e (x ^ p)) (e (x ^ p) * ((p : ℝ) * x ^ (p - 1))) x := by
      intro x _hx; exact hasDerivAt_runInt_pow he p x
    have hφ'cont : ContinuousOn (jacWeight' p) (Set.uIcc ε c) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      left
      exact hmem x hx
    have hφ'int : IntervalIntegrable (jacWeight' p) volume ε c :=
      hφ'cont.intervalIntegrable
    have hA'int : IntervalIntegrable
        (fun x => e (x ^ p) * ((p : ℝ) * x ^ (p - 1))) volume ε c := by
      apply Continuous.intervalIntegrable
      exact hgcont.mul (continuous_const.mul (continuous_pow _))
    have hIBP :
        (∫ x in ε..c, jacWeight p x * (e (x ^ p) * ((p : ℝ) * x ^ (p - 1))))
          = jacWeight p c * runInt e (c ^ p) - jacWeight p ε * runInt e (ε ^ p)
            - ∫ x in ε..c, jacWeight' p x * runInt e (x ^ p) :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := jacWeight p) (v := fun x : ℝ => runInt e (x ^ p))
        (u' := jacWeight' p)
        (v' := fun x => e (x ^ p) * ((p : ℝ) * x ^ (p - 1)))
        hφderiv hAderiv hφ'int hA'int
    have hlhs : (∫ x in ε..c, jacWeight p x * (e (x ^ p) * ((p : ℝ) * x ^ (p - 1))))
        = ∫ x in ε..c, g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hεc'] at hx
      exact jacWeight_mul_cancel hp1 e (lt_of_lt_of_le hε hx.1)
    have htail_nonpos : (∫ x in ε..c, jacWeight' p x * runInt e (x ^ p)) ≤ 0 := by
      have hle : (∫ x in ε..c, jacWeight' p x * runInt e (x ^ p))
          ≤ ∫ _ in ε..c, (0 : ℝ) := by
        apply intervalIntegral.integral_mono_on hεc'
        · exact hφ'int.mul_continuousOn
            ((continuous_runInt he).comp (continuous_pow p)).continuousOn
        · exact _root_.intervalIntegrable_const
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
          have hxIcc : x ^ p ∈ Icc (0:ℝ) 1 := by
            refine ⟨by positivity, ?_⟩
            exact pow_le_one₀ hx0.le (le_trans hx.2 hc.2)
          have hAx : 0 ≤ runInt e (x ^ p) := runInt_nonneg hrun hxIcc
          have hφ'x : jacWeight' p x ≤ 0 := by
            unfold jacWeight'
            have h1 : ((1 : ℝ) - p) / p ≤ 0 := by
              apply div_nonpos_of_nonpos_of_nonneg
              · linarith
              · positivity
            have h2 : 0 ≤ x ^ ((-p : ℝ)) := Real.rpow_nonneg hx0.le _
            exact mul_nonpos_of_nonpos_of_nonneg h1 h2
          exact mul_nonpos_of_nonpos_of_nonneg hφ'x hAx
      simpa using hle
    rw [hlhs] at hIBP
    linarith [hIBP, htail_nonpos]
  -- Lower boundary `φ(ε)·A(ε) → 0` as `ε ↓ 0`.
  obtain ⟨M, hM0, hMbound⟩ := abs_runInt_le he
  have hφεAε_bound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |jacWeight p ε * runInt e (ε ^ p)| ≤ (M / p) * ε := by
    intro ε hε hε1
    have hεp_mem : ε ^ p ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity, pow_le_one₀ hε.le hε1⟩
    have hAbound : |runInt e (ε ^ p)| ≤ M * ε ^ p := hMbound _ hεp_mem
    have hφε : jacWeight p ε = ε ^ ((1:ℝ) - p) / p := rfl
    rw [hφε, abs_mul]
    have hφabs : |ε ^ ((1:ℝ) - p) / p| = ε ^ ((1:ℝ) - p) / p := by
      rw [abs_of_nonneg]
      have : 0 ≤ ε ^ ((1:ℝ) - p) := Real.rpow_nonneg hε.le _
      positivity
    rw [hφabs]
    calc ε ^ ((1:ℝ) - p) / p * |runInt e (ε ^ p)|
        ≤ ε ^ ((1:ℝ) - p) / p * (M * ε ^ p) := by
          apply mul_le_mul_of_nonneg_left hAbound
          have : 0 ≤ ε ^ ((1:ℝ) - p) := Real.rpow_nonneg hε.le _
          positivity
      _ = (M / p) * ε := by
          have hεpR : (ε : ℝ) ^ p = ε ^ (p : ℝ) := (Real.rpow_natCast ε p).symm
          have hmul : ε ^ ((1:ℝ) - p) * ε ^ (p : ℝ) = ε := by
            rw [← Real.rpow_add hε, show (1:ℝ) - ↑p + ↑p = (1:ℝ) by ring, Real.rpow_one]
          have hpne : (p : ℝ) ≠ 0 := by positivity
          rw [hεpR]
          field_simp
          nlinarith [hmul]
  change jacWeight p c * runInt e (c ^ p) ≤ ∫ u in (0:ℝ)..c, g u
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hgcont.intervalIntegrable a b
  have hprim0 : Filter.Tendsto (fun ε : ℝ => ∫ u in (0:ℝ)..ε, g u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hcontprim : ContinuousAt (fun ε : ℝ => ∫ u in (0:ℝ)..ε, g u) 0 :=
      (intervalIntegral.integral_hasDerivAt_right (hgint 0 0)
        (hgcont.stronglyMeasurableAtFilter _ _) hgcont.continuousAt).continuousAt
    have : Filter.Tendsto (fun ε : ℝ => ∫ u in (0:ℝ)..ε, g u)
        (nhds 0) (nhds (∫ u in (0:ℝ)..(0:ℝ), g u)) := hcontprim.tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hφεAε_tendsto : Filter.Tendsto (fun ε : ℝ => jacWeight p ε * runInt e (ε ^ p))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro δ hδ
    refine ⟨min 1 (δ / (M / p + 1)), by positivity, ?_⟩
    intro ε hεIoi hεlt
    have hε : 0 < ε := hεIoi
    have hεlt' : ε < min 1 (δ / (M / p + 1)) := by
      rwa [Real.dist_eq, sub_zero, abs_of_pos hε] at hεlt
    have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hεlt' (min_le_left _ _))
    have hb := hφεAε_bound ε hε hε1
    rw [Real.dist_eq, sub_zero]
    have hεlt2 : ε < δ / (M / p + 1) :=
      lt_of_lt_of_le hεlt' (min_le_right _ _)
    have hMp1 : 0 < M / p + 1 := by positivity
    calc |jacWeight p ε * runInt e (ε ^ p)| ≤ (M / p) * ε := hb
      _ ≤ (M / p + 1) * ε := by nlinarith [hε.le]
      _ < (M / p + 1) * (δ / (M / p + 1)) := by
          apply mul_lt_mul_of_pos_left hεlt2 hMp1
      _ = δ := by field_simp
  have hlimit : Filter.Tendsto
      (fun ε : ℝ => jacWeight p c * runInt e (c ^ p)
        - jacWeight p ε * runInt e (ε ^ p) + ∫ u in (0:ℝ)..ε, g u)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (jacWeight p c * runInt e (c ^ p))) := by
    have := ((tendsto_const_nhds (x := jacWeight p c * runInt e (c ^ p))).sub
      hφεAε_tendsto).add hprim0
    simpa using this
  have hev : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      jacWeight p c * runInt e (c ^ p) - jacWeight p ε * runInt e (ε ^ p)
        + ∫ u in (0:ℝ)..ε, g u ≤ ∫ u in (0:ℝ)..c, g u := by
    have hIoo : Set.Ioo (0:ℝ) c ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT hc0
    filter_upwards [hIoo] with ε hε
    have hsplit : (∫ u in (0:ℝ)..c, g u)
        = (∫ u in (0:ℝ)..ε, g u) + ∫ u in ε..c, g u :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hgint 0 ε) (hgint ε c)).symm
    have hs := hstep ε hε.1 hε.2
    rw [hsplit]
    linarith [hs]
  exact le_of_tendsto hlimit hev

/-- **Strict running positivity under `u ↦ uᵖ`, abstract form.**  If `e` is
continuous with `∫₀ᵈ e > 0` for all `d ∈ (0,1]`, then `∫₀ᶜ e(uᵖ) > 0` for all
`c ∈ (0,1]` and `p ≥ 1`. -/
theorem running_pos_comp_pow_pos_of (he : Continuous e)
    (hrun : ∀ d ∈ Ioc (0 : ℝ) 1, 0 < ∫ v in (0 : ℝ)..d, e v) {p : ℕ}
    (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..c, e (u ^ p) := by
  have hc0 : 0 < c := hc.1
  have hc1 : c ≤ 1 := hc.2
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · interval_cases p
    simpa using hrun c hc
  · refine lt_of_lt_of_le ?_ (bdry_le_running_comp_pow he hrun hp2 ⟨hc0.le, hc1⟩ hc0)
    have hcp_mem : c ^ p ∈ Ioc (0 : ℝ) 1 :=
      ⟨by positivity, pow_le_one₀ hc0.le hc1⟩
    have hAc_pos : 0 < runInt e (c ^ p) := hrun _ hcp_mem
    have hφc_pos : 0 < jacWeight p c := by
      unfold jacWeight
      have : 0 < c ^ ((1 : ℝ) - p) := Real.rpow_pos_of_pos hc0 _
      positivity
    exact mul_pos hφc_pos hAc_pos

end PowerSubstitution

/-- **Corollary 3.2 (power substitution), finite `T`.**
Port of productinvariants `running_pos_comp_pow_pos`. -/
theorem running_pos_comp_pow_pos {T : Finset ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {p : ℕ}
    (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..c, blockE T (u ^ p) :=
  running_pos_comp_pow_pos_of (continuous_blockE T)
    (fun _d hd => blockE_partial_pos hT hd) hp hc

/-! ## The continuous lower envelope `E_H(v) = H(v) - (1 - v)`

`blockESet T` need not be continuous, but it dominates the *continuous*
function `E_H(v) = H(v) - (1 - v)` on `[0,1]` (paper (2.1)), whose running
integrals are positive by `running_pos_Hfun`.  All strictness below is obtained
through `E_H`, so no continuity of infinite products is ever required. -/

/-- Clamp to `[0,1]`. -/
private noncomputable def clamp01 (v : ℝ) : ℝ := max 0 (min v 1)

private theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

private theorem clamp01_mem (v : ℝ) : clamp01 v ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

private theorem clamp01_of_mem {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : clamp01 v = v := by
  unfold clamp01
  rw [min_eq_left hv.2, max_eq_right hv.1]

/-- A continuous extension of `H` from `[0,1]` to `ℝ` (constant outside). -/
noncomputable def HfunExt (v : ℝ) : ℝ := Hfun (clamp01 v)

theorem continuous_HfunExt : Continuous HfunExt :=
  Hfun_continuousOn.comp_continuous continuous_clamp01 clamp01_mem

theorem HfunExt_of_mem {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : HfunExt v = Hfun v := by
  unfold HfunExt
  rw [clamp01_of_mem hv]

/-- `E_H(v) = H(v) - (1 - v)`, extended continuously to `ℝ`. -/
noncomputable def blockEH (v : ℝ) : ℝ := HfunExt v - (1 - v)

theorem continuous_blockEH : Continuous blockEH :=
  continuous_HfunExt.sub (continuous_const.sub continuous_id)

/-- `∫₀ᵈ E_H > 0` on `(0,1]` (restatement of `running_pos_Hfun`). -/
theorem blockEH_partial_pos {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ v in (0 : ℝ)..d, blockEH v := by
  have hcongr : (∫ v in (0 : ℝ)..d, blockEH v) = ∫ v in (0 : ℝ)..d, (Hfun v - (1 - v)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hd.1.le] at hv
    simp only [blockEH, HfunExt_of_mem ⟨hv.1, hv.2.trans hd.2⟩]
  rw [hcongr, integral_sub (Hfun_intervalIntegrable ⟨le_rfl, by norm_num⟩ ⟨hd.1.le, hd.2⟩)
    (intervalIntegrable_const.sub intervalIntegrable_id),
    integral_sub intervalIntegrable_const intervalIntegrable_id,
    intervalIntegral.integral_const, integral_id]
  have := running_pos_Hfun hd
  simp only [sub_zero, smul_eq_mul, mul_one]
  linarith

/-- `H ≤ P_T` on the closed interval `[0,1]` for `T ⊆ {2,3,…}`. -/
theorem Hfun_le_qProdSet_Icc {T : Set ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : Hfun v ≤ qProdSet T v := by
  rcases eq_or_lt_of_le hv.2 with h | h
  · rw [h, Hfun_one]
    exact qProdSet_nonneg T ⟨zero_le_one, le_rfl⟩
  · exact Hfun_le_qProdSet_of_lt (fun n hn => hT n hn) hv.1 h

/-- `E_H ≤ E_T` on `[0,1]` for every `T ⊆ {2,3,…}`. -/
theorem blockEH_le_blockESet {T : Set ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : blockEH v ≤ blockESet T v := by
  unfold blockEH blockESet
  rw [HfunExt_of_mem hv]
  linarith [Hfun_le_qProdSet_Icc hT hv]

/-- `∫₀ᶜ E_H(uᵖ) > 0` for `c ∈ (0,1]`, `p ≥ 1`. -/
theorem running_pos_blockEH_comp_pow {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..c, blockEH (u ^ p) :=
  running_pos_comp_pow_pos_of continuous_blockEH (fun _d hd => blockEH_partial_pos hd) hp hc

/-! ## Integrability of `u ↦ P_A(uᵖ)` -/

/-- `u ↦ qProdSet A (uᵖ)` is interval-integrable on `[0,c]` for `c ∈ [0,1]`,
`p ≥ 1`: it is the a.e. limit of the continuous truncations and bounded by `1`. -/
theorem intervalIntegrable_qProdSet_comp_pow (A : Set ℕ) {p : ℕ} (hp : 1 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => qProdSet A (u ^ p)) volume 0 c := by
  classical
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc.1]
  have hmem : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) c)), u ∈ Ioc (0 : ℝ) c :=
    ae_restrict_mem measurableSet_Ioc
  have hlt : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) c)), u ^ p ∈ Ico (0 : ℝ) 1 := by
    filter_upwards [hmem, ae_restrict_ne_one (Ioc (0 : ℝ) c)] with u hu hu1
    exact ⟨pow_nonneg hu.1.le p,
      pow_lt_one₀ hu.1.le (lt_of_le_of_ne (hu.2.trans hc.2) hu1) (by omega)⟩
  have hmeas : AEStronglyMeasurable (fun u => qProdSet A (u ^ p))
      (volume.restrict (Ioc (0 : ℝ) c)) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun N u => qProd ((Finset.range (N + 1)).filter (· ∈ A)) (u ^ p))
      (fun N => (((qProd_continuous _).comp (continuous_pow p)).aestronglyMeasurable).restrict)
      ?_
    filter_upwards [hlt] with u hu
    exact qProdSet_eq_lim A hu.1 hu.2
  refine Integrable.of_bound hmeas 1 ?_
  filter_upwards [hlt] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (qProdSet_nonneg A ⟨hu.1, hu.2.le⟩)]
  exact qProdSet_le_one A hu.1 hu.2

theorem intervalIntegrable_blockESet_comp_pow (T : Set ℕ) {p : ℕ} (hp : 1 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => blockESet T (u ^ p)) volume 0 c :=
  (intervalIntegrable_qProdSet_comp_pow T hp hc).sub
    ((continuous_const.sub (continuous_pow p)).intervalIntegrable 0 c)

/-- **Corollary 3.2, arbitrary `T`.**  `E_T(uᵖ) ≥ E_H(uᵖ)` pointwise on `[0,c]`,
and the continuous envelope has positive running integrals by
`running_pos_blockEH_comp_pow`. -/
theorem running_pos_comp_pow_pos_set {T : Set ℕ} (hT : ∀ n ∈ T, 2 ≤ n) {p : ℕ}
    (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ u in (0 : ℝ)..c, blockESet T (u ^ p) := by
  refine lt_of_lt_of_le (running_pos_blockEH_comp_pow hp hc) ?_
  refine intervalIntegral.integral_mono_on hc.1.le
    ((continuous_blockEH.comp (continuous_pow p)).intervalIntegrable 0 c)
    (intervalIntegrable_blockESet_comp_pow T hp ⟨hc.1.le, hc.2⟩) ?_
  intro u hu
  exact blockEH_le_blockESet hT ⟨pow_nonneg hu.1 p, pow_le_one₀ hu.1 (hu.2.trans hc.2)⟩

/-! ## Block-step product algebra -/

/-- Inserting a fresh exponent factors the product weight. -/
theorem qProd_insert {S : Finset ℕ} {n : ℕ} (hn : n ∉ S) (u : ℝ) :
    qProd (insert n S) u = (1 - u ^ n) * qProd S u := by
  unfold qProd
  rw [Finset.prod_insert hn]

/-- Scaling the exponents by `p` reindexes the product as evaluation at `uᵖ`. -/
theorem qProd_image_mul (T : Finset ℕ) (p : ℕ)
    (hinj : Set.InjOn (· * p) T) (u : ℝ) :
    qProd (T.image (· * p)) u = qProd T (u ^ p) := by
  unfold qProd
  rw [Finset.prod_image (fun a ha b hb => hinj ha hb)]
  refine Finset.prod_congr rfl (fun n _hn => ?_)
  rw [← pow_mul, mul_comm n p]

/-- The product weight splits over a disjoint union. -/
theorem qProd_union {B S : Finset ℕ} (hdisj : Disjoint B S) (u : ℝ) :
    qProd (B ∪ S) u = qProd B u * qProd S u := by
  unfold qProd
  rw [Finset.prod_union hdisj]

/-- Pointwise block-step identity:
`P_{B ∪ pT}(u) − P_{B ∪ {p}}(u) = P_B(u)·E_T(uᵖ)`. -/
theorem qProd_blockStep_diff {B T : Finset ℕ} {p : ℕ}
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B)
    (hinj : Set.InjOn (· * p) T) (u : ℝ) :
    qProd (B ∪ T.image (· * p)) u - qProd (insert p B) u
      = qProd B u * blockE T (u ^ p) := by
  rw [qProd_union hdisj, qProd_image_mul T p hinj, qProd_insert hpB]
  unfold blockE
  ring

/-- Identity (1.2): `F_c(B ∪ pT) - F_c(B ∪ {p}) = ∫₀ᶜ P_B(u) E_T(uᵖ) du`. -/
theorem Fc_blockStep_diff {B T : Finset ℕ} {p : ℕ}
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B)
    (hinj : Set.InjOn (· * p) T) (c : ℝ) :
    Fc c (B ∪ T.image (· * p)) - Fc c (insert p B)
      = ∫ u in (0 : ℝ)..c, qProd B u * blockE T (u ^ p) := by
  unfold Fc
  rw [← intervalIntegral.integral_sub
    ((qProd_continuous _).intervalIntegrable _ _)
    ((qProd_continuous _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr (fun u _hu => ?_)
  exact qProd_blockStep_diff hdisj hpB hinj u

set_option linter.unusedVariables false in
/-- **Proposition 3.4 (strict block exchange), finite sets.**  Stated for every
positive integer `p`, not only primes: the proof uses only the substitution `v = uᵖ`
(this generality is Theorem 4.1 of the paper, extremality over an ambient set).
(`hTne` is not needed for the proof: for `T = ∅` one has `E_∅(v) = v`, whose
running integrals are still positive; the hypothesis is kept to match the paper.) -/
theorem block_exchange_lt {B T : Finset ℕ} {p : ℕ} (hp : 0 < p)
    (hB : ∀ b ∈ B, 2 ≤ b) (hT : ∀ t ∈ T, 2 ≤ t) (hTne : T.Nonempty)
    (hdisj : Disjoint B (T.image (· * p))) (hpB : p ∉ B)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    Fc c (insert p B) < Fc c (B ∪ T.image (· * p)) := by
  have hp1 : 1 ≤ p := hp
  have hinj : Set.InjOn (· * p) T := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_right hp hab
  have hB1 : ∀ b ∈ B, 1 ≤ b := fun b hb => le_trans (by norm_num) (hB b hb)
  have hcIcc : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  rw [← sub_pos, Fc_blockStep_diff hdisj hpB hinj c]
  refine integral_weight_mul_pos_upto (g := fun u => blockE T (u ^ p)) (w := qProd B)
    (w' := qProd' B) hc ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (continuous_blockE T).comp (continuous_pow p)
  · intro x _hx; exact hasDerivAt_qProd B x
  · exact continuous_qProd' B
  · exact qProd_nonneg B hcIcc
  · intro x hx; exact qProd'_nonpos B ⟨hx.1, hx.2.trans hc.2⟩
  · intro y hy; exact running_pos_comp_pow_pos hT hp1 ⟨hy.1, hy.2.trans hc.2⟩
  · -- Strictness: `B = ∅` gives `w(c) = 1 > 0`; otherwise `w'(c/2) < 0`.
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · left
      subst hBe
      simp [qProd]
    · right
      refine ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.1]⟩, ?_⟩
      exact qProd'_neg_of_nonempty hBne hB1 ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-! ## Block-step product algebra for arbitrary sets -/

/-- The infinite product splits over a disjoint union (`0 ≤ u < 1`). -/
theorem qProdSet_union {S T : Set ℕ} (hST : Disjoint S T) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    qProdSet (S ∪ T) u = qProdSet S u * qProdSet T u := by
  rw [qProdSet_eq_tprod_mulIndicator, qProdSet_eq_tprod_mulIndicator,
    qProdSet_eq_tprod_mulIndicator, Set.mulIndicator_union_of_disjoint hST]
  exact (multipliable_mulIndicator S h0 h1).tprod_mul (multipliable_mulIndicator T h0 h1)

theorem qProdSet_singleton (n : ℕ) (u : ℝ) : qProdSet {n} u = 1 - u ^ n := by
  rw [← Finset.coe_singleton, qProdSet_coe]
  simp [qProd]

/-- Inserting a fresh exponent factors the infinite product (`0 ≤ u < 1`). -/
theorem qProdSet_insert {S : Set ℕ} {n : ℕ} (hn : n ∉ S) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    qProdSet (insert n S) u = (1 - u ^ n) * qProdSet S u := by
  rw [Set.insert_eq, qProdSet_union (Set.disjoint_singleton_left.mpr hn) h0 h1,
    qProdSet_singleton]

/-- Scaling the exponents by `p ≥ 1` reindexes the infinite product as
evaluation at `uᵖ` (no convergence assumption needed). -/
theorem qProdSet_image_mul (T : Set ℕ) {p : ℕ} (hp : 0 < p) (u : ℝ) :
    qProdSet ((· * p) '' T) u = qProdSet T (u ^ p) := by
  rw [qProdSet_eq_tprod_mulIndicator, qProdSet_eq_tprod_mulIndicator]
  have hinj : Function.Injective (fun t : ℕ => t * p) :=
    fun a b h => Nat.eq_of_mul_eq_mul_right hp h
  rw [← hinj.tprod_eq (f := Set.mulIndicator ((· * p) '' T) (fun n : ℕ => 1 - u ^ n))
    (Set.mulSupport_mulIndicator_subset.trans (Set.image_subset_range _ _))]
  refine tprod_congr (fun t => ?_)
  by_cases ht : t ∈ T
  · have hmem : (fun t : ℕ => t * p) t ∈ (· * p) '' T := ⟨t, ht, rfl⟩
    rw [Set.mulIndicator_of_mem ht, Set.mulIndicator_of_mem hmem]
    simp only [← pow_mul, mul_comm]
  · have hmem : (fun t : ℕ => t * p) t ∉ (· * p) '' T := by
      rintro ⟨s, hs, hst⟩
      exact ht ((hinj hst) ▸ hs)
    rw [Set.mulIndicator_of_notMem ht, Set.mulIndicator_of_notMem hmem]

/-- Pointwise block-step identity for arbitrary sets, `0 ≤ u < 1`:
`P_{B ∪ pT}(u) − P_{B ∪ {p}}(u) = P_B(u)·E_T(uᵖ)`. -/
theorem qProdSet_blockStep_diff {B T : Set ℕ} {p : ℕ} (hp : 0 < p)
    (hdisj : Disjoint B ((· * p) '' T)) (hpB : p ∉ B) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    qProdSet (B ∪ (· * p) '' T) u - qProdSet (insert p B) u
      = qProdSet B u * blockESet T (u ^ p) := by
  rw [qProdSet_union hdisj h0 h1, qProdSet_image_mul T hp u, qProdSet_insert hpB h0 h1]
  unfold blockESet
  ring

/-! ## The uniform lower bound `κ` (paper, proof of Proposition 3.4)

With `g(u) = E_H(uᵖ)` (continuous) and `G(y) = ∫₀ʸ g`, integration by parts
gives, for every finite `S ⊆ {2,3,…}` containing `b`,
`∫₀ᶜ P_S g = P_S(c) G(c) − ∫₀ᶜ P_S' G ≥ ∫₀ᶜ b u^{b-1} H(u) G(u) du =: κ_c > 0`,
since `−P_S'(u) ≥ b u^{b-1} P_{S∖{b}}(u) ≥ b u^{b-1} H(u)`.  The bound is
independent of `S`, so it survives the truncation limit `B_N → B`. -/

/-- Integration by parts for a `C¹` weight against a continuous integrand. -/
theorem integral_weight_mul_eq_ibp {g w w' : ℝ → ℝ} {c : ℝ} (hg : Continuous g)
    (hw : ∀ x ∈ uIcc (0 : ℝ) c, HasDerivAt w (w' x) x) (hw'cont : Continuous w') :
    (∫ u in (0 : ℝ)..c, w u * g u) =
      w c * runInt g c - ∫ u in (0 : ℝ)..c, w' u * runInt g u := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := w) (v := runInt g) (u' := w') (v' := g) hw (fun x _ => hasDerivAt_runInt hg x)
    (hw'cont.intervalIntegrable 0 c) (hg.intervalIntegrable 0 c)
  rw [h, runInt_zero]
  ring

/-- For `b ∈ S ⊆ {2,3,…}`: `−P_S'(u) ≥ b u^{b-1} H(u)` on `[0,1]`. -/
theorem le_neg_qProd' {S : Finset ℕ} (hS : ∀ n ∈ S, 2 ≤ n) {b : ℕ} (hb : b ∈ S)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (b : ℝ) * u ^ (b - 1) * HfunExt u ≤ -qProd' S u := by
  classical
  unfold qProd'
  rw [← Finset.add_sum_erase S _ hb]
  have hrest : ∑ i ∈ S.erase b, (∏ j ∈ S.erase i, (1 - u ^ j)) * (-((i : ℝ) * u ^ (i - 1)))
      ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have hprod : 0 ≤ ∏ j ∈ S.erase i, (1 - u ^ j) :=
      Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (pow_le_one₀ hu.1 hu.2))
    have hpow : 0 ≤ (i : ℝ) * u ^ (i - 1) := mul_nonneg (by positivity) (pow_nonneg hu.1 _)
    nlinarith
  have hprod0 : 0 ≤ ∏ j ∈ S.erase b, (1 - u ^ j) :=
    Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (pow_le_one₀ hu.1 hu.2))
  have hH : HfunExt u ≤ ∏ j ∈ S.erase b, (1 - u ^ j) := by
    rw [HfunExt_of_mem hu]
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h] at hprod0 ⊢
      rw [Hfun_one]
      exact hprod0
    · exact Hfun_le_qProd_of_lt (S.erase b) (fun n hn => hS n (Finset.mem_of_mem_erase hn))
        hu.1 h
  have hpowb : 0 ≤ (b : ℝ) * u ^ (b - 1) := mul_nonneg (by positivity) (pow_nonneg hu.1 _)
  have := mul_le_mul_of_nonneg_left hH hpowb
  linarith

/-- The running integral `G̃(y) = ∫₀ʸ E_H(uᵖ) du`. -/
noncomputable def GH (p : ℕ) (y : ℝ) : ℝ := ∫ u in (0 : ℝ)..y, blockEH (u ^ p)

theorem GH_eq_runInt (p : ℕ) : GH p = runInt (fun u => blockEH (u ^ p)) := rfl

theorem continuous_GH (p : ℕ) : Continuous (GH p) := by
  rw [GH_eq_runInt]
  exact continuous_runInt (continuous_blockEH.comp (continuous_pow p))

theorem GH_nonneg {p : ℕ} (hp : 1 ≤ p) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ GH p y := by
  rw [GH_eq_runInt]
  exact runInt_nonneg (fun _d hd => running_pos_blockEH_comp_pow hp hd) hy

theorem GH_pos {p : ℕ} (hp : 1 ≤ p) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) : 0 < GH p y :=
  running_pos_blockEH_comp_pow hp hy

/-- The uniform lower bound `κ_c = ∫₀ᶜ b u^{b-1} H(u) G̃(u) du`. -/
noncomputable def kappa (b p : ℕ) (c : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..c, (b : ℝ) * u ^ (b - 1) * HfunExt u * GH p u

theorem continuous_kappa_integrand (b p : ℕ) :
    Continuous fun u : ℝ => (b : ℝ) * u ^ (b - 1) * HfunExt u * GH p u :=
  ((continuous_const.mul (continuous_pow _)).mul continuous_HfunExt).mul (continuous_GH p)

theorem kappa_pos {b p : ℕ} (hb : 1 ≤ b) (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < kappa b p c := by
  unfold kappa
  have h := integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun _ => (0 : ℝ))
    hc.1 continuousOn_const (continuous_kappa_integrand b p).continuousOn ?_ ?_
  · simpa using h
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans hc.2⟩
    have h1 : 0 ≤ (b : ℝ) * x ^ (b - 1) := mul_nonneg (by positivity) (pow_nonneg hx.1.le _)
    have h2 : 0 ≤ HfunExt x := by rw [HfunExt_of_mem hx']; exact Hfun_nonneg hx'
    exact mul_nonneg (mul_nonneg h1 h2) (GH_nonneg hp hx')
  · refine ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.1]⟩, ?_⟩
    have hmem : c / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have h1 : 0 < (b : ℝ) * (c / 2) ^ (b - 1) := mul_pos hbR (pow_pos (by linarith [hc.1]) _)
    have h2 : 0 < HfunExt (c / 2) := by
      rw [HfunExt_of_mem hmem]
      exact Hfun_pos_of_lt hmem.1 (by linarith [hc.2])
    have h3 : 0 < GH p (c / 2) := GH_pos hp ⟨by linarith [hc.1], by linarith [hc.2]⟩
    exact mul_pos (mul_pos h1 h2) h3

/-- For a finite `S ⊆ {2,3,…}` containing `b`: `∫₀ᶜ P_S(u) E_H(uᵖ) du ≥ κ_c`. -/
theorem kappa_le_integral_qProd_mul {S : Finset ℕ} (hS : ∀ n ∈ S, 2 ≤ n) {b : ℕ}
    (hb : b ∈ S) {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    kappa b p c ≤ ∫ u in (0 : ℝ)..c, qProd S u * blockEH (u ^ p) := by
  have hgcont : Continuous fun u : ℝ => blockEH (u ^ p) :=
    continuous_blockEH.comp (continuous_pow p)
  rw [integral_weight_mul_eq_ibp hgcont (fun x _ => hasDerivAt_qProd S x) (continuous_qProd' S),
    ← GH_eq_runInt]
  have hbdry : 0 ≤ qProd S c * GH p c :=
    mul_nonneg (qProd_nonneg S ⟨hc.1.le, hc.2⟩) (GH_nonneg hp ⟨hc.1.le, hc.2⟩)
  have htail : kappa b p c ≤ -∫ u in (0 : ℝ)..c, qProd' S u * GH p u := by
    unfold kappa
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on hc.1.le
    · exact (continuous_kappa_integrand b p).intervalIntegrable 0 c
    · exact (((continuous_qProd' S).mul (continuous_GH p)).neg).intervalIntegrable 0 c
    · intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hc.2⟩
      have := mul_le_mul_of_nonneg_right (le_neg_qProd' hS hb hu') (GH_nonneg hp hu')
      linarith
  linarith

/-- Dominated convergence: `∫₀ᶜ P_{B_N} g → ∫₀ᶜ P_B g` for continuous `g`. -/
theorem tendsto_integral_qProd_truncation_mul (B : Set ℕ) [DecidablePred (· ∈ B)] {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {g : ℝ → ℝ} (hg : Continuous g) :
    Filter.Tendsto
      (fun N => ∫ u in (0 : ℝ)..c, qProd ((Finset.range (N + 1)).filter (· ∈ B)) u * g u)
      Filter.atTop (nhds (∫ u in (0 : ℝ)..c, qProdSet B u * g u)) := by
  simp only [intervalIntegral.integral_of_le hc.1]
  apply tendsto_integral_of_dominated_convergence (bound := fun u => ‖g u‖)
  · exact fun N => (((qProd_continuous _).mul hg).aestronglyMeasurable).restrict
  · exact hg.integrableOn_Ioc.norm
  · intro N
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.trans hc.2⟩
    rw [norm_mul]
    calc ‖qProd ((Finset.range (N + 1)).filter (· ∈ B)) u‖ * ‖g u‖ ≤ 1 * ‖g u‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg (qProd_nonneg _ hu')]
          exact qProd_le_one _ hu'
      _ = ‖g u‖ := one_mul _
  · have hmem : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) c)), u ∈ Ioc (0 : ℝ) c :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hmem, ae_restrict_ne_one (Ioc (0 : ℝ) c)] with u hu hu1
    exact (qProdSet_eq_lim B hu.1.le (lt_of_le_of_ne (hu.2.trans hc.2) hu1)).mul
      tendsto_const_nhds

/-- The uniform bound survives the truncation limit:
`∫₀ᶜ P_B(u) E_H(uᵖ) du ≥ κ_c` for any `B ⊆ {2,3,…}` with `b ∈ B`. -/
theorem kappa_le_integral_qProdSet_mul {B : Set ℕ} (hB : ∀ n ∈ B, 2 ≤ n) {b : ℕ} (hb : b ∈ B)
    {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    kappa b p c ≤ ∫ u in (0 : ℝ)..c, qProdSet B u * blockEH (u ^ p) := by
  classical
  refine ge_of_tendsto (tendsto_integral_qProd_truncation_mul B ⟨hc.1.le, hc.2⟩
    (continuous_blockEH.comp (continuous_pow p))) ?_
  filter_upwards [Filter.eventually_ge_atTop b] with N hN
  apply kappa_le_integral_qProd_mul _ _ hp hc
  · intro n hn
    exact hB n (Finset.mem_filter.mp hn).2
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩

set_option linter.unusedVariables false in
/-- **Proposition 3.4, arbitrary sets**, for every positive integer `p`.  Route: a.e. on `[0,c]`,
`P_{B ∪ pT} − P_{B ∪ {p}} = P_B·E_T(uᵖ) ≥ P_B·E_H(uᵖ)` with `E_H` the
continuous envelope; the integral of the right side is `≥ κ_c > 0` uniformly
along the truncations `B_N` (`kappa_le_integral_qProdSet_mul`), or equals
`∫₀ᶜ E_H(uᵖ) > 0` when `B = ∅`.  (`hTne` is not needed, as in the finite case.) -/
theorem block_exchange_lt_set {B T : Set ℕ} {p : ℕ} (hp : 0 < p)
    (hB : ∀ b ∈ B, 2 ≤ b) (hT : ∀ t ∈ T, 2 ≤ t) (hTne : T.Nonempty)
    (hdisj : Disjoint B ((· * p) '' T)) (hpB : p ∉ B)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    FcSet c (insert p B) < FcSet c (B ∪ (· * p) '' T) := by
  have hp1 : 1 ≤ p := hp
  have hcIcc : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2⟩
  rw [← sub_pos]
  unfold FcSet
  rw [← intervalIntegral.integral_sub (intervalIntegrable_qProdSet _ hcIcc)
    (intervalIntegrable_qProdSet _ hcIcc)]
  have hlow : (∫ u in (0 : ℝ)..c, qProdSet B u * blockEH (u ^ p))
      ≤ ∫ u in (0 : ℝ)..c, (qProdSet (B ∪ (· * p) '' T) u - qProdSet (insert p B) u) := by
    apply intervalIntegral.integral_mono_ae_restrict hc.1.le
    · exact (intervalIntegrable_qProdSet B hcIcc).mul_continuousOn
        (continuous_blockEH.comp (continuous_pow p)).continuousOn
    · exact (intervalIntegrable_qProdSet _ hcIcc).sub (intervalIntegrable_qProdSet _ hcIcc)
    · have hmem : ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) c)), u ∈ Icc (0 : ℝ) c :=
        ae_restrict_mem measurableSet_Icc
      filter_upwards [hmem, ae_restrict_ne_one (Icc (0 : ℝ) c)] with u hu hu1
      have h1 : u < 1 := lt_of_le_of_ne (hu.2.trans hc.2) hu1
      rw [qProdSet_blockStep_diff hp hdisj hpB hu.1 h1]
      apply mul_le_mul_of_nonneg_left _ (qProdSet_nonneg B ⟨hu.1, h1.le⟩)
      exact blockEH_le_blockESet hT ⟨pow_nonneg hu.1 p, pow_le_one₀ hu.1 h1.le⟩
  rcases B.eq_empty_or_nonempty with hBe | ⟨b, hb⟩
  · -- `B = ∅`: the weight is identically `1`.
    subst hBe
    have hone : (∫ u in (0 : ℝ)..c, qProdSet ∅ u * blockEH (u ^ p))
        = ∫ u in (0 : ℝ)..c, blockEH (u ^ p) := by
      apply intervalIntegral.integral_congr
      intro u _
      simp [qProdSet]
    linarith [running_pos_blockEH_comp_pow hp1 hc]
  · have hb1 : 1 ≤ b := le_trans (by norm_num) (hB b hb)
    linarith [kappa_le_integral_qProdSet_mul hB hb hp1 hc, kappa_pos hb1 hp1 hc]

end RntPaper
