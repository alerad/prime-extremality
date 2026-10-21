import RntPaper.Endpoint
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Deriv

/-!
# Single crossing (paper Lemma 2.1) and Theorem 1.4 for `H`

`h(x) = log(H(x)/(1-x)) = log(1+x) + ∑_{n≥3} log(1 - xⁿ)` is strictly concave
on `[0,1)` with `h(0)=0`, `h'(0)=1`, `h → -∞`, so `H - (1-x)` is `+` then `-`
with one crossing.  Combined with `endpoint_estimate` and the abstract
unimodality lemma this gives `∫₀ᶜ H > c - c²/2` for all `c ∈ (0,1]`.

The abstract lemma is ported verbatim from
`ProductInvariants.integral_pos_of_single_crossing` (Mathlib-only proof).
-/

namespace RntPaper

open MeasureTheory intervalIntegral Set Filter Topology

/-- **Abstract unimodal positivity.** If `E` is continuous on `[0,1]`, `> 0` on
`(0,a)`, `< 0` on `(a,1)`, and `∫₀¹ E > 0`, then `∫₀ᶜ E > 0` for `c ∈ (0,1]`. -/
theorem integral_pos_of_single_crossing {E : ℝ → ℝ}
    (hEc : ContinuousOn E (Icc 0 1)) {a : ℝ} (_ha : a ∈ Ioo (0 : ℝ) 1)
    (hposo : ∀ x ∈ Ioo (0 : ℝ) a, 0 < E x)
    (hpos : ∀ x ∈ Ioc (0 : ℝ) a, 0 ≤ E x)
    (hneg : ∀ x ∈ Icc a (1 : ℝ), E x ≤ 0)
    (hnego : ∀ x ∈ Ioo a (1 : ℝ), E x < 0)
    (hend : 0 < ∫ x in (0:ℝ)..1, E x)
    {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    0 < ∫ x in (0:ℝ)..c, E x := by
  obtain ⟨hc0, hc1⟩ := hc
  have hint : ∀ x y : ℝ, x ∈ Icc (0:ℝ) 1 → y ∈ Icc (0:ℝ) 1 →
      IntervalIntegrable E volume x y := by
    intro x y hx hy
    apply ContinuousOn.intervalIntegrable
    apply hEc.mono
    apply uIcc_subset_Icc hx hy
  rcases le_total c a with hca | hca
  · apply intervalIntegral.integral_pos hc0
    · exact hEc.mono (Icc_subset_Icc le_rfl hc1)
    · intro x hx
      exact hpos x ⟨hx.1, le_trans hx.2 hca⟩
    · refine ⟨c / 2, ⟨by positivity, by linarith⟩, ?_⟩
      exact hposo (c / 2) ⟨by positivity, by linarith⟩
  · have hsplit : (∫ x in (0:ℝ)..1, E x)
        = (∫ x in (0:ℝ)..c, E x) + ∫ x in c..1, E x :=
      (integral_add_adjacent_intervals
        (hint 0 c ⟨le_rfl, by norm_num⟩ ⟨hc0.le, hc1⟩)
        (hint c 1 ⟨hc0.le, hc1⟩ ⟨by norm_num, le_rfl⟩)).symm
    have hneg_tail : (∫ x in c..1, E x) ≤ 0 := by
      rcases eq_or_lt_of_le hc1 with rfl | hc1'
      · simp
      · apply le_of_lt
        have : (∫ x in c..1, E x) < ∫ x in c..1, (0 : ℝ) := by
          apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt hc1'
            (hEc.mono (Icc_subset_Icc hc0.le le_rfl)) continuousOn_const
          · intro x hx
            exact hneg x ⟨le_trans hca hx.1.le, hx.2⟩
          · refine ⟨(c + 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
            exact hnego ((c + 1) / 2) ⟨by linarith, by linarith⟩
        simpa using this
    linarith [hsplit, hend, hneg_tail]

/-! ## Analytic facts about `H` -/

/-- `H` is continuous on `[0,1]` (locally uniform convergence on `[0,1)` and
`0 ≤ H ≤ 1 - x²` at the endpoint). -/
theorem Hfun_continuousOn : ContinuousOn Hfun (Icc 0 1) :=
  Hfun_continuousOn_Icc

theorem Hfun_nonneg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ Hfun x :=
  Hfun_nonneg_Icc hx

theorem Hfun_le_one_sub_sq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : Hfun x ≤ 1 - x ^ 2 :=
  Hfun_le_one_sub_sq_Icc hx

/-- `h(x) = log(H(x)/(1-x))`. -/
noncomputable def hlog (x : ℝ) : ℝ := Real.log (Hfun x / (1 - x))

/-- `h = log(1+x) + ∑_{n≥3} log(1 - xⁿ)` on `[0,1)`. -/
theorem hlog_eq_tsum {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    hlog x = Real.log (1 + x) + ∑' n : ℕ, Real.log (1 - x ^ (n + 3)) := by
  have h1x : 0 < 1 - x := by linarith [hx.2]
  unfold hlog
  rw [Real.log_div (Hfun_pos hx).ne' h1x.ne', log_Hfun hx,
    (summable_log_one_sub_pow hx 2).tsum_eq_zero_add]
  have e : ∀ n : ℕ, n + 1 + 2 = n + 3 := fun n => by ring
  simp only [e, zero_add]
  have h2 : (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) := by ring
  rw [h2, Real.log_mul h1x.ne' (by linarith [hx.1])]
  ring

/-- The tail `∑_{n≥3} log(1 - xⁿ)` as a function. -/
noncomputable def hlogTail (x : ℝ) : ℝ := ∑' n : ℕ, Real.log (1 - x ^ (n + 3))

theorem hlog_eq_tail {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    hlog x = Real.log (1 + x) + hlogTail x := hlog_eq_tsum hx

/-- `log(1 + x)` is strictly concave on `[0,1)`. -/
theorem strictConcaveOn_log_one_add :
    StrictConcaveOn ℝ (Ico (0:ℝ) 1) (fun x => Real.log (1 + x)) := by
  refine ⟨convex_Ico _ _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have h := strictConcaveOn_log_Ioi.2 (show (1 + x) ∈ Ioi (0:ℝ) by
      simp only [mem_Ioi]; linarith [hx.1])
    (show (1 + y) ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith [hy.1])
    (fun h => hxy (by linarith)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : 1 + (a * x + b * y) = a * (1 + x) + b * (1 + y) := by
    linear_combination (-1 : ℝ) * hab
  rw [e]; exact h

/-- Each `x ↦ log(1 - xᵏ)`, `k ≥ 1`, is concave on `[0,1)`: `1 - xᵏ` is concave
and `log` is concave and increasing. -/
theorem concaveOn_log_one_sub_pow {k : ℕ} (hk : k ≠ 0) :
    ConcaveOn ℝ (Ico (0:ℝ) 1) (fun x => Real.log (1 - x ^ k)) := by
  refine ⟨convex_Ico _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ Ico (0:ℝ) 1 := (convex_Ico (0:ℝ) 1) hx hy ha hb hab
  have hpx := one_sub_pow_pos' hx hk
  have hpy := one_sub_pow_pos' hy hk
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (show 1 - x ^ k ∈ Ioi (0:ℝ) from hpx)
    (show 1 - y ^ k ∈ Ioi (0:ℝ) from hpy) ha hb hab
  have hpow := (convexOn_pow k).2 (show x ∈ Ici (0:ℝ) from hx.1) (show y ∈ Ici (0:ℝ) from hy.1)
    ha hb hab
  simp only [smul_eq_mul] at hlog hpow ⊢
  refine le_trans hlog (Real.log_le_log ?_ ?_)
  · have : a * (1 - x ^ k) + b * (1 - y ^ k) = 1 - (a * x ^ k + b * y ^ k) := by
      linear_combination hab
    rw [this]
    have hm : 0 < min (1 - x ^ k) (1 - y ^ k) := lt_min hpx hpy
    have hsum : a * min (1 - x ^ k) (1 - y ^ k) + b * min (1 - x ^ k) (1 - y ^ k)
        = min (1 - x ^ k) (1 - y ^ k) := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left (1 - x ^ k) (1 - y ^ k)) ha,
      mul_le_mul_of_nonneg_left (min_le_right (1 - x ^ k) (1 - y ^ k)) hb]
  · linear_combination hpow + hab

/-- The tail is concave on `[0,1)` (termwise concavity passes to the `tsum`). -/
theorem hlogTail_concaveOn : ConcaveOn ℝ (Ico (0:ℝ) 1) hlogTail := by
  refine ⟨convex_Ico _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ Ico (0:ℝ) 1 := (convex_Ico (0:ℝ) 1) hx hy ha hb hab
  unfold hlogTail
  simp only [smul_eq_mul] at hxy ⊢
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_log_one_sub_pow hx 3).mul_left a).tsum_add
      ((summable_log_one_sub_pow hy 3).mul_left b)]
  refine Summable.tsum_le_tsum (fun n => ?_)
    (((summable_log_one_sub_pow hx 3).mul_left a).add
      ((summable_log_one_sub_pow hy 3).mul_left b)) (summable_log_one_sub_pow hxy 3)
  have := (concaveOn_log_one_sub_pow (k := n + 3) (by omega)).2 hx hy ha hb hab
  simpa only [smul_eq_mul] using this

/-- `h` is strictly concave on `[0,1)`.  The paper differentiates the series
twice (`h''(x) = -1/(1+x)² - ∑_{n≥3} n xⁿ⁻²((n-1) + xⁿ)/(1-xⁿ)² < 0`); here we
avoid differentiating the `tsum` and use instead that `log(1+x)` is strictly
concave and every `log(1 - xⁿ)` is concave, so the tail sum is concave. -/
theorem hlog_strictConcaveOn : StrictConcaveOn ℝ (Ico (0 : ℝ) 1) hlog :=
  (strictConcaveOn_log_one_add.add_concaveOn hlogTail_concaveOn).congr
    fun _ hx => (hlog_eq_tail hx).symm

theorem hlog_zero : hlog 0 = 0 := by
  unfold hlog
  rw [Hfun_zero]; simp

/-- `hlog` is continuous on `[0,1)`. -/
theorem hlog_continuousOn : ContinuousOn hlog (Ico (0:ℝ) 1) := by
  unfold hlog
  apply ContinuousOn.log
  · apply ContinuousOn.div (Hfun_continuousOn_Icc.mono Ico_subset_Icc_self)
      (by fun_prop)
    intro x hx; linarith [hx.2]
  · intro x hx
    exact (div_pos (Hfun_pos hx) (by linarith [hx.2])).ne'

/-- `h'(0) = 1 > 0`, so `h > 0` just to the right of `0`. -/
theorem hlog_pos_near_zero : ∃ δ > 0, ∀ x ∈ Ioo (0 : ℝ) δ, 0 < hlog x := by
  refine ⟨1 / 3, by norm_num, fun x hx => ?_⟩
  have hx' : x ∈ Ico (0:ℝ) 1 := ⟨hx.1.le, by linarith [hx.2]⟩
  have h1x : 0 < 1 - x := by linarith [hx'.2]
  rw [hlog_eq_tsum hx']
  -- `log(1+x) ≥ x/(1+x)`
  have hA : x / (1 + x) ≤ Real.log (1 + x) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1 + x by linarith [hx.1])
    have h1 : (1 + x) ≠ 0 := by linarith [hx.1]
    have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    linarith
  -- termwise `log(1 - xⁿ) ≥ -xⁿ/(1-x)`
  have hB : ∑' n : ℕ, -(x ^ (n + 3) / (1 - x)) ≤ ∑' n : ℕ, Real.log (1 - x ^ (n + 3)) := by
    refine Summable.tsum_le_tsum (fun n => ?_) ((summable_pow_shift hx' 3).div_const _).neg
      (summable_log_one_sub_pow hx' 3)
    have hp := one_sub_pow_pos' hx' (n := n + 3) (by omega)
    have := Real.one_sub_inv_le_log_of_pos hp
    have hle : x ^ (n + 3) ≤ x := by
      calc x ^ (n + 3) ≤ x ^ 1 := pow_le_pow_of_le_one hx'.1 hx'.2.le (by omega)
        _ = x := pow_one x
    have e : 1 - (1 - x ^ (n + 3))⁻¹ = -(x ^ (n + 3) / (1 - x ^ (n + 3))) := by
      field_simp; ring
    have hd : x ^ (n + 3) / (1 - x) ≥ x ^ (n + 3) / (1 - x ^ (n + 3)) :=
      div_le_div_of_nonneg_left (pow_nonneg hx'.1 _) h1x (by linarith)
    linarith
  have hC : ∑' n : ℕ, -(x ^ (n + 3) / (1 - x)) = -(x ^ 3 / (1 - x) ^ 2) := by
    rw [tsum_neg]
    simp only [div_eq_mul_inv]
    rw [tsum_mul_right, ← div_eq_mul_inv, tsum_pow_shift hx' 3]
    field_simp
  rw [hC] at hB
  -- `x/(1+x) > x³/(1-x)²` for `0 < x < 1/3`
  have hD : x ^ 3 / (1 - x) ^ 2 < x / (1 + x) := by
    rw [div_lt_div_iff₀ (by positivity) (by linarith [hx.1])]
    have h3 : x ^ 3 < 1 / 27 := by
      calc x ^ 3 < (1 / 3) ^ 3 := pow_lt_pow_left₀ hx.2 hx.1.le (by norm_num)
        _ = 1 / 27 := by norm_num
    have hpos : 0 < 1 - 2 * x - x ^ 3 := by linarith [hx.2]
    nlinarith [mul_pos hx.1 hpos]
  linarith

/-- `h(x) ≤ log(1+x) + log(1-x³) → -∞`, so `h < 0` near `1`. -/
theorem hlog_neg_near_one : ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ x ∈ Ioo δ 1, hlog x < 0 := by
  refine ⟨9 / 10, ⟨by norm_num, by norm_num⟩, fun x hx => ?_⟩
  have hx' : x ∈ Ico (0:ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  rw [hlog_eq_tsum hx', (summable_log_one_sub_pow hx' 3).tsum_eq_zero_add]
  have e : ∀ n : ℕ, n + 1 + 3 = n + 4 := fun n => by ring
  simp only [e, zero_add]
  have htail : ∑' n : ℕ, Real.log (1 - x ^ (n + 4)) ≤ 0 :=
    tsum_nonpos fun n => Real.log_nonpos (one_sub_pow_pos' hx' (n := n + 4) (by omega)).le
      (by linarith [pow_nonneg hx'.1 (n + 4)])
  have h3 : 0 < 1 - x ^ 3 := one_sub_pow_pos' hx' (by norm_num)
  have hmul : Real.log (1 + x) + Real.log (1 - x ^ 3) < 0 := by
    rw [← Real.log_mul (by linarith [hx'.1]) h3.ne']
    apply Real.log_neg (mul_pos (by linarith [hx'.1]) h3)
    nlinarith [hx.1, hx.2, sq_nonneg x, mul_pos (show (0:ℝ) < x by linarith [hx.1])
      (show (0:ℝ) < x by linarith [hx.1])]
  linarith

/-- **Lemma 2.1 (single crossing).** There is a unique `x* ∈ (0,1)` with
`H(x*) = 1 - x*`; `H - (1-x)` is `> 0` on `(0,x*)` and `< 0` on `(x*,1)`. -/
theorem single_crossing :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      Hfun a = 1 - a ∧
      (∀ x ∈ Ioo (0 : ℝ) a, 1 - x < Hfun x) ∧
      (∀ x ∈ Ioo a 1, Hfun x < 1 - x) := by
  obtain ⟨δ, hδ, hpos⟩ := hlog_pos_near_zero
  obtain ⟨δ', hδ', hneg⟩ := hlog_neg_near_one
  -- a point `p` where `h > 0` and a point `q > p` where `h < 0`
  set p := min δ δ' / 2 with hp
  set q := (δ' + 1) / 2 with hq
  have hp0 : 0 < p := by rw [hp]; exact half_pos (lt_min hδ hδ'.1)
  have hpδ : p < δ := by rw [hp]; linarith [min_le_left δ δ', half_lt_self (lt_min hδ hδ'.1)]
  have hpδ' : p < δ' := by rw [hp]; linarith [min_le_right δ δ', half_lt_self (lt_min hδ hδ'.1)]
  have hq1 : q < 1 := by rw [hq]; linarith [hδ'.2]
  have hqδ' : δ' < q := by rw [hq]; linarith [hδ'.2]
  have hpq : p < q := by linarith
  have hhp : 0 < hlog p := hpos p ⟨hp0, hpδ⟩
  have hhq : hlog q < 0 := hneg q ⟨hqδ', hq1⟩
  have hcont : ContinuousOn hlog (Icc p q) :=
    hlog_continuousOn.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨a, ⟨hpa, haq⟩, ha0⟩ := intermediate_value_Ioo' hpq.le hcont ⟨hhq, hhp⟩
  have ha : a ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have ha' : a ∈ Ico (0:ℝ) 1 := ⟨ha.1.le, ha.2⟩
  -- sign of `hlog` from strict concavity through `(0,0)` and `(a,0)`
  have hsign_pos : ∀ x ∈ Ioo (0:ℝ) a, 0 < hlog x := by
    intro x hx
    have hxa : x / a < 1 := (div_lt_one ha.1).mpr hx.2
    have h := hlog_strictConcaveOn.2 (show (0:ℝ) ∈ Ico (0:ℝ) 1 by simp) ha' ha.1.ne
      (show 0 < 1 - x / a by linarith) (show 0 < x / a from div_pos hx.1 ha.1) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, hlog_zero, ha0] at h
    rwa [div_mul_cancel₀ _ ha.1.ne'] at h
  have hsign_neg : ∀ x ∈ Ioo a 1, hlog x < 0 := by
    intro x hx
    have hx0 : 0 < x := by linarith [ha.1, hx.1]
    have hx' : x ∈ Ico (0:ℝ) 1 := ⟨hx0.le, hx.2⟩
    have hax : a / x < 1 := (div_lt_one hx0).mpr hx.1
    have h := hlog_strictConcaveOn.2 (show (0:ℝ) ∈ Ico (0:ℝ) 1 by simp) hx' hx0.ne
      (show 0 < 1 - a / x by linarith) (show 0 < a / x from div_pos ha.1 hx0) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, hlog_zero] at h
    rw [div_mul_cancel₀ _ hx0.ne', ha0] at h
    by_contra hcon
    have := mul_nonneg (div_pos ha.1 hx0).le (not_lt.mp hcon)
    linarith
  -- translate `hlog` signs into `Hfun` versus `1 - x`
  have hratio : ∀ x ∈ Ico (0:ℝ) 1, 0 < Hfun x / (1 - x) :=
    fun x hx => div_pos (Hfun_pos hx) (by linarith [hx.2])
  refine ⟨a, ha, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h := Real.exp_log (hratio a ha')
    unfold hlog at ha0
    rw [ha0, Real.exp_zero] at h
    have h1a : (1 - a) ≠ 0 := by linarith [ha.2]
    field_simp at h
    linarith
  · have hx' : x ∈ Ico (0:ℝ) 1 := ⟨hx.1.le, by linarith [hx.2, ha.2]⟩
    have h := hsign_pos x hx
    unfold hlog at h
    rw [Real.log_pos_iff (hratio x hx').le, one_lt_div (by linarith [hx'.2])] at h
    exact h
  · have hx' : x ∈ Ico (0:ℝ) 1 := ⟨by linarith [hx.1, ha.1], hx.2⟩
    have h := hsign_neg x hx
    unfold hlog at h
    rw [Real.log_neg_iff (hratio x hx'), div_lt_one (by linarith [hx'.2])] at h
    exact h

/-- **Theorem 1.4 for `T = {2,3,…}`.** `∫₀ᶜ H > c - c²/2` on `(0,1]`. -/
theorem running_pos_Hfun {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    c - c ^ 2 / 2 < ∫ x in (0 : ℝ)..c, Hfun x := by
  obtain ⟨a, ha, haeq, hposo, hnego⟩ := single_crossing
  set E : ℝ → ℝ := fun x => Hfun x - (1 - x) with hE
  have hEc : ContinuousOn E (Icc 0 1) :=
    Hfun_continuousOn.sub (by fun_prop)
  have hlin : ∀ d : ℝ, (∫ x in (0:ℝ)..d, (1 - x)) = d - d ^ 2 / 2 := by
    intro d
    rw [integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id]
    simp
  have hsplit : ∀ d ∈ Icc (0:ℝ) 1, (∫ x in (0:ℝ)..d, E x)
      = (∫ x in (0:ℝ)..d, Hfun x) - (d - d ^ 2 / 2) := by
    intro d hd
    rw [← hlin d]
    exact integral_sub (Hfun_intervalIntegrable ⟨le_rfl, by norm_num⟩ hd)
      (intervalIntegrable_const.sub intervalIntegrable_id)
  have hend : 0 < ∫ x in (0:ℝ)..1, E x := by
    rw [hsplit 1 ⟨by norm_num, le_rfl⟩]
    have := endpoint_estimate
    norm_num at this ⊢
    linarith
  have key := integral_pos_of_single_crossing hEc ha
    (fun x hx => by simp only [hE]; linarith [hposo x hx])
    (fun x hx => by
      simp only [hE]
      rcases eq_or_lt_of_le hx.2 with h | h
      · subst h; linarith
      · linarith [hposo x ⟨hx.1, h⟩])
    (fun x hx => by
      simp only [hE]
      rcases eq_or_lt_of_le hx.1 with h | h
      · subst h; linarith
      · rcases eq_or_lt_of_le hx.2 with h1 | h1
        · subst h1; rw [Hfun_one]; norm_num
        · linarith [hnego x ⟨h, h1⟩])
    (fun x hx => by simp only [hE]; linarith [hnego x hx])
    hend hc
  rw [hsplit c ⟨hc.1.le, hc.2⟩] at key
  linarith

end RntPaper
