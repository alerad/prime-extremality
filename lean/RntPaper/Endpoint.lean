import RntPaper.Basic
import LeanCert.Tactic
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The endpoint estimate (paper Lemma 2.2, Remark 2.4)

The rational identities are discharged by the `leancert` tactic, which
normalises polynomial integrands and integrates exactly over `ℚ`.  What
remains is the Weierstrass lower bound `H ≥ P₅ · (1 - x⁶/(1-x))`, i.e. the
infinite-product analogue of LeanCert's `one_sub_prod_one_sub_le_sum`.
-/

namespace RntPaper

open QProduct Set Filter Topology

/-- `∫₀¹ ∏_{n=2}^{5}(1 - xⁿ) dx = 96601/180180`. -/
theorem integral_P5 :
    (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * (1 - x ^ 3) * (1 - x ^ 4) * (1 - x ^ 5))
      = 96601 / 180180 := by
  leancert

/-- `∫₀¹ x⁶ ∏_{n=2}^{5}(1 - xⁿ)/(1 - x) dx = 275501/9699690`, with
`P₅/(1-x) = (1+x)(1-x³)(1-x⁴)(1-x⁵)`. -/
theorem integral_x6_P5_div_one_sub :
    (∫ x in (0 : ℝ)..1, x ^ 6 * (1 + x) * (1 - x ^ 3) * (1 - x ^ 4) * (1 - x ^ 5))
      = 275501 / 9699690 := by
  leancert

/-- The degree-19 lower bound integrates to `1/2 + 34619/4476780`. -/
theorem integral_polyLower :
    (∫ x in (0 : ℝ)..1, (1 + x) * (1 - x ^ 3) * (1 - x ^ 4) * (1 - x ^ 5) * (1 - x - x ^ 6))
      = 1 / 2 + 34619 / 4476780 := by
  leancert


/-! ## Analytic facts about `H` on `[0,1)`

Everything is derived from the `ℕ`-indexed form `H(x) = ∏'_{n} (1 - x^{n+2})`,
its exponential representation `H = exp ∑ log(1 - x^{n+2})` (positivity, the
logarithm of `H`), and the two-sided truncation bounds
`P_N(x) (1 - x^{N+2}/(1-x)) ≤ H(x) ≤ P_N(x)` with `P_N = ∏_{n<N}(1 - x^{n+2})`.
-/

/-- `ℕ ≃ {n // 2 ≤ n}`, `n ↦ n + 2`. -/
def shift2 : ℕ ≃ ({n : ℕ | 2 ≤ n} : Set ℕ) where
  toFun n := ⟨n + 2, by simp⟩
  invFun n := n.1 - 2
  left_inv n := by simp
  right_inv n := Subtype.ext (Nat.sub_add_cancel n.2)

theorem Hfun_eq_tprod_nat (x : ℝ) : Hfun x = ∏' n : ℕ, (1 - x ^ (n + 2)) := by
  unfold Hfun qProdSet
  exact (Equiv.tprod_eq shift2 _).symm

theorem summable_pow_shift {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (k : ℕ) :
    Summable fun n : ℕ => x ^ (n + k) := by
  simpa [pow_add] using (summable_geometric_of_lt_one hx.1 hx.2).mul_right (x ^ k)

theorem tsum_pow_shift {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (k : ℕ) :
    ∑' n : ℕ, x ^ (n + k) = x ^ k / (1 - x) := by
  simp only [pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hx.1 hx.2, div_eq_mul_inv, mul_comm]

theorem summable_log_one_sub_pow {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (k : ℕ) :
    Summable fun n : ℕ => Real.log (1 - x ^ (n + k)) := by
  have := Real.summable_log_one_add_of_summable (summable_pow_shift hx k).neg
  simpa [sub_eq_add_neg] using this

theorem one_sub_pow_pos' {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) {n : ℕ} (hn : n ≠ 0) :
    0 < 1 - x ^ n := by
  have := pow_lt_one₀ hx.1 hx.2 hn; linarith

theorem Hfun_eq_exp {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    Hfun x = Real.exp (∑' n : ℕ, Real.log (1 - x ^ (n + 2))) := by
  rw [Hfun_eq_tprod_nat]
  exact (Real.rexp_tsum_eq_tprod (fun n => one_sub_pow_pos' hx (by omega))
    (summable_log_one_sub_pow hx 2)).symm

theorem Hfun_pos {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) : 0 < Hfun x := by
  rw [Hfun_eq_exp hx]; exact Real.exp_pos _

theorem log_Hfun {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    Real.log (Hfun x) = ∑' n : ℕ, Real.log (1 - x ^ (n + 2)) := by
  rw [Hfun_eq_exp hx, Real.log_exp]

theorem multipliable_Hfun {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    Multipliable fun n : ℕ => 1 - x ^ (n + 2) := by
  have := Real.multipliable_one_add_of_summable (summable_pow_shift hx 2).neg
  simpa [sub_eq_add_neg] using this

/-- The truncations `P_N(x) = ∏_{n<N}(1 - x^{n+2})` converge to `H(x)`. -/
theorem tendsto_partial_Hfun {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    Tendsto (fun N => ∏ n ∈ Finset.range N, (1 - x ^ (n + 2))) atTop (𝓝 (Hfun x)) := by
  rw [Hfun_eq_tprod_nat]
  exact (multipliable_Hfun hx).hasProd.tendsto_prod_nat

theorem partial_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (s : Finset ℕ) :
    0 ≤ ∏ n ∈ s, (1 - x ^ (n + 2)) :=
  Finset.prod_nonneg fun _ _ => sub_nonneg.mpr (pow_le_one₀ hx.1 hx.2)

theorem partial_le_one {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (s : Finset ℕ) :
    ∏ n ∈ s, (1 - x ^ (n + 2)) ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => sub_nonneg.mpr (pow_le_one₀ hx.1 hx.2))
    (fun n _ => by linarith [pow_nonneg hx.1 (n + 2)])

/-- `H ≤ P_N`: every omitted factor lies in `[0,1]`. -/
theorem Hfun_le_partial {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (N : ℕ) :
    Hfun x ≤ ∏ n ∈ Finset.range N, (1 - x ^ (n + 2)) := by
  have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx.2.le⟩
  apply le_of_tendsto (tendsto_partial_Hfun hx)
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [← Finset.prod_range_mul_prod_Ico _ hM]
  exact mul_le_of_le_one_right (partial_nonneg hx' _) (partial_le_one hx' _)

/-- The infinite Weierstrass bound `H ≥ P_N · (1 - ∑_{n ≥ N+2} xⁿ)`. -/
theorem partial_mul_le_Hfun {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (N : ℕ) :
    (∏ n ∈ Finset.range N, (1 - x ^ (n + 2))) * (1 - x ^ (N + 2) / (1 - x)) ≤ Hfun x := by
  have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx.2.le⟩
  apply ge_of_tendsto (tendsto_partial_Hfun hx)
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [← Finset.prod_range_mul_prod_Ico _ hM]
  apply mul_le_mul_of_nonneg_left _ (partial_nonneg hx' _)
  have h1 := one_sub_prod_one_sub_le_sum (Finset.Ico N M) (fun n => x ^ (n + 2))
    (fun n _ => pow_nonneg hx.1 _) (fun n _ => pow_le_one₀ hx.1 hx.2.le)
  have h2 : ∑ n ∈ Finset.Ico N M, x ^ (n + 2) ≤ x ^ (N + 2) / (1 - x) := by
    rw [Finset.sum_Ico_add' (fun n => x ^ n) N M 2]
    exact geom_sum_Ico_le_of_lt_one hx.1 hx.2
  linarith

theorem Hfun_zero : Hfun 0 = 1 := by
  rw [Hfun_eq_tprod_nat]
  simp

theorem Hfun_one : Hfun 1 = 0 := by
  rw [Hfun_eq_tprod_nat]
  simp

theorem Hfun_nonneg_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ Hfun x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, Hfun_one]
  · exact (Hfun_pos ⟨hx.1, h⟩).le

theorem Hfun_le_one_sub_sq_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : Hfun x ≤ 1 - x ^ 2 := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, Hfun_one]; norm_num
  · simpa using Hfun_le_partial ⟨hx.1, h⟩ 1

/-- Uniform convergence of the truncations on `[0,r]`, `r < 1`. -/
theorem tendstoUniformlyOn_partial_Hfun {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    TendstoUniformlyOn (fun N x => ∏ n ∈ Finset.range N, (1 - x ^ (n + 2))) Hfun atTop
      (Icc 0 r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ => r ^ (N + 2) / (1 - r)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2).comp
      (tendsto_add_atTop_nat 2)).div_const (1 - r)
    simpa using this
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with N hN x hx
  have hx1 : x ∈ Ico (0:ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩
  have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx1.2.le⟩
  have hupper := Hfun_le_partial hx1 N
  have hlower := partial_mul_le_Hfun hx1 N
  have hP0 := partial_nonneg hx' (Finset.range N)
  have hP1 := partial_le_one hx' (Finset.range N)
  have hq : x ^ (N + 2) / (1 - x) ≤ r ^ (N + 2) / (1 - r) := by
    apply div_le_div₀ (pow_nonneg hr.1 _) (pow_le_pow_left₀ hx.1 hx.2 _)
      (by linarith [hr.2]) (by linarith [hx.2])
  have hq0 : 0 ≤ x ^ (N + 2) / (1 - x) := div_nonneg (pow_nonneg hx.1 _) (by linarith [hx1.2])
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · linarith
  · nlinarith

theorem continuous_partial (N : ℕ) :
    Continuous fun x : ℝ => ∏ n ∈ Finset.range N, (1 - x ^ (n + 2)) := by
  fun_prop

theorem Hfun_continuousOn_Icc_lt {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    ContinuousOn Hfun (Icc 0 r) :=
  (tendstoUniformlyOn_partial_Hfun hr).continuousOn
    (Frequently.of_forall fun N => (continuous_partial N).continuousOn)

/-- `H` is continuous on `[0,1]`: locally uniform convergence on `[0,1)` and the
squeeze `0 ≤ H ≤ 1 - x²` at `1`. -/
theorem Hfun_continuousOn_Icc : ContinuousOn Hfun (Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst h1
    -- squeeze at the endpoint
    rw [ContinuousWithinAt, Hfun_one]
    have hg : Tendsto (fun y : ℝ => 1 - y ^ 2) (𝓝[Icc (0:ℝ) 1] 1) (𝓝 0) := by
      have : Tendsto (fun y : ℝ => 1 - y ^ 2) (𝓝 1) (𝓝 (1 - 1 ^ 2)) :=
        (by fun_prop : Continuous fun y : ℝ => 1 - y ^ 2).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · exact eventually_nhdsWithin_of_forall fun y hy => Hfun_nonneg_Icc hy
    · exact eventually_nhdsWithin_of_forall fun y hy => Hfun_le_one_sub_sq_Icc hy
  · set r := (x + 1) / 2 with hr
    have hr' : r ∈ Ico (0:ℝ) 1 := ⟨by rw [hr]; linarith [hx.1], by rw [hr]; linarith⟩
    have hxr : x < r := by rw [hr]; linarith
    have hcont := Hfun_continuousOn_Icc_lt hr' x ⟨hx.1, hxr.le⟩
    apply hcont.mono_of_mem_nhdsWithin
    have : Icc (0:ℝ) 1 ∩ Iio r ∈ 𝓝[Icc (0:ℝ) 1] x :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds hxr)
    apply Filter.mem_of_superset this
    rintro y ⟨hy1, hy2⟩
    exact ⟨hy1.1, le_of_lt hy2⟩

theorem Hfun_intervalIntegrable {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable Hfun MeasureTheory.volume a b :=
  (Hfun_continuousOn_Icc.mono (uIcc_subset_Icc ha hb)).intervalIntegrable

/-- The degree-19 polynomial lower bound for `H` (paper, proof of Lemma 2.2).
Route: `H(x) = P₅(x) · ∏_{n≥6}(1 - xⁿ) ≥ P₅(x) · (1 - ∑_{n≥6} xⁿ)`, the
second factor being `1 - x⁶/(1-x)`; multiply through by `1 - x`. -/
theorem polyLower_le_Hfun {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    (1 + x) * (1 - x ^ 3) * (1 - x ^ 4) * (1 - x ^ 5) * (1 - x - x ^ 6) ≤ Hfun x := by
  have h := partial_mul_le_Hfun hx 4
  have hx1 : (1 - x) ≠ 0 := by linarith [hx.2]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at h
  convert h using 1
  field_simp
  ring

/-- **Lemma 2.2.** `∫₀¹ H - 1/2 ≥ 34619/4476780`. -/
theorem endpoint_estimate :
    1 / 2 + 34619 / 4476780 ≤ ∫ x in (0 : ℝ)..1, Hfun x := by
  rw [← integral_polyLower]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (1 + x) * (1 - x ^ 3) * (1 - x ^ 4) * (1 - x ^ 5) * (1 - x - x ^ 6)).intervalIntegrable _ _
  · exact Hfun_intervalIntegrable ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  · intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h; rw [Hfun_one]; norm_num
    · exact polyLower_le_Hfun ⟨hx.1, h⟩

/-! ## Remark 2.4: the degree-18 running certificate -/

/-- `Q̃(c)` with `∫₀ᶜ polyLower − (c − c²/2) = c² Q̃(c)`. Coefficients from
`supplement/crossing_endpoint.py`. -/
noncomputable def Qtilde (c : ℝ) : ℝ :=
  1 / 2 - c / 3 - c ^ 2 / 4 - c ^ 3 / 5 + c ^ 6 / 8 + c ^ 7 / 9 + c ^ 8 / 10
    + c ^ 9 / 11 + c ^ 10 / 12 - c ^ 12 / 14 - c ^ 13 / 15 - c ^ 14 / 8
    - c ^ 15 / 17 + c ^ 17 / 19 + c ^ 18 / 20

theorem Qtilde_one : Qtilde 1 = 34619 / 4476780 := by
  unfold Qtilde; norm_num

/-- `Q̃ > 0` on `[0,1]` (its minimum is `Q̃(1) = 34619/4476780`). Closed by
LeanCert's Bernstein polynomial certificate: all 19 Bernstein coefficients of
`Q̃` on `[0,1]` are positive, so no bisection is needed (paper Remark 2.4). -/
theorem Qtilde_pos : ∀ c ∈ Icc (0 : ℝ) 1, 0 < Qtilde c := by
  unfold Qtilde
  leancert (trust := kernel)

/-- The running integral of the polynomial lower bound factors as stated. -/
theorem integral_polyLower_running (c : ℝ) :
    (∫ x in (0 : ℝ)..c, (1 + x) * (1 - x ^ 3) * (1 - x ^ 4) * (1 - x ^ 5) * (1 - x - x ^ 6))
      = c - c ^ 2 / 2 + c ^ 2 * Qtilde c := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun c : ℝ => c - c ^ 2 / 2 + c ^ 2 * Qtilde c)
      ((1 + x) * (1 - x ^ 3) * (1 - x ^ 4) * (1 - x ^ 5) * (1 - x - x ^ 6)) x := by
    intro x
    have h : ∀ n : ℕ, HasDerivAt (fun c : ℝ => c ^ n) ((n : ℝ) * x ^ (n - 1)) x :=
      fun n => hasDerivAt_pow n x
    have hQ : HasDerivAt Qtilde
        (0 - 1 / 3 - (2:ℕ) * x ^ (2 - 1) / 4 - (3:ℕ) * x ^ (3 - 1) / 5 + (6:ℕ) * x ^ (6 - 1) / 8
          + (7:ℕ) * x ^ (7 - 1) / 9 + (8:ℕ) * x ^ (8 - 1) / 10 + (9:ℕ) * x ^ (9 - 1) / 11
          + (10:ℕ) * x ^ (10 - 1) / 12 - (12:ℕ) * x ^ (12 - 1) / 14 - (13:ℕ) * x ^ (13 - 1) / 15
          - (14:ℕ) * x ^ (14 - 1) / 8 - (15:ℕ) * x ^ (15 - 1) / 17 + (17:ℕ) * x ^ (17 - 1) / 19
          + (18:ℕ) * x ^ (18 - 1) / 20) x := by
      unfold Qtilde
      have h1 : HasDerivAt (fun c : ℝ => c / 3) (1 / 3) x := by
        simpa using (hasDerivAt_id x).div_const 3
      exact (((((((((((((((hasDerivAt_const x (1/2:ℝ)).sub h1).sub
        ((h 2).div_const 4)).sub ((h 3).div_const 5)).add ((h 6).div_const 8)).add
        ((h 7).div_const 9)).add ((h 8).div_const 10)).add ((h 9).div_const 11)).add
        ((h 10).div_const 12)).sub ((h 12).div_const 14)).sub ((h 13).div_const 15)).sub
        ((h 14).div_const 8)).sub ((h 15).div_const 17)).add ((h 17).div_const 19)).add
        ((h 18).div_const 20))
    have := ((hasDerivAt_id x).sub ((h 2).div_const 2)).add ((h 2).mul hQ)
    convert this using 1
    · funext c; simp only [Qtilde, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
    · simp only [Qtilde]; push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)]
  · simp [Qtilde]
  · apply Continuous.intervalIntegrable; fun_prop

end RntPaper
