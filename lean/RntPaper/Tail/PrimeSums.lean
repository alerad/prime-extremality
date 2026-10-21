import RntPaper.Tail.Defs

/-!
# Lemma A: exponential prime sums under `θ ~ id` (blueprint `OP3_PLAN.md`)
-/

namespace RntPaper

open QProduct Real Filter Topology Asymptotics MeasureTheory Set

/-- `log n` on primes, `0` elsewhere. -/
private noncomputable def plog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private lemma plog_nonneg (n : ℕ) : 0 ≤ plog n := by
  unfold plog; split_ifs
  · exact log_natCast_nonneg n
  · exact le_rfl

private lemma plog_le (n : ℕ) : plog n ≤ n := by
  unfold plog; split_ifs
  · exact log_le_self (Nat.cast_nonneg n)
  · exact Nat.cast_nonneg n

private lemma theta_nat (n : ℕ) : Chebyshev.theta n = ∑ k ∈ Finset.Ioc 0 n, plog k := by
  rw [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]; rfl

private lemma theta_succ (n : ℕ) :
    Chebyshev.theta ((n : ℝ) + 1) = Chebyshev.theta n + plog (n + 1) := by
  have := theta_nat (n + 1)
  push_cast at this
  rw [this, theta_nat, Finset.sum_Ioc_succ_top (Nat.zero_le n)]

private lemma exp_neg_nat_mul (n : ℕ) (u : ℝ) : rexp (-((n : ℝ) * u)) = rexp (-u) ^ n := by
  rw [← Real.exp_nat_mul]; ring_nf

private lemma exp_neg_lt_one {u : ℝ} (hu : 0 < u) : rexp (-u) < 1 :=
  Real.exp_lt_one_iff.2 (neg_lt_zero.2 hu)

private lemma hasSum_geom {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => rexp (-u) ^ n) (1 - rexp (-u))⁻¹ :=
  hasSum_geometric_of_lt_one (exp_pos _).le (exp_neg_lt_one hu)

private lemma hasSum_nat_geom {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => (n : ℝ) * rexp (-u) ^ n) (rexp (-u) / (1 - rexp (-u)) ^ 2) :=
  hasSum_coe_mul_geometric_of_norm_lt_one
    (by rw [Real.norm_of_nonneg (exp_pos _).le]; exact exp_neg_lt_one hu)

private lemma summable_exp_nat {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => rexp (-((n : ℝ) * u))) := by
  simp_rw [exp_neg_nat_mul]; exact (hasSum_geom hu).summable

private lemma summable_log_exp_nat {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => Real.log n * rexp (-((n : ℝ) * u))) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (log_natCast_nonneg n) (exp_pos _).le)
    (fun n => mul_le_mul_of_nonneg_right (log_le_self (Nat.cast_nonneg n)) (exp_pos _).le) ?_
  simp_rw [exp_neg_nat_mul]; exact (hasSum_nat_geom hu).summable

private lemma primes_inj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) :=
  fun _ _ h => Subtype.ext h

private lemma summable_S {u : ℝ} (hu : 0 < u) :
    Summable (fun p : Nat.Primes => rexp (-((p : ℝ) * u))) :=
  (summable_exp_nat hu).comp_injective primes_inj

private lemma summable_W {u : ℝ} (hu : 0 < u) :
    Summable (fun p : Nat.Primes => Real.log p * rexp (-((p : ℝ) * u))) :=
  (summable_log_exp_nat hu).comp_injective primes_inj

private lemma primeLogExpSum_eq_nat (u : ℝ) :
    primeLogExpSum u = ∑' n : ℕ, plog n * rexp (-u) ^ n := by
  unfold primeLogExpSum
  rw [← primes_inj.tsum_eq (f := fun n : ℕ => plog n * rexp (-u) ^ n)]
  · congr 1; ext p; simp [plog, p.2, exp_neg_nat_mul]
  · intro n hn
    by_cases h : n.Prime
    · exact ⟨⟨n, h⟩, rfl⟩
    · exact absurd (by simp [plog, h]) hn

/-- Summation by parts: `W(u) = (1 - e^{-u}) ∑ θ(n) e^{-nu}`. -/
private lemma primeLogExpSum_eq_theta {u : ℝ} (hu : 0 < u) :
    primeLogExpSum u =
      (1 - rexp (-u)) * ∑' n : ℕ, Chebyshev.theta n * rexp (-u) ^ n := by
  set x := rexp (-u) with hx
  have hx0 : 0 ≤ x := (exp_pos _).le
  have hf : Summable (fun n : ℕ => Chebyshev.theta n * x ^ n) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Chebyshev.theta_nonneg _) (pow_nonneg hx0 _))
      (fun n => mul_le_mul_of_nonneg_right
        (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) (pow_nonneg hx0 _)) ?_
    simp_rw [mul_assoc]; exact ((hasSum_nat_geom hu).summable).mul_left _
  have hg : Summable (fun n : ℕ => plog n * x ^ n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (plog_nonneg n) (pow_nonneg hx0 _))
      (fun n => mul_le_mul_of_nonneg_right (plog_le n) (pow_nonneg hx0 _))
      (hasSum_nat_geom hu).summable
  have hf1 : Summable (fun n : ℕ => Chebyshev.theta ((n + 1 : ℕ) : ℝ) * x ^ (n + 1)) :=
    (summable_nat_add_iff 1).2 hf
  rw [primeLogExpSum_eq_nat, ← hx]
  calc ∑' n : ℕ, plog n * x ^ n = ∑' n : ℕ, plog (n + 1) * x ^ (n + 1) := by
        rw [hg.tsum_eq_zero_add]; simp [plog]
    _ = ∑' n : ℕ, (Chebyshev.theta ((n + 1 : ℕ) : ℝ) * x ^ (n + 1)
          - x * (Chebyshev.theta n * x ^ n)) := by
        congr 1; ext n; push_cast; rw [theta_succ]; ring
    _ = ∑' n : ℕ, Chebyshev.theta ((n + 1 : ℕ) : ℝ) * x ^ (n + 1)
          - ∑' n : ℕ, x * (Chebyshev.theta n * x ^ n) := hf1.tsum_sub (hf.mul_left x)
    _ = (1 - x) * ∑' n : ℕ, Chebyshev.theta n * x ^ n := by
        rw [tsum_mul_left, hf.tsum_eq_zero_add]; simp [Chebyshev.theta_zero]; ring

private lemma theta_bound (hθ : Chebyshev.theta ~[atTop] id) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |Chebyshev.theta n - n| ≤ C + ε * n := by
  have h2 := tendsto_natCast_atTop_atTop.eventually (hθ.isLittleO.def hε)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 h2
  refine ⟨∑ n ∈ Finset.range n0, |Chebyshev.theta n - n|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), fun n => ?_⟩
  have hC : 0 ≤ ∑ n ∈ Finset.range n0, |Chebyshev.theta n - n| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases hn : n0 ≤ n
  · have := hn0 n hn
    simp only [Pi.sub_apply, id, Real.norm_eq_abs, Nat.abs_cast] at this
    linarith
  · have := Finset.single_le_sum (f := fun n : ℕ => |Chebyshev.theta n - n|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (not_le.1 hn))
    have : 0 ≤ ε * n := by positivity
    linarith

/-- The two-sided estimate behind A1. -/
private lemma uW_bounds {ε C u : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, |Chebyshev.theta n - n| ≤ C + ε * n) (hu : 0 < u) :
    (ε ≤ 1 → (1 - ε) * rexp (-u) - C * u ≤ u * primeLogExpSum u) ∧
      u * primeLogExpSum u ≤ (1 + ε) + C * u := by
  set x := rexp (-u) with hx
  have hx0 : 0 < x := exp_pos _
  have hx1 : x < 1 := exp_neg_lt_one hu
  have h1x : 1 - x ≤ u := by have := add_one_le_exp (-u); linarith
  have hux : u * x ≤ 1 - x := by
    have h := add_one_le_exp u
    have : x * rexp u = 1 := by rw [hx, ← exp_add]; simp
    nlinarith
  have hpos : 0 < 1 - x := by linarith
  have hT := (show Summable (fun n : ℕ => Chebyshev.theta n * x ^ n) by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Chebyshev.theta_nonneg _) (pow_nonneg hx0.le _))
      (fun n => mul_le_mul_of_nonneg_right
        (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) (pow_nonneg hx0.le _)) ?_
    simp_rw [mul_assoc]; exact ((hasSum_nat_geom hu).summable).mul_left _).hasSum
  have hG := hasSum_geom hu
  have hN := hasSum_nat_geom hu
  rw [← hx] at hG hN
  have hlo := hasSum_le (fun n : ℕ => show (1 - ε) * ((n : ℝ) * x ^ n) - C * x ^ n ≤
      Chebyshev.theta n * x ^ n by
        have := (abs_le.1 (hb n)).1
        have hp := pow_nonneg hx0.le n
        nlinarith) ((hN.mul_left (1 - ε)).sub (hG.mul_left C)) hT
  have hhi := hasSum_le (fun n : ℕ => show Chebyshev.theta n * x ^ n ≤
      (1 + ε) * ((n : ℝ) * x ^ n) + C * x ^ n by
        have := (abs_le.1 (hb n)).2
        have hp := pow_nonneg hx0.le n
        nlinarith) hT ((hN.mul_left (1 + ε)).add (hG.mul_left C))
  rw [primeLogExpSum_eq_theta hu, ← hx]
  set T := ∑' n : ℕ, Chebyshev.theta n * x ^ n
  have key : u * ((1 - x) * T) = u * (1 - x) * T := by ring
  have e1 : u * (1 - x) * (x / (1 - x) ^ 2) = u * x / (1 - x) := by
    field_simp
  have e2 : u * (1 - x) * (1 - x)⁻¹ = u := by field_simp
  have hr1 : x ≤ u * x / (1 - x) := by rw [le_div_iff₀ hpos]; nlinarith
  have hr2 : u * x / (1 - x) ≤ 1 := by rw [div_le_one hpos]; exact hux
  have hup : 0 ≤ u * (1 - x) := by positivity
  have E1 : u * (1 - x) * ((1 - ε) * (x / (1 - x) ^ 2) - C * (1 - x)⁻¹)
      = (1 - ε) * (u * x / (1 - x)) - C * u := by
    field_simp
  have E2 : u * (1 - x) * ((1 + ε) * (x / (1 - x) ^ 2) + C * (1 - x)⁻¹)
      = (1 + ε) * (u * x / (1 - x)) + C * u := by
    field_simp
  rw [key]
  constructor
  · intro hε1
    have := mul_le_mul_of_nonneg_left hlo hup
    rw [E1] at this
    nlinarith [mul_le_mul_of_nonneg_left hr1 (by linarith : (0:ℝ) ≤ 1 - ε)]
  · have := mul_le_mul_of_nonneg_left hhi hup
    rw [E2] at this
    nlinarith

private lemma log_inv_pos {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : 0 < Real.log u⁻¹ := by
  rw [Real.log_inv]; exact neg_pos.2 (Real.log_neg hu hu1)

private lemma exp_neg_log_inv {u : ℝ} (hu : 0 < u) : rexp (-Real.log u⁻¹) = u := by
  rw [Real.log_inv, neg_neg, exp_log hu]

/-- A2 upper, termwise: split at `log p = (1-δ) L(u)`. -/
private lemma S_upper {u δ : ℝ} (hu : 0 < u) (hu1 : u < 1) (hδ1 : δ < 1) :
    primeExpSum u ≤ ((1 - δ) * Real.log u⁻¹)⁻¹ * primeLogExpSum u
      + (rexp 1 / Real.log 2) * primeLogExpSum (rexp (-((1 - δ) * Real.log u⁻¹))) := by
  set L := Real.log u⁻¹ with hLdef
  have hL : 0 < L := log_inv_pos hu hu1
  set v := rexp (-((1 - δ) * L)) with hvdef
  have hv : 0 < v := exp_pos _
  have hc1 : 0 < (1 - δ) * L := mul_pos (by linarith) hL
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold primeExpSum primeLogExpSum
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_W hu).mul_left _).tsum_add ((summable_W hv).mul_left _)]
  refine (summable_S hu).tsum_le_tsum (fun p => ?_)
    (((summable_W hu).mul_left _).add ((summable_W hv).mul_left _))
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log two_pos hp2
  have he1 := exp_pos (-((p : ℝ) * u))
  have he2 := exp_pos (-((p : ℝ) * v))
  by_cases h : (1 - δ) * L ≤ Real.log p
  · have h1 : 1 ≤ ((1 - δ) * L)⁻¹ * Real.log p := by
      rw [inv_mul_eq_div, le_div_iff₀ hc1]; linarith
    have : rexp (-((p : ℝ) * u)) ≤ ((1 - δ) * L)⁻¹ * (Real.log p * rexp (-((p : ℝ) * u))) := by
      rw [← mul_assoc]; nlinarith
    have : 0 ≤ rexp 1 / Real.log 2 * (Real.log p * rexp (-((p : ℝ) * v))) :=
      mul_nonneg (div_nonneg (exp_pos _).le hl2.le) (mul_nonneg (by linarith) he2.le)
    linarith
  · push Not at h
    have hpv : (p : ℝ) * v < 1 := by
      have : (p : ℝ) * v = rexp (Real.log p - (1 - δ) * L) := by
        rw [sub_eq_add_neg, exp_add, exp_log hp0]
      rw [this]; exact Real.exp_lt_one_iff.2 (by linarith)
    have h1 : rexp (-((p : ℝ) * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h2 : 1 ≤ rexp 1 * rexp (-((p : ℝ) * v)) := by
      rw [← exp_add]; exact Real.one_le_exp (by linarith)
    have h3 : rexp 1 * rexp (-((p : ℝ) * v)) ≤
        rexp 1 / Real.log 2 * (Real.log p * rexp (-((p : ℝ) * v))) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      have := mul_le_mul_of_nonneg_left hlogp
        (mul_nonneg (exp_pos 1).le he2.le)
      nlinarith
    have : 0 ≤ ((1 - δ) * L)⁻¹ * (Real.log p * rexp (-((p : ℝ) * u))) :=
      mul_nonneg (inv_nonneg.2 hc1.le) (mul_nonneg (by linarith) he1.le)
    linarith

/-- A2 lower, termwise: split at `log p = (1+δ) L(u)`. -/
private lemma W_upper {u δ : ℝ} (hu : 0 < u) (hu1 : u < 1) (hδ0 : 0 < δ) :
    primeLogExpSum u ≤ (1 + δ) * Real.log u⁻¹ * primeExpSum u
      + rexp (-(rexp (δ * Real.log u⁻¹) / 2)) * primeLogExpSum (u / 2) := by
  have hu' := exp_neg_log_inv hu
  set L := Real.log u⁻¹ with hLdef
  have hL : 0 < L := log_inv_pos hu hu1
  set E := rexp (-(rexp (δ * L) / 2)) with hE
  have hu2 : 0 < u / 2 := by linarith
  unfold primeExpSum primeLogExpSum
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_S hu).mul_left _).tsum_add ((summable_W hu2).mul_left _)]
  refine (summable_W hu).tsum_le_tsum (fun p => ?_)
    (((summable_S hu).mul_left _).add ((summable_W hu2).mul_left _))
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have he1 := exp_pos (-((p : ℝ) * u))
  have he2 := exp_pos (-((p : ℝ) * (u / 2)))
  have hE0 : 0 ≤ E := (exp_pos _).le
  by_cases h : Real.log p ≤ (1 + δ) * L
  · have := mul_le_mul_of_nonneg_right h he1.le
    have : 0 ≤ E * (Real.log p * rexp (-((p : ℝ) * (u / 2)))) := by positivity
    linarith
  · push Not at h
    have hpu : rexp (δ * L) < p * u := by
      have hlt : rexp ((1 + δ) * L) < p := by
        rw [← exp_log hp0]; exact exp_lt_exp.2 h
      calc rexp (δ * L) = rexp ((1 + δ) * L) * rexp (-L) := by rw [← exp_add]; ring_nf
        _ < p * rexp (-L) := mul_lt_mul_of_pos_right hlt (exp_pos _)
        _ = p * u := by rw [hu']
    have hsplit : rexp (-((p : ℝ) * u)) =
        rexp (-((p : ℝ) * (u / 2))) * rexp (-((p : ℝ) * (u / 2))) := by
      rw [← exp_add]; ring_nf
    have hle : rexp (-((p : ℝ) * (u / 2))) ≤ E := exp_le_exp.2 (by linarith)
    have : Real.log p * rexp (-((p : ℝ) * u)) ≤
        E * (Real.log p * rexp (-((p : ℝ) * (u / 2)))) := by
      rw [hsplit]
      have := mul_le_mul_of_nonneg_left hle (mul_nonneg hlogp he2.le)
      nlinarith
    have : 0 ≤ (1 + δ) * L * rexp (-((p : ℝ) * u)) := by positivity
    linarith

section PNT

variable (hθ : Chebyshev.theta ~[atTop] id)
include hθ

/-- Lemma A1: `u W(u) → 1` as `u → 0⁺`. -/
theorem primeLogExpSum_asymp :
    Tendsto (fun u => u * primeLogExpSum u) (𝓝[>] 0) (𝓝 1) := by
  rw [tendsto_order]; constructor
  · intro a ha
    set ε := min ((1 - a) / 2) (1 / 2) with hεdef
    have hε : 0 < ε := lt_min (by linarith) (by norm_num)
    have hε1 : ε ≤ (1 - a) / 2 := min_le_left _ _
    obtain ⟨C, hC, hb⟩ := theta_bound hθ hε
    have hlim : Tendsto (fun u : ℝ => (1 - ε) * rexp (-u) - C * u) (𝓝[>] 0) (𝓝 (1 - ε)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      have : Continuous (fun u : ℝ => (1 - ε) * rexp (-u) - C * u) := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [hlim.eventually_const_lt (by linarith : a < 1 - ε), self_mem_nhdsWithin]
      with u h1 hu
    exact h1.trans_le ((uW_bounds hε.le hC hb hu).1 ((min_le_right _ _).trans (by norm_num)))
  · intro a ha
    set ε := (a - 1) / 2 with hεdef
    have hε : 0 < ε := by linarith
    obtain ⟨C, hC, hb⟩ := theta_bound hθ hε
    have hlim : Tendsto (fun u : ℝ => (1 + ε) + C * u) (𝓝[>] 0) (𝓝 (1 + ε)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      have : Continuous (fun u : ℝ => (1 + ε) + C * u) := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [hlim.eventually_lt_const (by linarith : 1 + ε < a), self_mem_nhdsWithin]
      with u h1 hu
    exact (uW_bounds hε.le hC hb hu).2.trans_lt h1

/-- Lemma A2: `u log(1/u) S(u) → 1` as `u → 0⁺`. -/
theorem primeExpSum_asymp :
    Tendsto (fun u => u * Real.log u⁻¹ * primeExpSum u) (𝓝[>] 0) (𝓝 1) := by
  have hA1 := primeLogExpSum_asymp hθ
  have hL : Tendsto (fun u : ℝ => Real.log u⁻¹) (𝓝[>] 0) atTop := by
    simp_rw [Real.log_inv]; exact tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  rw [tendsto_order]; constructor
  · intro a ha
    set δ := (1 - a) / 2 with hδdef
    have hδ : 0 < δ := by linarith
    have hδa : a < 1 / (1 + δ) := by
      rw [lt_div_iff₀ (by linarith)]; nlinarith
    have hE : Tendsto (fun u : ℝ => rexp (-(rexp (δ * Real.log u⁻¹) / 2))) (𝓝[>] 0) (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_exp_atTop.comp (hL.const_mul_atTop hδ)).atTop_div_const two_pos)
    have hhalf : Tendsto (fun u : ℝ => u / 2) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
        simpa using ((continuous_id.div_const (2 : ℝ)).tendsto 0)
      · filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
        exact div_pos hu two_pos
    have hlim := ((hA1.sub ((hE.const_mul 2).mul (hA1.comp hhalf))).div_const (1 + δ))
    simp only [mul_zero, zero_mul, sub_zero] at hlim
    filter_upwards [hlim.eventually_const_lt hδa, hsmall] with u h1 hu
    obtain ⟨hu, hu1⟩ := hu
    refine h1.trans_le ?_
    have h2 := mul_le_mul_of_nonneg_left (W_upper hu hu1 hδ) hu.le
    rw [div_le_iff₀ (by linarith)]
    simp only [Function.comp]
    nlinarith
  · intro a ha
    have ha0 : 0 < a := by linarith
    set δ := (1 - 1 / a) / 2 with hδdef
    have hia : 1 / a < 1 := by rw [div_lt_one ha0]; exact ha
    have hia0 : 0 < 1 / a := by positivity
    have hδ0 : 0 < δ := by linarith
    have hδ1 : δ < 1 := by linarith
    have hδa : 1 / (1 - δ) < a := by
      rw [div_lt_iff₀ (by linarith)]
      have : a * (1 / a) = 1 := by field_simp
      nlinarith
    set v := fun u : ℝ => rexp (-((1 - δ) * Real.log u⁻¹)) with hvdef
    have hv : Tendsto v (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_exp_neg_atTop_nhds_zero.comp
        (hL.const_mul_atTop (by linarith)), Eventually.of_forall (fun u => exp_pos _)⟩
    have hR : Tendsto (fun u : ℝ => Real.log u⁻¹ * rexp (-(δ * Real.log u⁻¹))) (𝓝[>] 0)
        (𝓝 0) := by
      have := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (hL.const_mul_atTop hδ0)).const_mul δ⁻¹
      rw [mul_zero] at this
      refine this.congr (fun u => ?_)
      simp only [Function.comp, pow_one]
      field_simp
    have hlim := ((hA1.div_const (1 - δ)).add
      (((hA1.comp hv).const_mul (rexp 1 / Real.log 2)).mul hR))
    simp only [mul_one, mul_zero, add_zero] at hlim
    filter_upwards [hlim.eventually_lt_const hδa, hsmall] with u h1 hu
    obtain ⟨hu, hu1⟩ := hu
    refine lt_of_le_of_lt ?_ h1
    have hL0 := log_inv_pos hu hu1
    have h2 := mul_le_mul_of_nonneg_left (S_upper hu hu1 hδ1) (mul_pos hu hL0).le
    have hu' : v u * rexp (-(δ * Real.log u⁻¹)) = u := by
      show rexp (-((1 - δ) * Real.log u⁻¹)) * rexp (-(δ * Real.log u⁻¹)) = u
      rw [← exp_add, show -((1 - δ) * Real.log u⁻¹) + -(δ * Real.log u⁻¹) = -Real.log u⁻¹ by ring]
      exact exp_neg_log_inv hu
    have hc : 0 < 1 - δ := by linarith
    refine h2.trans (le_of_eq ?_)
    simp only [Function.comp_apply]
    set W1 := primeLogExpSum u
    set W2 := primeLogExpSum (v u)
    set L := Real.log u⁻¹
    set R := rexp (-(δ * L))
    calc u * L * (((1 - δ) * L)⁻¹ * W1 + rexp 1 / Real.log 2 * W2)
        = u * W1 / (1 - δ) + rexp 1 / Real.log 2 * (u * L * W2) := by
          field_simp
      _ = _ := by
          rw [show u * L * W2 = v u * W2 * (L * R) by
            rw [show v u * W2 * (L * R) = (v u * R) * L * W2 by ring, hu']]
          ring

/-- Primes in short intervals `(N, (1+ε)N]`, from `θ ~ id`. -/
theorem exists_prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ q : ℕ, q.Prime ∧ N < q ∧ (q : ℝ) ≤ (1 + ε) * N := by
  set η := ε / (4 + 2 * ε) with hηdef
  have hη : 0 < η := by positivity
  have h := hθ.isLittleO.def hη
  have h1 := tendsto_natCast_atTop_atTop.eventually h
  have h2 := (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith : (0 : ℝ) < 1 + ε)).eventually h
  filter_upwards [h1, h2, eventually_ge_atTop 1] with N hN1 hN2 hN
  simp only [Pi.sub_apply, id, Real.norm_eq_abs] at hN1 hN2
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)] at hN1
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ε) * N)] at hN2
  have hlt : Chebyshev.theta N < Chebyshev.theta ((1 + ε) * N) := by
    have a1 := (abs_le.1 hN1).2
    have a2 := (abs_le.1 hN2).1
    have : η * (4 + 2 * ε) = ε := by rw [hηdef]; field_simp
    nlinarith
  by_contra hne
  push Not at hne
  apply hlt.not_ge
  rw [Chebyshev.theta_eq_theta_coe_floor ((1 + ε) * N)]
  unfold Chebyshev.theta
  rw [Nat.floor_natCast, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
    by_contra hpN
    push Not at hpN
    have h3 := hne p hp.2 hpN
    have h4 : (p : ℝ) ≤ (1 + ε) * N := (Nat.le_floor_iff (by positivity)).1 hp.1.2
    linarith
  · intro p hp _
    simp only [Finset.mem_filter] at hp
    exact log_nonneg (by exact_mod_cast hp.2.one_lt.le)

end PNT

end RntPaper
