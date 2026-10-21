import RntPaper.Tail.PrimeSums
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Lemma B: `Φ(t) ~ ζ(2) / (t log(1/t))` under `θ ~ id` (blueprint `OP3_PLAN.md`)

Route: `Φ(t) = ∑_{m} S(mt)/m` (`primePhi_eq_tsum`, a nonnegative double series), then
Tannery's theorem (`tendsto_tsum_of_dominated_convergence`): each term
`t log(1/t) S(mt)/m → 1/m²` by Lemma A2, and it is dominated uniformly for small `t` by
`C (1 + log m)/m²`, using `S(u) ≤ 2/(u log(1/u))` for small `u` and `S(u) ≤ 1/u` otherwise.
-/

namespace RntPaper

open QProduct Real Filter Topology Asymptotics MeasureTheory Set

lemma phi_primeExpSum_nonneg (u : ℝ) : 0 ≤ primeExpSum u :=
  tsum_nonneg fun _ => (exp_pos _).le

lemma phi_summable_exp_primes {u : ℝ} (hu : 0 < u) :
    Summable (fun p : Nat.Primes => rexp (-((p : ℝ) * u))) := by
  have h : Summable (fun n : ℕ => rexp (n * (-u))) :=
    Real.summable_exp_nat_mul_iff.mpr (by linarith)
  have h' := h.comp_injective (i := fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective
  refine h'.congr fun p => ?_
  simp only [Function.comp_apply]
  ring_nf

lemma phi_primeExpSum_le_inv {u : ℝ} (hu : 0 < u) : primeExpSum u ≤ 1 / u := by
  set f : ℕ → ℝ := fun n => rexp (-u) * rexp (-u) ^ n with hf
  have hr0 : 0 ≤ rexp (-u) := (exp_pos _).le
  have hr1 : rexp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hfs : Summable f := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q hpq
    have h2p := p.2.two_le
    have h2q := q.2.two_le
    exact Subtype.ext (by simp only at hpq; omega)
  have hle := tsum_comp_le_tsum_of_inj hfs (fun n => by positivity) hinj
  have hS : primeExpSum u = tsum (f ∘ fun p : Nat.Primes => (p : ℕ) - 1) := by
    unfold primeExpSum
    refine tsum_congr fun p => ?_
    have h1 := p.2.one_le
    simp only [hf, Function.comp_apply, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have htf : tsum f = rexp (-u) * (1 - rexp (-u))⁻¹ := by
    rw [hf, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [hS]
  refine hle.trans (le_of_eq_of_le htf ?_)
  have h1 : 0 < 1 - rexp (-u) := by linarith
  rw [← div_eq_mul_inv, div_le_div_iff₀ h1 hu]
  have := Real.add_one_le_exp u
  have h3 : rexp (-u) * rexp u = 1 := by rw [← exp_add]; simp
  nlinarith

lemma hasSum_neg_log_one_sub {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    HasSum (fun m : ℕ => y ^ m / m) (-Real.log (1 - y)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := y) (by rw [abs_lt]; constructor <;> linarith)
  rw [← hasSum_nat_add_iff' 1]
  simpa using h

lemma primePhi_eq_tsum {t : ℝ} (ht : 0 < t) :
    primePhi t = ∑' m : ℕ, primeExpSum (m * t) / m := by
  set F : Nat.Primes → ℕ → ℝ := fun p m => rexp (-((p : ℝ) * (m * t))) / m with hF
  have hrow : ∀ p : Nat.Primes, HasSum (F p) (-Real.log (1 - rexp (-((p : ℝ) * t)))) := by
    intro p
    have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    have h := hasSum_neg_log_one_sub (y := rexp (-((p : ℝ) * t))) (exp_pos _).le
      (by rw [Real.exp_lt_one_iff]; nlinarith)
    refine h.congr_fun fun m => ?_
    simp only [hF, ← Real.exp_nat_mul]
    congr 2
    ring
  have hsum : Summable (Function.uncurry F) := by
    have hA := (phi_summable_exp_primes ht).mul_left (rexp t)
    have hB : Summable (fun m : ℕ => rexp (-((m : ℝ) * t))) := by
      have := (Real.summable_exp_nat_mul_iff (a := -t)).mpr (by linarith)
      exact this.congr fun m => by ring_nf
    have hAB := hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity)
    refine hAB.of_nonneg_of_le (fun x => by simp only [hF, Function.uncurry]; positivity) ?_
    rintro ⟨p, m⟩
    simp only [hF, Function.uncurry]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp; positivity
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
    calc rexp (-((p : ℝ) * (m * t))) / m ≤ rexp (-((p : ℝ) * (m * t))) :=
          div_le_self (exp_pos _).le hm1
      _ ≤ rexp (t + -((p : ℝ) * t) + -((m : ℝ) * t)) := by
          rw [exp_le_exp]; nlinarith [mul_nonneg (sub_nonneg.2 hm1) (by linarith : (0:ℝ) ≤ p - 1)]
      _ = rexp t * rexp (-((p : ℝ) * t)) * rexp (-((m : ℝ) * t)) := by
          rw [exp_add, exp_add]
  unfold primePhi
  rw [tsum_congr fun p => (hrow p).tsum_eq.symm, ← hsum.tsum_comm]
  refine tsum_congr fun m => ?_
  simp only [hF, primeExpSum]
  rw [tsum_div_const]

lemma summable_one_add_log_div_sq :
    Summable (fun m : ℕ => (1 + Real.log m) / (m : ℝ) ^ 2) := by
  have hs := (Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2
  refine hs.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have := Real.log_nonneg this
    positivity
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := by linarith
    have hsq : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
    have hlog : Real.log m ≤ 2 * Real.sqrt m - 2 := by
      have h := Real.log_le_sub_one_of_pos hsq
      rw [Real.log_sqrt hm0.le] at h
      linarith
    have hpow : (m : ℝ) ^ (3 / 2 : ℝ) = m * Real.sqrt m := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm0, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [hpow]
    have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
    rw [div_le_iff₀ (by positivity)]
    have : 2 * ((m : ℝ) * Real.sqrt m)⁻¹ * (m : ℝ) ^ 2 = 2 * Real.sqrt m := by
      field_simp
      nlinarith [hss]
    rw [this]
    linarith

section PNT

variable (hθ : Chebyshev.theta ~[atTop] id)
include hθ

/-- Lemma B: `t log(1/t) Φ(t) → ζ(2) = π²/6` as `t → 0⁺`. -/
theorem primePhi_asymp :
    Tendsto (fun t => t * Real.log t⁻¹ * primePhi t) (𝓝[>] 0) (𝓝 (π ^ 2 / 6)) := by
  have hA := primeExpSum_asymp hθ
  have hL : Tendsto (fun u : ℝ => Real.log u⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  -- `u S(u) → 0`
  have huS : Tendsto (fun u => u * primeExpSum u) (𝓝[>] 0) (𝓝 0) := by
    have h := hA.mul hL.inv_tendsto_atTop
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with u hu
    have : 0 < Real.log u⁻¹ := Real.log_pos ((one_lt_inv₀ hu.1).2 hu.2)
    simp only [Pi.inv_apply]
    rw [mul_right_comm, mul_inv_cancel_right₀ this.ne']
  -- log identity
  have hlogid : ∀ {m t : ℝ}, 0 < m → 0 < t →
      Real.log t⁻¹ = Real.log (m * t)⁻¹ + Real.log m := by
    intro m t hm ht
    rw [Real.log_inv, Real.log_inv, Real.log_mul hm.ne' ht.ne']
    ring
  set f : ℝ → ℕ → ℝ := fun t m => t * Real.log t⁻¹ * primeExpSum (m * t) / m with hf
  have hmain : Tendsto (fun t => ∑' m, f t m) (𝓝[>] 0) (𝓝 (∑' m : ℕ, 1 / (m : ℝ) ^ 2)) := by
    obtain ⟨u0, hu0, hu0P⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
      (hA.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)))
    set u1 := min u0 (rexp (-1)) with hu1
    have hu1pos : 0 < u1 := lt_min hu0 (exp_pos _)
    have hLu1 : 1 ≤ Real.log u1⁻¹ := by
      rw [Real.log_inv, le_neg, ← Real.log_exp (-1)]
      exact Real.log_le_log hu1pos (min_le_right _ _)
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun m : ℕ => (2 + Real.log u1⁻¹) * ((1 + Real.log m) / (m : ℝ) ^ 2))
      (summable_one_add_log_div_sq.mul_left _) ?_ ?_
    · -- pointwise limits
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [hf]
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have hcomp : Tendsto (fun t : ℝ => (m : ℝ) * t) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall
          fun t (ht : 0 < t) => mul_pos hm0 ht⟩
        have : Tendsto (fun t : ℝ => (m : ℝ) * t) (𝓝 0) (𝓝 ((m : ℝ) * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h1 := (hA.comp hcomp).add ((huS.comp hcomp).const_mul (Real.log m))
      have h2 := h1.div_const ((m : ℝ) ^ 2)
      rw [mul_zero, add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      simp only [hf, Function.comp_apply]
      rw [hlogid hm0 ht]
      field_simp
    · -- domination
      filter_upwards [Ioo_mem_nhdsGT hu1pos] with t ht
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [hf]
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm0 : (0 : ℝ) < m := by linarith
      have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
      have ht0 := ht.1
      have ht1 : t < 1 := ht.2.trans_le ((min_le_right _ _).trans (by
        rw [exp_le_one_iff]; norm_num))
      have hLt : 0 ≤ Real.log t⁻¹ := (Real.log_pos ((one_lt_inv₀ ht0).2 ht1)).le
      set v := (m : ℝ) * t with hv
      have hv0 : 0 < v := mul_pos hm0 ht0
      set Y := v * primeExpSum v with hY
      have hY0 : 0 ≤ Y := mul_nonneg hv0.le (phi_primeExpSum_nonneg v)
      have hfeq : f t m = Y * Real.log t⁻¹ / (m : ℝ) ^ 2 := by
        simp only [hf, hY, hv]
        field_simp
      have hid := hlogid hm0 ht0
      rw [← hv] at hid
      have hfnn : 0 ≤ f t m := by rw [hfeq]; positivity
      rw [Real.norm_of_nonneg hfnn, hfeq, mul_div_assoc']
      apply div_le_div_of_nonneg_right _ (by positivity)
      rcases lt_or_ge v u1 with hvu | hvu
      · -- small `v`: use the asymptotic bound
        have hP := hu0P ⟨hv0, hvu.trans_le (min_le_left _ _)⟩
        have hLv : 1 ≤ Real.log v⁻¹ := by
          rw [Real.log_inv, le_neg, ← Real.log_exp (-1)]
          exact (Real.log_le_log hv0 (hvu.le.trans (min_le_right _ _)))
        have hX : Y * Real.log v⁻¹ < 2 := by
          simp only [hY]; linarith [hP, show v * primeExpSum v * Real.log v⁻¹ =
            v * Real.log v⁻¹ * primeExpSum v by ring]
        have hY2 : Y < 2 := by nlinarith
        rw [hid]
        nlinarith
      · -- large `v`: use `S(v) ≤ 1/v`
        have hY1 : Y ≤ 1 := by
          have := phi_primeExpSum_le_inv hv0
          simp only [hY]
          rw [le_div_iff₀ hv0] at this
          linarith
        have hLv : Real.log v⁻¹ ≤ Real.log u1⁻¹ := by
          rw [Real.log_inv, Real.log_inv, neg_le_neg_iff]
          exact Real.log_le_log hu1pos hvu
        have : Y * Real.log t⁻¹ ≤ Real.log t⁻¹ := by nlinarith
        rw [hid] at this ⊢
        nlinarith
  rw [hasSum_zeta_two.tsum_eq] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [primePhi_eq_tsum ht, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [hf]
  ring

end PNT

end RntPaper
