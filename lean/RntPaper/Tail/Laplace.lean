import RntPaper.Tail.Sandwich

/-!
# Lemma D: Laplace-type bounds for `I_N - Λ` (paper Lemma 5.5)

Unconditional, non-asymptotic bounds comparing `I_N - Λ` with `Φ`:

* `tail_le_of_primePhi`: if `B ≤ N t + Φ(t)` for all `t > 0` and `N ≥ 3`, then
  `I_N - Λ ≤ exp(1 + 2 log N - B)`, i.e. `I_N - Λ ≤ e N² e^{-M_N}`;
* `tail_ge_of_window`: a prime `q > N` and a bound `Φ ≤ A` on `[τ, (1+ε)τ]` give
  `I_N - Λ ≥ e^{-τ} (ετ/(1+ετ)) exp(-(A + q(1+ε)τ))`.
-/

namespace RntPaper

open QProduct Real Filter Topology Asymptotics MeasureTheory Set

/-! ## Monotonicity -/

/-- `Φ` is nonincreasing on `(0, ∞)`. -/
theorem primePhi_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : primePhi t ≤ primePhi s := by
  have ht : 0 < t := hs.trans_le hst
  rw [primePhi_eq_tsum_phiInd, primePhi_eq_tsum_phiInd]
  have hxs0 : 0 ≤ rexp (-s) := (exp_pos _).le
  have hxs1 : rexp (-s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hxt0 : 0 ≤ rexp (-t) := (exp_pos _).le
  have hxt1 : rexp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hle : rexp (-t) ≤ rexp (-s) := Real.exp_le_exp.mpr (by linarith)
  refine (summable_phiInd hxt0 hxt1).tsum_le_tsum (fun n => ?_) (summable_phiInd hxs0 hxs1)
  unfold phiInd
  by_cases hn : n ∈ {p : ℕ | p.Prime}
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn, neg_le_neg_iff]
    have hn0 : n ≠ 0 := (show n.Prime from hn).ne_zero
    have h1 : rexp (-t) ^ n ≤ rexp (-s) ^ n := pow_le_pow_left₀ hxt0 hle n
    have h2 : rexp (-s) ^ n < 1 := pow_lt_one₀ hxs0 hxs1 hn0
    exact Real.log_le_log (by linarith) (by linarith)
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]

theorem primePhi_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ primePhi t := by
  rw [primePhi_eq_tsum_phiInd]
  exact tsum_nonneg (phiInd_nonneg (exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith)))

private theorem qProd_antiOn (S : Finset ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    qProd S y ≤ qProd S x := by
  unfold qProd
  apply Finset.prod_le_prod₀
  · intro n _
    exact sub_nonneg.mpr (pow_le_one₀ (hx.trans hxy) hy)
  · intro n _
    exact sub_le_sub_left (pow_le_pow_left₀ hx hxy n) 1

/-- `1 - e^{-y} ≥ y/(1+y)` for `y ≥ 0`. -/
theorem div_one_add_le_one_sub_exp {y : ℝ} (hy : 0 ≤ y) : y / (1 + y) ≤ 1 - rexp (-y) := by
  have h1 : y + 1 ≤ rexp y := Real.add_one_le_exp y
  have h2 : rexp (-y) * rexp y = 1 := by rw [← exp_add]; simp
  have h3 : 0 < rexp (-y) := exp_pos _
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem one_le_log_of_three_le {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- For `t ≥ 2 log N / N` the error term of `qProd_le_exp_neg_primePhi` is at most `1`. -/
theorem qProd_le_exp_one_sub_of_ge {N : ℕ} (hN : 3 ≤ N) {t : ℝ}
    (ht : 2 * Real.log N / N ≤ t) :
    1 / (N : ℝ) ≤ 1 - rexp (-t) ∧ rexp (-((N : ℝ) * t)) ≤ 1 / (N : ℝ) ^ 2 ∧
      qProd (primesLE N) (rexp (-t)) ≤ rexp (1 - primePhi t) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ := one_le_log_of_three_le hN
  have hNt : 2 * Real.log N ≤ N * t := by
    rw [div_le_iff₀ hN0] at ht; linarith
  have ht0 : 0 < t := by
    have : 0 < 2 * Real.log N / N := by positivity
    linarith
  -- `1/N ≤ 1 - e^{-t}`
  have h1 : 1 / (N : ℝ) ≤ 1 - rexp (-t) := by
    refine le_trans ?_ (div_one_add_le_one_sub_exp ht0.le)
    rw [div_le_div_iff₀ hN0 (by linarith)]
    rcases le_or_gt t 1 with h | h <;> nlinarith
  -- `e^{-Nt} ≤ 1/N²`
  have hexp2 : rexp (2 * Real.log N) = (N : ℝ) ^ 2 := by
    rw [show 2 * Real.log N = Real.log N + Real.log N by ring, exp_add, exp_log hN0]; ring
  have h2 : rexp (-((N : ℝ) * t)) ≤ 1 / (N : ℝ) ^ 2 := by
    calc rexp (-((N : ℝ) * t)) ≤ rexp (-(2 * Real.log N)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (N : ℝ) ^ 2 := by rw [exp_neg, hexp2, one_div]
  refine ⟨h1, h2, ?_⟩
  refine (qProd_le_exp_neg_primePhi N ht0).trans (Real.exp_le_exp.mpr ?_)
  have hR : rexp (-(((N : ℝ) + 1) * t)) / (1 - rexp (-t)) ^ 2 ≤ 1 := by
    have hpos : 0 < (1 - rexp (-t)) ^ 2 := by
      have : 0 < 1 / (N : ℝ) := by positivity
      have : 0 < 1 - rexp (-t) := by linarith
      positivity
    rw [div_le_one hpos]
    have hsq : (1 / (N : ℝ)) ^ 2 ≤ (1 - rexp (-t)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : rexp (-(((N : ℝ) + 1) * t)) ≤ rexp (-((N : ℝ) * t)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc rexp (-(((N : ℝ) + 1) * t)) ≤ 1 / (N : ℝ) ^ 2 := h3.trans h2
      _ = (1 / (N : ℝ)) ^ 2 := by ring
      _ ≤ _ := hsq
  linarith

/-- **Lemma 5.5(a).** If `B ≤ N t + Φ(t)` for every `t > 0` (i.e. `B ≤ M_N`) and `N ≥ 3`, then
`I_N - Λ ≤ e N² e^{-B}`. -/
theorem tail_le_of_primePhi (N : ℕ) (hN : 3 ≤ N) {B : ℝ}
    (hB : ∀ t : ℝ, 0 < t → B ≤ N * t + primePhi t) :
    F (primesLE N) - primeLambda ≤ rexp (1 + 2 * Real.log N - B) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ := one_le_log_of_three_le hN
  set s := 2 * Real.log N / N with hs
  have hs0 : 0 < s := by positivity
  have hNs : (N : ℝ) * s = 2 * Real.log N := by rw [hs]; field_simp
  apply tail_le_of_forall
  intro x hx
  rcases hx.1.eq_or_lt with hx0 | hx0
  · subst hx0
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, sub_zero, div_one, zero_le_one, min_eq_right, mul_zero]
    exact (exp_pos _).le
  set t := -Real.log x with htdef
  have ht0 : 0 < t := by
    have := Real.log_neg hx0 hx.2
    linarith
  have hxt : x = rexp (-t) := by rw [htdef, neg_neg, exp_log hx0]
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx.2.le⟩
  have hP0 := qProd_nonneg (primesLE N) hxI
  by_cases hts : s ≤ t
  · obtain ⟨h1, h2, hP⟩ := qProd_le_exp_one_sub_of_ge hN hts
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hmin : min 1 (x ^ (N + 1) / (1 - x)) ≤ N * rexp (-((N : ℝ) * t)) := by
      refine (min_le_right _ _).trans ?_
      rw [div_le_iff₀ hx1]
      have hpow : x ^ (N + 1) ≤ rexp (-((N : ℝ) * t)) * x := by
        rw [pow_succ, hxt, ← Real.exp_nat_mul]
        exact mul_le_mul_of_nonneg_right (le_of_eq (by ring_nf)) (exp_pos _).le
      rw [← hxt] at h1
      have hxle : x ≤ 1 := hx.2.le
      have : rexp (-((N : ℝ) * t)) * x ≤ N * rexp (-((N : ℝ) * t)) * (1 - x) := by
        have he := (exp_pos (-((N : ℝ) * t))).le
        have : 1 ≤ (N : ℝ) * (1 - x) := by
          rw [div_le_iff₀ hN0] at h1; linarith
        nlinarith
      linarith
    have hPx : qProd (primesLE N) x ≤ rexp (1 - primePhi t) := by rw [hxt]; exact hP
    calc qProd (primesLE N) x * min 1 (x ^ (N + 1) / (1 - x))
        ≤ rexp (1 - primePhi t) * (N * rexp (-((N : ℝ) * t))) :=
          mul_le_mul hPx hmin (le_min zero_le_one (div_nonneg (pow_nonneg hx0.le _) hx1.le))
            (exp_pos _).le
      _ = rexp (Real.log N + 1 - (N * t + primePhi t)) := by
          rw [show Real.log N + 1 - (N * t + primePhi t) =
            Real.log N + ((1 - primePhi t) + -((N : ℝ) * t)) by ring, exp_add, exp_add,
            exp_log hN0]
          ring
      _ ≤ rexp (1 + 2 * Real.log N - B) :=
          Real.exp_le_exp.mpr (by linarith [hB t ht0])
  · push Not at hts
    obtain ⟨_, _, hP⟩ := qProd_le_exp_one_sub_of_ge hN (le_refl s)
    have hmono : qProd (primesLE N) x ≤ qProd (primesLE N) (rexp (-s)) := by
      refine qProd_antiOn _ (exp_pos _).le ?_ hx.2.le
      rw [hxt]; exact Real.exp_le_exp.mpr (by linarith)
    have hmin : min 1 (x ^ (N + 1) / (1 - x)) ≤ 1 := min_le_left _ _
    have hmin0 : 0 ≤ min 1 (x ^ (N + 1) / (1 - x)) :=
      le_min zero_le_one (div_nonneg (pow_nonneg hx0.le _) (by linarith [hx.2]))
    calc qProd (primesLE N) x * min 1 (x ^ (N + 1) / (1 - x))
        ≤ qProd (primesLE N) x := mul_le_of_le_one_right hP0 hmin
      _ ≤ rexp (1 - primePhi s) := hmono.trans hP
      _ ≤ rexp (1 + 2 * Real.log N - B) :=
          Real.exp_le_exp.mpr (by linarith [hB s hs0])

/-- **Lemma 5.5(b).** A prime `q > N` and a bound `Φ ≤ A` on the window `[τ, (1+ε)τ]` give
`I_N - Λ ≥ e^{-τ} (ετ/(1+ετ)) exp(-(A + q(1+ε)τ))`. -/
theorem tail_ge_of_window (N q : ℕ) (hq : q.Prime) (hNq : N < q) {τ ε A : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (hA : ∀ t ∈ Icc τ ((1 + ε) * τ), primePhi t ≤ A) :
    rexp (-τ) * (ε * τ / (1 + ε * τ)) * rexp (-(A + q * ((1 + ε) * τ))) ≤
      F (primesLE N) - primeLambda := by
  set a := rexp (-((1 + ε) * τ))
  set b := rexp (-τ)
  set B := rexp (-(A + q * ((1 + ε) * τ)))
  have hab : a ≤ b := Real.exp_le_exp.mpr (by nlinarith)
  have hb : b ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hB : ∀ x ∈ Icc a b, B ≤ qProd (primesLE N) x * x ^ q := by
    intro x hx
    have hx0 : 0 < x := (exp_pos _).trans_le hx.1
    set t := -Real.log x with htdef
    have hxt : x = rexp (-t) := by rw [htdef, neg_neg, exp_log hx0]
    have ht1 : τ ≤ t := by
      have := Real.log_le_log hx0 hx.2
      rw [Real.log_exp] at this; linarith
    have ht2 : t ≤ (1 + ε) * τ := by
      have := Real.log_le_log (exp_pos _) hx.1
      rw [Real.log_exp] at this; linarith
    have ht0 : 0 < t := hτ.trans_le ht1
    have hP : rexp (-A) ≤ qProd (primesLE N) x := by
      rw [hxt]
      exact (Real.exp_le_exp.mpr (neg_le_neg (hA t ⟨ht1, ht2⟩))).trans
        (exp_neg_primePhi_le_qProd N ht0)
    have hxq : rexp (-(q * ((1 + ε) * τ))) ≤ x ^ q := by
      rw [hxt, ← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by
        have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        nlinarith)
    calc B = rexp (-A) * rexp (-(q * ((1 + ε) * τ))) := by
          simp only [B]; rw [← exp_add]; ring_nf
      _ ≤ qProd (primesLE N) x * x ^ q :=
          mul_le_mul hP hxq (exp_pos _).le (qProd_nonneg _ ⟨hx0.le, hx.2.trans hb⟩)
  have h := le_tail_of_window N q hq hNq (exp_pos _).le hab hb hB
  have hlen : rexp (-τ) * (ε * τ / (1 + ε * τ)) ≤ b - a := by
    have hετ : 0 ≤ ε * τ := by positivity
    have h1 := div_one_add_le_one_sub_exp hετ
    have hba : b - a = rexp (-τ) * (1 - rexp (-(ε * τ))) := by
      simp only [a, b]
      rw [mul_sub, mul_one, ← exp_add]; ring_nf
    rw [hba]
    exact mul_le_mul_of_nonneg_left h1 (exp_pos _).le
  exact (mul_le_mul_of_nonneg_right hlen (exp_pos _).le).trans h

end RntPaper
