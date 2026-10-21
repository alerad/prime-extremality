import RntPaper.Tail.Defs2
import RntPaper.Tail.Laplace

/-!
# Second-order tail asymptotics: assembly (paper §5.5)

From the saddle estimates for `N t + Φ(t)` (`Tail/Saddle2.lean`) and a prime in
`(N, N + K N/log² N]` (from `ThetaErrLog2`), the sandwich of Lemma 5.5 gives
`-log(I_N - Λ) = λ_N · shape(N) + O(λ_N (log ℓ/ℓ)²)`.
-/

namespace RntPaper

open QProduct Real Filter Topology Asymptotics Set

/-! ## Primes in short intervals -/

/-- `θ(x) = x + O(x/log² x)` gives a prime in `(N, N + K N / log² N]`. -/
theorem exists_prime_short (hθ : ThetaErrLog2) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∃ q : ℕ, q.Prime ∧ N < q ∧ (q : ℝ) ≤ N + K * N / Real.log N ^ 2 := by
  obtain ⟨K₀, hK₀⟩ := hθ
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  refine ⟨4 * K, by positivity, ?_⟩
  -- for large `N`: `log N ≥ 2` and `4K ≤ log² N`, so `h = 4KN/ℓ² ≤ N`
  have hlog := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (max 2 (2 * √K)), eventually_ge_atTop 2]
    with N hN hN2
  simp only [Function.comp] at hN
  set ℓ := Real.log N with hℓ
  have hℓ2 : 2 ≤ ℓ := le_trans (le_max_left _ _) hN
  have hℓK : 2 * √K ≤ ℓ := le_trans (le_max_right _ _) hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hsq : 4 * K ≤ ℓ ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hℓK 2
    rw [mul_pow, Real.sq_sqrt (by linarith)] at h
    linarith
  set h : ℝ := 4 * K * N / ℓ ^ 2 with hhdef
  have hh0 : 0 < h := by positivity
  have hhN : h ≤ N := by
    rw [hhdef, div_le_iff₀ (by positivity)]
    nlinarith
  set y : ℝ := N + h with hy
  have hy2 : 2 ≤ y := by linarith
  have hyℓ : ℓ ≤ Real.log y := Real.log_le_log hN0 (by linarith)
  have hθx := hK₀ N hNr
  have hθy := hK₀ y hy2
  have hKK : K₀ ≤ K := le_max_left _ _
  -- `|θ(x) - x| ≤ K x/ℓ²` and `|θ(y) - y| ≤ K y/ℓ² ≤ 2K x/ℓ²`
  have ex : |Chebyshev.theta N - N| ≤ K * N / ℓ ^ 2 := by
    refine hθx.trans ?_
    gcongr
  have ey : |Chebyshev.theta y - y| ≤ K * (2 * N) / ℓ ^ 2 := by
    refine hθy.trans ?_
    have hlogy : ℓ ^ 2 ≤ Real.log y ^ 2 := pow_le_pow_left₀ hℓ0.le hyℓ 2
    calc K₀ * y / Real.log y ^ 2 ≤ K * y / Real.log y ^ 2 := by
          gcongr
      _ ≤ K * y / ℓ ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hlogy
      _ ≤ K * (2 * N) / ℓ ^ 2 := by
          gcongr
          linarith
  have hlt : Chebyshev.theta N < Chebyshev.theta y := by
    have a1 := (abs_le.1 ex).2
    have a2 := (abs_le.1 ey).1
    have : K * (2 * N) / ℓ ^ 2 + K * N / ℓ ^ 2 < h := by
      rw [hhdef]
      have : K * (2 * N) / ℓ ^ 2 + K * N / ℓ ^ 2 = 3 * K * N / ℓ ^ 2 := by ring
      rw [this]
      apply div_lt_div_of_pos_right _ (by positivity)
      nlinarith
    linarith
  by_contra hne
  push Not at hne
  apply hlt.not_ge
  rw [Chebyshev.theta_eq_theta_coe_floor y]
  unfold Chebyshev.theta
  rw [Nat.floor_natCast, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
    by_contra hpN
    push Not at hpN
    have h3 := hne p hp.2 hpN
    have h4 : (p : ℝ) ≤ y := (Nat.le_floor_iff (by linarith)).1 hp.1.2
    have : y = N + 4 * K * N / Real.log N ^ 2 := by rw [hy, hhdef]
    linarith
  · intro p hp _
    simp only [Finset.mem_filter] at hp
    exact log_nonneg (by exact_mod_cast hp.2.one_lt.le)

/-! ## Growth of the error scale -/

/-- `ℓ⁸ ≤ N` for large `N`. -/
theorem second_log_pow_le : ∀ᶠ N : ℝ in atTop, Real.log N ^ 8 ≤ N := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hN1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hN
  calc Real.log N ^ 8 ≤ (N ^ (1 / 8 : ℝ)) ^ 8 :=
        pow_le_pow_left₀ (Real.log_nonneg hN1) hN 8
    _ = N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num

/-- For every `M`, eventually `M ℓ ≤ λ_N (log ℓ/ℓ)²`. -/
theorem second_lin_le_lamErr {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∀ᶠ N : ℝ in atTop, M * Real.log N ≤ tailLam a N * tailErr N := by
  set A : ℝ := max M 1 / (2 * √(2 * a)) with hA
  have hA0 : 0 < A := by positivity
  filter_upwards [second_log_pow_le, tendsto_log_atTop.eventually_ge_atTop (max (rexp 1) (A ^ 2)),
    eventually_ge_atTop 1] with N h8 hℓ hN1
  set ℓ := Real.log N with hℓdef
  have he : rexp 1 ≤ ℓ := le_trans (le_max_left _ _) hℓ
  have hA2 : A ^ 2 ≤ ℓ := le_trans (le_max_right _ _) hℓ
  have hℓ1 : 1 ≤ ℓ := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) he
  have hℓ0 : 0 < ℓ := by linarith
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (exp_pos 1) he
  -- `tailErr ≥ 1/ℓ²`
  have herr : 1 / ℓ ^ 2 ≤ tailErr N := by
    unfold tailErr
    rw [← hℓdef, div_pow, one_div]
    rw [inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  -- `√(N/ℓ) ≥ A ℓ³`, since `N ≥ ℓ⁸ ≥ A² ℓ⁷`
  have hsq : A * ℓ ^ 3 ≤ √(N / ℓ) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hℓ0]
    have : A ^ 2 * ℓ ^ 7 ≤ ℓ ^ 8 := by
      have := mul_le_mul_of_nonneg_right hA2 (by positivity : (0 : ℝ) ≤ ℓ ^ 7)
      nlinarith
    nlinarith
  have hlam : tailLam a N = 2 * √(2 * a) * √(N / ℓ) := by
    unfold tailLam
    rw [← hℓdef, show 2 * a * N / ℓ = (2 * a) * (N / ℓ) by ring,
      Real.sqrt_mul (by positivity)]
    ring
  have hMA : max M 1 = A * (2 * √(2 * a)) := by
    rw [hA]; field_simp
  calc M * ℓ ≤ max M 1 * ℓ := by gcongr; exact le_max_left _ _
    _ = 2 * √(2 * a) * (A * ℓ ^ 3) * (1 / ℓ ^ 2) := by
        rw [hMA]; field_simp
    _ ≤ 2 * √(2 * a) * √(N / ℓ) * tailErr N := by
        gcongr
    _ = tailLam a N * tailErr N := by rw [hlam]

/-! ## Assembly -/

/-- Lower bound on `D_N` from Lemma 5.5(a). -/
theorem second_D_lower {N : ℕ} (hN : 3 ≤ N) {B : ℝ}
    (hB : ∀ t : ℝ, 0 < t → B ≤ N * t + primePhi t)
    (hX : 0 < F (primesLE N) - primeLambda) :
    B - 1 - 2 * Real.log N ≤ -Real.log (F (primesLE N) - primeLambda) := by
  have h := Real.log_le_log hX (tail_le_of_primePhi N hN hB)
  rw [Real.log_exp] at h
  linarith

/-- Upper bound on `D_N` from Lemma 5.5(b) with `ε = 1/ℓ²` and `A = Φ(τ)`. -/
theorem second_D_upper {N q : ℕ} (hN : 3 ≤ N) (hq : q.Prime) (hNq : N < q)
    {τ lam K₁ : ℝ} (hτN : 1 / (N : ℝ) ≤ τ) (hτ1 : τ ≤ 1) (hNτ : N * τ ≤ lam) (hK₁ : 0 < K₁)
    (hqle : (q : ℝ) ≤ N + K₁ * N / Real.log N ^ 2) :
    0 < F (primesLE N) - primeLambda ∧
    -Real.log (F (primesLE N) - primeLambda) ≤
      N * τ + primePhi τ + (3 * Real.log N + 2) + (2 * K₁ + 1) * lam / Real.log N ^ 2 := by
  set ℓ := Real.log N with hℓdef
  have hN3r : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ1 : 1 ≤ ℓ := one_le_log_of_three_le hN
  have hℓ0 : 0 < ℓ := by linarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτN
  have hlam0 : 0 ≤ lam := le_trans (by positivity) hNτ
  set ε : ℝ := 1 / ℓ ^ 2 with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hεdef, div_le_one (by positivity)]; nlinarith
  have hwin := tail_ge_of_window N q hq hNq hτ0 hε0 (A := primePhi τ)
    (fun t ht => primePhi_anti hτ0 ht.1)
  set w := rexp (-τ) * (ε * τ / (1 + ε * τ)) * rexp (-(primePhi τ + q * ((1 + ε) * τ)))
    with hw
  have hετ0 : 0 < ε * τ := mul_pos hε0 hτ0
  have hw0 : 0 < w := by
    rw [hw]
    exact mul_pos (mul_pos (exp_pos _) (div_pos hετ0 (by linarith))) (exp_pos _)
  have hX0 : 0 < F (primesLE N) - primeLambda := hw0.trans_le hwin
  refine ⟨hX0, ?_⟩
  have hD_up : -Real.log (F (primesLE N) - primeLambda) ≤ -Real.log w := by
    have := Real.log_le_log hw0 hwin; linarith
  have hlogw : -Real.log w = τ - Real.log (ε * τ / (1 + ε * τ)) +
      (primePhi τ + q * ((1 + ε) * τ)) := by
    rw [hw, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_exp, Real.log_exp]
    ring
  have hlog1 : -Real.log (ε * τ / (1 + ε * τ)) ≤ 3 * ℓ + 1 := by
    have hετ1 : ε * τ ≤ 1 := by
      calc ε * τ ≤ 1 * 1 := mul_le_mul hε1 hτ1 hτ0.le (by norm_num)
        _ = 1 := by norm_num
    have hfrac : ε * τ / 2 ≤ ε * τ / (1 + ε * τ) :=
      div_le_div_of_nonneg_left hετ0.le (by positivity) (by linarith)
    have h1 : Real.log (ε * τ / 2) ≤ Real.log (ε * τ / (1 + ε * τ)) :=
      Real.log_le_log (by positivity) hfrac
    have h2 : Real.log (ε * τ / 2) = Real.log ε + Real.log τ - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_mul hε0.ne' hτ0.ne']
    have h3 : Real.log ε = -(2 * Real.log ℓ) := by
      rw [hεdef, one_div, Real.log_inv, Real.log_pow]; push_cast; ring
    have h4 : -ℓ ≤ Real.log τ := by
      have := Real.log_le_log (by positivity) hτN
      rwa [one_div, Real.log_inv] at this
    have h5 : Real.log ℓ ≤ ℓ := (Real.log_le_sub_one_of_pos hℓ0).trans (by linarith)
    have h6 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hq_term : (q : ℝ) * ((1 + ε) * τ) ≤ N * τ + (2 * K₁ + 1) * lam * ε := by
    have hqN' : (q : ℝ) ≤ N * (1 + K₁ * ε) := by
      calc (q : ℝ) ≤ N + K₁ * N / ℓ ^ 2 := hqle
        _ = N * (1 + K₁ * ε) := by rw [hεdef]; field_simp
    have hKε : K₁ * ε ≤ K₁ := by
      calc K₁ * ε ≤ K₁ * 1 := mul_le_mul_of_nonneg_left hε1 hK₁.le
        _ = K₁ := mul_one _
    have hNτ0 : 0 ≤ N * τ := by positivity
    have h1 : (N * τ) * (K₁ + 1 + K₁ * ε) ≤ lam * (2 * K₁ + 1) :=
      mul_le_mul hNτ (by linarith) (by positivity) hlam0
    have h2 : (N * τ) * (K₁ + 1 + K₁ * ε) * ε ≤ lam * (2 * K₁ + 1) * ε :=
      mul_le_mul_of_nonneg_right h1 hε0.le
    calc (q : ℝ) * ((1 + ε) * τ) ≤ N * (1 + K₁ * ε) * ((1 + ε) * τ) := by
          gcongr
      _ = N * τ + (N * τ) * (K₁ + 1 + K₁ * ε) * ε := by ring
      _ ≤ N * τ + lam * (2 * K₁ + 1) * ε := by linarith
      _ = _ := by ring
  have hε' : (2 * K₁ + 1) * lam * ε = (2 * K₁ + 1) * lam / ℓ ^ 2 := by
    rw [hεdef]; ring
  linarith

/-- Assembly: the saddle estimates for `primePhi` and a prime in a short interval give
`|-log(I_N - Λ) - λ_N shape(N)| ≤ K λ_N (log ℓ/ℓ)²` for all large `N`. -/
theorem tail_second_order_of {a κ : ℝ} (ha : 0 < a) (hθ : ThetaErrLog2)
    (hsad : ∃ K : ℝ, ∀ᶠ N : ℝ in atTop,
      (∀ t : ℝ, 0 < t → tailLam a N * (tailShape a κ N - K * tailErr N) ≤ N * t + primePhi t) ∧
      ∃ τ : ℝ, 1 / N ≤ τ ∧ τ ≤ 1 ∧ N * τ ≤ tailLam a N ∧
        N * τ + primePhi τ ≤ tailLam a N * (tailShape a κ N + K * tailErr N)) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop,
      |-Real.log (F (primesLE N) - primeLambda) - tailLam a N * tailShape a κ N| ≤
        K * (tailLam a N * tailErr N) := by
  obtain ⟨K, hK⟩ := hsad
  obtain ⟨K₁, hK₁, hq⟩ := exists_prime_short hθ
  refine ⟨|K| + 2 * K₁ + 2, ?_⟩
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hNat.eventually hK, hq, eventually_ge_atTop 3,
    hNat.eventually (second_lin_le_lamErr ha 6),
    hNat.eventually (tendsto_log_atTop.eventually_ge_atTop (rexp 1))] with N hKN hqN hN3 hlin hℓe
  obtain ⟨hlow, τ, hτN, hτ1, hNτ, hup⟩ := hKN
  obtain ⟨q, hqp, hNq, hqle⟩ := hqN
  obtain ⟨hX0, hD_up⟩ := second_D_upper hN3 hqp hNq hτN hτ1 hNτ hK₁ hqle
  have hD_low := second_D_lower hN3 hlow hX0
  set D := -Real.log (F (primesLE N) - primeLambda)
  set ℓ := Real.log N with hℓdef
  set lam := tailLam a N
  set sh := tailShape a κ N
  set e := tailErr N
  have hℓ1 : 1 ≤ ℓ := one_le_log_of_three_le hN3
  have hℓ0 : 0 < ℓ := by linarith
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (exp_pos 1) hℓe
  have hlam0 : 0 ≤ lam := by
    show 0 ≤ tailLam a N
    unfold tailLam; positivity
  have he0 : 0 ≤ e := by
    show 0 ≤ tailErr N
    unfold tailErr; positivity
  have herr : 1 / ℓ ^ 2 ≤ e := by
    show 1 / ℓ ^ 2 ≤ tailErr N
    unfold tailErr
    rw [← hℓdef, div_pow, one_div, inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hlamε : lam / ℓ ^ 2 ≤ lam * e := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left herr hlam0
  have hKe : lam * (K * e) ≤ |K| * (lam * e) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self K) (mul_nonneg hlam0 he0)
    linarith [show lam * (K * e) = K * (lam * e) by ring]
  have hKe' : -(|K| * (lam * e)) ≤ lam * (K * e) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le K) (mul_nonneg hlam0 he0)
    linarith [show lam * (K * e) = K * (lam * e) by ring]
  have hlin' : 6 * ℓ ≤ lam * e := hlin
  have hle : 0 ≤ lam * e := mul_nonneg hlam0 he0
  have hK1e : (2 * K₁ + 1) * lam / ℓ ^ 2 ≤ (2 * K₁ + 1) * (lam * e) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hlamε (by linarith)
  have hsplit : (|K| + 2 * K₁ + 2) * (lam * e) =
      |K| * (lam * e) + (2 * K₁ + 1) * (lam * e) + lam * e := by ring
  have hK1pos : 0 ≤ (2 * K₁ + 1) * (lam * e) := mul_nonneg (by linarith) hle
  have hlowexp : lam * (sh - K * e) = lam * sh - lam * (K * e) := by ring
  have hupexp : lam * (sh + K * e) = lam * sh + lam * (K * e) := by ring
  rw [abs_le, hsplit]
  constructor
  · linarith
  · linarith

end RntPaper
