import RntPaper.MomentsWeight

/-!
# Executable polynomial certificates

Polynomials are lists of rational coefficients, `[c₀, c₁, …]` standing for `∑ cᵢ xⁱ`.
Everything here is computable, so `decide`/`native_decide` can run the checks, and every
check comes with a soundness theorem about the real polynomial function `ev p`.

* arithmetic: `add`, `smul`, `mul`, `prodOneSub` (`∏ (1 - x^n)`), `taylor` (`p(a + t)`),
  `scale` (`p(w t)`), `deriv`, `trim`;
* `posUnit n p`: a bisection test (Taylor bound `c₀ + ∑_{cᵢ<0} cᵢ` on `[0,1]`) proving
  `p > 0` on `[0,1]`; `posOn n p a b` for `[a,b]`;
* `signPattern_of`: `h > 0` on `[0,a]`, `h < 0` on `[b,1]`, `h' < 0` on `[a,b]` gives a
  single sign change of `h` in `(0,1)`;
* `intUnit g K = ∫₀¹ u^{K-1} g(u) du` (real `K > 0`) and `intTo g K y = ∫₀ʸ u^{K-1} g(u) du`
  (natural `K ≥ 1`), computed exactly.
-/

namespace RntPaper.CP

open MeasureTheory intervalIntegral Set

/-! ## Evaluation -/

/-- `ev p x = ∑ pᵢ xⁱ` (Horner). -/
def ev : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: p, x => (c : ℝ) + x * ev p x

/-- Rational evaluation. -/
def evQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: p, x => c + x * evQ p x

@[simp] theorem ev_nil (x : ℝ) : ev [] x = 0 := rfl
@[simp] theorem ev_cons (c : ℚ) (p : List ℚ) (x : ℝ) : ev (c :: p) x = c + x * ev p x := rfl

theorem evQ_cast (p : List ℚ) (x : ℚ) : ((evQ p x : ℚ) : ℝ) = ev p x := by
  induction p with
  | nil => simp [evQ]
  | cons c p ih => simp [evQ, ih]

theorem continuous_ev (p : List ℚ) : Continuous (ev p) := by
  induction p with
  | nil => exact continuous_const
  | cons c p ih => exact continuous_const.add (continuous_id.mul ih)

/-! ## Arithmetic -/

def add : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

@[simp] theorem ev_add (p q : List ℚ) (x : ℝ) : ev (add p q) x = ev p x + ev q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

def smul (a : ℚ) (p : List ℚ) : List ℚ := p.map (a * ·)

@[simp] theorem ev_smul (a : ℚ) (p : List ℚ) (x : ℝ) : ev (smul a p) x = a * ev p x := by
  induction p with
  | nil => simp [smul]
  | cons c p ih =>
    simp only [smul, List.map_cons] at ih ⊢
    simp [ih]; ring

def neg (p : List ℚ) : List ℚ := smul (-1) p

@[simp] theorem ev_neg (p : List ℚ) (x : ℝ) : ev (neg p) x = - ev p x := by
  simp [neg]

def sub (p q : List ℚ) : List ℚ := add p (neg q)

@[simp] theorem ev_sub (p q : List ℚ) (x : ℝ) : ev (sub p q) x = ev p x - ev q x := by
  simp [sub]; ring

/-- `xⁿ p(x)`. -/
def shiftN (n : ℕ) (p : List ℚ) : List ℚ := List.replicate n 0 ++ p

@[simp] theorem ev_shiftN (n : ℕ) (p : List ℚ) (x : ℝ) : ev (shiftN n p) x = x ^ n * ev p x := by
  induction n with
  | zero => simp [shiftN]
  | succ n ih =>
    simp only [shiftN, List.replicate_succ, List.cons_append] at ih ⊢
    simp [ih]; ring

def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c :: p, q => if c = 0 then 0 :: mul p q else add (smul c q) (0 :: mul p q)

@[simp] theorem ev_mul (p q : List ℚ) (x : ℝ) : ev (mul p q) x = ev p x * ev q x := by
  induction p with
  | nil => simp [mul]
  | cons c p ih =>
    by_cases hc : c = 0
    · simp [mul, hc, ih]; ring
    · simp [mul, hc, ih]; ring

/-- `(1 - xⁿ) p(x)`. -/
def mulOneSub (n : ℕ) (p : List ℚ) : List ℚ := sub p (shiftN n p)

@[simp] theorem ev_mulOneSub (n : ℕ) (p : List ℚ) (x : ℝ) :
    ev (mulOneSub n p) x = (1 - x ^ n) * ev p x := by
  simp [mulOneSub]; ring

/-- `∏_{n ∈ l} (1 - xⁿ)`. -/
def prodOneSub : List ℕ → List ℚ
  | [] => [1]
  | n :: l => mulOneSub n (prodOneSub l)

@[simp] theorem ev_prodOneSub (l : List ℕ) (x : ℝ) :
    ev (prodOneSub l) x = (l.map fun n => 1 - x ^ n).prod := by
  induction l with
  | nil => simp [prodOneSub]
  | cons n l ih => simp [prodOneSub, ih]

/-- `(a + x) p(x)`. -/
def mulLin (a : ℚ) (p : List ℚ) : List ℚ := add (smul a p) (0 :: p)

@[simp] theorem ev_mulLin (a : ℚ) (p : List ℚ) (x : ℝ) :
    ev (mulLin a p) x = (a + x) * ev p x := by
  simp [mulLin]; ring

/-- Taylor shift: `ev (taylor a p) t = ev p (a + t)`. -/
def taylor (a : ℚ) : List ℚ → List ℚ
  | [] => []
  | c :: p => add [c] (mulLin a (taylor a p))

@[simp] theorem ev_taylor (a : ℚ) (p : List ℚ) (t : ℝ) : ev (taylor a p) t = ev p (a + t) := by
  induction p with
  | nil => simp [taylor]
  | cons c p ih => simp [taylor, ih]

def scaleAux (w : ℚ) : ℚ → List ℚ → List ℚ
  | _, [] => []
  | s, c :: p => (c * s) :: scaleAux w (s * w) p

theorem ev_scaleAux (w : ℚ) (p : List ℚ) (s : ℚ) (t : ℝ) :
    ev (scaleAux w s p) t = s * ev p (w * t) := by
  induction p generalizing s with
  | nil => simp [scaleAux]
  | cons c p ih => simp [scaleAux, ih]; ring

/-- Scaling: `ev (scale w p) t = ev p (w t)`. -/
def scale (w : ℚ) (p : List ℚ) : List ℚ := scaleAux w 1 p

@[simp] theorem ev_scale (w : ℚ) (p : List ℚ) (t : ℝ) : ev (scale w p) t = ev p (w * t) := by
  simp [scale, ev_scaleAux]

/-- Formal derivative. -/
def deriv : List ℚ → List ℚ
  | [] => []
  | _ :: p => add p (0 :: deriv p)

theorem hasDerivAt_ev (p : List ℚ) (x : ℝ) : HasDerivAt (ev p) (ev (deriv p) x) x := by
  induction p with
  | nil =>
    have h0 : ev [] = fun _ : ℝ => (0 : ℝ) := funext fun _ => rfl
    rw [h0]; simp only [deriv, ev_nil]; exact hasDerivAt_const x 0
  | cons c p ih =>
    have h := (hasDerivAt_id x).mul ih
    have h2 := (hasDerivAt_const x (c : ℝ)).add h
    convert h2 using 1
    · funext y; simp
    · simp [deriv]

/-- Drop trailing zeros. -/
def trim : List ℚ → List ℚ
  | [] => []
  | c :: p => if trim p = [] ∧ c = 0 then [] else c :: trim p

@[simp] theorem ev_trim (p : List ℚ) (x : ℝ) : ev (trim p) x = ev p x := by
  induction p with
  | nil => simp [trim]
  | cons c p ih =>
    by_cases h : trim p = [] ∧ c = 0
    · obtain ⟨h1, rfl⟩ := h
      have h0 : ev p x = 0 := by rw [← ih, h1]; rfl
      simp [trim, h1, h0]
    · simp only [trim, h, ite_false, ev_cons, ih]

/-! ## Positivity on `[0,1]` by bisection -/

/-- `∑ min(0, cᵢ)`. -/
def negSum : List ℚ → ℚ
  | [] => 0
  | c :: p => min 0 c + negSum p

/-- The Taylor lower bound `c₀ + ∑_{i≥1} min(0, cᵢ)` on `[0,1]`. -/
def lowB : List ℚ → ℚ
  | [] => 0
  | c :: p => c + negSum p

theorem negSum_nonpos (p : List ℚ) : negSum p ≤ 0 := by
  induction p with
  | nil => simp [negSum]
  | cons c p ih => simp only [negSum]; linarith [min_le_left (0 : ℚ) c]

theorem negSum_le_ev (p : List ℚ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (negSum p : ℝ) ≤ ev p t := by
  induction p with
  | nil => simp [negSum]
  | cons c p ih =>
    simp only [negSum, ev_cons]
    push_cast
    have hn : (negSum p : ℝ) ≤ 0 := by exact_mod_cast negSum_nonpos p
    have h1 : (negSum p : ℝ) ≤ t * ev p t := by
      have : t * (negSum p : ℝ) ≤ t * ev p t := mul_le_mul_of_nonneg_left ih ht.1
      nlinarith [ht.2]
    have h2 : min 0 (c : ℝ) ≤ c := min_le_right _ _
    linarith

theorem lowB_le_ev (p : List ℚ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (lowB p : ℝ) ≤ ev p t := by
  cases p with
  | nil => simp [lowB]
  | cons c p =>
    simp only [lowB, ev_cons]
    push_cast
    have hn : (negSum p : ℝ) ≤ 0 := by exact_mod_cast negSum_nonpos p
    have h := negSum_le_ev p ht
    have : (negSum p : ℝ) ≤ t * ev p t := by
      have : t * (negSum p : ℝ) ≤ t * ev p t := mul_le_mul_of_nonneg_left h ht.1
      nlinarith [ht.2]
    linarith

/-- `p > 0` on `[0,1]`: Taylor bound, else bisect (`n` levels). -/
def posUnit : ℕ → List ℚ → Bool
  | 0, p => decide (0 < lowB p)
  | n + 1, p => decide (0 < lowB p) ||
      (posUnit n (scale (1 / 2) p) && posUnit n (taylor 1 (scale (1 / 2) p)))

theorem posUnit_sound : ∀ (n : ℕ) (p : List ℚ), posUnit n p = true →
    ∀ t ∈ Icc (0 : ℝ) 1, 0 < ev p t := by
  intro n
  induction n with
  | zero =>
    intro p h t ht
    simp only [posUnit, decide_eq_true_eq] at h
    exact lt_of_lt_of_le (by exact_mod_cast h) (lowB_le_ev p ht)
  | succ n ih =>
    intro p h t ht
    simp only [posUnit, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨hl, hr⟩
    · exact lt_of_lt_of_le (by exact_mod_cast h) (lowB_le_ev p ht)
    · rcases le_total t (1 / 2) with h2 | h2
      · have := ih _ hl (2 * t) ⟨by linarith [ht.1], by linarith⟩
        simp only [ev_scale] at this
        convert this using 2; push_cast; ring
      · have := ih _ hr (2 * t - 1) ⟨by linarith, by linarith [ht.2]⟩
        simp only [ev_taylor, ev_scale] at this
        convert this using 2; push_cast; ring

/-- `p > 0` on `[a,b]`. -/
def posOn (n : ℕ) (p : List ℚ) (a b : ℚ) : Bool := posUnit n (scale (b - a) (taylor a p))

theorem posOn_sound {n : ℕ} {p : List ℚ} {a b : ℚ} (hab : a < b) (h : posOn n p a b = true) :
    ∀ x ∈ Icc (a : ℝ) b, 0 < ev p x := by
  intro x hx
  have hba : (0 : ℝ) < b - a := by exact_mod_cast sub_pos.mpr hab
  have ht : (x - a) / (b - a) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [hx.1]) hba.le, (div_le_one hba).mpr (by linarith [hx.2])⟩
  have := posUnit_sound n _ h _ ht
  simp only [ev_scale, ev_taylor] at this
  convert this using 2
  push_cast
  field_simp
  ring

/-! ## A single sign change -/

/-- **Sign pattern.** If `h > 0` on `[0,a]`, `h < 0` on `[b,1]` and `h' < 0` on `[a,b]`
(`0 < a < b < 1`), then `h` vanishes at one `x₀ ∈ (a,b)`, is positive on `[0,x₀)` and
negative on `(x₀,1]`. -/
theorem signPattern_of {h : List ℚ} {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (h1 : ∀ x ∈ Icc (0 : ℝ) a, 0 < ev h x) (h2 : ∀ x ∈ Icc b (1 : ℝ), ev h x < 0)
    (h3 : ∀ x ∈ Icc a b, ev (deriv h) x < 0) :
    ∃ x₀ ∈ Ioo a b, (∀ x ∈ Ico (0 : ℝ) x₀, 0 < ev h x) ∧ (∀ x ∈ Ioc x₀ (1 : ℝ), ev h x < 0) := by
  have hc : Continuous (ev h) := continuous_ev h
  have hanti : StrictAntiOn (ev h) (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) hc.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_ev h x).deriv]
    exact h3 x ⟨hx.1.le, hx.2.le⟩
  have hpa : 0 < ev h a := h1 a ⟨ha.le, le_rfl⟩
  have hnb : ev h b < 0 := h2 b ⟨le_rfl, hb.le⟩
  obtain ⟨x₀, hx₀, hz⟩ := intermediate_value_Ioo' hab.le hc.continuousOn ⟨hnb, hpa⟩
  refine ⟨x₀, hx₀, fun x hx => ?_, fun x hx => ?_⟩
  · rcases le_or_gt x a with hxa | hxa
    · exact h1 x ⟨hx.1, hxa⟩
    · have := hanti ⟨hxa.le, by linarith [hx.2, hx₀.2]⟩ ⟨hx₀.1.le, hx₀.2.le⟩ hx.2
      linarith
  · rcases le_or_gt b x with hxb | hxb
    · exact h2 x ⟨hxb, hx.2⟩
    · have := hanti ⟨hx₀.1.le, hx₀.2.le⟩ ⟨by linarith [hx.1, hx₀.1], hxb.le⟩ hx.1
      linarith

/-! ## Exact integrals -/

/-- `∫₀¹ u^{K-1} g(u) du = ∑ gᵢ/(K+i)`. -/
def intUnit : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: p, K => c / K + intUnit p (K + 1)

theorem intervalIntegrable_rpow_mul_ev {K : ℝ} (hK : 0 < K) (p : List ℚ) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => u ^ (K - 1) * ev p u) volume a b :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn
    (continuous_ev p).continuousOn

/-- **Exact moment of a polynomial**: `∫₀¹ u^{K-1} g(u) du = intUnit g K` for `K > 0`. -/
theorem integral_eq_intUnit (p : List ℚ) {K : ℚ} (hK : 0 < K) :
    ∫ u in (0 : ℝ)..1, u ^ ((K : ℝ) - 1) * ev p u = intUnit p K := by
  induction p generalizing K with
  | nil => simp [intUnit]
  | cons c p ih =>
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    have hK1 : (0 : ℚ) < K + 1 := by linarith
    have hcongr : (∫ u in (0 : ℝ)..1, u ^ ((K : ℝ) - 1) * ev (c :: p) u)
        = ∫ u in (0 : ℝ)..1, ((c : ℝ) * u ^ ((K : ℝ) - 1)
            + u ^ (((K + 1 : ℚ) : ℝ) - 1) * ev p u) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with u hu
      rw [uIoc_of_le zero_le_one] at hu
      simp only [ev_cons]
      push_cast
      rw [show (K : ℝ) + 1 - 1 = ((K : ℝ) - 1) + 1 by ring, Real.rpow_add_one hu.1.ne']
      ring
    rw [hcongr, intervalIntegral.integral_add ((intervalIntegral.intervalIntegrable_rpow'
      (by linarith)).const_mul _) (intervalIntegrable_rpow_mul_ev (by exact_mod_cast hK1) p 0 1)]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), ih hK1]
    rw [show (K : ℝ) - 1 + 1 = K by ring, Real.zero_rpow hKR.ne', Real.one_rpow, sub_zero]
    simp only [intUnit]
    push_cast
    ring

/-- `∫₀ʸ u^{K-1} g(u) du` for natural `K ≥ 1` and rational `y`; `s = y^K` is carried along. -/
def intToAux (y : ℚ) : List ℚ → ℕ → ℚ → ℚ
  | [], _, _ => 0
  | c :: p, K, s => c * s / K + intToAux y p (K + 1) (s * y)

def intTo (p : List ℚ) (K : ℕ) (y : ℚ) : ℚ := intToAux y p K (y ^ K)

theorem integral_pow_mul_ev (p : List ℚ) {K : ℕ} (hK : 1 ≤ K) (y : ℚ) :
    ∫ u in (0 : ℝ)..y, u ^ (K - 1) * ev p u = intTo p K y := by
  unfold intTo
  induction p generalizing K with
  | nil => simp [intToAux]
  | cons c p ih =>
    have hK' : 1 ≤ K + 1 := by omega
    have hfun : (fun u : ℝ => u ^ (K - 1) * ev (c :: p) u)
        = fun u => (c : ℝ) * u ^ (K - 1) + u ^ (K + 1 - 1) * ev p u := by
      funext u
      simp only [ev_cons, Nat.add_sub_cancel]
      obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; ring
    rw [hfun, intervalIntegral.integral_add (by
      exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _) (by
      exact ((continuous_pow _).mul (continuous_ev p)).intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul, integral_pow, ih hK']
    simp only [intToAux]
    push_cast
    obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    push_cast
    ring

end RntPaper.CP
