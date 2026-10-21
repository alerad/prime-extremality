import QProduct.LeanCert

/-!
# Definitions (paper §1.1, §1.3)

Finite objects reuse LeanCert: `qProd S u = ∏_{n∈S}(1 - uⁿ)`, `F S = ∫₀¹ qProd S`,
`moment S k = ∫₀¹ qProd S u · uᵏ`, `primesLE N`, `primeLambda`.

New here: the truncated integrals `F_c`, infinite exponent sets via `tprod`,
primitive sets, the block integrand `E_T`, the full product `H`, the profile
`𝓛(c)`, and prime compression `C_p`.
-/

namespace RntPaper

open QProduct MeasureTheory Set

/-! ## Truncated integrals -/

/-- `F_c(S) = ∫₀ᶜ ∏_{n∈S}(1 - uⁿ) du` for a finite exponent set (paper (1.1)). -/
noncomputable def Fc (c : ℝ) (S : Finset ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..c, qProd S u

/-- At `c = 1` this is LeanCert's `F`. -/
@[simp] theorem Fc_one (S : Finset ℕ) : Fc 1 S = F S := rfl

/-! ## Infinite exponent sets -/

/-- Product profile of an arbitrary set of exponents, `P_A(u) = ∏_{n∈A}(1 - uⁿ)`,
as an unconditional `tprod` over the subtype `A`. For `u ∈ [0,1)` the product
converges because `∑_{n∈A} uⁿ < ∞`; the value at `u = 1` is irrelevant to
every integral below. -/
noncomputable def qProdSet (A : Set ℕ) (u : ℝ) : ℝ :=
  ∏' n : A, (1 - u ^ (n : ℕ))

/-- `F_c(A)` for an arbitrary (possibly infinite) exponent set. -/
noncomputable def FcSet (c : ℝ) (A : Set ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..c, qProdSet A u

/-- On finite sets the `tprod` is the finite product. -/
theorem qProdSet_coe (S : Finset ℕ) (u : ℝ) :
    qProdSet (S : Set ℕ) u = qProd S u := by
  unfold qProdSet qProd
  exact Finset.tprod_subtype S (fun n => 1 - u ^ n)

theorem FcSet_coe (c : ℝ) (S : Finset ℕ) : FcSet c (S : Set ℕ) = Fc c S := by
  unfold FcSet Fc
  simp only [qProdSet_coe]

/-! ## Primitive sets -/

/-- A set of integers `≥ 2` is primitive (a divisibility antichain) if no
element divides another. -/
def IsPrimitive (A : Set ℕ) : Prop :=
  (∀ a ∈ A, 2 ≤ a) ∧ ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/-- Finite primitive sets. -/
def IsPrimitiveFin (A : Finset ℕ) : Prop := IsPrimitive (A : Set ℕ)

/-- The set of all primes, `𝒫`. -/
def Primes : Set ℕ := {p | Nat.Prime p}

theorem primes_isPrimitive : IsPrimitive Primes :=
  ⟨fun _ hp => hp.two_le,
   fun _ ha _ hb hab => (Nat.prime_dvd_prime_iff_eq ha hb).mp hab⟩

theorem mem_primesLE {a N : ℕ} : a ∈ primesLE N ↔ Nat.Prime a ∧ a ≤ N := by
  simp only [primesLE, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

theorem primesLE_isPrimitiveFin (N : ℕ) : IsPrimitiveFin (primesLE N) := by
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · exact (mem_primesLE.mp (Finset.mem_coe.mp ha)).1.two_le
  · exact (Nat.prime_dvd_prime_iff_eq (mem_primesLE.mp (Finset.mem_coe.mp ha)).1
      (mem_primesLE.mp (Finset.mem_coe.mp hb)).1).mp hab

/-! ## The block integrand and the full product `H` -/

/-- `E_T(v) = ∏_{t∈T}(1 - vᵗ) - (1 - v)` (paper (1.2)), finite `T`. -/
noncomputable def blockE (T : Finset ℕ) (v : ℝ) : ℝ := qProd T v - (1 - v)

/-- `E_T` for an arbitrary exponent set. -/
noncomputable def blockESet (T : Set ℕ) (v : ℝ) : ℝ := qProdSet T v - (1 - v)

/-- `H(x) = ∏_{n≥2}(1 - xⁿ)` (paper §2). -/
noncomputable def Hfun (x : ℝ) : ℝ := qProdSet {n | 2 ≤ n} x

/-! ## The profile `𝓛` -/

/-- `𝓛(c) = ∫₀ᶜ ∏_p (1 - u^p) du` (paper Theorem 1.2). -/
noncomputable def Lfun (c : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..c, ∏' p : Nat.Primes, (1 - u ^ (p : ℕ))

/-- `𝓛(1) = Λ`, LeanCert's `primeLambda` (via its analytic bridge). -/
theorem Lfun_one_eq_primeLambda : Lfun 1 = primeLambda := by
  unfold Lfun
  exact primeLambda_eq_integral_tprod.symm

/-! ## Prime compression -/

/-- `C_p(A) = {p} ∪ {a ∈ A : p ∤ a}` (paper §1.3), finite version.
Matches `ProductInvariants.compressAt`. -/
def compressAt (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  insert p (A.filter (fun a => ¬ p ∣ a))

/-- `C_p(A)` for an arbitrary set. -/
def compressAtSet (p : ℕ) (A : Set ℕ) : Set ℕ :=
  insert p {a ∈ A | ¬ p ∣ a}

/-- The quotients `T = {a/p : a ∈ A, p ∣ a}` of the removed block. -/
def quotients (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.filter (fun a => p ∣ a)).image (fun a => a / p)

end RntPaper
