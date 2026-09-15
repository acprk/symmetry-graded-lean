/-
  Doubling.lean

  Formal verification (Lean 4 + Mathlib) of the Galois-axis statements of

    "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping"

  (Lemma "Sub-orbit products from doubling", Proposition "Orbit-product
  evaluation", Lemma "Correctness of the construction", Lemma "Correctness"
  of ComposedEval).  The Frobenius is modelled as an arbitrary ring
  endomorphism `φ : R →+* R` of a commutative ring `R`, acting on
  polynomials coefficientwise through `Polynomial.mapRingHom φ`.  With no unproved
  placeholders:

  * `orbProd`                  `Orb_n(x) = ∏_{i<n} φⁱ(x)`
  * `orbProd_add`, `map_orbProd`
                               `Orb_{m+n}(x) = Orb_m(x) · φ^m(Orb_n(x))`
  * `doubling`                 (Lemma "Sub-orbit products from doubling")
                               `N₀ = x`, `N_{j+1} = N_j · φ^{2^j}(N_j)` ⟹
                               `N_j = Orb_{2^j}(x)`
  * `orbProd_fixed`, `orbProd_fixed_pow`
                               `φ^d = id` ⟹ `φ(Orb_d(x)) = Orb_d(x)` (the norm is
                               Frobenius-invariant)
  * `eval_map_of_fixed`        `φ(y) = y` ⟹ `(φC)(y) = φ(C(y))`
  * `eval_orbProd`             `(Orb_d C)(y) = Orb_d(C(y))` for Frobenius-fixed `y`
  * `eval_coset`               `c·F = Q + Γ·H`, `Γ(y) = 0` ⟹ `Q(y) = c·F(y)`
  * `construction_correct`     (Lemma "Correctness of the construction")
                               `c·Orb_d(C) ≡ Q (mod Γ)` ⟹ `Q(y) = c·Orb_d(C(y))`
                               on the roots `y` of `Γ`
  * `composed_correct`         (Lemma "Correctness" of ComposedEval)
                               `P = c₁X + X^{r−1}Q(X^r)` and the coset relation give
                               `P(x) = c₁x + x^{r−1}·c·∏_{i<d} φⁱ(C(x^r))`
-/
import Mathlib

namespace Galois

open Polynomial

section OrbProd
variable {R : Type*} [CommRing R]

/-- The orbit product `Orb_n(x) = ∏_{i<n} φⁱ(x)` of `x` under the endomorphism `φ`
    (for `φ` the Frobenius and `n = d` this is the norm `N_{R/ℤ_{p^e}}(x)`). -/
def orbProd (φ : R →+* R) (n : ℕ) (x : R) : R := ∏ i ∈ Finset.range n, (φ ^ i) x

@[simp] lemma orbProd_zero (φ : R →+* R) (x : R) : orbProd φ 0 x = 1 := by
  simp [orbProd]

@[simp] lemma orbProd_one (φ : R →+* R) (x : R) : orbProd φ 1 x = x := by
  simp [orbProd]

lemma orbProd_succ (φ : R →+* R) (n : ℕ) (x : R) :
    orbProd φ (n + 1) x = orbProd φ n x * (φ ^ n) x := by
  simp [orbProd, Finset.prod_range_succ]

/-- `φ^m` maps the orbit product `∏_{i<n} φⁱ x` to the shifted product `∏_{i<n} φ^{m+i} x`. -/
lemma map_orbProd (φ : R →+* R) (m n : ℕ) (x : R) :
    (φ ^ m) (orbProd φ n x) = ∏ i ∈ Finset.range n, (φ ^ (m + i)) x := by
  unfold orbProd
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [pow_add, RingHom.mul_def, RingHom.comp_apply]

/-- `Orb_{m+n}(x) = Orb_m(x) · φ^m(Orb_n(x))`: the general block-splitting used for
    a slot degree `d` that is not a power of two. -/
theorem orbProd_add (φ : R →+* R) (m n : ℕ) (x : R) :
    orbProd φ (m + n) x = orbProd φ m x * (φ ^ m) (orbProd φ n x) := by
  rw [map_orbProd]
  unfold orbProd
  exact Finset.prod_range_add _ m n

/-- (Lemma "Sub-orbit products from doubling".)  If `N 0 = x` and
    `N (j+1) = N j · φ^{2^j}(N j)`, then `N j = ∏_{i < 2^j} φⁱ(x)` for every `j`. -/
theorem doubling (φ : R →+* R) (x : R) (N : ℕ → R) (h0 : N 0 = x)
    (hs : ∀ j, N (j + 1) = N j * (φ ^ (2 ^ j)) (N j)) (j : ℕ) :
    N j = orbProd φ (2 ^ j) x := by
  induction j with
  | zero => simp [h0]
  | succ j ih =>
      rw [hs, ih, ← orbProd_add, pow_succ, mul_two]

/-- (Proposition "Orbit-product evaluation", power-of-two case.)  The doubling
    schedule reaches `Orb_{2^ℓ}(x)` after `ℓ` products: the recursion
    `N_{j+1} = N_j · φ^{2^j}(N_j)` started at `N_0 = x` has `N_ℓ = Orb_{2^ℓ}(x)`. -/
theorem doubling_schedule (φ : R →+* R) (x : R) (ℓ : ℕ) :
    (fun j => Nat.rec x (fun j N => N * (φ ^ (2 ^ j)) N) j) ℓ = orbProd φ (2 ^ ℓ) x :=
  doubling φ x _ rfl (fun _ => rfl) ℓ

/-- If `φ^d = id` then the orbit product of length `d` is fixed by `φ`
    (the norm lies in the base ring). -/
theorem orbProd_fixed (φ : R →+* R) {d : ℕ} (hφ : φ ^ d = 1) (x : R) :
    φ (orbProd φ d x) = orbProd φ d x := by
  rcases d with _ | m
  · simp
  · have h1 : φ (orbProd φ (m + 1) x) = ∏ i ∈ Finset.range (m + 1), (φ ^ (i + 1)) x := by
      have := map_orbProd φ 1 (m + 1) x
      rw [pow_one] at this
      rw [this]
      apply Finset.prod_congr rfl
      intro i _; rw [add_comm]
    rw [h1, Finset.prod_range_succ, hφ, RingHom.one_def, RingHom.id_apply]
    unfold orbProd
    rw [Finset.prod_range_succ' (fun i => (φ ^ i) x) m, pow_zero, RingHom.one_def,
      RingHom.id_apply]

/-- Every power of `φ` fixes the orbit product of length `d` when `φ^d = id`. -/
theorem orbProd_fixed_pow (φ : R →+* R) {d : ℕ} (hφ : φ ^ d = 1) (x : R) (k : ℕ) :
    (φ ^ k) (orbProd φ d x) = orbProd φ d x := by
  rw [RingHom.coe_pow]
  exact Function.iterate_fixed (orbProd_fixed φ hφ x) k

end OrbProd

/-! ## 2. Orbit products of polynomials and evaluation at Frobenius-fixed points -/
section Poly
variable {R : Type*} [CommRing R]

/-- Powers of the coefficientwise action: `(mapRingHom φ)^i = mapRingHom (φ^i)`. -/
lemma mapRingHom_pow (φ : R →+* R) (i : ℕ) :
    (mapRingHom φ) ^ i = mapRingHom (φ ^ i) := by
  induction i with
  | zero => rw [pow_zero, pow_zero, RingHom.one_def, RingHom.one_def, mapRingHom_id]
  | succ i ih =>
      rw [pow_succ, pow_succ, ih, RingHom.mul_def, RingHom.mul_def, mapRingHom_comp]

/-- `φ(y) = y` ⟹ `(φ C)(y) = φ(C(y))`: evaluation at a Frobenius-fixed point
    commutes with the coefficientwise action. -/
theorem eval_map_of_fixed (φ : R →+* R) {y : R} (hy : φ y = y) (C : R[X]) :
    (C.map φ).eval y = φ (C.eval y) := by
  rw [eval_map]
  conv_lhs => rw [← hy]
  exact eval₂_at_apply φ y

/-- `(Orb_d C)(y) = Orb_d(C(y))` for Frobenius-fixed `y`, where `Orb_d C` is the orbit
    product of `C` under the coefficientwise action. -/
theorem eval_orbProd (φ : R →+* R) {y : R} (hy : φ y = y) (d : ℕ) (C : R[X]) :
    (orbProd (mapRingHom φ) d C).eval y = orbProd φ d (C.eval y) := by
  unfold orbProd
  rw [eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [mapRingHom_pow, coe_mapRingHom]
  have hyi : (φ ^ i) y = y := by
    rw [RingHom.coe_pow]; exact Function.iterate_fixed hy i
  exact eval_map_of_fixed (φ ^ i) hyi C

/-- Coset membership evaluated on a root of `Γ`:
    `c·F = Q + Γ·H` and `Γ(y) = 0` give `Q(y) = c·F(y)`. -/
theorem eval_coset {c : R} {F Q Γ H : R[X]} (h : C c * F = Q + Γ * H) {y : R}
    (hΓ : Γ.eval y = 0) : Q.eval y = c * F.eval y := by
  have := congrArg (Polynomial.eval y) h
  rw [eval_mul, eval_C, eval_add, eval_mul, hΓ, zero_mul, add_zero] at this
  exact this.symm

/-- (Lemma "Correctness of the construction".)  If `c·Orb_d(C) ≡ Q (mod Γ)`, then
    for every Frobenius-fixed root `y` of `Γ`:  `Q(y) = c·∏_{i<d} φⁱ(C(y))`. -/
theorem construction_correct (φ : R →+* R) {c : R} {Q Γ H : R[X]} {d : ℕ} {Cp : R[X]}
    (h : C c * orbProd (mapRingHom φ) d Cp = Q + Γ * H) {y : R} (hy : φ y = y)
    (hΓ : Γ.eval y = 0) : Q.eval y = c * orbProd φ d (Cp.eval y) := by
  rw [eval_coset h hΓ, eval_orbProd φ hy]

/-- (Lemma "Correctness" of ComposedEval.)  With the factored form
    `P = c₁X + X^{r−1}·Q(X^r)` and the coset relation `c·Orb_d(C) ≡ Q (mod Γ)`,
    for every `x` such that `x^r` is Frobenius-fixed and `Γ(x^r) = 0`,
        `P(x) = c₁·x + x^{r−1}·(c·∏_{i<d} φⁱ(C(x^r)))`.
    The right-hand side is exactly what Phases 1–6 of the algorithm compute. -/
theorem composed_correct (φ : R →+* R) {c₁ c : R} {r d : ℕ} {P Q Γ H Cp : R[X]}
    (hP : P = C c₁ * X + X ^ (r - 1) * expand R r Q)
    (h : C c * orbProd (mapRingHom φ) d Cp = Q + Γ * H) {x : R}
    (hx : φ (x ^ r) = x ^ r) (hΓ : Γ.eval (x ^ r) = 0) :
    P.eval x = c₁ * x + x ^ (r - 1) * (c * orbProd φ d (Cp.eval (x ^ r))) := by
  rw [hP, eval_add, eval_mul, eval_C, eval_X, eval_mul, eval_pow, eval_X, expand_eval,
    construction_correct φ h hx hΓ]

end Poly

end Galois
