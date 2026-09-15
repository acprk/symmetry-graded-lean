/-
  Obstruction.lean

  Formal verification (Lean 4 + Mathlib) of

    Theorem "Obstruction for the direct coset at r = 2"
    (Appendix "The obstruction at r = 2 and its repair")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  For the odd filter `P = X·Q(X²)` the pairs `(η, 0)`, `1 ≤ η ≤ B`, force
  `Q((ηA)²) = 0`, so `g = ∏_η (Y − (ηA)²)` is a fixed divisor of `Q`; and a
  simple root of a polynomial over `F_p` prevents it from being an orbit product
  `Orb_d(C) = ∏_{i<d} πⁱ(C)` for `d ≥ 2` (the `m_h = 1` case of the norm
  criterion).  With no unproved placeholders:

  * `eval_odd_filter`, `root_of_odd_filter`
        `P(x) = x·Q(x²)`; `P(x) = 0`, `x ≠ 0` ⟹ `Q(x²) = 0`.
  * `fixed_divisor`, `fixed_divisor_box`, `sq_injective_zmod`
        (Theorem "Obstruction", the fixed divisor)  `g ∣ Q` for the odd filter
        on the box; the roots `(ηA)²`, `1 ≤ η ≤ B`, are distinct in `ZMod p` when
        `2B < p` and `A ≠ 0`.
  * `pow_dvd_orbProd`, `dvd_of_dvd_orbProd`, `pow_dvd_orbProd_of_root`
        `(Y − a) ∣ C ⟹ (Y − a)^d ∣ Orb_d(C)`; conversely (for `π^d = id`)
        `(Y − a) ∣ Orb_d(C) ⟹ (Y − a) ∣ C`, hence `(Y − a)^d ∣ Orb_d(C)`.
  * `rootMultiplicity_orbProd_ge`, `no_simple_root_of_orbProd`
        (Norm criterion, `m_h = 1`)  every root of an orbit product of length
        `d` has multiplicity `≥ d`; for `d ≥ 2` an orbit product has no simple
        root.
  * `obstruction`
        (Theorem "Obstruction", multiplicity part)  if `F ≡ Q (mod Γ)` is an
        orbit product with `d ≥ 2`, then every root `a` of the fixed divisor
        `g` (a root of `Q` and of `Γ`) has `rootMultiplicity a F ≥ 2`.
-/
import Mathlib
import SymmetryGraded.Doubling

namespace Obstruction

open Polynomial

section OddFilter
variable {K : Type*} [Field K]

/-- The odd filter `P = X·Q(X²)` evaluates as `P(x) = x·Q(x²)`. -/
theorem eval_odd_filter (Q : K[X]) (x : K) :
    (X * expand K 2 Q).eval x = x * Q.eval (x ^ 2) := by
  rw [eval_mul, eval_X, expand_eval]

/-- A nonzero root `x` of the odd filter gives a root `x²` of the folded polynomial. -/
theorem root_of_odd_filter (Q : K[X]) {x : K} (hx : x ≠ 0)
    (h : (X * expand K 2 Q).eval x = 0) : Q.eval (x ^ 2) = 0 := by
  rw [eval_odd_filter] at h
  exact (mul_eq_zero.mp h).resolve_left hx

/-- (Theorem "Obstruction", the fixed divisor.)  If the odd filter `X·Q(X²)` vanishes
    at nonzero points `s i`, `i ∈ t`, whose squares are pairwise distinct, then
    `∏_{i ∈ t} (Y − (s i)²)` divides `Q`. -/
theorem fixed_divisor (Q : K[X]) {ι : Type*} (t : Finset ι) (s : ι → K)
    (hdist : ∀ i ∈ t, ∀ j ∈ t, (s i) ^ 2 = (s j) ^ 2 → i = j)
    (hne : ∀ i ∈ t, s i ≠ 0) (hroot : ∀ i ∈ t, (X * expand K 2 Q).eval (s i) = 0) :
    ∏ i ∈ t, (X - C ((s i) ^ 2)) ∣ Q := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    exact fun h => hij (hdist i hi j hj h)
  · intro i hi
    rw [dvd_iff_isRoot]
    exact root_of_odd_filter Q (hne i hi) (hroot i hi)

/-- The points `(ηA)²`, `1 ≤ η ≤ B`, are pairwise distinct in `ZMod p` for a prime
    `p > 2B` and `A ≠ 0`. -/
theorem sq_injective_zmod (p : ℕ) [Fact p.Prime] (A : ZMod p) (hA : A ≠ 0) (B : ℕ)
    (hB : 2 * B < p) :
    ∀ η₁ ∈ Finset.Icc 1 B, ∀ η₂ ∈ Finset.Icc 1 B,
      ((η₁ : ZMod p) * A) ^ 2 = ((η₂ : ZMod p) * A) ^ 2 → η₁ = η₂ := by
  intro η₁ h₁ η₂ h₂ h
  rw [Finset.mem_Icc] at h₁ h₂
  have hsq : ((η₁ : ZMod p) - η₂) * ((η₁ : ZMod p) + η₂) = 0 := by
    have hA2 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA
    have : (((η₁ : ZMod p) ^ 2 - (η₂ : ZMod p) ^ 2)) * A ^ 2 = 0 := by
      linear_combination h
    have := (mul_eq_zero.mp this).resolve_right hA2
    linear_combination this
  rcases mul_eq_zero.mp hsq with h0 | h0
  · -- `p ∣ η₁ − η₂` with `|η₁ − η₂| < p`
    have := sub_eq_zero.mp h0
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · -- `p ∣ η₁ + η₂` with `2 ≤ η₁ + η₂ ≤ 2B < p`: impossible
    exfalso
    have : ((η₁ + η₂ : ℕ) : ZMod p) = 0 := by push_cast; exact h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by omega) this
    omega

/-- (Theorem "Obstruction", the fixed divisor on the box.)  For the odd filter
    `P = X·Q(X²)` over `ZMod p` interpolating the low digit on the box (`P(ηA) = 0`
    for `1 ≤ η ≤ B`), with `A ≠ 0` and `2B < p`:
    `g(Y) = ∏_{η=1}^{B} (Y − (ηA)²)` divides `Q`. -/
theorem fixed_divisor_box (p : ℕ) [Fact p.Prime] (A : ZMod p) (hA : A ≠ 0) (B : ℕ)
    (hB : 2 * B < p) (Q : (ZMod p)[X])
    (hroot : ∀ η ∈ Finset.Icc 1 B, (X * expand (ZMod p) 2 Q).eval ((η : ZMod p) * A) = 0) :
    ∏ η ∈ Finset.Icc 1 B, (X - C (((η : ZMod p) * A) ^ 2)) ∣ Q := by
  apply fixed_divisor Q (Finset.Icc 1 B) (fun η => (η : ZMod p) * A)
    (sq_injective_zmod p A hA B hB)
  · intro η hη
    rw [Finset.mem_Icc] at hη
    apply mul_ne_zero _ hA
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  · exact hroot

end OddFilter

/-! ## 2. Roots of orbit products (the norm criterion for a linear factor) -/
section OrbProd
variable {K : Type*} [Field K]

/-- If `π` fixes `Y − a` and `(Y − a) ∣ C`, then `(Y − a)^d ∣ Orb_d(C) = ∏_{i<d} πⁱ(C)`. -/
theorem pow_dvd_orbProd (π : K[X] →+* K[X]) {a : K} (hπ : π (X - C a) = X - C a) (d : ℕ)
    {Cp : K[X]} (h : X - C a ∣ Cp) : (X - C a) ^ d ∣ Galois.orbProd π d Cp := by
  unfold Galois.orbProd
  have hpow : (X - C a) ^ d = ∏ _i ∈ Finset.range d, (X - C a) := by simp
  rw [hpow]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  have hfix : (π ^ i) (X - C a) = X - C a := by
    rw [RingHom.coe_pow]; exact Function.iterate_fixed hπ i
  rw [← hfix]
  exact map_dvd (π ^ i) h

/-- Conversely, if `π^d = id` and `(Y − a) ∣ Orb_d(C)`, then `(Y − a) ∣ C`. -/
theorem dvd_of_dvd_orbProd (π : K[X] →+* K[X]) {a : K} (hπ : π (X - C a) = X - C a)
    {d : ℕ} (hd : π ^ d = 1) {Cp : K[X]} (h : X - C a ∣ Galois.orbProd π d Cp) :
    X - C a ∣ Cp := by
  unfold Galois.orbProd at h
  obtain ⟨i, hi, hdvd⟩ := (Prime.dvd_finsetProd_iff (prime_X_sub_C a) _).mp h
  rw [Finset.mem_range] at hi
  have hfix : (π ^ (d - i)) (X - C a) = X - C a := by
    rw [RingHom.coe_pow]; exact Function.iterate_fixed hπ _
  have := map_dvd (π ^ (d - i)) hdvd
  rw [hfix, ← RingHom.comp_apply, ← RingHom.mul_def, ← pow_add, Nat.sub_add_cancel hi.le, hd,
    RingHom.one_def, RingHom.id_apply] at this
  exact this

/-- (Norm criterion, `m_h = 1`.)  If `π^d = id`, every linear factor `Y − a` fixed by
    `π` that divides `Orb_d(C)` divides it with multiplicity `≥ d`. -/
theorem pow_dvd_orbProd_of_root (π : K[X] →+* K[X]) {a : K} (hπ : π (X - C a) = X - C a)
    {d : ℕ} (hd : π ^ d = 1) {Cp : K[X]} (h : X - C a ∣ Galois.orbProd π d Cp) :
    (X - C a) ^ d ∣ Galois.orbProd π d Cp :=
  pow_dvd_orbProd π hπ d (dvd_of_dvd_orbProd π hπ hd h)

/-- Every root `a` (with `Y − a` fixed by `π`) of a nonzero orbit product of length
    `d` has root multiplicity at least `d`. -/
theorem rootMultiplicity_orbProd_ge (π : K[X] →+* K[X]) {a : K}
    (hπ : π (X - C a) = X - C a) {d : ℕ} (hd : π ^ d = 1) {Cp F : K[X]}
    (hF : F = Galois.orbProd π d Cp) (hF0 : F ≠ 0) (hroot : F.IsRoot a) :
    d ≤ F.rootMultiplicity a := by
  rw [le_rootMultiplicity_iff hF0, hF]
  apply pow_dvd_orbProd_of_root π hπ hd
  rw [← hF, dvd_iff_isRoot]; exact hroot

/-- (Norm criterion consequence.)  For `d ≥ 2`, an orbit product of length `d` has no
    simple root `a` with `Y − a` fixed by `π`. -/
theorem no_simple_root_of_orbProd (π : K[X] →+* K[X]) {a : K}
    (hπ : π (X - C a) = X - C a) {d : ℕ} (hd2 : 2 ≤ d) (hd : π ^ d = 1) {Cp F : K[X]}
    (hF : F = Galois.orbProd π d Cp) (hF0 : F ≠ 0) :
    F.rootMultiplicity a ≠ 1 := by
  intro h1
  have hroot : F.IsRoot a := by
    by_contra hn
    have := (rootMultiplicity_eq_zero_iff (p := F) (x := a)).mpr (fun h => absurd h hn)
    omega
  have := rootMultiplicity_orbProd_ge π hπ hd hF hF0 hroot
  omega

/-- (Theorem "Obstruction for the direct coset at r = 2", multiplicity part.)
    Let `F = Q + Γ·H` be a member of the coset `Q + (Γ)` which is an orbit product
    of length `d ≥ 2`.  Then every common root `a` of `Q` and `Γ` (in particular every
    root of the fixed divisor `g`) is a root of `F` of multiplicity `≥ d ≥ 2`; so the
    root cannot be simple.  In the paper this is the condition `c = −Q₁(a)/Γ₁(a)`
    imposed for each root of `g`. -/
theorem obstruction (π : K[X] →+* K[X]) {a : K} (hπ : π (X - C a) = X - C a)
    {d : ℕ} (hd2 : 2 ≤ d) (hd : π ^ d = 1) {Cp F Q Γ H : K[X]}
    (hF : F = Galois.orbProd π d Cp) (hcoset : F = Q + Γ * H) (hF0 : F ≠ 0)
    (hQ : Q.eval a = 0) (hΓ : Γ.eval a = 0) :
    2 ≤ F.rootMultiplicity a := by
  have hroot : F.IsRoot a := by
    rw [IsRoot.def, hcoset, eval_add, eval_mul, hQ, hΓ]; ring
  exact le_trans hd2 (rootMultiplicity_orbProd_ge π hπ hd hF hF0 hroot)

end OrbProd

end Obstruction
