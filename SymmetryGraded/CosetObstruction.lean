/-
  CosetObstruction.lean

  Formal verification (Lean 4 + Mathlib) of the final assembly of

    Theorem "Obstruction for the direct coset at r = 2"
    (Appendix "The obstruction at r = 2 and its repair")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  `Obstruction.lean` proves the fixed divisor `g ∣ Q`, the multiplicity obstruction
  (`rootMultiplicity ≥ d` at a common root of `Q` and `Γ`) and the per-root condition.
  What is added here is the paper's conclusion: each root of the fixed divisor imposes
  one condition on the single scalar `c`, so when two of the `B` values
  `−Q₁(a)/Γ₁(a)` differ, no member of the direct coset `Q + (Γ)` is an orbit product at
  any `d ≥ 2`.  With no unproved placeholders:

  * `prod_X_sub_C_ne_zero`, `rootMultiplicity_prod_X_sub_C`
        the vanishing polynomial of a finite set is nonzero and has every point of the
        set as a simple root.
  * `coset_scalar_eq`
        (Theorem "Obstruction", the coset condition)  from `Q = g·Q₁`, `Γ = g·Γ₁` and a
        root `a` of `g` with `Γ₁(a) ≠ 0`: if `Q + cΓ` is an orbit product of length
        `d ≥ 2` then `c = −Q₁(a)/Γ₁(a)`.
  * `no_norm_form_of_distinct_values`
        (Theorem "Obstruction", conclusion)  two roots with distinct values leave no
        admissible `c`: the direct coset contains no norm form at any `d ≥ 2`.
-/
import Mathlib
import SymmetryGraded.Obstruction

namespace Obstruction

open Polynomial

/-! ## The final assembly: `B` conditions on one scalar -/
section Assembly
variable {K : Type*} [Field K]

/-- The vanishing polynomial of a finite set is nonzero. -/
theorem prod_X_sub_C_ne_zero (W : Finset K) : (∏ y ∈ W, (X - C y)) ≠ 0 :=
  (monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y).ne_zero

/-- Every point of a finite set is a simple root of its vanishing polynomial. -/
theorem rootMultiplicity_prod_X_sub_C [DecidableEq K] (W : Finset K) {a : K} (ha : a ∈ W) :
    (∏ y ∈ W, (X - C y)).rootMultiplicity a = 1 := by
  rw [← count_roots, roots_prod_X_sub_C]
  exact Multiset.count_eq_one_of_mem W.nodup ha

/-- (Theorem "Obstruction for the direct coset at `r = 2`", the coset condition.)  Let
    `g = ∏_{y ∈ W}(Y − y)` be the fixed divisor of the direct coset, `Q = g·Q₁` and
    `Γ = g·Γ₁`, and let `a ∈ W` be a root at which `Γ₁(a) ≠ 0`, i.e. a simple root of `Γ`.
    If the member `F = Q + cΓ` of the coset is an orbit product of length `d ≥ 2`, then
    the scalar `c` is pinned down:  `c = −Q₁(a)/Γ₁(a)`. -/
theorem coset_scalar_eq [DecidableEq K] (π : K[X] →+* K[X]) (W : Finset K) {a : K}
    (ha : a ∈ W) (hπ : π (X - C a) = X - C a) {d : ℕ} (hd2 : 2 ≤ d) (hd : π ^ d = 1)
    {Q Γ Q₁ Γ₁ Cp : K[X]} {c : K}
    (hQ : Q = (∏ y ∈ W, (X - C y)) * Q₁) (hΓ : Γ = (∏ y ∈ W, (X - C y)) * Γ₁)
    (hΓ₁ : Γ₁.eval a ≠ 0)
    (hF : Q + C c * Γ = Galois.orbProd π d Cp) (hF0 : Q + C c * Γ ≠ 0) :
    c = -(Q₁.eval a) / Γ₁.eval a := by
  set g : K[X] := ∏ y ∈ W, (X - C y) with hg
  have hga : g.eval a = 0 := by
    rw [hg, eval_prod]
    exact Finset.prod_eq_zero ha (by simp)
  have hsplit : Q + C c * Γ = g * (Q₁ + C c * Γ₁) := by rw [hQ, hΓ]; ring
  have hfac0 : Q₁ + C c * Γ₁ ≠ 0 := by
    intro h
    rw [hsplit, h, mul_zero] at hF0
    exact hF0 rfl
  have hroot : (Q + C c * Γ).IsRoot a := by
    rw [IsRoot.def, hsplit, eval_mul, hga, zero_mul]
  have hmult : d ≤ (Q + C c * Γ).rootMultiplicity a :=
    rootMultiplicity_orbProd_ge π hπ hd hF hF0 hroot
  have hg0 : g ≠ 0 := prod_X_sub_C_ne_zero W
  have hmul : (Q + C c * Γ).rootMultiplicity a =
      g.rootMultiplicity a + (Q₁ + C c * Γ₁).rootMultiplicity a := by
    rw [hsplit]
    exact rootMultiplicity_mul (by rw [← hsplit]; exact hF0)
  rw [hmul, rootMultiplicity_prod_X_sub_C W ha] at hmult
  have hpos : 0 < (Q₁ + C c * Γ₁).rootMultiplicity a := by omega
  have hr2 : (Q₁ + C c * Γ₁).IsRoot a := (rootMultiplicity_pos hfac0).mp hpos
  rw [IsRoot.def, eval_add, eval_mul, eval_C] at hr2
  field_simp
  linear_combination hr2

/-- (Theorem "Obstruction for the direct coset at `r = 2`", conclusion.)  The roots of the
    fixed divisor impose one condition each on the single scalar `c`.  When two of the
    values `−Q₁(a)/Γ₁(a)` differ, no member `Q + cΓ` of the direct coset is an orbit
    product of length `d`, at any `d ≥ 2`: the direct coset contains no norm form. -/
theorem no_norm_form_of_distinct_values [DecidableEq K] (π : K[X] →+* K[X]) (W : Finset K)
    {a b : K} (ha : a ∈ W) (hb : b ∈ W)
    (hπa : π (X - C a) = X - C a) (hπb : π (X - C b) = X - C b)
    {d : ℕ} (hd2 : 2 ≤ d) (hd : π ^ d = 1)
    {Q Γ Q₁ Γ₁ : K[X]}
    (hQ : Q = (∏ y ∈ W, (X - C y)) * Q₁) (hΓ : Γ = (∏ y ∈ W, (X - C y)) * Γ₁)
    (hΓ₁a : Γ₁.eval a ≠ 0) (hΓ₁b : Γ₁.eval b ≠ 0)
    (hdist : -(Q₁.eval a) / Γ₁.eval a ≠ -(Q₁.eval b) / Γ₁.eval b) (c : K) :
    ¬ ∃ Cp : K[X], Q + C c * Γ = Galois.orbProd π d Cp ∧ Q + C c * Γ ≠ 0 := by
  rintro ⟨Cp, hF, hF0⟩
  apply hdist
  rw [← coset_scalar_eq π W ha hπa hd2 hd hQ hΓ hΓ₁a hF hF0,
    ← coset_scalar_eq π W hb hπb hd2 hd hQ hΓ hΓ₁b hF hF0]

end Assembly

end Obstruction
