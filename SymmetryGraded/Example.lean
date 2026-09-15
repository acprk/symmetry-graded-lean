/-
  Example.lean

  Machine-checked worked examples of

    "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping"

  over `F = ZMod 31` (Appendix "The folded evaluation: worked example",
  Appendix "Cost and depth of ComposedEval: the example continued", and the
  `r = 2` obstruction example of Appendix "The obstruction at r = 2").
  Every numerical claim is verified by `decide` (kernel evaluation in `ZMod 31`)
  and every polynomial identity by `linear_combination` against `31 = 0`.

  * Order six, `A = 6`, hexagon `B = 2`: `6² = 6 − 1`; the 19 hexagon pairs map
    injectively; `P = 23X + 29X⁵ + 12X¹¹ + 30X¹⁷` interpolates the low digit on
    all 19 pairs and satisfies the functional equation at every support point;
    `P` satisfies the *polynomial* functional equation `P(6X) = 6⁻¹(P(X) − X)`,
    so the Order-six character filter theorem applies and predicts
    `c₁ = (1 − 6²)⁻¹ = 23`; `P = 23X + X⁵Q(X⁶)` with `Q = 29 + 12Y + 30Y²`.
  * Composed evaluation, `d = 3`: the folded support is `{1, 2, 4}`,
    `Γ = (Y−1)(Y−2)(Y−4) = Y³ + 24Y² + 14Y + 23`, `F = Γ + 16Q = Y³ + 8Y² + 20Y + 22`
    has no root in `F₃₁` (hence is irreducible), and `2F = Q` on the folded support.
  * The `r = 2` obstruction, `A = 5`, box `B = 2`: `P = X·Q(X²)` with the stated
    degree-11 `Q` interpolates the 25 box points, and `g = Y² + 30Y + 20 =
    (Y − 25)(Y − 7)` divides `Q` — both by explicit quotient and through the
    theorem `Obstruction.fixed_divisor_box`.
  * (round 4) The root `α ∈ L = F₃₁[Y]/(F) ≅ F_{31³}` of `F`: `α³ = 23α² + 11α + 9`, the
    Frobenius images `α³¹ = 4 + 7α + 17α²`, `α⁹⁶¹ = 19 + 23α + 14α²` (the second by
    additivity of `x ↦ x³¹` in characteristic 31), the elementary symmetric functions
    `−8, 20, −22` of the three conjugates, and hence `F = ∏_{i<3}(Y − α^{31ⁱ}) = Orb₃(Y − α)`
    as a `Galois.orbProd` for the Frobenius of `NormCriterion.lean`; `[L : F₃₁] = 3`.
-/
import Mathlib
import SymmetryGraded.OrderSix
import SymmetryGraded.Lattice
import SymmetryGraded.Doubling
import SymmetryGraded.Obstruction
import SymmetryGraded.NormCriterion

namespace Example

open Polynomial

/-- The prime field `F₃₁`. -/
abbrev F := ZMod 31

instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

/-- `31 = 0` in `F[X]`, the tool for checking polynomial identities modulo 31. -/
lemma h31 : (31 : F[X]) = 0 := by
  rw [show (31 : F[X]) = C (31 : F) from (map_ofNat C 31).symm, show (31 : F) = 0 by decide,
    C_0]

/-! ## 1. Order six on the hexagon: `p = 31`, `A = 6`, `B = 2` -/

/-- `A = 6` is a root of `Φ₆ = X² − X + 1` modulo 31. -/
theorem A_sq : (6 : F) ^ 2 = 6 - 1 := by decide

theorem two_ne_zero' : (2 : F) ≠ 0 := by decide
theorem three_ne_zero' : (3 : F) ≠ 0 := by decide

/-- `A⁻¹ = 26`. -/
theorem A_inv : (6 : F)⁻¹ = 26 := inv_eq_of_mul_eq_one_right (by decide)

/-- The 19 digit pairs of the hexagon `T₂ = {|η|, |λ|, |η + λ| ≤ 2}`. -/
def hexPairs : List (ℤ × ℤ) := [(-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0)]

theorem hexPairs_length : hexPairs.length = 19 := by decide

/-- Every listed pair lies in the hexagon, and every hexagon pair is listed. -/
theorem hexPairs_sound : ∀ v ∈ hexPairs, OrderSix.hexNorm v.1 v.2 ≤ 2 := by decide

theorem hexPairs_complete :
    ∀ a ∈ List.range 5, ∀ b ∈ List.range 5,
      OrderSix.hexNorm ((a : ℤ) - 2) ((b : ℤ) - 2) ≤ 2 →
        ((a : ℤ) - 2, (b : ℤ) - 2) ∈ hexPairs := by decide

/-- The encoding `φ_A(η, λ) = 6η + λ` is injective on the hexagon (19 distinct images). -/
theorem phi_injective_on_hex : (hexPairs.map (DigitLattice.phi (6 : F))).Nodup := by decide

/-- The support `S_A = φ_A(T₂)`. -/
theorem support_eq : hexPairs.map (DigitLattice.phi (6 : F)) =
    [19, 20, 21, 24, 25, 26, 27, 29, 30, 0, 1, 2, 4, 5, 6, 7, 10, 11, 12] := by decide

/-- The digit-extraction polynomial `P = 23X + 29X⁵ + 12X¹¹ + 30X¹⁷`. -/
noncomputable def P : F[X] := 23 * X + 29 * X ^ 5 + 12 * X ^ 11 + 30 * X ^ 17

theorem eval_P (x : F) : P.eval x = 23 * x + 29 * x ^ 5 + 12 * x ^ 11 + 30 * x ^ 17 := by
  simp [P]

/-- `P` interpolates the low digit: `P(6η + λ) = λ` on all 19 hexagon pairs. -/
theorem P_interpolates : ∀ v ∈ hexPairs, P.eval (DigitLattice.phi 6 v) = (v.2 : F) := by
  have key : ∀ v ∈ hexPairs,
      23 * DigitLattice.phi (6 : F) v + 29 * (DigitLattice.phi (6 : F) v) ^ 5 +
        12 * (DigitLattice.phi (6 : F) v) ^ 11 + 30 * (DigitLattice.phi (6 : F) v) ^ 17 =
        (v.2 : F) := by decide
  intro v hv; rw [eval_P]; exact key v hv

/-- The functional equation `P(Aw) = A⁻¹(P(w) − w)` holds at every support point. -/
theorem fe_on_support :
    ∀ v ∈ hexPairs, P.eval (6 * DigitLattice.phi 6 v) =
      26 * (P.eval (DigitLattice.phi 6 v) - DigitLattice.phi 6 v) := by
  have key : ∀ v ∈ hexPairs,
      23 * (6 * DigitLattice.phi (6 : F) v) + 29 * (6 * DigitLattice.phi (6 : F) v) ^ 5 +
        12 * (6 * DigitLattice.phi (6 : F) v) ^ 11 + 30 * (6 * DigitLattice.phi (6 : F) v) ^ 17
      = 26 * ((23 * DigitLattice.phi (6 : F) v + 29 * (DigitLattice.phi (6 : F) v) ^ 5 +
        12 * (DigitLattice.phi (6 : F) v) ^ 11 + 30 * (DigitLattice.phi (6 : F) v) ^ 17)
        - DigitLattice.phi (6 : F) v) := by decide
  intro v hv; rw [eval_P, eval_P]; exact key v hv

/-- The genuine polynomial functional equation `P(6X) = 6⁻¹·(P(X) − X)` in `F[X]`. -/
theorem P_fe : P.comp (C (6 : F) * X) = C (6 : F)⁻¹ * (P - X) := by
  rw [A_inv, show (C (6 : F) : F[X]) = 6 from map_ofNat C 6,
    show (C (26 : F) : F[X]) = 26 from map_ofNat C 26]
  simp only [P, add_comp, mul_comp, pow_comp, X_comp, ofNat_comp]
  linear_combination ((-14) * X^1 + (7250) * X^5 + (140437560) * X^11 + (16380638172300) * X^17) * h31

/-- The Order-six character filter theorem applied to the example: the support is in
    `{1} ∪ {k ≡ 5 (mod 6)}` and `c₁ = (1 − A²)⁻¹`. -/
theorem P_filter :
    (∀ k, k ≠ 1 → k % 6 ≠ 5 → P.coeff k = 0) ∧ P.coeff 1 = (1 - (6 : F) ^ 2)⁻¹ := by
  obtain ⟨h1, -, h3⟩ := OrderSix.order_six_filter A_sq two_ne_zero' three_ne_zero' P P_fe
  exact ⟨h1, h3⟩

/-- `c₁ = (1 − 36)⁻¹ = 23` in `F₃₁`, matching the linear coefficient of `P`. -/
theorem c1_eq : (1 - (6 : F) ^ 2)⁻¹ = 23 := inv_eq_of_mul_eq_one_right (by decide)

/-- The folded polynomial `Q(Y) = 29 + 12Y + 30Y²`, with `P = 23X + X⁵·Q(X⁶)`. -/
noncomputable def Qhex : F[X] := 29 + 12 * X + 30 * X ^ 2

theorem P_factored : P = 23 * X + X ^ 5 * expand F 6 Qhex := by
  simp only [P, Qhex, map_add, map_mul, map_pow, expand_X, map_ofNat]
  ring

theorem eval_Qhex (y : F) : Qhex.eval y = 29 + 12 * y + 30 * y ^ 2 := by simp [Qhex]

/-! ## 2. The composed evaluation with `d = 3` -/

/-- The folded support `{x⁶ : x ∈ S_A ∖ {0}} = {1, 2, 4}`. -/
theorem folded_support :
    ∀ v ∈ hexPairs, DigitLattice.phi (6 : F) v ≠ 0 →
      (DigitLattice.phi (6 : F) v) ^ 6 ∈ [(1 : F), 2, 4] := by decide

/-- `Γ = (Y − 1)(Y − 2)(Y − 4) = Y³ + 24Y² + 14Y + 23`. -/
noncomputable def Γ : F[X] := X ^ 3 + 24 * X ^ 2 + 14 * X + 23

theorem Γ_eq : Γ = (X - 1) * (X - 2) * (X - 4) := by
  unfold Γ; linear_combination (X ^ 2 + 1) * h31

theorem eval_Γ (y : F) : Γ.eval y = y ^ 3 + 24 * y ^ 2 + 14 * y + 23 := by simp [Γ]

theorem Γ_vanishes : ∀ y ∈ [(1 : F), 2, 4], Γ.eval y = 0 := by
  intro y hy; rw [eval_Γ]; revert y; decide

/-- The coset member `F = Γ + 16·Q = Y³ + 8Y² + 20Y + 22`. -/
noncomputable def Fpoly : F[X] := X ^ 3 + 8 * X ^ 2 + 20 * X + 22

theorem Fpoly_eq : Fpoly = Γ + 16 * Qhex := by
  unfold Fpoly Γ Qhex; linear_combination (-15 - 6 * X - 16 * X ^ 2) * h31

theorem eval_Fpoly (y : F) : Fpoly.eval y = y ^ 3 + 8 * y ^ 2 + 20 * y + 22 := by simp [Fpoly]

/-- `F` has no root in `F₃₁`. -/
theorem Fpoly_no_root : ∀ y : F, Fpoly.eval y ≠ 0 := by
  intro y; rw [eval_Fpoly]; revert y; decide

theorem Fpoly_natDegree : Fpoly.natDegree = 3 := by
  unfold Fpoly; compute_degree!

/-- A cubic without roots is irreducible: `F` is irreducible over `F₃₁`, hence (by the
    norm criterion) a norm form `Orb₃(Y − α)` for a root `α ∈ F₃₁³`. -/
theorem Fpoly_irreducible : Irreducible Fpoly := by
  have hne : Fpoly ≠ 0 := by
    intro h; have := Fpoly_natDegree; rw [h, natDegree_zero] at this; omega
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [Fpoly_natDegree]; norm_num)
    (by rw [Fpoly_natDegree])]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro y hy
  rw [mem_roots hne, IsRoot.def] at hy
  exact Fpoly_no_root y hy

/-- `2·F ≡ Q` on the folded support (the coset relation `c·F ≡ Q (mod Γ)` with `c = 2`). -/
theorem two_F_eq_Q : ∀ y ∈ [(1 : F), 2, 4], 2 * Fpoly.eval y = Qhex.eval y := by
  intro y hy; rw [eval_Fpoly, eval_Qhex]; revert y; decide

/-- The same, as the polynomial coset identity `C 2 · F = Q + Γ · 2`
    (input to `Galois.eval_coset` / `Galois.composed_correct`). -/
theorem coset_identity : C (2 : F) * Fpoly = Qhex + Γ * 2 := by
  rw [show (C (2 : F) : F[X]) = 2 from map_ofNat C 2, Fpoly_eq]
  linear_combination Qhex * h31

/-- Consequently `P(x) = 23x + x⁵·(2·F(x⁶))` for every `x` with `x⁶` a root of `Γ`. -/
theorem P_eval_via_F (x : F) (hx : Γ.eval (x ^ 6) = 0) :
    P.eval x = 23 * x + x ^ 5 * (2 * Fpoly.eval (x ^ 6)) := by
  rw [P_factored, eval_add, eval_mul, eval_mul, eval_pow, eval_X, expand_eval,
    Galois.eval_coset coset_identity hx]
  simp

/-! ## 3. The `r = 2` obstruction: `p = 31`, `A = 5`, box `B = 2` -/

/-- The 25 digit pairs of the box `[−2, 2]²`. -/
def boxPairs : List (ℤ × ℤ) := [(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2)]

theorem boxPairs_length : boxPairs.length = 25 := by decide

/-- `φ_A` with `A = 5` is injective on the box (`2B(|A| + 1) = 24 < 31`). -/
theorem phi5_injective_on_box : (boxPairs.map (DigitLattice.phi (5 : F))).Nodup := by decide

/-- The folded polynomial of the odd filter (degree 11), from the interpolant
    `P = X·Q(X²)` on the 25 box points. -/
noncomputable def Qodd : F[X] :=
  23 + 28 * X + 4 * X ^ 2 + 22 * X ^ 3 + 13 * X ^ 4 + 13 * X ^ 5 + 20 * X ^ 6 + 9 * X ^ 7 +
    8 * X ^ 8 + 6 * X ^ 9 + 12 * X ^ 10 + 29 * X ^ 11

theorem eval_Qodd (y : F) : Qodd.eval y =
    23 + 28 * y + 4 * y ^ 2 + 22 * y ^ 3 + 13 * y ^ 4 + 13 * y ^ 5 + 20 * y ^ 6 + 9 * y ^ 7 +
      8 * y ^ 8 + 6 * y ^ 9 + 12 * y ^ 10 + 29 * y ^ 11 := by
  simp [Qodd]

/-- `P = X·Q(X²)` interpolates the low digit on all 25 box points. -/
theorem Podd_interpolates :
    ∀ v ∈ boxPairs, (X * expand F 2 Qodd).eval (DigitLattice.phi 5 v) = (v.2 : F) := by
  have key : ∀ v ∈ boxPairs, DigitLattice.phi (5 : F) v *
      (23 + 28 * (DigitLattice.phi (5 : F) v) ^ 2 + 4 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 2 +
        22 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 3 + 13 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 4 +
        13 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 5 + 20 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 6 +
        9 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 7 + 8 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 8 +
        6 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 9 + 12 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 10 +
        29 * ((DigitLattice.phi (5 : F) v) ^ 2) ^ 11) = (v.2 : F) := by decide
  intro v hv
  rw [Obstruction.eval_odd_filter, eval_Qodd]
  exact key v hv

/-- The fixed divisor `g = Y² + 30Y + 20 = (Y − 25)(Y − 7)` (`25 = 5²`, `7 = 10²`). -/
noncomputable def g : F[X] := X ^ 2 + 30 * X + 20

theorem g_eq : g = (X - 25) * (X - 7) := by
  unfold g; linear_combination (2 * X - 5) * h31

/-- The explicit quotient `H = Q / g`. -/
noncomputable def H : F[X] :=
  12 + 2 * X + 9 * X ^ 2 + 3 * X ^ 3 + 5 * X ^ 4 + 24 * X ^ 5 + 19 * X ^ 6 + 25 * X ^ 7 +
    10 * X ^ 8 + 29 * X ^ 9

theorem Qodd_eq_g_mul_H : Qodd = g * H := by
  unfold Qodd g H
  linear_combination (-7 - 12 * X - 8 * X ^ 2 - 10 * X ^ 3 - 6 * X ^ 4 - 20 * X ^ 5 -
    35 * X ^ 6 - 35 * X ^ 7 - 31 * X ^ 8 - 29 * X ^ 9 - 28 * X ^ 10) * h31

/-- `g ∣ Q` (explicit quotient). -/
theorem g_dvd_Qodd : g ∣ Qodd := ⟨H, Qodd_eq_g_mul_H⟩

/-- `g ∣ Q` through the theorem `Obstruction.fixed_divisor_box`: the pairs `(1, 0)` and
    `(2, 0)` force `Q(25) = Q(7) = 0`. -/
theorem g_dvd_Qodd' : g ∣ Qodd := by
  have hroot : ∀ η ∈ Finset.Icc (1 : ℕ) 2, (X * expand F 2 Qodd).eval ((η : F) * 5) = 0 := by
    intro η hη
    rw [Obstruction.eval_odd_filter, eval_Qodd]
    revert η; decide
  have hdvd := Obstruction.fixed_divisor_box 31 (5 : F) (by decide) 2 (by norm_num) Qodd hroot
  have hprod : ∏ η ∈ Finset.Icc (1 : ℕ) 2, (X - C ((((η : ℕ) : F) * 5) ^ 2)) = g := by
    rw [show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    rw [show (((1 : ℕ) : F) * 5) ^ 2 = 25 by decide, show (((2 : ℕ) : F) * 5) ^ 2 = 7 by decide,
      show (C (25 : F) : F[X]) = 25 from map_ofNat C 25,
      show (C (7 : F) : F[X]) = 7 from map_ofNat C 7, g_eq]
  rwa [hprod] at hdvd

/-- `Q` vanishes at both roots of `g` (the two conditions `c = −Q₁(a)/Γ₁(a)` of the
    obstruction theorem come from these two roots). -/
theorem Qodd_roots : Qodd.eval 25 = 0 ∧ Qodd.eval 7 = 0 := by
  rw [eval_Qodd, eval_Qodd]; decide

/-! ## 4. The root `α ∈ F_{31³}` with `F = Orb₃(Y − α)` -/

instance : Fact (Irreducible Fpoly) := ⟨Fpoly_irreducible⟩

/-- The cubic extension `L = F₃₁[Y]/(F) ≅ F_{31³}`. -/
abbrev L := AdjoinRoot Fpoly

/-- The root `α` of `F` in `L`. -/
noncomputable def α : L := AdjoinRoot.root Fpoly

theorem Fpoly_ne_zero : Fpoly ≠ 0 := Fpoly_irreducible.ne_zero

/-- `[L : F₃₁] = 3`. -/
theorem finrank_L : Module.finrank F L = 3 := by
  rw [(AdjoinRoot.powerBasis Fpoly_ne_zero).finrank, AdjoinRoot.powerBasis_dim, Fpoly_natDegree]

instance : Module.Finite F L := (AdjoinRoot.powerBasis Fpoly_ne_zero).finite
instance : Finite L := Module.finite_of_finite F

/-- `31 = 0` in `L`. -/
lemma h31L : (31 : L) = 0 := by
  rw [show (31 : L) = algebraMap F L 31 from (map_ofNat _ 31).symm, show (31 : F) = 0 by decide,
    map_zero]

/-- The defining relation `α³ = −8α² − 20α − 22 = 23α² + 11α + 9`. -/
theorem α_cube : α ^ 3 = 23 * α ^ 2 + 11 * α + 9 := by
  have h : AdjoinRoot.mk Fpoly (X ^ 3 + 8 * X ^ 2 + 20 * X + 22) = 0 := AdjoinRoot.mk_self
  have hX : AdjoinRoot.mk Fpoly X = α := AdjoinRoot.mk_X
  rw [map_add, map_add, map_add, map_pow, map_mul, map_pow, map_mul, hX,
    show (8 : F[X]) = C 8 from (map_ofNat C 8).symm,
    show (20 : F[X]) = C 20 from (map_ofNat C 20).symm,
    show (22 : F[X]) = C 22 from (map_ofNat C 22).symm, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
    AdjoinRoot.mk_C, map_ofNat, map_ofNat, map_ofNat] at h
  linear_combination h - (α ^ 2 + α + 1) * h31L

theorem α_pow_four : α ^ 4 = 21 + 14 * α + 13 * α ^ 2 := by
  linear_combination (α + 23) * α_cube + (17 * α ^ 2 + 8 * α + 6) * h31L

theorem α_pow_eight : α ^ 8 = 12 + 14 * α + 27 * α ^ 2 := by
  linear_combination (α ^ 4 + (21 + 14 * α + 13 * α ^ 2)) * α_pow_four +
    (169 * α + 4251) * α_cube + (3237 * α ^ 2 + 1576 * α + 1248) * h31L

theorem α_pow_sixteen : α ^ 16 = 30 + 10 * α + 26 * α ^ 2 := by
  linear_combination (α ^ 8 + (12 + 14 * α + 27 * α ^ 2)) * α_pow_eight +
    (729 * α + 17523) * α_cube + (13286 * α ^ 2 + 6440 * α + 5091) * h31L

/-- The Frobenius image `α³¹ = 4 + 7α + 17α²`. -/
theorem α_pow_31 : α ^ 31 = 4 + 7 * α + 17 * α ^ 2 := by
  linear_combination α ^ 15 * α_pow_sixteen +
    (30 + 10 * α + 26 * α ^ 2) * α ^ 7 * α_pow_eight +
    (30 + 10 * α + 26 * α ^ 2) * (12 + 14 * α + 27 * α ^ 2) * α ^ 3 * α_pow_four +
    (9126 * α ^ 6 + 227968 * α ^ 5 + 5383674 * α ^ 4 + 126452286 * α ^ 3 + 2969713446 * α ^ 2 +
      69742853850 * α + 1637890564590) * α_cube +
    (1240818767707 * α ^ 2 + 601434899843 * α + 475516615526) * h31L

instance : CharP L 31 := charP_of_injective_algebraMap (algebraMap F L).injective 31

/-- Constants of `F₃₁` are Frobenius-fixed in `L`. -/
lemma const_pow_31 (c : F) : (algebraMap F L c) ^ 31 = algebraMap F L c := by
  rw [← map_pow, ZMod.pow_card]

/-- The second Frobenius image `α⁹⁶¹ = (α³¹)³¹ = 19 + 23α + 14α²`, by additivity of the
    Frobenius in characteristic 31. -/
theorem α_pow_961 : α ^ 961 = 19 + 23 * α + 14 * α ^ 2 := by
  have h : α ^ 961 = (4 + 7 * α + 17 * α ^ 2) ^ 31 := by
    rw [← α_pow_31, ← pow_mul]
  have h4 : (4 : L) ^ 31 = 4 := by
    rw [show (4 : L) = algebraMap F L 4 from (map_ofNat _ 4).symm, const_pow_31]
  have h7 : (7 : L) ^ 31 = 7 := by
    rw [show (7 : L) = algebraMap F L 7 from (map_ofNat _ 7).symm, const_pow_31]
  have h17 : (17 : L) ^ 31 = 17 := by
    rw [show (17 : L) = algebraMap F L 17 from (map_ofNat _ 17).symm, const_pow_31]
  rw [h, add_pow_char _ _ 31, add_pow_char _ _ 31, mul_pow, mul_pow, pow_right_comm α 2 31,
    h4, h7, h17, α_pow_31]
  linear_combination (4913 * α + 117045) * α_cube + (88688 * α ^ 2 + 42990 * α + 33990) * h31L

/-- The elementary symmetric functions of the three conjugates:
    `α + α³¹ + α⁹⁶¹ = −8`, `Σ αⁱαʲ = 20`, `α·α³¹·α⁹⁶¹ = −22`. -/
theorem conj_sum : α + α ^ 31 + α ^ 961 = 23 := by
  rw [α_pow_31, α_pow_961]; linear_combination (α ^ 2 + α) * h31L

theorem conj_e2 : α * α ^ 31 + α ^ 31 * α ^ 961 + α ^ 961 * α = 20 := by
  rw [α_pow_31, α_pow_961]
  linear_combination (238 * α + 5994) * α_cube + (4550 * α ^ 2 + 2204 * α + 1742) * h31L

theorem conj_prod : α * α ^ 31 * α ^ 961 = 9 := by
  rw [α_pow_31, α_pow_961]
  linear_combination (238 * α ^ 2 + 5963 * α + 140307) * α_cube +
    (106291 * α ^ 2 + 51520 * α + 40734) * h31L

/-- `Fpoly` with its constants written under `C`. -/
theorem Fpoly_C_form : Fpoly = X ^ 3 + C 8 * X ^ 2 + C 20 * X + C 22 := by
  unfold Fpoly; simp only [map_ofNat]

/-- **`F = ∏_{i<3} (Y − α^{31ⁱ})` over `L`**: the coset member `F` of the worked example is
    the orbit product of the linear factor `Y − α`. -/
theorem Fpoly_eq_conjProd :
    Fpoly.map (algebraMap F L) = ∏ i ∈ Finset.range 3, (X - C (α ^ (31 ^ i))) := by
  have key : ∀ a b c : L, (X - C a) * (X - C b) * (X - C c) =
      X ^ 3 - C (a + b + c) * X ^ 2 + C (a * b + b * c + c * a) * X - C (a * b * c) := by
    intro a b c; simp only [map_add, map_mul]; ring
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one,
    show (31 : ℕ) ^ 2 = 961 by norm_num]
  rw [key, conj_sum, conj_e2, conj_prod, congrArg (Polynomial.map (algebraMap F L)) Fpoly_C_form]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C]
  rw [map_ofNat (algebraMap F L) 8, map_ofNat (algebraMap F L) 20, map_ofNat (algebraMap F L) 22,
    show (8 : L) = -23 by linear_combination h31L, show (22 : L) = -9 by linear_combination h31L]
  simp only [map_neg]
  ring

/-- The Frobenius of `L/F₃₁` is `x ↦ x³¹`. -/
theorem frob_apply_L (x : L) : (NormCriterion.frob : L ≃ₐ[F] L) x = x ^ 31 := by
  rw [NormCriterion.frob_apply, ZMod.card]

theorem frob_pow_apply_L (i : ℕ) (x : L) :
    ((NormCriterion.frob : L ≃ₐ[F] L) ^ i) x = x ^ (31 ^ i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, ih, frob_apply_L, ← pow_mul, pow_succ]

/-- `Orb₃(Y − α) = ∏_{i<3} (Y − Frobⁱ α) = F` over `L` (the conjugate product of
    `NormCriterion.lean`). -/
theorem conjProd_eq :
    NormCriterion.conjProd (NormCriterion.frob : L ≃ₐ[F] L) 3 α = Fpoly.map (algebraMap F L) := by
  rw [Fpoly_eq_conjProd, NormCriterion.conjProd]
  exact Finset.prod_congr rfl (fun i _ => by rw [frob_pow_apply_L])

/-- **The worked example instantiated in the norm criterion**: `F = Orb₃(Y − α)` as a
    Frobenius orbit product in the sense of `Galois.orbProd`. -/
theorem Fpoly_orbProd :
    Fpoly.map (algebraMap F L) =
      Galois.orbProd (mapRingHom (NormCriterion.toHom (NormCriterion.frob : L ≃ₐ[F] L))) 3
        (X - C α) := by
  rw [← NormCriterion.conjProd_eq_orbProd, conjProd_eq]

/-- `α` is a root of `F` (`aeval α F = 0`), so the abstract theorem
    `NormCriterion.irreducible_eq_orbProd` applies to this `α`. -/
theorem aeval_α_Fpoly : aeval α Fpoly = 0 := by
  rw [α, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

end Example
