/-
  NonAbelian.lean

  Formal verification (Lean 4 + Mathlib) of

    Proposition "No non-abelian gain"
    (Appendix "Non-abelian and reflection symmetries")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  The proposition has two parts.  Part (1): an algebra automorphism `U` of the
  quotient for which the monomial basis is a simultaneous eigenbasis is exactly a
  scalar substitution `σ_c`, and the admissible `c` form the stabilizer
  `Stab^×(S) = {c ∈ Kˣ : c·S = S}`, a cyclic group whose order is bounded by the
  crystallographic ceiling `6`.  Part (2): forcing a polynomial into a
  one-character isotypic component of a group `G` constrains it only through the
  abelianization of `G`; for the dihedral group `D₆ = ⟨M, κ⟩` with
  `κMκ⁻¹ = M⁻¹` this caps the rotation eigenvalue at order two, i.e. at density
  `1/2`, never the density `1/6` of the order-six character filter.
  With no unproved placeholders:

  * `sigmaAlg`, `sigmaAlg_apply`, `sigma_X_pow`
        the scalar substitution `σ_c` of `Commute.lean` as a `K`-algebra
        endomorphism of `K[X]`, with `σ_c(X^k) = c^k X^k`.
  * `monomial_eigenbasis_iff`
        (Proposition, part (1))  a `K`-algebra endomorphism of `K[X]` has the
        monomial basis as a simultaneous eigenbasis iff it is `σ_c` for some `c`.
  * `stabUnits`, `mem_stabUnits`, `finite_stabUnits`, `isCyclic_stabUnits`
        the stabilizer `Stab^×(S) ≤ Kˣ` as a subgroup; it is finite as soon as `S`
        contains a nonzero element, hence cyclic.
  * `dvd_G_sigma_of_mem_stab`, `span_G_sigma_le_of_mem_stab`
        a stabilizer element makes `σ_c` descend to `V = K[X]/(G_S)`.
  * `matAct`, `matAct_one`, `matAct_mul`, `phi_matAct_pow`, `pow_eq_one_of_matAct`,
    `orderOf_dvd_of_matAct`, `orderOf_scalar_mem`, `orderOf_scalar_le_six`
        the ceiling: a scalar whose action on the digit lattice is induced by an
        integer `2 × 2` matrix of finite order has `orderOf c ∈ {1, 2, 3, 4, 6}`,
        hence `orderOf c ≤ 6`.  This is the crystallographic restriction
        (`Crystallographic.orderOf_mem`) transported along `DigitLattice.phi`.
  * `linearChar_sq_eq_one`, `linearChar_orderOf_dvd_two`, `linearChar_ne_order_three_six`
        (Proposition, part (2))  a one-dimensional character of a group containing
        `M, κ` with `κMκ⁻¹ = M⁻¹` sends `M` to an element of order dividing two.
  * `commutatorElement_eq_sq`, `sq_mem_commutator`
        `M κ M⁻¹ κ⁻¹ = M²`, i.e. `⁅M, κ⁆ = M²`, so `M²` lies in the commutator
        subgroup and the character constraint factors through the abelianization.
  * `kappa`, `MAinv`, `rotU`, `kappaU`, `kappaU_conj_rotU`, `orderOf_rotU`
        the concrete witness for the hexagon: the reflection
        `κ(η, λ) = (−η, η + λ)` and the order-six rotation `M_A` generate a
        dihedral pair, so the hypotheses of part (2) are not vacuous.

  Not formalized: the statement that *every* automorphism of the quotient with a
  monomial-spanned eigenspace is scalar (the paper explicitly restricts part (1)
  to the monomial-diagonal family its mechanism uses), and the identification
  `D₆^ab ≅ C₂ × C₂` as an isomorphism of groups — only the consequence actually
  used, `χ(M)² = 1`, is proved here.
-/
import Mathlib
import SymmetryGraded.Commute
import SymmetryGraded.Crystallographic

namespace NonAbelian

open Polynomial

/-! ## 1. Monomial-diagonal automorphisms are exactly the scalar substitutions -/
section Diagonal
variable {K : Type*} [Field K]

/-- The scalar substitution `σ_A : p(X) ↦ p(A·X)` as a `K`-algebra endomorphism of
    `K[X]`; it fixes the constants by `GaloisCommute.sigma_C`. -/
noncomputable def sigmaAlg (A : K) : K[X] →ₐ[K] K[X] :=
  { GaloisCommute.sigma A with
    commutes' := fun c => GaloisCommute.sigma_C A c }

@[simp] theorem sigmaAlg_apply (A : K) (p : K[X]) :
    sigmaAlg A p = GaloisCommute.sigma A p := rfl

/-- The monomials are eigenvectors of `σ_A`: `σ_A(X^k) = A^k·X^k`. -/
theorem sigma_X_pow (A : K) (k : ℕ) :
    GaloisCommute.sigma A (X ^ k) = C (A ^ k) * X ^ k := by
  ext n
  rw [GaloisCommute.sigma_coeff, coeff_C_mul, coeff_X_pow]
  by_cases h : n = k
  · subst h; simp
  · simp [h]

/-- (Proposition "No non-abelian gain", part (1).)  A `K`-algebra endomorphism `U` of
    `K[X]` has the monomial basis as a simultaneous eigenbasis if and only if it is the
    scalar substitution `σ_c` for some `c ∈ K`.  A `K`-algebra map out of `K[X]` is
    determined by the image of `X`, and the eigenvector condition at `k = 1` fixes that
    image to be `c·X`. -/
theorem monomial_eigenbasis_iff (U : K[X] →ₐ[K] K[X]) :
    (∀ k : ℕ, ∃ μ : K, U (X ^ k) = C μ * X ^ k) ↔
      ∃ c : K, ∀ p, U p = GaloisCommute.sigma c p := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h 1
    rw [pow_one] at hc
    refine ⟨c, ?_⟩
    have hU : U = sigmaAlg c := by
      apply Polynomial.algHom_ext
      rw [hc, sigmaAlg_apply, GaloisCommute.sigma_X]
    intro p
    rw [hU, sigmaAlg_apply]
  · rintro ⟨c, hc⟩ k
    exact ⟨c ^ k, by rw [hc, sigma_X_pow]⟩

end Diagonal

/-! ## 2. The stabilizer `Stab^×(S)` is a finite, hence cyclic, subgroup of `Kˣ` -/
section Stabilizer
variable {K : Type*} [Field K] [DecidableEq K]

/-- The multiplicative stabilizer `Stab^×(S) = {c ∈ Kˣ : c·S = S}` of a finite
    support `S`. -/
def stabUnits (S : Finset K) : Subgroup Kˣ where
  carrier := {c : Kˣ | S.image (fun a => (c : K) * a) = S}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one, one_mul]
    exact Finset.image_id
  mul_mem' := by
    intro c d hc hd
    simp only [Set.mem_setOf_eq] at hc hd ⊢
    calc S.image (fun a => ((c * d : Kˣ) : K) * a)
        = S.image ((fun a => (c : K) * a) ∘ (fun a => (d : K) * a)) := by
          apply Finset.image_congr
          intro a _
          simp [mul_assoc]
      _ = (S.image (fun a => (d : K) * a)).image (fun a => (c : K) * a) := by
          rw [Finset.image_image]
      _ = S := by rw [hd, hc]
  inv_mem' := by
    intro c hc
    simp only [Set.mem_setOf_eq] at hc ⊢
    have key : (S.image (fun a => ((c : Kˣ) : K) * a)).image
        (fun a => ((c⁻¹ : Kˣ) : K) * a) = S := by
      rw [Finset.image_image]
      refine Eq.trans (Finset.image_congr ?_) Finset.image_id
      intro a _
      simp only [Function.comp_apply, id_eq, ← mul_assoc, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_mul]
    rw [hc] at key
    exact key

@[simp] theorem mem_stabUnits {S : Finset K} {c : Kˣ} :
    c ∈ stabUnits S ↔ S.image (fun a => (c : K) * a) = S := Iff.rfl

/-- A stabilizer element maps the support into itself. -/
theorem mul_mem_of_mem_stabUnits {S : Finset K} {c : Kˣ} (hc : c ∈ stabUnits S) {a : K}
    (ha : a ∈ S) : (c : K) * a ∈ S := by
  rw [mem_stabUnits] at hc
  rw [← hc]
  exact Finset.mem_image_of_mem _ ha

/-- The stabilizer is finite as soon as the support contains a nonzero point: the map
    `c ↦ c·s₀` injects it into `S`. -/
theorem finite_stabUnits {S : Finset K} {s₀ : K} (hs₀ : s₀ ∈ S) (hne : s₀ ≠ 0) :
    Finite (stabUnits S) := by
  have hmem : ∀ c : stabUnits S, ((c : Kˣ) : K) * s₀ ∈ S :=
    fun c => mul_mem_of_mem_stabUnits c.2 hs₀
  refine Finite.of_injective
    (fun c : stabUnits S => (⟨((c : Kˣ) : K) * s₀, hmem c⟩ : {x // x ∈ S})) ?_
  intro c d hcd
  rw [Subtype.mk.injEq] at hcd
  have hval : ((c : Kˣ) : K) = ((d : Kˣ) : K) := mul_right_cancel₀ hne hcd
  exact Subtype.ext (Units.ext hval)

/-- A finite subgroup of the units of a field is cyclic, so `Stab^×(S)` is cyclic. -/
theorem isCyclic_stabUnits {S : Finset K} {s₀ : K} (hs₀ : s₀ ∈ S) (hne : s₀ ≠ 0) :
    IsCyclic (stabUnits S) := by
  haveI := finite_stabUnits hs₀ hne
  infer_instance

/-- A stabilizer element makes `σ_c` preserve the ideal `(G_S)`, so `σ_c` descends to
    the quotient `V = K[X]/(G_S)`. -/
theorem dvd_G_sigma_of_mem_stab {S : Finset K} {c : Kˣ} (hc : c ∈ stabUnits S) {p : K[X]}
    (h : GaloisCommute.G S ∣ p) :
    GaloisCommute.G S ∣ GaloisCommute.sigma ((c : K)) p :=
  GaloisCommute.dvd_sigma_of_dvd c.isUnit hc h

/-- Ideal form of the descent: `σ_c((G_S)) ⊆ (G_S)` for `c ∈ Stab^×(S)`. -/
theorem span_G_sigma_le_of_mem_stab {S : Finset K} {c : Kˣ} (hc : c ∈ stabUnits S) :
    (Ideal.span {GaloisCommute.G S}).map (GaloisCommute.sigma ((c : K))) ≤
      Ideal.span {GaloisCommute.G S} :=
  GaloisCommute.span_G_map_sigma_le c.isUnit hc

end Stabilizer

/-! ## 3. The ceiling: a scalar induced by an integer matrix has order at most six -/
section Ceiling

/-- The action of an integer `2 × 2` matrix on a digit pair, written on the pair
    directly rather than on column vectors. -/
def matAct (M : Crystallographic.M2) (v : ℤ × ℤ) : ℤ × ℤ :=
  (M 0 0 * v.1 + M 0 1 * v.2, M 1 0 * v.1 + M 1 1 * v.2)

@[simp] theorem matAct_one (v : ℤ × ℤ) : matAct 1 v = v := by
  simp [matAct]

theorem matAct_mul (M N : Crystallographic.M2) (v : ℤ × ℤ) :
    matAct (M * N) v = matAct M (matAct N v) := by
  simp only [matAct, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq]
  constructor <;> ring

variable {K : Type*} [CommRing K]

/-- If `M` induces multiplication by `c` on the encoded digit lattice, then `M^n`
    induces multiplication by `c^n`. -/
theorem phi_matAct_pow {A c : K} {M : Crystallographic.M2}
    (hcov : ∀ v : ℤ × ℤ, DigitLattice.phi A (matAct M v) = c * DigitLattice.phi A v)
    (n : ℕ) (v : ℤ × ℤ) :
    DigitLattice.phi A (matAct (M ^ n) v) = c ^ n * DigitLattice.phi A v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, matAct_mul, ih (matAct M v), hcov v, pow_succ]
      ring

/-- A matrix relation `M^n = 1` forces `c^n = 1`: evaluate the induced action on the
    digit pair `(0, 1)`, whose encoding is `1`. -/
theorem pow_eq_one_of_matAct {A c : K} {M : Crystallographic.M2} {n : ℕ}
    (hcov : ∀ v : ℤ × ℤ, DigitLattice.phi A (matAct M v) = c * DigitLattice.phi A v)
    (hM : M ^ n = 1) : c ^ n = 1 := by
  have h := phi_matAct_pow hcov n ((0 : ℤ), (1 : ℤ))
  rw [hM, matAct_one] at h
  have hphi : DigitLattice.phi A ((0 : ℤ), (1 : ℤ)) = 1 := by
    simp [DigitLattice.phi]
  rw [hphi, mul_one] at h
  exact h.symm

/-- The order of the scalar divides the order of the inducing matrix. -/
theorem orderOf_dvd_of_matAct {A c : K} {M : Crystallographic.M2}
    (hcov : ∀ v : ℤ × ℤ, DigitLattice.phi A (matAct M v) = c * DigitLattice.phi A v) :
    orderOf c ∣ orderOf M :=
  orderOf_dvd_of_pow_eq_one (pow_eq_one_of_matAct hcov (pow_orderOf_eq_one M))

/-- Every divisor of an element of `{1, 2, 3, 4, 6}` lies in `{1, 2, 3, 4, 6}`. -/
theorem dvd_mem_of_mem {a m : ℕ} (h : a ∣ m) (hm : m ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    a ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
  have hm0 : 0 < m := by omega
  have hle : a ≤ 6 := le_trans (Nat.le_of_dvd hm0 h) (by omega)
  interval_cases a <;> omega

/-- (Proposition "No non-abelian gain", the ceiling of part (1).)  A scalar `c` whose
    multiplication action on the encoded digit lattice is induced by an integer `2 × 2`
    matrix of finite order has `orderOf c ∈ {1, 2, 3, 4, 6}`.  This is the
    crystallographic restriction `Crystallographic.orderOf_mem` transported along the
    encoding `φ_A`. -/
theorem orderOf_scalar_mem {A c : K} {M : Crystallographic.M2} {n : ℕ} (hn : 1 ≤ n)
    (hM : M ^ n = 1)
    (hcov : ∀ v : ℤ × ℤ, DigitLattice.phi A (matAct M v) = c * DigitLattice.phi A v) :
    orderOf c ∈ ({1, 2, 3, 4, 6} : Finset ℕ) :=
  dvd_mem_of_mem (orderOf_dvd_of_matAct hcov) (Crystallographic.orderOf_mem M hn hM)

/-- The order ceiling in the form used by the paper: `orderOf c ≤ 6`. -/
theorem orderOf_scalar_le_six {A c : K} {M : Crystallographic.M2} {n : ℕ} (hn : 1 ≤ n)
    (hM : M ^ n = 1)
    (hcov : ∀ v : ℤ × ℤ, DigitLattice.phi A (matAct M v) = c * DigitLattice.phi A v) :
    orderOf c ≤ 6 := by
  have := orderOf_scalar_mem hn hM hcov
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

end Ceiling

/-! ## 4. Part (2): a one-dimensional character sees only the abelianization -/
section Abelianization
variable {G : Type*} [Group G] {H : Type*} [CommGroup H]

/-- (Proposition "No non-abelian gain", part (2).)  If `κMκ⁻¹ = M⁻¹` — the dihedral
    relation — then every one-dimensional character `χ` of the ambient group satisfies
    `χ(M)² = 1`: the target is commutative, so conjugation acts trivially and
    `χ(M) = χ(M)⁻¹`. -/
theorem linearChar_sq_eq_one {M κ : G} (h : κ * M * κ⁻¹ = M⁻¹) (χ : G →* H) :
    χ M ^ 2 = 1 := by
  have hχ := congrArg χ h
  simp only [map_mul, map_inv] at hχ
  have hself : χ κ * χ M * (χ κ)⁻¹ = χ M := by
    rw [mul_comm (χ κ) (χ M), mul_assoc, mul_inv_cancel, mul_one]
  rw [hself] at hχ
  rw [sq]
  exact mul_eq_one_iff_eq_inv.mpr hχ

/-- The order of the rotation eigenvalue under a one-dimensional character divides two:
    the character can never see a primitive sixth root of unity. -/
theorem linearChar_orderOf_dvd_two {M κ : G} (h : κ * M * κ⁻¹ = M⁻¹) (χ : G →* H) :
    orderOf (χ M) ∣ 2 :=
  orderOf_dvd_of_pow_eq_one (linearChar_sq_eq_one h χ)

/-- Consequently the eigenvalue attached to the rotation by a one-dimensional character
    has order neither three nor six: the isotypic constraint coming from a single
    character of the dihedral group reaches density `1/2` at best, never `1/3` or `1/6`. -/
theorem linearChar_ne_order_three_six {M κ : G} (h : κ * M * κ⁻¹ = M⁻¹) (χ : G →* H) :
    orderOf (χ M) ≠ 3 ∧ orderOf (χ M) ≠ 6 := by
  have hd := linearChar_orderOf_dvd_two h χ
  constructor <;> intro hcon <;> rw [hcon] at hd <;> omega

/-- The dihedral relation exhibits `M²` as the commutator `M κ M⁻¹ κ⁻¹`. -/
theorem commutatorElement_eq_sq {M κ : G} (h : κ * M * κ⁻¹ = M⁻¹) :
    M * κ * M⁻¹ * κ⁻¹ = M ^ 2 := by
  have hinv : κ * M⁻¹ * κ⁻¹ = M := by
    have h' := congrArg (fun g : G => g⁻¹) h
    simpa [mul_assoc] using h'
  rw [sq]
  calc M * κ * M⁻¹ * κ⁻¹ = M * (κ * M⁻¹ * κ⁻¹) := by group
    _ = M * M := by rw [hinv]

open scoped commutatorElement in
/-- Hence `M²` lies in the commutator subgroup: the one-character constraint factors
    through the abelianization, which is what caps the rotation eigenvalue at order two. -/
theorem sq_mem_commutator {M κ : G} (h : κ * M * κ⁻¹ = M⁻¹) : M ^ 2 ∈ commutator G := by
  have hbr : ⁅M, κ⁆ = M ^ 2 := commutatorElement_eq_sq h
  rw [← hbr]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top M) (Subgroup.mem_top κ)

end Abelianization

/-! ## 5. The dihedral pair of the hexagon -/
section Witness

open DigitLattice

/-- The Eisenstein reflection `κ(η, λ) = (−η, η + λ)` as an integer matrix acting on
    column vectors. -/
def kappa : Crystallographic.M2 := !![-1, 0; 1, 1]

/-- The inverse of the order-six rotation `M_A = [[1, 1], [−1, 0]]`. -/
def MAinv : Crystallographic.M2 := !![0, -1; 1, 1]

theorem kappa_mulVec (η l : ℤ) : kappa.mulVec ![η, l] = ![-η, η + l] := by
  ext i; fin_cases i <;> simp [kappa, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem kappa_det : kappa.det = -1 := by simp [kappa, Matrix.det_fin_two]

theorem kappa_mul_self : kappa * kappa = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kappa, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem MA_mul_MAinv : MA 1 * MAinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [MA, MAinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem MAinv_mul_MA : MAinv * MA 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [MA, MAinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem kappa_conj_MA : kappa * MA 1 * kappa = MAinv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kappa, MA, MAinv, Matrix.mul_apply, Fin.sum_univ_two]

/-- The order-six rotation as a unit of the matrix monoid. -/
def rotU : (Crystallographic.M2)ˣ := ⟨MA 1, MAinv, MA_mul_MAinv, MAinv_mul_MA⟩

/-- The reflection as a unit of the matrix monoid; it is its own inverse. -/
def kappaU : (Crystallographic.M2)ˣ := ⟨kappa, kappa, kappa_mul_self, kappa_mul_self⟩

/-- The dihedral relation `κMκ⁻¹ = M⁻¹` for the hexagon, so the hypotheses of part (2)
    are satisfied by a genuine pair of lattice symmetries. -/
theorem kappaU_conj_rotU : kappaU * rotU * kappaU⁻¹ = rotU⁻¹ := by
  apply Units.ext
  show kappa * MA 1 * kappa = MAinv
  exact kappa_conj_MA

/-- The rotation has order six as a unit, so `χ(M)² = 1` genuinely loses information:
    a one-dimensional character cannot distinguish the six rotations. -/
theorem orderOf_rotU : orderOf rotU = 6 := by
  have : orderOf ((rotU : (Crystallographic.M2)ˣ) : Crystallographic.M2) = orderOf rotU :=
    orderOf_units
  rw [← this]
  exact Crystallographic.MA_orderOf_six

end Witness

end NonAbelian
