/-
  Monodromy.lean

  Formal verification (Lean 4 + Mathlib) of the deterministic algebraic part of

    Theorem "Full monodromy of the folded pencil"  and
    Corollary "Chebotarev density of norm forms"   (Appendix "Selection of the pencil")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  For `Γ` monic of degree `n'`, `deg Q < n'` and `δ = n' − deg Q`, the pencil is
  `Γ + cQ` and the hypotheses of the theorem are (H1) `gcd(Q, Γ) = 1`, (H2) `Q` squarefree,
  (H3) `δ ≤ 2`, (H4) `Δ(u) = disc_Y(Γ + uQ)` squarefree of degree `2n' − 2 − (δ − 1)`.
  With no unproved placeholders:

  * `pencil`, `pencil_monic`, `pencil_natDegree`, `pencil_ne_zero`, `pencil_sub_pencil`
        every member `Γ + cQ` of the pencil is monic of degree `n'`, and two members
        differ by `(c₁ − c₂)·Q`.
  * `isUnit_of_dvd_pencil_of_dvd_Q`, `isUnit_of_dvd_pencil`, `isCoprime_pencil`
        (H1) ⟹ the pencil has no fixed divisor: a common divisor of two distinct members
        divides `Q` and `Γ`, hence is a unit; over the principal ideal domain `F[Y]` this
        upgrades to coprimality of distinct members.
  * `bipencil`, `bipencil_coeff_zero`, `bipencil_coeff_one`, `bipencil_natDegree`,
    `bipencil_isPrimitive`, `bipencil_irreducible`
        (H1) ⟹ `Γ(Y) + u·Q(Y)`, viewed in `F[Y][u]`, is primitive of degree one in `u`,
        hence irreducible.
  * `swap_bipencil`, `swap_bipencil_monic`, `generic_irreducible`
        the same polynomial read in `Y` over `F[u]` is monic of degree `n'`, hence primitive,
        so Gauss's lemma transports irreducibility: the generic member `Γ + uQ` is
        irreducible over the rational function field `F(u)`.  (This is the transitivity
        bullet of the monodromy proof.)
  * `Hyp`
        the hypotheses (H1)–(H4) bundled; the discriminant `Δ` is a field of the structure,
        since the paper verifies (H4) numerically for each instance, and `Mathlib`'s
        `Polynomial.discr` carries no usable API.
  * `Hyp.pencil_monic`, `Hyp.pencil_natDegree`, `Hyp.isCoprime_pencil`, `Hyp.mem_branch`,
    `branch_card_le`, `squarefree_pencil_of_notMem`
        the branch locus is contained in the root set of `Δ`, has at most `2n' − 2` points,
        and off it every member of the pencil is squarefree (separable fibre).
  * `fullCycleType`, `sum_fullCycleType`, `cycleDivisible`, `Pi`, `Pi_pos`, `Pi_le_one`
        the density constant `Π_d(n')`: the proportion of permutations of `n'` letters all of
        whose cycle lengths are divisible by `d`, with `0 < Π_d(n') ≤ 1` for `d ∣ n'`,
        `n' > 0` (an `n'`-cycle witnesses positivity).  `Mathlib`'s `Equiv.Perm.cycleType`
        omits fixed points, so `fullCycleType` adds them back as parts equal to `1`; this is
        the partition of `n'` meant in the corollary.
  * `IsNormForm`, `normFormFinset`, `mem_normFormFinset`, `isNormForm_iff_of_factors`
        being a norm form `Orb_d(C)` over `F_{p^d}`, and the bridge to the already formalised
        Lemma "Norm criterion": for a member given in factored form as a product of pairwise
        distinct monic irreducibles, `Γ + cQ` is a norm form iff `d` divides every factor
        degree (`NormCriterion.normForm_iff_galoisField` at multiplicity one).
  * `ChebotarevBound`, `exists_normForm_of_density`
        the density statement `#{c ∈ F_p : Γ + cQ a norm form} ≥ Π_d(n')·p − err·√p` as an
        explicit hypothesis carrying its own implied constant, and its only use: a norm form
        exists in the pencil as soon as `err·√p < Π_d(n')·p`.

  Assumed, never proved here: (H1)–(H4) (fields of `Hyp`, in particular the numerically
  verified discriminant data) and the density bound (a field of `ChebotarevBound`).

  Not formalized: the monodromy computation itself — the Riemann–Hurwitz count of the
  branch locus, the tame fundamental group of `P¹ ∖ branch`, and the resulting identification
  of the geometric and arithmetic monodromy groups of `ψ = −Γ/Q` with `S_{n'}` — and the
  Chebotarev density theorem for function fields, which is not in Mathlib.  Both enter only
  through the hypotheses listed above.
-/
import Mathlib
import SymmetryGraded.Doubling
import SymmetryGraded.NormCriterion

namespace Monodromy

open Polynomial
open scoped Polynomial.Bivariate

section Pencil
variable {F : Type*} [Field F]

/-- The member `Γ + c·Q` of the pencil spanned by `Γ` and `Q`. -/
noncomputable def pencil (Γ Q : F[X]) (c : F) : F[X] := Γ + C c * Q

/-- The degree of the tail `c·Q` of a pencil member is smaller than the degree of `Γ`. -/
theorem degree_C_mul_lt {Γ Q : F[X]} (hdeg : Q.natDegree < Γ.natDegree) (c : F) :
    (C c * Q).degree < Γ.degree := by
  refine lt_of_le_of_lt ?_ (degree_lt_degree hdeg)
  rw [← smul_eq_C_mul]
  exact degree_smul_le c Q

/-- Every member of the pencil is monic when `Γ` is monic and `deg Q < deg Γ`. -/
theorem pencil_monic {Γ Q : F[X]} (hΓ : Γ.Monic) (hdeg : Q.natDegree < Γ.natDegree) (c : F) :
    (pencil Γ Q c).Monic :=
  hΓ.add_of_left (degree_C_mul_lt hdeg c)

/-- Every member of the pencil has the same degree `n'` as `Γ`. -/
theorem pencil_natDegree {Γ Q : F[X]} (hdeg : Q.natDegree < Γ.natDegree) (c : F) :
    (pencil Γ Q c).natDegree = Γ.natDegree :=
  natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (degree_C_mul_lt hdeg c))

/-- Every member of the pencil is nonzero. -/
theorem pencil_ne_zero {Γ Q : F[X]} (hΓ : Γ.Monic) (hdeg : Q.natDegree < Γ.natDegree) (c : F) :
    pencil Γ Q c ≠ 0 :=
  (pencil_monic hΓ hdeg c).ne_zero

/-- The difference of two members of the pencil is `(c₁ − c₂)·Q`. -/
theorem pencil_sub_pencil (Γ Q : F[X]) (c₁ c₂ : F) :
    pencil Γ Q c₁ - pencil Γ Q c₂ = C (c₁ - c₂) * Q := by
  simp only [pencil, C_sub]
  ring

end Pencil

/-! ## 2. No fixed divisor -/
section NoFixedDivisor
variable {F : Type*} [Field F]

/-- **(H1) ⟹ no fixed divisor, one member.**  A common divisor of a pencil member and of `Q`
    is a unit. -/
theorem isUnit_of_dvd_pencil_of_dvd_Q {Γ Q : F[X]} (h1 : IsCoprime Q Γ) {c : F} {g : F[X]}
    (hgp : g ∣ pencil Γ Q c) (hgQ : g ∣ Q) : IsUnit g := by
  refine h1.isUnit_of_dvd' hgQ ?_
  have : Γ = pencil Γ Q c - C c * Q := by simp [pencil]
  rw [this]
  exact dvd_sub hgp (hgQ.mul_left _)

/-- **(H1) ⟹ no fixed divisor.**  Two distinct members of the pencil have no common
    nonunit divisor: such a divisor would divide `(c₁ − c₂)·Q`, hence `Q`, hence also `Γ`. -/
theorem isUnit_of_dvd_pencil {Γ Q : F[X]} (h1 : IsCoprime Q Γ) {c₁ c₂ : F} (hne : c₁ ≠ c₂)
    {g : F[X]} (hg₁ : g ∣ pencil Γ Q c₁) (hg₂ : g ∣ pencil Γ Q c₂) : IsUnit g := by
  have hsub : g ∣ C (c₁ - c₂) * Q := by
    rw [← pencil_sub_pencil]
    exact dvd_sub hg₁ hg₂
  have hu : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  have hgQ : g ∣ Q := by
    have h := hsub.mul_left (C (c₁ - c₂)⁻¹)
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hu, C_1, one_mul] at h
  exact isUnit_of_dvd_pencil_of_dvd_Q h1 hg₁ hgQ

/-- **(H1) ⟹ distinct members of the pencil are coprime.**  `F[X]` is a principal ideal
    domain, so "every common divisor is a unit" upgrades to a Bézout identity. -/
theorem isCoprime_pencil {Γ Q : F[X]} (h1 : IsCoprime Q Γ) {c₁ c₂ : F} (hne : c₁ ≠ c₂) :
    IsCoprime (pencil Γ Q c₁) (pencil Γ Q c₂) :=
  IsRelPrime.isCoprime (fun _ hg₁ hg₂ => isUnit_of_dvd_pencil h1 hne hg₁ hg₂)

end NoFixedDivisor

/-! ## 3. Irreducibility of the generic member -/
section Generic
variable {F : Type*} [Field F]

/-- The pencil as a bivariate polynomial `Γ(Y) + u·Q(Y)`, the outer variable `Y` playing the
    role of the pencil parameter `u`. -/
noncomputable def bipencil (Γ Q : F[X]) : F[X][Y] := C Γ + Y * C Q

/-- The constant coefficient of the bivariate pencil is `Γ`. -/
@[simp] theorem bipencil_coeff_zero (Γ Q : F[X]) : (bipencil Γ Q).coeff 0 = Γ := by
  simp [bipencil]

/-- The linear coefficient of the bivariate pencil is `Q`. -/
@[simp] theorem bipencil_coeff_one (Γ Q : F[X]) : (bipencil Γ Q).coeff 1 = Q := by
  simp [bipencil]

/-- The bivariate pencil has degree one in the parameter, provided `Q ≠ 0`. -/
theorem bipencil_natDegree {Γ Q : F[X]} (hQ : Q ≠ 0) : (bipencil Γ Q).natDegree = 1 := by
  have h : bipencil Γ Q = C Q * X + C Γ := by rw [bipencil]; ring
  rw [h, natDegree_linear hQ]

/-- **(H1) ⟹ the bivariate pencil is primitive.**  A content of `Γ + u·Q` divides both `Γ`
    and `Q`, hence is a unit. -/
theorem bipencil_isPrimitive {Γ Q : F[X]} (h1 : IsCoprime Q Γ) : (bipencil Γ Q).IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have hQ := hr 1
  have hΓ := hr 0
  rw [bipencil_coeff_one] at hQ
  rw [bipencil_coeff_zero] at hΓ
  exact h1.isUnit_of_dvd' hQ hΓ

/-- **(H1) ⟹ `Γ + u·Q` is irreducible in `F[Y][u]`.**  A primitive polynomial of degree one
    over a commutative domain is irreducible. -/
theorem bipencil_irreducible {Γ Q : F[X]} (h1 : IsCoprime Q Γ) (hQ : Q ≠ 0) :
    Irreducible (bipencil Γ Q) := by
  have hprim := bipencil_isPrimitive h1
  have hdeg := bipencil_natDegree (Γ := Γ) hQ
  have hne : bipencil Γ Q ≠ 0 := fun h => by simp [h] at hdeg
  refine ⟨fun hu => by simp [natDegree_eq_zero_of_isUnit hu] at hdeg, ?_⟩
  intro a b hab
  have ha0 : a ≠ 0 := by rintro rfl; exact hne (by simp [hab])
  have hb0 : b ≠ 0 := by rintro rfl; exact hne (by simp [hab])
  have hsum : a.natDegree + b.natDegree = 1 := by
    rw [← natDegree_mul ha0 hb0, ← hab, hdeg]
  have key : ∀ g : F[X][Y], g ∣ bipencil Γ Q → g.natDegree = 0 → IsUnit g := by
    intro g hg hg0
    obtain ⟨r, hr⟩ := natDegree_eq_zero.mp hg0
    rw [← hr] at hg ⊢
    exact isUnit_C.mpr (hprim r hg)
  rcases Nat.eq_zero_or_pos a.natDegree with h | h
  · exact Or.inl (key a ⟨b, hab⟩ h)
  · exact Or.inr (key b ⟨a, by rw [hab]; ring⟩ (by omega))

/-- The bivariate pencil read in the paper's variable `Y`, with coefficients in `F[u]`. -/
theorem swap_bipencil (Γ Q : F[X]) :
    Bivariate.swap (bipencil Γ Q) = Γ.map C + C X * Q.map C := by
  rw [bipencil, map_add, map_mul, Bivariate.swap_C, Bivariate.swap_C, Bivariate.swap_Y]

/-- Read in the variable `Y`, the pencil is monic of degree `n'` over `F[u]`. -/
theorem swap_bipencil_monic {Γ Q : F[X]} (hΓ : Γ.Monic) (hdeg : Q.natDegree < Γ.natDegree) :
    (Bivariate.swap (bipencil Γ Q)).Monic := by
  rw [swap_bipencil]
  have hle : (C X * Q.map (C : F →+* F[X])).degree ≤ (Q.map (C : F →+* F[X])).degree := by
    rw [← smul_eq_C_mul]
    exact degree_smul_le _ _
  have hlt : (Q.map (C : F →+* F[X])).degree < (Γ.map (C : F →+* F[X])).degree := by
    rw [degree_map_eq_of_injective C_injective, degree_map_eq_of_injective C_injective]
    exact degree_lt_degree hdeg
  exact (hΓ.map (C : F →+* F[X])).add_of_left (lt_of_le_of_lt hle hlt)

/-- **(H1) ⟹ the generic member is irreducible.**  `Γ + uQ` is irreducible over the rational
    function field `F(u)`: it is primitive (being monic in `Y`) and irreducible over `F[u]`,
    so Gauss's lemma applies. -/
theorem generic_irreducible {Γ Q : F[X]} (h1 : IsCoprime Q Γ) (hQ : Q ≠ 0) (hΓ : Γ.Monic)
    (hdeg : Q.natDegree < Γ.natDegree) :
    Irreducible ((Bivariate.swap (bipencil Γ Q)).map
        (algebraMap (F[X]) (FractionRing (F[X])))) := by
  have hprim : (Bivariate.swap (bipencil Γ Q)).IsPrimitive :=
    (swap_bipencil_monic hΓ hdeg).isPrimitive
  rw [← hprim.irreducible_iff_irreducible_map_fraction_map]
  exact (MulEquiv.irreducible_iff
    (Bivariate.swap : F[X][Y] ≃ₐ[F] F[X][Y]).toRingEquiv.toMulEquiv).mpr
      (bipencil_irreducible h1 hQ)

end Generic

/-! ## 4. The hypotheses (H1)–(H4) and the branch locus -/
section Hypotheses
variable {F : Type*} [Field F]

/-- The standing hypotheses of the theorem "Full monodromy of the folded pencil":
    `Γ` monic of degree `n'`, `deg Q < n'`, (H1) `gcd(Q, Γ) = 1`, (H2) `Q` squarefree,
    (H3) `δ = n' − deg Q ≤ 2`, and (H4) the discriminant `Δ(u) = disc_Y(Γ + uQ)` — supplied
    as data, since the paper verifies it numerically per instance — is squarefree of degree
    `2n' − 2 − (δ − 1)` and its roots are exactly the parameters with a non-squarefree fibre. -/
structure Hyp (Γ Q : F[X]) where
  /-- `Γ` is monic. -/
  monic : Γ.Monic
  /-- `deg Q < deg Γ = n'`. -/
  degQ : Q.natDegree < Γ.natDegree
  /-- (H1) `Q` and `Γ` are coprime. -/
  h1 : IsCoprime Q Γ
  /-- (H2) `Q` is squarefree. -/
  h2 : Squarefree Q
  /-- (H3) `δ = n' − deg Q ≤ 2`. -/
  h3 : Γ.natDegree - Q.natDegree ≤ 2
  /-- The discriminant `Δ(u) = disc_Y(Γ + uQ)`, supplied as data. -/
  Δ : F[X]
  /-- (H4) `Δ` is nonzero. -/
  h4_ne : Δ ≠ 0
  /-- (H4) `Δ` has degree `2n' − 2 − (δ − 1)`. -/
  h4_deg : Δ.natDegree = 2 * Γ.natDegree - 2 - (Γ.natDegree - Q.natDegree - 1)
  /-- (H4) `Δ` is squarefree. -/
  h4_sqf : Squarefree Δ
  /-- (H4) `Δ` cuts out the branch locus: the fibre over `c` is non-squarefree iff `Δ(c) = 0`. -/
  h4_branch : ∀ c : F, ¬ Squarefree (pencil Γ Q c) ↔ Δ.IsRoot c

variable {Γ Q : F[X]}

/-- Under the standing hypotheses every member of the pencil is monic. -/
theorem Hyp.pencil_monic (H : Hyp Γ Q) (c : F) : (pencil Γ Q c).Monic :=
  _root_.Monodromy.pencil_monic H.monic H.degQ c

/-- Under the standing hypotheses every member of the pencil has degree `n'`. -/
theorem Hyp.pencil_natDegree (H : Hyp Γ Q) (c : F) : (pencil Γ Q c).natDegree = Γ.natDegree :=
  _root_.Monodromy.pencil_natDegree H.degQ c

/-- Under the standing hypotheses distinct members of the pencil are coprime. -/
theorem Hyp.isCoprime_pencil (H : Hyp Γ Q) {c₁ c₂ : F} (hne : c₁ ≠ c₂) :
    IsCoprime (pencil Γ Q c₁) (pencil Γ Q c₂) :=
  _root_.Monodromy.isCoprime_pencil H.h1 hne

/-- The branch locus is contained in the root set of `Δ`. -/
theorem Hyp.mem_branch [DecidableEq F] (H : Hyp Γ Q) {c : F} (hc : ¬ Squarefree (pencil Γ Q c)) :
    c ∈ H.Δ.roots.toFinset :=
  Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨H.h4_ne, (H.h4_branch c).mp hc⟩)

/-- **The branch locus has at most `2n' − 2` points.**  It is cut out by `Δ`, whose degree is
    at most `2n' − 2`. -/
theorem branch_card_le [DecidableEq F] (H : Hyp Γ Q) :
    H.Δ.roots.toFinset.card ≤ 2 * Γ.natDegree - 2 := by
  calc H.Δ.roots.toFinset.card ≤ Multiset.card H.Δ.roots := Multiset.toFinset_card_le _
    _ ≤ H.Δ.natDegree := card_roots' _
    _ = 2 * Γ.natDegree - 2 - (Γ.natDegree - Q.natDegree - 1) := H.h4_deg
    _ ≤ 2 * Γ.natDegree - 2 := Nat.sub_le _ _

/-- **Off the branch locus the fibre is squarefree.**  Every parameter which is not a root of
    `Δ` gives a squarefree member `Γ + cQ`, i.e. a separable fibre. -/
theorem squarefree_pencil_of_notMem [DecidableEq F] (H : Hyp Γ Q) {c : F}
    (hc : c ∉ H.Δ.roots.toFinset) : Squarefree (pencil Γ Q c) := by
  by_contra hcon
  exact hc (H.mem_branch hcon)

end Hypotheses

/-! ## 5. The cycle-type density constant -/
section Density

open Equiv Equiv.Perm

/-- The full cycle type of a permutation of `Fin n`, i.e. the partition of `n` given by the
    lengths of all its cycles.  Mathlib's `Equiv.Perm.cycleType` records only the cycles of
    length at least two, so the fixed points are added back here as parts equal to `1`. -/
def fullCycleType {n : ℕ} (σ : Equiv.Perm (Fin n)) : Multiset ℕ :=
  σ.cycleType + Multiset.replicate (n - σ.support.card) 1

/-- The full cycle type is a partition of `n`. -/
theorem sum_fullCycleType {n : ℕ} (σ : Equiv.Perm (Fin n)) : (fullCycleType σ).sum = n := by
  have hle : σ.support.card ≤ n := by
    simpa using σ.support.card_le_univ
  rw [fullCycleType, Multiset.sum_add, sum_cycleType, Multiset.sum_replicate, smul_eq_mul,
    mul_one]
  omega

/-- The permutations of `n` letters all of whose cycle lengths are divisible by `d`. -/
def cycleDivisible (d n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => ∀ k ∈ fullCycleType σ, d ∣ k)

/-- The proportion `Π_d(n)` of permutations of `n` letters all of whose cycle lengths are
    divisible by `d`. -/
def Pi (d n : ℕ) : ℚ := (cycleDivisible d n).card / (Nat.factorial n)

/-- **`Π_d(n') > 0` for `d ∣ n'`.**  An `n'`-cycle has a single cycle, of length `n'`. -/
theorem Pi_pos {d n : ℕ} (hd : d ∣ n) (hn : 0 < n) : 0 < Pi d n := by
  have hcard : 0 < (cycleDivisible d n).card := by
    rw [Finset.card_pos]
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn1 : n = 1 := by omega
      subst hn1
      refine ⟨1, ?_⟩
      simp only [cycleDivisible, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k _
      rw [Nat.dvd_one.mp hd]
      exact one_dvd k
    · refine ⟨finRotate n, ?_⟩
      simp only [cycleDivisible, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k hk
      rw [fullCycleType, cycleType_finRotate_of_le h, support_finRotate_of_le h,
        Finset.card_univ, Fintype.card_fin, Nat.sub_self, Multiset.replicate_zero,
        add_zero, Multiset.mem_singleton] at hk
      rw [hk]
      exact hd
  have hfac : (0 : ℚ) < (Nat.factorial n : ℚ) := by
    exact_mod_cast Nat.factorial_pos n
  exact div_pos (by exact_mod_cast hcard) hfac

/-- `Π_d(n) ≤ 1`: it is a proportion. -/
theorem Pi_le_one (d n : ℕ) : Pi d n ≤ 1 := by
  have hcard : (cycleDivisible d n).card ≤ Nat.factorial n := by
    have h1 : (cycleDivisible d n).card ≤ Fintype.card (Equiv.Perm (Fin n)) :=
      Finset.card_le_univ _
    rwa [Fintype.card_perm, Fintype.card_fin] at h1
  have hfac : (0 : ℚ) < (Nat.factorial n : ℚ) := by
    exact_mod_cast Nat.factorial_pos n
  rw [Pi, div_le_one hfac]
  exact_mod_cast hcard

end Density

/-! ## 6. The Chebotarev input, as an explicit hypothesis -/
section Chebotarev

/-- `G ∈ F_p[Y]` is a norm form over `F_{p^d}`: it is the Frobenius orbit product
    `Orb_d(C) = ∏_{i<d} σⁱ(C)` of a nonzero `C ∈ F_{p^d}[Y]`.  This is literally the
    left-hand side of `NormCriterion.normForm_iff_galoisField`. -/
def IsNormForm (p d : ℕ) [Fact p.Prime] (G : (ZMod p)[X]) : Prop :=
  ∃ Cp : (GaloisField p d)[X], Cp ≠ 0 ∧
    G.map (algebraMap (ZMod p) (GaloisField p d)) =
      Galois.orbProd (NormCriterion.act
        (NormCriterion.frob : GaloisField p d ≃ₐ[ZMod p] GaloisField p d)) d Cp

/-- The set of parameters `c ∈ F_p` for which the pencil member `Γ + cQ` is a norm form
    over `F_{p^d}`. -/
noncomputable def normFormFinset (p d : ℕ) [Fact p.Prime] (Γ Q : (ZMod p)[X]) :
    Finset (ZMod p) :=
  letI : DecidablePred (fun c : ZMod p => IsNormForm p d (pencil Γ Q c)) := Classical.decPred _
  Finset.univ.filter (fun c : ZMod p => IsNormForm p d (pencil Γ Q c))

/-- Membership in `normFormFinset` is being a norm form. -/
theorem mem_normFormFinset {p d : ℕ} [Fact p.Prime] {Γ Q : (ZMod p)[X]} {c : ZMod p} :
    c ∈ normFormFinset p d Γ Q ↔ IsNormForm p d (pencil Γ Q c) := by
  letI : DecidablePred (fun c : ZMod p => IsNormForm p d (pencil Γ Q c)) := Classical.decPred _
  rw [normFormFinset, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **The Chebotarev density input, isolated as an explicit hypothesis.**  The corollary
    "Chebotarev density of norm forms" asserts that, once the monodromy groups of the folded
    pencil are both `S_{n'}`, the number of parameters `c ∈ F_p` with `Γ + cQ` a norm form is
    `Π_d(n')·p + O_{n'}(√p)`.  Neither the monodromy computation nor the Chebotarev density
    theorem is available in Mathlib, so the lower bound is taken here as data: a constant
    `err ≥ 0` together with the inequality it certifies. -/
structure ChebotarevBound (p d n' : ℕ) [Fact p.Prime] (Γ Q : (ZMod p)[X]) where
  /-- The implied constant of the error term `O_{n'}(√p)`. -/
  err : ℝ
  /-- The implied constant is nonnegative. -/
  err_nonneg : 0 ≤ err
  /-- The density lower bound `#{c : Γ + cQ a norm form} ≥ Π_d(n')·p − err·√p`. -/
  count_ge : ((normFormFinset p d Γ Q).card : ℝ) ≥ (Pi d n' : ℝ) * (p : ℝ)
    - err * Real.sqrt (p : ℝ)

/-- Under the density bound of `ChebotarevBound`, a norm form exists in the pencil as soon as
    the field is large enough.  This is the only place where the Chebotarev density theorem is
    used, and it enters as an explicit hypothesis, never as an unproved constant. -/
theorem exists_normForm_of_density {p d n' : ℕ} [Fact p.Prime] {Γ Q : (ZMod p)[X]}
    (hb : ChebotarevBound p d n' Γ Q)
    (hlarge : hb.err * Real.sqrt (p : ℝ) < (Pi d n' : ℝ) * (p : ℝ)) :
    ∃ c : ZMod p, IsNormForm p d (pencil Γ Q c) := by
  have hcount : (0 : ℝ) < ((normFormFinset p d Γ Q).card : ℝ) := by
    have h := hb.count_ge
    linarith
  have hpos : 0 < (normFormFinset p d Γ Q).card := by exact_mod_cast hcount
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  exact ⟨c, mem_normFormFinset.mp hc⟩

/-- **Bridge to the norm criterion.**  For a member of the pencil given in factored form as a
    product of pairwise distinct monic irreducibles, being a norm form over `F_{p^d}` is
    equivalent to `d` dividing every factor degree. -/
theorem isNormForm_iff_of_factors {p d : ℕ} [Fact p.Prime] (hd : d ≠ 0) {ι : Type*}
    (s : Finset ι) (h : ι → (ZMod p)[X]) (hirr : ∀ i ∈ s, Irreducible (h i))
    (hmon : ∀ i ∈ s, (h i).Monic) (hdist : ∀ i ∈ s, ∀ j ∈ s, h i = h j → i = j)
    {Γ Q : (ZMod p)[X]} {c : ZMod p} (hF : pencil Γ Q c = ∏ i ∈ s, h i) :
    IsNormForm p d (pencil Γ Q c) ↔ ∀ i ∈ s, d ∣ (h i).natDegree := by
  have hprod : pencil Γ Q c = ∏ i ∈ s, h i ^ (1 : ℕ) := by simpa using hF
  rw [IsNormForm, hprod, NormCriterion.normForm_iff_galoisField p d hd s h (fun _ => 1)
    hirr hmon hdist]
  simp

end Chebotarev

end Monodromy
