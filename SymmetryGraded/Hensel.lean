/-
  Hensel.lean

  Formal verification (Lean 4 + Mathlib) of the lifting step of

    Lemma "Norm criterion"  (Appendix "Proofs for the framework")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  Over the residue field `F_p` the criterion is proved in `NormCriterion.lean`;
  the paper then remarks that for `e > 1` and squarefree `F` the `d` conjugate
  factors are pairwise coprime, so Hensel's lemma lifts the linear factor `C`
  from `F_{p^d}[Y]` to `R[Y]` with `R = GR(p^e, d)`.  That lifting step is what
  is formalised here, abstractly: `GR(p^e, d)` is not constructed, it is replaced
  by an arbitrary commutative ring `S` carrying a ring automorphism `σ` (the
  Frobenius) in which the defect of the approximate root is nilpotent — which is
  exactly the situation of a Galois ring, whose maximal ideal `(p)` satisfies
  `p^e = 0`.  With no unproved placeholders:

  * `prod_X_sub_C_dvd`
        if `F` has roots `a i` for `i` in a finite set and the differences
        `a i − a j` (`i ≠ j`) are units, then `∏ (Y − a i) ∣ F`; this is the
        "pairwise coprime conjugate factors" of the paper.
  * `map_pow_X_sub_C`, `map_pow_eq_self`, `coe_pow_apply`
        bookkeeping for the iterated Frobenius: `(mapRingHom f)^i (Y − α) = Y − f^i α`,
        and a `σ`-fixed `F` (i.e. one with coefficients in the base ring) is fixed by
        every power of `σ`.
  * `eq_of_isNilpotent_sub_of_isRoot`
        uniqueness of the Hensel lift: two roots of `F` congruent to a simple
        approximate root `α₀` modulo the nilradical are equal.
  * `eq_orbProd_of_isNilpotent`   (the Hensel lift, main statement)
        let `F` be monic of degree `d` with `σ`-invariant coefficients, let `α₀`
        satisfy `F(α₀)` nilpotent and `F'(α₀)` a unit, and let the `d` conjugates
        `σⁱ α₀` be pairwise separated (pairwise differences are units).  Then there
        is a root `α` of `F` with `α − α₀` nilpotent and
        `F = Galois.orbProd (mapRingHom σ) d (Y − α) = ∏_{i<d} (Y − σⁱ α)`.
  * `eq_orbProd_of_local`
        the same statement for a local ring whose maximal ideal consists of
        nilpotents, with "unit" replaced by "outside the maximal ideal"; the
        residue field is then the `F_{p^d}` of the paper.
  * `isNilpotent_of_mem_span_singleton`, `eq_orbProd_of_maximalIdeal_eq_span`
        the Galois-ring instance: if the maximal ideal is `(p)` and `p^e = 0`,
        the nilpotence hypothesis is automatic.
  * `mem_mapC_iff_map_eq_zero`, `mapC_mul_mem`, `mapC_modByMonic`, `mapC_divByMonic`
        the ideal `C(I)·S[Y]` of polynomials all of whose coefficients lie in `I`:
        it is stable under `%ₘ` and `/ₘ` by a monic polynomial, and multiplying
        two such polynomials lands in the ideal attached to the product `I·J`.
  * `exists_step`
        one Newton step for a factorisation: if `F − g·h` has coefficients in `I`,
        `g`, `h` are monic with `deg g + deg h = deg F`, and `u·g + v·h ≡ 1` modulo
        `J ⊇ I`, then there are corrections `b`, `a` with coefficients in `I`,
        `deg b < deg g`, `deg a < deg h`, such that `F − (g+b)(h+a)` has coefficients
        in `I·J`.
  * `exists_lift_aux`, `exists_lift_of_isCoprime`
        (general, non-linear factor case) iterating the Newton step: if `J^N = 0`,
        `F`, `g`, `h` are monic with `deg g + deg h = deg F`, `F ≡ g·h` modulo `J`
        and the reductions of `g` and `h` are coprime over `S ⧸ J`, then the
        factorisation lifts: `F = g'·h'` exactly, with `g'`, `h'` monic of the same
        degrees and `g' ≡ g`, `h' ≡ h` modulo `J`.
  * `mapRingHom_pow_apply`, `pow_apply_mem`, `mapC_pow_mem`
        further bookkeeping: `(mapRingHom f)^i p = p.map (f^i)`, a `σ`-stable ideal is
        stable under every power of `σ`, and powers of a polynomial with coefficients
        in `I` have coefficients in the corresponding power of `I`.
  * `isCoprime_of_isCoprime_map_quotient`
        coprimality lifts along a nilpotent ideal: if the reductions of `a` and `b`
        modulo `J` are coprime and `J^N = 0`, then `a` and `b` are coprime in `S[Y]`
        (the Bezout defect is nilpotent, so `1 + defect` is a unit).
  * `eq_orbProd_of_lift`   (Lemma "Norm criterion" over the Galois ring, general case)
        the full Hensel lift of the criterion for a non-linear `C`: if `F` is monic with
        `σ`-invariant coefficients, `deg F = d · deg C₀`, `F ≡ Orb_d(C₀)` modulo the
        nilpotent ideal `J`, `σ J ⊆ J`, and the `d` conjugates of `C₀` are pairwise
        coprime modulo `J`, then `C₀` lifts to a monic `C ≡ C₀ (mod J)` of the same
        degree with `F = Orb_d(C)` exactly.

  Not formalized: the construction of `GR(p^e, d)` itself.
-/
import Mathlib
import SymmetryGraded.Doubling

namespace HenselLift

open Polynomial

variable {S : Type*} [CommRing S]

section Separated

/-- If `F` vanishes at `a i` for every `i` in a finite set `s` and the differences
    `a i − a j` for `i ≠ j` in `s` are units (the roots are "pairwise coprime"),
    then the product `∏_{i ∈ s} (X − a i)` of the corresponding linear factors
    divides `F`. -/
theorem prod_X_sub_C_dvd {ι : Type*} (s : Finset ι) (a : ι → S) (F : S[X])
    (hroot : ∀ i ∈ s, F.IsRoot (a i))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (a i - a j)) :
    (∏ i ∈ s, (X - C (a i))) ∣ F := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty => simp
  | insert b s hb ih =>
      have hbroot : F.IsRoot (a b) := hroot b (Finset.mem_insert_self b s)
      obtain ⟨G, hG⟩ := (dvd_iff_isRoot).2 hbroot
      have hGroot : ∀ i ∈ s, G.IsRoot (a i) := by
        intro i hi
        have hiF : F.IsRoot (a i) := hroot i (Finset.mem_insert_of_mem hi)
        have hu : IsUnit (a i - a b) :=
          hsep i (Finset.mem_insert_of_mem hi) b (Finset.mem_insert_self b s)
            (by rintro rfl; exact hb hi)
        have hmul : (a i - a b) * G.eval (a i) = 0 := by
          rw [IsRoot, hG] at hiF
          simpa using hiF
        obtain ⟨u, hu'⟩ := hu
        rw [← hu'] at hmul
        exact (IsUnit.mul_right_eq_zero ⟨u, rfl⟩).1 hmul
      have hdvd := ih G hGroot fun i hi j hj hij =>
        hsep i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      rw [Finset.prod_insert hb, hG]
      exact mul_dvd_mul_left _ hdvd

end Separated

section Frobenius

/-- The `i`-th iterate of the coefficientwise action of `f` on a linear polynomial:
    `(mapRingHom f)^i (X − C α) = X − C (fⁱ α)`. -/
lemma map_pow_X_sub_C (f : S →+* S) (i : ℕ) (α : S) :
    ((Polynomial.mapRingHom f) ^ i) (X - C α) = X - C ((f ^ i) α) := by
  induction i with
  | zero => simp [RingHom.one_def]
  | succ n ih =>
      rw [pow_succ', pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, RingHom.mul_def,
        RingHom.comp_apply]
      simp

/-- A polynomial fixed by the coefficientwise action of `f` is fixed by every power of `f`. -/
lemma map_pow_eq_self {f : S →+* S} {F : S[X]} (hfix : F.map f = F) (i : ℕ) :
    F.map (f ^ i) = F := by
  induction i with
  | zero => simp [RingHom.one_def]
  | succ n ih => rw [pow_succ', RingHom.mul_def, ← Polynomial.map_map, ih, hfix]

/-- Powers of a ring equivalence agree with powers of the underlying ring homomorphism. -/
lemma coe_pow_apply (σ : S ≃+* S) (i : ℕ) (x : S) :
    ((σ : S →+* S) ^ i) x = (σ ^ i) x := by
  induction i with
  | zero => simp [RingHom.one_def]
  | succ n ih =>
      rw [pow_succ', pow_succ', RingHom.mul_def, RingHom.comp_apply, ih]
      simp

end Frobenius

section Lift

/-- Uniqueness of the Hensel lift: if `F(α₀)` is nilpotent and `F'(α₀)` is a unit, then
    `F` has at most one root congruent to `α₀` modulo nilpotents. -/
theorem eq_of_isNilpotent_sub_of_isRoot {F : S[X]} {α₀ α β : S}
    (hnil : IsNilpotent (F.eval α₀)) (hunit : IsUnit (F.derivative.eval α₀))
    (hα : IsNilpotent (α - α₀)) (hαr : F.eval α = 0)
    (hβ : IsNilpotent (β - α₀)) (hβr : F.eval β = 0) : α = β := by
  obtain ⟨r, -, huniq⟩ :=
    Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (R := S) (S := S) (P := F) (x := α₀)
      (by simpa [Polynomial.coe_aeval_eq_eval] using hnil)
      (by simpa [Polynomial.coe_aeval_eq_eval] using hunit)
  rw [huniq α ⟨by simpa [neg_sub] using hα.neg, by simpa [Polynomial.coe_aeval_eq_eval] using hαr⟩,
    huniq β ⟨by simpa [neg_sub] using hβ.neg, by simpa [Polynomial.coe_aeval_eq_eval] using hβr⟩]

/-- Hensel lift of the norm criterion.  Let `σ` be a ring automorphism of `S`, let `F` be a
    monic polynomial of degree `d` whose coefficients are `σ`-invariant, and let `α₀` be an
    approximate simple root: `F(α₀)` is nilpotent and `F'(α₀)` is a unit.  If the `d`
    conjugates `σⁱ α₀` are pairwise separated (their differences are units), then `F` splits
    as the orbit product of a single linear factor: there is a genuine root `α` of `F` with
    `α − α₀` nilpotent and `F = ∏_{i<d} (X − σⁱ α)`. -/
theorem eq_orbProd_of_isNilpotent (σ : S ≃+* S) (d : ℕ) (F : S[X]) (α₀ : S)
    (hmonic : F.Monic) (hdeg : F.natDegree = d)
    (hfix : F.map (σ : S →+* S) = F)
    (hnil : IsNilpotent (F.eval α₀)) (hunit : IsUnit (F.derivative.eval α₀))
    (hsep : ∀ i < d, ∀ j < d, i ≠ j → IsUnit ((σ ^ i) α₀ - (σ ^ j) α₀)) :
    ∃ α : S, IsNilpotent (α - α₀) ∧ F.eval α = 0 ∧
      F = Galois.orbProd (Polynomial.mapRingHom (σ : S →+* S)) d (X - C α) := by
  rcases subsingleton_or_nontrivial S with _ | _
  · have : Subsingleton S[X] := ⟨fun p q => Polynomial.ext fun n => Subsingleton.elim _ _⟩
    exact ⟨0, ⟨1, Subsingleton.elim _ _⟩, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  obtain ⟨α, ⟨hn, hr⟩, -⟩ :=
    Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (R := S) (S := S) (P := F) (x := α₀)
      (by simpa [Polynomial.coe_aeval_eq_eval] using hnil)
      (by simpa [Polynomial.coe_aeval_eq_eval] using hunit)
  rw [Polynomial.coe_aeval_eq_eval] at hr
  have hnα : IsNilpotent (α - α₀) := by simpa [neg_sub] using hn.neg
  refine ⟨α, hnα, hr, ?_⟩
  have hroot : ∀ i ∈ Finset.range d, F.IsRoot ((σ ^ i) α) := by
    intro i _
    have hmap : F.map ((σ : S →+* S) ^ i) = F := map_pow_eq_self hfix i
    have hev : F.eval (((σ : S →+* S) ^ i) α) = ((σ : S →+* S) ^ i) (F.eval α) := by
      conv_lhs => rw [← hmap]
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [IsRoot, ← coe_pow_apply, hev, hr, map_zero]
  have hsep' : ∀ i ∈ Finset.range d, ∀ j ∈ Finset.range d, i ≠ j →
      IsUnit ((σ ^ i) α - (σ ^ j) α) := by
    intro i hi j hj hij
    have hu : IsUnit ((σ ^ i) α₀ - (σ ^ j) α₀) :=
      hsep i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij
    have hni : IsNilpotent ((σ ^ i) α - (σ ^ i) α₀) := by
      simpa [map_sub] using hnα.map (σ ^ i)
    have hnj : IsNilpotent ((σ ^ j) α - (σ ^ j) α₀) := by
      simpa [map_sub] using hnα.map (σ ^ j)
    have hdiff : IsNilpotent (((σ ^ i) α - (σ ^ i) α₀) - ((σ ^ j) α - (σ ^ j) α₀)) :=
      (Commute.all _ _).isNilpotent_sub hni hnj
    have hsum := hdiff.isUnit_add_left_of_commute hu (Commute.all _ _)
    convert hsum using 1
    ring
  have hdvd : (∏ i ∈ Finset.range d, (X - C ((σ ^ i) α))) ∣ F :=
    prod_X_sub_C_dvd _ _ _ hroot hsep'
  have hpm : (∏ i ∈ Finset.range d, (X - C ((σ ^ i) α))).Monic :=
    monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hpd : (∏ i ∈ Finset.range d, (X - C ((σ ^ i) α))).natDegree = d := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C ((σ ^ i) α)]
    simp
  have hFeq := eq_of_monic_of_dvd_of_natDegree_le hpm hmonic hdvd (by rw [hdeg, hpd])
  rw [hFeq, Galois.orbProd]
  exact Finset.prod_congr rfl fun i _ => by rw [map_pow_X_sub_C, coe_pow_apply]

end Lift

section LocalRing

/-- The Galois-ring form of the Hensel lift.  In a local ring whose maximal ideal consists of
    nilpotent elements (e.g. `GR(p^e, d)`, where the maximal ideal is `(p)` and `p^e = 0`),
    the unit hypotheses of `eq_orbProd_of_isNilpotent` become membership conditions for the
    maximal ideal: `α₀` is a root of `F` in the residue field, it is a simple root there, and
    its `d` conjugates are pairwise distinct in the residue field. -/
theorem eq_orbProd_of_local [IsLocalRing S]
    (hnilm : ∀ x ∈ IsLocalRing.maximalIdeal S, IsNilpotent x)
    (σ : S ≃+* S) (d : ℕ) (F : S[X]) (α₀ : S)
    (hmonic : F.Monic) (hdeg : F.natDegree = d)
    (hfix : F.map (σ : S →+* S) = F)
    (hroot : F.eval α₀ ∈ IsLocalRing.maximalIdeal S)
    (hder : F.derivative.eval α₀ ∉ IsLocalRing.maximalIdeal S)
    (hsep : ∀ i < d, ∀ j < d, i ≠ j →
      ((σ ^ i) α₀ - (σ ^ j) α₀) ∉ IsLocalRing.maximalIdeal S) :
    ∃ α : S, IsNilpotent (α - α₀) ∧ F.eval α = 0 ∧
      F = Galois.orbProd (Polynomial.mapRingHom (σ : S →+* S)) d (X - C α) :=
  eq_orbProd_of_isNilpotent σ d F α₀ hmonic hdeg hfix (hnilm _ hroot)
    (IsLocalRing.notMem_maximalIdeal.1 hder)
    fun i hi j hj hij => IsLocalRing.notMem_maximalIdeal.1 (hsep i hi j hj hij)

/-- Every element of the ideal generated by a nilpotent element is nilpotent. -/
lemma isNilpotent_of_mem_span_singleton {p : S} {e : ℕ} (hp : p ^ e = 0) {x : S}
    (hx : x ∈ Ideal.span ({p} : Set S)) : IsNilpotent x := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 hx
  exact ⟨e, by rw [mul_pow, hp, zero_mul]⟩

/-- The Hensel lift for a local ring whose maximal ideal is generated by a nilpotent element
    `p` with `p ^ e = 0`: this is exactly the Galois ring `GR(p^e, d)` of the paper, whose
    residue field is `F_{p^d}`. -/
theorem eq_orbProd_of_maximalIdeal_eq_span [IsLocalRing S] {p : S} {e : ℕ}
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span ({p} : Set S)) (hp : p ^ e = 0)
    (σ : S ≃+* S) (d : ℕ) (F : S[X]) (α₀ : S)
    (hmonic : F.Monic) (hdeg : F.natDegree = d)
    (hfix : F.map (σ : S →+* S) = F)
    (hroot : F.eval α₀ ∈ IsLocalRing.maximalIdeal S)
    (hder : F.derivative.eval α₀ ∉ IsLocalRing.maximalIdeal S)
    (hsep : ∀ i < d, ∀ j < d, i ≠ j →
      ((σ ^ i) α₀ - (σ ^ j) α₀) ∉ IsLocalRing.maximalIdeal S) :
    ∃ α : S, IsNilpotent (α - α₀) ∧ F.eval α = 0 ∧
      F = Galois.orbProd (Polynomial.mapRingHom (σ : S →+* S)) d (X - C α) :=
  eq_orbProd_of_local (fun _ hx => isNilpotent_of_mem_span_singleton hp (hmax ▸ hx))
    σ d F α₀ hmonic hdeg hfix hroot hder hsep

end LocalRing

section Factorisation

/-- A polynomial has all its coefficients in the ideal `I` exactly when it dies in
    `(S ⧸ I)[X]`. -/
lemma mem_mapC_iff_map_eq_zero {I : Ideal S} {p : S[X]} :
    p ∈ Ideal.map (C : S →+* S[X]) I ↔ p.map (Ideal.Quotient.mk I) = 0 := by
  rw [Ideal.mem_map_C_iff, Polynomial.ext_iff]
  simp [coeff_map, Ideal.Quotient.eq_zero_iff_mem]

/-- The product of a polynomial with coefficients in `I` and one with coefficients in `J`
    has all its coefficients in `I * J`. -/
lemma mapC_mul_mem {I J : Ideal S} {p q : S[X]}
    (hp : p ∈ Ideal.map (C : S →+* S[X]) I) (hq : q ∈ Ideal.map (C : S →+* S[X]) J) :
    p * q ∈ Ideal.map (C : S →+* S[X]) (I * J) := by
  rw [Ideal.mem_map_C_iff] at hp hq ⊢
  intro n
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_mul (hp _) (hq _)

/-- Division with remainder by a monic polynomial preserves the property of having all
    coefficients in an ideal (remainder). -/
lemma mapC_modByMonic {I : Ideal S} {p q : S[X]} (hp : p ∈ Ideal.map (C : S →+* S[X]) I)
    (hq : q.Monic) : p %ₘ q ∈ Ideal.map (C : S →+* S[X]) I := by
  rw [mem_mapC_iff_map_eq_zero] at hp ⊢
  rw [Polynomial.map_modByMonic _ hq, hp, zero_modByMonic]

/-- Division with remainder by a monic polynomial preserves the property of having all
    coefficients in an ideal (quotient). -/
lemma mapC_divByMonic {I : Ideal S} {p q : S[X]} (hp : p ∈ Ideal.map (C : S →+* S[X]) I)
    (hq : q.Monic) : p /ₘ q ∈ Ideal.map (C : S →+* S[X]) I := by
  rw [mem_mapC_iff_map_eq_zero] at hp ⊢
  rw [Polynomial.map_divByMonic _ hq, hp, zero_divByMonic]

/-- One Newton step for the lifting of a factorisation.  Let `I ≤ J` be ideals, let `F`,
    `g`, `h` be monic with `deg F = deg g + deg h`, let the defect `F − g·h` have all its
    coefficients in `I`, and let `u·g + v·h − 1` have all its coefficients in `J` (a lifted
    Bezout identity witnessing that `g` and `h` are coprime modulo `J`).  Then `g` and `h`
    can be corrected by polynomials `b`, `a` with coefficients in `I` and with
    `deg b < deg g`, `deg a < deg h`, so that the new defect `F − (g+b)·(h+a)` has all its
    coefficients in the smaller ideal `I·J`. -/
lemma exists_step [Nontrivial S] {I J : Ideal S} (hIJ : I ≤ J) {F g h u v : S[X]}
    (hF : F.Monic) (hg : g.Monic) (hh : h.Monic)
    (hdeg : F.natDegree = g.natDegree + h.natDegree)
    (hD : F - g * h ∈ Ideal.map (C : S →+* S[X]) I)
    (hw : u * g + v * h - 1 ∈ Ideal.map (C : S →+* S[X]) J) :
    ∃ b a : S[X], b ∈ Ideal.map (C : S →+* S[X]) I ∧ a ∈ Ideal.map (C : S →+* S[X]) I ∧
      b.degree < g.degree ∧ a.degree < h.degree ∧
      F - (g + b) * (h + a) ∈ Ideal.map (C : S →+* S[X]) (I * J) := by
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : S[X], Δ = F - g * h := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : S[X], q = (u * Δ) /ₘ h := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : S[X], a = (u * Δ) %ₘ h := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : S[X], b = (Δ - g * a) /ₘ h := ⟨_, rfl⟩
  rw [← hΔ] at hD
  have haI : a ∈ Ideal.map (C : S →+* S[X]) I := by
    rw [ha]; exact mapC_modByMonic (Ideal.mul_mem_left _ u hD) hh
  have hgaI : Δ - g * a ∈ Ideal.map (C : S →+* S[X]) I :=
    Ideal.sub_mem _ hD (Ideal.mul_mem_left _ g haI)
  have hbI : b ∈ Ideal.map (C : S →+* S[X]) I := by
    rw [hb]; exact mapC_divByMonic hgaI hh
  have hg0 : g ≠ 0 := hg.ne_zero
  have hh0 : h ≠ 0 := hh.ne_zero
  have hgb : g.degree ≠ ⊥ := fun hx => hg0 (degree_eq_bot.1 hx)
  have hhb : h.degree ≠ ⊥ := fun hx => hh0 (degree_eq_bot.1 hx)
  have hadeg : a.degree < h.degree := by rw [ha]; exact degree_modByMonic_lt _ hh
  have hFgh : F.degree = (g * h).degree := by
    rw [degree_eq_natDegree hF.ne_zero, degree_eq_natDegree (hg.mul hh).ne_zero,
      hg.natDegree_mul hh, hdeg]
  have hΔlt : Δ.degree < F.degree := by
    rw [hΔ]
    exact degree_sub_lt hFgh hF.ne_zero (by simp [hF.leadingCoeff, (hg.mul hh).leadingCoeff])
  have hFd : F.degree = g.degree + h.degree := by rw [hFgh, hh.degree_mul]
  have hhle : h.degree ≤ g.degree + h.degree := by
    have h0 : (0 : WithBot ℕ) ≤ g.degree := zero_le_degree_iff.2 hg0
    simpa [add_comm] using add_le_add_right h0 h.degree
  have hkey : h * b = (Δ - g * a) - ((Δ - g * a) %ₘ h) := by
    have hmd := modByMonic_add_div (Δ - g * a) h
    rw [hb]; linear_combination hmd
  have hrhs : ((Δ - g * a) - ((Δ - g * a) %ₘ h)).degree < g.degree + h.degree := by
    refine lt_of_le_of_lt (degree_sub_le _ _) ?_
    rw [max_lt_iff]
    refine ⟨?_, lt_of_lt_of_le (degree_modByMonic_lt _ hh) hhle⟩
    refine lt_of_le_of_lt (degree_sub_le _ _) ?_
    rw [max_lt_iff]
    refine ⟨by rwa [hFd] at hΔlt, ?_⟩
    rw [mul_comm, hg.degree_mul, add_comm g.degree h.degree]
    exact WithBot.add_lt_add_right hgb hadeg
  have hbdeg : b.degree < g.degree := by
    rw [← hkey, mul_comm, hh.degree_mul] at hrhs
    exact (WithBot.add_lt_add_iff_right hhb).1 hrhs
  refine ⟨b, a, hbI, haI, hbdeg, hadeg, ?_⟩
  have hmodeq : (Δ - g * a) %ₘ h = (-((u * g + v * h - 1) * Δ)) %ₘ h := by
    refine modByMonic_eq_of_dvd_sub hh ⟨g * q + v * Δ, ?_⟩
    have hmd : a + h * q = u * Δ := by rw [ha, hq]; exact modByMonic_add_div _ _
    linear_combination (-g : S[X]) * hmd
  have hM : (Δ - g * a) %ₘ h ∈ Ideal.map (C : S →+* S[X]) (I * J) := by
    rw [hmodeq]
    refine mapC_modByMonic (neg_mem ?_) hh
    have hmem := mapC_mul_mem hw hD
    rwa [mul_comm J I] at hmem
  have hab : a * b ∈ Ideal.map (C : S →+* S[X]) (I * J) :=
    Ideal.map_mono (Ideal.mul_mono_right hIJ) (mapC_mul_mem haI hbI)
  have hfinal : F - (g + b) * (h + a) = ((Δ - g * a) %ₘ h) - a * b := by
    linear_combination -hkey - hΔ
  rw [hfinal]
  exact Ideal.sub_mem _ hM hab

/-- Iterating the Newton step `exists_step`: starting from a factorisation that is correct
    modulo `J`, after `k` steps the defect has all its coefficients in `J ^ (k+1)`, while the
    factors stay monic of unchanged degree and congruent to the originals modulo `J`. -/
lemma exists_lift_aux [Nontrivial S] {J : Ideal S} {F u v : S[X]} (hF : F.Monic) (k : ℕ) :
    ∀ g h : S[X], g.Monic → h.Monic → F.natDegree = g.natDegree + h.natDegree →
      F - g * h ∈ Ideal.map (C : S →+* S[X]) J →
      u * g + v * h - 1 ∈ Ideal.map (C : S →+* S[X]) J →
      ∃ g' h' : S[X], g'.Monic ∧ h'.Monic ∧ g'.natDegree = g.natDegree ∧
        h'.natDegree = h.natDegree ∧ g' - g ∈ Ideal.map (C : S →+* S[X]) J ∧
        h' - h ∈ Ideal.map (C : S →+* S[X]) J ∧
        F - g' * h' ∈ Ideal.map (C : S →+* S[X]) (J ^ (k + 1)) := by
  induction k with
  | zero =>
      intro g h hg hh _ hD _
      exact ⟨g, h, hg, hh, rfl, rfl, by simp, by simp, by simpa using hD⟩
  | succ k ih =>
      intro g h hg hh hdeg hD hw
      obtain ⟨g₁, h₁, hg₁, hh₁, hdg₁, hdh₁, hsg₁, hsh₁, hD₁⟩ := ih g h hg hh hdeg hD hw
      have hdeg₁ : F.natDegree = g₁.natDegree + h₁.natDegree := by rw [hdg₁, hdh₁, hdeg]
      have hw₁ : u * g₁ + v * h₁ - 1 ∈ Ideal.map (C : S →+* S[X]) J := by
        have hrw : u * g₁ + v * h₁ - 1
            = (u * g + v * h - 1) + (u * (g₁ - g) + v * (h₁ - h)) := by ring
        rw [hrw]
        exact Ideal.add_mem _ hw (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hsg₁)
          (Ideal.mul_mem_left _ _ hsh₁))
      have hIJ : J ^ (k + 1) ≤ J := by
        simpa using Ideal.pow_le_pow_right (I := J) (m := 1) (n := k + 1) (by omega)
      obtain ⟨b, a, hbI, haI, hbdeg, hadeg, hE⟩ := exists_step hIJ hF hg₁ hh₁ hdeg₁ hD₁ hw₁
      refine ⟨g₁ + b, h₁ + a, hg₁.add_of_left hbdeg, hh₁.add_of_left hadeg, ?_, ?_, ?_, ?_, ?_⟩
      · exact (natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hbdeg)).trans hdg₁
      · exact (natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hadeg)).trans hdh₁
      · have hrw : g₁ + b - g = (g₁ - g) + b := by ring
        exact hrw ▸ Ideal.add_mem _ hsg₁ (Ideal.map_mono hIJ hbI)
      · have hrw : h₁ + a - h = (h₁ - h) + a := by ring
        exact hrw ▸ Ideal.add_mem _ hsh₁ (Ideal.map_mono hIJ haI)
      · rwa [pow_succ] at hE ⊢

/-- Hensel lifting of a coprime factorisation modulo a nilpotent ideal.  Let `J` be an ideal
    with `J ^ N = 0`, let `F`, `g`, `h` be monic with `deg F = deg g + deg h`, suppose all the
    coefficients of `F − g·h` lie in `J`, and suppose the reductions of `g` and `h` are
    coprime in `(S ⧸ J)[X]`.  Then the factorisation lifts to an exact one: `F = g' · h'` with
    `g'`, `h'` monic of the same degrees as `g`, `h`, and `g' ≡ g`, `h' ≡ h` modulo `J`.  For
    `J = (p)` in a Galois ring this is the general (non-linear) form of the lifting used by
    the norm criterion. -/
theorem exists_lift_of_isCoprime (J : Ideal S) {N : ℕ} (hJ : J ^ N = ⊥)
    (F : S[X]) (hF : F.Monic) (g h : S[X]) (hg : g.Monic) (hh : h.Monic)
    (hdeg : F.natDegree = g.natDegree + h.natDegree)
    (hmod : ∀ n, (F - g * h).coeff n ∈ J)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk J)) (h.map (Ideal.Quotient.mk J))) :
    ∃ g' h' : S[X], g'.Monic ∧ h'.Monic ∧ g'.natDegree = g.natDegree ∧
      h'.natDegree = h.natDegree ∧ F = g' * h' ∧
      (∀ n, (g' - g).coeff n ∈ J) ∧ (∀ n, (h' - h).coeff n ∈ J) := by
  rcases subsingleton_or_nontrivial S with _ | _
  · have : Subsingleton S[X] := ⟨fun p q => Polynomial.ext fun n => Subsingleton.elim _ _⟩
    exact ⟨g, h, hg, hh, rfl, rfl, Subsingleton.elim _ _, fun n => by simp, fun n => by simp⟩
  obtain ⟨u', v', huv⟩ := hcop
  obtain ⟨u, rfl⟩ :=
    Polynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective u'
  obtain ⟨v, rfl⟩ :=
    Polynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective v'
  have hw : u * g + v * h - 1 ∈ Ideal.map (C : S →+* S[X]) J := by
    rw [mem_mapC_iff_map_eq_zero, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_one, huv, sub_self]
  have hD : F - g * h ∈ Ideal.map (C : S →+* S[X]) J := Ideal.mem_map_C_iff.2 hmod
  obtain ⟨g', h', hg', hh', hdg', hdh', hsg', hsh', hE⟩ :=
    exists_lift_aux (J := J) (u := u) (v := v) hF N g h hg hh hdeg hD hw
  have hbot : J ^ (N + 1) = ⊥ := le_bot_iff.1 (hJ ▸ Ideal.pow_le_pow_right (by omega))
  have hzero : F - g' * h' = 0 := by
    rw [hbot] at hE
    exact Polynomial.ext fun n => by simpa using Ideal.mem_map_C_iff.1 hE n
  exact ⟨g', h', hg', hh', hdg', hdh', by linear_combination hzero,
    fun n => Ideal.mem_map_C_iff.1 hsg' n, fun n => Ideal.mem_map_C_iff.1 hsh' n⟩

end Factorisation

section OrbitLift

/-- The `i`-th iterate of the coefficientwise action of `f` is the coefficientwise action
    of `f ^ i`. -/
lemma mapRingHom_pow_apply (f : S →+* S) (i : ℕ) (p : S[X]) :
    ((Polynomial.mapRingHom f) ^ i) p = p.map (f ^ i) := by
  induction i with
  | zero => simp [RingHom.one_def]
  | succ n ih =>
      rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, pow_succ', RingHom.mul_def]
      simp [Polynomial.map_map]

/-- An ideal stable under a ring automorphism is stable under all of its powers. -/
lemma pow_apply_mem {J : Ideal S} {σ : S ≃+* S} (hσJ : ∀ x ∈ J, σ x ∈ J) (i : ℕ) {x : S}
    (hx : x ∈ J) : ((σ : S →+* S) ^ i) x ∈ J := by
  induction i with
  | zero => simpa [RingHom.one_def] using hx
  | succ n ih =>
      rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
      exact hσJ _ ih

/-- A power of a polynomial whose coefficients lie in `I` has its coefficients in the
    corresponding power of `I`. -/
lemma mapC_pow_mem {I : Ideal S} {p : S[X]} (hp : p ∈ Ideal.map (C : S →+* S[X]) I) (k : ℕ) :
    p ^ (k + 1) ∈ Ideal.map (C : S →+* S[X]) (I ^ (k + 1)) := by
  induction k with
  | zero => simpa using hp
  | succ k ih => rw [pow_succ, pow_succ]; exact mapC_mul_mem ih hp

/-- Coprimality lifts along a nilpotent ideal: if the reductions of `a` and `b` modulo `J`
    are coprime and `J ^ N = 0`, then `a` and `b` are already coprime in `S[X]`.  Indeed a
    lifted Bezout identity reads `u·a + v·b = 1 + n` with `n` having all coefficients in `J`,
    hence nilpotent, so that `1 + n` is a unit. -/
lemma isCoprime_of_isCoprime_map_quotient {J : Ideal S} {N : ℕ} (hJ : J ^ N = ⊥) {a b : S[X]}
    (hab : IsCoprime (a.map (Ideal.Quotient.mk J)) (b.map (Ideal.Quotient.mk J))) :
    IsCoprime a b := by
  obtain ⟨u', v', huv⟩ := hab
  obtain ⟨u, rfl⟩ :=
    Polynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective u'
  obtain ⟨v, rfl⟩ :=
    Polynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective v'
  have hmem : u * a + v * b - 1 ∈ Ideal.map (C : S →+* S[X]) J := by
    rw [mem_mapC_iff_map_eq_zero, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_one, huv, sub_self]
  have hbot : J ^ (N + 1) = ⊥ := le_bot_iff.1 (hJ ▸ Ideal.pow_le_pow_right (by omega))
  have hnil : IsNilpotent (u * a + v * b - 1) := by
    refine ⟨N + 1, ?_⟩
    have hp := mapC_pow_mem hmem N
    rw [hbot] at hp
    exact Polynomial.ext fun n => by simpa using Ideal.mem_map_C_iff.1 hp n
  have hunit : IsUnit (u * a + v * b) := by
    simpa using hnil.isUnit_add_left_of_commute isUnit_one (Commute.all _ _)
  obtain ⟨w, hw⟩ := hunit.exists_left_inv
  exact ⟨w * u, w * v, by linear_combination hw⟩

/-- The norm criterion over the Galois ring, general (non-linear) case.  Let `J` be a
    nilpotent ideal stable under the automorphism `σ` (for a Galois ring, `J = (p)` with
    `p ^ e = 0`).  Let `F` be monic of degree `d · deg C₀` with `σ`-invariant coefficients,
    let `C₀` be monic, assume `F ≡ Orb_d(C₀) = ∏_{i<d} σⁱ C₀` modulo `J`, and assume the `d`
    conjugates of `C₀` are pairwise coprime modulo `J` (the reduction of `F` is squarefree
    in the paper's hypothesis).  Then `C₀` lifts to a monic `C` of the same degree with
    `C ≡ C₀` modulo `J` and `F = Orb_d(C)` exactly. -/
theorem eq_orbProd_of_lift (J : Ideal S) {N : ℕ} (hJ : J ^ N = ⊥)
    (σ : S ≃+* S) (hσJ : ∀ x ∈ J, σ x ∈ J) (d : ℕ)
    (F C₀ : S[X]) (hF : F.Monic) (hC₀ : C₀.Monic)
    (hfix : F.map (σ : S →+* S) = F)
    (hdeg : F.natDegree = d * C₀.natDegree)
    (hcong : ∀ n, (F - Galois.orbProd (Polynomial.mapRingHom (σ : S →+* S)) d C₀).coeff n ∈ J)
    (hcop : ∀ i < d, ∀ j < d, i ≠ j →
        IsCoprime ((((Polynomial.mapRingHom (σ : S →+* S)) ^ i) C₀).map (Ideal.Quotient.mk J))
                  ((((Polynomial.mapRingHom (σ : S →+* S)) ^ j) C₀).map (Ideal.Quotient.mk J))) :
    ∃ C : S[X], C.Monic ∧ C.natDegree = C₀.natDegree ∧ (∀ n, (C - C₀).coeff n ∈ J) ∧
      F = Galois.orbProd (Polynomial.mapRingHom (σ : S →+* S)) d C := by
  rcases subsingleton_or_nontrivial S with _ | _
  · have : Subsingleton S[X] := ⟨fun p q => Polynomial.ext fun n => Subsingleton.elim _ _⟩
    exact ⟨C₀, hC₀, rfl, fun n => by simp, Subsingleton.elim _ _⟩
  have hcm : ∀ i : ℕ, (((Polynomial.mapRingHom (σ : S →+* S)) ^ i) C₀).Monic := fun i => by
    rw [mapRingHom_pow_apply]; exact hC₀.map _
  have hcd : ∀ i : ℕ,
      (((Polynomial.mapRingHom (σ : S →+* S)) ^ i) C₀).natDegree = C₀.natDegree := fun i => by
    rw [mapRingHom_pow_apply]; exact hC₀.natDegree_map _
  cases d with
  | zero =>
      refine ⟨C₀, hC₀, rfl, fun n => by simp, ?_⟩
      rw [Galois.orbProd_zero]
      exact eq_one_of_monic_natDegree_zero hF (by simpa using hdeg)
  | succ n =>
      obtain ⟨T, hT⟩ : ∃ T : S[X], T = ∏ i ∈ Finset.range n,
          ((Polynomial.mapRingHom (σ : S →+* S)) ^ (i + 1)) C₀ := ⟨_, rfl⟩
      have hTm : T.Monic := by rw [hT]; exact monic_prod_of_monic _ _ fun i _ => hcm _
      have hTd : T.natDegree = n * C₀.natDegree := by
        have hsum : ∑ i ∈ Finset.range n,
            (((Polynomial.mapRingHom (σ : S →+* S)) ^ (i + 1)) C₀).natDegree
              = ∑ _i ∈ Finset.range n, C₀.natDegree :=
          Finset.sum_congr rfl fun i _ => hcd (i + 1)
        rw [hT, natDegree_prod_of_monic _ _ fun i _ => hcm (i + 1), hsum, Finset.sum_const,
          Finset.card_range, smul_eq_mul]
      have horb : Galois.orbProd (Polynomial.mapRingHom (σ : S →+* S)) (n + 1) C₀ = C₀ * T := by
        rw [Galois.orbProd, Finset.prod_range_succ', hT, mul_comm]
        simp [RingHom.one_def]
      have hdeg' : F.natDegree = C₀.natDegree + T.natDegree := by
        rw [hdeg, hTd]; ring
      have hmod : ∀ k, (F - C₀ * T).coeff k ∈ J := by rw [← horb]; exact hcong
      have hcopq : IsCoprime (C₀.map (Ideal.Quotient.mk J)) (T.map (Ideal.Quotient.mk J)) := by
        rw [hT, Polynomial.map_prod]
        refine IsCoprime.prod_right fun i hi => ?_
        have h0 : ((Polynomial.mapRingHom (σ : S →+* S)) ^ 0) C₀ = C₀ := by simp [RingHom.one_def]
        have hci := hcop 0 (by omega) (i + 1) (by simp only [Finset.mem_range] at hi; omega)
          (by omega)
        rwa [h0] at hci
      obtain ⟨G, T', hGm, -, hGd, -, hFeq, hGsub, -⟩ :=
        exists_lift_of_isCoprime J hJ F hF C₀ T hC₀ hTm hdeg' hmod hcopq
      refine ⟨G, hGm, hGd, hGsub, ?_⟩
      have hGdvd : ∀ i : ℕ, ((Polynomial.mapRingHom (σ : S →+* S)) ^ i) G ∣ F := by
        intro i
        rw [mapRingHom_pow_apply]
        have hd := Polynomial.map_dvd ((σ : S →+* S) ^ i) (Dvd.intro T' hFeq.symm)
        rwa [map_pow_eq_self hfix i] at hd
      have hred : ∀ i : ℕ,
          (((Polynomial.mapRingHom (σ : S →+* S)) ^ i) G).map (Ideal.Quotient.mk J)
            = (((Polynomial.mapRingHom (σ : S →+* S)) ^ i) C₀).map (Ideal.Quotient.mk J) := by
        intro i
        have hsub : ((Polynomial.mapRingHom (σ : S →+* S)) ^ i) G
            - ((Polynomial.mapRingHom (σ : S →+* S)) ^ i) C₀
              ∈ Ideal.map (C : S →+* S[X]) J := by
          rw [mapRingHom_pow_apply, mapRingHom_pow_apply, Ideal.mem_map_C_iff]
          intro k
          have hk : (G.map ((σ : S →+* S) ^ i) - C₀.map ((σ : S →+* S) ^ i)).coeff k
              = ((σ : S →+* S) ^ i) ((G - C₀).coeff k) := by simp
          rw [hk]
          exact pow_apply_mem hσJ i (hGsub k)
        rw [mem_mapC_iff_map_eq_zero, Polynomial.map_sub, sub_eq_zero] at hsub
        exact hsub
      have hproddvd :
          (∏ i ∈ Finset.range (n + 1), ((Polynomial.mapRingHom (σ : S →+* S)) ^ i) G) ∣ F := by
        refine Finset.prod_dvd_of_coprime ?_ fun i _ => hGdvd i
        intro i hi j hj hij
        refine isCoprime_of_isCoprime_map_quotient hJ ?_
        rw [hred i, hred j]
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        exact hcop i hi j hj hij
      have hpm : (∏ i ∈ Finset.range (n + 1),
          ((Polynomial.mapRingHom (σ : S →+* S)) ^ i) G).Monic :=
        monic_prod_of_monic _ _ fun i _ => by rw [mapRingHom_pow_apply]; exact hGm.map _
      have hpd : (∏ i ∈ Finset.range (n + 1),
          ((Polynomial.mapRingHom (σ : S →+* S)) ^ i) G).natDegree = (n + 1) * C₀.natDegree := by
        rw [natDegree_prod_of_monic _ _ fun i _ =>
          (by rw [mapRingHom_pow_apply]; exact hGm.map _ :
            (((Polynomial.mapRingHom (σ : S →+* S)) ^ i) G).Monic)]
        have hone : ∀ i : ℕ, (((Polynomial.mapRingHom (σ : S →+* S)) ^ i) G).natDegree
            = C₀.natDegree := by
          intro i; rw [mapRingHom_pow_apply, hGm.natDegree_map, hGd]
        rw [Finset.sum_congr rfl fun i _ => hone i, Finset.sum_const, Finset.card_range,
          smul_eq_mul]
      rw [Galois.orbProd]
      exact eq_of_monic_of_dvd_of_natDegree_le hpm hF hproddvd (by rw [hdeg, hpd])

end OrbitLift

end HenselLift
