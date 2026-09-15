/-
  Commute.lean

  Formal verification (Lean 4 + Mathlib) of

    Lemma "Scalar rotation is a diagonal automorphism",
    Lemma "The scalar and Galois actions commute"  and
    Proposition "Bigraded decomposition"
    (Appendix B.2, "Commutation of the scalar and Galois actions")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  The Frobenius is an arbitrary ring endomorphism `φ : R →+* R` of a commutative
  ring, acting coefficientwise on `R[X]` (`Polynomial.map φ`); the scalar
  rotation `σ_A` is the substitution `X ↦ A·X`, i.e. the ring endomorphism
  `p ↦ p.comp (C A * X)`, which acts coefficientwise as `cₖ ↦ Aᵏ·cₖ`.
  With no unproved placeholders:

  * `sigma`, `sigma_coeff`, `sigma_eq_comp`
        `σ_A` as a ring endomorphism of `R[X]`; `(σ_A p).coeff k = Aᵏ · p.coeff k`.
  * `sigma_sigma`, `sigma_pow`, `sigma_pow_eq_one`, `sigma_inv_sigma`
        (Lemma "Scalar rotation is a diagonal automorphism")
        `σ_A ∘ σ_B = σ_{AB}`, `σ_Aˡ = σ_{Aˡ}`, `σ_A^r = id` for `A^r = 1`,
        and `σ_{A⁻¹}` is the inverse of `σ_A` for a unit `A`.
  * `map_sigma`                (Lemma "commute", part (a))
        `φ(A) = A` ⟹ `map φ (σ_A p) = σ_A (map φ p)`.
  * `G`, `map_G`, `sigma_G`   (descent to `V = R[X]/(G_S)`, part (b))
        `G_S = ∏_{a∈S}(X − a)`; `φ` fixes `S` ⟹ `map φ G_S = G_S`;
        `A·S = S`, `A` a unit ⟹ `σ_A G_S = A^{|S|} · G_S`.
  * `dvd_sigma_of_dvd`, `dvd_map_of_dvd`, `span_G_map_sigma_le`, `span_G_map_le`
        both operators preserve the ideal `(G_S)`.
  * `pi`, `pi_coeff`, `sigma_pi`, `sum_pi`, `pi_pi`, `map_pi`
        (Proposition "Bigraded decomposition", over a field, `A` of exact
        order `r`, `r ≠ 0` in `K`)  the character idempotents
        `π_j = (1/r) Σ_{ℓ<r} A^{−jℓ} σ_A^ℓ` satisfy
        `(π_j p).coeff k = [Aᵏ = Aʲ]·p.coeff k`, `σ_A ∘ π_j = A^j · π_j`,
        `Σ_j π_j = id`, `π_j ∘ π_{j'} = [j = j'] π_j`, and `map φ ∘ π_j = π_j ∘ map φ`.
  * `direct_product`, `direct_product_hom`
        (Lemma "commute", direct product)  `σ_A^a = (map φ)^b` on `R[X]` forces
        `A^a = 1` and `φ^b = 1` (evaluate on `X` and on constants).
-/
import Mathlib
import SymmetryGraded.Doubling

namespace GaloisCommute

open Polynomial Finset

/-! ## 1. The scalar rotation `σ_A` -/
section Ring
variable {R : Type*} [CommRing R]

/-- The scalar rotation `σ_A : p(X) ↦ p(A·X)` as a ring endomorphism of `R[X]`. -/
noncomputable def sigma (A : R) : R[X] →+* R[X] := compRingHom (C A * X)

theorem sigma_eq_comp (A : R) (p : R[X]) : sigma A p = p.comp (C A * X) := rfl

/-- Coefficientwise, `σ_A` scales the `k`-th coefficient by `Aᵏ`: `σ_A : cₖ ↦ Aᵏ·cₖ`. -/
theorem sigma_coeff (A : R) (p : R[X]) (k : ℕ) :
    (sigma A p).coeff k = A ^ k * p.coeff k := by
  rw [sigma_eq_comp]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, mul_add]
  | monomial m a =>
      have hpow : (C A * X) ^ m = C (A ^ m) * X ^ m := by rw [mul_pow, ← C_pow]
      rw [monomial_comp, hpow, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_monomial]
      by_cases h : k = m
      · subst h; rw [if_pos rfl, if_pos rfl]; ring
      · rw [if_neg h, if_neg (fun e => h e.symm)]; ring

theorem sigma_X (A : R) : sigma A X = C A * X := by
  rw [sigma_eq_comp, X_comp]

theorem sigma_C (A c : R) : sigma A (C c) = C c := by
  rw [sigma_eq_comp, C_comp]

/-- `σ_A ∘ σ_B = σ_{AB}`. -/
theorem sigma_sigma (A B : R) (p : R[X]) : sigma A (sigma B p) = sigma (A * B) p := by
  ext k; rw [sigma_coeff, sigma_coeff, sigma_coeff, mul_pow]; ring

theorem sigma_one (p : R[X]) : sigma (1 : R) p = p := by
  ext k; rw [sigma_coeff, one_pow, one_mul]

theorem sigma_one_hom : sigma (1 : R) = RingHom.id R[X] :=
  RingHom.ext sigma_one

/-- `σ_A^ℓ = σ_{A^ℓ}` (the iterates of the rotation are rotations). -/
theorem sigma_pow (A : R) (ℓ : ℕ) : sigma A ^ ℓ = sigma (A ^ ℓ) := by
  induction ℓ with
  | zero => rw [pow_zero, pow_zero, RingHom.one_def, sigma_one_hom]
  | succ ℓ ih =>
      refine RingHom.ext fun p => ?_
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, sigma_sigma, ← pow_succ]

/-- (Lemma "Scalar rotation is a diagonal automorphism".)  `A^r = 1` ⟹ `σ_A^r = id`. -/
theorem sigma_pow_eq_one {A : R} {r : ℕ} (hAr : A ^ r = 1) : sigma A ^ r = 1 := by
  rw [sigma_pow, hAr, sigma_one_hom, RingHom.one_def]

/-- For a unit `A` with inverse `B`, `σ_B` inverts `σ_A`. -/
theorem sigma_inv_sigma {A B : R} (h : B * A = 1) (p : R[X]) :
    sigma B (sigma A p) = p := by
  rw [sigma_sigma, h, sigma_one]

/-! ## 2. Commutation with the coefficientwise action (part (a)) -/

/-- (Lemma "The scalar and Galois actions commute", part (a).)  If `φ` fixes the
    radix `A`, the coefficientwise action commutes with the scalar rotation:
    `map φ (σ_A p) = σ_A (map φ p)`. -/
theorem map_sigma (φ : R →+* R) {A : R} (hφA : φ A = A) (p : R[X]) :
    (sigma A p).map φ = sigma A (p.map φ) := by
  ext k
  rw [coeff_map, sigma_coeff, sigma_coeff, coeff_map, map_mul, map_pow, hφA]

/-- The same statement for the ring homomorphisms: `mapRingHom φ ∘ σ_A = σ_A ∘ mapRingHom φ`. -/
theorem mapRingHom_comp_sigma (φ : R →+* R) {A : R} (hφA : φ A = A) :
    (mapRingHom φ).comp (sigma A) = (sigma A).comp (mapRingHom φ) := by
  refine RingHom.ext fun p => ?_
  exact map_sigma φ hφA p

/-! ## 3. The vanishing polynomial `G_S` and the descent to `V = R[X]/(G_S)` (part (b)) -/

/-- The vanishing polynomial `G_S = ∏_{a ∈ S} (X − a)` of the support. -/
noncomputable def G (S : Finset R) : R[X] := ∏ a ∈ S, (X - C a)

/-- If `φ` fixes every support point, `map φ G_S = G_S`; hence `Frob` descends to `V`. -/
theorem map_G (φ : R →+* R) {S : Finset R} (hS : ∀ a ∈ S, φ a = a) :
    (G S).map φ = G S := by
  unfold G
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro a ha
  rw [Polynomial.map_sub, map_X, map_C, hS a ha]

/-- `A`-stability of the support: if `A·S = S` and `A` is a unit, then
    `G_S(AX) = A^{|S|} · G_S(X)`; hence `σ_A` descends to `V`. -/
theorem sigma_G [DecidableEq R] {A : R} (hA : IsUnit A) {S : Finset R} (hS : S.image (fun a => A * a) = S) :
    sigma A (G S) = C (A ^ S.card) * G S := by
  classical
  unfold G
  rw [map_prod]
  have hinj : ∀ x ∈ S, ∀ y ∈ S, A * x = A * y → x = y :=
    fun x _ y _ hxy => hA.mul_right_injective hxy
  calc ∏ a ∈ S, sigma A (X - C a)
      = ∏ a ∈ S.image (fun a => A * a), sigma A (X - C a) := by rw [hS]
    _ = ∏ a ∈ S, sigma A (X - C (A * a)) := Finset.prod_image hinj
    _ = ∏ a ∈ S, C A * (X - C a) := by
        apply Finset.prod_congr rfl
        intro a _
        rw [map_sub, sigma_X, sigma_C, C_mul]; ring
    _ = C (A ^ S.card) * ∏ a ∈ S, (X - C a) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, C_pow]

/-- `σ_A` preserves the ideal `(G_S)`: `G_S ∣ p ⟹ G_S ∣ σ_A p`. -/
theorem dvd_sigma_of_dvd [DecidableEq R] {A : R} (hA : IsUnit A) {S : Finset R}
    (hS : S.image (fun a => A * a) = S) {p : R[X]} (h : G S ∣ p) : G S ∣ sigma A p := by
  obtain ⟨H, rfl⟩ := h
  rw [map_mul, sigma_G hA hS]
  exact ⟨C (A ^ S.card) * sigma A H, by ring⟩

/-- `map φ` preserves the ideal `(G_S)`: `G_S ∣ p ⟹ G_S ∣ map φ p`. -/
theorem dvd_map_of_dvd (φ : R →+* R) {S : Finset R} (hS : ∀ a ∈ S, φ a = a) {p : R[X]}
    (h : G S ∣ p) : G S ∣ p.map φ := by
  have := map_dvd (mapRingHom φ) h
  rwa [coe_mapRingHom, map_G φ hS] at this

/-- Ideal form: `σ_A ((G_S)) ⊆ (G_S)`. -/
theorem span_G_map_sigma_le [DecidableEq R] {A : R} (hA : IsUnit A) {S : Finset R}
    (hS : S.image (fun a => A * a) = S) :
    (Ideal.span {G S}).map (sigma A) ≤ Ideal.span {G S} := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff,
    SetLike.mem_coe, Ideal.mem_span_singleton]
  exact dvd_sigma_of_dvd hA hS dvd_rfl

/-- Ideal form: `(map φ)((G_S)) ⊆ (G_S)`. -/
theorem span_G_map_le (φ : R →+* R) {S : Finset R} (hS : ∀ a ∈ S, φ a = a) :
    (Ideal.span {G S}).map (mapRingHom φ) ≤ Ideal.span {G S} := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff,
    SetLike.mem_coe, Ideal.mem_span_singleton, coe_mapRingHom]
  exact dvd_map_of_dvd φ hS dvd_rfl

/-! ## 4. The direct product `⟨σ_A, Frob⟩ ≅ C_r × C_d` -/

/-- (Lemma "commute", direct product.)  If `σ_{A^a} = map (φ^b)` as maps on `R[X]`,
    then `A^a = 1` (evaluate on `X`) and `φ^b = 1` (evaluate on constants). -/
theorem direct_product (φ : R →+* R) {A : R} {a b : ℕ}
    (h : ∀ p : R[X], sigma (A ^ a) p = p.map (φ ^ b)) : A ^ a = 1 ∧ φ ^ b = 1 := by
  refine ⟨?_, ?_⟩
  · have hX := congrArg (fun q : R[X] => q.coeff 1) (h X)
    simp only [sigma_coeff, coeff_X_one, map_X] at hX
    simpa using hX
  · ext c
    have hc := h (C c)
    rw [sigma_C, map_C] at hc
    exact (C_inj.mp hc).symm

/-- The same at the level of ring homomorphisms: `σ_A^a = (mapRingHom φ)^b` forces
    `A^a = 1` and `φ^b = 1`; so `⟨σ_A⟩ ∩ ⟨Frob⟩` is trivial and the two cyclic
    groups generate their direct product. -/
theorem direct_product_hom (φ : R →+* R) {A : R} {a b : ℕ}
    (h : sigma A ^ a = mapRingHom φ ^ b) : A ^ a = 1 ∧ φ ^ b = 1 := by
  apply direct_product φ
  intro p
  have := congrArg (fun f : R[X] →+* R[X] => f p) h
  simpa only [sigma_pow, Galois.mapRingHom_pow, coe_mapRingHom] using this

end Ring

/-! ## 5. Proposition "Bigraded decomposition": the character idempotents -/
section Field
variable {K : Type*} [Field K]

/-- The geometric sum of an `r`-th root of unity: `Σ_{ℓ<r} ωˡ = r` if `ω = 1`, else `0`. -/
theorem geom_sum_root [DecidableEq K] {ω : K} {r : ℕ} (hω : ω ^ r = 1) :
    ∑ ℓ ∈ range r, ω ^ ℓ = if ω = 1 then (r : K) else 0 := by
  split_ifs with h1
  · subst h1; simp
  · rw [geom_sum_eq h1, hω, sub_self, zero_div]

/-- The character idempotent `π_j = (1/r) Σ_{ℓ<r} A^{−jℓ} σ_A^ℓ` (with `A^{−1}` the field
    inverse and `σ_A^ℓ = σ_{A^ℓ}`). -/
noncomputable def pi (A : K) (r j : ℕ) (p : K[X]) : K[X] :=
  C ((r : K)⁻¹) * ∑ ℓ ∈ range r, C (A⁻¹ ^ (j * ℓ)) * sigma (A ^ ℓ) p

/-- `π_j` is additive. -/
theorem pi_add (A : K) (r j : ℕ) (p q : K[X]) : pi A r j (p + q) = pi A r j p + pi A r j q := by
  simp only [pi, map_add, mul_add, Finset.sum_add_distrib]

/-- Coefficient formula: `(π_j p).coeff k = (1/r)(Σ_ℓ (A^k A^{−j})^ℓ) · p.coeff k`. -/
theorem pi_coeff_geom (A : K) (r j : ℕ) (p : K[X]) (k : ℕ) :
    (pi A r j p).coeff k = (r : K)⁻¹ * (∑ ℓ ∈ range r, (A ^ k * A⁻¹ ^ j) ^ ℓ) * p.coeff k := by
  unfold pi
  rw [coeff_C_mul, finsetSum_coeff, mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [coeff_C_mul, sigma_coeff, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm j ℓ,
    mul_comm ℓ k]
  ring

/-- (Proposition "Bigraded decomposition", coefficient form.)  For `A` of exact order
    `r` with `r ≠ 0` in `K`: `(π_j p).coeff k = p.coeff k` if `Aᵏ = Aʲ` and `0` otherwise.
    So `π_j` keeps exactly the monomials `X^k` with `k ≡ j (mod r)`. -/
theorem pi_coeff [DecidableEq K] {A : K} {r : ℕ} (hAr : A ^ r = 1) (hr : 1 ≤ r) (hrK : (r : K) ≠ 0)
    (j : ℕ) (p : K[X]) (k : ℕ) :
    (pi A r j p).coeff k = if A ^ k = A ^ j then p.coeff k else 0 := by
  have hA0 : A ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hAr; exact zero_ne_one hAr
  have hω : (A ^ k * A⁻¹ ^ j) ^ r = 1 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k r, mul_comm j r, pow_mul, pow_mul, hAr,
      inv_pow, hAr, inv_one, one_pow, one_pow, mul_one]
  rw [pi_coeff_geom, geom_sum_root hω]
  have hiff : A ^ k * A⁻¹ ^ j = 1 ↔ A ^ k = A ^ j := by
    rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hA0)]
  by_cases h : A ^ k = A ^ j
  · rw [if_pos (hiff.mpr h), if_pos h, inv_mul_cancel₀ hrK, one_mul]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero, zero_mul]

/-- `π_j (V)` lies in the `A^j`-eigenspace of `σ_A`: `σ_A (π_j p) = A^j · π_j p`. -/
theorem sigma_pi [DecidableEq K] {A : K} {r : ℕ} (hAr : A ^ r = 1) (hr : 1 ≤ r) (hrK : (r : K) ≠ 0)
    (j : ℕ) (p : K[X]) : sigma A (pi A r j p) = C (A ^ j) * pi A r j p := by
  ext k
  rw [sigma_coeff, coeff_C_mul, pi_coeff hAr hr hrK]
  split_ifs with h
  · rw [h]
  · simp

/-- Exact order `r`: `Aᵏ = Aʲ ↔ k ≡ j (mod r)`. -/
theorem pow_eq_pow_iff {A : K} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (k j : ℕ) :
    A ^ k = A ^ j ↔ k % r = j % r := by
  have horder : orderOf A = r :=
    (orderOf_eq_iff (by omega)).mpr ⟨hAr, fun m hm hm0 => hord m hm0 hm⟩
  have hfin : IsOfFinOrder A := isOfFinOrder_iff_pow_eq_one.mpr ⟨r, by omega, hAr⟩
  rw [hfin.pow_inj_mod, horder]

/-- `Σ_{j<r} π_j = id` (the idempotents resolve the identity). -/
theorem sum_pi [DecidableEq K] {A : K} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (hrK : (r : K) ≠ 0)
    (p : K[X]) : ∑ j ∈ range r, pi A r j p = p := by
  ext k
  rw [finsetSum_coeff]
  simp only [pi_coeff hAr hr hrK]
  have hcongr : ∀ j ∈ range r, (if A ^ k = A ^ j then p.coeff k else 0) =
      if k % r = j then p.coeff k else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [pow_eq_pow_iff hAr hord hr, Nat.mod_eq_of_lt hj]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))]

/-- `π_j ∘ π_{j'} = [j = j'] π_j` for `j, j' < r` (orthogonal idempotents). -/
theorem pi_pi [DecidableEq K] {A : K} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (hrK : (r : K) ≠ 0)
    {j j' : ℕ} (hj : j < r) (hj' : j' < r) (p : K[X]) :
    pi A r j (pi A r j' p) = if j = j' then pi A r j p else 0 := by
  by_cases hjj : j = j'
  · subst hjj
    rw [if_pos rfl]
    ext k
    rw [pi_coeff hAr hr hrK, pi_coeff hAr hr hrK]
    by_cases h : A ^ k = A ^ j <;> simp [h]
  · rw [if_neg hjj]
    ext k
    rw [pi_coeff hAr hr hrK, pi_coeff hAr hr hrK, coeff_zero]
    by_cases h1 : A ^ k = A ^ j
    · by_cases h2 : A ^ k = A ^ j'
      · exfalso
        apply hjj
        have := (pow_eq_pow_iff hAr hord hr j j').mp (h1.symm.trans h2)
        rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at this
      · rw [if_pos h1, if_neg h2]
    · rw [if_neg h1]

/-- `π_j` commutes with the coefficientwise action of any `φ` fixing `A`
    (no order hypothesis needed): `map φ (π_j p) = π_j (map φ p)`. -/
theorem map_pi (φ : K →+* K) {A : K} (hφA : φ A = A) (r j : ℕ) (p : K[X]) :
    (pi A r j p).map φ = pi A r j (p.map φ) := by
  unfold pi
  rw [Polynomial.map_mul, map_C, Polynomial.map_sum, map_inv₀, map_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [Polynomial.map_mul, map_C, map_pow, map_inv₀, hφA, map_sigma φ (by rw [map_pow, hφA])]

/-- Every isotypic component `V_j = π_j(V)` is `Frob`-stable: the image of `π_j` is
    mapped into itself by `map φ`. -/
theorem map_mem_range_pi (φ : K →+* K) {A : K} (hφA : φ A = A) (r j : ℕ) (q : K[X])
    (hq : ∃ p, q = pi A r j p) : ∃ p, q.map φ = pi A r j p := by
  obtain ⟨p, rfl⟩ := hq
  exact ⟨p.map φ, map_pi φ hφA r j p⟩

/-- `X^k ∈ V_{k mod r}`: `π_j X^k = X^k` if `k ≡ j (mod r)`, else `0`. -/
theorem pi_X_pow [DecidableEq K] {A : K} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (hrK : (r : K) ≠ 0)
    (j k : ℕ) : pi A r j (X ^ k) = if k % r = j % r then X ^ k else 0 := by
  ext n
  rw [pi_coeff hAr hr hrK, coeff_X_pow, apply_ite (fun q : K[X] => q.coeff n), coeff_zero,
    coeff_X_pow]
  by_cases hn : n = k
  · subst hn
    have := pow_eq_pow_iff hAr hord hr n j
    by_cases h : A ^ n = A ^ j
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]
  · simp [hn]

end Field

end GaloisCommute

