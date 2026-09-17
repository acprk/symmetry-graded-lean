/-
  Isotypic.lean

  Formal verification (Lean 4 + Mathlib) of

    Theorem "Isotypic decomposition"      (Section "Preliminaries")
    Proposition "Bigraded decomposition"  (Appendix B.2)

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping",
  at the level of the quotient `V = K[X]/(G_S)` itself.  `Commute.lean` carries
  the idempotent calculus `π_j = (1/r) Σ_ℓ A^{−jℓ} σ_A^ℓ` on `K[X]`; this file
  descends it to `V = AdjoinRoot G_S`, where `G_S = ∏_{s ∈ S}(X − s)`, and
  assembles the direct-sum decomposition.  With no unproved placeholders:

  * `natCast_ne_zero_of_exact_order`
        `char K ∤ r` from the order hypothesis alone: an `A ∈ K` of exact order
        `r ≥ 1` forces `(r : K) ≠ 0`.  In characteristic `p ∣ r` the `p`-th power
        map is injective, so `A^{r/p} = 1` already.
  * `sum_pi'`, `pi_pi'`, `sigma_pi'`, `pi_coeff'`, `pi_X_pow'`
        the `Commute.lean` idempotent identities with the hypothesis `(r : K) ≠ 0`
        discharged by `natCast_ne_zero_of_exact_order`.
  * `monic_G`, `natDegree_G`
        `G_S` is monic of degree `|S|`, so `V = K[X]/(G_S)` is `|S|`-dimensional.
  * `sigmaQ`, `sigmaQ_mk`, `sigmaL`, `sigmaL_pow_mk`
        the scalar rotation descends to `V`: `A·S = S` makes `σ_A` preserve the
        ideal `(G_S)`, and the descended map is `K`-linear.
  * `piQ`, `piQ_mk`, `sum_piQ`, `piQ_piQ`
        the descended character idempotents, resolving the identity on `V` and
        orthogonal.
  * `Vcomp`, `mem_Vcomp_iff`, `sigmaL_apply_of_mem_Vcomp`, `piQ_apply_sum`,
    `piQ_eq_self_of_sigmaL_eq`, `mem_Vcomp_iff_eigen`, `root_pow_mem_Vcomp`
        the isotypic components `V_j = π_j(V)`; `V_j` is exactly the `A^j`-eigenspace
        `{f ∈ V : σ_A(f) = A^j f}` of the descended `σ_A`, and `X^k ∈ V_{k mod r}`.
  * `map_piQ_of_commute`, `Vcomp_stable_of_commute`
        (Proposition "Bigraded decomposition", stability half)  an additive endomorphism
        of `V` that commutes with `σ_A` and with multiplication by the coefficients
        `A^{-jℓ}/r` of `π_j` commutes with `π_j` and preserves every `V_j`.  These are the
        two properties the paper uses of the coefficientwise Frobenius; the Frobenius
        itself is not constructed here, as Mathlib has no Galois rings, so the base ring
        is a field `K` and the stability is stated for an abstract such endomorphism.
  * `iSup_Vcomp`, `iSupIndep_Vcomp`, `isInternal_Vcomp`
        `V = ⊕_{j<r} V_j` as an internal direct sum of `K`-submodules.
  * `card_filter_mod_eq`
        the count `#{k < N : k ≡ j (mod r)} = ⌈(N − j)/r⌉`, written
        `(N + r − 1 − j)/r` in natural-number division.
  * `finrank_span_basis_image`, `piQ_root_pow`, `Vcomp_eq_span`, `finrank_Vcomp`
        `V_j` is the span of the monomials `X^k`, `k < |S|`, `k ≡ j (mod r)`, and
        `dim V_j = ⌈(|S| − j)/r⌉`.
-/
import Mathlib
import SymmetryGraded.Commute

namespace Isotypic

open Polynomial Finset

/-! ## 1. `char K ∤ r` from the exact-order hypothesis -/
section Char
variable {K : Type*} [Field K]

/-- An element of exact order `r ≥ 1` forces `char K ∤ r`, i.e. `(r : K) ≠ 0`.
    If `p = char K` divided `r`, then `(A^{r/p} − 1)^p = A^r − 1 = 0`, so already
    `A^{r/p} = 1` with `0 < r/p < r`. -/
theorem natCast_ne_zero_of_exact_order {A : K} {r : ℕ} (hr : 1 ≤ r) (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) : (r : K) ≠ 0 := by
  intro hrK
  have hdvd : ringChar K ∣ r := ringChar.dvd hrK
  rcases Nat.eq_zero_or_pos (ringChar K) with hp0 | hppos
  · rw [hp0] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by omega)
  · haveI hchar : CharP K (ringChar K) := ringChar.charP K
    haveI hnz : NeZero (ringChar K) := ⟨by omega⟩
    haveI hprime : Fact (Nat.Prime (ringChar K)) := CharP.char_is_prime_of_pos K (ringChar K)
    obtain ⟨m, hm⟩ := hdvd
    have hp2 : 2 ≤ ringChar K := hprime.out.two_le
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm; omega
      · exact h
    have hmr : m < r := by nlinarith [hm]
    refine hord m hm0 hmr ?_
    have hpow : (A ^ m - 1) ^ ringChar K = 0 := by
      rw [sub_pow_char, ← pow_mul, mul_comm m (ringChar K), ← hm, hAr, one_pow, sub_self]
    have h0 : A ^ m - 1 = 0 := by
      by_contra hne0
      exact pow_ne_zero (ringChar K) hne0 hpow
    linear_combination h0

end Char

/-! ## 2. The idempotent calculus with the characteristic hypothesis discharged -/
section Idempotents
variable {K : Type*} [Field K] [DecidableEq K] {A : K} {r : ℕ}

/-- `Σ_{j<r} π_j = id` for `A` of exact order `r`, with no hypothesis on `char K`. -/
theorem sum_pi' (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    (p : K[X]) : ∑ j ∈ range r, GaloisCommute.pi A r j p = p :=
  GaloisCommute.sum_pi hAr hord hr (natCast_ne_zero_of_exact_order hr hAr hord) p

/-- `π_j ∘ π_{j'} = [j = j'] π_j`, with no hypothesis on `char K`. -/
theorem pi_pi' (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    {j j' : ℕ} (hj : j < r) (hj' : j' < r) (p : K[X]) :
    GaloisCommute.pi A r j (GaloisCommute.pi A r j' p) =
      if j = j' then GaloisCommute.pi A r j p else 0 :=
  GaloisCommute.pi_pi hAr hord hr (natCast_ne_zero_of_exact_order hr hAr hord) hj hj' p

/-- `σ_A ∘ π_j = A^j · π_j`, with no hypothesis on `char K`. -/
theorem sigma_pi' (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    (j : ℕ) (p : K[X]) :
    GaloisCommute.sigma A (GaloisCommute.pi A r j p) =
      C (A ^ j) * GaloisCommute.pi A r j p :=
  GaloisCommute.sigma_pi hAr hr (natCast_ne_zero_of_exact_order hr hAr hord) j p

/-- `π_j` keeps exactly the monomials of degree `≡ j (mod r)`, with no hypothesis
    on `char K`. -/
theorem pi_coeff' (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    (j : ℕ) (p : K[X]) (k : ℕ) :
    (GaloisCommute.pi A r j p).coeff k = if A ^ k = A ^ j then p.coeff k else 0 :=
  GaloisCommute.pi_coeff hAr hr (natCast_ne_zero_of_exact_order hr hAr hord) j p k

/-- `X^k ∈ V_{k mod r}` at the level of `K[X]`, with no hypothesis on `char K`. -/
theorem pi_X_pow' (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    (j k : ℕ) :
    GaloisCommute.pi A r j ((X : K[X]) ^ k) = if k % r = j % r then X ^ k else 0 :=
  GaloisCommute.pi_X_pow hAr hord hr (natCast_ne_zero_of_exact_order hr hAr hord) j k

end Idempotents

/-! ## 3. The vanishing polynomial and the quotient `V = K[X]/(G_S)` -/
section Quotient
variable {K : Type*} [Field K]

/-- `G_S = ∏_{s ∈ S}(X − s)` is monic. -/
theorem monic_G (S : Finset K) : (GaloisCommute.G S).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a

/-- `G_S` has degree `|S|`, so `V = K[X]/(G_S)` is `|S|`-dimensional. -/
theorem natDegree_G (S : Finset K) : (GaloisCommute.G S).natDegree = S.card := by
  unfold GaloisCommute.G
  rw [natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C a]
  simp

/-- The scalar rotation `σ_A` is `K`-linear on `K[X]`. -/
theorem sigma_smul (A c : K) (p : K[X]) :
    GaloisCommute.sigma A (c • p) = c • GaloisCommute.sigma A p := by
  ext k
  rw [GaloisCommute.sigma_coeff, coeff_smul, coeff_smul, GaloisCommute.sigma_coeff,
    smul_eq_mul, smul_eq_mul]
  ring

variable [DecidableEq K] {A : K} {S : Finset K}

/-- The scalar rotation descends to the quotient `V = K[X]/(G_S)` whenever the
    support is `A`-stable: `σ_A` then preserves the ideal `(G_S)`. -/
noncomputable def sigmaQ (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) :
    AdjoinRoot (GaloisCommute.G S) →+* AdjoinRoot (GaloisCommute.G S) :=
  Ideal.Quotient.lift (Ideal.span {GaloisCommute.G S})
    ((AdjoinRoot.mk (GaloisCommute.G S)).comp (GaloisCommute.sigma A)) (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      rw [RingHom.comp_apply, AdjoinRoot.mk_eq_zero]
      exact GaloisCommute.dvd_sigma_of_dvd hA hS ha)

/-- The descended rotation acts on classes by the rotation of representatives. -/
theorem sigmaQ_mk (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) (p : K[X]) :
    sigmaQ hA hS (AdjoinRoot.mk (GaloisCommute.G S) p) =
      AdjoinRoot.mk (GaloisCommute.G S) (GaloisCommute.sigma A p) := rfl

/-- The descended rotation as a `K`-linear endomorphism of `V`. -/
noncomputable def sigmaL (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) :
    AdjoinRoot (GaloisCommute.G S) →ₗ[K] AdjoinRoot (GaloisCommute.G S) where
  toFun := sigmaQ hA hS
  map_add' x y := map_add _ x y
  map_smul' c v := by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective v
    simp only [RingHom.id_apply, AdjoinRoot.smul_mk, sigmaQ_mk, sigma_smul]

theorem sigmaL_mk (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) (p : K[X]) :
    sigmaL hA hS (AdjoinRoot.mk (GaloisCommute.G S) p) =
      AdjoinRoot.mk (GaloisCommute.G S) (GaloisCommute.sigma A p) := rfl

/-- The `ℓ`-th power of the descended rotation is the descent of `σ_{A^ℓ}`. -/
theorem sigmaL_pow_mk (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) (ℓ : ℕ) (p : K[X]) :
    (sigmaL hA hS ^ ℓ) (AdjoinRoot.mk (GaloisCommute.G S) p) =
      AdjoinRoot.mk (GaloisCommute.G S) (GaloisCommute.sigma (A ^ ℓ) p) := by
  induction ℓ generalizing p with
  | zero => simp [GaloisCommute.sigma_one]
  | succ ℓ ih =>
      have hstep : (sigmaL hA hS ^ (ℓ + 1)) (AdjoinRoot.mk (GaloisCommute.G S) p)
          = (sigmaL hA hS ^ ℓ) (sigmaL hA hS (AdjoinRoot.mk (GaloisCommute.G S) p)) := by
        rw [pow_succ, Module.End.mul_apply]
      rw [hstep, sigmaL_mk, ih, GaloisCommute.sigma_sigma, ← pow_succ]

/-- The descended character idempotent `π_j : V → V`. -/
noncomputable def piQ (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) (r j : ℕ) :
    AdjoinRoot (GaloisCommute.G S) →ₗ[K] AdjoinRoot (GaloisCommute.G S) :=
  (r : K)⁻¹ • ∑ ℓ ∈ range r, (A⁻¹ ^ (j * ℓ)) • (sigmaL hA hS ^ ℓ)

/-- The descended idempotent acts on classes by the idempotent of representatives. -/
theorem piQ_mk (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) (r j : ℕ) (p : K[X]) :
    piQ hA hS r j (AdjoinRoot.mk (GaloisCommute.G S) p) =
      AdjoinRoot.mk (GaloisCommute.G S) (GaloisCommute.pi A r j p) := by
  have hpi : GaloisCommute.pi A r j p =
      C ((r : K)⁻¹) * ∑ ℓ ∈ range r, C (A⁻¹ ^ (j * ℓ)) * GaloisCommute.sigma (A ^ ℓ) p := rfl
  have hpiQ : piQ hA hS r j =
      (r : K)⁻¹ • ∑ ℓ ∈ range r, (A⁻¹ ^ (j * ℓ)) • (sigmaL hA hS ^ ℓ) := rfl
  rw [hpi, ← smul_eq_C_mul, ← AdjoinRoot.smul_mk, map_sum, hpiQ, LinearMap.smul_apply,
    LinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [LinearMap.smul_apply, sigmaL_pow_mk, ← smul_eq_C_mul, ← AdjoinRoot.smul_mk]

/-- The descended idempotents resolve the identity: `Σ_{j<r} π_j = id` on `V`. -/
theorem sum_piQ (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) :
    ∑ j ∈ range r, piQ hA hS r j = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective v
  rw [LinearMap.sum_apply]
  simp only [piQ_mk, LinearMap.id_coe, id_eq]
  rw [← map_sum, sum_pi' hAr hord hr]

/-- The descended idempotents are orthogonal: `π_j ∘ π_{j'} = [j = j'] π_j`. -/
theorem piQ_piQ (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    {j j' : ℕ} (hj : j < r) (hj' : j' < r) (v : AdjoinRoot (GaloisCommute.G S)) :
    piQ hA hS r j (piQ hA hS r j' v) = if j = j' then piQ hA hS r j v else 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective v
  rw [piQ_mk, piQ_mk, piQ_mk, pi_pi' hAr hord hr hj hj']
  split_ifs with h
  · rfl
  · exact map_zero _

/-! ## 4. The isotypic components of `V` -/

/-- The isotypic component `V_j = π_j(V)` of the quotient `V = K[X]/(G_S)`. -/
noncomputable def Vcomp (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) (r j : ℕ) :
    Submodule K (AdjoinRoot (GaloisCommute.G S)) := LinearMap.range (piQ hA hS r j)

theorem mem_Vcomp (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) (r j : ℕ)
    (v : AdjoinRoot (GaloisCommute.G S)) :
    v ∈ Vcomp hA hS r j ↔ ∃ w, piQ hA hS r j w = v := Iff.rfl

/-- `V_j` is exactly the fixed set of `π_j`. -/
theorem mem_Vcomp_iff (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    {j : ℕ} (hj : j < r) (v : AdjoinRoot (GaloisCommute.G S)) :
    v ∈ Vcomp hA hS r j ↔ piQ hA hS r j v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [piQ_piQ hA hS hAr hord hr hj hj, if_pos rfl]
  · intro h
    exact ⟨v, h⟩

/-- `V_j` is contained in the `A^j`-eigenspace of the descended rotation. -/
theorem sigmaL_apply_of_mem_Vcomp (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (j : ℕ)
    {v : AdjoinRoot (GaloisCommute.G S)} (hv : v ∈ Vcomp hA hS r j) :
    sigmaL hA hS v = (A ^ j) • v := by
  obtain ⟨w, rfl⟩ := hv
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective w
  rw [piQ_mk, sigmaL_mk, sigma_pi' hAr hord hr, ← smul_eq_C_mul, ← AdjoinRoot.smul_mk]

/-- The descended idempotent written as a single sum, with the normalising factor `1/r`
    pulled into the coefficients `A^{-jℓ}/r`. -/
theorem piQ_apply_sum (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) (r j : ℕ)
    (v : AdjoinRoot (GaloisCommute.G S)) :
    piQ hA hS r j v =
      ∑ ℓ ∈ range r, ((r : K)⁻¹ * A⁻¹ ^ (j * ℓ)) • (sigmaL hA hS ^ ℓ) v := by
  show ((r : K)⁻¹ • ∑ ℓ ∈ range r, (A⁻¹ ^ (j * ℓ)) • (sigmaL hA hS ^ ℓ)) v = _
  rw [LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [LinearMap.smul_apply, smul_smul]

/-- An `A^j`-eigenvector of the descended rotation is fixed by `π_j`. -/
theorem piQ_eq_self_of_sigmaL_eq (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (j : ℕ)
    {v : AdjoinRoot (GaloisCommute.G S)} (hv : sigmaL hA hS v = (A ^ j) • v) :
    piQ hA hS r j v = v := by
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : r ≠ 0)] at hAr
    exact zero_ne_one hAr
  have hrK : (r : K) ≠ 0 := natCast_ne_zero_of_exact_order hr hAr hord
  have hpow : ∀ ℓ : ℕ, (sigmaL hA hS ^ ℓ) v = ((A ^ j) ^ ℓ) • v := by
    intro ℓ
    induction ℓ with
    | zero => simp
    | succ ℓ ih =>
        have hstep : (sigmaL hA hS ^ (ℓ + 1)) v = (sigmaL hA hS ^ ℓ) (sigmaL hA hS v) := by
          rw [pow_succ, Module.End.mul_apply]
        rw [hstep, hv, map_smul, ih, smul_smul, ← pow_succ']
  have hterm : ∀ ℓ ∈ range r,
      ((r : K)⁻¹ * A⁻¹ ^ (j * ℓ)) • (sigmaL hA hS ^ ℓ) v = (r : K)⁻¹ • v := by
    intro ℓ _
    rw [hpow ℓ, smul_smul, mul_assoc, ← pow_mul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hA0), mul_one]
  rw [piQ_apply_sum, Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hrK, one_smul]

/-- (Theorem "Isotypic decomposition", eigenspace form.)  `V_j` is exactly the
    `A^j`-eigenspace `{f ∈ V : σ_A(f) = A^j f}` of the descended rotation. -/
theorem mem_Vcomp_iff_eigen (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (j : ℕ)
    (v : AdjoinRoot (GaloisCommute.G S)) :
    v ∈ Vcomp hA hS r j ↔ sigmaL hA hS v = (A ^ j) • v := by
  constructor
  · exact sigmaL_apply_of_mem_Vcomp hA hS hAr hord hr j
  · intro hv
    exact ⟨v, piQ_eq_self_of_sigmaL_eq hA hS hAr hord hr j hv⟩

/-- An additive endomorphism that commutes with `σ_A` and with multiplication by the
    coefficients `A^{-jℓ}/r` of `π_j` commutes with `π_j`.  In the setting of the paper the
    base ring is `ℤ/p^e` and the endomorphism is the coefficientwise Frobenius, which
    commutes with `σ_A` and fixes those coefficients because they lie in the base ring. -/
theorem map_piQ_of_commute (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r j : ℕ}
    (F : AdjoinRoot (GaloisCommute.G S) →+ AdjoinRoot (GaloisCommute.G S))
    (hcomm : ∀ w, F (sigmaL hA hS w) = sigmaL hA hS (F w))
    (hsmul : ∀ (ℓ : ℕ) (w), F (((r : K)⁻¹ * A⁻¹ ^ (j * ℓ)) • w)
      = ((r : K)⁻¹ * A⁻¹ ^ (j * ℓ)) • F w)
    (v : AdjoinRoot (GaloisCommute.G S)) :
    F (piQ hA hS r j v) = piQ hA hS r j (F v) := by
  have hpow : ∀ (ℓ : ℕ) (w), F ((sigmaL hA hS ^ ℓ) w) = (sigmaL hA hS ^ ℓ) (F w) := by
    intro ℓ
    induction ℓ with
    | zero => intro w; simp
    | succ ℓ ih =>
        intro w
        rw [pow_succ, Module.End.mul_apply, ih, hcomm, Module.End.mul_apply]
  rw [piQ_apply_sum, piQ_apply_sum, map_sum]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [hsmul, hpow]

/-- (Proposition "Bigraded decomposition", stability half.)  Each isotypic component `V_j`
    is stable under an additive endomorphism commuting with `σ_A` and with the coefficients
    of `π_j`; for the coefficientwise Frobenius this is `Frob(V_j) ⊆ V_j`. -/
theorem Vcomp_stable_of_commute (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r j : ℕ}
    (F : AdjoinRoot (GaloisCommute.G S) →+ AdjoinRoot (GaloisCommute.G S))
    (hcomm : ∀ w, F (sigmaL hA hS w) = sigmaL hA hS (F w))
    (hsmul : ∀ (ℓ : ℕ) (w), F (((r : K)⁻¹ * A⁻¹ ^ (j * ℓ)) • w)
      = ((r : K)⁻¹ * A⁻¹ ^ (j * ℓ)) • F w)
    {v : AdjoinRoot (GaloisCommute.G S)} (hv : v ∈ Vcomp hA hS r j) :
    F v ∈ Vcomp hA hS r j := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨F w, (map_piQ_of_commute hA hS F hcomm hsmul w).symm⟩

/-- `X^k` lies in the component `V_{k mod r}`. -/
theorem root_pow_mem_Vcomp (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (k : ℕ) :
    (AdjoinRoot.root (GaloisCommute.G S)) ^ k ∈ Vcomp hA hS r (k % r) := by
  refine ⟨AdjoinRoot.mk (GaloisCommute.G S) (X ^ k), ?_⟩
  have hmm : k % r = k % r % r := (Nat.mod_mod_of_dvd k dvd_rfl).symm
  rw [piQ_mk, pi_X_pow' hAr hord hr, if_pos hmm, map_pow, AdjoinRoot.mk_X]

/-- `V = Σ_{j<r} V_j`. -/
theorem iSup_Vcomp (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) :
    (⨆ j : Fin r, Vcomp hA hS r (j : ℕ)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : ∑ j : Fin r, piQ hA hS r (j : ℕ) v = v := by
    rw [Fin.sum_univ_eq_sum_range (fun j => piQ hA hS r j v) r, ← LinearMap.sum_apply,
      sum_piQ hA hS hAr hord hr, LinearMap.id_coe, id_eq]
  rw [← hv]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ v)

/-- The components `V_j` are independent. -/
theorem iSupIndep_Vcomp (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) :
    iSupIndep (fun j : Fin r => Vcomp hA hS r (j : ℕ)) := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hxi hxsup
  have hker : (⨆ (j : Fin r) (_ : j ≠ i), Vcomp hA hS r (j : ℕ))
      ≤ LinearMap.ker (piQ hA hS r (i : ℕ)) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    rintro y ⟨z, rfl⟩
    have hij : (i : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
    simp only [LinearMap.mem_ker]
    rw [piQ_piQ hA hS hAr hord hr i.isLt j.isLt, if_neg hij]
  have h1 : piQ hA hS r (i : ℕ) x = 0 := hker hxsup
  have h2 : piQ hA hS r (i : ℕ) x = x :=
    (mem_Vcomp_iff hA hS hAr hord hr i.isLt x).mp hxi
  rw [← h2, h1]

/-- (Theorem "Isotypic decomposition".)  `V = ⊕_{j<r} V_j` as an internal direct sum
    of `K`-submodules of `V = K[X]/(G_S)`. -/
theorem isInternal_Vcomp (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) :
    DirectSum.IsInternal (fun j : Fin r => Vcomp hA hS r (j : ℕ)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_Vcomp hA hS hAr hord hr) (iSup_Vcomp hA hS hAr hord hr)

end Quotient

/-! ## 5. The dimension count -/
section Counting

/-- The number of exponents `k < N` in a fixed residue class `j` modulo `r` is
    `⌈(N − j)/r⌉`, written `(N + r − 1 − j)/r` in natural-number division.  This is
    the dimension `dim V_j` of the isotypic component, `V_j` being spanned by the
    monomials `X^k`, `k < N = |S|`, `k ≡ j (mod r)`. -/
theorem card_filter_mod_eq (N r j : ℕ) (hr : 0 < r) (hj : j < r) :
    ((range N).filter (fun k => k % r = j)).card = (N + r - 1 - j) / r := by
  have hkey : ∀ i : ℕ, r * i + j < N ↔ i < (N + r - 1 - j) / r := by
    intro i
    rcases Nat.lt_or_ge N (j + 1) with hN | hN
    · have hlt : N + r - 1 - j < r := by omega
      rw [Nat.div_eq_of_lt hlt]
      constructor
      · intro h; omega
      · intro h; omega
    · have h1 : i < (N + r - 1 - j) / r ↔ i + 1 ≤ (N + r - 1 - j) / r := by omega
      rw [h1, Nat.le_div_iff_mul_le hr]
      have h2 : (i + 1) * r = r * i + r := by ring
      rw [h2]
      omega
  have hset : (range N).filter (fun k => k % r = j)
      = (range ((N + r - 1 - j) / r)).image (fun i => r * i + j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, hmod⟩
      have hdm : r * (k / r) + j = k := by
        rw [← hmod]; exact Nat.div_add_mod k r
      exact ⟨k / r, (hkey (k / r)).mp (by omega), hdm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hkey i).mpr hi, by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]⟩
  rw [hset, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hr
    (by omega)), Finset.card_range]

end Counting

/-! ## 6. The dimension of the isotypic components -/
section BasisSpan
variable {K : Type*} [Field K]

/-- The span of a subfamily of a finite basis has dimension the size of the subfamily. -/
theorem finrank_span_basis_image {M : Type*} [AddCommGroup M] [Module K M] {ι : Type*}
    [Fintype ι] (b : Module.Basis ι K M) (p : ι → Prop) [DecidablePred p] :
    Module.finrank K (Submodule.span K (b '' {i | p i})) = (Finset.univ.filter p).card := by
  have hrange : Set.range (fun i : {i // p i} => b (i : ι)) = b '' {i | p i} := by
    rw [show (fun i : {i // p i} => b (i : ι)) = b ∘ Subtype.val from rfl,
      Set.range_comp, Subtype.range_coe_subtype]
  have hli : LinearIndependent K (fun i : {i // p i} => b (i : ι)) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have hbasis : Module.Basis {i // p i} K (Submodule.span K (b '' {i | p i})) := by
    rw [← hrange]; exact Module.Basis.span hli
  rw [Module.finrank_eq_card_basis hbasis, Fintype.card_subtype]

end BasisSpan

section Dimension
variable {K : Type*} [Field K] [DecidableEq K] {A : K} {S : Finset K}

/-- The descended idempotent on a monomial: `π_j(X^k) = X^k` for `k ≡ j (mod r)`, else `0`. -/
theorem piQ_root_pow (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r) (j k : ℕ) :
    piQ hA hS r j ((AdjoinRoot.root (GaloisCommute.G S)) ^ k)
      = if k % r = j % r then (AdjoinRoot.root (GaloisCommute.G S)) ^ k else 0 := by
  have hroot : (AdjoinRoot.root (GaloisCommute.G S)) ^ k
      = AdjoinRoot.mk (GaloisCommute.G S) (X ^ k) := by
    rw [map_pow, AdjoinRoot.mk_X]
  rw [hroot, piQ_mk, pi_X_pow' hAr hord hr]
  split_ifs with h
  · rfl
  · exact map_zero _

/-- (Theorem "Isotypic decomposition", monomial description.)  The component `V_j` is the
    span of the monomials `X^k`, `k < |S|`, `k ≡ j (mod r)`. -/
theorem Vcomp_eq_span (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    {j : ℕ} (hj : j < r) :
    Vcomp hA hS r j = Submodule.span K
      ((AdjoinRoot.powerBasis' (monic_G S)).basis ''
        {i : Fin (GaloisCommute.G S).natDegree | (i : ℕ) % r = j}) := by
  have hbas : ∀ i : Fin (GaloisCommute.G S).natDegree,
      (AdjoinRoot.powerBasis' (monic_G S)).basis i
        = (AdjoinRoot.root (GaloisCommute.G S)) ^ (i : ℕ) := fun i => by
    rw [(AdjoinRoot.powerBasis' (monic_G S)).basis_eq_pow i, AdjoinRoot.powerBasis'_gen]
  have hjj : j % r = j := Nat.mod_eq_of_lt hj
  have hmap : Vcomp hA hS r j = Submodule.span K
      ((piQ hA hS r j) '' Set.range (AdjoinRoot.powerBasis' (monic_G S)).basis) := by
    show LinearMap.range (piQ hA hS r j) = _
    rw [LinearMap.range_eq_map,
      ← (AdjoinRoot.powerBasis' (monic_G S)).basis.span_eq, Submodule.map_span]
  rw [hmap]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨x, ⟨i, rfl⟩, rfl⟩
    rw [hbas i, piQ_root_pow hA hS hAr hord hr]
    by_cases h : (i : ℕ) % r = j % r
    · rw [if_pos h]
      exact Submodule.subset_span ⟨i, by rw [← hjj]; exact h, hbas i⟩
    · rw [if_neg h]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro y ⟨i, hi, rfl⟩
    refine Submodule.subset_span
      ⟨(AdjoinRoot.powerBasis' (monic_G S)).basis i, ⟨i, rfl⟩, ?_⟩
    rw [hbas i, piQ_root_pow hA hS hAr hord hr, if_pos (by rw [hjj]; exact hi)]

/-- (Theorem "Isotypic decomposition", dimension.)  `dim V_j = ⌈(|S| − j)/r⌉`, written
    `(|S| + r − 1 − j)/r` in natural-number division. -/
theorem finrank_Vcomp (hA : IsUnit A) (hS : S.image (fun a => A * a) = S) {r : ℕ}
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 1 ≤ r)
    {j : ℕ} (hj : j < r) :
    Module.finrank K (Vcomp hA hS r j) = (S.card + r - 1 - j) / r := by
  have h1 : Module.finrank K (Vcomp hA hS r j)
      = (Finset.univ.filter
          (fun i : Fin (GaloisCommute.G S).natDegree => (i : ℕ) % r = j)).card := by
    rw [Vcomp_eq_span hA hS hAr hord hr hj]
    exact finrank_span_basis_image (AdjoinRoot.powerBasis' (monic_G S)).basis
      (fun i : Fin (GaloisCommute.G S).natDegree => (i : ℕ) % r = j)
  have hcard : (Finset.univ.filter
        (fun i : Fin (GaloisCommute.G S).natDegree => (i : ℕ) % r = j)).card
      = ((Finset.range (GaloisCommute.G S).natDegree).filter (fun k => k % r = j)).card := by
    rw [Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_eq_sum_range (fun k => if k % r = j then 1 else 0)
        (GaloisCommute.G S).natDegree]
  rw [h1, hcard, card_filter_mod_eq _ r j (by omega) hj, natDegree_G]

end Dimension

end Isotypic
