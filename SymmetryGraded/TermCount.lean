/-
  TermCount.lean

  Formal verification (Lean 4 + Mathlib) of

    Theorem "The term count is generically attained"  (Appendix "Proofs for the scalar axis")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping": on a set of
  `n` interpolation nodes, the coefficient `c_k` of `X^k` (`k < n`) of the Lagrange
  interpolant is a *nonzero* linear functional of the interpolated data, so it vanishes
  only on a hyperplane of the data space.  With no unproved placeholders:

  * `coeffFunctional`, `coeffFunctional_apply`
        `c_k(λ) = Σ_s λ(s)·[X^k]L_s`, the covector `ℓ_k = ([X^k]L_s)_s`.
  * `interpolate_monomial`
        the Lagrange basis reproduces `X^k` for `k < n`.
  * `coeffFunctional_ne_zero`, `exists_data_coeff_ne_zero`
        `ℓ_k ≠ 0` for every `k < n`.
  * `ker_ne_top`, `range_eq_top`, `finrank_ker`
        `{c_k = 0}` is a proper subspace of codimension one (a hyperplane):
        `dim ker c_k = n − 1`.
  * `coeffFunctional_S_*`, `finrank_ker_S`
        the instance where the node set is a `Finset K` (the support `S_A`).
-/
import Mathlib
import SymmetryGraded.Lattice

namespace TermCount

open Polynomial

variable {K : Type*} [Field K]

/-! ## 1. General node set `s : Finset ι` with injective node map `v` -/
section General
variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → K)

/-- The coefficient functional `c_k : λ ↦ [X^k] (interpolant of λ)`. -/
noncomputable def coeffFunctional (k : ℕ) : (ι → K) →ₗ[K] K :=
  (lcoeff K k).comp (Lagrange.interpolate s v)

/-- `c_k(λ) = Σ_{i∈s} λ(i)·[X^k]L_i` (the covector `ℓ_k`). -/
theorem coeffFunctional_apply (k : ℕ) (lam : ι → K) :
    coeffFunctional s v k lam = ∑ i ∈ s, lam i * (Lagrange.basis s v i).coeff k := by
  simp only [coeffFunctional, LinearMap.comp_apply, lcoeff_apply, Lagrange.interpolate_apply,
    finsetSum_coeff, coeff_C_mul]

/-- `c_k(λ) = 0 ↔ λ ∈ ker c_k` (the hyperplane phrasing). -/
theorem coeff_eq_zero_iff_mem_ker (k : ℕ) (lam : ι → K) :
    (Lagrange.interpolate s v lam).coeff k = 0 ↔ lam ∈ LinearMap.ker (coeffFunctional s v k) := by
  simp [coeffFunctional, LinearMap.mem_ker]

variable (hv : Set.InjOn v s)
include hv

/-- The Lagrange basis on `s` reproduces `X^k` for `k < |s|`. -/
theorem interpolate_monomial {k : ℕ} (hk : k < s.card) :
    Lagrange.interpolate s v (fun i => v i ^ k) = X ^ k := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _ hv
  · rw [degree_X_pow]; exact_mod_cast hk
  · intro i _; simp

/-- `ℓ_k ≠ 0` for every `k < |s|`: the data `λ(i) = v(i)^k` has `c_k = 1`. -/
theorem coeffFunctional_ne_zero {k : ℕ} (hk : k < s.card) : coeffFunctional s v k ≠ 0 := by
  intro h
  have := congrArg (fun f : (ι → K) →ₗ[K] K => f (fun i => v i ^ k)) h
  simp only [coeffFunctional, LinearMap.comp_apply, lcoeff_apply, LinearMap.zero_apply] at this
  rw [interpolate_monomial s v hv hk, coeff_X_pow_self] at this
  exact one_ne_zero this

/-- Some data has a nonzero `k`-th coefficient. -/
theorem exists_data_coeff_ne_zero {k : ℕ} (hk : k < s.card) :
    ∃ lam : ι → K, (Lagrange.interpolate s v lam).coeff k ≠ 0 :=
  ⟨fun i => v i ^ k, by rw [interpolate_monomial s v hv hk, coeff_X_pow_self]; exact one_ne_zero⟩

/-- The zero set `{c_k = 0}` is a proper subspace. -/
theorem ker_ne_top {k : ℕ} (hk : k < s.card) : LinearMap.ker (coeffFunctional s v k) ≠ ⊤ := by
  intro h
  exact coeffFunctional_ne_zero s v hv hk (LinearMap.ker_eq_top.mp h)

/-- A nonzero functional into a field is surjective. -/
theorem range_eq_top {k : ℕ} (hk : k < s.card) : LinearMap.range (coeffFunctional s v k) = ⊤ := by
  obtain ⟨lam, hlam⟩ := exists_data_coeff_ne_zero s v hv hk
  have hne : coeffFunctional s v k lam ≠ 0 := hlam
  rw [eq_top_iff]
  rintro c -
  refine ⟨(c / coeffFunctional s v k lam) • lam, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]

/-- `{c_k = 0}` is a hyperplane: `dim ker c_k = dim (ι → K) − 1` for finite `ι`. -/
theorem finrank_ker [Fintype ι] {k : ℕ} (hk : k < s.card) :
    Module.finrank K (LinearMap.ker (coeffFunctional s v k)) = Fintype.card ι - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (coeffFunctional s v k)
  rw [range_eq_top s v hv hk, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h
  omega

end General

/-! ## 2. The support `S ⊆ K` as node set (`ι = ↥S`, `v = Subtype.val`) -/
section Support
variable [DecidableEq K] (S : Finset K)

/-- Node map on the subtype `↥S`. -/
def nodes : S → K := fun x => (x : K)

omit [Field K] [DecidableEq K] in
theorem nodes_injOn : Set.InjOn (nodes S) (Finset.univ : Finset S) :=
  fun _ _ _ _ h => Subtype.ext h

/-- `c_k` on the data space `Λ = K^{S}`. -/
noncomputable def coeffFunctionalS (k : ℕ) : (S → K) →ₗ[K] K :=
  coeffFunctional (Finset.univ : Finset S) (nodes S) k

theorem coeffFunctionalS_apply (k : ℕ) (lam : S → K) :
    coeffFunctionalS S k lam = ∑ x, lam x * (Lagrange.basis Finset.univ (nodes S) x).coeff k :=
  coeffFunctional_apply _ _ _ _

omit [Field K] [DecidableEq K] in
theorem card_univ_S : (Finset.univ : Finset S).card = S.card := by
  rw [Finset.card_univ, Fintype.card_coe]

theorem coeffFunctionalS_ne_zero {k : ℕ} (hk : k < S.card) : coeffFunctionalS S k ≠ 0 :=
  coeffFunctional_ne_zero _ _ (nodes_injOn S) (by rwa [card_univ_S])

theorem exists_data_coeff_ne_zero_S {k : ℕ} (hk : k < S.card) :
    ∃ lam : S → K, (Lagrange.interpolate Finset.univ (nodes S) lam).coeff k ≠ 0 :=
  exists_data_coeff_ne_zero _ _ (nodes_injOn S) (by rwa [card_univ_S])

theorem ker_ne_top_S {k : ℕ} (hk : k < S.card) : LinearMap.ker (coeffFunctionalS S k) ≠ ⊤ :=
  ker_ne_top _ _ (nodes_injOn S) (by rwa [card_univ_S])

/-- **Theorem (The term count is generically attained), hyperplane part**: for every
    `k < |S|`, `{λ ∈ K^S : c_k(λ) = 0}` is a hyperplane, `dim = |S| − 1`. -/
theorem finrank_ker_S {k : ℕ} (hk : k < S.card) :
    Module.finrank K (LinearMap.ker (coeffFunctionalS S k)) = S.card - 1 := by
  rw [coeffFunctionalS, finrank_ker _ _ (nodes_injOn S) (by rwa [card_univ_S]), Fintype.card_coe]

end Support

/-! ## 3. Bridge to the digit setting of `Interpolation.lean` -/
section Digits

/-- On an injective digit region `T`, the interpolant `Lagrange.interpolate T (φ_A) λ` of
    `Interpolation.exists_unique_interpolant` has, for every `k < |T|`, some data `λ`
    with nonzero `k`-th coefficient. -/
theorem exists_digit_data_coeff_ne_zero (A : K) (T : Finset (ℤ × ℤ))
    (hinj : Set.InjOn (DigitLattice.phi A) T) {k : ℕ} (hk : k < T.card) :
    ∃ lam : ℤ × ℤ → K, (Lagrange.interpolate T (DigitLattice.phi A) lam).coeff k ≠ 0 :=
  exists_data_coeff_ne_zero T _ hinj hk

end Digits

end TermCount
