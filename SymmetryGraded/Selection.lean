/-
  Selection.lean

  Formal verification (Lean 4 + Mathlib) of

    Lemma "Absence of the obstruction for r ≥ 3"   (Appendix "Selection of the pencil")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  For `r ≥ 3` the folded polynomial `Q` of the factored form `P = c₁X + X^{r−1}Q(X^r)`
  has no root on the folded support `Ω_A^{(r)} = {x^r : x ∈ S_A \ {0}}`, because the
  linear coefficient `c₁ = 1/(1 − A²)` is nonzero: a root would force
  `λA + η ≡ 0`, i.e. `φ_A(λ, η) = φ_A(0, 0)`, and the swap symmetry of the region
  together with injectivity of `φ_A` then forces `(η, λ) = (0, 0)`, which is excluded.
  Consequently `gcd(Q, Γ) = 1` for the vanishing polynomial `Γ` of the folded support
  enlarged by pad points chosen off the roots of `Q`.  With no unproved placeholders:

  * `foldedSupport`
        `Ω_A^{(r)} = {x^r : x ∈ S_A \ {0}}` as a `Finset`.
  * `eval_Q_ne_zero`
        (Lemma "Absence of the obstruction", main step)  `Q(x^r) ≠ 0` for every
        nonzero `x ∈ S_A`, from the factored form and the swap symmetry of `T`.
  * `eval_Q_ne_zero_of_mem_foldedSupport`
        the same statement read on `Ω_A^{(r)}`.
  * `isCoprime_prod_X_sub_C`
        `Q(y) ≠ 0` on a finite set `W` gives `gcd(Q, ∏_{y∈W}(Y − y)) = 1`.
  * `isCoprime_Gamma`
        (Lemma "Absence of the obstruction", conclusion)  `gcd(Q, Γ) = 1` for
        `Γ = ∏_{y ∈ Ω_A^{(r)} ∪ Z}(Y − y)` and pad points `Z` with `Q(z) ≠ 0`.
  * `hyp_h1`, `hyp`, `monodromy_of_selection`
        the hypothesis `Monodromy.Hyp.h1` discharged: the field `h1` of the standing
        hypotheses of the monodromy theorem is supplied by `isCoprime_Gamma` instead of
        being assumed, `hyp` assembles a full `Monodromy.Hyp` from the remaining data
        (`Γ.Monic` is likewise proved, not assumed), and `monodromy_of_selection` reads
        off the deterministic conclusions — pairwise coprimality of the pencil, the
        branch-locus bound `2n' − 2`, squarefreeness of the fibres off the branch
        locus — from the geometric data and (H2)–(H4) alone.
  * `eval_Q_ne_zero_interp`, `isCoprime_Gamma_interp`
        the same conclusions starting from interpolation alone: the factored form is
        produced by `Interpolation.order_r_factored`, so only stability, the swap
        symmetry, `(0,0) ∈ T` and injectivity are assumed.
-/
import Mathlib
import SymmetryGraded.Interpolation
import SymmetryGraded.Monodromy

namespace Selection

open Polynomial DigitLattice

variable {K : Type*} [Field K]

/-! ## 1. The folded support -/

/-- The folded support `Ω_A^{(r)} = {x^r : x ∈ S_A \ {0}}`, where `S_A = φ_A(T)`. -/
noncomputable def foldedSupport [DecidableEq K] (A : K) (r : ℕ) (T : Finset (ℤ × ℤ)) :
    Finset K :=
  ((T.image (phi A)).erase 0).image (fun x => x ^ r)

theorem mem_foldedSupport [DecidableEq K] {A : K} {r : ℕ} {T : Finset (ℤ × ℤ)} {y : K} :
    y ∈ foldedSupport A r T ↔ ∃ v ∈ T, phi A v ≠ 0 ∧ y = (phi A v) ^ r := by
  unfold foldedSupport
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx0, hxm⟩ := Finset.mem_erase.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hxm
    exact ⟨v, hv, hx0, rfl⟩
  · rintro ⟨v, hv, hv0, rfl⟩
    exact Finset.mem_image.mpr
      ⟨phi A v, Finset.mem_erase.mpr ⟨hv0, Finset.mem_image_of_mem _ hv⟩, rfl⟩

/-! ## 2. The folded polynomial does not vanish on the folded support -/

/-- (Lemma "Absence of the obstruction for `r ≥ 3`", main step.)  Let `A` have exact
    order `r ≥ 3`, let the region `T` be stable under the swap `(η, λ) ↦ (λ, η)` and
    contain the origin, let `φ_A` be injective on `T`, and let
    `P = c₁X + X^{r−1}Q(X^r)` with `c₁ = 1/(1 − A²)` interpolate the low digit on `T`.
    Then `Q(x^r) ≠ 0` for every nonzero `x = φ_A(v)`, `v ∈ T`. -/
theorem eval_Q_ne_zero {A : K} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    {T : Finset (ℤ × ℤ)} (hswap : ∀ v ∈ T, (v.2, v.1) ∈ T) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T)
    (hinj : Set.InjOn (phi A) T) {P Q : K[X]}
    (hfact : P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand K r Q)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K))
    {v : ℤ × ℤ} (hv : v ∈ T) (hv0 : phi A v ≠ 0) :
    Q.eval ((phi A v) ^ r) ≠ 0 := by
  intro hQ0
  have hA0 : A ≠ 0 := OrderR.A_ne_zero hAr (by omega)
  have hc : (1 : K) - A ^ 2 ≠ 0 := OrderR.one_sub_sq_ne_zero hord hr
  -- the interpolation value at `x` collapses to `c₁ x`
  have hval : (v.2 : K) = (1 - A ^ 2)⁻¹ * phi A v := by
    rw [← hinterp v hv, hfact]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, expand_eval, hQ0, mul_zero,
      add_zero]
  -- clear the denominator: `(1 − A²)λ = ηA + λ`, i.e. `A(Aλ + η) = 0`
  have hcinv : (1 - A ^ 2) * (1 - A ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hc
  have hlin : A * ((v.2 : K) * A + (v.1 : K)) = 0 := by
    have h := congrArg (fun z => (1 - A ^ 2) * z) hval
    simp only [phi] at h ⊢
    rw [← mul_assoc, hcinv, one_mul] at h
    linear_combination -h
  have hswap0 : phi A (v.2, v.1) = 0 := by
    simp only [phi]
    exact (mul_eq_zero.mp hlin).resolve_left hA0
  -- injectivity on the swap-stable region forces `(λ, η) = (0, 0)`
  have hmem : (v.2, v.1) ∈ T := hswap v hv
  have heq : phi A (v.2, v.1) = phi A ((0 : ℤ), (0 : ℤ)) := by
    rw [hswap0]; simp [phi]
  have := hinj (Finset.mem_coe.mpr hmem) (Finset.mem_coe.mpr h0) heq
  have h1 : v.1 = 0 := (Prod.mk.injEq _ _ _ _ ▸ this).2
  have h2 : v.2 = 0 := (Prod.mk.injEq _ _ _ _ ▸ this).1
  exact hv0 (by simp [phi, h1, h2])

/-- (Lemma "Absence of the obstruction for `r ≥ 3`".)  `Q` has no root on the folded
    support `Ω_A^{(r)}`. -/
theorem eval_Q_ne_zero_of_mem_foldedSupport [DecidableEq K] {A : K} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    {T : Finset (ℤ × ℤ)} (hswap : ∀ v ∈ T, (v.2, v.1) ∈ T) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T)
    (hinj : Set.InjOn (phi A) T) {P Q : K[X]}
    (hfact : P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand K r Q)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K))
    {y : K} (hy : y ∈ foldedSupport A r T) : Q.eval y ≠ 0 := by
  obtain ⟨v, hv, hv0, rfl⟩ := mem_foldedSupport.mp hy
  exact eval_Q_ne_zero hAr hord hr hswap h0 hinj hfact hinterp hv hv0

/-! ## 3. Coprimality with the vanishing polynomial -/

/-- If `Q` has no root in a finite set `W`, it is coprime to `∏_{y ∈ W}(Y − y)`. -/
theorem isCoprime_prod_X_sub_C (Q : K[X]) (W : Finset K) (h : ∀ y ∈ W, Q.eval y ≠ 0) :
    IsCoprime Q (∏ y ∈ W, (X - C y)) := by
  refine IsCoprime.prod_right fun y hy => ?_
  refine (((irreducible_X_sub_C y).coprime_iff_not_dvd).mpr ?_).symm
  rw [dvd_iff_isRoot]
  exact h y hy

/-- (Lemma "Absence of the obstruction for `r ≥ 3`", conclusion.)  With the pad points
    `Z` chosen off the roots of `Q`, the vanishing polynomial
    `Γ = ∏_{y ∈ Ω_A^{(r)} ∪ Z}(Y − y)` of the padded folded support is coprime to `Q`. -/
theorem isCoprime_Gamma [DecidableEq K] {A : K} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    {T : Finset (ℤ × ℤ)} (hswap : ∀ v ∈ T, (v.2, v.1) ∈ T) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T)
    (hinj : Set.InjOn (phi A) T) {P Q : K[X]}
    (hfact : P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand K r Q)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K))
    (Z : Finset K) (hZ : ∀ z ∈ Z, Q.eval z ≠ 0) :
    IsCoprime Q (∏ y ∈ foldedSupport A r T ∪ Z, (X - C y)) := by
  refine isCoprime_prod_X_sub_C Q _ fun y hy => ?_
  rcases Finset.mem_union.mp hy with hy | hy
  · exact eval_Q_ne_zero_of_mem_foldedSupport hAr hord hr hswap h0 hinj hfact hinterp hy
  · exact hZ y hy

/-! ## 4. From interpolation alone -/

/-- The same conclusion with the factored form produced by interpolation: only
    `M_A`-stability, the swap symmetry, `(0,0) ∈ T` and injectivity are assumed. -/
theorem eval_Q_ne_zero_interp {A : K} {τ : ℤ} {r : ℕ} (hA : A ^ 2 = τ * A - 1)
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    {T : Finset (ℤ × ℤ)} (hT : ∀ v ∈ T, rot τ v ∈ T) (hcard : 2 ≤ T.card)
    (hswap : ∀ v ∈ T, (v.2, v.1) ∈ T) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T)
    (hinj : Set.InjOn (phi A) T) {P : K[X]} (hdeg : P.degree < T.card)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K)) :
    ∃ Q : K[X], P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand K r Q ∧
      ∀ v ∈ T, phi A v ≠ 0 → Q.eval ((phi A v) ^ r) ≠ 0 := by
  obtain ⟨Q, hfact, -⟩ :=
    Interpolation.order_r_factored hA hAr hord hr T hT hcard hinj P hdeg hinterp
  exact ⟨Q, hfact, fun v hv hv0 =>
    eval_Q_ne_zero hAr hord hr hswap h0 hinj hfact hinterp hv hv0⟩

/-- Coprimality of `Q` and `Γ` from interpolation alone. -/
theorem isCoprime_Gamma_interp [DecidableEq K] {A : K} {τ : ℤ} {r : ℕ} (hA : A ^ 2 = τ * A - 1)
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    {T : Finset (ℤ × ℤ)} (hT : ∀ v ∈ T, rot τ v ∈ T) (hcard : 2 ≤ T.card)
    (hswap : ∀ v ∈ T, (v.2, v.1) ∈ T) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T)
    (hinj : Set.InjOn (phi A) T) {P : K[X]} (hdeg : P.degree < T.card)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K))
    (Z : Finset K) :
    ∃ Q : K[X], P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand K r Q ∧
      ((∀ z ∈ Z, Q.eval z ≠ 0) →
        IsCoprime Q (∏ y ∈ foldedSupport A r T ∪ Z, (X - C y))) := by
  obtain ⟨Q, hfact, -⟩ :=
    Interpolation.order_r_factored hA hAr hord hr T hT hcard hinj P hdeg hinterp
  exact ⟨Q, hfact, fun hZ =>
    isCoprime_Gamma hAr hord hr hswap h0 hinj hfact hinterp Z hZ⟩

/-! ## 5. Discharging the hypothesis `Monodromy.Hyp.h1` -/

section Hyp
variable {p : ℕ} [Fact p.Prime]

/-- **The hypothesis (H1) of the monodromy theorem is not assumed but proved.**  For the
    paper's instance — `A` of exact order `r ≥ 3`, a swap-stable region containing the
    origin on which `φ_A` is injective, and pad points off the roots of `Q` — the field
    `Monodromy.Hyp.h1`, i.e. `IsCoprime Q Γ`, follows from
    Lemma "Absence of the obstruction for `r ≥ 3`". -/
theorem hyp_h1 {A : ZMod p} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    {T : Finset (ℤ × ℤ)} (hswap : ∀ v ∈ T, (v.2, v.1) ∈ T) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T)
    (hinj : Set.InjOn (phi A) T) {P Q : (ZMod p)[X]}
    (hfact : P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand (ZMod p) r Q)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : ZMod p))
    (Z : Finset (ZMod p)) (hZ : ∀ z ∈ Z, Q.eval z ≠ 0)
    {Γ : (ZMod p)[X]} (hΓ : Γ = ∏ y ∈ foldedSupport A r T ∪ Z, (X - C y)) :
    IsCoprime Q Γ := by
  subst hΓ
  exact isCoprime_Gamma hAr hord hr hswap h0 hinj hfact hinterp Z hZ

/-- **The standing hypotheses of the monodromy theorem with (H1) discharged.**  Given the
    geometric data of the paper's instance, `Monodromy.Hyp Γ Q` is assembled from the
    remaining hypotheses (H2)–(H4) only; (H1) is supplied by `hyp_h1`. -/
noncomputable def hyp {A : ZMod p} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    {T : Finset (ℤ × ℤ)} (hswap : ∀ v ∈ T, (v.2, v.1) ∈ T) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T)
    (hinj : Set.InjOn (phi A) T) {P Q : (ZMod p)[X]}
    (hfact : P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand (ZMod p) r Q)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : ZMod p))
    (Z : Finset (ZMod p)) (hZ : ∀ z ∈ Z, Q.eval z ≠ 0)
    {Γ : (ZMod p)[X]} (hΓ : Γ = ∏ y ∈ foldedSupport A r T ∪ Z, (X - C y))
    (degQ : Q.natDegree < Γ.natDegree) (h2 : Squarefree Q)
    (h3 : Γ.natDegree - Q.natDegree ≤ 2) (Δ : (ZMod p)[X]) (h4_ne : Δ ≠ 0)
    (h4_deg : Δ.natDegree = 2 * Γ.natDegree - 2 - (Γ.natDegree - Q.natDegree - 1))
    (h4_sqf : Squarefree Δ)
    (h4_branch : ∀ c : ZMod p, ¬ Squarefree (Monodromy.pencil Γ Q c) ↔ Δ.IsRoot c) :
    Monodromy.Hyp Γ Q where
  monic := by
    subst hΓ
    exact monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  degQ := degQ
  h1 := hyp_h1 hAr hord hr hswap h0 hinj hfact hinterp Z hZ hΓ
  h2 := h2
  h3 := h3
  Δ := Δ
  h4_ne := h4_ne
  h4_deg := h4_deg
  h4_sqf := h4_sqf
  h4_branch := h4_branch

/-- **The monodromy consequences with (H1) supplied rather than assumed.**  From the
    geometric data of the paper's instance together with (H2)–(H4): distinct members of the
    pencil `Γ + cQ` are coprime, the branch locus has at most `2n' − 2` points, and every
    parameter off the branch locus gives a squarefree fibre.  No coprimality hypothesis is
    taken anywhere in the statement; it is `isCoprime_Gamma`. -/
theorem monodromy_of_selection {A : ZMod p} {r : ℕ} (hAr : A ^ r = 1)
    (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    {T : Finset (ℤ × ℤ)} (hswap : ∀ v ∈ T, (v.2, v.1) ∈ T) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ T)
    (hinj : Set.InjOn (phi A) T) {P Q : (ZMod p)[X]}
    (hfact : P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand (ZMod p) r Q)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : ZMod p))
    (Z : Finset (ZMod p)) (hZ : ∀ z ∈ Z, Q.eval z ≠ 0)
    {Γ : (ZMod p)[X]} (hΓ : Γ = ∏ y ∈ foldedSupport A r T ∪ Z, (X - C y))
    (degQ : Q.natDegree < Γ.natDegree) (h2 : Squarefree Q)
    (h3 : Γ.natDegree - Q.natDegree ≤ 2) (Δ : (ZMod p)[X]) (h4_ne : Δ ≠ 0)
    (h4_deg : Δ.natDegree = 2 * Γ.natDegree - 2 - (Γ.natDegree - Q.natDegree - 1))
    (h4_sqf : Squarefree Δ)
    (h4_branch : ∀ c : ZMod p, ¬ Squarefree (Monodromy.pencil Γ Q c) ↔ Δ.IsRoot c) :
    (∀ c₁ c₂ : ZMod p, c₁ ≠ c₂ →
        IsCoprime (Monodromy.pencil Γ Q c₁) (Monodromy.pencil Γ Q c₂)) ∧
      Δ.roots.toFinset.card ≤ 2 * Γ.natDegree - 2 ∧
      (∀ c : ZMod p, c ∉ Δ.roots.toFinset → Squarefree (Monodromy.pencil Γ Q c)) := by
  let H : Monodromy.Hyp Γ Q :=
    hyp hAr hord hr hswap h0 hinj hfact hinterp Z hZ hΓ degQ h2 h3 Δ h4_ne h4_deg h4_sqf
      h4_branch
  have hΔ : H.Δ = Δ := rfl
  refine ⟨fun _ _ hne => H.isCoprime_pencil hne, ?_, fun c hc => ?_⟩
  · rw [← hΔ]
    exact Monodromy.branch_card_le H
  · exact Monodromy.squarefree_pencil_of_notMem H (by rw [hΔ]; exact hc)

end Hyp

end Selection
