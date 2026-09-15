/-
  Interpolation.lean

  Formal verification (Lean 4 + Mathlib) of the derivation of the functional
  equation from interpolation, in

    "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping"

  (Theorem "Unified order-r functional equation").  The digit-extraction
  polynomial `P_A` is *the* polynomial of degree `< |T|` with `P_A(ηA + λ) = λ`
  on an `M_A`-stable region `T ⊆ ℤ²` on which `φ_A(η,λ) = ηA + λ` is injective.
  The intertwining `φ_A ∘ M_A = A·φ_A` and uniqueness of interpolation force
  `P_A(AX) = A⁻¹(P_A(X) − X)`; the support theorems of `OrderR.lean` then apply
  with no functional-equation hypothesis.  With no unproved placeholders:

  * `exists_unique_interpolant`
        existence and uniqueness of the interpolant (Mathlib's `Lagrange.interpolate`).
  * `functional_equation`
        (Theorem "Unified order-r functional equation")  stability
        `M_A(T) ⊆ T`, injectivity of `φ_A` on `T`, `deg P < |T|`, `2 ≤ |T|` and
        `P(φ_A v) = v.2` on `T` give `P(AX) = A⁻¹(P(X) − X)`.
  * `order_r_support`, `order_r_factored`
        (Corollary "Support of the order-r filter", from interpolation)
        the support `{1} ∪ {k ≡ r−1 (mod r)}`, `c₁ = 1/(1 − A²)`, and the
        factored form `P = c₁X + X^{r−1}Q(X^r)` — no functional equation assumed.
  * `hex_image_rot`, `hex_functional_equation`, `hex_support`, `hex_factored`
        the hexagon instance (`τ = 1`, `A² = A − 1`): `M_A T_B = T_B` from
        `hex_rot_iff`, and the order-six theorem from interpolation on `T_B`.
  * `box_image_rot`, `box_functional_equation`, `box_support`
        the box instance (`τ = 0`, `A² = −1`).
-/
import Mathlib
import SymmetryGraded.OrderR
import SymmetryGraded.Lattice

namespace Interpolation

open Polynomial DigitLattice

variable {K : Type*} [Field K]

/-! ## 1. Stability: the two formulations -/
section Stability

/-- If `rot τ` maps `T` onto itself as a finset, every `rot τ v`, `v ∈ T`, lies in `T`. -/
theorem rot_mem_of_image_eq {τ : ℤ} {T : Finset (ℤ × ℤ)} (hT : T.image (rot τ) = T) :
    ∀ v ∈ T, rot τ v ∈ T := by
  intro v hv
  rw [← hT]
  exact Finset.mem_image_of_mem _ hv

/-- Conversely, the pointwise form `rot τ v ∈ T ↔ v ∈ T` gives `rot τ '' T = T`
    (by injectivity of `rot τ` and a cardinality count). -/
theorem image_rot_eq_of_iff {τ : ℤ} {T : Finset (ℤ × ℤ)}
    (h : ∀ v, rot τ v ∈ T ↔ v ∈ T) : T.image (rot τ) = T := by
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact (h v).mpr hv
  · rw [Finset.card_image_of_injective _ (rot_bijective τ).injective]

end Stability

/-! ## 2. Existence and uniqueness of the interpolant -/
section Interpolant

/-- Existence and uniqueness of the interpolant: for `φ_A` injective on `T` there is
    exactly one `P` of degree `< |T|` with `P(φ_A v) = v.2` for all `v ∈ T`
    (Mathlib's Lagrange interpolation). -/
theorem exists_unique_interpolant (A : K) (T : Finset (ℤ × ℤ))
    (hinj : Set.InjOn (phi A) T) :
    ∃! P : K[X], P.degree < T.card ∧ ∀ v ∈ T, P.eval (phi A v) = (v.2 : K) := by
  classical
  refine ⟨Lagrange.interpolate T (phi A) (fun v => (v.2 : K)), ⟨?_, ?_⟩, ?_⟩
  · exact Lagrange.degree_interpolate_lt _ hinj
  · intro v hv
    exact Lagrange.eval_interpolate_at_node _ hinj hv
  · rintro P ⟨hdeg, hev⟩
    exact Lagrange.eq_interpolate_of_eval_eq _ hinj hdeg hev

end Interpolant

/-! ## 3. The functional equation from stability and injectivity -/
section FunctionalEquation

/-- `A ≠ 0` for `A² = τA − 1`. -/
theorem A_ne_zero_of_char {A : K} {τ : ℤ} (hA : A ^ 2 = τ * A - 1) : A ≠ 0 := by
  intro h; rw [h] at hA; norm_num at hA

/-- (Theorem "Unified order-r functional equation".)  Let `A² = τA − 1`, let
    `T ⊆ ℤ²` be finite with `M_A(T) ⊆ T` and `2 ≤ |T|`, let `φ_A` be injective on `T`,
    and let `P` have degree `< |T|` and interpolate the low digit,
    `P(ηA + λ) = λ` on `T`.  Then `P(AX) = A⁻¹(P(X) − X)`. -/
theorem functional_equation {A : K} {τ : ℤ} (hA : A ^ 2 = τ * A - 1)
    (T : Finset (ℤ × ℤ)) (hT : ∀ v ∈ T, rot τ v ∈ T) (hcard : 2 ≤ T.card)
    (hinj : Set.InjOn (phi A) T) (P : K[X]) (hdeg : P.degree < T.card)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K)) :
    P.comp (C A * X) = C A⁻¹ * (P - X) := by
  classical
  have hA0 : A ≠ 0 := A_ne_zero_of_char hA
  -- the difference `R` vanishes on the `|T|` distinct points `φ_A(T)` and has degree `< |T|`
  set R : K[X] := P.comp (C A * X) - C A⁻¹ * (P - X) with hR
  have hcardim : (T.image (phi A)).card = T.card := Finset.card_image_of_injOn hinj
  have hRdeg : R.degree < (T.image (phi A)).card := by
    rw [hcardim, degree_lt_iff_coeff_zero]
    intro m hm
    have hPm : P.coeff m = 0 :=
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast hm))
    have hXm : (X : K[X]).coeff m = 0 := by
      rw [coeff_X]; exact if_neg (by omega)
    rw [hR, coeff_sub, OrderFour.coeff_comp_C_mul_X, coeff_C_mul, coeff_sub, hPm, hXm]
    ring
  have hRzero : R = 0 := by
    apply eq_zero_of_degree_lt_of_eval_finset_eq_zero _ hRdeg
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have h1 : P.eval (A * phi A v) = (-(v.1) : ℤ) := by
      rw [← phi_rot hA, hinterp _ (hT v hv)]; rfl
    rw [hR, eval_sub, eval_comp, eval_mul, eval_C, eval_X, eval_mul, eval_C, eval_sub,
      eval_X, h1, hinterp v hv]
    simp only [phi]
    push_cast
    field_simp
    ring
  exact sub_eq_zero.mp hRzero

/-- (Corollary "Support of the order-r filter", from interpolation.)  For `A` of exact
    order `r ≥ 3` with `A² = τA − 1`, the interpolant of the low digit on an `M_A`-stable
    injective region has support in `{1} ∪ {k ≡ r − 1 (mod r)}` and `c₁ = 1/(1 − A²)`.
    No functional equation is assumed. -/
theorem order_r_support {A : K} {τ : ℤ} {r : ℕ} (hA : A ^ 2 = τ * A - 1)
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    (T : Finset (ℤ × ℤ)) (hT : ∀ v ∈ T, rot τ v ∈ T) (hcard : 2 ≤ T.card)
    (hinj : Set.InjOn (phi A) T) (P : K[X]) (hdeg : P.degree < T.card)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K)) :
    (∀ k, k ≠ 1 → k % r ≠ r - 1 → P.coeff k = 0) ∧ P.coeff 1 = (1 - A ^ 2)⁻¹ := by
  obtain ⟨h1, -, h3⟩ := OrderR.order_r_filter hAr hord hr P
    (functional_equation hA T hT hcard hinj P hdeg hinterp)
  exact ⟨h1, h3⟩

/-- The factored form `P = c₁X + X^{r−1}Q(X^r)`, `c₁ = 1/(1 − A²)`, from interpolation. -/
theorem order_r_factored {A : K} {τ : ℤ} {r : ℕ} (hA : A ^ 2 = τ * A - 1)
    (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1) (hr : 3 ≤ r)
    (T : Finset (ℤ × ℤ)) (hT : ∀ v ∈ T, rot τ v ∈ T) (hcard : 2 ≤ T.card)
    (hinj : Set.InjOn (phi A) T) (P : K[X]) (hdeg : P.degree < T.card)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K)) :
    ∃ Q : K[X], P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand K r Q ∧
      Q.natDegree ≤ (P.natDegree - (r - 1)) / r :=
  OrderR.factored_form_poly hAr hord hr P (functional_equation hA T hT hcard hinj P hdeg hinterp)

end FunctionalEquation

/-! ## 4. The hexagon instance (`τ = 1`) and the box instance (`τ = 0`) -/
section Instances

/-- `M_A T_B = T_B` for the sixth turn (from `hex_rot_iff`). -/
theorem hex_image_rot (B : ℤ) : (hex B).image (rot 1) = hex B :=
  image_rot_eq_of_iff (hex_rot_iff B)

/-- `M_A [−B,B]² = [−B,B]²` for the quarter turn (from `box_rot_iff`). -/
theorem box_image_rot (B : ℤ) : (box B).image (rot 0) = box B :=
  image_rot_eq_of_iff (box_rot_iff B)

/-- `|T_B| ≥ 2` for `B ≥ 1` (it contains `(0,0)` and `(0,1)`). -/
theorem two_le_card_hex (B : ℤ) (hB : 1 ≤ B) : 2 ≤ (hex B).card := by
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ hex B := by
    rw [mem_hex]; simp; omega
  have h1 : ((0 : ℤ), (1 : ℤ)) ∈ hex B := by
    rw [mem_hex]; simp; omega
  have : ({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))} : Finset (ℤ × ℤ)) ⊆ hex B := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h0
    · exact h1
  have hc := Finset.card_le_card this
  rw [Finset.card_pair (by decide)] at hc
  exact hc

/-- `|[−B,B]²| ≥ 2` for `B ≥ 1`. -/
theorem two_le_card_box (B : ℤ) (hB : 1 ≤ B) : 2 ≤ (box B).card := by
  have h0 : ((0 : ℤ), (0 : ℤ)) ∈ box B := by
    rw [mem_box]; simp; omega
  have h1 : ((0 : ℤ), (1 : ℤ)) ∈ box B := by
    rw [mem_box]; simp; omega
  have : ({((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))} : Finset (ℤ × ℤ)) ⊆ box B := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h0
    · exact h1
  have hc := Finset.card_le_card this
  rw [Finset.card_pair (by decide)] at hc
  exact hc

/-- (Hexagon instance.)  For `A² = A − 1`, `B ≥ 1`, `φ_A` injective on `T_B`, and `P`
    of degree `< |T_B|` interpolating the low digit on `T_B`:  `P(AX) = A⁻¹(P(X) − X)`. -/
theorem hex_functional_equation {A : K} (hA : A ^ 2 = A - 1) (B : ℤ) (hB : 1 ≤ B)
    (hinj : Set.InjOn (phi A) (hex B)) (P : K[X]) (hdeg : P.degree < (hex B).card)
    (hinterp : ∀ v ∈ hex B, P.eval (phi A v) = (v.2 : K)) :
    P.comp (C A * X) = C A⁻¹ * (P - X) := by
  have hA' : A ^ 2 = (1 : ℤ) * A - 1 := by rw [hA]; push_cast; ring
  exact functional_equation hA' (hex B) (fun v hv => (hex_rot_iff B v).mpr hv)
    (two_le_card_hex B hB) hinj P hdeg hinterp

/-- (Theorem "Order-six character filter", from interpolation on the hexagon.)
    Support `{1} ∪ {k ≡ 5 (mod 6)}` and `c₁ = 1/(1 − A²)`, with `2 ≠ 0 ≠ 3`. -/
theorem hex_support {A : K} (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (B : ℤ) (hB : 1 ≤ B)
    (hinj : Set.InjOn (phi A) (hex B)) (P : K[X]) (hdeg : P.degree < (hex B).card)
    (hinterp : ∀ v ∈ hex B, P.eval (phi A v) = (v.2 : K)) :
    (∀ k, k ≠ 1 → k % 6 ≠ 5 → P.coeff k = 0) ∧ P.coeff 1 = (1 - A ^ 2)⁻¹ := by
  obtain ⟨h6, hord⟩ := OrderSix.order_six_exact hA h2 h3
  have hA' : A ^ 2 = (1 : ℤ) * A - 1 := by rw [hA]; push_cast; ring
  exact order_r_support hA' h6 hord (by norm_num) (hex B)
    (fun v hv => (hex_rot_iff B v).mpr hv) (two_le_card_hex B hB) hinj P hdeg hinterp

/-- The factored form `P = c₁X + X⁵Q(X⁶)` from interpolation on the hexagon. -/
theorem hex_factored {A : K} (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (B : ℤ) (hB : 1 ≤ B)
    (hinj : Set.InjOn (phi A) (hex B)) (P : K[X]) (hdeg : P.degree < (hex B).card)
    (hinterp : ∀ v ∈ hex B, P.eval (phi A v) = (v.2 : K)) :
    ∃ Q : K[X], P = C (1 - A ^ 2)⁻¹ * X + X ^ 5 * expand K 6 Q ∧
      Q.natDegree ≤ (P.natDegree - 5) / 6 := by
  obtain ⟨h6, hord⟩ := OrderSix.order_six_exact hA h2 h3
  have hA' : A ^ 2 = (1 : ℤ) * A - 1 := by rw [hA]; push_cast; ring
  exact order_r_factored hA' h6 hord (by norm_num) (hex B)
    (fun v hv => (hex_rot_iff B v).mpr hv) (two_le_card_hex B hB) hinj P hdeg hinterp

/-- (Box instance.)  For `A² = −1`, `B ≥ 1`, `φ_A` injective on `[−B,B]²`, and `P` of
    degree `< (2B+1)²` interpolating the low digit on the box:
    `P(AX) = A⁻¹(P(X) − X)`. -/
theorem box_functional_equation {A : K} (hA : A ^ 2 = -1) (B : ℤ) (hB : 1 ≤ B)
    (hinj : Set.InjOn (phi A) (box B)) (P : K[X]) (hdeg : P.degree < (box B).card)
    (hinterp : ∀ v ∈ box B, P.eval (phi A v) = (v.2 : K)) :
    P.comp (C A * X) = C A⁻¹ * (P - X) := by
  have hA' : A ^ 2 = (0 : ℤ) * A - 1 := by rw [hA]; push_cast; ring
  exact functional_equation hA' (box B) (fun v hv => (box_rot_iff B v).mpr hv)
    (two_le_card_box B hB) hinj P hdeg hinterp

/-- (Theorem "Order-four character filter", from interpolation on the box.)
    Support `{1} ∪ {k ≡ 3 (mod 4)}` and `c₁ = 1/(1 − A²) = 1/2`. -/
theorem box_support {A : K} (hA : A ^ 2 = -1) (h2 : (2 : K) ≠ 0) (B : ℤ) (hB : 1 ≤ B)
    (hinj : Set.InjOn (phi A) (box B)) (P : K[X]) (hdeg : P.degree < (box B).card)
    (hinterp : ∀ v ∈ box B, P.eval (phi A v) = (v.2 : K)) :
    (∀ k, k ≠ 1 → k % 4 ≠ 3 → P.coeff k = 0) ∧ P.coeff 1 = 2⁻¹ := by
  obtain ⟨h4, hord⟩ := OrderR.order_four_exact hA h2
  have hA' : A ^ 2 = (0 : ℤ) * A - 1 := by rw [hA]; push_cast; ring
  obtain ⟨hs, hc⟩ := order_r_support hA' h4 hord (by norm_num) (box B)
    (fun v hv => (box_rot_iff B v).mpr hv) (two_le_card_box B hB) hinj P hdeg hinterp
  refine ⟨hs, ?_⟩
  rw [hc, hA]; norm_num

end Instances

end Interpolation
