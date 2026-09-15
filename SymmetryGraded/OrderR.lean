/-
  OrderR.lean

  Formal verification (Lean 4 + Mathlib) of the unified order-`r` statements of

    "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping"

  (Theorem "Unified order-r functional equation" / Corollary "Support of the
  order-r filter"), for a radix `A` of *exact* order `r ≥ 3` in a field `K`.
  Exact order is expressed by the two hypotheses
      `hAr  : A ^ r = 1`      and      `hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1`
  (equivalently `orderOf A = r`, see `exact_order_of_orderOf`).  With no unproved placeholders:

  * `inv_eq_pow_pred`, `pow_eq_inv_iff`, `filter_factor_zero_iff`
        `A⁻¹ = A^(r−1)` and `Aᵏ − A⁻¹ = 0 ↔ k ≡ r − 1 (mod r)`.

  * `A_sub_inv_ne_zero`
        `A ≠ A⁻¹` for `r ≥ 3`.

  * `order_r_filter_coeff`, `order_r_filter`
        (Corollary "Support of the order-r filter")
        The covariance `cₖ·Aᵏ = A⁻¹·cₖ − A⁻¹·[k=1]` (coefficientwise
        `P(AX) = A⁻¹(P(X) − X)`) forces `c₁ = A⁻¹/(A⁻¹ − A) = 1/(1 − A²)` and
        `cₖ = 0` unless `k = 1` or `k ≡ r − 1 (mod r)`.

  * `sparse_factor`, `factored_form_poly`
        `P = c₁·X + X^(r−1)·Q(X^r)` with `natDegree Q ≤ (natDegree P − (r−1))/r`.

  * `isotypic_support` (Lemma "Character grading is degree reduction")
        `σ_A P = A^s P` forces `supp P ⊆ {k ≡ s (mod r)}`.

  * Instance `r = 4`: `order_four_exact`, `order_four_agrees` — the `r = 4`
    specialization reproduces `OrderFour.order_four_filter_coeff` (with
    `c₁ = 1/2`).  The `r = 6` instance is checked in `OrderSix.lean`.
-/
import Mathlib
import SymmetryGraded.OrderFour
import SymmetryGraded.Character

namespace OrderR

open Polynomial

/-! ## 1. Exact order `r` and the inverse -/
section Field
variable {K : Type*} [Field K] {A : K} {r : ℕ}

/-- If `orderOf A = r` then `A` has exact order `r` in the sense used here. -/
theorem exact_order_of_orderOf (h : orderOf A = r) :
    A ^ r = 1 ∧ ∀ j, 0 < j → j < r → A ^ j ≠ 1 := by
  refine ⟨h ▸ pow_orderOf_eq_one A, ?_⟩
  intro j hj hjr hpow
  have := orderOf_le_of_pow_eq_one hj hpow
  omega

/-- `A⁻¹ = A^(r−1)` for `A^r = 1`, `r ≥ 1`. -/
theorem inv_eq_pow_pred (hAr : A ^ r = 1) (hr : 1 ≤ r) : A⁻¹ = A ^ (r - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel hr, hAr]

/-- `A ≠ 0` for `A^r = 1`, `r ≥ 1`. -/
theorem A_ne_zero (hAr : A ^ r = 1) (hr : 1 ≤ r) : A ≠ 0 := by
  intro h; rw [h, zero_pow (by omega)] at hAr; exact zero_ne_one hAr

/-- `Aᵏ = A⁻¹ ↔ k ≡ r − 1 (mod r)` for `A` of exact order `r ≥ 1`. -/
theorem pow_eq_inv_iff (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 1 ≤ r) (k : ℕ) : A ^ k = A⁻¹ ↔ k % r = r - 1 := by
  have hr0 : r ≠ 0 := by omega
  rw [inv_eq_pow_pred hAr hr, OrderFour.Character.pow_mod_order hAr hr0 k]
  constructor
  · intro h
    by_contra hne
    have hlt : k % r < r := Nat.mod_lt _ (by omega)
    have hlt' : k % r + 1 < r := by omega
    apply hord (k % r + 1) (by omega) hlt'
    rw [pow_succ, h, ← pow_succ, Nat.sub_add_cancel hr, hAr]
  · intro h; rw [h]

/-- The order-`r` character filter: `Aᵏ − A⁻¹ = 0 ↔ k ≡ r − 1 (mod r)`. -/
theorem filter_factor_zero_iff (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 1 ≤ r) (k : ℕ) : A ^ k - A⁻¹ = 0 ↔ k % r = r - 1 := by
  rw [sub_eq_zero]; exact pow_eq_inv_iff hAr hord hr k

/-- For `r ≥ 3`, `A ≠ A⁻¹` (an element of exact order `≥ 3` is not an involution). -/
theorem A_sub_inv_ne_zero (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 3 ≤ r) : A - A⁻¹ ≠ 0 := by
  intro h
  have hA0 : A ≠ 0 := A_ne_zero hAr (by omega)
  have h2 : A ^ 2 = 1 := by
    have h' : A = A⁻¹ := by linear_combination h
    calc A ^ 2 = A * A := by ring
      _ = A * A⁻¹ := by rw [← h']
      _ = 1 := mul_inv_cancel₀ hA0
  exact hord 2 (by norm_num) (by omega) h2

/-- `1 − A² ≠ 0` for `r ≥ 3`. -/
theorem one_sub_sq_ne_zero (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 3 ≤ r) : 1 - A ^ 2 ≠ 0 := by
  intro h; exact hord 2 (by norm_num) (by omega) (by linear_combination -h)

/-! ## 2. Corollary "Support of the order-r filter" (coefficient form)

The functional equation `P(AX) = A⁻¹(P(X) − X)` reads coefficientwise
`cₖ·Aᵏ = A⁻¹·cₖ − A⁻¹·[k=1]`, i.e. `(Aᵏ − A⁻¹)·cₖ = −A⁻¹·[k=1]`. -/

/-- The unified order-`r` filter: `cₖ = 0` unless `k = 1` or `k ≡ r−1 (mod r)`, and
    `c₁ = A⁻¹/(A⁻¹ − A) = 1/(1 − A²)`. -/
theorem order_r_filter_coeff (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 3 ≤ r) (c : ℕ → K)
    (hfe : ∀ k, c k * A ^ k = A⁻¹ * c k - A⁻¹ * (if k = 1 then 1 else 0)) :
    (∀ k, k ≠ 1 → k % r ≠ r - 1 → c k = 0) ∧ c 1 = A⁻¹ / (A⁻¹ - A) ∧
      c 1 = (1 - A ^ 2)⁻¹ := by
  have hfac : ∀ k, (A ^ k - A⁻¹) * c k = -(A⁻¹ * (if k = 1 then 1 else 0)) := by
    intro k; linear_combination hfe k
  have hne := A_sub_inv_ne_zero hAr hord hr
  have hA0 : A ≠ 0 := A_ne_zero hAr (by omega)
  have hAinv : A * A⁻¹ = 1 := mul_inv_cancel₀ hA0
  refine ⟨?_, ?_, ?_⟩
  · intro k hk1 hkr
    have h := hfac k
    rw [if_neg hk1, mul_zero, neg_zero] at h
    refine (mul_eq_zero.mp h).resolve_left ?_
    intro h0
    exact hkr ((filter_factor_zero_iff hAr hord (by omega) k).mp h0)
  · have h := hfac 1
    rw [if_pos rfl, mul_one, pow_one] at h
    have hne' : A⁻¹ - A ≠ 0 := by intro h'; exact hne (by linear_combination -h')
    rw [eq_div_iff hne']; linear_combination -h
  · have h := hfac 1
    rw [if_pos rfl, mul_one, pow_one] at h
    apply eq_inv_of_mul_eq_one_left
    -- multiply `(A − A⁻¹)c₁ = −A⁻¹` by `A`:  `(A² − 1)c₁ = −1`
    linear_combination -A * h + (1 - c 1) * hAinv

/-- Polynomial form: `P(AX) = A⁻¹·(P(X) − X)` forces the support into
    `{1} ∪ {k ≡ r − 1 (mod r)}` and `c₁ = A⁻¹/(A⁻¹ − A) = 1/(1 − A²)`. -/
theorem order_r_filter (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 3 ≤ r) (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) :
    (∀ k, k ≠ 1 → k % r ≠ r - 1 → P.coeff k = 0) ∧ P.coeff 1 = A⁻¹ / (A⁻¹ - A) ∧
      P.coeff 1 = (1 - A ^ 2)⁻¹ := by
  apply order_r_filter_coeff hAr hord hr P.coeff
  intro k
  have hco := congrArg (fun p : K[X] => p.coeff k) hfe
  simp only [OrderFour.coeff_comp_C_mul_X, coeff_C_mul, coeff_sub] at hco
  by_cases hk : k = 1
  · subst hk; rw [coeff_X_one] at hco; rw [if_pos rfl]; linear_combination hco
  · rw [if_neg hk]
    have hz : (X : K[X]).coeff k = 0 := by rw [coeff_X]; exact if_neg (by omega)
    rw [hz, sub_zero] at hco
    linear_combination hco

/-- The monomial support of `P` is contained in `{1} ∪ {k : k ≡ r − 1 (mod r)}`. -/
theorem support_subset (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 3 ≤ r) (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) :
    ∀ k ∈ P.support, k = 1 ∨ k % r = r - 1 := by
  intro k hk
  by_contra hcon
  rw [not_or] at hcon
  exact (Polynomial.mem_support_iff.mp hk)
    ((order_r_filter hAr hord hr P hfe).1 k hcon.1 hcon.2)

/-! ## 3. The factored form `P = c₁X + X^(r−1)·Q(X^r)` -/

/-- Generic sparse factoring: if `P.coeff 1 = c₁` and every exponent in the support
    is `1` or `≡ r − 1 (mod r)`, then `P = c₁·X + X^(r−1)·Q(X^r)` for the polynomial
    `Q = Σ_j c_{rj + r − 1} Y^j`, with `natDegree Q ≤ (natDegree P − (r−1))/r`.
    (`Q(X^r)` is Mathlib's `expand K r Q`.) -/
theorem sparse_factor (hr : 3 ≤ r) (P : K[X]) (c₁ : K) (hc1 : P.coeff 1 = c₁)
    (hsupp : ∀ k ∈ P.support, k = 1 ∨ k % r = r - 1) :
    ∃ Q : K[X], P = C c₁ * X + X ^ (r - 1) * expand K r Q ∧
      Q.natDegree ≤ (P.natDegree - (r - 1)) / r := by
  have hr0 : 0 < r := by omega
  set Q : K[X] := ∑ j ∈ Finset.range (P.natDegree + 1),
      C (P.coeff (r * j + (r - 1))) * X ^ j with hQ
  have hQc : ∀ j, Q.coeff j = P.coeff (r * j + (r - 1)) := by
    intro j
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases hj : j < P.natDegree + 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; rw [if_neg (Ne.symm hb), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · rw [Finset.sum_eq_zero]
      · symm
        apply coeff_eq_zero_of_natDegree_lt
        have : r * j ≥ j := Nat.le_mul_of_pos_left j hr0
        omega
      · intro b hb
        rw [Finset.mem_range] at hb
        rw [if_neg (by omega), mul_zero]
  refine ⟨Q, ?_, ?_⟩
  · ext k
    rw [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow_mul', coeff_expand hr0, hQc]
    by_cases hk1 : k = 1
    · subst hk1
      rw [if_pos rfl, if_neg (by omega)]
      simp [hc1]
    · rw [if_neg (fun h => hk1 h.symm), mul_zero, zero_add]
      by_cases hkr : k % r = r - 1
      · have hle : r - 1 ≤ k := by
          have := Nat.mod_le k r; omega
        rw [if_pos hle]
        have hdiv : k - (r - 1) = r * (k / r) := by
          have := Nat.div_add_mod k r; omega
        have hd : r ∣ k - (r - 1) := ⟨k / r, hdiv⟩
        rw [if_pos hd, hdiv, Nat.mul_div_cancel_left _ hr0]
        congr 1
        have := Nat.div_add_mod k r; omega
      · have hP : P.coeff k = 0 := by
          by_contra hne
          rcases hsupp k (mem_support_iff.mpr hne) with h | h
          · exact hk1 h
          · exact hkr h
        rw [hP]
        split_ifs with hle hd
        · exfalso
          obtain ⟨m, hm⟩ := hd
          apply hkr
          have hk : k = r * m + (r - 1) := by omega
          rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        · rfl
        · rfl
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hQc]
    apply coeff_eq_zero_of_natDegree_lt
    obtain ⟨q, s, hs, hqs⟩ : ∃ q s, s < r ∧ P.natDegree - (r - 1) = r * q + s :=
      ⟨(P.natDegree - (r - 1)) / r, (P.natDegree - (r - 1)) % r,
        Nat.mod_lt _ hr0, (Nat.div_add_mod _ r).symm⟩
    have hq : (P.natDegree - (r - 1)) / r = q := by
      rw [hqs, Nat.mul_add_div hr0, Nat.div_eq_of_lt hs, add_zero]
    rw [hq] at hN
    have h1 : r * (q + 1) ≤ r * N := Nat.mul_le_mul_left r hN
    rw [mul_add, mul_one] at h1
    omega

/-- (Corollary "Support of the order-r filter", factored form.)  From the functional
    equation `P(AX) = A⁻¹(P(X) − X)`:  `P = c₁·X + X^(r−1)·Q(X^r)` with
    `c₁ = 1/(1 − A²)` and `natDegree Q ≤ (natDegree P − (r − 1))/r`. -/
theorem factored_form_poly (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 3 ≤ r) (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) :
    ∃ Q : K[X], P = C (1 - A ^ 2)⁻¹ * X + X ^ (r - 1) * expand K r Q ∧
      Q.natDegree ≤ (P.natDegree - (r - 1)) / r := by
  obtain ⟨hsupp, -, hc1⟩ := order_r_filter hAr hord hr P hfe
  exact sparse_factor hr P _ hc1 (support_subset hAr hord hr P hfe)

/-! ## 4. Lemma "Character grading is degree reduction" (isotypic support) -/

/-- If `σ_A P = A^s·P` coefficientwise (`Aᵏ·cₖ = A^s·cₖ`) for `A` of exact order `r`,
    then `cₖ = 0` unless `k ≡ s (mod r)`.  This generalizes the monomial support
    constraint of `Character.lean` to an exact-order hypothesis. -/
theorem isotypic_support (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 1 ≤ r) (s : ℕ) (c : ℕ → K) (hcov : ∀ k, A ^ k * c k = A ^ s * c k)
    (k : ℕ) (hk : k % r ≠ s % r) : c k = 0 := by
  have hr0 : r ≠ 0 := by omega
  have h : (A ^ k - A ^ s) * c k = 0 := by linear_combination hcov k
  refine (mul_eq_zero.mp h).resolve_left ?_
  intro h0
  rw [sub_eq_zero, OrderFour.Character.pow_mod_order hAr hr0 k,
    OrderFour.Character.pow_mod_order hAr hr0 s] at h0
  -- `A^(k%r) = A^(s%r)` with both exponents `< r` forces equality of exponents
  have hlt1 : k % r < r := Nat.mod_lt _ (by omega)
  have hlt2 : s % r < r := Nat.mod_lt _ (by omega)
  have hA0 : A ≠ 0 := A_ne_zero hAr hr
  rcases lt_or_gt_of_ne hk with hlt | hlt
  · -- k%r < s%r: A^(s%r - k%r) = 1
    apply hord (s % r - k % r) (by omega) (by omega)
    have : A ^ (s % r) = A ^ (k % r) * A ^ (s % r - k % r) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [this] at h0
    have hne : A ^ (k % r) ≠ 0 := pow_ne_zero _ hA0
    exact (mul_right_eq_self₀.mp h0.symm).resolve_right hne
  · apply hord (k % r - s % r) (by omega) (by omega)
    have : A ^ (k % r) = A ^ (s % r) * A ^ (k % r - s % r) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [this] at h0
    have hne : A ^ (s % r) ≠ 0 := pow_ne_zero _ hA0
    exact (mul_right_eq_self₀.mp h0).resolve_right hne

end Field

/-! ## 5. Instance `r = 4`: agreement with `OrderFour.lean` -/
section Four
variable {K : Type*} [Field K] {A : K}

/-- `A² = −1` with `2 ≠ 0` gives an element of exact order four. -/
theorem order_four_exact (hA : A ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    A ^ 4 = 1 ∧ ∀ j, 0 < j → j < 4 → A ^ j ≠ 1 := by
  refine ⟨OrderFour.sq_neg_one_pow_four hA, ?_⟩
  intro j hj hj4
  interval_cases j
  · rw [pow_one]; exact OrderFour.A_ne_one hA h2
  · rw [hA]; intro h; exact h2 (by linear_combination -h)
  · rw [OrderFour.pow_three hA]; intro h
    exact OrderFour.A_ne_neg_one hA h2 (by linear_combination -h)

/-- The order-four functional equation `(Aᵏ + A)cₖ = A·[k=1]` of `OrderFour.lean` is
    the `r = 4` instance of the unified covariance `cₖAᵏ = A⁻¹cₖ − A⁻¹[k=1]`
    (because `A⁻¹ = −A`). -/
theorem order_four_fe_equiv (hA : A ^ 2 = -1) (c : ℕ → K) (k : ℕ) :
    (A ^ k + A) * c k = (if k = 1 then A else 0) ↔
      c k * A ^ k = A⁻¹ * c k - A⁻¹ * (if k = 1 then 1 else 0) := by
  have hinv : A⁻¹ = -A := by
    apply inv_eq_of_mul_eq_one_right; linear_combination -hA
  rw [hinv]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> linear_combination h

/-- The unified theorem at `r = 4` reproduces `OrderFour.order_four_filter_coeff`:
    support in `{1} ∪ {k ≡ 3 (mod 4)}` and `c₁ = 1/(1 − A²) = 1/2`. -/
theorem order_four_agrees (hA : A ^ 2 = -1) (h2 : (2 : K) ≠ 0) (c : ℕ → K)
    (hfe : ∀ k, (A ^ k + A) * c k = if k = 1 then A else 0) :
    (∀ k, k ≠ 1 → k % 4 ≠ 3 → c k = 0) ∧ c 1 = 2⁻¹ := by
  obtain ⟨h4, hord⟩ := order_four_exact hA h2
  obtain ⟨hs, -, hc1⟩ := order_r_filter_coeff h4 hord (by norm_num) c
    (fun k => (order_four_fe_equiv hA c k).mp (hfe k))
  refine ⟨hs, ?_⟩
  rw [hc1, hA]; norm_num

end Four

end OrderR
