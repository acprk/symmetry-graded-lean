/-
  OrderSix.lean

  Formal verification (Lean 4 + Mathlib) of the order-six instance of

    "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping"

  This file mirrors `OrderFour.lean` (the `r = 4` instance) for the radix
  relation `A² = A − 1` (τ = 1), i.e. `Φ₆(A) = 0`.  With no unproved placeholders:

  * `pow_three_eq_neg_one`, `pow_six_eq_one`, `pow_mod_six`, `mul_one_sub`,
    `inv_eq_one_sub`, `inv_eq_pow_five`
        `A² = A − 1` forces `A³ = −1`, `A⁶ = 1`, `Aᵏ = A^(k mod 6)` and
        `A⁻¹ = 1 − A = A⁵`.                              (order-six action)

  * `stability_pointwise`
        `A·(ηA + λ) = (η+λ)A + (−η)`: multiplication by `A` is the sixth turn
        `(η, λ) ↦ (η+λ, −η)`.        (Lemma "Order-six stability of the hexagon", core)

  * `hexNorm`, `hexNorm_rot`
        `N(η,λ) = max{|η|,|λ|,|η+λ|}` satisfies `N ∘ M_A = N`, so every hexagon
        `T_B = {N ≤ B}` is `M_A`-stable.

  * `M6`, `M6_pow_three`, `M6_pow_six`, `M6_pow_ne_one`, `M4_pow_two`, `M4_pow_four`
        The integer matrices `M_A` for τ = 1 and τ = 0: `M6³ = −I`, `M6⁶ = I`,
        `M6ᵏ ≠ I` for `1 ≤ k ≤ 5` (so `ord M6 = 6`), and `M4² = −I`, `M4⁴ = I`.

  * `filter_factor_eq_zero`, `filter_factor_ne_zero`, `filter_factor_zero_iff`
        Over a field with `A² = A − 1` and `2 ≠ 0 ≠ 3`,
             `Aᵏ − A⁻¹ = 0  ↔  k ≡ 5 (mod 6)`.            (the "character filter")

  * `order_six_filter_coeff`, `order_six_filter`
        (Theorem "Order-six character filter")
        The functional equation `P(AX) = A⁻¹(P(X) − X)` forces every
        coefficient `cₖ` with `k ≠ 1`, `k ≢ 5 (mod 6)` to vanish, and
        `c₁ = A⁻¹/(A⁻¹ − A) = 1/(1 − A²)`.

  * `factored_form`, `factored_form_poly`
        `P = c₁·X + X⁵·Q(X⁶)` (coefficient statement and genuine polynomial
        statement with `natDegree Q ≤ (natDegree P − 5)/6`).

  * `coeff_even_eq_zero`, `odd_poly`
        (Oddness) all even-index coefficients vanish and `P(−X) = −P(X)`.

  * `card_v5`, `card_v5_mod`, `support_card_le`, `term_count_bound`
        (Term count) at most `(|S_A| − 1)/6 + 1` nonzero coefficients below
        `|S_A| = 6t + 1`.
-/
import Mathlib
import SymmetryGraded.OrderFour
import SymmetryGraded.OrderR

namespace OrderSix

open Polynomial

/-! ## 1. Order-six element:  A² = A − 1  ⟹  A³ = −1, A⁶ = 1 -/
section Ring
variable {R : Type*} [CommRing R] {A : R}

/-- `A² = A − 1` gives `A³ = −1`. -/
lemma pow_three_eq_neg_one (hA : A ^ 2 = A - 1) : A ^ 3 = -1 := by
  linear_combination (A + 1) * hA

/-- `A² = A − 1` gives `A⁶ = 1`: `A` has multiplicative order dividing 6. -/
lemma pow_six_eq_one (hA : A ^ 2 = A - 1) : A ^ 6 = 1 := by
  have h : A ^ 6 = (A ^ 3) ^ 2 := by ring
  rw [h, pow_three_eq_neg_one hA]; norm_num

/-- The order-six action is 6-periodic in the exponent: `Aᵏ = A^(k mod 6)`. -/
lemma pow_mod_six (hA : A ^ 2 = A - 1) (k : ℕ) : A ^ k = A ^ (k % 6) := by
  conv_lhs => rw [← Nat.div_add_mod k 6]
  rw [pow_add, pow_mul, pow_six_eq_one hA, one_pow, one_mul]

/-- `A·(1 − A) = 1`: the inverse of `A` is `1 − A` (ring version). -/
lemma mul_one_sub (hA : A ^ 2 = A - 1) : A * (1 - A) = 1 := by
  linear_combination -hA

/-- `A⁴ = −A` and `A⁵ = 1 − A`. -/
lemma pow_four_eq_neg (hA : A ^ 2 = A - 1) : A ^ 4 = -A := by
  have : A ^ 4 = A ^ 3 * A := by ring
  rw [this, pow_three_eq_neg_one hA]; ring

lemma pow_five_eq_one_sub (hA : A ^ 2 = A - 1) : A ^ 5 = 1 - A := by
  have : A ^ 5 = A ^ 3 * A ^ 2 := by ring
  rw [this, pow_three_eq_neg_one hA, hA]; ring

/-- Lemma "Order-six stability" (algebraic core).  Multiplication by an
    order-six radix `A` (`A² = A − 1`) is the sixth turn
    `(η, λ) ↦ (η + λ, −η)` on the digit lattice:
    `A·(ηA + λ) = (η+λ)A + (−η)`. -/
lemma stability_pointwise (hA : A ^ 2 = A - 1) (η l : R) :
    A * (η * A + l) = (η + l) * A + (-η) := by
  linear_combination η * hA

end Ring

/-! ## 2. The hexagon norm and the integer rotation matrices -/
section Lattice

/-- The hexagon norm `N(η,λ) = max{|η|, |λ|, |η+λ|}` on the digit lattice `ℤ²`. -/
def hexNorm (η l : ℤ) : ℤ := max |η| (max |l| |η + l|)

/-- `N ∘ M_A = N`: the sixth turn `(η,λ) ↦ (η+λ, −η)` permutes the three linear
    forms `η, λ, η+λ` up to sign, so it preserves the hexagon norm.  Hence every
    hexagon `T_B = {N ≤ B}` is mapped onto itself. -/
theorem hexNorm_rot (η l : ℤ) : hexNorm (η + l) (-η) = hexNorm η l := by
  unfold hexNorm
  have h : η + l + -η = l := by ring
  rw [h, abs_neg]
  simp only [abs_eq_max_neg]
  omega

/-- The sixth turn preserves membership in the hexagon `T_B`. -/
theorem hex_stable (B η l : ℤ) (h : hexNorm η l ≤ B) : hexNorm (η + l) (-η) ≤ B := by
  rwa [hexNorm_rot]

/-- The companion matrix of `Φ₆ = X² − X + 1`: `M_A = [[1,1],[−1,0]]` (τ = 1). -/
def M6 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; -1, 0]

/-- The companion matrix of `Φ₄ = X² + 1`: `M_A = [[0,1],[−1,0]]` (τ = 0). -/
def M4 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

lemma M6_sq : M6 ^ 2 = !![0, 1; -1, -1] := by
  rw [pow_two, M6, Matrix.mul_fin_two]; norm_num

/-- `M_A³ = −I` for the order-six rotation. -/
theorem M6_pow_three : M6 ^ 3 = -1 := by
  rw [pow_succ, M6_sq, M6, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- `M_A⁶ = I` for the order-six rotation. -/
theorem M6_pow_six : M6 ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, M6_pow_three]; simp

/-- `M_A` acts as the sixth turn `(η, λ) ↦ (η+λ, −η)` on column vectors. -/
theorem M6_mulVec (η l : ℤ) : M6.mulVec ![η, l] = ![η + l, -η] := by
  ext i; fin_cases i <;> simp [M6, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `M_Aᵏ ≠ I` for `k = 1, …, 5`: the order of `M_A` is exactly six. -/
theorem M6_pow_ne_one (k : ℕ) (hk1 : 1 ≤ k) (hk5 : k ≤ 5) : M6 ^ k ≠ 1 := by
  have h4 : M6 ^ 4 = -M6 := by rw [pow_succ, M6_pow_three]; simp
  have h5 : M6 ^ 5 = -(M6 ^ 2) := by
    rw [pow_succ, h4, pow_two]; simp
  interval_cases k
  · rw [pow_one]; intro h
    have := congrFun (congrFun h 0) 1
    simp [M6] at this
  · rw [M6_sq]; intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  · rw [M6_pow_three]; intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  · rw [h4]; intro h
    have := congrFun (congrFun h 0) 0
    simp [M6] at this
  · rw [h5, M6_sq]; intro h
    have := congrFun (congrFun h 0) 0
    simp at this

/-- The order of `M_A` (τ = 1) in `GL₂(ℤ)` is exactly six. -/
theorem orderOf_M6 : orderOf M6 = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) M6_pow_six
  intro p hp hpd
  have hp6 : p ∣ 6 := hpd
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hp6
  interval_cases p
  all_goals first
    | exact absurd hp6 (by decide)
    | exact absurd hp (by decide)
    | exact M6_pow_ne_one _ (by norm_num) (by norm_num)

/-- `M_A² = −I` for the order-four rotation (τ = 0). -/
theorem M4_pow_two : M4 ^ 2 = -1 := by
  rw [pow_two, M4, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- `M_A⁴ = I` for the order-four rotation. -/
theorem M4_pow_four : M4 ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, M4_pow_two]; simp

end Lattice

/-! ## 3. The character filter over a field with `2 ≠ 0 ≠ 3` -/
section Field
variable {K : Type*} [Field K] {A : K}

lemma A_ne_zero (hA : A ^ 2 = A - 1) : A ≠ 0 := by
  intro h; rw [h] at hA; norm_num at hA

lemma A_ne_one (hA : A ^ 2 = A - 1) : A ≠ 1 := by
  intro h; rw [h] at hA; norm_num at hA

lemma A_ne_two (hA : A ^ 2 = A - 1) (h3 : (3 : K) ≠ 0) : A ≠ 2 := by
  intro h; rw [h] at hA
  exact h3 (by linear_combination hA)

/-- `A⁻¹ = 1 − A` in a field. -/
lemma inv_eq_one_sub (hA : A ^ 2 = A - 1) : A⁻¹ = 1 - A :=
  inv_eq_of_mul_eq_one_right (mul_one_sub hA)

/-- `A⁻¹ = A⁵`. -/
lemma inv_eq_pow_five (hA : A ^ 2 = A - 1) : A⁻¹ = A ^ 5 := by
  rw [inv_eq_one_sub hA, pow_five_eq_one_sub hA]

/-- `A ≠ A⁻¹`: an order-six element is not an involution (needs `3 ≠ 0`). -/
lemma A_ne_inv (hA : A ^ 2 = A - 1) (h3 : (3 : K) ≠ 0) :
    A - A⁻¹ ≠ 0 := by
  rw [inv_eq_one_sub hA]
  intro h
  -- 2A = 1, so 4A² = 1 = 4A − 4, i.e. 3 = 0
  have h2A : (2 : K) * A = 1 := by linear_combination h
  exact h3 (by linear_combination -(2 * A - 1) * h2A + 4 * hA)

/-- The filter *passes* exactly the exponents `k ≡ 5 (mod 6)`: there the
    coefficient factor `Aᵏ − A⁻¹` vanishes. -/
lemma filter_factor_eq_zero (hA : A ^ 2 = A - 1) {k : ℕ} (hk : k % 6 = 5) :
    A ^ k - A⁻¹ = 0 := by
  rw [pow_mod_six hA, hk, inv_eq_pow_five hA, sub_self]

/-- The filter *kills* every other exponent: for `k ≢ 5 (mod 6)` the factor
    `Aᵏ − A⁻¹` is nonzero. -/
lemma filter_factor_ne_zero (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {k : ℕ} (hk : k % 6 ≠ 5) : A ^ k - A⁻¹ ≠ 0 := by
  rw [pow_mod_six hA, inv_eq_one_sub hA]
  have hlt : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases (show k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 by omega) with
    h0 | h1 | h2' | h3' | h4
  · -- k ≡ 0 : 1 − (1 − A) = A ≠ 0
    rw [h0, pow_zero]; intro h; exact A_ne_zero hA (by linear_combination h)
  · -- k ≡ 1 : A − (1 − A) = 2A − 1 ≠ 0
    rw [h1, pow_one]; intro h
    have := A_ne_inv hA h3
    rw [inv_eq_one_sub hA] at this; exact this h
  · -- k ≡ 2 : (A − 1) − (1 − A) = 2(A − 1) ≠ 0
    rw [h2', hA]; intro h
    have h' : (2 : K) * (A - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact h2 h''
    · exact A_ne_one hA (by linear_combination h'')
  · -- k ≡ 3 : −1 − (1 − A) = A − 2 ≠ 0
    rw [h3', pow_three_eq_neg_one hA]; intro h
    exact A_ne_two hA h3 (by linear_combination h)
  · -- k ≡ 4 : −A − (1 − A) = −1 ≠ 0
    rw [h4, pow_four_eq_neg hA]; intro h
    have : (1 : K) = 0 := by linear_combination -h
    exact one_ne_zero this

/-- The order-six character filter as an iff. -/
theorem filter_factor_zero_iff (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (k : ℕ) : A ^ k - A⁻¹ = 0 ↔ k % 6 = 5 := by
  constructor
  · intro h; by_contra hk; exact filter_factor_ne_zero hA h2 h3 hk h
  · exact filter_factor_eq_zero hA

/-- For `k = 1` the factor is nonzero: `A − A⁻¹ ≠ 0` (this is `r ≥ 3`). -/
theorem filter_factor_one_ne_zero (hA : A ^ 2 = A - 1) (h3 : (3 : K) ≠ 0) :
    A ^ 1 - A⁻¹ ≠ 0 := by
  rw [pow_one]; exact A_ne_inv hA h3

/-! ## 4. Theorem "Order-six character filter" (coefficient form)

The functional equation `P(AX) = A⁻¹·(P(X) − X)`, read off coefficient by
coefficient, is the hypothesis `hfe` below:
`cₖ·Aᵏ = A⁻¹·cₖ − A⁻¹·[k=1]`.  This is the self-contained heart of the theorem. -/

/-- Every coefficient off the support `{1} ∪ {k ≡ 5 (mod 6)}` vanishes, and the
    linear coefficient equals `c₁ = A⁻¹/(A⁻¹ − A) = 1/(1 − A²)`. -/
theorem order_six_filter_coeff (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (c : ℕ → K)
    (hfe : ∀ k, c k * A ^ k = A⁻¹ * c k - A⁻¹ * (if k = 1 then 1 else 0)) :
    (∀ k, k ≠ 1 → k % 6 ≠ 5 → c k = 0) ∧ c 1 = A⁻¹ / (A⁻¹ - A) ∧ c 1 = (1 - A ^ 2)⁻¹ := by
  have hfac : ∀ k, (A ^ k - A⁻¹) * c k = -(A⁻¹ * (if k = 1 then 1 else 0)) := by
    intro k; linear_combination hfe k
  refine ⟨?_, ?_, ?_⟩
  · intro k hk1 hk5
    have h := hfac k
    rw [if_neg hk1, mul_zero, neg_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (filter_factor_ne_zero hA h2 h3 hk5)
  · have h := hfac 1
    rw [if_pos rfl, mul_one, pow_one] at h
    have hne : A⁻¹ - A ≠ 0 := by
      intro h'; exact A_ne_inv hA h3 (by linear_combination -h')
    rw [eq_div_iff hne]; linear_combination -h
  · have h := hfac 1
    rw [if_pos rfl, mul_one, pow_one] at h
    have hA0 : A ≠ 0 := A_ne_zero hA
    have hne : 1 - A ^ 2 ≠ 0 := by
      rw [hA]; intro h'; exact A_ne_two hA h3 (by linear_combination -h')
    apply eq_inv_of_mul_eq_one_left
    have hAinv : A * A⁻¹ = 1 := mul_inv_cancel₀ hA0
    -- (A − A⁻¹)c₁ = −A⁻¹; multiply by A: (A² − 1)c₁ = −1
    linear_combination -A * h + (1 - c 1) * hAinv

/-! ## 5. Bridge to the genuine polynomial functional equation -/

/-- Theorem "Order-six character filter" (polynomial form).  If `P` satisfies
    `P(AX) = A⁻¹·(P(X) − X)`, then its support lies in `{1} ∪ {k ≡ 5 (mod 6)}`
    and `c₁ = A⁻¹/(A⁻¹ − A)`. -/
theorem order_six_filter (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) :
    (∀ k, k ≠ 1 → k % 6 ≠ 5 → P.coeff k = 0) ∧ P.coeff 1 = A⁻¹ / (A⁻¹ - A) ∧
      P.coeff 1 = (1 - A ^ 2)⁻¹ := by
  apply order_six_filter_coeff hA h2 h3 P.coeff
  intro k
  have hco := congrArg (fun p : K[X] => p.coeff k) hfe
  simp only [OrderFour.coeff_comp_C_mul_X, coeff_C_mul, coeff_sub] at hco
  by_cases hk : k = 1
  · subst hk; rw [coeff_X_one] at hco; rw [if_pos rfl]; linear_combination hco
  · rw [if_neg hk]
    have hz : (X : K[X]).coeff k = 0 := by rw [coeff_X]; exact if_neg (by omega)
    rw [hz, sub_zero] at hco
    linear_combination hco

/-- The monomial support of `P` is contained in `{1} ∪ {k : k ≡ 5 (mod 6)}`. -/
theorem support_subset (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) :
    ∀ k ∈ P.support, k = 1 ∨ k % 6 = 5 := by
  intro k hk
  by_contra hcon
  rw [not_or] at hcon
  exact (Polynomial.mem_support_iff.mp hk)
    ((order_six_filter hA h2 h3 P hfe).1 k hcon.1 hcon.2)

/-- (Factored form, coefficient statement.)  `c₁ = 1/(1 − A²)`, the coefficients
    at `k ≡ 5 (mod 6)` are free (they are the coefficients `q_j = c_{6j+5}` of `Q`),
    and every other coefficient vanishes: `P = c₁·X + X⁵·Q(X⁶)`. -/
theorem factored_form (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) (k : ℕ) :
    P.coeff k = if k = 1 then (1 - A ^ 2)⁻¹ else if k % 6 = 5 then P.coeff k else 0 := by
  obtain ⟨hsupp, -, hc1⟩ := order_six_filter hA h2 h3 P hfe
  split_ifs with h h'
  · rw [h]; exact hc1
  · rfl
  · exact hsupp k h h'

/-- (Theorem "Order-six character filter", factored form.)  There is a polynomial
    `Q` with `P = c₁·X + X⁵·Q(X⁶)` (`Q(X⁶)` is `expand K 6 Q`) and
    `natDegree Q ≤ (natDegree P − 5)/6`. -/
theorem factored_form_poly (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) :
    ∃ Q : K[X], P = C (1 - A ^ 2)⁻¹ * X + X ^ 5 * expand K 6 Q ∧
      Q.natDegree ≤ (P.natDegree - 5) / 6 := by
  obtain ⟨-, -, hc1⟩ := order_six_filter hA h2 h3 P hfe
  exact OrderR.sparse_factor (r := 6) (by norm_num) P _ hc1
    (fun k hk => by simpa using support_subset hA h2 h3 P hfe k hk)

/-! ## 6. Oddness -/

/-- (Oddness, coefficient form.)  Every even-index coefficient vanishes: the
    surviving exponents `1` and `6j + 5` are odd. -/
theorem coeff_even_eq_zero (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) (k : ℕ) (hk : k % 2 = 0) :
    P.coeff k = 0 :=
  (order_six_filter hA h2 h3 P hfe).1 k (by omega) (by omega)

/-- (Oddness, polynomial form.)  `P(−X) = −P(X)`. -/
theorem odd_poly (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (P : K[X]) (hfe : P.comp (C A * X) = C A⁻¹ * (P - X)) :
    P.comp (-X) = -P := by
  have hneg : (-X : K[X]) = C (-1) * X := by simp
  ext k
  rw [hneg, OrderFour.coeff_comp_C_mul_X, coeff_neg]
  rcases Nat.even_or_odd k with he | ho
  · rw [coeff_even_eq_zero hA h2 h3 P hfe k (Nat.even_iff.mp he)]; simp
  · rw [Odd.neg_one_pow ho]; ring

/-! ## 7. Term count -/

/-- Among the exponents `k < 6t + 1` exactly `t` satisfy `k ≡ 5 (mod 6)`
    (namely `5, 11, …, 6t − 1`). -/
theorem card_v5 (t : ℕ) :
    ((Finset.range (6 * t + 1)).filter (fun k => k % 6 = 5)).card = t := by
  induction t with
  | zero => decide
  | succ t ih =>
      have hstep :
          (Finset.range (6 * (t + 1) + 1)).filter (fun k => k % 6 = 5)
            = insert (6 * t + 5)
                ((Finset.range (6 * t + 1)).filter (fun k => k % 6 = 5)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        omega
      have hnot : 6 * t + 5 ∉
          (Finset.range (6 * t + 1)).filter (fun k => k % 6 = 5) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hstep, Finset.card_insert_of_notMem hnot, ih]

/-- General-`n` form: for `n ≡ 1 (mod 6)` (the hexagon has `|T_B| = 3B² + 3B + 1`
    and the box closure `|Ω_B| = 6B² + 6B + 1`, both `≡ 1 (mod 6)`), the number of
    exponents `k < n` with `k ≡ 5 (mod 6)` is `(n − 1)/6`. -/
theorem card_v5_mod {n : ℕ} (hn : n % 6 = 1) :
    ((Finset.range n).filter (fun k => k % 6 = 5)).card = (n - 1) / 6 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 6 * t + 1 := ⟨n / 6, by omega⟩
  rw [card_v5]; omega

/-- (Term count, upper bound.)  A coefficient sequence vanishing off
    `{1} ∪ {k ≡ 5 (mod 6)}` has at most `t + 1 = (|S_A| − 1)/6 + 1` nonzero
    entries below `|S_A| = 6t + 1`. -/
theorem support_card_le [DecidableEq K] (c : ℕ → K) (t : ℕ)
    (hc : ∀ k, k ≠ 1 → k % 6 ≠ 5 → c k = 0) :
    ((Finset.range (6 * t + 1)).filter (fun k => c k ≠ 0)).card ≤ t + 1 := by
  have hsub : (Finset.range (6 * t + 1)).filter (fun k => c k ≠ 0) ⊆
      insert 1 ((Finset.range (6 * t + 1)).filter (fun k => k % 6 = 5)) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    by_cases h1 : k = 1
    · exact Or.inl h1
    · by_cases h5 : k % 6 = 5
      · exact Or.inr ⟨hk.1, h5⟩
      · exact absurd (hc k h1 h5) hk.2
  calc ((Finset.range (6 * t + 1)).filter (fun k => c k ≠ 0)).card
      ≤ (insert 1 ((Finset.range (6 * t + 1)).filter
            (fun k => k % 6 = 5))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.range (6 * t + 1)).filter
            (fun k => k % 6 = 5)).card + 1 := Finset.card_insert_le _ _
    _ = t + 1 := by rw [card_v5]

/-- (Term count, end to end.)  Directly from the order-six functional equation:
    at most `(|S_A| − 1)/6 + 1` nonzero coefficients below `|S_A| = 6t + 1`. -/
theorem term_count_bound [DecidableEq K] (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (c : ℕ → K)
    (hfe : ∀ k, c k * A ^ k = A⁻¹ * c k - A⁻¹ * (if k = 1 then 1 else 0)) (t : ℕ) :
    ((Finset.range (6 * t + 1)).filter (fun k => c k ≠ 0)).card ≤ t + 1 :=
  support_card_le c t (order_six_filter_coeff hA h2 h3 c hfe).1

/-! ## 8. Agreement with the unified order-`r` theorem (`OrderR.lean`) -/

/-- `A² = A − 1` with `2 ≠ 0 ≠ 3` is an element of *exact* order six. -/
theorem order_six_exact (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    A ^ 6 = 1 ∧ ∀ j, 0 < j → j < 6 → A ^ j ≠ 1 := by
  refine ⟨pow_six_eq_one hA, ?_⟩
  intro j hj hj6
  interval_cases j
  · rw [pow_one]; exact A_ne_one hA
  · rw [hA]; intro h; exact A_ne_two hA h3 (by linear_combination h)
  · rw [pow_three_eq_neg_one hA]; intro h; exact h2 (by linear_combination -h)
  · rw [pow_four_eq_neg hA]; intro h
    exact h3 (by linear_combination (A - 2) * h + hA)
  · rw [pow_five_eq_one_sub hA]; intro h; exact A_ne_zero hA (by linear_combination -h)

/-- The unified theorem `OrderR.order_r_filter_coeff` at `r = 6` reproduces
    `order_six_filter_coeff`. -/
theorem order_six_agrees (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (c : ℕ → K)
    (hfe : ∀ k, c k * A ^ k = A⁻¹ * c k - A⁻¹ * (if k = 1 then 1 else 0)) :
    (∀ k, k ≠ 1 → k % 6 ≠ 5 → c k = 0) ∧ c 1 = A⁻¹ / (A⁻¹ - A) ∧ c 1 = (1 - A ^ 2)⁻¹ := by
  obtain ⟨h6, hord⟩ := order_six_exact hA h2 h3
  exact OrderR.order_r_filter_coeff h6 hord (by norm_num) c hfe

end Field

end OrderSix
