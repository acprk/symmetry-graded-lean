/-
  Radix.lean

  Formal verification (Lean 4 + Mathlib) of

    Proposition "Available orders by the residue class of p"
    (Appendix "Proofs for the scalar axis")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  The multiplicative group `(ZMod p)ˣ` is cyclic of order `p − 1`, so an element of
  exact order `r` exists iff `r ∣ p − 1`; the radices of orders `3, 4, 6` are the
  roots of `Φ₃ = Y² + Y + 1`, `Φ₄ = Y² + 1`, `Φ₆ = Y² − Y + 1`, and `A = −1` always
  has order two.  With no unproved placeholders:

  * `exists_orderOf_eq_iff`          `∃ u : (ZMod p)ˣ, orderOf u = r ↔ r ∣ p − 1`  (`r > 0`)
  * `exists_exact_order_iff`         the same for field elements in the `OrderR`
                                     convention `A^r = 1 ∧ ∀ 0 < j < r, A^j ≠ 1`
  * `dvd_pred_iff_mod`               `r ∣ p − 1 ↔ p % r = 1`  (`p ≥ 1`, `r ≥ 2`)
  * `exact_order_three_iff`, `exact_order_four_iff`, `exact_order_six_iff`
                                     `Φ_r(A) = 0 ↔ A` has exact order `r` (`r = 3, 4, 6`)
  * `root_Phi3_iff`, `root_Phi4_iff`, `root_Phi6_iff`
                                     a root of `Φ_r` exists in `ZMod p` iff `p ≡ 1 (mod r)`
                                     (for `r = 3, 6`: iff `p ≡ 1 (mod 3)`, `p > 3`)
  * `neg_one_exact_order_two`        `A = −1` has exact order two (`p > 2`)
  * `prime_mod_twelve`               `p > 3` prime ⟹ `p % 12 ∈ {1, 5, 7, 11}`
  * `available_orders_one/five/seven/eleven`
                                     the four rows of the table: available orders
                                     `{2,3,4,6}`, `{2,4}`, `{2,3,6}`, `{2}`
-/
import Mathlib
import SymmetryGraded.OrderR
import SymmetryGraded.OrderSix

namespace Radix

/-! ## 1. Existence of an element of order `r` in `(ZMod p)ˣ` -/
section Units
variable (p : ℕ) [hp : Fact p.Prime]

/-- `(ZMod p)ˣ` has `Nat.card = p − 1`. -/
lemma natCard_units : Nat.card (ZMod p)ˣ = p - 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units]

/-- In the cyclic group `(ZMod p)ˣ` of order `p − 1`, an element of order `r > 0`
    exists iff `r ∣ p − 1`. -/
theorem exists_orderOf_eq_iff (r : ℕ) (hr : 0 < r) :
    (∃ u : (ZMod p)ˣ, orderOf u = r) ↔ r ∣ p - 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ZMod.orderOf_units_dvd_card_sub_one u
  · intro hdvd
    haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp.out
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
    rw [natCard_units] at hg
    have hg0 : orderOf g ≠ 0 := by
      rw [hg]; have := hp.out.two_le; omega
    refine ⟨g ^ (orderOf g / r), ?_⟩
    exact orderOf_pow_orderOf_div hg0 (hg ▸ hdvd)

/-- Transfer to field elements: an `A : ZMod p` with `A^r = 1` and `A^j ≠ 1` for
    `0 < j < r` (the exact-order convention of `OrderR`) exists iff `r ∣ p − 1`. -/
theorem exists_exact_order_iff (r : ℕ) (hr : 0 < r) :
    (∃ A : ZMod p, A ^ r = 1 ∧ ∀ j, 0 < j → j < r → A ^ j ≠ 1) ↔ r ∣ p - 1 := by
  rw [← exists_orderOf_eq_iff p r hr]
  constructor
  · rintro ⟨A, hAr, hord⟩
    have hA0 : A ≠ 0 := OrderR.A_ne_zero hAr hr
    refine ⟨Units.mk0 A hA0, ?_⟩
    rw [← orderOf_units, Units.val_mk0]
    exact (orderOf_eq_iff hr).mpr ⟨hAr, fun m hm hm0 => hord m hm0 hm⟩
  · rintro ⟨u, hu⟩
    refine ⟨(u : ZMod p), ?_⟩
    have : orderOf (u : ZMod p) = r := by rw [orderOf_units, hu]
    exact OrderR.exact_order_of_orderOf this

end Units

/-! ## 2. Residue classes -/

/-- `r ∣ p − 1 ↔ p % r = 1` for `p ≥ 1` and `r ≥ 2`. -/
theorem dvd_pred_iff_mod {p r : ℕ} (hp : 1 ≤ p) (hr : 2 ≤ r) : r ∣ p - 1 ↔ p % r = 1 := by
  rw [← Nat.modEq_iff_dvd' hp]
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt (by omega : 1 < r)]
  exact eq_comm

section Char
variable (p : ℕ) [hp : Fact p.Prime]

lemma two_ne_zero' (h : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

lemma three_ne_zero' (h : 3 < p) : (3 : ZMod p) ≠ 0 := by
  intro h0
  have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

end Char

/-! ## 3. Cyclotomic roots and exact orders, over any field -/
section Cyclo
variable {K : Type*} [Field K] {A : K}

/-- `Φ₄(A) = A² + 1 = 0 ↔ A` has exact order four (with `2 ≠ 0`). -/
theorem exact_order_four_iff (h2 : (2 : K) ≠ 0) :
    A ^ 2 + 1 = 0 ↔ (A ^ 4 = 1 ∧ ∀ j, 0 < j → j < 4 → A ^ j ≠ 1) := by
  constructor
  · intro h
    exact OrderR.order_four_exact (by linear_combination h) h2
  · rintro ⟨h4, hord⟩
    have h2ne : A ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (hord 2 (by norm_num) (by norm_num))
    have : (A ^ 2 - 1) * (A ^ 2 + 1) = 0 := by linear_combination h4
    exact (mul_eq_zero.mp this).resolve_left h2ne

/-- `Φ₃(A) = A² + A + 1 = 0 ↔ A` has exact order three (with `3 ≠ 0`). -/
theorem exact_order_three_iff (h3 : (3 : K) ≠ 0) :
    A ^ 2 + A + 1 = 0 ↔ (A ^ 3 = 1 ∧ ∀ j, 0 < j → j < 3 → A ^ j ≠ 1) := by
  constructor
  · intro h
    refine ⟨by linear_combination (A - 1) * h, ?_⟩
    intro j hj hj3
    interval_cases j
    · rw [pow_one]; intro h1; subst h1; exact h3 (by linear_combination h)
    · intro h2
      -- A² = 1 and A² + A + 1 = 0 give A = −2, then 4 − 2 + 1 = 3 = 0
      have hA : A = -2 := by linear_combination h - h2
      subst hA; exact h3 (by linear_combination h)
  · rintro ⟨h3', hord⟩
    have h1ne : A - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hord 1 (by norm_num) (by norm_num))
    have : (A - 1) * (A ^ 2 + A + 1) = 0 := by linear_combination h3'
    exact (mul_eq_zero.mp this).resolve_left h1ne

/-- `Φ₆(A) = A² − A + 1 = 0` (i.e. `A² = A − 1`) `↔ A` has exact order six
    (with `2 ≠ 0`, `3 ≠ 0`). -/
theorem exact_order_six_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    A ^ 2 = A - 1 ↔ (A ^ 6 = 1 ∧ ∀ j, 0 < j → j < 6 → A ^ j ≠ 1) := by
  constructor
  · intro h; exact OrderSix.order_six_exact h h2 h3
  · rintro ⟨h6, hord⟩
    have h3ne : A ^ 3 - 1 ≠ 0 := sub_ne_zero.mpr (hord 3 (by norm_num) (by norm_num))
    have hcube : A ^ 3 + 1 = 0 := by
      have : (A ^ 3 - 1) * (A ^ 3 + 1) = 0 := by linear_combination h6
      exact (mul_eq_zero.mp this).resolve_left h3ne
    have hne : A + 1 ≠ 0 := by
      intro h
      have hA : A = -1 := by linear_combination h
      exact hord 2 (by norm_num) (by norm_num) (by rw [hA]; norm_num)
    have : (A + 1) * (A ^ 2 - A + 1) = 0 := by linear_combination hcube
    have := (mul_eq_zero.mp this).resolve_left hne
    linear_combination this

/-- `A = −1` has exact order two when `2 ≠ 0`. -/
theorem neg_one_exact_order_two (h2 : (2 : K) ≠ 0) :
    (-1 : K) ^ 2 = 1 ∧ ∀ j, 0 < j → j < 2 → (-1 : K) ^ j ≠ 1 := by
  refine ⟨by norm_num, ?_⟩
  intro j hj hj2
  interval_cases j
  rw [pow_one]; intro h; exact h2 (by linear_combination -h)

end Cyclo

/-! ## 4. Roots of `Φ_r` in `ZMod p` by the residue class of `p` -/
section ZModRoots
variable (p : ℕ) [hp : Fact p.Prime]

/-- A prime `p > 2` is odd. -/
lemma prime_odd (h : 2 < p) : p % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h2 | h2
  · omega
  · exact h2

/-- A root of `Φ₄` exists in `ZMod p` iff `p ≡ 1 (mod 4)` (`p > 2`). -/
theorem root_Phi4_iff (h : 2 < p) : (∃ A : ZMod p, A ^ 2 + 1 = 0) ↔ p % 4 = 1 := by
  rw [← dvd_pred_iff_mod (by omega) (by norm_num), ← exists_exact_order_iff p 4 (by norm_num)]
  exact exists_congr fun A => exact_order_four_iff (two_ne_zero' p h)

/-- A root of `Φ₃` exists in `ZMod p` iff `p ≡ 1 (mod 3)` (`p > 3`). -/
theorem root_Phi3_iff (h : 3 < p) : (∃ A : ZMod p, A ^ 2 + A + 1 = 0) ↔ p % 3 = 1 := by
  rw [← dvd_pred_iff_mod (by omega) (by norm_num), ← exists_exact_order_iff p 3 (by norm_num)]
  exact exists_congr fun A => exact_order_three_iff (three_ne_zero' p h)

/-- A root of `Φ₆` (`A² = A − 1`) exists in `ZMod p` iff `p ≡ 1 (mod 6)`, i.e. (for odd
    `p`) iff `p ≡ 1 (mod 3)` (`p > 3`). -/
theorem root_Phi6_iff (h : 3 < p) : (∃ A : ZMod p, A ^ 2 = A - 1) ↔ p % 3 = 1 := by
  have hodd : p % 2 = 1 := prime_odd p (by omega)
  have : (∃ A : ZMod p, A ^ 2 = A - 1) ↔ p % 6 = 1 := by
    rw [← dvd_pred_iff_mod (by omega) (by norm_num), ← exists_exact_order_iff p 6 (by norm_num)]
    exact exists_congr fun A => exact_order_six_iff (two_ne_zero' p (by omega)) (three_ne_zero' p h)
  rw [this]; omega

/-- A radix of order two always exists (`p > 2`): `A = −1`. -/
theorem exists_order_two (h : 2 < p) :
    ∃ A : ZMod p, A ^ 2 = 1 ∧ ∀ j, 0 < j → j < 2 → A ^ j ≠ 1 :=
  ⟨-1, neg_one_exact_order_two (two_ne_zero' p h)⟩

/-- A prime `p > 3` lies in one of the four classes `1, 5, 7, 11` modulo `12`. -/
theorem prime_mod_twelve (h : 3 < p) :
    p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
  have hodd : p % 2 = 1 := prime_odd p (by omega)
  have h3 : p % 3 ≠ 0 := by
    intro h0
    have := (Nat.dvd_of_mod_eq_zero h0)
    rcases hp.out.eq_one_or_self_of_dvd 3 this with h' | h' <;> omega
  omega

/-- "An order-`r` radix exists in `ZMod p`", in the `OrderR` convention. -/
def HasOrder (r : ℕ) : Prop :=
  ∃ A : ZMod p, A ^ r = 1 ∧ ∀ j, 0 < j → j < r → A ^ j ≠ 1

theorem hasOrder_iff (r : ℕ) (hr : 2 ≤ r) : HasOrder p r ↔ p % r = 1 := by
  unfold HasOrder
  rw [exists_exact_order_iff p r (by omega), dvd_pred_iff_mod hp.out.one_le hr]

/-- `p ≡ 1 (mod 12)`: orders `2, 3, 4, 6` are all available. -/
theorem available_orders_one (h : p % 12 = 1) :
    HasOrder p 2 ∧ HasOrder p 3 ∧ HasOrder p 4 ∧ HasOrder p 6 := by
  simp only [hasOrder_iff p _ (by norm_num : 2 ≤ 2), hasOrder_iff p _ (by norm_num : 2 ≤ 3),
    hasOrder_iff p _ (by norm_num : 2 ≤ 4), hasOrder_iff p _ (by norm_num : 2 ≤ 6)]
  omega

/-- `p ≡ 5 (mod 12)`: orders `2, 4` available, `3, 6` not. -/
theorem available_orders_five (h : p % 12 = 5) :
    HasOrder p 2 ∧ HasOrder p 4 ∧ ¬ HasOrder p 3 ∧ ¬ HasOrder p 6 := by
  simp only [hasOrder_iff p _ (by norm_num : 2 ≤ 2), hasOrder_iff p _ (by norm_num : 2 ≤ 3),
    hasOrder_iff p _ (by norm_num : 2 ≤ 4), hasOrder_iff p _ (by norm_num : 2 ≤ 6)]
  omega

/-- `p ≡ 7 (mod 12)`: orders `2, 3, 6` available, `4` not. -/
theorem available_orders_seven (h : p % 12 = 7) :
    HasOrder p 2 ∧ HasOrder p 3 ∧ HasOrder p 6 ∧ ¬ HasOrder p 4 := by
  simp only [hasOrder_iff p _ (by norm_num : 2 ≤ 2), hasOrder_iff p _ (by norm_num : 2 ≤ 3),
    hasOrder_iff p _ (by norm_num : 2 ≤ 4), hasOrder_iff p _ (by norm_num : 2 ≤ 6)]
  omega

/-- `p ≡ 11 (mod 12)`: only order `2` is available. -/
theorem available_orders_eleven (h : p % 12 = 11) :
    HasOrder p 2 ∧ ¬ HasOrder p 3 ∧ ¬ HasOrder p 4 ∧ ¬ HasOrder p 6 := by
  simp only [hasOrder_iff p _ (by norm_num : 2 ≤ 2), hasOrder_iff p _ (by norm_num : 2 ≤ 3),
    hasOrder_iff p _ (by norm_num : 2 ≤ 4), hasOrder_iff p _ (by norm_num : 2 ≤ 6)]
  omega

/-- The proposition in one statement: for `r ∈ {3, 4, 6}` an order-`r` radix exists iff
    `p ≡ 1 (mod r)`, and order two always exists (`p > 3`). -/
theorem available_orders (h : 3 < p) :
    HasOrder p 2 ∧ (HasOrder p 3 ↔ p % 3 = 1) ∧ (HasOrder p 4 ↔ p % 4 = 1) ∧
      (HasOrder p 6 ↔ p % 3 = 1) := by
  refine ⟨exists_order_two p (by omega), hasOrder_iff p 3 (by norm_num),
    hasOrder_iff p 4 (by norm_num), ?_⟩
  rw [hasOrder_iff p 6 (by norm_num)]
  have hodd : p % 2 = 1 := prime_odd p (by omega)
  omega

end ZModRoots

end Radix
