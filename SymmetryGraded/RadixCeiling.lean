/-
  RadixCeiling.lean

  Formal verification (Lean 4 + Mathlib) of

    Corollary "Admissible radix orders"  (Section "Admissible orders")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping":
  if a radix `A` is intertwined with an integer `2 × 2` matrix `M` of finite order,
  `φ_A ∘ M = A · φ_A`, then `A^s = 1` whenever `M^s = 1`, so `ord A ∣ ord M` and the
  crystallographic restriction gives `ord A ∈ {1, 2, 3, 4, 6}`.  Conversely the
  companion matrices `M_A = [[τ,1],[−1,0]]`, `τ ∈ {−1, 0, 1}`, intertwine the roots of
  `Φ₃, Φ₄, Φ₆` and have exactly the order of the radix.  With no unproved placeholders:

  * `act`, `act_mul`, `act_pow`
        the action of `M ∈ M₂(ℤ)` on the digit lattice `ℤ²` and its compatibility
        with matrix multiplication and powers.
  * `phi_act_iterate`, `pow_eq_one_of_intertwine`
        `φ_A(Mⁿ v) = Aⁿ φ_A(v)`; evaluating at `v = (0,1)` gives `A^s = 1` from `M^s = 1`.
  * `orderOf_dvd_of_intertwine`, `orderOf_dvd_orderOf_matrix`
        `ord A ∣ s` and `ord A ∣ ord M`.
  * `orderOf_mem` (Corollary "Admissible radix orders")
        `ord A ∈ {1, 2, 3, 4, 6}`; `no_order_five_or_ge_seven`.
  * `MA_intertwines`, `orderOf_eq_six`, `orderOf_eq_four`, `orderOf_eq_three`
        the converse for the companion matrices: `M_A` intertwines every `A` with
        `A² = τA − 1`, and `ord A = ord M_A = 6, 4, 3` for `τ = 1, 0, −1`.

  The Latimer–MacDuffee uniqueness of `M` up to `GL₂(ℤ)`-conjugacy is not formalized.
-/
import Mathlib
import SymmetryGraded.Lattice
import SymmetryGraded.Crystallographic
import SymmetryGraded.OrderSix
import SymmetryGraded.Radix

namespace RadixCeiling

open DigitLattice

/-! ## 1. The action of `M₂(ℤ)` on the digit lattice -/
section Action

/-- The action of an integer `2 × 2` matrix on a digit pair, `v ↦ M v`. -/
def act (M : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) : ℤ × ℤ :=
  (M.mulVec ![v.1, v.2] 0, M.mulVec ![v.1, v.2] 1)

lemma vec_pair (w : Fin 2 → ℤ) : ![w 0, w 1] = w := by
  ext i; fin_cases i <;> rfl

@[simp] theorem act_one (v : ℤ × ℤ) : act 1 v = v := by
  simp [act]

theorem act_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (v : ℤ × ℤ) :
    act (M * N) v = act M (act N v) := by
  simp only [act, vec_pair, Matrix.mulVec_mulVec]

/-- `Mⁿ` acts as the `n`-fold iterate of the action of `M`. -/
theorem act_pow (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) (v : ℤ × ℤ) :
    act (M ^ n) v = (act M)^[n] v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih => rw [pow_succ, act_mul, Function.iterate_succ_apply, ih]

/-- The companion matrix `M_A = [[τ,1],[−1,0]]` acts as `rot τ`. -/
theorem act_MA (τ : ℤ) (v : ℤ × ℤ) : act (MA τ) v = rot τ v := by
  simp only [act, MA_mulVec, rot]; rfl

end Action

/-! ## 2. From an intertwining matrix of finite order to the order of the radix -/
section Ceiling
variable {R : Type*} [CommRing R]

/-- `φ_A(Mⁿ v) = Aⁿ · φ_A(v)` for an intertwining matrix `M`. -/
theorem phi_act_iterate (A : R) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hint : ∀ v, phi A (act M v) = A * phi A v) (n : ℕ) (v : ℤ × ℤ) :
    phi A ((act M)^[n] v) = A ^ n * phi A v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, ih, hint, pow_succ]; ring

/-- (Corollary "Admissible radix orders", first step.)  If `M^s = 1` and
    `φ_A ∘ M = A · φ_A`, then `A^s = 1`: evaluate the intertwining at `v = (0, 1)`,
    where `φ_A(0,1) = 1`. -/
theorem pow_eq_one_of_intertwine (A : R) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hint : ∀ v, phi A (act M v) = A * phi A v) {s : ℕ} (hM : M ^ s = 1) : A ^ s = 1 := by
  have h := phi_act_iterate A M hint s (0, 1)
  rw [← act_pow, hM, act_one] at h
  simpa [phi] using h.symm

variable {K : Type*} [Field K]

/-- `ord A ∣ s` for every `s` with `M^s = 1`. -/
theorem orderOf_dvd_of_intertwine (A : K) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hint : ∀ v, phi A (act M v) = A * phi A v) {s : ℕ} (hM : M ^ s = 1) :
    orderOf A ∣ s :=
  orderOf_dvd_of_pow_eq_one (pow_eq_one_of_intertwine A M hint hM)

/-- `ord A ∣ ord M`. -/
theorem orderOf_dvd_orderOf_matrix (A : K) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hint : ∀ v, phi A (act M v) = A * phi A v) : orderOf A ∣ orderOf M :=
  orderOf_dvd_of_intertwine A M hint (pow_orderOf_eq_one M)

/-- A positive divisor of an element of `{1, 2, 3, 4, 6}` lies in `{1, 2, 3, 4, 6}`. -/
lemma mem_of_dvd_mem {a m : ℕ} (ha : 0 < a) (hm : m ∈ ({1, 2, 3, 4, 6} : Finset ℕ))
    (hdvd : a ∣ m) : a ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
  have hle : a ≤ m := Nat.le_of_dvd (by omega) hdvd
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> interval_cases a <;> simp_all

/-- **Corollary (Admissible radix orders).**  Let `A ∈ K` and let `M ∈ M₂(ℤ)` satisfy
    `M^s = 1` for some `s ≥ 1` and `φ_A ∘ M = A · φ_A`.  Then
    `ord A ∈ {1, 2, 3, 4, 6}`. -/
theorem orderOf_mem (A : K) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hint : ∀ v, phi A (act M v) = A * phi A v) {s : ℕ} (hs : 1 ≤ s) (hM : M ^ s = 1) :
    orderOf A ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  have hpos : 0 < orderOf A :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨s, by omega, pow_eq_one_of_intertwine A M hint hM⟩)
  exact mem_of_dvd_mem hpos (Crystallographic.orderOf_mem M hs hM)
    (orderOf_dvd_orderOf_matrix A M hint)

/-- No radix intertwined with a finite-order integer matrix has order `5` or `≥ 7`. -/
theorem no_order_five_or_ge_seven (A : K) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hint : ∀ v, phi A (act M v) = A * phi A v) {s : ℕ} (hs : 1 ≤ s) (hM : M ^ s = 1)
    (h : orderOf A = 5 ∨ 7 ≤ orderOf A) : False := by
  have := orderOf_mem A M hint hs hM
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

/-- The exact-order form used throughout `OrderR`: `A^{ord A} = 1` and no smaller
    positive power is `1`, with `ord A ∈ {1, 2, 3, 4, 6}`. -/
theorem exact_order_mem (A : K) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hint : ∀ v, phi A (act M v) = A * phi A v) {s : ℕ} (hs : 1 ≤ s) (hM : M ^ s = 1) :
    orderOf A ∈ ({1, 2, 3, 4, 6} : Finset ℕ) ∧
      A ^ orderOf A = 1 ∧ ∀ j, 0 < j → j < orderOf A → A ^ j ≠ 1 :=
  ⟨orderOf_mem A M hint hs hM, OrderR.exact_order_of_orderOf rfl⟩

end Ceiling

/-! ## 3. The converse: the companion matrices realise the orders `3, 4, 6` -/
section Converse
variable {R : Type*} [CommRing R]

/-- `M_A` intertwines every `A` with `A² = τA − 1` (this is `DigitLattice.phi_rot`). -/
theorem MA_intertwines {A : R} {τ : ℤ} (hA : A ^ 2 = τ * A - 1) :
    ∀ v, phi A (act (MA τ) v) = A * phi A v := by
  intro v; rw [act_MA]; exact phi_rot hA v

variable {K : Type*} [Field K]

/-- `τ = 1`: a root of `Φ₆` has `ord A = 6 = ord M_A` (with `2, 3 ≠ 0`). -/
theorem orderOf_eq_six {A : K} (hA : A ^ 2 = A - 1) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    orderOf A = 6 ∧ orderOf (MA 1) = 6 := by
  refine ⟨?_, Crystallographic.MA_orderOf_six⟩
  obtain ⟨h6, hlt⟩ := (Radix.exact_order_six_iff h2 h3).mp hA
  exact (orderOf_eq_iff (by norm_num)).mpr ⟨h6, fun m hm hm0 => hlt m hm0 hm⟩

/-- `τ = 0`: a root of `Φ₄` has `ord A = 4 = ord M_A` (with `2 ≠ 0`). -/
theorem orderOf_eq_four {A : K} (hA : A ^ 2 = -1) (h2 : (2 : K) ≠ 0) :
    orderOf A = 4 ∧ orderOf (MA 0) = 4 := by
  refine ⟨?_, Crystallographic.MA_orderOf_four⟩
  obtain ⟨h4, hlt⟩ := (Radix.exact_order_four_iff h2).mp (by linear_combination hA)
  exact (orderOf_eq_iff (by norm_num)).mpr ⟨h4, fun m hm hm0 => hlt m hm0 hm⟩

/-- `τ = −1`: a root of `Φ₃` has `ord A = 3 = ord M_A` (with `3 ≠ 0`). -/
theorem orderOf_eq_three {A : K} (hA : A ^ 2 = -A - 1) (h3 : (3 : K) ≠ 0) :
    orderOf A = 3 ∧ orderOf (MA (-1)) = 3 := by
  refine ⟨?_, Crystallographic.MA_orderOf_three⟩
  obtain ⟨h3', hlt⟩ := (Radix.exact_order_three_iff h3).mp (by linear_combination hA)
  exact (orderOf_eq_iff (by norm_num)).mpr ⟨h3', fun m hm hm0 => hlt m hm0 hm⟩

/-- Round trip for `τ ∈ {−1, 0, 1}`: the companion matrix intertwines and has exactly
    the order of the radix, and the ceiling theorem applied to it returns that order. -/
theorem orderOf_eq_orderOf_MA {A : K} {τ : ℤ} (hA : A ^ 2 = τ * A - 1)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hτ : τ = -1 ∨ τ = 0 ∨ τ = 1) :
    orderOf A = orderOf (MA τ) ∧
      orderOf A ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rcases hτ with rfl | rfl | rfl <;> push_cast at hA
  · obtain ⟨h1, h2'⟩ := orderOf_eq_three (by linear_combination hA) h3
    rw [h1, h2']; decide
  · obtain ⟨h1, h2'⟩ := orderOf_eq_four (by linear_combination hA) h2
    rw [h1, h2']; decide
  · obtain ⟨h1, h2'⟩ := orderOf_eq_six (by linear_combination hA) h2 h3
    rw [h1, h2']; decide

end Converse

end RadixCeiling
