/-
  Stability.lean

  Formal verification (Lean 4 + Mathlib) of the two region-symmetry statements of

    Proposition "Oddness"                                     (Section "Preliminaries")
    Theorem "Classification of admissible orders by stable region", the box
                                       (Section "The scalar axis" / Appendix "Proofs for
                                        the scalar axis")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  Both are uniqueness-of-interpolation, respectively finite signed-permutation,
  arguments about the digit region rather than about the radix.  With no unproved
  placeholders:

  * `phi_neg`, `odd_interpolant`, `even_coeff_eq_zero`, `card_filter_odd_range`,
    `card_support_le`, `box_neg_stable`, `box_odd`
        (Proposition "Oddness")  a digit region stable under the half turn `v ↦ −v`
        forces `P_A(−X) = −P_A(X)`, hence all coefficients of even index vanish and
        `P_A` has at most `|S_A| / 2` nonzero coefficients — for `|S_A|` odd, as on the
        box where `|S_A| = (2B+1)²`, this is the paper's `(|S_A| − 1)/2`.
  * `box_rot_stable_iff`, `box_not_rot_stable_pm_one`, `sq_eq_one_iff_pm_one`,
    `box_stable_pm_one`, `box_stable_order_four`
        (Theorem "Classification of admissible orders by stable region", the box)
        the box `[−B, B]²`, `B ≥ 1`, is `M_A`-stable iff `τ = 0`, i.e. iff `A² = −1`,
        i.e. iff the exact order is four; and for `A² = 1`, i.e. `A = ±1`, the box is
        stable under `±I`, which induces multiplication by `A` as well.  Together these
        are the paper's "the box is stable iff `A² ≡ ±1 (mod p)`".
        Only the box half of the theorem is covered here: the hexagon as the region of
        order six is `OrderSix`, the exclusion of `r = 5` and `r ≥ 7` on a rank-two
        region is `Crystallographic`, and the existence of an order-`r` radix modulo `p`
        iff `p ≡ 1 (mod r)` is `Radix`.
-/
import Mathlib
import SymmetryGraded.Interpolation

namespace Stability

open Polynomial DigitLattice

variable {K : Type*} [Field K]

/-! ## 1. Proposition "Oddness" -/
section Oddness

/-- `φ_A(−v) = −φ_A(v)`. -/
theorem phi_neg (A : K) (v : ℤ × ℤ) : phi A (-v) = -(phi A v) := by
  simp only [phi, Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

/-- (Proposition "Oddness".)  If the digit region `T` is stable under the half turn
    `v ↦ −v` — as the box `[−B,B]²` is — and `φ_A` is injective on `T`, then the
    interpolant of the low digit is odd:  `P(−X) = −P(X)`.  The proof is uniqueness of
    the interpolant: `−P(−X)` has degree `< |T|` and interpolates the same data. -/
theorem odd_interpolant {A : K} {T : Finset (ℤ × ℤ)} (hneg : ∀ v ∈ T, -v ∈ T)
    (hinj : Set.InjOn (phi A) T) (P : K[X]) (hdeg : P.degree < T.card)
    (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K)) :
    P.comp (C (-1 : K) * X) = -P := by
  classical
  set R : K[X] := P.comp (C (-1 : K) * X) + P with hR
  have hcardim : (T.image (phi A)).card = T.card := Finset.card_image_of_injOn hinj
  have hRdeg : R.degree < (T.image (phi A)).card := by
    rw [hcardim, degree_lt_iff_coeff_zero]
    intro m hm
    have hPm : P.coeff m = 0 :=
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast hm))
    rw [hR, coeff_add, OrderFour.coeff_comp_C_mul_X, hPm]
    ring
  have hRzero : R = 0 := by
    apply eq_zero_of_degree_lt_of_eval_finset_eq_zero _ hRdeg
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have hval : P.eval ((-1 : K) * phi A v) = -(v.2 : K) := by
      have hne : (-1 : K) * phi A v = phi A (-v) := by rw [phi_neg]; ring
      rw [hne, hinterp _ (hneg v hv)]
      simp
    rw [hR, eval_add, eval_comp, eval_mul, eval_C, eval_X, hval, hinterp v hv]
    ring
  have := sub_eq_zero.mpr (neg_eq_of_add_eq_zero_left hRzero)
  linear_combination (norm := ring_nf) -this

/-- (Proposition "Oddness", coefficients.)  All coefficients of even index vanish. -/
theorem even_coeff_eq_zero {A : K} (h2 : (2 : K) ≠ 0) {T : Finset (ℤ × ℤ)}
    (hneg : ∀ v ∈ T, -v ∈ T) (hinj : Set.InjOn (phi A) T) (P : K[X])
    (hdeg : P.degree < T.card) (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K))
    {k : ℕ} (hk : k % 2 = 0) : P.coeff k = 0 := by
  have h := congrArg (fun q : K[X] => q.coeff k)
    (odd_interpolant hneg hinj P hdeg hinterp)
  simp only [OrderFour.coeff_comp_C_mul_X, coeff_neg] at h
  have heven : (-1 : K) ^ k = 1 := by
    obtain ⟨m, rfl⟩ := (Nat.even_iff.mpr hk).exists_two_nsmul _
    simp [pow_mul]
  rw [heven, one_mul] at h
  have : (2 : K) * P.coeff k = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left h2

/-- The number of odd indices below `n` is `n / 2`. -/
theorem card_filter_odd_range (n : ℕ) :
    ((Finset.range n).filter (fun k => k % 2 = 1)).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hn : n % 2 = 1
      · rw [if_pos hn, Finset.card_insert_of_notMem (by simp), ih]
        omega
      · rw [if_neg hn, ih]
        omega

/-- (Proposition "Oddness", term count.)  An odd interpolant of degree `< |S_A|` has at
    most `|S_A| / 2` nonzero coefficients; for `|S_A|` odd — as for the box, where
    `|S_A| = (2B+1)²` — this is `(|S_A| − 1)/2`. -/
theorem card_support_le {A : K} (h2 : (2 : K) ≠ 0) {T : Finset (ℤ × ℤ)}
    (hneg : ∀ v ∈ T, -v ∈ T) (hinj : Set.InjOn (phi A) T) (P : K[X])
    (hdeg : P.degree < T.card) (hinterp : ∀ v ∈ T, P.eval (phi A v) = (v.2 : K)) :
    P.support.card ≤ T.card / 2 := by
  classical
  have hsub : P.support ⊆ (Finset.range T.card).filter (fun k => k % 2 = 1) := by
    intro k hk
    have hne : P.coeff k ≠ 0 := mem_support_iff.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have hle : (k : WithBot ℕ) ≤ P.degree := le_degree_of_ne_zero hne
      have : (k : WithBot ℕ) < (T.card : WithBot ℕ) := lt_of_le_of_lt hle hdeg
      exact_mod_cast this
    · by_contra hodd
      exact hne (even_coeff_eq_zero h2 hneg hinj P hdeg hinterp (by omega))
  calc P.support.card ≤ ((Finset.range T.card).filter (fun k => k % 2 = 1)).card :=
        Finset.card_le_card hsub
    _ = T.card / 2 := card_filter_odd_range _

/-- The box is stable under the half turn, so the order-two instance of
    Proposition "Oddness" applies to every `B`-injective radix on the box. -/
theorem box_neg_stable (B : ℤ) : ∀ v ∈ box B, -v ∈ box B := by
  intro v hv
  rw [mem_box] at hv ⊢
  simpa using hv

/-- (Proposition "Oddness", box instance.)  For every `B`-injective radix `A`, the
    digit-extraction polynomial on the box is odd and has at most `(2B+1)² / 2`
    nonzero coefficients. -/
theorem box_odd {A : K} (h2 : (2 : K) ≠ 0) (B : ℤ) (hinj : Set.InjOn (phi A) (box B))
    (P : K[X]) (hdeg : P.degree < (box B).card)
    (hinterp : ∀ v ∈ box B, P.eval (phi A v) = (v.2 : K)) :
    P.comp (C (-1 : K) * X) = -P ∧ (∀ k, k % 2 = 0 → P.coeff k = 0) ∧
      P.support.card ≤ (box B).card / 2 :=
  ⟨odd_interpolant (box_neg_stable B) hinj P hdeg hinterp,
    fun _ hk => even_coeff_eq_zero h2 (box_neg_stable B) hinj P hdeg hinterp hk,
    card_support_le h2 (box_neg_stable B) hinj P hdeg hinterp⟩

end Oddness

/-! ## 2. Box stability and the classification of admissible orders -/
section BoxStability

/-- (Theorem "Classification of admissible orders by stable region", the box.)  For
    `B ≥ 1` the box `[−B, B]²` is `M_A`-stable exactly for the quarter turn `τ = 0`.
    This is the signed-permutation argument of the paper, made finite: a linear map of
    `ℤ²` preserves `‖·‖_∞` iff it is a signed permutation matrix, and
    `M_A = [[τ, 1], [−1, 0]]` is one iff `τ = 0`; for every other `τ` one of the two
    corners `(B, B)`, `(B, −B)` escapes, since `M_A(B, B) = (τB + B, −B)` and
    `M_A(B, −B) = (τB − B, −B)`. -/
theorem box_rot_stable_iff (B : ℤ) (hB : 1 ≤ B) (τ : ℤ) :
    (∀ v ∈ box B, rot τ v ∈ box B) ↔ τ = 0 := by
  constructor
  · intro h
    have hmem1 : ((B, B) : ℤ × ℤ) ∈ box B := by
      simp only [mem_box, abs_le]; omega
    have hmem2 : ((B, -B) : ℤ × ℤ) ∈ box B := by
      simp only [mem_box, abs_le]; omega
    have h1 : |τ * B + B| ≤ B := (mem_box.mp (h _ hmem1)).1
    have h2 : |τ * B + -B| ≤ B := (mem_box.mp (h _ hmem2)).1
    rw [abs_le] at h1 h2
    have hz : τ * B = 0 := le_antisymm (by linarith [h1.2]) (by linarith [h2.1])
    exact (mul_eq_zero.mp hz).resolve_right (by omega)
  · rintro rfl
    exact fun v hv => (box_rot_iff B v).mpr hv

/-- The box is not `M_A`-stable for `τ = ±1`: the order-three and order-six rotations
    move a corner out of the box. -/
theorem box_not_rot_stable_pm_one (B : ℤ) (hB : 1 ≤ B) {τ : ℤ} (hτ : τ = 1 ∨ τ = -1) :
    ¬ (∀ v ∈ box B, rot τ v ∈ box B) := by
  intro h
  have := (box_rot_stable_iff B hB τ).mp h
  rcases hτ with rfl | rfl <;> omega

/-- `A² = 1` in a field means `A = ±1`: the degenerate box-stable radices, of order at
    most two, for which multiplication by `A` preserves every symmetric support. -/
theorem sq_eq_one_iff_pm_one {A : K} (hA : A ^ 2 = 1) :
    A = 1 ∨ A = -1 := by
  have h : (A - 1) * (A + 1) = 0 := by linear_combination hA
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h)

/-- (Theorem "Classification of admissible orders by stable region", the degenerate half.)
    For `A² = 1` the box is stable under a lattice symmetry inducing multiplication by `A`:
    the identity for `A = 1` and the half turn `v ↦ −v` for `A = −1`.  Together with
    `box_stable_order_four` this is the paper's `A² ≡ ±1`, the `+1` side being realised by
    `±I` rather than by the companion rotation `M_A`. -/
theorem box_stable_pm_one {A : K} (hA : A ^ 2 = 1) (B : ℤ) :
    ∃ M : ℤ × ℤ → ℤ × ℤ, (∀ v ∈ box B, M v ∈ box B) ∧ ∀ v, phi A (M v) = A * phi A v := by
  rcases sq_eq_one_iff_pm_one hA with rfl | rfl
  · exact ⟨id, fun v hv => hv, fun v => by rw [id]; ring⟩
  · refine ⟨fun v => -v, box_neg_stable B, fun v => ?_⟩
    rw [phi_neg]
    ring

/-- (Theorem "Classification of admissible orders by stable region", radix form.)  A radix
    `A` of exact order `r ≥ 3` with `A² = τA − 1` whose companion rotation stabilises the
    box `[−B, B]²`, `B ≥ 1`, has `τ = 0`, hence `A² = −1` and `r = 4`.  Together with the
    degenerate case `A² = 1` of `sq_eq_one_iff_pm_one` this is the paper's
    "the box is `M_A`-stable iff `A² ≡ ±1`": order four is the only nontrivial
    box-stable order. -/
theorem box_stable_order_four {A : K} {τ : ℤ} {r : ℕ}
    (hA : A ^ 2 = τ * A - 1) (hAr : A ^ r = 1) (hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1)
    (hr : 3 ≤ r) {B : ℤ} (hB : 1 ≤ B) (hstab : ∀ v ∈ box B, rot τ v ∈ box B) :
    τ = 0 ∧ A ^ 2 = -1 ∧ r = 4 := by
  have hτ : τ = 0 := (box_rot_stable_iff B hB τ).mp hstab
  subst hτ
  have hA2 : A ^ 2 = -1 := by rw [hA]; push_cast; ring
  have h4 : A ^ 4 = 1 := by
    have : A ^ 4 = (A ^ 2) ^ 2 := by ring
    rw [this, hA2]; norm_num
  have hle : r ≤ 4 := by
    by_contra hc
    exact hord 4 (by norm_num) (by omega) h4
  have hne3 : r ≠ 3 := by
    intro h3
    subst h3
    apply hord 1 (by norm_num) (by norm_num)
    have hA4 : A ^ 4 = A := by
      have : A ^ 4 = A ^ 3 * A := by ring
      rw [this, hAr, one_mul]
    rw [pow_one, ← hA4, h4]
  exact ⟨rfl, hA2, by omega⟩

end BoxStability

end Stability
