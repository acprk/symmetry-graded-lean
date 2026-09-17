/-
  NormSchedule.lean

  Formal verification (Lean 4 + Mathlib) of

    Proposition "Cost of the norm map" for an arbitrary slot degree `d`
    (Section "The Galois axis" / Appendix "Deferred proofs for the Galois axis")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  `Galois.doubling_schedule` covers `d = 2^ℓ` only.  The general case is the binary
  decomposition `d = Σ_j 2^{b_j}`: halving at even `d` and peeling one factor at odd `d`
  realises `Orb_d(x) = ∏_{i<d} φⁱ(x)` in at most `2⌈log₂ d⌉ ` products and as many
  automorphism applications, through the block splitting `Galois.orbProd_add`.
  With no unproved placeholders:

  * `orbSchedule`
        the schedule as a triple `(Orb_d(x), #products, #automorphisms)`; each recursion
        step performs exactly one product and one application of a power of `φ`.
  * `orbSteps`
        the step count of the schedule.
  * `orbSchedule_fst`
        correctness: the value computed is `Galois.orbProd φ d x`, for every `d`.
  * `orbSchedule_products`, `orbSchedule_automorphisms`
        both counts equal `orbSteps d`.
  * `log_two_pred_of_odd`, `orbSteps_le_two_mul_log`
        `orbSteps d ≤ 2·log₂ d` for `d ≥ 1`, by strong induction with the sharper
        even-`d` bound `orbSteps d + 1 ≤ 2·log₂ d` carried along.
  * `orbSchedule_cost_le`
        the proposition: correctness together with
        `#products, #automorphisms ≤ 2⌈log₂ d⌉`.
-/
import Mathlib
import SymmetryGraded.Doubling

namespace Galois

open Polynomial

/-! ## The general slot degree: the binary schedule -/
section Binary
variable {R : Type*} [CommRing R]

/-- The binary orbit-product schedule for an arbitrary length `d`, together with its
    cost.  The triple is `(Orb_d(x), #products, #automorphisms)`: at even `d` the
    length is halved by `Orb_{2m}(x) = Orb_m(x)·φ^m(Orb_m(x))`, at odd `d` one factor is
    peeled off by `Orb_{m+1}(x) = Orb_m(x)·φ^m(x)`.  Each step performs exactly one
    product and one application of a power of `φ`. -/
def orbSchedule (φ : R →+* R) (x : R) : ℕ → R × ℕ × ℕ
  | 0 => (1, 0, 0)
  | 1 => (x, 0, 0)
  | (d + 2) =>
      if (d + 2) % 2 = 0 then
        ((orbSchedule φ x ((d + 2) / 2)).1 *
            (φ ^ ((d + 2) / 2)) (orbSchedule φ x ((d + 2) / 2)).1,
          (orbSchedule φ x ((d + 2) / 2)).2.1 + 1,
          (orbSchedule φ x ((d + 2) / 2)).2.2 + 1)
      else
        ((orbSchedule φ x (d + 1)).1 * (φ ^ (d + 1)) x,
          (orbSchedule φ x (d + 1)).2.1 + 1,
          (orbSchedule φ x (d + 1)).2.2 + 1)
  decreasing_by
    · omega
    · omega

/-- The step count of the binary schedule. -/
def orbSteps : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (d + 2) => if (d + 2) % 2 = 0 then orbSteps ((d + 2) / 2) + 1 else orbSteps (d + 1) + 1
  decreasing_by
    · omega
    · omega

/-- (Proposition "Cost of the norm map", general `d`, correctness.)  The binary schedule
    computes the orbit product: its value is `Orb_d(x) = ∏_{i<d} φⁱ(x)`, for every `d`,
    not only for `d` a power of two.  The proof is the binary decomposition
    `d = Σ_j 2^{b_j}` read through `orbProd_add`. -/
theorem orbSchedule_fst (φ : R →+* R) (x : R) (d : ℕ) :
    (orbSchedule φ x d).1 = orbProd φ d x := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      match d with
      | 0 => simp [orbSchedule]
      | 1 => simp [orbSchedule]
      | (e + 2) =>
          rw [orbSchedule]
          by_cases hpar : (e + 2) % 2 = 0
          · rw [if_pos hpar, ih ((e + 2) / 2) (by omega)]
            have hsplit : e + 2 = (e + 2) / 2 + (e + 2) / 2 := by omega
            conv_rhs => rw [hsplit]
            rw [orbProd_add]
          · rw [if_neg hpar, ih (e + 1) (by omega)]
            have hs : orbProd φ (e + 2) x = orbProd φ (e + 1) x * (φ ^ (e + 1)) x :=
              orbProd_succ φ (e + 1) x
            rw [hs]

/-- The number of products of the binary schedule is `orbSteps d`. -/
theorem orbSchedule_products (φ : R →+* R) (x : R) (d : ℕ) :
    (orbSchedule φ x d).2.1 = orbSteps d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      match d with
      | 0 => simp [orbSchedule, orbSteps]
      | 1 => simp [orbSchedule, orbSteps]
      | (e + 2) =>
          rw [orbSchedule, orbSteps]
          by_cases hpar : (e + 2) % 2 = 0
          · rw [if_pos hpar, if_pos hpar, ih ((e + 2) / 2) (by omega)]
          · rw [if_neg hpar, if_neg hpar, ih (e + 1) (by omega)]

/-- The number of automorphism applications of the binary schedule is `orbSteps d`,
    the same as the number of products. -/
theorem orbSchedule_automorphisms (φ : R →+* R) (x : R) (d : ℕ) :
    (orbSchedule φ x d).2.2 = orbSteps d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      match d with
      | 0 => simp [orbSchedule, orbSteps]
      | 1 => simp [orbSchedule, orbSteps]
      | (e + 2) =>
          rw [orbSchedule, orbSteps]
          by_cases hpar : (e + 2) % 2 = 0
          · rw [if_pos hpar, if_pos hpar, ih ((e + 2) / 2) (by omega)]
          · rw [if_neg hpar, if_neg hpar, ih (e + 1) (by omega)]

/-- `log₂` is unchanged when an odd number `≥ 3` is decreased by one. -/
theorem log_two_pred_of_odd {d : ℕ} (hd : 3 ≤ d) (hpar : d % 2 = 1) :
    Nat.log 2 (d - 1) = Nat.log 2 d := by
  have hk : 1 ≤ Nat.log 2 d := Nat.log_pos (by norm_num) (by omega)
  have hle : 2 ^ Nat.log 2 d ≤ d := Nat.pow_log_le_self 2 (by omega)
  have hlt : d < 2 ^ (Nat.log 2 d + 1) := Nat.lt_pow_succ_log_self (by norm_num) d
  have heven : 2 ∣ 2 ^ Nat.log 2 d := dvd_pow_self 2 (by omega)
  have hne : 2 ^ Nat.log 2 d ≠ d := by
    intro h
    rw [h] at heven
    omega
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ (by omega)
  omega

/-- The step count of the binary schedule is at most `2·log₂ d`. -/
theorem orbSteps_le_two_mul_log : ∀ d, 1 ≤ d →
    orbSteps d ≤ 2 * Nat.log 2 d ∧
      (2 ≤ d → d % 2 = 0 → orbSteps d + 1 ≤ 2 * Nat.log 2 d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      intro hd
      match d with
      | 1 => exact ⟨by simp [orbSteps], by omega⟩
      | (e + 2) =>
          have hk : 1 ≤ Nat.log 2 (e + 2) := Nat.log_pos (by norm_num) (by omega)
          by_cases hpar : (e + 2) % 2 = 0
          · have hhalf : 1 ≤ (e + 2) / 2 := by omega
            have hlt : (e + 2) / 2 < e + 2 := by omega
            have hIH := (ih ((e + 2) / 2) hlt hhalf).1
            have hlog : Nat.log 2 ((e + 2) / 2) = Nat.log 2 (e + 2) - 1 :=
              Nat.log_div_base 2 (e + 2)
            rw [hlog] at hIH
            have hstep : orbSteps (e + 2) = orbSteps ((e + 2) / 2) + 1 := by
              rw [orbSteps, if_pos hpar]
            omega
          · have hodd : (e + 2) % 2 = 1 := by omega
            have h3 : 3 ≤ e + 2 := by omega
            have hprev : 2 ≤ e + 1 := by omega
            have hpprev : (e + 1) % 2 = 0 := by omega
            have hIH := (ih (e + 1) (by omega) (by omega)).2 hprev hpprev
            have hlog : Nat.log 2 (e + 1) = Nat.log 2 (e + 2) := by
              have := log_two_pred_of_odd h3 hodd
              simpa using this
            rw [hlog] at hIH
            have hstep : orbSteps (e + 2) = orbSteps (e + 1) + 1 := by
              rw [orbSteps, if_neg hpar]
            exact ⟨by omega, by omega⟩

/-- (Proposition "Cost of the norm map", general `d`, cost.)  For every `d ≥ 1` the binary
    schedule computes `Orb_d(x)` in at most `2⌈log₂ d⌉` products and as many automorphism
    applications.  The power-of-two case `d = 2^ℓ` of `doubling_schedule` is the special
    case in which the count drops to `ℓ = log₂ d`. -/
theorem orbSchedule_cost_le (φ : R →+* R) (x : R) {d : ℕ} (hd : 1 ≤ d) :
    (orbSchedule φ x d).1 = orbProd φ d x ∧
      (orbSchedule φ x d).2.1 ≤ 2 * Nat.clog 2 d ∧
      (orbSchedule φ x d).2.2 ≤ 2 * Nat.clog 2 d := by
  have hbound : orbSteps d ≤ 2 * Nat.clog 2 d :=
    le_trans (orbSteps_le_two_mul_log d hd).1
      (Nat.mul_le_mul_left 2 (Nat.log_le_clog 2 d))
  exact ⟨orbSchedule_fst φ x d,
    by rw [orbSchedule_products]; exact hbound,
    by rw [orbSchedule_automorphisms]; exact hbound⟩

end Binary

end Galois
