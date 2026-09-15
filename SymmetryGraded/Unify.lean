/-
  Unify.lean

  Formal verification (Lean 4 + Mathlib) of

    Definition "(r,d)-graded cost", Theorem "Prior evaluators as corners of the
    graded cost" and Proposition "Cost monotonicity" (saturated branch included)

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping", at the
  level of the cost function.  The three-branch cost is
      cost(D; r, d) = log₂ d                      if d ≥ 2 and D/r ≤ d   (saturated)
                    = 2√(D/(rd)) + log₂(D/r)      if d ≥ 2 and d < D/r   (interior)
                    = 2√(D/r)                      if d = 1               (scalar only).
  The paper's upper bound `D/r < d·log₂ p` of the interior regime is a range
  restriction on the inputs, not part of the formula, and is not modelled.  The
  intended domain is `d ≥ 1` (a slot degree); the definition is total on ℝ.
  With no unproved placeholders:

  * `gcost`                                  the three-branch cost
  * `gcost_one_one`, `gcost_two_one`, `gcost_four_one`,
    `gcost_norm_saturated`, `gcost_norm_extended`, `corners`
                                             (Theorem "Prior evaluators as corners")
                                             `(1,1) ↦ 2√D`, `(2,1) ↦ 2√(D/2)`,
                                             `(4,1) ↦ √D`, `(1, d ≥ D) ↦ log₂ d`,
                                             `(1, 2 ≤ d < D) ↦ 2√(D/d) + log₂ D`
  * `gcost_interior`, `interior_eq_cost`     the interior branch is `Cost.cost`,
                                             i.e. `2√(D/(rd)) + log₂(D/r)`
  * `gcost_antitone`, `gcost_strict_lt`, `gcost_saturated_tie`
                                             (Proposition "Cost monotonicity")
                                             non-increasing in `r > 0`; strict unless
                                             the smaller order is already saturated;
                                             two saturated orders tie
  * `interior_at_boundary`, `saturation_jump`
                                             at `D/r = d` the interior formula equals
                                             `2 + log₂ d > log₂ d`: a downward jump
-/
import Mathlib
import SymmetryGraded.Cost

namespace Unify

open Real

/-- The `(r, d)`-graded cost (Definition "(r,d)-graded cost"). -/
noncomputable def gcost (D r d : ℝ) : ℝ :=
  if d = 1 then 2 * Real.sqrt (D / r)
  else if D / r ≤ d then Real.logb 2 d
  else 2 * Real.sqrt (D / (r * d)) + Real.logb 2 (D / r)

/-! ## 1. Corners -/

/-- Generic Paterson–Stockmeyer, `(r, d) = (1, 1)`: cost `2√D`. -/
theorem gcost_one_one (D : ℝ) : gcost D 1 1 = 2 * Real.sqrt D := by
  simp [gcost]

/-- Odd polynomials, `(2, 1)`: cost `2√(D/2)`. -/
theorem gcost_two_one (D : ℝ) : gcost D 2 1 = 2 * Real.sqrt (D / 2) := by
  simp [gcost]

/-- The order-four character filter, `(4, 1)`: cost `√D`. -/
theorem gcost_four_one (D : ℝ) (hD : 0 ≤ D) : gcost D 4 1 = Real.sqrt D := by
  simp only [gcost, if_true]
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_div hD, h4]; ring

/-- The Galois norm map in the saturated regime, `(1, d)` with `d ≥ D`: cost `log₂ d`. -/
theorem gcost_norm_saturated {D d : ℝ} (hd : 2 ≤ d) (hDd : D ≤ d) :
    gcost D 1 d = Real.logb 2 d := by
  have h1 : d ≠ 1 := by linarith
  simp [gcost, h1, hDd]

/-- The norm map in the extended regime, `(1, d)` with `2 ≤ d < D`:
    cost `2√(D/d) + log₂ D`. -/
theorem gcost_norm_extended {D d : ℝ} (hd : 2 ≤ d) (hDd : d < D) :
    gcost D 1 d = 2 * Real.sqrt (D / d) + Real.logb 2 D := by
  have h1 : d ≠ 1 := by linarith
  simp [gcost, h1, not_le.mpr hDd]

/-- The interior point: for `d ≥ 2` and `d < D/r` the graded cost is `Cost.cost D d r`. -/
theorem gcost_interior {D r d : ℝ} (hd : 2 ≤ d) (hDr : d < D / r) :
    gcost D r d = Cost.cost D d r := by
  have h1 : d ≠ 1 := by linarith
  simp [gcost, h1, not_le.mpr hDr, Cost.cost]

/-- The interior branch is `2√(D/(rd)) + log₂(D/r)`. -/
theorem interior_eq_cost {D r d : ℝ} (hd : 2 ≤ d) (hDr : d < D / r) :
    gcost D r d = 2 * Real.sqrt (D / (r * d)) + Real.logb 2 (D / r) :=
  gcost_interior hd hDr

/-- (Theorem "Prior evaluators as corners of the graded cost".)  The five prior
    evaluators are the listed corners of `gcost`. -/
theorem corners (D : ℝ) (hD : 0 ≤ D) :
    gcost D 1 1 = 2 * Real.sqrt D ∧
    gcost D 2 1 = 2 * Real.sqrt (D / 2) ∧
    gcost D 4 1 = Real.sqrt D ∧
    (∀ d, 2 ≤ d → D ≤ d → gcost D 1 d = Real.logb 2 d) ∧
    (∀ d, 2 ≤ d → d < D → gcost D 1 d = 2 * Real.sqrt (D / d) + Real.logb 2 D) :=
  ⟨gcost_one_one D, gcost_two_one D, gcost_four_one D hD,
    fun _ hd hDd => gcost_norm_saturated hd hDd,
    fun _ hd hDd => gcost_norm_extended hd hDd⟩

/-! ## 2. Monotonicity in `r` -/

/-- Interior cost dominates the saturated value: for `d < D/r` (so `log₂ d < log₂(D/r)`),
    `log₂ d ≤ 2√(D/(rd)) + log₂(D/r)`. -/
lemma logb_le_interior {D r d : ℝ} (hd : 0 < d) (hDr : d < D / r) :
    Real.logb 2 d ≤ 2 * Real.sqrt (D / (r * d)) + Real.logb 2 (D / r) := by
  have hl : Real.logb 2 d < Real.logb 2 (D / r) :=
    Real.logb_lt_logb (by norm_num) hd hDr
  have hs : 0 ≤ Real.sqrt (D / (r * d)) := Real.sqrt_nonneg _
  linarith

/-- Two orders that are both saturated (`D/r ≤ d`) have the same cost `log₂ d`. -/
theorem gcost_saturated_tie {D r₁ r₂ d : ℝ} (hd : 2 ≤ d) (h₁ : D / r₁ ≤ d)
    (h₂ : D / r₂ ≤ d) : gcost D r₁ d = gcost D r₂ d := by
  have h1 : d ≠ 1 := by linarith
  simp [gcost, h1, h₁, h₂]

/-- (Proposition "Cost monotonicity", strict part.)  For `0 < r₁ < r₂`, `D > 0` and a slot
    degree `d ∈ {1} ∪ [2, ∞)`, if `r₁` is not already in the saturated regime, then
    `gcost D r₂ d < gcost D r₁ d`. -/
theorem gcost_strict_lt {D r₁ r₂ d : ℝ} (hD : 0 < D) (hdom : d = 1 ∨ 2 ≤ d) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hsat : ¬ (2 ≤ d ∧ D / r₁ ≤ d)) :
    gcost D r₂ d < gcost D r₁ d := by
  have h₂ : 0 < r₂ := lt_trans h₁ hlt
  rcases hdom with hd1 | hd2
  · subst hd1
    simp only [gcost, if_true]
    exact Cost.sqrtCost_strictAntiOn hD h₁ h₂ hlt
  · have hne : d ≠ 1 := by linarith
    have hsat₁ : ¬ D / r₁ ≤ d := fun h => hsat ⟨hd2, h⟩
    have hint₁ : d < D / r₁ := not_le.mp hsat₁
    have hd0 : 0 < d := by linarith
    have hDr : D / r₂ < D / r₁ := div_lt_div_of_pos_left hD h₁ hlt
    simp only [gcost, hne, if_false, hsat₁]
    by_cases hsat₂ : D / r₂ ≤ d
    · rw [if_pos hsat₂]
      -- interior → saturated: `log₂ d < log₂(D/r₁) ≤ interior(r₁)`
      have hl : Real.logb 2 d < Real.logb 2 (D / r₁) :=
        Real.logb_lt_logb (by norm_num) hd0 hint₁
      have hs : 0 ≤ Real.sqrt (D / (r₁ * d)) := Real.sqrt_nonneg _
      linarith
    · rw [if_neg hsat₂]
      exact Cost.cost_lt_of_lt hD hd0 h₁ hlt

/-- (Proposition "Cost monotonicity".)  For fixed `D > 0` and `d ∈ {1} ∪ [2, ∞)`, the
    graded cost is non-increasing in `r` on `r > 0`. -/
theorem gcost_antitone {D d : ℝ} (hD : 0 < D) (hdom : d = 1 ∨ 2 ≤ d) :
    AntitoneOn (fun r => gcost D r d) (Set.Ioi 0) := by
  intro r₁ h₁ r₂ _ hle
  rcases hle.lt_or_eq with hlt | rfl
  · by_cases hsat : 2 ≤ d ∧ D / r₁ ≤ d
    · have h₂ : (0 : ℝ) < r₂ := lt_trans h₁ hlt
      have hsat₂ : D / r₂ ≤ d :=
        le_trans (div_lt_div_of_pos_left hD h₁ hlt).le hsat.2
      exact (gcost_saturated_tie hsat.1 hsat.2 hsat₂).ge
    · exact (gcost_strict_lt hD hdom h₁ hlt hsat).le
  · exact le_rfl

/-! ## 3. The saturation jump -/

/-- At the boundary `D/r = d` the interior formula evaluates to `2 + log₂ d`. -/
theorem interior_at_boundary {D r d : ℝ} (hd : 0 < d) (hb : D / r = d) :
    2 * Real.sqrt (D / (r * d)) + Real.logb 2 (D / r) = 2 + Real.logb 2 d := by
  have h1 : D / (r * d) = 1 := by
    rw [← div_div, hb, div_self hd.ne']
  rw [h1, Real.sqrt_one, hb]; ring

/-- The saturated value `log₂ d` lies strictly below the interior formula at the boundary,
    `2 + log₂ d`: increasing `r` across the boundary `D/r = d` is a downward jump. -/
theorem saturation_jump {D r d : ℝ} (hd : 2 ≤ d) (hb : D / r = d) :
    Real.logb 2 d < 2 * Real.sqrt (D / (r * d)) + Real.logb 2 (D / r) ∧
    gcost D r d = Real.logb 2 d := by
  have hd0 : 0 < d := by linarith
  refine ⟨?_, ?_⟩
  · rw [interior_at_boundary hd0 hb]; linarith
  · have hne : d ≠ 1 := by linarith
    simp [gcost, hne, hb.le]

end Unify

