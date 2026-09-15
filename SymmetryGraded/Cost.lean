/-
  Cost.lean

  Formal verification (Lean 4 + Mathlib) of

    Proposition "Cost monotonicity"  and  Proposition "Composed cost, quantified"
    (Appendix "Corners of the graded cost and monotonicity in r")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping", as
  real-analysis statements about the interior-regime cost
      cost(D; r, d) = 2·√(D/(r·d)) + log₂(D/r).
  With no unproved placeholders:

  * `cost`, `cost_strictAntiOn`      the cost is strictly decreasing in `r > 0`
  * `sqrtCost_strictAntiOn`          `r ↦ 2√(D/r)` (the `d = 1` branch) is strictly
                                     decreasing in `r > 0`
  * `cost_lt_of_lt`                  pointwise form: `r₁ < r₂ ⟹ cost r₂ < cost r₁`
  * `speedup_eq`, `speedup_lt_sqrt`  (Proposition "Composed cost, quantified")
                                     `2√D / cost = √(rd) / (1 + √(rd)·log₂(D/r)/(2√D))`,
                                     which is `< √(rd)` when `D > r`
  * `nu_two`, `nu_three`, `nu_four`, `nu_six`
                                     (Proposition "Base-two alignment cost") the
                                     alignment counts `ν(2) = ν(3) = ν(4) = 0`, `ν(6) = 1`
-/
import Mathlib

namespace Cost

open Real

/-- The interior-regime cost `cost(D; r, d) = 2√(D/(rd)) + log₂(D/r)` of the
    `(r, d)`-graded evaluator, as a function of the scalar order `r`. -/
noncomputable def cost (D d r : ℝ) : ℝ := 2 * Real.sqrt (D / (r * d)) + Real.logb 2 (D / r)

/-- The `d = 1` branch `2√(D/r)`. -/
noncomputable def sqrtCost (D r : ℝ) : ℝ := 2 * Real.sqrt (D / r)

/-- Pointwise monotonicity: for `0 < r₁ < r₂`, `cost(D; r₂, d) < cost(D; r₁, d)`. -/
theorem cost_lt_of_lt {D d r₁ r₂ : ℝ} (hD : 0 < D) (hd : 0 < d) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) : cost D d r₂ < cost D d r₁ := by
  unfold cost
  have h₂ : 0 < r₂ := lt_trans h₁ hlt
  have hs : Real.sqrt (D / (r₂ * d)) < Real.sqrt (D / (r₁ * d)) := by
    apply Real.sqrt_lt_sqrt (div_nonneg hD.le (mul_pos h₂ hd).le)
    apply div_lt_div_of_pos_left hD (mul_pos h₁ hd)
    exact mul_lt_mul_of_pos_right hlt hd
  have hl : Real.logb 2 (D / r₂) < Real.logb 2 (D / r₁) := by
    apply Real.logb_lt_logb (by norm_num) (by positivity)
    exact div_lt_div_of_pos_left hD h₁ hlt
  linarith

/-- (Proposition "Cost monotonicity", interior branch.)  For fixed `D, d > 0` the
    cost `r ↦ 2√(D/(rd)) + log₂(D/r)` is strictly decreasing on `r > 0`. -/
theorem cost_strictAntiOn {D d : ℝ} (hD : 0 < D) (hd : 0 < d) :
    StrictAntiOn (cost D d) (Set.Ioi 0) := by
  intro r₁ h₁ r₂ _ hlt
  exact cost_lt_of_lt hD hd h₁ hlt

/-- (Proposition "Cost monotonicity", `d = 1` branch.)  `r ↦ 2√(D/r)` is strictly
    decreasing on `r > 0`. -/
theorem sqrtCost_strictAntiOn {D : ℝ} (hD : 0 < D) :
    StrictAntiOn (sqrtCost D) (Set.Ioi 0) := by
  intro r₁ h₁ r₂ _ hlt
  unfold sqrtCost
  have h₁' : (0 : ℝ) < r₁ := h₁
  have h₂' : (0 : ℝ) < r₂ := lt_trans h₁' hlt
  have hs : Real.sqrt (D / r₂) < Real.sqrt (D / r₁) := by
    apply Real.sqrt_lt_sqrt (div_nonneg hD.le h₂'.le)
    exact div_lt_div_of_pos_left hD h₁' hlt
  linarith

/-- (Proposition "Composed cost, quantified".)  The speedup over generic
    Paterson–Stockmeyer, `2√D / cost(D; r, d)`, equals
    `√(rd) / (1 + √(rd)·log₂(D/r)/(2√D))`. -/
theorem speedup_eq {D d r : ℝ} (hD : 0 < D) (hd : 0 < d) (hr : 0 < r) :
    2 * Real.sqrt D / cost D d r =
      Real.sqrt (r * d) / (1 + Real.sqrt (r * d) * Real.logb 2 (D / r) / (2 * Real.sqrt D)) := by
  unfold cost
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsrd : 0 < Real.sqrt (r * d) := Real.sqrt_pos.mpr (by positivity)
  have hsplit : Real.sqrt (D / (r * d)) = Real.sqrt D / Real.sqrt (r * d) := by
    rw [Real.sqrt_div hD.le]
  rw [hsplit]
  field_simp

/-- The speedup is strictly below `√(rd)` as soon as `D > r` (so that `log₂(D/r) > 0`),
    the shortfall being the additive term `log₂(D/r)`. -/
theorem speedup_lt_sqrt {D d r : ℝ} (hD : 0 < D) (hd : 0 < d) (hr : 0 < r) (hDr : r < D) :
    2 * Real.sqrt D / cost D d r < Real.sqrt (r * d) := by
  rw [speedup_eq hD hd hr]
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsrd : 0 < Real.sqrt (r * d) := Real.sqrt_pos.mpr (by positivity)
  have hlog : 0 < Real.logb 2 (D / r) := by
    apply Real.logb_pos (by norm_num)
    rw [lt_div_iff₀ hr]; linarith
  have hpos : 0 < Real.sqrt (r * d) * Real.logb 2 (D / r) / (2 * Real.sqrt D) := by positivity
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-! ## Alignment counts (Proposition "Base-two alignment cost") -/

/-- The length `|𝒞_r|` of the power chain used by the factored evaluation
    (`x²` for `r = 2`; `x², x³` for `r = 3`; `x², x⁴, x³` for `r = 4`;
    `x², x³, x⁶, x⁵` for `r = 6`). -/
def chainLen : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 6 => 4
  | _ => 0

/-- The number of squarings in the chain `𝒞_r`. -/
def squarings : ℕ → ℕ
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 6 => 2
  | _ => 0

/-- The alignment cost `ν(r) = |𝒞_r| − #squarings − 1` (the assembly power `x^{r−1}` is
    counted separately; for `r = 2` it is `x` itself and costs nothing). -/
def nu (r : ℕ) : ℕ := chainLen r - squarings r - (if r = 2 then 0 else 1)

theorem nu_two : nu 2 = 0 := by decide
theorem nu_three : nu 3 = 0 := by decide
theorem nu_four : nu 4 = 0 := by decide
theorem nu_six : nu 6 = 1 := by decide

/-- Alignment is at most one product for every admissible order. -/
theorem nu_le_one : ∀ r ∈ ({2, 3, 4, 6} : Finset ℕ), nu r ≤ 1 := by decide

end Cost
