/-
  PSCount.lean

  Formal verification (Lean 4 + Mathlib) of the operation-count bookkeeping of

    Theorem "Factored order-r evaluation", Definition "Effective order",
    Proposition "The evaluator spends ρ", Proposition "Cost of ComposedEval"

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping", as
  arithmetic identities and inequalities over `ℕ` and `ℝ`.  The Paterson–Stockmeyer
  parameters are those of `Noise.lean`: `k = ⌈√m⌉ = BGVNoise.kOf m`,
  `g = ⌈(m+1)/k⌉ = BGVNoise.gOf m`, and `⌈log₂ ·⌉ = Nat.clog 2`.  With no unproved
  placeholders:

  * `psCount`, `psCount_eq`, `psCount_le`
        the PS count `(k−2) + ⌈log₂ g⌉ + (g−1) = k + g + ⌈log₂ g⌉ − 3`, and the explicit
        bound `psCount m ≤ 2√m + log₂(√m + 2) + 1`  (`= 2√m + O(log m)`).
  * `factoredCount`, `factoredCount_six`, `factoredCount_le`
        `C_r = (r−1) + PS(deg Q) + 1`, with the `r = 6` power-chain shortcut `4 ≤ 5`.
  * `rho`, `rho_stable`, `div_r_eq_div_rho`, `sqrt_degQ_le`, `rho_box_closure`
        the effective order `ρ = r|T|/|Ω|`; `|Ω|/r = |T|/ρ`; `deg Q ≤ |Ω|/r ⟹
        2√(deg Q) ≤ 2√(|T|/ρ)`; on the box closure `ρ = 4 + 2/(6B²+6B+1)`.
  * `composedCount`, `composedCount_eq`, `composedCount_eq_ks`, `ks_le_composedCount`
        the phase sum of ComposedEval, its closed form, and its agreement with the
        product count of the straight-line program of `Noise.lean`.
-/
import Mathlib
import SymmetryGraded.Noise
import SymmetryGraded.Lattice

namespace PSCount

open BGVNoise BGVNoise.NoiseModel

/-! ## 1. The Paterson–Stockmeyer count -/

/-- PS count in terms of `(k, g)`: `(k−2)` baby steps, `⌈log₂ g⌉` giant-step squarings,
    `(g−1)` recursion products. -/
def psCount' (k g : ℕ) : ℕ := (k - 2) + Nat.clog 2 g + (g - 1)

/-- PS count on a polynomial of degree `m` with `k = ⌈√m⌉`, `g = ⌈(m+1)/k⌉`. -/
def psCount (m : ℕ) : ℕ := psCount' (kOf m) (gOf m)

theorem psCount_def (m : ℕ) :
    psCount m = (kOf m - 2) + Nat.clog 2 (gOf m) + (gOf m - 1) := rfl

theorem kOf_pos (m : ℕ) : 1 ≤ kOf m := by unfold kOf; omega

/-- `g ≤ k + 1`, since `m + 1 ≤ k² + 1`. -/
theorem gOf_le_kOf_succ (m : ℕ) : gOf m ≤ kOf m + 1 := by
  have hk := kOf_pos m
  have hsq := le_kOf_sq m
  unfold gOf
  rw [Nat.div_le_iff_le_mul_add_pred hk]
  have : kOf m * (kOf m + 1) = kOf m ^ 2 + kOf m := by ring
  omega

theorem gOf_pos (m : ℕ) : 1 ≤ gOf m := by
  have hk := kOf_pos m
  unfold gOf
  rw [Nat.le_div_iff_mul_le hk]; omega

/-- `k = ⌈√m⌉ ≤ √m + 1`. -/
theorem kOf_le_sqrt_add_one (m : ℕ) : (kOf m : ℝ) ≤ Real.sqrt m + 1 := by
  unfold kOf
  push_cast
  have h1 : (Nat.sqrt (m - 1) : ℝ) ≤ Real.sqrt m := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have := Nat.sqrt_le' (m - 1)
    have h2 : ((Nat.sqrt (m - 1)) ^ 2 : ℕ) ≤ m := le_trans this (Nat.sub_le m 1)
    exact_mod_cast h2
  linarith

/-- `⌈log₂ m⌉ ≤ log₂ m + 1` for `m ≥ 1`. -/
theorem clog_le_logb_add_one {m : ℕ} (hm : 1 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ Real.logb 2 m + 1 := by
  rcases Nat.lt_or_ge 1 m with h | h
  · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hpos : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) h
    have hlt' : ((2 : ℝ) ^ (Nat.clog 2 m - 1) : ℝ) < m := by exact_mod_cast hlt
    have hlog : ((Nat.clog 2 m - 1 : ℕ) : ℝ) < Real.logb 2 m := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
      rw [Real.rpow_natCast]; exact hlt'
    have : ((Nat.clog 2 m - 1 : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
      rw [Nat.cast_sub hpos]; simp
    linarith
  · have : m = 1 := by omega
    subst this; simp

theorem psCount_le_nat {m : ℕ} (hk : 2 ≤ kOf m) :
    psCount m ≤ 2 * kOf m - 2 + Nat.clog 2 (gOf m) := by
  have := gOf_le_kOf_succ m
  unfold psCount psCount'; omega

/-- **Explicit PS bound**: `psCount m ≤ 2√m + log₂(√m + 2) + 1` for `m ≥ 1`
    (the paper's `2√m + O(log m)`). -/
theorem psCount_le {m : ℕ} (hm : 1 ≤ m) :
    (psCount m : ℝ) ≤ 2 * Real.sqrt m + Real.logb 2 (Real.sqrt m + 2) + 1 := by
  have hsqrt : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hclog : (Nat.clog 2 (gOf m) : ℝ) ≤ Real.logb 2 (Real.sqrt m + 2) + 1 := by
    have h1 : Nat.clog 2 (gOf m) ≤ Nat.clog 2 (kOf m + 1) :=
      Nat.clog_mono_right 2 (gOf_le_kOf_succ m)
    have h2 := clog_le_logb_add_one (m := kOf m + 1) (by omega)
    have h3 : Real.logb 2 ((kOf m + 1 : ℕ) : ℝ) ≤ Real.logb 2 (Real.sqrt m + 2) := by
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      push_cast; linarith [kOf_le_sqrt_add_one m]
    calc (Nat.clog 2 (gOf m) : ℝ) ≤ (Nat.clog 2 (kOf m + 1) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2
      _ ≤ _ := by linarith
  rcases Nat.lt_or_ge (kOf m) 2 with hk | hk
  · -- `k = 1`, i.e. `m = 1`: `psCount 1 = 2`
    have hk1 : kOf m = 1 := by have := kOf_pos m; omega
    have hm1 : m = 1 := by
      unfold kOf at hk1
      have h0 : Nat.sqrt (m - 1) = 0 := by omega
      rw [Nat.sqrt_eq_zero] at h0; omega
    subst hm1
    have : psCount 1 = 2 := by decide
    rw [this]
    have hl : (0 : ℝ) ≤ Real.logb 2 (Real.sqrt 1 + 2) :=
      Real.logb_nonneg (by norm_num) (by rw [Real.sqrt_one]; norm_num)
    push_cast; linarith [Real.sqrt_one]
  · have h := psCount_le_nat hk
    have hcast : ((2 * kOf m - 2 + Nat.clog 2 (gOf m) : ℕ) : ℝ) =
        2 * (kOf m : ℝ) - 2 + Nat.clog 2 (gOf m) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
    have hk' := kOf_le_sqrt_add_one m
    calc (psCount m : ℝ) ≤ ((2 * kOf m - 2 + Nat.clog 2 (gOf m) : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * (kOf m : ℝ) - 2 + Nat.clog 2 (gOf m) := hcast
      _ ≤ _ := by linarith

/-- The closed form `(k−2) + ⌈log₂ g⌉ + (g−1) + 3 = k + g + ⌈log₂ g⌉`. -/
theorem psCount_eq {m : ℕ} (hk : 2 ≤ kOf m) :
    psCount m + 3 = kOf m + gOf m + Nat.clog 2 (gOf m) := by
  have := gOf_pos m
  unfold psCount psCount'; omega

theorem psCount'_eq {k g : ℕ} (hk : 2 ≤ k) (hg : 1 ≤ g) :
    psCount' k g + 3 = k + g + Nat.clog 2 g := by
  unfold psCount'; omega

/-! ## 2. The factored evaluation `C_r = (r−1) + PS(deg Q) + 1` -/

/-- `C_r`: power chain (`chainMuls r`: 3 at `r = 4`, 4 at `r = 6`), PS on `Q`, assembly. -/
def factoredCount (r degQ : ℕ) : ℕ := chainMuls r + psCount degQ + 1

/-- The power chain uses at most `r − 1` products; at `r = 6` only `4 < 5`. -/
theorem chainMuls_le_pred : ∀ r ∈ ({4, 6} : Finset ℕ), chainMuls r ≤ r - 1 := by decide

theorem factoredCount_six (m : ℕ) : factoredCount 6 m = 4 + psCount m + 1 := rfl

theorem factoredCount_four (m : ℕ) : factoredCount 4 m = 3 + psCount m + 1 := rfl

/-- `C_r ≤ (r − 1) + PS(deg Q) + 1` for `r ∈ {4, 6}`. -/
theorem factoredCount_le {r : ℕ} (hr : r ∈ ({4, 6} : Finset ℕ)) (m : ℕ) :
    factoredCount r m ≤ (r - 1) + psCount m + 1 := by
  have := chainMuls_le_pred r hr
  unfold factoredCount; omega

/-- The real bound `C_r ≤ (r−1) + 2√(deg Q) + log₂(√(deg Q) + 2) + 2`. -/
theorem factoredCount_le_real {r : ℕ} (hr : r ∈ ({4, 6} : Finset ℕ)) {m : ℕ} (hm : 1 ≤ m) :
    (factoredCount r m : ℝ) ≤
      (r - 1 : ℝ) + 2 * Real.sqrt m + Real.logb 2 (Real.sqrt m + 2) + 2 := by
  have h1 := factoredCount_le hr m
  have h2 := psCount_le hm
  have hr1 : 1 ≤ r := by simp at hr; omega
  have : ((r - 1 + psCount m + 1 : ℕ) : ℝ) = (r - 1 : ℝ) + psCount m + 1 := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hr1]; push_cast; ring
  calc (factoredCount r m : ℝ) ≤ ((r - 1 + psCount m + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = _ := this
    _ ≤ _ := by linarith

/-! ## 3. Effective order `ρ = r|T|/|Ω|` -/

/-- Definition "Effective order": `ρ(A, T) = r·|T|/|Ω|`. -/
noncomputable def rho (r T Ω : ℝ) : ℝ := r * T / Ω

/-- `ρ = r` on a stable region (`Ω = T`). -/
theorem rho_stable {r T : ℝ} (hT : 0 < T) : rho r T T = r := by
  unfold rho; field_simp

/-- `|Ω|/r = |T|/ρ`. -/
theorem div_r_eq_div_rho {r T Ω : ℝ} (hr : 0 < r) (hT : 0 < T) (hΩ : 0 < Ω) :
    Ω / r = T / rho r T Ω := by
  unfold rho; field_simp

/-- (Proposition "The evaluator spends ρ".)  `deg Q ≤ |Ω|/r ⟹ 2√(deg Q) ≤ 2√(|T|/ρ)`. -/
theorem sqrt_degQ_le {r T Ω degQ : ℝ} (hr : 0 < r) (hT : 0 < T) (hΩ : 0 < Ω)
    (hdeg : degQ ≤ Ω / r) : 2 * Real.sqrt degQ ≤ 2 * Real.sqrt (T / rho r T Ω) := by
  rw [← div_r_eq_div_rho hr hT hΩ]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdeg) (by norm_num)

/-- On the box closure at `r = 6`: `ρ = 6(2B+1)²/(6B²+6B+1) = 4 + 2/(6B²+6B+1)`. -/
theorem rho_box_closure (B : ℕ) :
    rho 6 ((DigitLattice.box B).card) ((DigitLattice.closure B).card) =
      4 + 2 / (6 * (B : ℝ) ^ 2 + 6 * B + 1) := by
  rw [DigitLattice.card_box, DigitLattice.card_closure]
  unfold rho
  push_cast
  have : (6 * (B : ℝ) ^ 2 + 6 * B + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- `ρ > 4` on the box closure, with `ρ → 4` as `B → ∞` (the paper's "`ρ = 4`"). -/
theorem rho_box_closure_gt_four (B : ℕ) :
    4 < rho 6 ((DigitLattice.box B).card) ((DigitLattice.closure B).card) := by
  rw [rho_box_closure]
  have : (0 : ℝ) < 2 / (6 * (B : ℝ) ^ 2 + 6 * B + 1) := by positivity
  linarith

theorem rho_box_closure_le (B : ℕ) :
    rho 6 ((DigitLattice.box B).card) ((DigitLattice.closure B).card) ≤ 6 := by
  rw [rho_box_closure]
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have h1 : (1 : ℝ) ≤ 6 * (B : ℝ) ^ 2 + 6 * B + 1 := by nlinarith
  have : 2 / (6 * (B : ℝ) ^ 2 + 6 * B + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

/-! ## 4. The composed count (Proposition "Cost of ComposedEval") -/

/-- The phase sum `(r−1) + (k−2) + ⌈log₂ g⌉ + (g−1) + ⌈log₂ d⌉ + 1`. -/
def composedCount (r k g d : ℕ) : ℕ :=
  (r - 1) + (k - 2) + Nat.clog 2 g + (g - 1) + Nat.clog 2 d + 1

/-- Phase split: `(r−1) + PS(k,g) + ⌈log₂ d⌉ + 1`. -/
theorem composedCount_phases (r k g d : ℕ) :
    composedCount r k g d = (r - 1) + psCount' k g + Nat.clog 2 d + 1 := by
  unfold composedCount psCount'; omega

/-- Closed form `k + g + ⌈log₂ g⌉ + ⌈log₂ d⌉ + r − 3`. -/
theorem composedCount_eq {r k g d : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k) (hg : 1 ≤ g) :
    composedCount r k g d = k + g + Nat.clog 2 g + Nat.clog 2 d + r - 3 := by
  unfold composedCount; omega

/-- The product count of the straight-line program `composedEval` of `Noise.lean`
    is the phase sum with the actual chain length `chainMuls r` in Phase 1. -/
theorem composedCount_eq_ks (M : NoiseModel) (rec : ℕ → ℕ × ℕ) (r k g d : ℕ) (nC : ℕ → ℝ)
    (nc nc1 : ℝ) (ct : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.composedEval rec r k g d nC nc nc1 ct).2.1 =
      chainMuls r + (k - 2) + Nat.clog 2 g + (g - 1) + Nat.clog 2 d + 1 := by
  rw [M.composedEval_ks rec r k g d nC nc nc1 ct hk hg]

/-- The program's product count is at most the paper's phase sum whenever
    `chainMuls r ≤ r − 1` (true for `r ∈ {4, 6}`). -/
theorem ks_le_composedCount (M : NoiseModel) (rec : ℕ → ℕ × ℕ) (r k g d : ℕ) (nC : ℕ → ℝ)
    (nc nc1 : ℝ) (ct : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g) (hr : chainMuls r ≤ r - 1) :
    (M.composedEval rec r k g d nC nc nc1 ct).2.1 ≤ composedCount r k g d := by
  rw [composedCount_eq_ks M rec r k g d nC nc nc1 ct hk hg]
  unfold composedCount; omega

/-- The program's count is `chainMuls r + PS(k,g) + ⌈log₂ d⌉ + 1`. -/
theorem ks_eq_phases (M : NoiseModel) (rec : ℕ → ℕ × ℕ) (r k g d : ℕ) (nC : ℕ → ℝ)
    (nc nc1 : ℝ) (ct : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.composedEval rec r k g d nC nc nc1 ct).2.1 =
      chainMuls r + psCount' k g + Nat.clog 2 d + 1 := by
  rw [composedCount_eq_ks M rec r k g d nC nc nc1 ct hk hg]
  unfold psCount'; omega

/-- Case IV instance (`r = 6`, `k = g = 5`, `d = 14`): the phase sum with `r − 1 = 5` is `20`,
    with the actual chain `4` it is `19` (the paper's count). -/
theorem composedCount_instance : composedCount 6 5 5 14 = 20 := by decide

theorem composedCount_instance_chain :
    chainMuls 6 + (5 - 2) + Nat.clog 2 5 + (5 - 1) + Nat.clog 2 14 + 1 = 19 := by decide

/-- PS parameters of the instance: `deg C = 22` gives `k = g = 5`, `psCount 22 = 10`. -/
theorem kOf_instance' : kOf 22 = 5 := by
  have h : Nat.sqrt 21 = 4 := by
    symm; rw [Nat.eq_sqrt]; norm_num
  unfold kOf
  rw [show (22 - 1 : ℕ) = 21 by norm_num, h]

theorem gOf_instance' : gOf 22 = 5 := by
  unfold gOf; rw [kOf_instance']

theorem psCount_instance : psCount 22 = 10 := by
  unfold psCount; rw [kOf_instance', gOf_instance']; decide

end PSCount
