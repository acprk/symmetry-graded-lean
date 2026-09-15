/-
  Noise.lean

  An abstract **noise-and-level model** (Lean 4 + Mathlib) of the composed digit
  extraction inside BGV thin bootstrapping, Appendix C.5 ("Correctness and noise
  analysis of Algorithm 3") of

    "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping",

  in the style of an abstract noise-bound model (ciphertext noise is a nonnegative
  real, each homomorphic primitive is a *definition* returning the worst-case bound
  of the corresponding displayed inequality, and theorems derive end-to-end bounds).

  Modelling assumptions (all stated, none hidden):

  * a ciphertext is an abstract pair `⟨noise, level⟩ : ℝ × ℕ`; `level` counts the
    modulus switches consumed so far;
  * the ring constants `δ_R`, `E_ks`, `B_scale` and the modulus ratio `ρ = q'/q`
    are abstract nonnegative reals with `ρ ≤ 1` (`NoiseModel`);
  * the five primitives (13)–(17) of Appendix C.5 are **definitions** of the model
    (worst-case composition): `add`, `ptct`, `mulRaw` (relinearised product),
    `aut` (automorphism + key switch), `modSwitch`; `mul := modSwitch ∘ mulRaw`
    consumes one level, `aut` consumes none;
  * a plaintext constant of norm `c` enters as the trivial ciphertext `triv c` of
    level `0` (the appendix's `ν(ct) = ‖m + p^{r₀}ε‖_∞` includes the message);
  * the programs (`composedEval`, `composedEvalSeq`, `baselineEval`) are explicit
    straight-line programs built from the primitives in the order of Algorithm 2;
    every phase returns its value together with the number of key-switch-bearing
    operations (`mul`/`aut`) it issues, so the operation counts are computed by
    the same definitions as the values.

  Contents (no unproved placeholders, standard axioms only):

  1. `NoiseModel`, `Ct`, the primitives and their monotonicity lemmas;
  2. exact level of the composed program (`composedEval_level`), of the literal
     Algorithm 2 with sequential baby steps (`composedEvalSeq_level`), of the
     baseline (`baselineEval_level`); the paper's formulas `L_comp`, `L_base` and
     their relation to the program levels (`L_prog_le_L_comp`, `L_prog_eq_L_comp_iff`,
     …); the Case IV instance (`L_comp_instance : L_comp 6 22 14 = 15`,
     `L_base_instance : L_base 25 25 = 13`, and the program-level values);
  3. phase noise bounds (power chain, giant steps, orbit doubling, assembly) and the
     doubling-versus-sequential level comparison (`clog_le_pred`, `clog_lt_pred`);
  4. plaintext-level correctness of Algorithm 3 (`recover`, `step6_of_step5`,
     `full_boot_slots`) and the decryption criterion (`correct`,
     `composedEval_correct_of_bound`);
  5. key-switch counts (`composedEval_ks`, `composedEval_ks_instance : … = 23`);
  6. (round 5, section 9) the **phase table** of Appendix C.5: `PhaseRow`, `phaseTable`,
     `psPhase`/`assembly` (Phases 2–4 and 6 isolated), `composedEval_eq_phases`,
     `phase_table` (each row against the program), `L_comp_eq_phase_sum` (the level
     column summed is `L_comp`), `composedEval_ks_eq_phase_sum` (the operation columns
     summed are the program's counts), `phaseTable_instance` (Case IV rows
     `(4,0,3), (10,0,7), (4,4,4), (1,0,1)`).
-/
import Mathlib
import SymmetryGraded.Doubling

namespace BGVNoise

/-! ## 1. The model -/

/-- Abstract ring constants of Appendix C.5: expansion factor `δ_R`, key-switching
noise `E_ks`, modulus-switch rounding error `B_scale`, and the modulus ratio
`ρ = q'/q ≤ 1` of one switch down the chain. -/
structure NoiseModel where
  δ : ℝ
  E_ks : ℝ
  B_scale : ℝ
  ρ : ℝ
  δ_nonneg : 0 ≤ δ
  E_ks_nonneg : 0 ≤ E_ks
  B_scale_nonneg : 0 ≤ B_scale
  ρ_nonneg : 0 ≤ ρ
  ρ_le_one : ρ ≤ 1

/-- An abstract ciphertext: its noise bound `ν` and its level (number of modulus
switches consumed). -/
@[ext]
structure Ct where
  noise : ℝ
  level : ℕ

namespace NoiseModel

variable (M : NoiseModel)

/-- (13) `ν(ct₁ + ct₂) ≤ ν₁ + ν₂`, no level consumed. -/
def add (_M : NoiseModel) (c₁ c₂ : Ct) : Ct := ⟨c₁.noise + c₂.noise, max c₁.level c₂.level⟩

/-- (14) `ν(c · ct) ≤ ‖c‖₁ ν`, plaintext–ciphertext product, no level consumed;
`c` is the `ℓ₁`-norm of the plaintext constant. -/
def ptct (_M : NoiseModel) (c : ℝ) (ct : Ct) : Ct := ⟨c * ct.noise, ct.level⟩

/-- (15) `ν(Mul(ct₁, ct₂)) ≤ δ_R ν₁ ν₂ + E_ks`, relinearised product **before** the
modulus switch. -/
def mulRaw (c₁ c₂ : Ct) : Ct := ⟨M.δ * c₁.noise * c₂.noise + M.E_ks, max c₁.level c₂.level⟩

/-- (16) `ν(τ(ct)) ≤ ν + E_ks`, automorphism followed by a key switch, no level. -/
def aut (ct : Ct) : Ct := ⟨ct.noise + M.E_ks, ct.level⟩

/-- (17) `ν(ModSwitch_{q→q'}(ct)) ≤ (q'/q) ν + B_scale`, consumes one level. -/
def modSwitch (ct : Ct) : Ct := ⟨M.ρ * ct.noise + M.B_scale, ct.level + 1⟩

/-- A product followed by a modulus switch: consumes one level. -/
def mul (c₁ c₂ : Ct) : Ct := M.modSwitch (M.mulRaw c₁ c₂)

/-- The trivial ciphertext of a plaintext constant of norm `c` (level `0`). -/
def triv (_M : NoiseModel) (c : ℝ) : Ct := ⟨c, 0⟩

/-! ### The five displayed equations (13)–(17), as the defining equations of the model -/

@[simp] theorem add_noise (c₁ c₂ : Ct) : (M.add c₁ c₂).noise = c₁.noise + c₂.noise := rfl
@[simp] theorem add_level (c₁ c₂ : Ct) : (M.add c₁ c₂).level = max c₁.level c₂.level := rfl
@[simp] theorem ptct_noise (c : ℝ) (ct : Ct) : (M.ptct c ct).noise = c * ct.noise := rfl
@[simp] theorem ptct_level (c : ℝ) (ct : Ct) : (M.ptct c ct).level = ct.level := rfl
@[simp] theorem mulRaw_noise (c₁ c₂ : Ct) :
    (M.mulRaw c₁ c₂).noise = M.δ * c₁.noise * c₂.noise + M.E_ks := rfl
@[simp] theorem mulRaw_level (c₁ c₂ : Ct) : (M.mulRaw c₁ c₂).level = max c₁.level c₂.level := rfl
@[simp] theorem aut_noise (ct : Ct) : (M.aut ct).noise = ct.noise + M.E_ks := rfl
@[simp] theorem aut_level (ct : Ct) : (M.aut ct).level = ct.level := rfl
@[simp] theorem modSwitch_noise (ct : Ct) :
    (M.modSwitch ct).noise = M.ρ * ct.noise + M.B_scale := rfl
@[simp] theorem modSwitch_level (ct : Ct) : (M.modSwitch ct).level = ct.level + 1 := rfl
@[simp] theorem mul_noise (c₁ c₂ : Ct) :
    (M.mul c₁ c₂).noise = M.ρ * (M.δ * c₁.noise * c₂.noise + M.E_ks) + M.B_scale := rfl
@[simp] theorem mul_level (c₁ c₂ : Ct) : (M.mul c₁ c₂).level = max c₁.level c₂.level + 1 := rfl
@[simp] theorem triv_noise (c : ℝ) : (M.triv c).noise = c := rfl
@[simp] theorem triv_level (c : ℝ) : (M.triv c).level = 0 := rfl

/-- A product followed by a switch consumes exactly one level; an automorphism none. -/
theorem mul_consumes_one (c₁ c₂ : Ct) :
    (M.mul c₁ c₂).level = max c₁.level c₂.level + 1 := rfl
theorem aut_consumes_none (ct : Ct) : (M.aut ct).level = ct.level := rfl

/-- The switched product is bounded by the unswitched one plus the rounding error
(`ρ ≤ 1`, noises nonnegative). -/
theorem mul_noise_le (c₁ c₂ : Ct) (h₁ : 0 ≤ c₁.noise) (h₂ : 0 ≤ c₂.noise) :
    (M.mul c₁ c₂).noise ≤ M.δ * c₁.noise * c₂.noise + M.E_ks + M.B_scale := by
  simp only [mul_noise]
  have h0 : 0 ≤ M.δ * c₁.noise * c₂.noise + M.E_ks := by
    have := M.δ_nonneg; have := M.E_ks_nonneg; positivity
  nlinarith [M.ρ_le_one, M.ρ_nonneg]

/-! ### Monotonicity of every primitive in its inputs -/

theorem add_mono {c₁ c₂ c₁' c₂' : Ct} (h₁ : c₁.noise ≤ c₁'.noise) (h₂ : c₂.noise ≤ c₂'.noise) :
    (M.add c₁ c₂).noise ≤ (M.add c₁' c₂').noise := by
  simp only [add_noise]; linarith

theorem ptct_mono {c : ℝ} (hc : 0 ≤ c) {ct ct' : Ct} (h : ct.noise ≤ ct'.noise) :
    (M.ptct c ct).noise ≤ (M.ptct c ct').noise := by
  simp only [ptct_noise]; exact mul_le_mul_of_nonneg_left h hc

theorem mulRaw_mono {c₁ c₂ c₁' c₂' : Ct} (h₁0 : 0 ≤ c₁.noise) (h₂0 : 0 ≤ c₂.noise)
    (h₁ : c₁.noise ≤ c₁'.noise) (h₂ : c₂.noise ≤ c₂'.noise) :
    (M.mulRaw c₁ c₂).noise ≤ (M.mulRaw c₁' c₂').noise := by
  simp only [mulRaw_noise]
  have := M.δ_nonneg
  have : M.δ * c₁.noise * c₂.noise ≤ M.δ * c₁'.noise * c₂'.noise := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left h₁ ‹_›) h₂ h₂0
    exact mul_nonneg ‹_› (h₁0.trans h₁)
  linarith

theorem aut_mono {ct ct' : Ct} (h : ct.noise ≤ ct'.noise) :
    (M.aut ct).noise ≤ (M.aut ct').noise := by
  simp only [aut_noise]; linarith

theorem modSwitch_mono {ct ct' : Ct} (h : ct.noise ≤ ct'.noise) :
    (M.modSwitch ct).noise ≤ (M.modSwitch ct').noise := by
  simp only [modSwitch_noise]
  have := mul_le_mul_of_nonneg_left h M.ρ_nonneg
  linarith

theorem mul_mono {c₁ c₂ c₁' c₂' : Ct} (h₁0 : 0 ≤ c₁.noise) (h₂0 : 0 ≤ c₂.noise)
    (h₁ : c₁.noise ≤ c₁'.noise) (h₂ : c₂.noise ≤ c₂'.noise) :
    (M.mul c₁ c₂).noise ≤ (M.mul c₁' c₂').noise :=
  M.modSwitch_mono (M.mulRaw_mono h₁0 h₂0 h₁ h₂)

/-- Nonnegativity is preserved by every primitive. -/
theorem add_nonneg' {c₁ c₂ : Ct} (h₁ : 0 ≤ c₁.noise) (h₂ : 0 ≤ c₂.noise) :
    0 ≤ (M.add c₁ c₂).noise := by simp only [add_noise]; linarith
theorem ptct_nonneg {c : ℝ} (hc : 0 ≤ c) {ct : Ct} (h : 0 ≤ ct.noise) :
    0 ≤ (M.ptct c ct).noise := by simp only [ptct_noise]; positivity
theorem mulRaw_nonneg {c₁ c₂ : Ct} (h₁ : 0 ≤ c₁.noise) (h₂ : 0 ≤ c₂.noise) :
    0 ≤ (M.mulRaw c₁ c₂).noise := by
  simp only [mulRaw_noise]; have := M.δ_nonneg; have := M.E_ks_nonneg; positivity
theorem aut_nonneg {ct : Ct} (h : 0 ≤ ct.noise) : 0 ≤ (M.aut ct).noise := by
  simp only [aut_noise]; have := M.E_ks_nonneg; linarith
theorem modSwitch_nonneg {ct : Ct} (h : 0 ≤ ct.noise) : 0 ≤ (M.modSwitch ct).noise := by
  simp only [modSwitch_noise]; have := M.ρ_nonneg; have := M.B_scale_nonneg; positivity
theorem mul_nonneg' {c₁ c₂ : Ct} (h₁ : 0 ≤ c₁.noise) (h₂ : 0 ≤ c₂.noise) :
    0 ≤ (M.mul c₁ c₂).noise :=
  M.modSwitch_nonneg (M.mulRaw_nonneg h₁ h₂)


end NoiseModel

/-! ## 2. Ceiling logarithms: helper lemmas -/

/-- `⌈log₂ i⌉ = ⌈log₂ ⌈i/2⌉⌉ + 1` for `i ≥ 2`: the depth recursion of a balanced product tree. -/
theorem clog_two_half {i : ℕ} (hi : 2 ≤ i) :
    Nat.clog 2 i = Nat.clog 2 (i - i / 2) + 1 := by
  rw [Nat.clog_of_two_le (by norm_num) hi]
  congr 2; omega

/-- `⌈log₂ d⌉ ≤ d − 1` for `d ≥ 1`. -/
theorem clog_le_pred {d : ℕ} (hd : 1 ≤ d) : Nat.clog 2 d ≤ d - 1 := by
  apply Nat.clog_le_of_le_pow
  have := @Nat.lt_two_pow_self (d - 1)
  omega

/-- `d ≤ 2^{d−2}` for `d ≥ 4`. -/
theorem le_two_pow_sub_two {d : ℕ} (hd : 4 ≤ d) : d ≤ 2 ^ (d - 2) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have : 2 ^ (n + 1 - 2) = 2 * 2 ^ (n - 2) := by
        rw [show n + 1 - 2 = (n - 2) + 1 by omega, pow_succ]; ring
      omega

/-- `⌈log₂ d⌉ < d − 1` for `d ≥ 4` (the doubling saves levels; at `d = 3` both cost `2`). -/
theorem clog_lt_pred {d : ℕ} (hd : 4 ≤ d) : Nat.clog 2 d < d - 1 := by
  have := Nat.clog_le_of_le_pow (b := 2) (le_two_pow_sub_two hd)
  omega

theorem clog_three : Nat.clog 2 3 = 2 := by decide

/-- `⌈log₂ (k−1)⌉ ≤ ⌈log₂ k⌉`. -/
theorem clog_pred_le (k : ℕ) : Nat.clog 2 (k - 1) ≤ Nat.clog 2 k :=
  Nat.clog_mono_right 2 (Nat.sub_le k 1)

/-- `⌈log₂ (k−1)⌉ = ⌈log₂ k⌉` iff `k − 1` is not a power of two (`k ≥ 2`). -/
theorem clog_pred_eq_iff {k : ℕ} (hk : 2 ≤ k) :
    Nat.clog 2 (k - 1) = Nat.clog 2 k ↔ 2 ^ Nat.clog 2 (k - 1) ≠ k - 1 := by
  have := Nat.clog_eq_clog_succ_iff (b := 2) (n := k - 1) (by norm_num)
  rw [show k - 1 + 1 = k by omega] at this
  exact this

/-! ## 3. Straight-line programs -/

namespace NoiseModel

variable (M : NoiseModel)

/-- Operation counts of a phase: `(relinearised products, automorphisms)`; every entry is
one key-switch-bearing operation. -/
abbrev KS := ℕ × ℕ

/-! ### Sums of ciphertexts -/

/-- `Σ_{i<n} f i` as a left fold of (13), starting from the empty sum (noise `0`, level `0`). -/
def sumCt (f : ℕ → Ct) : ℕ → Ct
  | 0 => M.triv 0
  | n + 1 => M.add (sumCt f n) (f n)

theorem sumCt_noise (f : ℕ → Ct) (n : ℕ) :
    (M.sumCt f n).noise = ∑ i ∈ Finset.range n, (f i).noise := by
  induction n with
  | zero => simp [sumCt]
  | succ n ih => rw [sumCt, add_noise, ih, Finset.sum_range_succ]

theorem sumCt_level_le (f : ℕ → Ct) (n L : ℕ) (h : ∀ i < n, (f i).level ≤ L) :
    (M.sumCt f n).level ≤ L := by
  induction n with
  | zero => simp [sumCt]
  | succ n ih =>
      rw [sumCt, add_level]
      exact max_le (ih fun i hi => h i (by omega)) (h n (by omega))

theorem le_sumCt_level (f : ℕ → Ct) {n i : ℕ} (hi : i < n) :
    (f i).level ≤ (M.sumCt f n).level := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [sumCt, add_level]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact (ih h).trans (le_max_left _ _)
      · subst h; exact le_max_right _ _

/-! ### Phase 1: the power chain -/

/-- `r = 4`: `ct₂ = x²`, `Y = x⁴ = ct₂²`, `u = x³ = ct₂·x` (3 products, 2 levels). -/
def chain4 (ct : Ct) : Ct × Ct × KS :=
  let c2 := M.mul ct ct
  (M.mul c2 c2, M.mul c2 ct, (3, 0))

/-- `r = 6`: `ct₂ = x²`, `ct₃ = x³`, `Y = x⁶ = ct₃²`, `u = x⁵ = ct₂·ct₃` (4 products, 3 levels). -/
def chain6 (ct : Ct) : Ct × Ct × KS :=
  let c2 := M.mul ct ct
  let c3 := M.mul c2 ct
  (M.mul c3 c3, M.mul c2 c3, (4, 0))

/-- The power chain of Algorithm 2, Phase 1, for `r ∈ {4, 6}` (the two radices implemented);
returns `(ct_Y, ct_u, counts)` with `Y = x^r`, `u = x^{r−1}`. -/
def powerChain (r : ℕ) (ct : Ct) : Ct × Ct × KS :=
  if r = 4 then M.chain4 ct else M.chain6 ct

/-- Levels consumed by the power chain: `δ₄ = 2`, `δ₆ = 3`. -/
def deltaR (r : ℕ) : ℕ := if r = 4 then 2 else 3

/-- Products in the power chain: `3` at `r = 4`, `4` at `r = 6` (`x⁶ = (x³)²`, `x⁵ = x²·x³`). -/
def chainMuls (r : ℕ) : ℕ := if r = 4 then 3 else 4

theorem deltaR_four : deltaR 4 = 2 := rfl
theorem deltaR_six : deltaR 6 = 3 := rfl
theorem chainMuls_four : chainMuls 4 = 3 := rfl
theorem chainMuls_six : chainMuls 6 = 4 := rfl

theorem powerChain_Y_level (r : ℕ) (ct : Ct) :
    (M.powerChain r ct).1.level = ct.level + deltaR r := by
  unfold powerChain deltaR; split_ifs <;> simp [chain4, chain6]

theorem powerChain_u_level (r : ℕ) (ct : Ct) :
    (M.powerChain r ct).2.1.level = ct.level + deltaR r := by
  unfold powerChain deltaR; split_ifs <;> simp [chain4, chain6]

theorem powerChain_ks (r : ℕ) (ct : Ct) : (M.powerChain r ct).2.2 = (chainMuls r, 0) := by
  unfold powerChain chainMuls; split_ifs <;> rfl

/-! ### Phase 2: the baby-step power table -/

/-- The power table `T` with `T 0 = 1` (trivial), `T 1 = Y` and, for `2 ≤ i ≤ n`,
`T i = Mul (T (rec i).1) (T (rec i).2)`, built iteratively (each product issued once);
returns the table and its operation count `(n − 1, 0)`.
`rec` is the recipe: balanced `i ↦ (⌊i/2⌋, ⌈i/2⌉)` or sequential `i ↦ (i − 1, 1)`. -/
def powTable (rec : ℕ → ℕ × ℕ) (Y : Ct) : ℕ → (ℕ → Ct) × KS
  | 0 => (fun i => if i = 0 then M.triv 1 else Y, (0, 0))
  | 1 => (fun i => if i = 0 then M.triv 1 else Y, (0, 0))
  | n + 2 =>
      let P := powTable rec Y (n + 1)
      (Function.update P.1 (n + 2) (M.mul (P.1 (rec (n + 2)).1) (P.1 (rec (n + 2)).2)),
        (P.2.1 + 1, 0))

/-- balanced recipe `i ↦ (⌊i/2⌋, ⌈i/2⌉)` -/
def bal (i : ℕ) : ℕ × ℕ := (i / 2, i - i / 2)

/-- sequential recipe `i ↦ (i − 1, 1)` (the literal loop of Algorithm 2, Phase 2) -/
def seq (i : ℕ) : ℕ × ℕ := (i - 1, 1)

theorem powTable_ks (rec : ℕ → ℕ × ℕ) (Y : Ct) (n : ℕ) :
    (M.powTable rec Y n).2 = (n - 1, 0) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih =>
      simp only [powTable]
      rw [ih]
      simp

theorem powTable_apply_zero (rec : ℕ → ℕ × ℕ) (Y : Ct) (n : ℕ) :
    (M.powTable rec Y n).1 0 = M.triv 1 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih =>
      simp only [powTable]
      rw [Function.update_of_ne (by omega), ih]

theorem powTable_apply_one (rec : ℕ → ℕ × ℕ) (Y : Ct) (n : ℕ) :
    (M.powTable rec Y n).1 1 = Y := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih =>
      simp only [powTable]
      rw [Function.update_of_ne (by omega), ih]

/-- Entries below the last index are unchanged by the last step. -/
theorem powTable_apply_of_le (rec : ℕ → ℕ × ℕ) (Y : Ct) {n i : ℕ} (hi : i ≤ n + 1) :
    (M.powTable rec Y (n + 2)).1 i = (M.powTable rec Y (n + 1)).1 i := by
  simp only [powTable]
  rw [Function.update_of_ne (by omega)]

theorem powTable_apply_last (rec : ℕ → ℕ × ℕ) (Y : Ct) (n : ℕ) :
    (M.powTable rec Y (n + 2)).1 (n + 2) =
      M.mul ((M.powTable rec Y (n + 1)).1 (rec (n + 2)).1)
        ((M.powTable rec Y (n + 1)).1 (rec (n + 2)).2) := by
  simp only [powTable]
  rw [Function.update_self]

/-- Generic level formula for a power table: if `f 1 = 0` and, for `i ≥ 2`, the recipe
uses indices in `[1, i−1]` and `f i = max (f a) (f b) + 1`, then `T i` sits at level
`Y.level + f i` for `1 ≤ i ≤ n`. -/
theorem powTable_level (rec : ℕ → ℕ × ℕ) (f : ℕ → ℕ) (hf1 : f 1 = 0)
    (hrec : ∀ i, 2 ≤ i → 1 ≤ (rec i).1 ∧ (rec i).1 < i ∧ 1 ≤ (rec i).2 ∧ (rec i).2 < i)
    (hf : ∀ i, 2 ≤ i → f i = max (f (rec i).1) (f (rec i).2) + 1)
    (Y : Ct) (n : ℕ) : ∀ i, 1 ≤ i → i ≤ n → ((M.powTable rec Y n).1 i).level = Y.level + f i := by
  induction n using Nat.twoStepInduction with
  | zero => intro i h1 h2; omega
  | one =>
      intro i h1 h2
      have : i = 1 := by omega
      subst this; simp [powTable, hf1]
  | more n _ ih =>
      intro i h1 h2
      rcases Nat.lt_or_ge i (n + 2) with h | h
      · rw [powTable_apply_of_le _ _ _ (by omega)]
        exact ih i h1 (by omega)
      · have hi : i = n + 2 := by omega
        subst hi
        rw [powTable_apply_last, mul_level]
        obtain ⟨ha1, ha2, hb1, hb2⟩ := hrec (n + 2) (by omega)
        rw [ih _ ha1 (by omega), ih _ hb1 (by omega), hf (n + 2) (by omega)]
        omega

/-- Balanced baby steps: `T i` sits at level `Y.level + ⌈log₂ i⌉`. -/
theorem powTable_bal_level (Y : Ct) (n : ℕ) :
    ∀ i, 1 ≤ i → i ≤ n → ((M.powTable bal Y n).1 i).level = Y.level + Nat.clog 2 i := by
  apply powTable_level M bal (Nat.clog 2) (by simp)
  · intro i hi; simp only [bal]; omega
  · intro i hi
    simp only [bal]
    rw [clog_two_half hi]
    have : Nat.clog 2 (i / 2) ≤ Nat.clog 2 (i - i / 2) := Nat.clog_mono_right 2 (by omega)
    omega

/-- Sequential baby steps (the literal loop of Algorithm 2): `T i` sits at level
`Y.level + (i − 1)`. -/
theorem powTable_seq_level (Y : Ct) (n : ℕ) :
    ∀ i, 1 ≤ i → i ≤ n → ((M.powTable seq Y n).1 i).level = Y.level + (i - 1) := by
  apply powTable_level M seq (fun i => i - 1) (by simp)
  · intro i hi; simp only [seq]; omega
  · intro i hi; simp only [seq]; omega

/-! ### Phase 3: giant-step squarings -/

/-- `Z^{2^i}` by repeated squaring from `Z`. -/
def giantPow (Z : Ct) : ℕ → Ct
  | 0 => Z
  | i + 1 => M.mul (giantPow Z i) (giantPow Z i)

theorem giantPow_level (Z : Ct) (i : ℕ) : (M.giantPow Z i).level = Z.level + i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [giantPow, mul_level, ih]; omega

/-! ### Phase 4: block sums and the Paterson–Stockmeyer recursion -/

/-- `ct_{C^{(j)}} = Σ_{i<k} C_{jk+i} · T i` (plaintext–ciphertext only); `nC e = ‖C_e‖₁`. -/
def block (T : ℕ → Ct) (k : ℕ) (nC : ℕ → ℝ) (j : ℕ) : Ct :=
  M.sumCt (fun i => M.ptct (nC (j * k + i)) (T i)) k

theorem block_noise (T : ℕ → Ct) (k : ℕ) (nC : ℕ → ℝ) (j : ℕ) :
    (M.block T k nC j).noise = ∑ i ∈ Finset.range k, nC (j * k + i) * (T i).noise := by
  simp [block, sumCt_noise]

/-- The PS recursion on `n` consecutive blocks starting at `off`:
`PS(n, off) = PS(h, off) + Z^{h} · PS(n − h, off + h)` with `h = 2^{⌈log₂ n⌉ − 1}`
(`Zp i` encrypts `Z^{2^i}`); returns the value and the count `(n − 1, 0)`. -/
def psRec (Zp : ℕ → Ct) (blk : ℕ → Ct) (n off : ℕ) : Ct × KS :=
  if h : n ≤ 1 then (blk off, (0, 0)) else
    have hn : 1 < n := by omega
    have hlt : 2 ^ (Nat.clog 2 n - 1) < n := by
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hn
      simpa [Nat.pred_eq_sub_one] using this
    have hpos : 0 < 2 ^ (Nat.clog 2 n - 1) := by positivity
    let L := psRec Zp blk (2 ^ (Nat.clog 2 n - 1)) off
    let R := psRec Zp blk (n - 2 ^ (Nat.clog 2 n - 1)) (off + 2 ^ (Nat.clog 2 n - 1))
    (M.add L.1 (M.mul (Zp (Nat.clog 2 n - 1)) R.1), (L.2.1 + R.2.1 + 1, 0))
termination_by n
decreasing_by
  · exact hlt
  · omega

theorem psRec_ks (Zp : ℕ → Ct) (blk : ℕ → Ct) :
    ∀ n off, 1 ≤ n → (M.psRec Zp blk n off).2 = (n - 1, 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro off hn
      rcases Nat.lt_or_ge 1 n with h | h
      · rw [psRec, dif_neg (by omega)]
        have hlt : 2 ^ (Nat.clog 2 n - 1) < n := by
          have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
          simpa [Nat.pred_eq_sub_one] using this
        have hpos : 0 < 2 ^ (Nat.clog 2 n - 1) := by positivity
        simp only
        rw [ih _ hlt _ hpos, ih _ (by omega) _ (by omega)]
        simp only [Prod.mk.injEq, and_true]
        omega
      · have : n = 1 := by omega
        subst this; rw [psRec, dif_pos le_rfl]

/-- Upper bound: the PS recursion on `n ≥ 1` blocks sits at level `≤ b + ⌈log₂ n⌉` when the
squaring chain sits at `b + i` and every block at `≤ b`. -/
theorem psRec_level_le (Zp : ℕ → Ct) (blk : ℕ → Ct) (b : ℕ)
    (hZ : ∀ i, (Zp i).level = b + i) (hb : ∀ j, (blk j).level ≤ b) :
    ∀ n off, (M.psRec Zp blk n off).1.level ≤ b + Nat.clog 2 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro off
      rcases Nat.lt_or_ge 1 n with h | h
      · rw [psRec, dif_neg (by omega)]
        have hlt : 2 ^ (Nat.clog 2 n - 1) < n := by
          have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
          simpa [Nat.pred_eq_sub_one] using this
        have hpos : 0 < 2 ^ (Nat.clog 2 n - 1) := by positivity
        have hm : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) h
        simp only [add_level, mul_level, hZ]
        have hL := ih _ hlt off
        have hR := ih (n - 2 ^ (Nat.clog 2 n - 1)) (by omega) (off + 2 ^ (Nat.clog 2 n - 1))
        rw [Nat.clog_pow 2 _ (by norm_num)] at hL
        have hR' : Nat.clog 2 (n - 2 ^ (Nat.clog 2 n - 1)) ≤ Nat.clog 2 n - 1 := by
          apply Nat.clog_le_of_le_pow
          have h1 := Nat.le_pow_clog (b := 2) (by norm_num) n
          have h2 : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
            rw [← pow_succ']; congr 1; omega
          omega
        omega
      · rw [psRec, dif_pos h]
        exact (hb off).trans (by omega)

/-- Lower bound: for `n ≥ 2` blocks the top product involves `Z^{2^{⌈log₂ n⌉−1}}`, so the
level is at least `b + ⌈log₂ n⌉`. -/
theorem psRec_level_ge (Zp : ℕ → Ct) (blk : ℕ → Ct) (b : ℕ)
    (hZ : ∀ i, (Zp i).level = b + i) {n : ℕ} (hn : 2 ≤ n) (off : ℕ) :
    b + Nat.clog 2 n ≤ (M.psRec Zp blk n off).1.level := by
  rw [psRec, dif_neg (by omega)]
  have hm : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
  simp only [add_level, mul_level, hZ]
  omega

/-- Exact level of the PS recursion on `n ≥ 2` blocks: `b + ⌈log₂ n⌉`. -/
theorem psRec_level (Zp : ℕ → Ct) (blk : ℕ → Ct) (b : ℕ)
    (hZ : ∀ i, (Zp i).level = b + i) (hb : ∀ j, (blk j).level ≤ b) {n : ℕ} (hn : 2 ≤ n)
    (off : ℕ) : (M.psRec Zp blk n off).1.level = b + Nat.clog 2 n :=
  le_antisymm (M.psRec_level_le Zp blk b hZ hb n off) (M.psRec_level_ge Zp blk b hZ hn off)

/-! ### Phase 5: the Frobenius orbit by doubling -/

/-- One doubling step `N ↦ Mul(N, τ(N))`: one automorphism, one product, one level. -/
def orbitStep (N : Ct) : Ct := M.mul N (M.aut N)

/-- `ℓ` doubling steps: `(N_ℓ, (ℓ products, ℓ automorphisms))`. -/
def orbit (ℓ : ℕ) (N : Ct) : Ct × KS := ((M.orbitStep)^[ℓ] N, (ℓ, ℓ))

theorem orbitStep_level (N : Ct) : (M.orbitStep N).level = N.level + 1 := by
  simp [orbitStep]

theorem orbit_level (ℓ : ℕ) (N : Ct) : (M.orbit ℓ N).1.level = N.level + ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
      simp only [orbit] at ih ⊢
      rw [Function.iterate_succ_apply', orbitStep_level, ih]; omega

theorem orbit_ks (ℓ : ℕ) (N : Ct) : (M.orbit ℓ N).2 = (ℓ, ℓ) := rfl

/-- The sequential alternative: `N ↦ Mul(N, τ_i(x))` for the conjugates one at a time,
`n = d − 1` steps: `n` products, `n` automorphisms, `n` levels. -/
def seqOrbit (x : Ct) (n : ℕ) : Ct × KS := ((fun N => M.mul N (M.aut x))^[n] x, (n, n))

theorem seqOrbit_level (x : Ct) (n : ℕ) : (M.seqOrbit x n).1.level = x.level + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [seqOrbit] at ih ⊢
      rw [Function.iterate_succ_apply', mul_level, ih, aut_level]
      omega

/-- (Comparison, Appendix C.5, Phase 5.)  Closing the orbit of length `d` sequentially costs
`d − 1` levels; by doubling it costs `⌈log₂ d⌉ ≤ d − 1`, strictly fewer for `d ≥ 4`. -/
theorem doubling_saves_levels (x : Ct) {d : ℕ} (hd : 1 ≤ d) :
    (M.orbit (Nat.clog 2 d) x).1.level ≤ (M.seqOrbit x (d - 1)).1.level := by
  rw [orbit_level, seqOrbit_level]
  have := clog_le_pred hd
  omega

theorem doubling_saves_levels_strict (x : Ct) {d : ℕ} (hd : 4 ≤ d) :
    (M.orbit (Nat.clog 2 d) x).1.level < (M.seqOrbit x (d - 1)).1.level := by
  rw [orbit_level, seqOrbit_level]
  have := clog_lt_pred hd
  omega

/-! ### The composed program (Algorithm 2) -/

/-- **ComposedEval** as a straight-line program over the primitives, in the order of
Algorithm 2.  Inputs: the recipe `rec` for the baby steps (`bal` or `seq`), `r`, `k`, `g`,
`d`, the norms `nC e = ‖C_e‖₁`, `nc = ‖c‖₁`, `nc1 = |c₁|`, and the input ciphertext.
Output: `(ct_out, (products, automorphisms))`. -/
def composedEval (rec : ℕ → ℕ × ℕ) (r k g d : ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct) :
    Ct × KS :=
  -- Phase 1: power chain
  let ch := M.powerChain r ct
  let Y := ch.1
  let u := ch.2.1
  -- Phase 2: baby steps `Y^1, …, Y^{k−1}`
  let T := M.powTable rec Y (k - 1)
  -- Phase 3: `Z = Y^{k−1}·Y` and the squarings `Z^{2^i}`, `i < ⌈log₂ g⌉`
  let Z := M.mul (T.1 (k - 1)) (T.1 1)
  let m := Nat.clog 2 g
  let Zp := M.giantPow Z
  -- Phase 4: block sums and the PS recursion on `g` blocks
  let blk := M.block T.1 k nC
  let ps := M.psRec Zp blk g 0
  -- Phase 5: orbit doubling, `⌈log₂ d⌉` steps
  let orb := M.orbit (Nat.clog 2 d) ps.1
  -- Phase 6: assembly `c · Mul(ct_o, ct_u) + c₁ · ct`
  let out := M.add (M.ptct nc (M.mul orb.1 u)) (M.ptct nc1 ct)
  (out, ch.2.2 + T.2 + (1 + (m - 1), 0) + ps.2 + orb.2 + (1, 0))

/-- The paper's level count for the composed evaluator (Appendix C.5):
`L_comp = δ_r + ⌈log₂ k⌉ + ⌈log₂ g⌉ + 1 + ⌈log₂ d⌉ + 1`. -/
def L_comp' (r k g d : ℕ) : ℕ :=
  deltaR r + Nat.clog 2 k + Nat.clog 2 g + 1 + Nat.clog 2 d + 1

/-- The exact level of the balanced-tree program:
`δ_r + ⌈log₂ (k−1)⌉ + 1 + ⌈log₂ g⌉ + ⌈log₂ d⌉ + 1`. -/
def L_prog (r k g d : ℕ) : ℕ :=
  deltaR r + Nat.clog 2 (k - 1) + 1 + Nat.clog 2 g + Nat.clog 2 d + 1

/-- The exact level of the literal Algorithm 2 (sequential baby steps):
`δ_r + (k − 1) + ⌈log₂ g⌉ + ⌈log₂ d⌉ + 1`. -/
def L_seq (r k g d : ℕ) : ℕ :=
  deltaR r + (k - 1) + Nat.clog 2 g + Nat.clog 2 d + 1

/-- **Exact level of the composed program** (balanced baby steps), `k, g ≥ 2`. -/
theorem composedEval_level (r k g d : ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct)
    (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.composedEval bal r k g d nC nc nc1 ct).1.level = ct.level + L_prog r k g d := by
  -- levels of the intermediate ciphertexts
  have hY := M.powerChain_Y_level r ct
  have hu := M.powerChain_u_level r ct
  have hT := M.powTable_bal_level (M.powerChain r ct).1 (k - 1)
  have hT1 := M.powTable_apply_one bal (M.powerChain r ct).1 (k - 1)
  have hTk := hT (k - 1) (by omega) le_rfl
  set Y := (M.powerChain r ct).1 with hYdef
  set T := M.powTable bal Y (k - 1) with hTdef
  set Z := M.mul (T.1 (k - 1)) (T.1 1) with hZdef
  have hZ : Z.level = Y.level + Nat.clog 2 (k - 1) + 1 := by
    rw [hZdef, mul_level, hTk, hT1]; omega
  have hZp : ∀ i, (M.giantPow Z i).level = Z.level + i := M.giantPow_level Z
  have hblk : ∀ j, (M.block T.1 k nC j).level ≤ Z.level := by
    intro j
    apply M.sumCt_level_le
    intro i hi
    rw [ptct_level]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [M.powTable_apply_zero]; simp
    · rw [hT i hpos (by omega), hZ]
      have := Nat.clog_mono_right 2 (show i ≤ k - 1 by omega)
      omega
  have hps := M.psRec_level (M.giantPow Z) (M.block T.1 k nC) Z.level hZp hblk hg 0
  simp only [composedEval, add_level, ptct_level, mul_level, orbit_level]
  rw [← hTdef, ← hZdef, hps, hZ, hY, hu, L_prog]
  omega

/-- **Exact level of the literal Algorithm 2** (sequential baby steps), `k, g ≥ 2`. -/
theorem composedEvalSeq_level (r k g d : ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct)
    (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.composedEval seq r k g d nC nc nc1 ct).1.level = ct.level + L_seq r k g d := by
  have hY := M.powerChain_Y_level r ct
  have hu := M.powerChain_u_level r ct
  have hT := M.powTable_seq_level (M.powerChain r ct).1 (k - 1)
  have hT1 := M.powTable_apply_one seq (M.powerChain r ct).1 (k - 1)
  have hTk := hT (k - 1) (by omega) le_rfl
  set Y := (M.powerChain r ct).1 with hYdef
  set T := M.powTable seq Y (k - 1) with hTdef
  set Z := M.mul (T.1 (k - 1)) (T.1 1) with hZdef
  have hZ : Z.level = Y.level + (k - 1 - 1) + 1 := by
    rw [hZdef, mul_level, hTk, hT1]; omega
  have hZp : ∀ i, (M.giantPow Z i).level = Z.level + i := M.giantPow_level Z
  have hblk : ∀ j, (M.block T.1 k nC j).level ≤ Z.level := by
    intro j
    apply M.sumCt_level_le
    intro i hi
    rw [ptct_level]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [M.powTable_apply_zero]; simp
    · rw [hT i hpos (by omega), hZ]; omega
  have hps := M.psRec_level (M.giantPow Z) (M.block T.1 k nC) Z.level hZp hblk hg 0
  simp only [composedEval, add_level, ptct_level, mul_level, orbit_level]
  rw [← hTdef, ← hZdef, hps, hZ, hY, hu, L_seq]
  omega

/-- The program level never exceeds the paper's formula. -/
theorem L_prog_le_L_comp' (r k g d : ℕ) : L_prog r k g d ≤ L_comp' r k g d := by
  unfold L_prog L_comp'
  have := clog_pred_le k
  omega

/-- The paper's formula is exact iff `k − 1` is not a power of two (`k ≥ 2`). -/
theorem L_prog_eq_L_comp'_iff (r k g d : ℕ) (hk : 2 ≤ k) :
    L_prog r k g d = L_comp' r k g d ↔ 2 ^ Nat.clog 2 (k - 1) ≠ k - 1 := by
  rw [← clog_pred_eq_iff hk]
  unfold L_prog L_comp'
  omega

/-- The paper's formula and the sequential level differ by `⌈log₂ k⌉ + 1 − (k − 1)`
(they agree for `k = 5`, the instance). -/
theorem L_seq_eq (r k g d : ℕ) :
    L_seq r k g d + Nat.clog 2 k + 1 = L_comp' r k g d + (k - 1) := by
  unfold L_seq L_comp'; omega

/-! ### The baseline program (odd polynomial `X·Q₀(X²)` by Paterson–Stockmeyer) -/

/-- **Baseline**: `x²` (one product), baby steps `Y^1..Y^{k₀−1}` above `Y = x²`, `Z = Y^{k₀}`,
squarings, PS on `g₀` blocks, then `X · Q₀(X²)` (one product). -/
def baselineEval (rec : ℕ → ℕ × ℕ) (k₀ g₀ : ℕ) (nQ : ℕ → ℝ) (ct : Ct) : Ct × KS :=
  let Y := M.mul ct ct
  let T := M.powTable rec Y (k₀ - 1)
  let Z := M.mul (T.1 (k₀ - 1)) (T.1 1)
  let m := Nat.clog 2 g₀
  let Zp := M.giantPow Z
  let blk := M.block T.1 k₀ nQ
  let ps := M.psRec Zp blk g₀ 0
  let out := M.mul ct ps.1
  (out, (1, 0) + T.2 + (1 + (m - 1), 0) + ps.2 + (1, 0))

/-- The paper's baseline count `L_base = 1 + ⌈log₂ k₀⌉ + ⌈log₂ g₀⌉ + 2`. -/
def L_base (k₀ g₀ : ℕ) : ℕ := 1 + Nat.clog 2 k₀ + Nat.clog 2 g₀ + 2

/-- The exact level of the baseline program: `1 + ⌈log₂ (k₀−1)⌉ + 1 + ⌈log₂ g₀⌉ + 1`. -/
def L_baseProg (k₀ g₀ : ℕ) : ℕ := 1 + Nat.clog 2 (k₀ - 1) + 1 + Nat.clog 2 g₀ + 1

theorem baselineEval_level (k₀ g₀ : ℕ) (nQ : ℕ → ℝ) (ct : Ct) (hk : 2 ≤ k₀) (hg : 2 ≤ g₀) :
    (M.baselineEval bal k₀ g₀ nQ ct).1.level = ct.level + L_baseProg k₀ g₀ := by
  have hT := M.powTable_bal_level (M.mul ct ct) (k₀ - 1)
  have hT1 := M.powTable_apply_one bal (M.mul ct ct) (k₀ - 1)
  have hTk := hT (k₀ - 1) (by omega) le_rfl
  set Y := M.mul ct ct with hYdef
  have hY : Y.level = ct.level + 1 := by rw [hYdef, mul_level]; omega
  set T := M.powTable bal Y (k₀ - 1) with hTdef
  set Z := M.mul (T.1 (k₀ - 1)) (T.1 1) with hZdef
  have hZ : Z.level = Y.level + Nat.clog 2 (k₀ - 1) + 1 := by
    rw [hZdef, mul_level, hTk, hT1]; omega
  have hZp : ∀ i, (M.giantPow Z i).level = Z.level + i := M.giantPow_level Z
  have hblk : ∀ j, (M.block T.1 k₀ nQ j).level ≤ Z.level := by
    intro j
    apply M.sumCt_level_le
    intro i hi
    rw [ptct_level]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [M.powTable_apply_zero]; simp
    · rw [hT i hpos (by omega), hZ]
      have := Nat.clog_mono_right 2 (show i ≤ k₀ - 1 by omega)
      omega
  have hps := M.psRec_level (M.giantPow Z) (M.block T.1 k₀ nQ) Z.level hZp hblk hg 0
  simp only [baselineEval, mul_level]
  rw [← hTdef, ← hZdef, hps, hZ, hY, L_baseProg]
  omega

theorem L_baseProg_le_L_base (k₀ g₀ : ℕ) : L_baseProg k₀ g₀ ≤ L_base k₀ g₀ := by
  unfold L_baseProg L_base; have := clog_pred_le k₀; omega

theorem L_baseProg_eq_L_base_iff (k₀ g₀ : ℕ) (hk : 2 ≤ k₀) :
    L_baseProg k₀ g₀ = L_base k₀ g₀ ↔ 2 ^ Nat.clog 2 (k₀ - 1) ≠ k₀ - 1 := by
  rw [← clog_pred_eq_iff hk]; unfold L_baseProg L_base; omega

end NoiseModel

/-! ## 4. The paper's parameters `k = ⌈√deg C⌉`, `g = ⌈(deg C + 1)/k⌉` and the level formulas -/

/-- `k = ⌈√degC⌉` (for `degC ≥ 1`): the least `k` with `k² ≥ degC`. -/
def kOf (degC : ℕ) : ℕ := Nat.sqrt (degC - 1) + 1

/-- `g = ⌈(degC + 1)/k⌉`. -/
def gOf (degC : ℕ) : ℕ := (degC + 1 + kOf degC - 1) / kOf degC

theorem le_kOf_sq (degC : ℕ) : degC ≤ kOf degC ^ 2 := by
  unfold kOf
  have := Nat.lt_succ_sqrt' (degC - 1)
  simp only [Nat.succ_eq_add_one] at this
  omega

theorem kOf_pred_sq_lt {degC : ℕ} (h : 1 ≤ degC) : (kOf degC - 1) ^ 2 < degC := by
  unfold kOf
  have := Nat.sqrt_le' (degC - 1)
  simp only [Nat.add_sub_cancel]
  omega

/-- ceiling division: `n ≤ k · ⌈n/k⌉` -/
theorem le_mul_ceilDiv {n k : ℕ} (hk : 0 < k) : n ≤ k * ((n + k - 1) / k) := by
  have h1 := Nat.div_add_mod (n + k - 1) k
  have h2 := Nat.mod_lt (n + k - 1) hk
  omega

/-- ceiling division: `k · (⌈n/k⌉ − 1) < n` -/
theorem mul_ceilDiv_pred_lt {n k : ℕ} (hk : 0 < k) (hn : 1 ≤ n) :
    k * ((n + k - 1) / k - 1) < n := by
  have h1 := Nat.div_add_mod (n + k - 1) k
  have h2 := Nat.mod_lt (n + k - 1) hk
  have h3 : 1 ≤ (n + k - 1) / k := by
    rw [Nat.le_div_iff_mul_le hk]; omega
  have h4 : k * ((n + k - 1) / k - 1) = k * ((n + k - 1) / k) - k := by
    rw [Nat.mul_sub, mul_one]
  omega

theorem gOf_spec (degC : ℕ) :
    degC + 1 ≤ kOf degC * gOf degC ∧ kOf degC * (gOf degC - 1) < degC + 1 :=
  ⟨le_mul_ceilDiv (by unfold kOf; omega), mul_ceilDiv_pred_lt (by unfold kOf; omega) (by omega)⟩

open NoiseModel in
/-- **The paper's formula**
`L_comp(r, deg C, d) = δ_r + ⌈log₂ k⌉ + ⌈log₂ g⌉ + 1 + ⌈log₂ d⌉ + 1` with
`k = ⌈√deg C⌉`, `g = ⌈(deg C + 1)/k⌉`. -/
def L_comp (r degC d : ℕ) : ℕ := L_comp' r (kOf degC) (gOf degC) d

theorem L_comp_eq (r degC d : ℕ) :
    L_comp r degC d = NoiseModel.deltaR r + Nat.clog 2 (kOf degC) + Nat.clog 2 (gOf degC) + 1 +
      Nat.clog 2 d + 1 := rfl

/-- The balanced-tree program's level is bounded by the paper's `L_comp`. -/
theorem L_prog_le_L_comp (r degC d : ℕ) :
    NoiseModel.L_prog r (kOf degC) (gOf degC) d ≤ L_comp r degC d :=
  NoiseModel.L_prog_le_L_comp' r _ _ d

/-! ### The Case IV instance: `deg C = 22`, `d = 14`, `r = 6`, `k = g = 5`; baseline `k₀ = g₀ = 25` -/

theorem kOf_instance : kOf 22 = 5 := by norm_num [kOf, Nat.sqrt]
theorem gOf_instance : gOf 22 = 5 := by rw [gOf, kOf_instance]
theorem L_comp_instance : L_comp 6 22 14 = 15 := by
  rw [L_comp, kOf_instance, gOf_instance]; decide
theorem L_base_instance : NoiseModel.L_base 25 25 = 13 := by decide
theorem L_comp_sub_L_base_instance : L_comp 6 22 14 - NoiseModel.L_base 25 25 = 2 := by
  rw [L_comp_instance, L_base_instance]

/-- The literal Algorithm 2 (sequential baby steps) consumes exactly `15` levels in the instance. -/
theorem L_seq_instance : NoiseModel.L_seq 6 5 5 14 = 15 := by decide
/-- The balanced-tree program consumes `14` levels in the instance (`k − 1 = 4` is a power of two). -/
theorem L_prog_instance : NoiseModel.L_prog 6 5 5 14 = 14 := by decide
/-- The baseline program consumes exactly `13` levels in the instance (`k₀ − 1 = 24` is not a power of two). -/
theorem L_baseProg_instance : NoiseModel.L_baseProg 25 25 = 13 := by decide

theorem composedEvalSeq_level_instance (M : NoiseModel) (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct) :
    (M.composedEval NoiseModel.seq 6 5 5 14 nC nc nc1 ct).1.level = ct.level + 15 := by
  rw [M.composedEvalSeq_level _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), L_seq_instance]

theorem composedEval_level_instance (M : NoiseModel) (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct) :
    (M.composedEval NoiseModel.bal 6 5 5 14 nC nc nc1 ct).1.level = ct.level + 14 := by
  rw [M.composedEval_level _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), L_prog_instance]

theorem baselineEval_level_instance (M : NoiseModel) (nQ : ℕ → ℝ) (ct : Ct) :
    (M.baselineEval NoiseModel.bal 25 25 nQ ct).1.level = ct.level + 13 := by
  rw [M.baselineEval_level _ _ _ _ (by norm_num) (by norm_num), L_baseProg_instance]


/-! ## 5. Phase noise bounds (Appendix C.5, "Noise and levels of Step 5") -/

namespace NoiseModel

variable (M : NoiseModel)

/-- (a) Power chain, before the switch: `ν(x²) = δ_R ν_in² + E_ks`. -/
theorem sq_noise_raw (ct : Ct) : (M.mulRaw ct ct).noise = M.δ * ct.noise ^ 2 + M.E_ks := by
  simp [mulRaw_noise, sq, mul_assoc]

/-- (a) Power chain, after the switch: `ν(x²) ≤ δ_R ν_in² + E_ks + B_scale`. -/
theorem sq_noise_le (ct : Ct) (h : 0 ≤ ct.noise) :
    (M.mul ct ct).noise ≤ M.δ * ct.noise ^ 2 + M.E_ks + M.B_scale := by
  have := M.mul_noise_le ct ct h h
  rw [sq, ← mul_assoc]; exact this

/-- (a) In the `r = 6` chain, `Y = x⁶ = (x³)²`: `ν(x⁶) ≤ δ_R ν(x³)² + E_ks + B_scale`. -/
theorem chain6_Y_noise_le (ct : Ct) (h : 0 ≤ ct.noise) :
    (M.chain6 ct).1.noise ≤
      M.δ * (M.mul (M.mul ct ct) ct).noise ^ 2 + M.E_ks + M.B_scale :=
  M.sq_noise_le _ (M.mul_nonneg' (M.mul_nonneg' h h) h)

/-- (a) In the `r = 4` chain, `Y = x⁴ = (x²)²`. -/
theorem chain4_Y_noise_le (ct : Ct) (h : 0 ≤ ct.noise) :
    (M.chain4 ct).1.noise ≤ M.δ * (M.mul ct ct).noise ^ 2 + M.E_ks + M.B_scale :=
  M.sq_noise_le _ (M.mul_nonneg' h h)

/-- (b) Giant step, before the switch:
`ν(ct_{C^{(j)}} · Z^j) = δ_R (Σ_{i<k} ‖C_{jk+i}‖₁ ν(Y^i)) ν(Z^j) + E_ks`. -/
theorem giant_step_noise_raw (T : ℕ → Ct) (k : ℕ) (nC : ℕ → ℝ) (j : ℕ) (Zj : Ct) :
    (M.mulRaw (M.block T k nC j) Zj).noise =
      M.δ * (∑ i ∈ Finset.range k, nC (j * k + i) * (T i).noise) * Zj.noise + M.E_ks := by
  rw [mulRaw_noise, block_noise]

/-- (b) Giant step, after the switch: `≤ δ_R (Σ ‖C_{jk+i}‖₁ ν(Y^i)) ν(Z^j) + E_ks + B_scale`. -/
theorem giant_step_noise_le (T : ℕ → Ct) (k : ℕ) (nC : ℕ → ℝ) (j : ℕ) (Zj : Ct)
    (hC : ∀ e, 0 ≤ nC e) (hT : ∀ i, 0 ≤ (T i).noise) (hZ : 0 ≤ Zj.noise) :
    (M.mul (M.block T k nC j) Zj).noise ≤
      M.δ * (∑ i ∈ Finset.range k, nC (j * k + i) * (T i).noise) * Zj.noise + M.E_ks +
        M.B_scale := by
  have hb : 0 ≤ (M.block T k nC j).noise := by
    rw [block_noise]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC _) (hT i)
  have := M.mul_noise_le _ _ hb hZ
  rwa [block_noise] at this

/-- (c) Orbit doubling, before the switch:
`ν(N_{j+1}) = δ_R ν(N_j)(ν(N_j) + E_ks) + E_ks`. -/
theorem orbit_step_noise_raw (N : Ct) :
    (M.mulRaw N (M.aut N)).noise = M.δ * N.noise * (N.noise + M.E_ks) + M.E_ks := by
  simp [mulRaw_noise, aut_noise]

/-- (c) Orbit doubling, after the switch: `≤ δ_R ν(N_j)(ν(N_j) + E_ks) + E_ks + B_scale`. -/
theorem orbit_step_noise_le (N : Ct) (h : 0 ≤ N.noise) :
    (M.orbitStep N).noise ≤ M.δ * N.noise * (N.noise + M.E_ks) + M.E_ks + M.B_scale := by
  have := M.mul_noise_le N (M.aut N) h (M.aut_nonneg h)
  simpa [orbitStep, aut_noise] using this

/-- (d) Assembly, exact (before the switch of the last product):
`ν_out = ‖c‖₁ (δ_R ν(ct_o) ν(x^{r−1}) + E_ks) + |c₁| ν_in`. -/
theorem assembly_noise_raw (o u ct : Ct) (nc nc1 : ℝ) :
    (M.add (M.ptct nc (M.mulRaw o u)) (M.ptct nc1 ct)).noise =
      nc * (M.δ * o.noise * u.noise + M.E_ks) + nc1 * ct.noise := by
  simp

/-- (d) Assembly, the paper's form (`‖c‖₁ ≤ 1`):
`ν_out ≤ δ_R ν(x^{r−1}) ν(ct_o) + |c₁| ν_in + E_ks`. -/
theorem assembly_noise_le (o u ct : Ct) (nc nc1 : ℝ) (hnc : nc ≤ 1)
    (ho : 0 ≤ o.noise) (hu : 0 ≤ u.noise) :
    (M.add (M.ptct nc (M.mulRaw o u)) (M.ptct nc1 ct)).noise ≤
      M.δ * u.noise * o.noise + nc1 * ct.noise + M.E_ks := by
  rw [assembly_noise_raw]
  have h0 : 0 ≤ M.δ * o.noise * u.noise + M.E_ks := by
    have := M.δ_nonneg; have := M.E_ks_nonneg; positivity
  nlinarith

/-- (d) Assembly as performed by the program (switched product):
`ν_out ≤ ‖c‖₁ (δ_R ν(ct_o) ν(x^{r−1}) + E_ks + B_scale) + |c₁| ν_in`. -/
theorem assembly_noise_le' (o u ct : Ct) (nc nc1 : ℝ) (hnc0 : 0 ≤ nc)
    (ho : 0 ≤ o.noise) (hu : 0 ≤ u.noise) :
    (M.add (M.ptct nc (M.mul o u)) (M.ptct nc1 ct)).noise ≤
      nc * (M.δ * o.noise * u.noise + M.E_ks + M.B_scale) + nc1 * ct.noise := by
  simp only [add_noise, ptct_noise]
  have := mul_le_mul_of_nonneg_left (M.mul_noise_le o u ho hu) hnc0
  linarith

/-! ## 6. Decryption criterion and the sufficiency statement -/

/-- Decryption is correct iff `ν(ct) < q/2` (`q` the modulus at the ciphertext's level). -/
def correct (q : ℝ) (ct : Ct) : Prop := ct.noise < q / 2

theorem correct_iff (q : ℝ) (ct : Ct) : correct q ct ↔ ct.noise < q / 2 := Iff.rfl

/-- Capacity `κ(ct) = log₂(q/ν)`; correctness iff `κ > 1`. -/
noncomputable def capacity (q : ℝ) (ct : Ct) : ℝ := Real.logb 2 (q / ct.noise)

theorem correct_iff_capacity (q : ℝ) (ct : Ct) (hq : 0 < q) (hν : 0 < ct.noise) :
    correct q ct ↔ 1 < capacity q ct := by
  unfold correct capacity
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_one,
    lt_div_iff₀ hν]
  constructor <;> intro h <;> linarith

/-- **Sufficiency.**  Let `chain ℓ` be the modulus `q_ℓ` available after `ℓ` switches and let
the chain provide `L ≥ L_prog` levels (`k, g ≥ 2`).  If the recursive worst-case bound
computed by the model — which *is* the noise of the program's output — stays below
`q_{L_prog}/2`, then the output of ComposedEval decrypts correctly, at a level covered by
the chain.  (No numeric ring constants are needed: the bound is the hypothesis.) -/
theorem composedEval_correct_of_bound (chain : ℕ → ℝ) (L r k g d : ℕ) (nC : ℕ → ℝ)
    (nc nc1 : ℝ) (ct : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g)
    (hL : ct.level + L_prog r k g d ≤ L)
    (hbound : (M.composedEval bal r k g d nC nc nc1 ct).1.noise <
      chain (ct.level + L_prog r k g d) / 2) :
    let out := (M.composedEval bal r k g d nC nc nc1 ct).1
    correct (chain out.level) out ∧ out.level ≤ L := by
  intro out
  have hlev : out.level = ct.level + L_prog r k g d :=
    M.composedEval_level r k g d nC nc nc1 ct hk hg
  refine ⟨?_, by omega⟩
  unfold correct
  rw [hlev]
  exact hbound

/-! ## 7. Key-switching counts -/

/-- The number of key-switch-bearing operations of the composed program:
`(products, automorphisms) = (chainMuls r + (k−2) + ⌈log₂ g⌉ + (g−1) + ⌈log₂ d⌉ + 1, ⌈log₂ d⌉)`
for `k, g ≥ 2`; the total is `chainMuls r + (k−2) + ⌈log₂ g⌉ + (g−1) + 2⌈log₂ d⌉ + 1`. -/
theorem composedEval_ks (rec : ℕ → ℕ × ℕ) (r k g d : ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct)
    (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.composedEval rec r k g d nC nc nc1 ct).2 =
      (chainMuls r + (k - 2) + Nat.clog 2 g + (g - 1) + Nat.clog 2 d + 1, Nat.clog 2 d) := by
  have hm : 1 ≤ Nat.clog 2 g := Nat.clog_pos (by norm_num) (by omega)
  simp only [composedEval, powerChain_ks, powTable_ks, orbit_ks]
  rw [M.psRec_ks _ _ g 0 (by omega)]
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  omega

/-- Total number of key-switch-bearing operations. -/
def ksTotal (c : KS) : ℕ := c.1 + c.2

theorem composedEval_ksTotal (rec : ℕ → ℕ × ℕ) (r k g d : ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ)
    (ct : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g) :
    ksTotal (M.composedEval rec r k g d nC nc nc1 ct).2 =
      chainMuls r + (k - 2) + Nat.clog 2 g + (g - 1) + 2 * Nat.clog 2 d + 1 := by
  rw [M.composedEval_ks rec r k g d nC nc nc1 ct hk hg, ksTotal]; omega

/-- Instance (Case IV): `4 + 3 + 3 + 4 + 4 + 1 = 19` products and `4` automorphisms, `23` in total. -/
theorem composedEval_ks_instance (rec : ℕ → ℕ × ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct) :
    (M.composedEval rec 6 5 5 14 nC nc nc1 ct).2 = (19, 4) := by
  rw [M.composedEval_ks rec 6 5 5 14 nC nc nc1 ct (by norm_num) (by norm_num)]; decide

theorem composedEval_ksTotal_instance (rec : ℕ → ℕ × ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct) :
    ksTotal (M.composedEval rec 6 5 5 14 nC nc nc1 ct).2 = 23 := by
  rw [M.composedEval_ks_instance]; rfl

/-- The baseline issues `1 + (k₀ − 2) + ⌈log₂ g₀⌉ + (g₀ − 1) + 1` products and no automorphism. -/
theorem baselineEval_ks (rec : ℕ → ℕ × ℕ) (k₀ g₀ : ℕ) (nQ : ℕ → ℝ) (ct : Ct)
    (hk : 2 ≤ k₀) (hg : 2 ≤ g₀) :
    (M.baselineEval rec k₀ g₀ nQ ct).2 = (1 + (k₀ - 2) + Nat.clog 2 g₀ + (g₀ - 1) + 1, 0) := by
  have hm : 1 ≤ Nat.clog 2 g₀ := Nat.clog_pos (by norm_num) (by omega)
  simp only [baselineEval, powTable_ks]
  rw [M.psRec_ks _ _ g₀ 0 (by omega)]
  simp only [Prod.mk_add_mk, Prod.mk.injEq, and_true]
  omega

/-- Instance: the baseline issues `54 > 50` key-switch-bearing operations. -/
theorem baselineEval_ks_instance (rec : ℕ → ℕ × ℕ) (nQ : ℕ → ℝ) (ct : Ct) :
    (M.baselineEval rec 25 25 nQ ct).2 = (54, 0) := by
  rw [M.baselineEval_ks rec 25 25 nQ ct (by norm_num) (by norm_num)]; decide

/-- Each key-switch-bearing operation adds exactly one `E_ks` term in the model
(products via (15), automorphisms via (16)). -/
theorem mulRaw_adds_E_ks (c₁ c₂ : Ct) :
    (M.mulRaw c₁ c₂).noise = M.δ * c₁.noise * c₂.noise + M.E_ks := rfl
theorem aut_adds_E_ks (ct : Ct) : (M.aut ct).noise = ct.noise + M.E_ks := rfl

end NoiseModel

/-! ## 9. The phase table of Appendix C.5 (round 5)

The paper's table lists, per phase of Algorithm 2, the number of relinearised products,
the number of automorphisms, and the levels consumed:

| phase | products | automorphisms | levels |
|---|---|---|---|
| 1 power chain | `r − 1` (program: `chainMuls r`) | 0 | `δ_r` |
| 2–4 Paterson–Stockmeyer on `C` | `(k−2) + ⌈log₂ g⌉ + (g−1)` | 0 | `⌈log₂ k⌉ + ⌈log₂ g⌉ + 1` |
| 5 orbit doubling | `⌈log₂ d⌉` | `⌈log₂ d⌉` | `⌈log₂ d⌉` |
| 6 assembly | 1 | 0 | 1 |

`phase_table` proves each row against the straight-line program (`powerChain`, `psPhase`,
`orbit`, `assembly`), `L_comp_eq_phase_sum` is the level column summed, and
`composedEval_ks_eq_phase_sum` the two operation columns summed. -/

/-- A row of the phase table: relinearised products, automorphisms, levels. -/
structure PhaseRow where
  muls : ℕ
  auts : ℕ
  levels : ℕ
  deriving DecidableEq, Repr

/-- Row 1, power chain: `chainMuls r` products, `δ_r` levels. -/
def row1 (r : ℕ) : PhaseRow := ⟨NoiseModel.chainMuls r, 0, NoiseModel.deltaR r⟩
/-- Rows 2–4, Paterson–Stockmeyer on `C`: `(k−2) + ⌈log₂ g⌉ + (g−1)` products,
    `⌈log₂ k⌉ + ⌈log₂ g⌉ + 1` levels. -/
def row24 (k g : ℕ) : PhaseRow :=
  ⟨(k - 2) + Nat.clog 2 g + (g - 1), 0, Nat.clog 2 k + Nat.clog 2 g + 1⟩
/-- Row 5, orbit doubling: `⌈log₂ d⌉` products, `⌈log₂ d⌉` automorphisms, `⌈log₂ d⌉` levels. -/
def row5 (d : ℕ) : PhaseRow := ⟨Nat.clog 2 d, Nat.clog 2 d, Nat.clog 2 d⟩
/-- Row 6, assembly: one product, one level. -/
def row6 : PhaseRow := ⟨1, 0, 1⟩

/-- The paper's table (with the program's chain length `chainMuls r` in Phase 1). -/
def phaseTable (r k g d : ℕ) : List PhaseRow := [row1 r, row24 k g, row5 d, row6]

namespace NoiseModel

variable (M : NoiseModel)

/-- Phases 2–4 of the composed program in isolation (baby steps, `Z = Y^k`, giant-step
    squarings, block sums and the PS recursion), returning `(ct, (products, automorphisms))`. -/
def psPhase (rec : ℕ → ℕ × ℕ) (k g : ℕ) (nC : ℕ → ℝ) (Y : Ct) : Ct × KS :=
  let T := M.powTable rec Y (k - 1)
  let Z := M.mul (T.1 (k - 1)) (T.1 1)
  let m := Nat.clog 2 g
  let Zp := M.giantPow Z
  let blk := M.block T.1 k nC
  let ps := M.psRec Zp blk g 0
  (ps.1, T.2 + (1 + (m - 1), 0) + ps.2)

/-- Phase 6 in isolation: `c · Mul(ct_o, ct_u) + c₁ · ct`. -/
def assembly (nc nc1 : ℝ) (o u ct : Ct) : Ct × KS :=
  (M.add (M.ptct nc (M.mul o u)) (M.ptct nc1 ct), (1, 0))

/-- The composed program is the composition of its phases (definitional). -/
theorem composedEval_eq_phases (rec : ℕ → ℕ × ℕ) (r k g d : ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ)
    (ct : Ct) :
    M.composedEval rec r k g d nC nc nc1 ct =
      (let ch := M.powerChain r ct
       let ps := M.psPhase rec k g nC ch.1
       let orb := M.orbit (Nat.clog 2 d) ps.1
       let out := M.assembly nc nc1 orb.1 ch.2.1 ct
       (out.1, ch.2.2 + ps.2 + orb.2 + out.2)) := by
  simp only [composedEval, psPhase, assembly, add_assoc]

/-- Phases 2–4, balanced baby steps: exact level `⌈log₂(k−1)⌉ + 1 + ⌈log₂ g⌉` above `Y`. -/
theorem psPhase_level (k g : ℕ) (nC : ℕ → ℝ) (Y : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.psPhase bal k g nC Y).1.level = Y.level + (Nat.clog 2 (k - 1) + 1 + Nat.clog 2 g) := by
  have hT := M.powTable_bal_level Y (k - 1)
  have hT1 := M.powTable_apply_one bal Y (k - 1)
  have hTk := hT (k - 1) (by omega) le_rfl
  set T := M.powTable bal Y (k - 1) with hTdef
  set Z := M.mul (T.1 (k - 1)) (T.1 1) with hZdef
  have hZ : Z.level = Y.level + Nat.clog 2 (k - 1) + 1 := by
    rw [hZdef, mul_level, hTk, hT1]; omega
  have hZp : ∀ i, (M.giantPow Z i).level = Z.level + i := M.giantPow_level Z
  have hblk : ∀ j, (M.block T.1 k nC j).level ≤ Z.level := by
    intro j
    apply M.sumCt_level_le
    intro i hi
    rw [ptct_level]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [M.powTable_apply_zero]; simp
    · rw [hT i hpos (by omega), hZ]
      have := Nat.clog_mono_right 2 (show i ≤ k - 1 by omega)
      omega
  have hps := M.psRec_level (M.giantPow Z) (M.block T.1 k nC) Z.level hZp hblk hg 0
  simp only [psPhase]
  rw [← hTdef, ← hZdef, hps, hZ]
  omega

/-- Phases 2–4: the level is at most the paper's row `⌈log₂ k⌉ + ⌈log₂ g⌉ + 1`. -/
theorem psPhase_level_le (k g : ℕ) (nC : ℕ → ℝ) (Y : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.psPhase bal k g nC Y).1.level ≤ Y.level + (Nat.clog 2 k + Nat.clog 2 g + 1) := by
  rw [M.psPhase_level k g nC Y hk hg]
  have := clog_pred_le k
  omega

/-- Phases 2–4: `(k − 2) + ⌈log₂ g⌉ + (g − 1)` products, no automorphism (any recipe). -/
theorem psPhase_ks (rec : ℕ → ℕ × ℕ) (k g : ℕ) (nC : ℕ → ℝ) (Y : Ct) (hg : 2 ≤ g) :
    (M.psPhase rec k g nC Y).2 = ((k - 2) + Nat.clog 2 g + (g - 1), 0) := by
  have hm : 1 ≤ Nat.clog 2 g := Nat.clog_pos (by norm_num) (by omega)
  simp only [psPhase, powTable_ks]
  rw [M.psRec_ks _ _ g 0 (by omega)]
  simp only [Prod.mk_add_mk, Prod.mk.injEq, and_true]
  omega

/-- Phase 6: one product, one level above `max(level ct_o, level ct_u)` (and at least the
    level of the input). -/
theorem assembly_level (nc nc1 : ℝ) (o u ct : Ct) :
    (M.assembly nc nc1 o u ct).1.level = max (max o.level u.level + 1) ct.level := by
  simp [assembly]

theorem assembly_ks (nc nc1 : ℝ) (o u ct : Ct) : (M.assembly nc nc1 o u ct).2 = (1, 0) := rfl

/-- **The phase table**, row by row, against the program (`k, g ≥ 2`, balanced baby steps):
    Phase 1 consumes `δ_r` levels with `chainMuls r` products; Phases 2–4 consume
    `⌈log₂(k−1)⌉ + 1 + ⌈log₂ g⌉ ≤ ⌈log₂ k⌉ + ⌈log₂ g⌉ + 1` levels with
    `(k−2) + ⌈log₂ g⌉ + (g−1)` products; Phase 5 consumes `⌈log₂ d⌉` levels with `⌈log₂ d⌉`
    products and `⌈log₂ d⌉` automorphisms; Phase 6 consumes one level with one product. -/
theorem phase_table (r k g d : ℕ) (nC : ℕ → ℝ) (nc nc1 : ℝ) (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (∀ ct : Ct, (M.powerChain r ct).1.level = ct.level + (row1 r).levels ∧
        (M.powerChain r ct).2.1.level = ct.level + (row1 r).levels ∧
        (M.powerChain r ct).2.2 = ((row1 r).muls, (row1 r).auts)) ∧
    (∀ Y : Ct, (M.psPhase bal k g nC Y).1.level ≤ Y.level + (row24 k g).levels ∧
        (M.psPhase bal k g nC Y).2 = ((row24 k g).muls, (row24 k g).auts)) ∧
    (∀ N : Ct, (M.orbit (Nat.clog 2 d) N).1.level = N.level + (row5 d).levels ∧
        (M.orbit (Nat.clog 2 d) N).2 = ((row5 d).muls, (row5 d).auts)) ∧
    (∀ o u ct : Ct, (M.assembly nc nc1 o u ct).1.level =
          max (max o.level u.level + row6.levels) ct.level ∧
        (M.assembly nc nc1 o u ct).2 = (row6.muls, row6.auts)) := by
  simp only [row1, row24, row5, row6]
  refine ⟨fun ct => ⟨M.powerChain_Y_level r ct, M.powerChain_u_level r ct, M.powerChain_ks r ct⟩,
    fun Y => ⟨M.psPhase_level_le k g nC Y hk hg, M.psPhase_ks bal k g nC Y hg⟩,
    fun N => ⟨M.orbit_level _ N, M.orbit_ks _ N⟩,
    fun o u ct => ⟨M.assembly_level nc nc1 o u ct, M.assembly_ks nc nc1 o u ct⟩⟩

end NoiseModel

/-- **`L_comp` is the level column of the phase table summed.** -/
theorem L_comp_eq_phase_sum (r k g d : ℕ) :
    NoiseModel.L_comp' r k g d = ((phaseTable r k g d).map PhaseRow.levels).sum := by
  simp only [phaseTable, row1, row24, row5, row6, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, NoiseModel.L_comp']
  omega

/-- The same for the paper's `L_comp(r, deg C, d)` with `k = ⌈√deg C⌉`, `g = ⌈(deg C+1)/k⌉`. -/
theorem L_comp_eq_phase_sum' (r degC d : ℕ) :
    L_comp r degC d = ((phaseTable r (kOf degC) (gOf degC) d).map PhaseRow.levels).sum :=
  L_comp_eq_phase_sum r _ _ d

/-- **The operation columns summed** are the program's key-switch counts:
    products `= Σ muls`, automorphisms `= Σ auts` (`k, g ≥ 2`). -/
theorem composedEval_ks_eq_phase_sum (M : NoiseModel) (rec : ℕ → ℕ × ℕ) (r k g d : ℕ)
    (nC : ℕ → ℝ) (nc nc1 : ℝ) (ct : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.composedEval rec r k g d nC nc nc1 ct).2 =
      (((phaseTable r k g d).map PhaseRow.muls).sum,
        ((phaseTable r k g d).map PhaseRow.auts).sum) := by
  rw [M.composedEval_ks rec r k g d nC nc nc1 ct hk hg]
  simp only [phaseTable, row1, row24, row5, row6, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ext <;> simp only <;> omega

/-- The program's level (balanced baby steps) is at most the level column summed. -/
theorem composedEval_level_le_phase_sum (M : NoiseModel) (r k g d : ℕ) (nC : ℕ → ℝ)
    (nc nc1 : ℝ) (ct : Ct) (hk : 2 ≤ k) (hg : 2 ≤ g) :
    (M.composedEval NoiseModel.bal r k g d nC nc nc1 ct).1.level ≤
      ct.level + ((phaseTable r k g d).map PhaseRow.levels).sum := by
  rw [M.composedEval_level r k g d nC nc nc1 ct hk hg, ← L_comp_eq_phase_sum]
  have := NoiseModel.L_prog_le_L_comp' r k g d
  omega

/-- Case IV instance of the table: rows `(4,0,3)`, `(10,0,7)`, `(4,4,4)`, `(1,0,1)`;
    columns sum to `19` products, `4` automorphisms, `15` levels. -/
theorem phaseTable_instance :
    phaseTable 6 5 5 14 = [⟨4, 0, 3⟩, ⟨10, 0, 7⟩, ⟨4, 4, 4⟩, ⟨1, 0, 1⟩] := by
  simp only [phaseTable, row1, row24, row5, row6]
  decide

theorem phaseTable_instance_sums :
    ((phaseTable 6 5 5 14).map PhaseRow.muls).sum = 19 ∧
      ((phaseTable 6 5 5 14).map PhaseRow.auts).sum = 4 ∧
      ((phaseTable 6 5 5 14).map PhaseRow.levels).sum = 15 := by
  rw [phaseTable_instance]; decide

/-! ## 8. Correctness of Algorithm 3 at the plaintext level (exact, algebraic) -/

section Correctness

variable {R : Type*} [CommRing R]

/-- Step 6 of Algorithm 3: `A⁻¹((A·m + q·I) − q·I) = m` for a unit `A`. -/
theorem recover (A : Rˣ) (q m I : R) : (↑A⁻¹ : R) * ((↑A * m + q * I) - q * I) = m := by
  simp

/-- If Step 5 returns `P_A(w_i) = I_i` on every slot, then Step 6 returns `m_i` on every slot. -/
theorem step6_of_step5 {ι : Type*} (A : Rˣ) (q : R) (m I w : ι → R) (PA : R → R)
    (h5 : ∀ i, PA (w i) = I i) (i : ι) :
    (↑A⁻¹ : R) * ((↑A * m i + q * I i) - q * PA (w i)) = m i := by
  rw [h5]; exact recover A q (m i) (I i)

open Polynomial in
/-- **Correctness of Algorithm 3 on the slots**, assembled from
`Galois.composed_correct` (Step 5) and `recover` (Step 6): with the factored form
`P = c₁X + X^{r−1}Q(X^r)`, the coset relation `c·Orb_d(C) = Q + ΓH`, slot values `w_i` with
`φ(w_i^r) = w_i^r`, `Γ(w_i^r) = 0`, and the composed value equal to the overflow digit `I_i`,
the ciphertext `A⁻¹(ct_up − q·ct_I)` holds `m_i` in every slot. -/
theorem full_boot_slots {ι : Type*} (φ : R →+* R) {c₁ c : R} {r d : ℕ}
    {P Q Γ H Cp : R[X]}
    (hP : P = C c₁ * X + X ^ (r - 1) * expand R r Q)
    (h : C c * Galois.orbProd (mapRingHom φ) d Cp = Q + Γ * H)
    (w m I : ι → R)
    (hx : ∀ i, φ (w i ^ r) = w i ^ r) (hΓ : ∀ i, Γ.eval (w i ^ r) = 0)
    (h5 : ∀ i, c₁ * w i + w i ^ (r - 1) * (c * Galois.orbProd φ d (Cp.eval (w i ^ r))) = I i)
    (A : Rˣ) (q : R) (i : ι) :
    (↑A⁻¹ : R) * ((↑A * m i + q * I i) - q * P.eval (w i)) = m i := by
  apply step6_of_step5 A q m I w (fun x => P.eval x)
  intro j
  rw [Galois.composed_correct φ hP h (hx j) (hΓ j)]
  exact h5 j

end Correctness

end BGVNoise
