/-
  Crystallographic.lean

  Formal verification (Lean 4 + Mathlib) of

    Theorem "Crystallographic restriction in rank two"
    (Section "Preliminaries", proof in Appendix "The crystallographic restriction")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping":
  an integer `2 × 2` matrix `M` of finite multiplicative order has `det M = ±1`
  and order `r ∈ {1, 2, 3, 4, 6}`; `det M = −1` forces `r = 2`; `det M = 1`
  forces `M = ±I` or `tr M ∈ {−1, 0, 1}` with `r = 3, 4, 6` respectively.

  The proof avoids complex eigenvalues.  It uses the `2 × 2` Cayley–Hamilton
  identity `M² = (tr M)·M − (det M)·I` to write `Mⁿ⁺¹ = aₙ₊₁ M − d·aₙ I` with
  the Lucas-type sequence `a₀ = 0, a₁ = 1, aₙ₊₂ = t·aₙ₊₁ − d·aₙ`
  (`t = tr M`, `d = det M`), and an elementary growth argument for `aₙ`.
  With no unproved placeholders:

  * `cayley_hamilton`            `M * M = tr M • M − det M • 1`
  * `pow_succ_eq_lucas`          `M^(n+1) = a(n+1) • M − (d·a n) • 1`
  * `det_eq_one_or_neg_one`      finite order ⟹ `det M = ±1`
  * `lucas_pos_of_two_le`, `lucas_pos_of_one_le_of_nonpos`, `lucas_neg`,
    `lucas_ne_zero_of_two_le_abs`, `lucas_ne_zero_of_det_neg`   the growth lemmas
  * `scalar_or_lucas_eq_zero`, `pm_one_or_lucas_eq_zero`
                                 `M^r = 1` ⟹ `M = ±I` or `a_r = 0`
  * `abs_trace_le_two`           finite order ⟹ `|tr M| ≤ 2`
  * `eq_one_of_trace_two`, `eq_neg_one_of_trace_neg_two`   unipotent ⟹ `±I`
  * `classification`             the full case analysis of the theorem
  * `orderOf_mem`                `orderOf M ∈ {1, 2, 3, 4, 6}`
  * `orderOf_eq_two_of_det_neg_one`, `orderOf_eq_three`, `orderOf_eq_four`,
    `orderOf_eq_six`              exact orders in each case
  * `MA_orderOf_three/four/six`  the companion matrices `M_A` of `Φ₃, Φ₄, Φ₆`
-/
import Mathlib
import SymmetryGraded.Lattice

namespace Crystallographic

open Matrix

/-- Integer `2 × 2` matrices. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ

/-! ## 1. Cayley–Hamilton in rank two -/

/-- Cayley–Hamilton for `2 × 2` integer matrices: `M² = (tr M)·M − (det M)·I`. -/
theorem cayley_hamilton (M : M2) : M * M = M.trace • M - M.det • (1 : M2) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The Lucas-type sequence `a₀ = 0, a₁ = 1, aₙ₊₂ = t·aₙ₊₁ − d·aₙ`. -/
def lucas (t d : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => t * lucas t d (n + 1) - d * lucas t d n

@[simp] lemma lucas_zero (t d : ℤ) : lucas t d 0 = 0 := rfl
@[simp] lemma lucas_one (t d : ℤ) : lucas t d 1 = 1 := rfl
lemma lucas_succ_succ (t d : ℤ) (n : ℕ) :
    lucas t d (n + 2) = t * lucas t d (n + 1) - d * lucas t d n := rfl

/-- `Mⁿ⁺¹ = aₙ₊₁·M − (d·aₙ)·I` with `a = lucas (tr M) (det M)`. -/
theorem pow_succ_eq_lucas (M : M2) (n : ℕ) :
    M ^ (n + 1) = lucas M.trace M.det (n + 1) • M - (M.det * lucas M.trace M.det n) • (1 : M2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, cayley_hamilton,
        lucas_succ_succ]
      module

/-! ## 2. Determinant -/

/-- Finite order forces `det M = ±1`. -/
theorem det_eq_one_or_neg_one (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1) :
    M.det = 1 ∨ M.det = -1 := by
  have h : M.det ^ r = 1 := by rw [← Matrix.det_pow, hM, Matrix.det_one]
  have h1 : |M.det| ^ r = 1 := by rw [← abs_pow, h, abs_one]
  have h2 : |M.det| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by omega)).mp h1
  rcases (abs_eq zero_le_one).mp h2 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ## 3. Growth of the Lucas sequence -/

/-- For `t ≥ 2` and `|d| ≤ 1` the sequence is nondecreasing and positive from `n = 1`. -/
theorem lucas_pos_of_two_le {t d : ℤ} (ht : 2 ≤ t) (hd : |d| ≤ 1) (n : ℕ) :
    0 ≤ lucas t d n ∧ lucas t d n ≤ lucas t d (n + 1) ∧ 1 ≤ lucas t d (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨h0, hmono, h1⟩ := ih
      rw [abs_le] at hd
      have hda : d * lucas t d n ≤ lucas t d (n + 1) := by nlinarith
      have hta : 2 * lucas t d (n + 1) ≤ t * lucas t d (n + 1) := by nlinarith
      rw [lucas_succ_succ]
      refine ⟨by linarith, by linarith, by linarith⟩

/-- For `t ≥ 1` and `d ≤ 0` the sequence is nondecreasing and positive from `n = 1`. -/
theorem lucas_pos_of_one_le_of_nonpos {t d : ℤ} (ht : 1 ≤ t) (hd : d ≤ 0) (n : ℕ) :
    0 ≤ lucas t d n ∧ lucas t d n ≤ lucas t d (n + 1) ∧ 1 ≤ lucas t d (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨h0, hmono, h1⟩ := ih
      have hda : d * lucas t d n ≤ 0 := by nlinarith
      have hta : lucas t d (n + 1) ≤ t * lucas t d (n + 1) := by nlinarith
      rw [lucas_succ_succ]
      refine ⟨by linarith, by linarith, by linarith⟩

/-- Sign symmetry: `lucas (−t) d n = (−1)^(n+1) · lucas t d n`. -/
theorem lucas_neg (t d : ℤ) (n : ℕ) :
    lucas (-t) d n = (-1) ^ (n + 1) * lucas t d n ∧
      lucas (-t) d (n + 1) = (-1) ^ (n + 2) * lucas t d (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      rw [lucas_succ_succ, lucas_succ_succ, h1, h2]
      ring

/-- `|t| ≥ 2` and `|d| ≤ 1` ⟹ `lucas t d r ≠ 0` for `r ≥ 1`. -/
theorem lucas_ne_zero_of_two_le_abs {t d : ℤ} (ht : 2 ≤ |t|) (hd : |d| ≤ 1) {r : ℕ}
    (hr : 1 ≤ r) : lucas t d r ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rcases le_or_gt 0 t with hpos | hneg
  · rw [abs_of_nonneg hpos] at ht
    have := (lucas_pos_of_two_le ht hd n).2.2
    omega
  · rw [abs_of_neg hneg] at ht
    have h := (lucas_pos_of_two_le ht hd n).2.2
    have hsym := (lucas_neg (-t) d n).2
    rw [neg_neg] at hsym
    rw [hsym]
    intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 (pow_ne_zero _ (by norm_num))
    · omega

/-- `t ≠ 0` and `d = −1` ⟹ `lucas t d r ≠ 0` for `r ≥ 1`. -/
theorem lucas_ne_zero_of_det_neg {t : ℤ} (ht : t ≠ 0) {r : ℕ} (hr : 1 ≤ r) :
    lucas t (-1) r ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have h := (lucas_pos_of_one_le_of_nonpos (t := -t) (d := -1) (by omega) (by norm_num) n).2.2
    have hsym := (lucas_neg (-t) (-1) n).2
    rw [neg_neg] at hsym
    rw [hsym]
    intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 (pow_ne_zero _ (by norm_num))
    · omega
  · have := (lucas_pos_of_one_le_of_nonpos (t := t) (d := -1) (by omega) (by norm_num) n).2.2
    omega

/-! ## 4. Scalar or `a_r = 0` -/

/-- If `a • M − b • 1 = 1` with `a ≠ 0` then `M` is a scalar matrix. -/
lemma scalar_of_smul_sub (M : M2) {a b : ℤ} (h : a • M - b • (1 : M2) = 1) (ha : a ≠ 0) :
    ∃ c : ℤ, M = c • (1 : M2) := by
  have hE : ∀ i j, a * M i j - b * (1 : M2) i j = (1 : M2) i j := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using this
  have h01 := hE 0 1
  have h10 := hE 1 0
  have h00 := hE 0 0
  have h11 := hE 1 1
  norm_num [Matrix.one_apply] at h01 h10 h00 h11
  refine ⟨M 0 0, ?_⟩
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]
  · rcases h01 with h | h
    · exact absurd h ha
    · exact h
  · rcases h10 with h | h
    · exact absurd h ha
    · exact h
  · have : a * (M 0 0 - M 1 1) = 0 := by linear_combination h00 - h11
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha
    · linarith

/-- `M^r = 1` (`r ≥ 1`) forces `M` scalar or `a_r = 0`. -/
theorem scalar_or_lucas_eq_zero (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1) :
    (∃ c : ℤ, M = c • (1 : M2)) ∨ lucas M.trace M.det r = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ_eq_lucas] at hM
  by_cases ha : lucas M.trace M.det (n + 1) = 0
  · exact Or.inr ha
  · exact Or.inl (scalar_of_smul_sub M hM ha)

/-- A scalar matrix of finite order is `±I`. -/
theorem scalar_pow_eq_one (M : M2) {c : ℤ} (hc : M = c • (1 : M2)) {r : ℕ} (hr : 1 ≤ r)
    (hM : M ^ r = 1) : M = 1 ∨ M = -1 := by
  rw [hc, smul_pow, one_pow] at hM
  have hE := congrFun (congrFun hM 0) 0
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] at hE
  have h1 : |c| ^ r = 1 := by rw [← abs_pow, hE, abs_one]
  have h2 : |c| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by omega)).mp h1
  rcases (abs_eq zero_le_one).mp h2 with h | h
  · left; rw [hc, h, one_smul]
  · right; rw [hc, h, neg_one_smul]

/-- Either `M = ±I`, or `M` is not scalar and `a_r = 0`. -/
theorem pm_one_or_lucas_eq_zero (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1) :
    M = 1 ∨ M = -1 ∨ lucas M.trace M.det r = 0 := by
  rcases scalar_or_lucas_eq_zero M hr hM with ⟨c, hc⟩ | hz
  · rcases scalar_pow_eq_one M hc hr hM with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hz)

/-! ## 5. `|tr M| ≤ 2` -/

/-- (Theorem "Crystallographic restriction", trace bound.)  Every integer `2 × 2`
    matrix of finite order has `|tr M| ≤ 2`. -/
theorem abs_trace_le_two (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1) :
    |M.trace| ≤ 2 := by
  have hd : |M.det| ≤ 1 := by
    rcases det_eq_one_or_neg_one M hr hM with h | h <;> rw [h] <;> norm_num
  rcases pm_one_or_lucas_eq_zero M hr hM with h | h | hz
  · rw [h, Matrix.trace_one]; norm_num
  · rw [h, Matrix.trace_neg, Matrix.trace_one]; norm_num
  · by_contra hcon
    exact lucas_ne_zero_of_two_le_abs (by omega) hd hr hz

/-! ## 6. The case analysis -/

/-- `tr M = −1`, `det M = 1` ⟹ `M³ = 1`. -/
theorem pow_three_eq_one_of (M : M2) (ht : M.trace = -1) (hd : M.det = 1) : M ^ 3 = 1 := by
  have h := cayley_hamilton M
  rw [ht, hd] at h
  have h3 : M ^ 3 = M * (M * M) := by rw [pow_succ, pow_two, mul_assoc]
  rw [h3, h, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, h]
  module

/-- `tr M = 0`, `det M = 1` ⟹ `M² = −1`, hence `M⁴ = 1`. -/
theorem pow_two_eq_neg_one_of (M : M2) (ht : M.trace = 0) (hd : M.det = 1) : M ^ 2 = -1 := by
  have h := cayley_hamilton M
  rw [ht, hd] at h
  rw [pow_two, h]; module

theorem pow_four_eq_one_of (M : M2) (ht : M.trace = 0) (hd : M.det = 1) : M ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two_eq_neg_one_of M ht hd]; simp

/-- `tr M = 1`, `det M = 1` ⟹ `M³ = −1`, hence `M⁶ = 1`. -/
theorem pow_three_eq_neg_one_of (M : M2) (ht : M.trace = 1) (hd : M.det = 1) : M ^ 3 = -1 := by
  have h := cayley_hamilton M
  rw [ht, hd] at h
  have h3 : M ^ 3 = M * (M * M) := by rw [pow_succ, pow_two, mul_assoc]
  rw [h3, h, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, h]
  module

theorem pow_six_eq_one_of (M : M2) (ht : M.trace = 1) (hd : M.det = 1) : M ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, pow_three_eq_neg_one_of M ht hd]; simp

/-- `tr M = 0`, `det M = −1` ⟹ `M² = 1`. -/
theorem pow_two_eq_one_of_det_neg (M : M2) (ht : M.trace = 0) (hd : M.det = -1) :
    M ^ 2 = 1 := by
  have h := cayley_hamilton M
  rw [ht, hd] at h
  rw [pow_two, h]; module

/-- `tr M = ±2`, `det M = 1` ⟹ `(M ∓ 1)² = 0` (unipotent). -/
theorem unipotent_of (M : M2) (ht : M.trace = 2) (hd : M.det = 1) : (M - 1) ^ 2 = 0 := by
  have h := cayley_hamilton M
  rw [ht, hd] at h
  rw [pow_two, sub_mul, mul_sub, mul_sub, h, mul_one, one_mul, one_mul]; module

theorem unipotent_of_neg (M : M2) (ht : M.trace = -2) (hd : M.det = 1) : (M + 1) ^ 2 = 0 := by
  have h := cayley_hamilton M
  rw [ht, hd] at h
  rw [pow_two, add_mul, mul_add, mul_add, h, mul_one, one_mul, one_mul]; module

/-- A unipotent matrix of finite order is the identity: `tr M = 2`, `det M = 1`,
    `M^r = 1` ⟹ `M = 1` (and `tr M = −2` ⟹ `M = −1`). -/
theorem eq_one_of_trace_two (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1)
    (ht : M.trace = 2) (hd : M.det = 1) : M = 1 := by
  rcases pm_one_or_lucas_eq_zero M hr hM with h | h | hz
  · exact h
  · rw [h, Matrix.trace_neg, Matrix.trace_one] at ht; norm_num at ht
  · rw [ht, hd] at hz
    exact absurd hz (lucas_ne_zero_of_two_le_abs (by norm_num) (by norm_num) hr)

theorem eq_neg_one_of_trace_neg_two (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1)
    (ht : M.trace = -2) (hd : M.det = 1) : M = -1 := by
  rcases pm_one_or_lucas_eq_zero M hr hM with h | h | hz
  · rw [h, Matrix.trace_one] at ht; norm_num at ht
  · exact h
  · rw [ht, hd] at hz
    exact absurd hz (lucas_ne_zero_of_two_le_abs (by norm_num) (by norm_num) hr)

/-- (Theorem "Crystallographic restriction in rank two", full case analysis.)
    An integer `2 × 2` matrix with `M^r = 1`, `r ≥ 1`, is one of:
    `I`; `−I`; a reflection (`det = −1`, `tr = 0`, `M² = 1`); or a rotation of order
    `3`, `4`, `6` (`det = 1`, `tr = −1, 0, 1`, `M³ = 1`, `M⁴ = 1`, `M⁶ = 1`). -/
theorem classification (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1) :
    M = 1 ∨ M = -1 ∨
    (M.det = -1 ∧ M.trace = 0 ∧ M ^ 2 = 1) ∨
    (M.det = 1 ∧ M.trace = -1 ∧ M ^ 3 = 1) ∨
    (M.det = 1 ∧ M.trace = 0 ∧ M ^ 4 = 1) ∨
    (M.det = 1 ∧ M.trace = 1 ∧ M ^ 6 = 1) := by
  rcases pm_one_or_lucas_eq_zero M hr hM with h | h | hz
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have htr := abs_trace_le_two M hr hM
    rw [abs_le] at htr
    rcases det_eq_one_or_neg_one M hr hM with hd | hd
    · -- det = 1: `tr M = ±2` is excluded by the growth lemma
      have h2 : M.trace ≠ 2 := by
        intro ht; rw [ht, hd] at hz
        exact lucas_ne_zero_of_two_le_abs (by norm_num) (by norm_num) hr hz
      have hm2 : M.trace ≠ -2 := by
        intro ht; rw [ht, hd] at hz
        exact lucas_ne_zero_of_two_le_abs (by norm_num) (by norm_num) hr hz
      have : M.trace = -1 ∨ M.trace = 0 ∨ M.trace = 1 := by omega
      rcases this with ht | ht | ht
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, ht, pow_three_eq_one_of M ht hd⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, ht, pow_four_eq_one_of M ht hd⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hd, ht, pow_six_eq_one_of M ht hd⟩))))
    · -- det = −1: the trace must vanish
      have ht : M.trace = 0 := by
        by_contra hne
        rw [hd] at hz
        exact lucas_ne_zero_of_det_neg hne hr hz
      exact Or.inr (Or.inr (Or.inl ⟨hd, ht, pow_two_eq_one_of_det_neg M ht hd⟩))

/-! ## 7. Orders -/

/-- (Theorem "Crystallographic restriction", order statement.)
    `orderOf M ∈ {1, 2, 3, 4, 6}` for every integer `2 × 2` matrix of finite order. -/
theorem orderOf_mem (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1) :
    orderOf M ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  have hpos : 0 < orderOf M :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨r, by omega, hM⟩)
  have hdvd : orderOf M ∣ 6 ∨ orderOf M ∣ 4 := by
    rcases classification M hr hM with h | h | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · left; rw [h, orderOf_one]; norm_num
    · left; apply orderOf_dvd_of_pow_eq_one; rw [h]; norm_num
    · left; exact dvd_trans (orderOf_dvd_of_pow_eq_one h) (by norm_num)
    · left; exact dvd_trans (orderOf_dvd_of_pow_eq_one h) (by norm_num)
    · right; exact orderOf_dvd_of_pow_eq_one h
    · left; exact orderOf_dvd_of_pow_eq_one h
  have hle : orderOf M ≤ 6 := by
    rcases hdvd with h | h
    · exact Nat.le_of_dvd (by norm_num) h
    · exact le_trans (Nat.le_of_dvd (by norm_num) h) (by norm_num)
  interval_cases h : orderOf M <;> simp_all

/-- `det M = −1` and finite order ⟹ `orderOf M = 2`
    (the paper's "`det M = −1` forces `r = 2`"). -/
theorem orderOf_eq_two_of_det_neg_one (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1)
    (hd : M.det = -1) : orderOf M = 2 := by
  rcases classification M hr hM with h | h | ⟨-, -, h⟩ | ⟨h', -, -⟩ | ⟨h', -, -⟩ | ⟨h', -, -⟩
  · rw [h, Matrix.det_one] at hd; norm_num at hd
  · rw [h, Matrix.det_neg, Matrix.det_one] at hd; norm_num at hd
  · apply orderOf_eq_prime h
    intro h1; rw [h1, Matrix.det_one] at hd; norm_num at hd
  all_goals rw [h'] at hd; norm_num at hd

/-- `tr M = −1`, `det M = 1` ⟹ `orderOf M = 3`. -/
theorem orderOf_eq_three (M : M2) (ht : M.trace = -1) (hd : M.det = 1) : orderOf M = 3 := by
  apply orderOf_eq_prime (pow_three_eq_one_of M ht hd)
  intro h; rw [h, Matrix.trace_one] at ht; norm_num at ht

/-- `tr M = 0`, `det M = 1` ⟹ `orderOf M = 4`. -/
theorem orderOf_eq_four (M : M2) (ht : M.trace = 0) (hd : M.det = 1) : orderOf M = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · rw [pow_one, pow_two_eq_neg_one_of M ht hd]
    intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  · exact pow_four_eq_one_of M ht hd

/-- `tr M = 1`, `det M = 1` ⟹ `orderOf M = 6`. -/
theorem orderOf_eq_six (M : M2) (ht : M.trace = 1) (hd : M.det = 1) : orderOf M = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (pow_six_eq_one_of M ht hd)
  intro p hp hpd
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpd
  interval_cases p
  all_goals first
    | exact absurd hp (by decide)
    | exact absurd hpd (by decide)
    | -- p = 2: M^3 = −1 ≠ 1
      (rw [show (6 / 2 : ℕ) = 3 from rfl, pow_three_eq_neg_one_of M ht hd]
       intro h
       have := congrFun (congrFun h 0) 0
       simp at this)
    | -- p = 3: M^2 = M − 1 ≠ 1 (else M = 2I, of trace 4)
      (rw [show (6 / 3 : ℕ) = 2 from rfl]
       intro h
       have hch := cayley_hamilton M
       rw [ht, hd, one_smul, one_smul, ← pow_two, h] at hch
       have htr := congrArg Matrix.trace hch
       rw [Matrix.trace_sub, Matrix.trace_one, ht] at htr
       norm_num at htr)

/-- The companion matrices `M_A = [[τ, 1], [−1, 0]]` of `Φ₃, Φ₄, Φ₆` (τ = −1, 0, 1)
    have orders exactly `3, 4, 6`. -/
theorem MA_orderOf_three : orderOf (DigitLattice.MA (-1)) = 3 :=
  orderOf_eq_three _ (DigitLattice.MA_trace _) (DigitLattice.MA_det _)

theorem MA_orderOf_four : orderOf (DigitLattice.MA 0) = 4 :=
  orderOf_eq_four _ (DigitLattice.MA_trace _) (DigitLattice.MA_det _)

theorem MA_orderOf_six : orderOf (DigitLattice.MA 1) = 6 :=
  orderOf_eq_six _ (DigitLattice.MA_trace _) (DigitLattice.MA_det _)

/-- No integer `2 × 2` matrix has order `5`, nor any order `≥ 7`. -/
theorem no_order_five_or_ge_seven (M : M2) (h5 : orderOf M = 5 ∨ 7 ≤ orderOf M) : False := by
  have hpos : 0 < orderOf M := by omega
  have hmem := orderOf_mem M hpos (pow_orderOf_eq_one M)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

end Crystallographic
