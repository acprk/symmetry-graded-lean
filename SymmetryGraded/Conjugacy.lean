/-
  Conjugacy.lean

  Formal verification (Lean 4 + Mathlib) of the rank-two case of the

    Latimer--MacDuffee correspondence

  as it is used in "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping":
  the paper only needs that the `GL₂(ℤ)`-conjugacy class of an integer matrix with
  characteristic polynomial `Φ_r`, `r ∈ {3, 4, 6}`, is unique, because `ℤ[ζ_r]` is
  `ℤ[ω]` or `ℤ[i]`, a principal ideal domain, so there is a single ideal class.  That
  class-number-one input is replaced here by an explicit, self-contained reduction of
  binary quadratic forms of discriminant `τ² − 4 ∈ {−3, −4}`.

  With no unproved placeholders:

  * `qform`, `exists_repr`
        every integral binary quadratic form `A x² + B x y + C y²` of discriminant
        `D = B² − 4AC` with `−4 ≤ D < 0` represents `1` or `−1`.  Proof: strong
        induction on `|A|`; reduce `B` modulo `2A` to `|B'| ≤ |A|`, then
        `4|A||C'| = B'² − D ≤ A² + 4 ≤ 2A²` forces `|C'| < |A|`, and the swapped form
        `(C', −B', A)` has the same discriminant.  The bound `3m² ≤ 4 − τ²` of the
        classical argument is exactly what makes the descent stop at `|A| = 1`.
  * `entries`, `trace_det_of_sq`
        `M² = τ·M − I` with `τ² < 4` forces `tr M = τ` and `det M = 1` (a scalar
        solution would need `(2a − τ)² = τ² − 4 < 0`).
  * `exists_conj_comp` (the rank-two Latimer--MacDuffee statement)
        every `M ∈ M₂(ℤ)` with `M² = τ·M − I` and `τ² < 4` is `GL₂(ℤ)`-conjugate to the
        companion matrix `comp τ = [[0, −1], [1, τ]]`: a vector `v` with
        `det[v | Mv] = ±1` exists by `exists_repr`, and `U = [v | Mv]` intertwines.
  * `conj_of_sq_eq`
        any two such matrices (same `τ`) are `GL₂(ℤ)`-conjugate.
  * `exists_conj_MA`, `trace_mem_of_rotation`, `conj_MA_of_pow_eq_one`
        the paper's form: an intertwiner of finite order with `det M = 1`, `M ≠ ±I`,
        is conjugate to the companion matrix `M_A = [[τ, 1], [−1, 0]]` of `Φ_r`,
        `τ = tr M ∈ {−1, 0, 1}`, i.e. `r ∈ {3, 4, 6}`.
  * `conj_neg_one` (`r = 4`), `conj_eisenstein` (`r = 6`)
        the two instances used by the paper: `M² = −I` is conjugate to `[[0,−1],[1,0]]`
        and `M² = M − I` is conjugate to `[[0,−1],[1,1]]`.

  Not formalized: the general Latimer--MacDuffee theorem (conjugacy classes of integer
  matrices with a given irreducible characteristic polynomial ↔ ideal classes of the
  associated order), which is not needed: only the rank-two, class-number-one case is
  used, and it is proved here outright.
-/
import Mathlib
import SymmetryGraded.Lattice
import SymmetryGraded.Crystallographic

namespace Conjugacy

open Matrix Crystallographic

/-! ## 1. Binary quadratic forms of discriminant `−3` and `−4` -/

/-- The binary quadratic form `(A, B, C)` evaluated at `(x, y)`. -/
def qform (A B C x y : ℤ) : ℤ := A * x ^ 2 + B * x * y + C * y ^ 2

/-- A form of negative discriminant has a nonzero leading coefficient. -/
lemma leading_ne_zero {A B C D : ℤ} (hD : D < 0) (h : B ^ 2 - 4 * A * C = D) : A ≠ 0 := by
  rintro rfl
  nlinarith [sq_nonneg B]

/-- The middle coefficient can be reduced modulo `2A` to `|B'| ≤ |A|`. -/
lemma exists_reduced_middle {A : ℤ} (hA : A ≠ 0) (B : ℤ) :
    ∃ k : ℤ, |B + 2 * k * A| ≤ |A| := by
  have hpos : (0 : ℤ) < 2 * |A| := by
    have := abs_pos.mpr hA; omega
  have hr0 : 0 ≤ B % (2 * |A|) := Int.emod_nonneg B (by omega)
  have hr1 : B % (2 * |A|) < 2 * |A| := Int.emod_lt_of_pos B hpos
  have ht : 2 * |A| * (B / (2 * |A|)) + B % (2 * |A|) = B := Int.mul_ediv_add_emod B (2 * |A|)
  set t : ℤ := B / (2 * |A|) with htdef
  set r : ℤ := B % (2 * |A|) with hrdef
  rcases abs_cases A with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
  · rw [hA1] at ht hr1 ⊢
    by_cases hle : r ≤ A
    · refine ⟨-t, ?_⟩
      have e : B + 2 * (-t) * A = r := by linear_combination -ht
      rw [e, abs_of_nonneg hr0]; omega
    · refine ⟨-t - 1, ?_⟩
      have e : B + 2 * (-t - 1) * A = r - 2 * A := by linear_combination -ht
      rw [e, abs_le]; omega
  · rw [hA1] at ht hr1 ⊢
    by_cases hle : r ≤ -A
    · refine ⟨t, ?_⟩
      have e : B + 2 * t * A = r := by linear_combination -ht
      rw [e, abs_of_nonneg hr0]; omega
    · refine ⟨t + 1, ?_⟩
      have e : B + 2 * (t + 1) * A = r + 2 * A := by linear_combination -ht
      rw [e, abs_le]; omega

/-- Strong-induction core: a form of discriminant `D` with `−4 ≤ D < 0` represents `±1`. -/
theorem exists_repr_aux {D : ℤ} (hD1 : -4 ≤ D) (hD2 : D < 0) :
    ∀ (n : ℕ) (A B C : ℤ), A.natAbs = n → B ^ 2 - 4 * A * C = D →
      ∃ x y : ℤ, qform A B C x y = 1 ∨ qform A B C x y = -1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B C hn hdisc
    have hA : A ≠ 0 := leading_ne_zero hD2 hdisc
    have hnpos : 0 < n := by
      rw [← hn]; exact Int.natAbs_pos.mpr hA
    rcases eq_or_ne n 1 with h1 | h1
    · refine ⟨1, 0, ?_⟩
      have : A = 1 ∨ A = -1 := by
        rw [h1] at hn; omega
      rcases this with h | h <;> simp [qform, h]
    · -- `|A| ≥ 2`
      have hA2 : 2 ≤ |A| := by
        have : (A.natAbs : ℤ) = |A| := (Int.abs_eq_natAbs A).symm
        omega
      obtain ⟨k, hk⟩ := exists_reduced_middle hA B
      set B' : ℤ := B + 2 * k * A with hB'
      set C' : ℤ := A * k ^ 2 + B * k + C with hC'
      have hdisc' : B' ^ 2 - 4 * A * C' = D := by rw [hB', hC']; linear_combination hdisc
      have hprod : 4 * A * C' = B' ^ 2 - D := by linarith
      have habs : 4 * |A| * |C'| = B' ^ 2 - D := by
        have h4 : |4 * A * C'| = 4 * |A| * |C'| := by
          rw [abs_mul, abs_mul]; norm_num
        rw [← h4, hprod, abs_of_nonneg (by nlinarith [sq_nonneg B'])]
      have hB'sq : B' ^ 2 ≤ A ^ 2 := by
        have h1 : |B'| ≤ |A| := hk
        nlinarith [abs_nonneg B', abs_nonneg A, sq_abs B', sq_abs A]
      have hCabs : 2 * |C'| ≤ |A| := by nlinarith [sq_abs A, abs_nonneg C']
      have hC'ne : C' ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hprod
        nlinarith [sq_nonneg B']
      have hlt : C'.natAbs < n := by
        have e1 : (C'.natAbs : ℤ) = |C'| := (Int.abs_eq_natAbs C').symm
        have e2 : (A.natAbs : ℤ) = |A| := (Int.abs_eq_natAbs A).symm
        have : (1 : ℤ) ≤ |C'| := by
          have := abs_pos.mpr hC'ne; omega
        omega
      obtain ⟨x, y, hxy⟩ := ih C'.natAbs hlt C' (-B') A rfl (by linear_combination hdisc')
      refine ⟨y - k * x, -x, ?_⟩
      have key : qform A B C (y - k * x) (-x) = qform C' (-B') A x y := by
        simp only [qform, hB', hC']; ring
      rw [key]; exact hxy

/-- **Class number one, rank two.**  Every integral binary quadratic form whose
    discriminant `D = B² − 4AC` satisfies `−4 ≤ D < 0` represents `1` or `−1`.
    For `D = −4` and `D = −3` these are the norm forms of `ℤ[i]` and `ℤ[ω]`. -/
theorem exists_repr {D : ℤ} (hD1 : -4 ≤ D) (hD2 : D < 0) (A B C : ℤ)
    (hdisc : B ^ 2 - 4 * A * C = D) :
    ∃ x y : ℤ, qform A B C x y = 1 ∨ qform A B C x y = -1 :=
  exists_repr_aux hD1 hD2 A.natAbs A B C rfl hdisc

/-! ## 2. Matrices with `M² = τ·M − I` -/

/-- The companion matrix `[[0, −1], [1, τ]]` of `X² − τX + 1`. -/
def comp (τ : ℤ) : M2 := !![0, -1; 1, τ]

/-- The four scalar equations contained in `M² = τ·M − I`. -/
lemma entries {τ : ℤ} {M : M2} (h : M * M = τ • M - 1) :
    M 0 0 * M 0 0 + M 0 1 * M 1 0 = τ * M 0 0 - 1 ∧
    M 0 0 * M 0 1 + M 0 1 * M 1 1 = τ * M 0 1 ∧
    M 1 0 * M 0 0 + M 1 1 * M 1 0 = τ * M 1 0 ∧
    M 1 0 * M 0 1 + M 1 1 * M 1 1 = τ * M 1 1 - 1 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.one_apply] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `M² = τ·M − I` with `τ² < 4` forces `tr M = τ` and `det M = 1`: the characteristic
    polynomial is `X² − τX + 1 = Φ_r`. -/
theorem trace_det_of_sq {τ : ℤ} (hτ : τ ^ 2 < 4) {M : M2} (h : M * M = τ • M - 1) :
    M.trace = τ ∧ M.det = 1 := by
  obtain ⟨e00, e01, e10, e11⟩ := entries h
  have htr : M 0 0 + M 1 1 = τ := by
    by_contra hne
    have hfac : (M 0 0 - M 1 1) * (M 0 0 + M 1 1 - τ) = 0 := by linear_combination e00 - e11
    have hne' : M 0 0 + M 1 1 - τ ≠ 0 := fun hc => hne (by linarith)
    have had : M 0 0 = M 1 1 := by
      rcases mul_eq_zero.mp hfac with h2 | h2
      · linarith
      · exact absurd h2 hne'
    have hb : M 0 1 * (M 0 0 + M 1 1 - τ) = 0 := by linear_combination e01
    have hc : M 1 0 * (M 0 0 + M 1 1 - τ) = 0 := by linear_combination e10
    have hb0 : M 0 1 = 0 := by
      rcases mul_eq_zero.mp hb with h2 | h2
      · exact h2
      · exact absurd h2 hne'
    have hc0 : M 1 0 = 0 := by
      rcases mul_eq_zero.mp hc with h2 | h2
      · exact h2
      · exact absurd h2 hne'
    rw [hb0, hc0] at e00
    nlinarith [sq_nonneg (2 * M 0 0 - τ)]
  refine ⟨by rw [Matrix.trace_fin_two]; exact htr, ?_⟩
  rw [Matrix.det_fin_two]
  linear_combination -e00 + M 0 0 * htr

/-! ## 3. The rank-two Latimer--MacDuffee statement -/

/-- **Rank-two Latimer--MacDuffee.**  Every `M ∈ M₂(ℤ)` with `M² = τ·M − I` and `τ² < 4`
    is `GL₂(ℤ)`-conjugate to the companion matrix `[[0, −1], [1, τ]]`.  The conjugating
    matrix is `U = [v | Mv]` for a vector `v` with `det[v | Mv] = ±1`, which exists
    because the form `v ↦ det[v | Mv]` has discriminant `τ² − 4 ∈ {−3, −4}`. -/
theorem exists_conj_comp {τ : ℤ} (hτ : τ ^ 2 < 4) {M : M2} (h : M * M = τ • M - 1) :
    ∃ U : M2, IsUnit U.det ∧ M * U = U * comp τ := by
  obtain ⟨e00, e01, e10, e11⟩ := entries h
  obtain ⟨htr, hdet⟩ := trace_det_of_sq hτ h
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨x, y, hxy⟩ :=
    exists_repr (D := τ ^ 2 - 4) (by nlinarith) (by nlinarith)
      (M 1 0) (M 1 1 - M 0 0) (-(M 0 1)) (by linear_combination (M 0 0 + M 1 1 + τ) * htr - 4 * hdet)
  refine ⟨!![x, M 0 0 * x + M 0 1 * y; y, M 1 0 * x + M 1 1 * y], ?_, ?_⟩
  · have hd : (!![x, M 0 0 * x + M 0 1 * y; y, M 1 0 * x + M 1 1 * y] : M2).det =
        qform (M 1 0) (M 1 1 - M 0 0) (-(M 0 1)) x y := by
      rw [Matrix.det_fin_two]; simp [qform]; ring
    rw [hd, Int.isUnit_iff]
    rcases hxy with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, comp]
    · linear_combination x * e00 + y * e01
    · linear_combination x * e10 + y * e11

/-- Any two integer matrices satisfying the same equation `M² = τ·M − I` with `τ² < 4`
    are `GL₂(ℤ)`-conjugate: there is a single conjugacy class. -/
theorem conj_of_sq_eq {τ : ℤ} (hτ : τ ^ 2 < 4) {M N : M2}
    (hM : M * M = τ • M - 1) (hN : N * N = τ • N - 1) :
    ∃ U : M2, IsUnit U.det ∧ M * U = U * N := by
  obtain ⟨U₁, hU₁, h₁⟩ := exists_conj_comp hτ hM
  obtain ⟨U₂, hU₂, h₂⟩ := exists_conj_comp hτ hN
  refine ⟨U₁ * U₂⁻¹, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact hU₁.mul (Matrix.isUnit_nonsing_inv_det U₂ hU₂)
  · have hkey : comp τ * U₂⁻¹ = U₂⁻¹ * N := by
      have h3 : U₂⁻¹ * (N * U₂) * U₂⁻¹ = U₂⁻¹ * (U₂ * comp τ) * U₂⁻¹ := by rw [h₂]
      rw [← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ hU₂, one_mul, mul_assoc,
        mul_assoc, Matrix.mul_nonsing_inv _ hU₂, mul_one] at h3
      exact h3.symm
    calc M * (U₁ * U₂⁻¹) = (M * U₁) * U₂⁻¹ := by rw [mul_assoc]
      _ = (U₁ * comp τ) * U₂⁻¹ := by rw [h₁]
      _ = U₁ * (comp τ * U₂⁻¹) := by rw [mul_assoc]
      _ = U₁ * (U₂⁻¹ * N) := by rw [hkey]
      _ = U₁ * U₂⁻¹ * N := by rw [mul_assoc]

/-! ## 4. The instances used by the paper -/

/-- The paper's companion matrix `M_A = [[τ, 1], [−1, 0]]` satisfies `M² = τ·M − I`. -/
theorem MA_sq (τ : ℤ) :
    DigitLattice.MA τ * DigitLattice.MA τ = τ • DigitLattice.MA τ - 1 := by
  have h := cayley_hamilton (DigitLattice.MA τ)
  rw [DigitLattice.MA_trace, DigitLattice.MA_det] at h
  simpa using h

/-- Every `M` with `M² = τ·M − I`, `τ² < 4`, is `GL₂(ℤ)`-conjugate to the companion
    matrix `M_A = [[τ, 1], [−1, 0]]` of `Φ_r`. -/
theorem exists_conj_MA {τ : ℤ} (hτ : τ ^ 2 < 4) {M : M2} (h : M * M = τ • M - 1) :
    ∃ U : M2, IsUnit U.det ∧ M * U = U * DigitLattice.MA τ :=
  conj_of_sq_eq hτ h (MA_sq τ)

/-- An integer `2 × 2` matrix of finite order with `det M = 1` and `M ≠ ±I` is a rotation
    of order `3`, `4` or `6`, so its characteristic polynomial is `Φ_r` with
    `τ = tr M ∈ {−1, 0, 1}`. -/
theorem trace_mem_of_rotation (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1)
    (hdet : M.det = 1) (h1 : M ≠ 1) (h2 : M ≠ -1) :
    M.trace = -1 ∨ M.trace = 0 ∨ M.trace = 1 := by
  rcases classification M hr hM with h | h | ⟨hd, -, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd h h1
  · exact absurd h h2
  · rw [hdet] at hd; norm_num at hd
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr ht)

/-- (Latimer--MacDuffee, the form used in the paper.)  A rotation of finite order is
    `GL₂(ℤ)`-conjugate to the companion matrix `M_A = [[τ, 1], [−1, 0]]` of its
    characteristic polynomial `Φ_r`, `τ = tr M`; the conjugacy class is unique. -/
theorem conj_MA_of_pow_eq_one (M : M2) {r : ℕ} (hr : 1 ≤ r) (hM : M ^ r = 1)
    (hdet : M.det = 1) (h1 : M ≠ 1) (h2 : M ≠ -1) :
    ∃ U : M2, IsUnit U.det ∧ M * U = U * DigitLattice.MA M.trace := by
  have ht := trace_mem_of_rotation M hr hM hdet h1 h2
  have hsq : M.trace ^ 2 < 4 := by rcases ht with h | h | h <;> rw [h] <;> norm_num
  refine exists_conj_MA hsq ?_
  have h := cayley_hamilton M
  rw [hdet] at h
  simpa using h

/-- (`r = 4`.)  Every `M ∈ M₂(ℤ)` with `M² = −I` is `GL₂(ℤ)`-conjugate to `[[0,−1],[1,0]]`. -/
theorem conj_neg_one {M : M2} (h : M * M = -1) :
    ∃ U : M2, IsUnit U.det ∧ M * U = U * !![0, -1; 1, 0] := by
  have h' : M * M = (0 : ℤ) • M - 1 := by simpa using h
  simpa [comp] using exists_conj_comp (τ := 0) (by norm_num) h'

/-- (`r = 6`.)  Every `M ∈ M₂(ℤ)` with `M² = M − I` is `GL₂(ℤ)`-conjugate to
    `[[0,−1],[1,1]]`. -/
theorem conj_eisenstein {M : M2} (h : M * M = M - 1) :
    ∃ U : M2, IsUnit U.det ∧ M * U = U * !![0, -1; 1, 1] := by
  have h' : M * M = (1 : ℤ) • M - 1 := by simpa using h
  simpa [comp] using exists_conj_comp (τ := 1) (by norm_num) h'

end Conjugacy
