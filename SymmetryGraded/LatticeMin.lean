/-
  LatticeMin.lean

  Formal verification (Lean 4 + Mathlib) of

    Lemma "Injectivity as a lattice minimum"  (second equivalence)
    Theorem "Feasibility", the constants `c₄ = 8` (box) and `c₆ = 4` (hexagon)

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  With no unproved placeholders:

  * `box_sub_box`, `hex_sub_hex`
        the difference sets `T − T = 2T` of the box and of the hexagon:
        `[−B,B]² − [−B,B]² = [−2B,2B]²`, `T_B − T_B = T_{2B}`.
  * `injOn_box_iff`, `injOn_hex_iff`, `injOn_box_iff_kernel`, `injOn_hex_iff_kernel`
        `φ_A` injective on `T` ⟺ every nonzero kernel vector `w ∈ L_A` has
        `N_T(w) > 2B` (box norm `‖·‖∞`, hexagon norm `N`).
  * `dvd_sq_add_sq`, `sq_add_sq_ge`, `boxNorm_sq_ge`, `sqrt_half_p_le_boxNorm`
        for `A² ≡ −1 (mod p)` every nonzero kernel vector `(u,v)` has
        `p ∣ u² + v²`, hence `u² + v² ≥ p` and `‖(u,v)‖∞ ≥ √(p/2)`.
  * `box_injective_of_lt`, `box_injective_of_lt_sqrt`
        `8B² < p` (i.e. `B < √(p/8)`) ⟹ `φ_A` injective on the box   (`c₄ = 8`).
  * `dvd_eisenstein`, `eisenstein_pos`, `eisenstein_le_hexNorm_sq`, `hexNorm_sq_ge`
        for `A² ≡ A − 1 (mod p)` every nonzero kernel vector has
        `p ∣ u² + uv + v²`, `u² + uv + v² ≤ N(u,v)²`, hence `N(u,v) ≥ √p`.
  * `hex_injective_of_lt`, `hex_injective_of_lt_sqrt`
        `4B² < p` (i.e. `B < √p / 2`) ⟹ `φ_A` injective on the hexagon (`c₆ = 4`).

  * (round 5, section 7) the **upper bounds**:
    `exists_kernel_sq_add_sq_eq` (Fermat: a kernel vector with `u² + v² = p`),
    `exists_kernel_boxNorm_le_sqrt`, `lambda1_box_bounds` (`√(p/2) ≤ λ₁^∞ ≤ √p`),
    `box_injective_imp` (injective ⟹ `4B² < p`), `box_constants` (`4 ≤ c₄ ≤ 8`);
    `exists_kernel_eisenstein_eq` (a self-contained Thue/pigeonhole argument: a kernel
    vector with `u² + uv + v² = p`; Mathlib has no `p = a² + 3b²` theorem),
    `exists_kernel_hexNorm_le`, `lambda1_hex_bounds` (`√p ≤ λ₁^hex ≤ (2/√3)√p`),
    `hex_injective_imp` (injective ⟹ `3B² < p`), `hex_constants` (`3 ≤ c₆ ≤ 4`).

  Not formalized: the numerical constant `12` of the box closure (computed, not proved,
  in the paper).
-/
import Mathlib
import SymmetryGraded.Lattice
import SymmetryGraded.OrderSix

namespace LatticeMin

open DigitLattice
open scoped Pointwise

/-! ## 1. Norms and difference sets -/

/-- The box norm `‖(η, λ)‖∞ = max{|η|, |λ|}`. -/
def boxNorm (v : ℤ × ℤ) : ℤ := max |v.1| |v.2|

theorem mem_box_iff_boxNorm {B : ℤ} {v : ℤ × ℤ} : v ∈ box B ↔ boxNorm v ≤ B := by
  rw [mem_box, boxNorm]; simp

/-- `[−B,B]² − [−B,B]² = [−2B,2B]²`. -/
theorem box_sub_box (B : ℤ) : box B - box B = box (2 * B) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_sub, mem_box, abs_le, Prod.exists, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨x, y, ⟨hx, hy⟩, x', y', ⟨hx', hy'⟩, rfl, rfl⟩; omega
  · rintro ⟨ha, hb⟩
    refine ⟨-((-a) / 2), -((-b) / 2), ?_, -((-a) / 2) - a, -((-b) / 2) - b, ?_, ?_, ?_⟩ <;> omega

/-- `T_B − T_B = T_{2B}`. -/
theorem hex_sub_hex (B : ℤ) : hex B - hex B = hex (2 * B) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_sub, mem_hex, abs_le, Prod.exists, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨x, y, ⟨hx, hy, hxy⟩, x', y', ⟨hx', hy', hxy'⟩, rfl, rfl⟩; omega
  · rintro ⟨ha, hb, hab⟩
    refine ⟨-((-a) / 2), b / 2, ?_, -((-a) / 2) - a, b / 2 - b, ?_, ?_, ?_⟩ <;> omega

/-! ## 2. Injectivity as a lattice minimum -/
section Minimum
variable {R : Type*} [CommRing R]

/-- The kernel lattice `L_A = {w : φ_A(w) = 0}`. -/
def kernelLattice (A : R) : Set (ℤ × ℤ) := {w | phi A w = 0}

theorem mem_kernelLattice {A : R} {w : ℤ × ℤ} : w ∈ kernelLattice A ↔ phi A w = 0 := Iff.rfl

/-- (Lemma "Injectivity as a lattice minimum", box.)  `φ_A` is injective on `[−B,B]²`
    iff every nonzero kernel vector has `‖w‖∞ > 2B`. -/
theorem injOn_box_iff (A : R) (B : ℤ) :
    Set.InjOn (phi A) (box B) ↔ ∀ w : ℤ × ℤ, phi A w = 0 → w ≠ 0 → 2 * B < boxNorm w := by
  rw [injOn_iff_kernel, box_sub_box B]
  constructor
  · intro h w hw hw0
    by_contra hle
    exact hw0 (h w (mem_box_iff_boxNorm.mpr (not_lt.mp hle)) hw)
  · intro h w hw hw0
    by_contra hne
    exact absurd (mem_box_iff_boxNorm.mp hw) (not_le.mpr (h w hw0 hne))

/-- (Lemma "Injectivity as a lattice minimum", hexagon.)  `φ_A` is injective on `T_B`
    iff every nonzero kernel vector has `N(w) > 2B`. -/
theorem injOn_hex_iff (A : R) (B : ℤ) :
    Set.InjOn (phi A) (hex B) ↔
      ∀ w : ℤ × ℤ, phi A w = 0 → w ≠ 0 → 2 * B < OrderSix.hexNorm w.1 w.2 := by
  rw [injOn_iff_kernel, hex_sub_hex B]
  constructor
  · intro h w hw hw0
    by_contra hle
    exact hw0 (h w (mem_hex_iff_hexNorm.mpr (not_lt.mp hle)) hw)
  · intro h w hw hw0
    by_contra hne
    exact absurd (mem_hex_iff_hexNorm.mp hw) (not_le.mpr (h w hw0 hne))

theorem injOn_box_iff_kernel (A : R) (B : ℤ) :
    Set.InjOn (phi A) (box B) ↔ ∀ w ∈ kernelLattice A \ {0}, 2 * B < boxNorm w := by
  rw [injOn_box_iff A B]
  simp [kernelLattice]

theorem injOn_hex_iff_kernel (A : R) (B : ℤ) :
    Set.InjOn (phi A) (hex B) ↔
      ∀ w ∈ kernelLattice A \ {0}, 2 * B < OrderSix.hexNorm w.1 w.2 := by
  rw [injOn_hex_iff A B]
  simp [kernelLattice]

end Minimum

/-! ## 3. The kernel lattice modulo `p` -/

theorem phi_zmod_eq_zero_iff (A : ℤ) (p : ℕ) (w : ℤ × ℤ) :
    phi (A : ZMod p) w = 0 ↔ (p : ℤ) ∣ w.1 * A + w.2 := by
  have : phi (A : ZMod p) w = ((w.1 * A + w.2 : ℤ) : ZMod p) := by simp [phi]
  rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-! ## 4. Gaussian case `A² ≡ −1`: `u² + v² ≡ 0`, box constant `c₄ = 8` -/
section Gaussian

theorem dvd_sq_add_sq {A p u v : ℤ} (hA : p ∣ A ^ 2 + 1) (hw : p ∣ u * A + v) :
    p ∣ u ^ 2 + v ^ 2 := by
  have h : u ^ 2 + v ^ 2 = u ^ 2 * (A ^ 2 + 1) - (u * A + v) * (u * A - v) := by ring
  rw [h]
  exact (hA.mul_left _).sub (hw.mul_right _)

theorem sq_add_sq_pos {u v : ℤ} (hw0 : (u, v) ≠ 0) : 0 < u ^ 2 + v ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · have hv : v ≠ 0 := by rintro rfl; exact hw0 rfl
    positivity
  · positivity

theorem sq_add_sq_ge {A p u v : ℤ} (hA : p ∣ A ^ 2 + 1) (hw : p ∣ u * A + v)
    (hw0 : (u, v) ≠ 0) : p ≤ u ^ 2 + v ^ 2 :=
  Int.le_of_dvd (sq_add_sq_pos hw0) (dvd_sq_add_sq hA hw)

theorem sq_le_boxNorm_sq_left (u v : ℤ) : u ^ 2 ≤ boxNorm (u, v) ^ 2 := by
  unfold boxNorm
  have h1 : |u| ≤ max |u| |v| := le_max_left _ _
  have h2 : 0 ≤ |u| := abs_nonneg u
  nlinarith [sq_abs u]

theorem sq_le_boxNorm_sq_right (u v : ℤ) : v ^ 2 ≤ boxNorm (u, v) ^ 2 := by
  unfold boxNorm
  have h1 : |v| ≤ max |u| |v| := le_max_right _ _
  have h2 : 0 ≤ |v| := abs_nonneg v
  nlinarith [sq_abs v]

/-- Every nonzero kernel vector has `2‖w‖∞² ≥ p`, i.e. `‖w‖∞ ≥ √(p/2)`. -/
theorem boxNorm_sq_ge {A p u v : ℤ} (hA : p ∣ A ^ 2 + 1) (hw : p ∣ u * A + v)
    (hw0 : (u, v) ≠ 0) : p ≤ 2 * boxNorm (u, v) ^ 2 := by
  have := sq_add_sq_ge hA hw hw0
  have := sq_le_boxNorm_sq_left u v
  have := sq_le_boxNorm_sq_right u v
  linarith

theorem sqrt_half_p_le_boxNorm {A p u v : ℤ} (hA : p ∣ A ^ 2 + 1)
    (hw : p ∣ u * A + v) (hw0 : (u, v) ≠ 0) :
    Real.sqrt ((p : ℝ) / 2) ≤ (boxNorm (u, v) : ℝ) := by
  have hN : (0 : ℤ) ≤ boxNorm (u, v) := le_trans (abs_nonneg _) (le_max_left _ _)
  have h := boxNorm_sq_ge hA hw hw0
  rw [Real.sqrt_le_left (by exact_mod_cast hN)]
  have : (p : ℝ) ≤ 2 * (boxNorm (u, v) : ℝ) ^ 2 := by exact_mod_cast h
  linarith

/-- (Theorem "Feasibility", box, `c₄ = 8`.)  For `A² ≡ −1 (mod p)` and `8B² < p`,
    `φ_A` is injective on `[−B,B]²` into `ZMod p`. -/
theorem box_injective_of_lt (A : ℤ) (p : ℕ) (hA : (p : ℤ) ∣ A ^ 2 + 1) {B : ℤ}
    (hB : 0 ≤ B) (h8 : 8 * B ^ 2 < p) : Set.InjOn (phi (A : ZMod p)) (box B) := by
  rw [injOn_box_iff _ B]
  rintro ⟨u, v⟩ hw hw0
  rw [phi_zmod_eq_zero_iff] at hw
  have h := boxNorm_sq_ge hA hw hw0
  have hN : (0 : ℤ) ≤ boxNorm (u, v) := le_trans (abs_nonneg _) (le_max_left _ _)
  nlinarith

/-- The same with the real-form hypothesis `B < √(p/8)`. -/
theorem box_injective_of_lt_sqrt (A : ℤ) (p : ℕ) (hA : (p : ℤ) ∣ A ^ 2 + 1)
    {B : ℤ} (hB : 0 ≤ B) (h8 : (B : ℝ) < Real.sqrt ((p : ℝ) / 8)) :
    Set.InjOn (phi (A : ZMod p)) (box B) := by
  apply box_injective_of_lt A p hA hB
  rw [Real.lt_sqrt (by exact_mod_cast hB)] at h8
  have : (8 * B ^ 2 : ℝ) < p := by linarith
  exact_mod_cast this

end Gaussian

/-! ## 5. Eisenstein case `A² ≡ A − 1`: `u² + uv + v² ≡ 0`, hexagon constant `c₆ = 4` -/
section Eisenstein

theorem dvd_eisenstein {A p u v : ℤ} (hA : p ∣ A ^ 2 - A + 1) (hw : p ∣ u * A + v) :
    p ∣ u ^ 2 + u * v + v ^ 2 := by
  have h : u ^ 2 + u * v + v ^ 2 =
      u ^ 2 * (A ^ 2 - A + 1) - (u * A + v) * (u * A - u - v) := by ring
  rw [h]
  exact (hA.mul_left _).sub (hw.mul_right _)

theorem eisenstein_pos {u v : ℤ} (hw0 : (u, v) ≠ 0) : 0 < u ^ 2 + u * v + v ^ 2 := by
  have h4 : 4 * (u ^ 2 + u * v + v ^ 2) = (2 * u + v) ^ 2 + 3 * v ^ 2 := by ring
  rcases eq_or_ne v 0 with rfl | hv
  · have hu : u ≠ 0 := by rintro rfl; exact hw0 rfl
    have : 0 < u ^ 2 := by positivity
    nlinarith
  · have : 0 < v ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * u + v)]

/-- `u² + uv + v² ≤ N(u,v)²` for the hexagon norm `N = max{|u|,|v|,|u+v|}`. -/
theorem eisenstein_le_hexNorm_sq (u v : ℤ) :
    u ^ 2 + u * v + v ^ 2 ≤ OrderSix.hexNorm u v ^ 2 := by
  unfold OrderSix.hexNorm
  set N := max |u| (max |v| |u + v|) with hN
  have hu : |u| ≤ N := le_max_left _ _
  have hv : |v| ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have huv : |u + v| ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hN0 : 0 ≤ N := le_trans (abs_nonneg _) hu
  have hu2 : u ^ 2 ≤ N ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hv2 : v ^ 2 ≤ N ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
  have huv2 : (u + v) ^ 2 ≤ N ^ 2 := by nlinarith [sq_abs (u + v), abs_nonneg (u + v)]
  rcases le_total 0 (u * v) with h | h
  · nlinarith
  · rcases le_total (v ^ 2) (u ^ 2) with h' | h'
    · -- u² + uv + v² ≤ u² since uv + v² ≤ 0 : v² ≤ |u||v| = -uv
      have : v ^ 2 ≤ -(u * v) := by
        have h1 : |u * v| = -(u * v) := abs_of_nonpos h
        have h2 : |v| ≤ |u| := by
          rw [← sq_le_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs]; exact h'
        have h3 : |v| * |v| ≤ |u| * |v| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        have h4 : |u| * |v| = -(u * v) := by rw [← abs_mul, h1]
        nlinarith [sq_abs v]
      nlinarith
    · have : u ^ 2 ≤ -(u * v) := by
        have h1 : |u * v| = -(u * v) := abs_of_nonpos h
        have h2 : |u| ≤ |v| := by
          rw [← sq_le_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs]; exact h'
        have h3 : |u| * |u| ≤ |u| * |v| := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        have h4 : |u| * |v| = -(u * v) := by rw [← abs_mul, h1]
        nlinarith [sq_abs u]
      nlinarith

theorem eisenstein_ge {A p u v : ℤ} (hA : p ∣ A ^ 2 - A + 1)
    (hw : p ∣ u * A + v) (hw0 : (u, v) ≠ 0) : p ≤ u ^ 2 + u * v + v ^ 2 :=
  Int.le_of_dvd (eisenstein_pos hw0) (dvd_eisenstein hA hw)

/-- Every nonzero kernel vector has `N(w)² ≥ p`, i.e. `N(w) ≥ √p`. -/
theorem hexNorm_sq_ge {A p u v : ℤ} (hA : p ∣ A ^ 2 - A + 1)
    (hw : p ∣ u * A + v) (hw0 : (u, v) ≠ 0) : p ≤ OrderSix.hexNorm u v ^ 2 :=
  le_trans (eisenstein_ge hA hw hw0) (eisenstein_le_hexNorm_sq u v)

theorem hexNorm_nonneg (u v : ℤ) : 0 ≤ OrderSix.hexNorm u v :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem sqrt_p_le_hexNorm {A p u v : ℤ} (hA : p ∣ A ^ 2 - A + 1)
    (hw : p ∣ u * A + v) (hw0 : (u, v) ≠ 0) :
    Real.sqrt (p : ℝ) ≤ (OrderSix.hexNorm u v : ℝ) := by
  have h := hexNorm_sq_ge hA hw hw0
  rw [Real.sqrt_le_left (by exact_mod_cast hexNorm_nonneg u v)]
  exact_mod_cast h

/-- (Theorem "Feasibility", hexagon, `c₆ = 4`.)  For `A² ≡ A − 1 (mod p)` and `4B² < p`,
    `φ_A` is injective on the hexagon `T_B` into `ZMod p`. -/
theorem hex_injective_of_lt (A : ℤ) (p : ℕ) (hA : (p : ℤ) ∣ A ^ 2 - A + 1)
    {B : ℤ} (hB : 0 ≤ B) (h4 : 4 * B ^ 2 < p) : Set.InjOn (phi (A : ZMod p)) (hex B) := by
  rw [injOn_hex_iff _ B]
  rintro ⟨u, v⟩ hw hw0
  rw [phi_zmod_eq_zero_iff] at hw
  have h := hexNorm_sq_ge hA hw hw0
  have hN := hexNorm_nonneg u v
  simp only at h hN ⊢
  nlinarith

/-- The same with the real-form hypothesis `B < √p / 2`. -/
theorem hex_injective_of_lt_sqrt (A : ℤ) (p : ℕ) (hA : (p : ℤ) ∣ A ^ 2 - A + 1)
    {B : ℤ} (hB : 0 ≤ B) (h4 : (B : ℝ) < Real.sqrt (p : ℝ) / 2) :
    Set.InjOn (phi (A : ZMod p)) (hex B) := by
  apply hex_injective_of_lt A p hA hB
  have h2 : (2 * B : ℝ) < Real.sqrt (p : ℝ) := by linarith
  rw [Real.lt_sqrt (by positivity)] at h2
  have : (4 * B ^ 2 : ℝ) < p := by linarith
  exact_mod_cast this

end Eisenstein

/-! ## 6. Sanity instances -/

/-- `p = 31`, `A = 6` (`36 − 6 + 1 = 31`), `B = 2`: `16 < 31`. -/
example : Set.InjOn (phi ((6 : ℤ) : ZMod 31)) (hex 2) :=
  hex_injective_of_lt 6 31 (by norm_num) (by norm_num) (by norm_num)

/-- `p = 29`, `A = 12` (`145 = 5·29`), `B = 1`: `8 < 29`. -/
example : Set.InjOn (phi ((12 : ℤ) : ZMod 29)) (box 1) :=
  box_injective_of_lt 12 29 (by norm_num) (by norm_num) (by norm_num)

/-! ## 7. Upper bounds: a kernel vector of norm exactly `p` (round 5) -/

/-! ### 7a. Gaussian case: Fermat's two-squares theorem gives `(u,v) ∈ L_A` with `u² + v² = p` -/
section GaussianUpper

/-- `A² ≡ −1 (mod p)` makes `−1` a square in `ZMod p`. -/
theorem isSquare_neg_one_of_dvd {A : ℤ} {p : ℕ} (hA : (p : ℤ) ∣ A ^ 2 + 1) :
    IsSquare (-1 : ZMod p) := by
  refine ⟨(A : ZMod p), ?_⟩
  have h : ((A ^ 2 + 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hA
  push_cast at h
  linear_combination -h

/-- (Existence of a kernel vector of Euclidean norm `p`, Gaussian case.)  For a prime `p`
    with `A² ≡ −1 (mod p)` there is `(u, v) ≠ 0` in `L_A` with `u² + v² = p`: write
    `p = a² + b²` (Fermat), then `p ∣ (a − bA)(a + bA)`, so `(b, a)` or `(b, −a)` is in `L_A`. -/
theorem exists_kernel_sq_add_sq_eq {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 + 1) :
    ∃ u v : ℤ, (u, v) ≠ 0 ∧ (p : ℤ) ∣ u * A + v ∧ u ^ 2 + v ^ 2 = p := by
  obtain ⟨a, b, hab⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one (isSquare_neg_one_of_dvd hA)
  have hab' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = p := by exact_mod_cast hab.symm
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : (2 : ℕ) ≤ p := hp.two_le
  have hne : ((b : ℤ), (a : ℤ)) ≠ 0 ∧ ((b : ℤ), -(a : ℤ)) ≠ 0 := by
    constructor <;> intro h <;> simp only [Prod.mk_eq_zero, neg_eq_zero, Nat.cast_eq_zero] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> simp at hab <;> omega
  -- p ∣ (a − bA)(a + bA) = a² − b²A² = (a² + b²) − b²(A² + 1)
  have hdvd : (p : ℤ) ∣ ((a : ℤ) - b * A) * (a + b * A) := by
    have : ((a : ℤ) - b * A) * (a + b * A) = (a ^ 2 + b ^ 2) - b ^ 2 * (A ^ 2 + 1) := by ring
    rw [this, hab']
    exact (dvd_refl _).sub (hA.mul_left _)
  rcases hpI.dvd_or_dvd hdvd with h | h
  · -- a ≡ bA : (b, −a) ∈ L_A
    refine ⟨b, -a, hne.2, ?_, by rw [neg_sq]; linarith⟩
    have : (b : ℤ) * A + -a = -((a : ℤ) - b * A) := by ring
    rw [this]; exact h.neg_right
  · -- a ≡ −bA : (b, a) ∈ L_A
    refine ⟨b, a, hne.1, ?_, by linarith⟩
    have : (b : ℤ) * A + a = (a : ℤ) + b * A := by ring
    rw [this]; exact h

/-- The box norm of that vector satisfies `‖w‖∞² ≤ p`. -/
theorem boxNorm_sq_le_of_sq_add_sq {u v : ℤ} {p : ℕ} (h : u ^ 2 + v ^ 2 = p) :
    boxNorm (u, v) ^ 2 ≤ p := by
  unfold boxNorm
  simp only
  rcases le_total |u| |v| with huv | huv
  · rw [max_eq_right huv, sq_abs]; nlinarith [sq_nonneg u]
  · rw [max_eq_left huv, sq_abs]; nlinarith [sq_nonneg v]

/-- (Lemma "Injective packing", upper bound, box.)  `λ₁^∞(L_A) ≤ √p`: there is a nonzero
    kernel vector with `‖w‖∞ ≤ √p`. -/
theorem exists_kernel_boxNorm_le_sqrt {A : ℤ} {p : ℕ} (hp : p.Prime)
    (hA : (p : ℤ) ∣ A ^ 2 + 1) :
    ∃ w : ℤ × ℤ, w ≠ 0 ∧ phi (A : ZMod p) w = 0 ∧ (boxNorm w : ℝ) ≤ Real.sqrt p := by
  obtain ⟨u, v, hne, hker, hsum⟩ := exists_kernel_sq_add_sq_eq hp hA
  refine ⟨(u, v), hne, (phi_zmod_eq_zero_iff A p (u, v)).mpr hker, ?_⟩
  have hN : (0 : ℤ) ≤ boxNorm (u, v) := le_trans (abs_nonneg _) (le_max_left _ _)
  rw [Real.le_sqrt (by exact_mod_cast hN) (by positivity)]
  exact_mod_cast boxNorm_sq_le_of_sq_add_sq hsum

/-- (Lemma "Injective packing", two-sided bound, box.)  For a prime `p` with `A² ≡ −1`:
    every nonzero kernel vector has `‖w‖∞ ≥ √(p/2)`, and some nonzero kernel vector has
    `‖w‖∞ ≤ √p`; i.e. `√(p/2) ≤ λ₁^∞(L_A) ≤ √p`. -/
theorem lambda1_box_bounds {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 + 1) :
    (∀ w : ℤ × ℤ, w ≠ 0 → phi (A : ZMod p) w = 0 →
        Real.sqrt ((p : ℝ) / 2) ≤ (boxNorm w : ℝ)) ∧
      ∃ w : ℤ × ℤ, w ≠ 0 ∧ phi (A : ZMod p) w = 0 ∧ (boxNorm w : ℝ) ≤ Real.sqrt p := by
  refine ⟨?_, exists_kernel_boxNorm_le_sqrt hp hA⟩
  rintro ⟨u, v⟩ hne hker
  rw [phi_zmod_eq_zero_iff] at hker
  exact sqrt_half_p_le_boxNorm hA hker hne

/-- (Necessary side of Theorem "Feasibility", box.)  If `φ_A` is injective on `[−B,B]²`
    then `4B² < p`: the kernel vector of norm `p` has `‖w‖∞ ≤ √p`, so `2B < √p`. -/
theorem box_injective_imp {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 + 1)
    {B : ℤ} (hB : 0 ≤ B) (hinj : Set.InjOn (phi (A : ZMod p)) (box B)) : 4 * B ^ 2 < p := by
  rw [injOn_box_iff] at hinj
  obtain ⟨u, v, hne, hker, hsum⟩ := exists_kernel_sq_add_sq_eq hp hA
  have h := hinj (u, v) ((phi_zmod_eq_zero_iff A p (u, v)).mpr hker) hne
  have hN2 := boxNorm_sq_le_of_sq_add_sq hsum
  nlinarith

end GaussianUpper

/-! ### 7b. Eisenstein case: a Thue/pigeonhole argument gives `(u,v) ∈ L_A` with
`u² + uv + v² = p` (Mathlib has no `p = a² + 3b²` theorem; the argument below is
self-contained: `(⌊√p⌋+1)² > p` boxes collide modulo `L_A`, the difference has
`0 < u² + uv + v² < 3p`, `p ∣ u² + uv + v²`, and `2p` is excluded by a parity check). -/
section EisensteinUpper

/-- `p ∣ A² − A + 1` forces `p` odd (`A² − A + 1 = A(A−1) + 1` is odd). -/
theorem odd_of_dvd_eisenstein {A : ℤ} {p : ℕ} (hA : (p : ℤ) ∣ A ^ 2 - A + 1) : Odd p := by
  rcases Nat.even_or_odd p with hp | hp
  · exfalso
    obtain ⟨k, hk⟩ := hp
    have h2 : (2 : ℤ) ∣ A ^ 2 - A + 1 := by
      have : (p : ℤ) = 2 * k := by rw [hk]; push_cast; ring
      rw [this] at hA
      exact (dvd_mul_right 2 _).trans hA
    have hAA : (2 : ℤ) ∣ A * (A - 1) := by
      rcases Int.even_or_odd A with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m * (A - 1), by rw [hm]; ring⟩
      · exact ⟨A * m, by rw [hm]; ring⟩
    have : (2 : ℤ) ∣ 1 := by
      have h := h2.sub hAA
      have e : A ^ 2 - A + 1 - A * (A - 1) = 1 := by ring
      rwa [e] at h
    omega
  · exact hp

/-- The Eisenstein form is never `≡ 2 (mod 4)`; in particular `u² + uv + v² = 2p` is
    impossible for odd `p`. -/
theorem eisenstein_ne_two_mul_odd {u v : ℤ} {p : ℕ} (hp : Odd p) :
    u ^ 2 + u * v + v ^ 2 ≠ 2 * p := by
  intro h
  have h4 : ∀ x y : ZMod 4, x ^ 2 + x * y + y ^ 2 ≠ 2 := by decide
  obtain ⟨k, hk⟩ := hp
  have hcast : ((u : ZMod 4)) ^ 2 + (u : ZMod 4) * (v : ZMod 4) + (v : ZMod 4) ^ 2 = 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod 4)) h
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at this
    rw [this]
    have hp' : (p : ZMod 4) = 2 * (k : ZMod 4) + 1 := by exact_mod_cast congrArg (Nat.cast) hk
    rw [hp']
    have : ∀ z : ZMod 4, 2 * (2 * z + 1) = 2 := by decide
    push_cast
    exact this _
  exact h4 _ _ hcast

/-- A prime is not a perfect square: `⌊√p⌋² < p`. -/
theorem sqrt_sq_lt_of_prime {p : ℕ} (hp : p.Prime) : Nat.sqrt p * Nat.sqrt p < p := by
  rcases (Nat.sqrt_le p).lt_or_eq with h | h
  · exact h
  · exfalso
    have hd : Nat.sqrt p ∣ p := ⟨Nat.sqrt p, h.symm⟩
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · rw [h1] at h; simp at h; exact hp.one_lt.ne' h.symm
    · rw [h1] at h
      have := hp.one_lt
      nlinarith

/-- Pigeonhole: two distinct points of `{0,…,s}²`, `s = ⌊√p⌋`, have the same image under
    `(u,v) ↦ uA + v ∈ ZMod p`; their difference is a nonzero kernel vector with
    `|u|, |v| ≤ s`. -/
theorem exists_kernel_small {A : ℤ} {p : ℕ} (hp : p.Prime) :
    ∃ u v : ℤ, (u, v) ≠ 0 ∧ (p : ℤ) ∣ u * A + v ∧
      |u| ≤ Nat.sqrt p ∧ |v| ≤ Nat.sqrt p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set s := Nat.sqrt p with hs
  let S : Finset (ℕ × ℕ) := (Finset.range (s + 1)) ×ˢ (Finset.range (s + 1))
  let f : ℕ × ℕ → ZMod p := fun x => (x.1 : ZMod p) * (A : ZMod p) + (x.2 : ZMod p)
  have hcard : (Finset.univ : Finset (ZMod p)).card < S.card := by
    rw [Finset.card_univ, ZMod.card, Finset.card_product, Finset.card_range]
    have := Nat.lt_succ_sqrt p
    nlinarith
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := f) (fun _ _ => Finset.mem_univ _)
  simp only [S, Finset.mem_product, Finset.mem_range] at hx hy
  refine ⟨(x.1 : ℤ) - y.1, (x.2 : ℤ) - y.2, ?_, ?_, ?_, ?_⟩
  · intro h
    simp only [Prod.mk_eq_zero, sub_eq_zero, Nat.cast_inj] at h
    exact hxy (Prod.ext h.1 h.2)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [f] at hfxy
    push_cast
    linear_combination hfxy
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

/-- (Existence of a kernel vector of Eisenstein norm `p`.)  For a prime `p` with
    `A² ≡ A − 1 (mod p)` there is `(u, v) ≠ 0` in `L_A` with `u² + uv + v² = p`. -/
theorem exists_kernel_eisenstein_eq {A : ℤ} {p : ℕ} (hp : p.Prime)
    (hA : (p : ℤ) ∣ A ^ 2 - A + 1) :
    ∃ u v : ℤ, (u, v) ≠ 0 ∧ (p : ℤ) ∣ u * A + v ∧ u ^ 2 + u * v + v ^ 2 = p := by
  obtain ⟨u, v, hne, hker, hu, hv⟩ := exists_kernel_small (A := A) hp
  refine ⟨u, v, hne, hker, ?_⟩
  have hdvd : (p : ℤ) ∣ u ^ 2 + u * v + v ^ 2 := dvd_eisenstein hA hker
  have hpos : 0 < u ^ 2 + u * v + v ^ 2 := eisenstein_pos hne
  have hs : (Nat.sqrt p : ℤ) * Nat.sqrt p < p := by exact_mod_cast sqrt_sq_lt_of_prime hp
  -- `u² + uv + v² ≤ 3 s² < 3p`
  have hlt : u ^ 2 + u * v + v ^ 2 < 3 * p := by
    have hu2 : u ^ 2 ≤ (Nat.sqrt p : ℤ) * Nat.sqrt p := by
      have := abs_nonneg u; nlinarith [sq_abs u]
    have hv2 : v ^ 2 ≤ (Nat.sqrt p : ℤ) * Nat.sqrt p := by
      have := abs_nonneg v; nlinarith [sq_abs v]
    have huv : u * v ≤ (Nat.sqrt p : ℤ) * Nat.sqrt p := by
      have h1 : u * v ≤ |u * v| := le_abs_self _
      rw [abs_mul] at h1
      have := mul_le_mul hu hv (abs_nonneg v) (by positivity)
      linarith
    linarith
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 < m := by
    by_contra h
    have h' : m ≤ 0 := not_lt.mp h
    have : (p : ℤ) * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h'
    linarith
  have hm3 : m < 3 := by
    by_contra h
    have h' : 3 ≤ m := not_lt.mp h
    have : (p : ℤ) * 3 ≤ p * m := mul_le_mul_of_nonneg_left h' (by positivity)
    linarith
  have hodd := odd_of_dvd_eisenstein hA
  interval_cases m
  · linarith
  · exact absurd (by rw [hm]; ring) (eisenstein_ne_two_mul_odd (u := u) (v := v) hodd)

/-- The hexagon norm of a vector with `u² + uv + v² = p` satisfies `3N² ≤ 4p`, from
    `4(u² + uv + v²) = (2u + v)² + 3v²` and its two symmetric forms. -/
theorem three_mul_hexNorm_sq_le {u v : ℤ} {p : ℕ} (h : u ^ 2 + u * v + v ^ 2 = p) :
    3 * OrderSix.hexNorm u v ^ 2 ≤ 4 * p := by
  unfold OrderSix.hexNorm
  have e1 : 4 * (u ^ 2 + u * v + v ^ 2) = (2 * u + v) ^ 2 + 3 * v ^ 2 := by ring
  have e2 : 4 * (u ^ 2 + u * v + v ^ 2) = (2 * v + u) ^ 2 + 3 * u ^ 2 := by ring
  have e3 : 4 * (u ^ 2 + u * v + v ^ 2) = (u - v) ^ 2 + 3 * (u + v) ^ 2 := by ring
  rcases le_total |u| (max |v| |u + v|) with h1 | h1
  · rw [max_eq_right h1]
    rcases le_total |v| |u + v| with h2 | h2
    · rw [max_eq_right h2, sq_abs]; nlinarith [sq_nonneg (u - v)]
    · rw [max_eq_left h2, sq_abs]; nlinarith [sq_nonneg (2 * u + v)]
  · rw [max_eq_left h1, sq_abs]; nlinarith [sq_nonneg (2 * v + u)]

/-- (Lemma "Injective packing", upper bound, hexagon.)  `λ₁^hex(L_A) ≤ (2/√3)·√p`: there is
    a nonzero kernel vector with `N(w) ≤ 2√p/√3`. -/
theorem exists_kernel_hexNorm_le {A : ℤ} {p : ℕ} (hp : p.Prime)
    (hA : (p : ℤ) ∣ A ^ 2 - A + 1) :
    ∃ w : ℤ × ℤ, w ≠ 0 ∧ phi (A : ZMod p) w = 0 ∧
      (OrderSix.hexNorm w.1 w.2 : ℝ) ≤ 2 / Real.sqrt 3 * Real.sqrt p := by
  obtain ⟨u, v, hne, hker, hsum⟩ := exists_kernel_eisenstein_eq hp hA
  refine ⟨(u, v), hne, (phi_zmod_eq_zero_iff A p (u, v)).mpr hker, ?_⟩
  simp only
  have h3 : (3 : ℝ) * (OrderSix.hexNorm u v : ℝ) ^ 2 ≤ 4 * p := by
    exact_mod_cast three_mul_hexNorm_sq_le hsum
  have hN : (0 : ℝ) ≤ (OrderSix.hexNorm u v : ℝ) := by exact_mod_cast hexNorm_nonneg u v
  have key : (OrderSix.hexNorm u v : ℝ) ≤ Real.sqrt (4 / 3 * p) := by
    rw [Real.le_sqrt hN (by positivity)]; linarith
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e : Real.sqrt (4 / 3 * p) = 2 / Real.sqrt 3 * Real.sqrt p := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_div (by norm_num), h4]
  rw [← e]; exact key

/-- (Lemma "Injective packing", two-sided bound, hexagon.)  For a prime `p` with
    `A² ≡ A − 1`: every nonzero kernel vector has `N(w) ≥ √p`, and some nonzero kernel vector
    has `N(w) ≤ (2/√3)√p`; i.e. `√p ≤ λ₁^hex(L_A) ≤ (2/√3)√p`. -/
theorem lambda1_hex_bounds {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 - A + 1) :
    (∀ w : ℤ × ℤ, w ≠ 0 → phi (A : ZMod p) w = 0 →
        Real.sqrt p ≤ (OrderSix.hexNorm w.1 w.2 : ℝ)) ∧
      ∃ w : ℤ × ℤ, w ≠ 0 ∧ phi (A : ZMod p) w = 0 ∧
        (OrderSix.hexNorm w.1 w.2 : ℝ) ≤ 2 / Real.sqrt 3 * Real.sqrt p := by
  refine ⟨?_, exists_kernel_hexNorm_le hp hA⟩
  rintro ⟨u, v⟩ hne hker
  rw [phi_zmod_eq_zero_iff] at hker
  exact sqrt_p_le_hexNorm hA hker hne

/-- (Necessary side of Theorem "Feasibility", hexagon.)  If `φ_A` is injective on `T_B`
    then `3B² < p`: the kernel vector with `3N² ≤ 4p` would otherwise have `N ≤ 2B`. -/
theorem hex_injective_imp {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 - A + 1)
    {B : ℤ} (hB : 0 ≤ B) (hinj : Set.InjOn (phi (A : ZMod p)) (hex B)) : 3 * B ^ 2 < p := by
  rw [injOn_hex_iff] at hinj
  obtain ⟨u, v, hne, hker, hsum⟩ := exists_kernel_eisenstein_eq hp hA
  have h := hinj (u, v) ((phi_zmod_eq_zero_iff A p (u, v)).mpr hker) hne
  have hN2 := three_mul_hexNorm_sq_le hsum
  simp only at h
  nlinarith

/-- The constants are pinned to `4 ≤ c₄ ≤ 8` (box) and `3 ≤ c₆ ≤ 4` (hexagon):
    `8B² < p ⟹ injective ⟹ 4B² < p` and `4B² < p ⟹ injective ⟹ 3B² < p`. -/
theorem box_constants {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 + 1)
    {B : ℤ} (hB : 0 ≤ B) :
    (8 * B ^ 2 < p → Set.InjOn (phi (A : ZMod p)) (box B)) ∧
      (Set.InjOn (phi (A : ZMod p)) (box B) → 4 * B ^ 2 < p) :=
  ⟨box_injective_of_lt A p hA hB, box_injective_imp hp hA hB⟩

theorem hex_constants {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 - A + 1)
    {B : ℤ} (hB : 0 ≤ B) :
    (4 * B ^ 2 < p → Set.InjOn (phi (A : ZMod p)) (hex B)) ∧
      (Set.InjOn (phi (A : ZMod p)) (hex B) → 3 * B ^ 2 < p) :=
  ⟨hex_injective_of_lt A p hA hB, hex_injective_imp hp hA hB⟩

end EisensteinUpper

end LatticeMin
