/-
  Closure.lean

  Formal verification (Lean 4 + Mathlib) of the feasibility constant of the

    order-six filter on the *closure of the box*

  in "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".  The paper
  states that injectivity of the digit map on the hexagonal closure
  `Ω_B = {(η,λ) : at least two of |η|, |λ|, |η+λ| are ≤ B}` (of cardinality `6B²+6B+1`)
  holds as soon as the lattice minimum is large enough, with the numerical threshold
  `p ≳ 12B²` obtained by computing exact lattice minima over all primes
  `p ≡ 1 (mod 12)` below `7·10⁴`.  Here the constant `12` is *proved* on the sufficient
  side, together with a matching witness showing it cannot be improved, and the
  necessary side is proved with the constant `27/4`.

  With no unproved placeholders:

  * `sub_rot_iff`, `box_subset_sub`, `closure_subset_sub`, `hex_base`, `hex_subset_sub`,
    `sub_subset`, `closure_sub_closure`
        the difference set of the closure is computed exactly:
        `Ω_B − Ω_B = Ω_{2B} ∪ T_{3B}`
        (`T_R` the hexagon `{N ≤ R}`, `N(u,v) = max{|u|,|v|,|u+v|}`).  The inclusion `⊇`
        is by explicit decompositions; `⊆` is a linear case analysis.
  * `eisenstein_le_twelve`, `eisenstein_le_of_mem_sub`
        the Eisenstein norm on `Ω_B − Ω_B` is at most `12B²`, attained at `(2B, 2B)`.
  * `closure_injective_of_lt`   (sufficient side, constant exactly `12`)
        `A² ≡ A − 1 (mod p)` and `12B² < p` ⟹ `φ_A` is injective on `Ω_B`.
  * `twelve_sharp`
        `(2B, 2B) ∈ Ω_B − Ω_B` has Eisenstein norm exactly `12B²`, so no constant below
        `12` makes the argument of `closure_injective_of_lt` work.
  * `closure_injective_imp`     (necessary side, constant `27/4`)
        `φ_A` injective on `Ω_B` ⟹ `27B² + 18B + 3 ≤ 4p`, since the kernel vector with
        `u² + uv + v² = p` must lie outside `T_{3B} ⊆ Ω_B − Ω_B` and `3N² ≤ 4p`.
  * `closure_constants`
        the two-sided statement `27/4 ≤ c_Ω ≤ 12`.

  Not formalized: that the numerical threshold is exactly `12` (i.e. that for infinitely
  many `p` injectivity really fails at `p` slightly below `12B²`); this is a statement
  about the distribution of the shortest vectors of the ideals `(p, A − ω)` and is
  verified in the paper only by computation.
-/
import Mathlib
import SymmetryGraded.Lattice
import SymmetryGraded.OrderSix
import SymmetryGraded.LatticeMin

namespace Closure

open DigitLattice LatticeMin
open scoped Pointwise

/-! ## 1. The difference set of the box closure -/

/-- The sixth turn is additive. -/
theorem rot_sub (τ : ℤ) (v w : ℤ × ℤ) : rot τ (v - w) = rot τ v - rot τ w := by
  simp only [rot, Prod.mk_sub_mk, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
  constructor <;> ring

/-- The inverse sixth turn is additive. -/
theorem rotInv_sub (τ : ℤ) (v w : ℤ × ℤ) : rotInv τ (v - w) = rotInv τ v - rotInv τ w := by
  simp only [rotInv, Prod.mk_sub_mk, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
  constructor <;> ring

/-- `Ω_B` is stable under the inverse sixth turn as well. -/
theorem closure_rotInv_iff (B : ℤ) (v : ℤ × ℤ) :
    rotInv 1 v ∈ DigitLattice.closure B ↔ v ∈ DigitLattice.closure B := by
  have h := closure_rot_iff B (rotInv 1 v)
  rw [rot_rotInv] at h
  exact h.symm

/-- The difference set `Ω_B − Ω_B` is stable under the sixth turn. -/
theorem sub_rot_iff (B : ℤ) (d : ℤ × ℤ) :
    rot 1 d ∈ DigitLattice.closure B - DigitLattice.closure B ↔
      d ∈ DigitLattice.closure B - DigitLattice.closure B := by
  constructor
  · intro h
    obtain ⟨v, hv, w, hw, hvw⟩ := Finset.mem_sub.mp h
    refine Finset.mem_sub.mpr ⟨rotInv 1 v, (closure_rotInv_iff B v).mpr hv,
      rotInv 1 w, (closure_rotInv_iff B w).mpr hw, ?_⟩
    rw [← rotInv_sub, hvw, rotInv_rot]
  · intro h
    obtain ⟨v, hv, w, hw, hvw⟩ := Finset.mem_sub.mp h
    refine Finset.mem_sub.mpr ⟨rot 1 v, (closure_rot_iff B v).mpr hv,
      rot 1 w, (closure_rot_iff B w).mpr hw, ?_⟩
    rw [← rot_sub, hvw]

/-- `[−2B, 2B]² = [−B,B]² − [−B,B]² ⊆ Ω_B − Ω_B`. -/
theorem box_subset_sub (B : ℤ) :
    box (2 * B) ⊆ DigitLattice.closure B - DigitLattice.closure B := by
  rw [← box_sub_box]
  intro d hd
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.mem_sub.mp hd
  exact Finset.mem_sub.mpr ⟨v, box_subset_closure B hv, w, box_subset_closure B hw, hvw⟩

/-- `Ω_{2B} ⊆ Ω_B − Ω_B`: each of the three box images of `Ω_{2B}` is a difference of
    two box images inside `Ω_B`. -/
theorem closure_subset_sub (B : ℤ) :
    DigitLattice.closure (2 * B) ⊆ DigitLattice.closure B - DigitLattice.closure B := by
  rintro ⟨a, b⟩ hd
  rw [mem_closure] at hd
  simp only [abs_le] at hd
  rcases hd with h | h | h
  · exact box_subset_sub B (mem_box.mpr (by simp only [abs_le]; exact h))
  · -- `|a| ≤ 2B`, `|a+b| ≤ 2B`: the first turn of the box
    have hmem : rot 1 (a, b) ∈ box (2 * B) := by
      rw [mem_box]; simp only [rot, abs_le]; omega
    have h1 := box_subset_sub B hmem
    rw [sub_rot_iff] at h1
    exact h1
  · -- `|b| ≤ 2B`, `|a+b| ≤ 2B`: the second turn of the box
    have hmem : rot 1 (rot 1 (a, b)) ∈ box (2 * B) := by
      rw [mem_box]; simp only [rot, abs_le]; omega
    have h1 := box_subset_sub B hmem
    rw [sub_rot_iff, sub_rot_iff] at h1
    exact h1

/-- The base case of `T_{3B} ⊆ Ω_B − Ω_B`: a point with `|b| ≤ 2B`, `|a| ≤ 3B`,
    `|a+b| ≤ 3B` is the difference of a point of the box and a point of its first turn.
    The witnesses are explicit clamps. -/
theorem hex_base {B a b : ℤ} (hb : |b| ≤ 2 * B) (ha : |a| ≤ 3 * B) (hab : |a + b| ≤ 3 * B) :
    ((a, b) : ℤ × ℤ) ∈ DigitLattice.closure B - DigitLattice.closure B := by
  simp only [abs_le] at hb ha hab
  set s : ℤ := a + b with hs
  set y₁ : ℤ := max (max (-B) (b - B)) (min (min B (b + B)) s) with hy₁
  set s₂ : ℤ := max (-B) (min B (y₁ - s)) with hs₂
  refine Finset.mem_sub.mpr ⟨(s + s₂ - y₁, y₁), ?_, (s₂ - (y₁ - b), y₁ - b), ?_, ?_⟩
  · rw [mem_closure]; simp only [abs_le]; left; omega
  · rw [mem_closure]; simp only [abs_le]; right; right; omega
  · simp only [Prod.mk_sub_mk, Prod.mk.injEq]; omega

/-- `T_{3B} ⊆ Ω_B − Ω_B`: in the hexagon of radius `3B` at least one of `|η|`, `|λ|`,
    `|η+λ|` is at most `2B`, and the three cases are turns of one another. -/
theorem hex_subset_sub (B : ℤ) :
    hex (3 * B) ⊆ DigitLattice.closure B - DigitLattice.closure B := by
  rintro ⟨a, b⟩ hd
  rw [mem_hex] at hd
  obtain ⟨ha, hb, hab⟩ := hd
  -- at least one of the three coordinates is small
  have hone : |b| ≤ 2 * B ∨ |a| ≤ 2 * B ∨ |a + b| ≤ 2 * B := by
    simp only [abs_le] at ha hb hab ⊢; omega
  rcases hone with h | h | h
  · exact hex_base h ha hab
  · -- the first turn moves `a` into the second coordinate
    have hr : rot 1 ((a, b) : ℤ × ℤ) = (a + b, -a) := by simp [rot]
    have h1 : rot 1 ((a, b) : ℤ × ℤ) ∈ DigitLattice.closure B - DigitLattice.closure B := by
      rw [hr]
      refine hex_base (a := a + b) (b := -a) ?_ ?_ ?_ <;>
        simp only [abs_le] at ha hb hab h ⊢ <;> omega
    rwa [sub_rot_iff] at h1
  · -- the second turn moves `a + b` into the second coordinate
    have hr : rot 1 (rot 1 ((a, b) : ℤ × ℤ)) = (b, -(a + b)) := by simp [rot]
    have h1 : rot 1 (rot 1 ((a, b) : ℤ × ℤ)) ∈
        DigitLattice.closure B - DigitLattice.closure B := by
      rw [hr]
      refine hex_base (a := b) (b := -(a + b)) ?_ ?_ ?_ <;>
        simp only [abs_le] at ha hb hab h ⊢ <;> omega
    rwa [sub_rot_iff, sub_rot_iff] at h1

/-- `Ω_B − Ω_B ⊆ Ω_{2B} ∪ T_{3B}`: a linear case analysis over the nine pairs of box
    images. -/
theorem sub_subset (B : ℤ) :
    DigitLattice.closure B - DigitLattice.closure B ⊆
      DigitLattice.closure (2 * B) ∪ hex (3 * B) := by
  rintro ⟨a, b⟩ hd
  simp only [Finset.mem_sub, mem_closure, abs_le, Prod.exists, Prod.mk_sub_mk,
    Prod.mk.injEq] at hd
  simp only [Finset.mem_union, mem_closure, mem_hex, abs_le]
  omega

/-- The difference set of the closure of the box, exactly: `Ω_B − Ω_B = Ω_{2B} ∪ T_{3B}`. -/
theorem closure_sub_closure (B : ℤ) :
    DigitLattice.closure B - DigitLattice.closure B =
      DigitLattice.closure (2 * B) ∪ hex (3 * B) := by
  refine Finset.Subset.antisymm (sub_subset B) ?_
  intro d hd
  rcases Finset.mem_union.mp hd with h | h
  · exact closure_subset_sub B h
  · exact hex_subset_sub B h

/-! ## 2. The Eisenstein norm on the difference set: the constant `12` -/

/-- The Eisenstein form on a box: `|X|, |Y| ≤ C` implies `X² + XY + Y² ≤ 3C²`, with
    equality at `X = Y = C`. -/
theorem quad_le {X Y C : ℤ} (hX : -C ≤ X) (hX' : X ≤ C) (hY : -C ≤ Y) (hY' : Y ≤ C) :
    X ^ 2 + X * Y + Y ^ 2 ≤ 3 * C ^ 2 := by
  have hx2 : X ^ 2 ≤ C ^ 2 := by nlinarith
  have hy2 : Y ^ 2 ≤ C ^ 2 := by nlinarith
  have hxy : 2 * (X * Y) ≤ X ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg (X - Y)]
  linarith

/-- On `Ω_{2B}` the Eisenstein norm `u² + uv + v²` is at most `12B²`. -/
theorem eisenstein_le_twelve {B u v : ℤ} (h : ((u, v) : ℤ × ℤ) ∈ DigitLattice.closure (2 * B)) :
    u ^ 2 + u * v + v ^ 2 ≤ 12 * B ^ 2 := by
  rw [mem_closure] at h
  simp only [abs_le] at h
  have hC : 3 * (2 * B) ^ 2 = 12 * B ^ 2 := by ring
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := quad_le (X := u) (Y := v) (C := 2 * B) h1.1 h1.2 h2.1 h2.2
    linarith
  · have := quad_le (X := u) (Y := -(u + v)) (C := 2 * B) h1.1 h1.2 (by omega) (by omega)
    nlinarith [this]
  · have := quad_le (X := v) (Y := -(u + v)) (C := 2 * B) h1.1 h1.2 (by omega) (by omega)
    nlinarith [this]

/-- On the whole difference set `Ω_B − Ω_B` the Eisenstein norm is at most `12B²`. -/
theorem eisenstein_le_of_mem_sub {B u v : ℤ} (hB : 0 ≤ B)
    (h : ((u, v) : ℤ × ℤ) ∈ DigitLattice.closure B - DigitLattice.closure B) :
    u ^ 2 + u * v + v ^ 2 ≤ 12 * B ^ 2 := by
  rcases Finset.mem_union.mp (sub_subset B h) with h' | h'
  · exact eisenstein_le_twelve h'
  · have h1 := eisenstein_le_hexNorm_sq u v
    rw [mem_hex_iff_hexNorm] at h'
    have h2 : OrderSix.hexNorm u v ≤ 3 * B := h'
    have h3 : 0 ≤ OrderSix.hexNorm u v := hexNorm_nonneg u v
    nlinarith

/-- The constant `12` is attained: `(2B, 2B)` lies in `Ω_B − Ω_B` and has Eisenstein norm
    exactly `12B²`, so the bound of `eisenstein_le_of_mem_sub` is sharp. -/
theorem twelve_sharp {B : ℤ} (hB : 0 ≤ B) :
    ((2 * B, 2 * B) : ℤ × ℤ) ∈ DigitLattice.closure B - DigitLattice.closure B ∧
      (2 * B) ^ 2 + (2 * B) * (2 * B) + (2 * B) ^ 2 = 12 * B ^ 2 := by
  refine ⟨box_subset_sub B ?_, by ring⟩
  rw [mem_box]; simp only [abs_le]; omega

/-! ## 3. The feasibility constants of the closure -/

/-- (Theorem "Feasibility", box closure, sufficient side with the constant `12`.)
    For `A² ≡ A − 1 (mod p)` and `12B² < p`, `φ_A` is injective on the closure `Ω_B`. -/
theorem closure_injective_of_lt (A : ℤ) (p : ℕ) (hA : (p : ℤ) ∣ A ^ 2 - A + 1) {B : ℤ}
    (hB : 0 ≤ B) (h12 : 12 * B ^ 2 < p) :
    Set.InjOn (phi (A : ZMod p)) (DigitLattice.closure B) := by
  rw [injOn_iff_kernel]
  rintro ⟨u, v⟩ hmem hker
  by_contra hne
  rw [phi_zmod_eq_zero_iff] at hker
  have h1 : (p : ℤ) ≤ u ^ 2 + u * v + v ^ 2 := eisenstein_ge hA hker hne
  have h2 := eisenstein_le_of_mem_sub hB hmem
  linarith

/-- (Theorem "Feasibility", box closure, necessary side with the constant `27/4`.)
    If `φ_A` is injective on `Ω_B` then `27B² + 18B + 3 ≤ 4p`: the kernel vector with
    `u² + uv + v² = p` lies outside `T_{3B} ⊆ Ω_B − Ω_B`, hence has `N > 3B`, and
    `3N² ≤ 4p`. -/
theorem closure_injective_imp {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 - A + 1)
    {B : ℤ} (hB : 0 ≤ B)
    (hinj : Set.InjOn (phi (A : ZMod p)) (DigitLattice.closure B)) :
    27 * B ^ 2 + 18 * B + 3 ≤ 4 * p := by
  rw [injOn_iff_kernel] at hinj
  obtain ⟨u, v, hne, hker, hsum⟩ := exists_kernel_eisenstein_eq hp hA
  have hnotin : ((u, v) : ℤ × ℤ) ∉ DigitLattice.closure B - DigitLattice.closure B := fun hm =>
    hne (hinj _ hm ((phi_zmod_eq_zero_iff A p (u, v)).mpr hker))
  have hnothex : ((u, v) : ℤ × ℤ) ∉ hex (3 * B) := fun hm => hnotin (hex_subset_sub B hm)
  have hN : 3 * B < OrderSix.hexNorm u v := by
    by_contra hc
    exact hnothex (mem_hex_iff_hexNorm.mpr (not_lt.mp hc))
  have h3 := three_mul_hexNorm_sq_le hsum
  nlinarith

/-- The feasibility constant of the box closure is pinned to `27/4 ≤ c_Ω ≤ 12`:
    `12B² < p ⟹ injective ⟹ 27B² < 4p`. -/
theorem closure_constants {A : ℤ} {p : ℕ} (hp : p.Prime) (hA : (p : ℤ) ∣ A ^ 2 - A + 1)
    {B : ℤ} (hB : 0 ≤ B) :
    (12 * B ^ 2 < p → Set.InjOn (phi (A : ZMod p)) (DigitLattice.closure B)) ∧
      (Set.InjOn (phi (A : ZMod p)) (DigitLattice.closure B) → 27 * B ^ 2 < 4 * p) := by
  refine ⟨closure_injective_of_lt A p hA hB, fun hinj => ?_⟩
  have h := closure_injective_imp hp hA hB hinj
  linarith

end Closure
