/-
  Lattice.lean

  Formal verification (Lean 4 + Mathlib) of the digit-lattice statements of

    "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping"

  (Section "Preliminaries: the rank-two digit lattice", Lemma "Injectivity
  criterion", Lemma "Injectivity as a lattice minimum", Lemma "Order-six
  stability of the hexagon", Lemma "The order-six filter on the closed box").
  With no unproved placeholders:

  * `phi`, `rot`, `phi_rot`
        The encoding `φ_A(η,λ) = ηA + λ` and the companion action
        `M_A(η,λ) = (τη + λ, −η)` intertwine:  `φ_A ∘ M_A = A · φ_A`
        whenever `A² = τA − 1`.                                (eq. (M_A))

  * `MA`, `MA_mulVec`, `rot_bijective`
        `M_A = [[τ,1],[−1,0]]` acts on column vectors as `rot τ`; it is a
        bijection of `ℤ²` (inverse `(a,b) ↦ (−b, a + τb)`).

  * `injOn_iff_kernel`
        (Lemma "Injectivity as a lattice minimum", first equivalence)
        `φ_A` is injective on a finite `T ⊆ ℤ²` iff no nonzero element of
        `T − T` lies in the kernel lattice `L_A = ker φ_A`.

  * `kernel_box_trivial`, `box_injective_int`, `box_injective_zmod`
        (Lemma "Injectivity criterion", sufficiency)
        `2B < |A|` and `2B(|A| + 1) < p` imply that `φ_A` is injective on
        `[−B,B]²` modulo `p`.

  * `box`, `hex`, `closure`, `mem_*`, `hex_rot_iff`, `box_rot_iff`, `closure_rot_iff`
        The box, the hexagon `T_B = {|η|,|λ|,|η+λ| ≤ B}` and the orbit closure
        `Ω_B = {at least two of |η|,|λ|,|η+λ| ≤ B}`; stability of the box under
        the quarter turn (τ = 0) and of the hexagon and the closure under the
        sixth turn (τ = 1).

  * `card_box`, `card_hex`, `card_closure`
        `|[−B,B]²| = (2B+1)²`, `|T_B| = 3B² + 3B + 1` and
        `|Ω_B| = 6B² + 6B + 1`, symbolically in `B`
        (Lemma "The order-six filter on the closed box", inclusion–exclusion).
-/
import Mathlib
import SymmetryGraded.OrderSix

namespace DigitLattice

open Finset
open scoped Pointwise

/-! ## 1. The encoding map and the companion action -/
section Intertwine
variable {R : Type*} [CommRing R]

/-- The encoding map `φ_A(η, λ) = ηA + λ` from the digit lattice `ℤ²` into `R`. -/
def phi (A : R) (v : ℤ × ℤ) : R := v.1 * A + v.2

/-- The companion action `M_A(η, λ) = (τη + λ, −η)` on the digit lattice. -/
def rot (τ : ℤ) (v : ℤ × ℤ) : ℤ × ℤ := (τ * v.1 + v.2, -v.1)

@[simp] lemma phi_zero (A : R) : phi A 0 = 0 := by simp [phi]

lemma phi_sub (A : R) (v w : ℤ × ℤ) : phi A (v - w) = phi A v - phi A w := by
  simp only [phi, Prod.fst_sub, Prod.snd_sub]; push_cast; ring

/-- The intertwining identity `φ_A(M_A v) = A · φ_A(v)` for `A² = τA − 1`:
    `A·(ηA + λ) = (τη + λ)A − η`. -/
theorem phi_rot {A : R} {τ : ℤ} (hA : A ^ 2 = τ * A - 1) (v : ℤ × ℤ) :
    phi A (rot τ v) = A * phi A v := by
  simp only [phi, rot]; push_cast
  linear_combination -(v.1 : R) * hA

/-- Iterating: `φ_A(M_Aⁿ v) = Aⁿ · φ_A(v)`. -/
theorem phi_rot_iterate {A : R} {τ : ℤ} (hA : A ^ 2 = τ * A - 1) (n : ℕ) (v : ℤ × ℤ) :
    phi A ((rot τ)^[n] v) = A ^ n * phi A v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, phi_rot hA, pow_succ]; ring

/-- The companion matrix `M_A = [[τ, 1], [−1, 0]]`. -/
def MA (τ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![τ, 1; -1, 0]

/-- `M_A` acts on column vectors as `rot τ`. -/
theorem MA_mulVec (τ η l : ℤ) : (MA τ).mulVec ![η, l] = ![τ * η + l, -η] := by
  ext i; fin_cases i <;> simp [MA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `M_A` has determinant `1` and trace `τ`. -/
theorem MA_det (τ : ℤ) : (MA τ).det = 1 := by simp [MA, Matrix.det_fin_two]

theorem MA_trace (τ : ℤ) : (MA τ).trace = τ := by simp [MA, Matrix.trace_fin_two]

/-- The inverse action `(a, b) ↦ (−b, a + τb)`. -/
def rotInv (τ : ℤ) (v : ℤ × ℤ) : ℤ × ℤ := (-v.2, v.1 + τ * v.2)

theorem rotInv_rot (τ : ℤ) (v : ℤ × ℤ) : rotInv τ (rot τ v) = v := by
  simp only [rotInv, rot]; ext <;> simp

theorem rot_rotInv (τ : ℤ) (v : ℤ × ℤ) : rot τ (rotInv τ v) = v := by
  simp only [rotInv, rot]; ext <;> simp

/-- `rot τ` is a bijection of the digit lattice. -/
theorem rot_bijective (τ : ℤ) : Function.Bijective (rot τ) :=
  Function.bijective_iff_has_inverse.mpr ⟨rotInv τ, rotInv_rot τ, rot_rotInv τ⟩

end Intertwine

/-! ## 2. Injectivity as a kernel condition on `T − T` -/
section Injectivity
variable {R : Type*} [CommRing R]

/-- (Lemma "Injectivity as a lattice minimum", first equivalence.)  For a finite
    region `T ⊆ ℤ²`, the encoding `φ_A` is injective on `T` iff the only element of
    the difference set `T − T` in the kernel lattice `L_A = {u : φ_A(u) = 0}` is `0`. -/
theorem injOn_iff_kernel (A : R) (T : Finset (ℤ × ℤ)) :
    Set.InjOn (phi A) T ↔ ∀ u ∈ T - T, phi A u = 0 → u = 0 := by
  constructor
  · intro hinj u hu hu0
    obtain ⟨v, hv, w, hw, rfl⟩ := Finset.mem_sub.mp hu
    rw [phi_sub, sub_eq_zero] at hu0
    rw [hinj hv hw hu0, sub_self]
  · intro hker v hv w hw hvw
    have hmem : v - w ∈ T - T := Finset.sub_mem_sub hv hw
    have h0 : phi A (v - w) = 0 := by rw [phi_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hker _ hmem h0)

end Injectivity

/-! ## 3. Lemma "Injectivity criterion": the sufficient condition -/
section Criterion

/-- An integer multiple of `p` of absolute value `< p` is zero. -/
lemma eq_zero_of_dvd_of_abs_lt {p x : ℤ} (hdvd : p ∣ x) (habs : |x| < p) : x = 0 := by
  rcases hdvd with ⟨t, rfl⟩
  have hp0 : 0 < p := lt_of_le_of_lt (abs_nonneg _) habs
  by_contra hne
  have ht0 : t ≠ 0 := by rintro rfl; exact hne (mul_zero p)
  have h1 : (1 : ℤ) ≤ |t| := Int.one_le_abs ht0
  have hle : p ≤ |p * t| := by
    rw [abs_mul, abs_of_pos hp0]
    calc p = p * 1 := (mul_one p).symm
      _ ≤ p * |t| := mul_le_mul_of_nonneg_left h1 hp0.le
  linarith

/-- (Lemma "Injectivity criterion", kernel form.)  If `2B < |A|` and
    `2B(|A|+1) < p`, then the only kernel vector `(u, v)` (i.e. `p ∣ uA + v`) in
    `[−2B, 2B]²` is `(0, 0)`. -/
theorem kernel_box_trivial (A p B : ℤ) (hA : 2 * B < |A|) (hp : 2 * B * (|A| + 1) < p)
    {u v : ℤ} (hu : |u| ≤ 2 * B) (hv : |v| ≤ 2 * B) (hdvd : p ∣ u * A + v) :
    u = 0 ∧ v = 0 := by
  have hB : 0 ≤ 2 * B := le_trans (abs_nonneg u) hu
  have habs : |u * A + v| < p := by
    calc |u * A + v| ≤ |u * A| + |v| := abs_add_le _ _
      _ = |u| * |A| + |v| := by rw [abs_mul]
      _ ≤ 2 * B * |A| + 2 * B :=
          add_le_add (mul_le_mul_of_nonneg_right hu (abs_nonneg A)) hv
      _ = 2 * B * (|A| + 1) := by ring
      _ < p := hp
  have h0 : u * A + v = 0 := eq_zero_of_dvd_of_abs_lt hdvd habs
  have hu0 : u = 0 := by
    by_contra hne
    have h1 : (1 : ℤ) ≤ |u| := Int.one_le_abs hne
    have hvA : |v| = |u| * |A| := by
      rw [← abs_mul, abs_eq_abs]; right; linear_combination h0
    have : |A| ≤ |u| * |A| := by
      calc |A| = 1 * |A| := (one_mul _).symm
        _ ≤ |u| * |A| := mul_le_mul_of_nonneg_right h1 (abs_nonneg A)
    linarith
  subst hu0
  exact ⟨rfl, by linarith⟩

/-- (Lemma "Injectivity criterion", integer form.)  Under `2B < |A|` and
    `2B(|A|+1) < p`, two digit pairs in `[−B, B]²` whose encodings agree modulo
    `p` are equal. -/
theorem box_injective_int (A p B : ℤ) (hA : 2 * B < |A|) (hp : 2 * B * (|A| + 1) < p)
    {η₁ l₁ η₂ l₂ : ℤ} (hη₁ : |η₁| ≤ B) (hl₁ : |l₁| ≤ B) (hη₂ : |η₂| ≤ B) (hl₂ : |l₂| ≤ B)
    (hdvd : p ∣ (η₁ * A + l₁) - (η₂ * A + l₂)) : η₁ = η₂ ∧ l₁ = l₂ := by
  have hu : |η₁ - η₂| ≤ 2 * B := by
    calc |η₁ - η₂| ≤ |η₁| + |η₂| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hv : |l₁ - l₂| ≤ 2 * B := by
    calc |l₁ - l₂| ≤ |l₁| + |l₂| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hd : p ∣ (η₁ - η₂) * A + (l₁ - l₂) := by
    have : (η₁ - η₂) * A + (l₁ - l₂) = (η₁ * A + l₁) - (η₂ * A + l₂) := by ring
    rw [this]; exact hdvd
  obtain ⟨h1, h2⟩ := kernel_box_trivial A p B hA hp hu hv hd
  exact ⟨by linarith, by linarith⟩

/-- (Lemma "Injectivity criterion", `ZMod p` form.)  With `A` the balanced integer
    representative of the radix, `φ_A` is injective on `[−B, B]²` into `ZMod p`. -/
theorem box_injective_zmod (A : ℤ) (p : ℕ) (B : ℤ) (hA : 2 * B < |A|)
    (hp : 2 * B * (|A| + 1) < p)
    {η₁ l₁ η₂ l₂ : ℤ} (hη₁ : |η₁| ≤ B) (hl₁ : |l₁| ≤ B) (hη₂ : |η₂| ≤ B) (hl₂ : |l₂| ≤ B)
    (heq : phi (A : ZMod p) (η₁, l₁) = phi (A : ZMod p) (η₂, l₂)) :
    (η₁, l₁) = (η₂, l₂) := by
  have hcast : ∀ η l : ℤ, phi (A : ZMod p) (η, l) = ((η * A + l : ℤ) : ZMod p) := by
    intro η l; simp [phi]
  rw [hcast, hcast, ZMod.intCast_eq_intCast_iff_dvd_sub] at heq
  have hdvd : (p : ℤ) ∣ (η₁ * A + l₁) - (η₂ * A + l₂) := dvd_sub_comm.mp heq
  obtain ⟨h1, h2⟩ := box_injective_int A p B hA hp hη₁ hl₁ hη₂ hl₂ hdvd
  rw [h1, h2]

end Criterion

/-! ## 4. The box, the hexagon and the orbit closure -/
section Regions

/-- The box `[−B, B]²`. -/
noncomputable def box (B : ℤ) : Finset (ℤ × ℤ) := Icc (-B) B ×ˢ Icc (-B) B

/-- The hexagon `T_B = {(η, λ) : |η|, |λ|, |η + λ| ≤ B}`. -/
noncomputable def hex (B : ℤ) : Finset (ℤ × ℤ) := (box B).filter (fun v => |v.1 + v.2| ≤ B)

/-- The orbit closure of the box under the sixth turn:
    `Ω_B = {(η, λ) : at least two of |η|, |λ|, |η + λ| are ≤ B}`. -/
noncomputable def closure (B : ℤ) : Finset (ℤ × ℤ) :=
  (box (2 * B)).filter (fun v =>
    (|v.1| ≤ B ∧ |v.2| ≤ B) ∨ (|v.1| ≤ B ∧ |v.1 + v.2| ≤ B) ∨ (|v.2| ≤ B ∧ |v.1 + v.2| ≤ B))

theorem mem_box {B : ℤ} {v : ℤ × ℤ} : v ∈ box B ↔ |v.1| ≤ B ∧ |v.2| ≤ B := by
  simp [box, Finset.mem_product, abs_le]

theorem mem_hex {B : ℤ} {v : ℤ × ℤ} :
    v ∈ hex B ↔ |v.1| ≤ B ∧ |v.2| ≤ B ∧ |v.1 + v.2| ≤ B := by
  simp [hex, mem_box, and_assoc]

theorem mem_closure {B : ℤ} {v : ℤ × ℤ} :
    v ∈ closure B ↔
      (|v.1| ≤ B ∧ |v.2| ≤ B) ∨ (|v.1| ≤ B ∧ |v.1 + v.2| ≤ B) ∨
        (|v.2| ≤ B ∧ |v.1 + v.2| ≤ B) := by
  simp only [closure, Finset.mem_filter, mem_box]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    simp only [abs_le] at h ⊢
    omega

/-- The hexagon is the sublevel set `{N ≤ B}` of the hexagon norm of `OrderSix.lean`. -/
theorem mem_hex_iff_hexNorm {B : ℤ} {v : ℤ × ℤ} :
    v ∈ hex B ↔ OrderSix.hexNorm v.1 v.2 ≤ B := by
  rw [mem_hex, OrderSix.hexNorm]; simp

theorem box_subset_closure (B : ℤ) : box B ⊆ closure B := by
  intro v hv; rw [mem_closure]; exact Or.inl (mem_box.mp hv)

theorem hex_subset_box (B : ℤ) : hex B ⊆ box B := Finset.filter_subset _ _

/-- (Lemma "Order-six stability of the hexagon".)  The sixth turn
    `(η, λ) ↦ (η + λ, −η)` maps `T_B` onto itself. -/
theorem hex_rot_iff (B : ℤ) (v : ℤ × ℤ) : rot 1 v ∈ hex B ↔ v ∈ hex B := by
  simp only [mem_hex, rot, abs_le]; omega

/-- The quarter turn `(η, λ) ↦ (λ, −η)` maps the box onto itself
    (Theorem "Classification of admissible orders by stable region", the box). -/
theorem box_rot_iff (B : ℤ) (v : ℤ × ℤ) : rot 0 v ∈ box B ↔ v ∈ box B := by
  simp only [mem_box, rot, abs_le]; omega

/-- The sixth turn maps the orbit closure `Ω_B` onto itself
    (Lemma "The order-six filter on the closed box", stability). -/
theorem closure_rot_iff (B : ℤ) (v : ℤ × ℤ) : rot 1 v ∈ closure B ↔ v ∈ closure B := by
  simp only [mem_closure, rot, abs_le]; omega

/-- The box is *not* stable under the sixth turn for `B ≥ 1`: the corner `(B, B)`
    escapes to `(2B, −B)`. -/
theorem box_not_rot_stable (B : ℤ) (hB : 1 ≤ B) :
    (B, B) ∈ box B ∧ rot 1 (B, B) ∉ box B := by
  simp only [mem_box, rot, abs_le]; omega

/-- The closure is the union of the three orbit images of the box; it is the
    smallest sixth-turn-stable region containing the box. -/
theorem closure_eq_union (B : ℤ) :
    closure B = box B ∪ (box B).image (rot 1) ∪ (box B).image (rot 1 ∘ rot 1) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_union, Finset.mem_image, mem_closure, mem_box, rot,
    Function.comp, Prod.mk.injEq, Prod.exists, abs_le, one_mul]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · refine Or.inr ⟨-(x + y), x, ?_⟩; omega
    · refine Or.inl (Or.inr ⟨-y, x + y, ?_⟩); omega
  · rintro ((h | ⟨a, b, hab, ha, hb⟩) | ⟨a, b, hab, ha, hb⟩)
    · exact Or.inl h
    · right; right; omega
    · right; left; omega

end Regions

/-! ## 5. Counting: `|[−B,B]²| = (2B+1)²`, `|T_B| = 3B²+3B+1`, `|Ω_B| = 6B²+6B+1` -/
section Counting

lemma card_Icc_sym (B : ℕ) : (Icc (-(B : ℤ)) B).card = 2 * B + 1 := by
  rw [Int.card_Icc]; omega

/-- `|[−B, B]²| = (2B + 1)²`. -/
theorem card_box (B : ℕ) : (box B).card = (2 * B + 1) ^ 2 := by
  rw [box, Finset.card_product, card_Icc_sym]; ring

/-- The fibre of the hexagon over a fixed `η` is an interval of `2B + 1 − |η|`
    values of `λ`. -/
lemma card_hex_fiber (B : ℕ) (η : ℤ) (hη : η ∈ Icc (-(B : ℤ)) B) :
    ((hex B).filter (fun v => v.1 = η)).card = (2 * B + 1 - |η|).toNat := by
  have hfib : (hex B).filter (fun v => v.1 = η) =
      (Icc (max (-(B : ℤ)) (-B - η)) (min (B : ℤ) (B - η))).map
        ⟨fun l => (η, l), fun a b h => by simpa using h⟩ := by
    rw [Finset.mem_Icc] at hη
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, mem_hex, Finset.mem_map, Finset.mem_Icc,
      Function.Embedding.coeFn_mk, Prod.mk.injEq, abs_le]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨b, by omega, rfl, rfl⟩
    · rintro ⟨l, hl, rfl, rfl⟩
      exact ⟨by omega, rfl⟩
  rw [hfib, Finset.card_map, Int.card_Icc]
  rw [Finset.mem_Icc] at hη
  rw [abs_eq_max_neg]
  omega

/-- `Σ_{η = −B}^{B} |η| = B(B + 1)`. -/
lemma sum_abs_Icc (B : ℕ) : ∑ η ∈ Icc (-(B : ℤ)) B, |η| = B * (B + 1) := by
  induction B with
  | zero => simp
  | succ n ih =>
      have hsplit : Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
          insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Icc (-(n : ℤ)) n)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
      have h1 : ((n : ℤ) + 1) ∉ Icc (-(n : ℤ)) n := by simp
      have h2 : -((n : ℤ) + 1) ∉ insert ((n : ℤ) + 1) (Icc (-(n : ℤ)) n) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert h2, Finset.sum_insert h1, ih, abs_neg,
        abs_of_nonneg (by positivity)]
      push_cast; ring

/-- (Lemma "The order-six filter on the closed box", hexagon count.)
    `|T_B| = 3B² + 3B + 1`. -/
theorem card_hex (B : ℕ) : (hex B).card = 3 * B ^ 2 + 3 * B + 1 := by
  have hmaps : Set.MapsTo Prod.fst (↑(hex B) : Set (ℤ × ℤ)) (↑(Icc (-(B : ℤ)) B)) := by
    intro v hv
    rw [Finset.mem_coe, mem_hex] at hv
    rw [Finset.mem_coe, Finset.mem_Icc]; exact abs_le.mp hv.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  rw [Finset.sum_congr rfl (fun η hη => card_hex_fiber B η hη)]
  have hcast : ((∑ η ∈ Icc (-(B : ℤ)) B, (2 * (B : ℤ) + 1 - |η|).toNat : ℕ) : ℤ)
      = ∑ η ∈ Icc (-(B : ℤ)) B, (2 * (B : ℤ) + 1 - |η|) := by
    push_cast
    apply Finset.sum_congr rfl
    intro η hη
    rw [Finset.mem_Icc] at hη
    have habs : |η| ≤ B := abs_le.mpr ⟨hη.1, hη.2⟩
    rw [Int.toNat_of_nonneg (by omega)]
  have hsum : ∑ η ∈ Icc (-(B : ℤ)) B, (2 * (B : ℤ) + 1 - |η|)
      = 3 * (B : ℤ) ^ 2 + 3 * B + 1 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_Icc_sym, sum_abs_Icc]
    simp only [nsmul_eq_mul]; push_cast; ring
  have := hcast.trans hsum
  exact_mod_cast this

/-- The image of the box under the sixth turn is `{|λ| ≤ B, |η+λ| ≤ B}`. -/
lemma mem_image_rot {B : ℤ} {v : ℤ × ℤ} :
    v ∈ (box B).image (rot 1) ↔ |v.2| ≤ B ∧ |v.1 + v.2| ≤ B := by
  obtain ⟨x, y⟩ := v
  simp only [Finset.mem_image, mem_box, rot, Prod.exists, Prod.mk.injEq, abs_le, one_mul]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩; omega
  · intro h; refine ⟨-y, x + y, ?_⟩; omega

/-- The image of the box under two sixth turns is `{|η| ≤ B, |η+λ| ≤ B}`. -/
lemma mem_image_rot_rot {B : ℤ} {v : ℤ × ℤ} :
    v ∈ (box B).image (rot 1 ∘ rot 1) ↔ |v.1| ≤ B ∧ |v.1 + v.2| ≤ B := by
  obtain ⟨x, y⟩ := v
  simp only [Finset.mem_image, mem_box, rot, Function.comp, Prod.exists, Prod.mk.injEq,
    abs_le, one_mul]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩; omega
  · intro h; refine ⟨-(x + y), x, ?_⟩; omega

lemma card_image_rot (B : ℕ) : ((box B).image (rot 1)).card = (2 * B + 1) ^ 2 := by
  rw [Finset.card_image_of_injective _ (rot_bijective 1).1, card_box]

lemma card_image_rot_rot (B : ℕ) :
    ((box B).image (rot 1 ∘ rot 1)).card = (2 * B + 1) ^ 2 := by
  rw [Finset.card_image_of_injective _ ((rot_bijective 1).1.comp (rot_bijective 1).1),
    card_box]

/-- (Lemma "The order-six filter on the closed box", closure count.)
    `|Ω_B| = 6B² + 6B + 1 = (3(2B+1)² − 1)/2`, by inclusion–exclusion over the
    three box images, every pairwise and the triple intersection being the hexagon. -/
theorem card_closure (B : ℕ) : (closure B).card = 6 * B ^ 2 + 6 * B + 1 := by
  set X := box (B : ℤ) with hX
  set Y := (box (B : ℤ)).image (rot 1) with hY
  set Z := (box (B : ℤ)).image (rot 1 ∘ rot 1) with hZ
  have hXY : X ∩ Y = hex B := by
    ext v; simp only [Finset.mem_inter, hX, hY, mem_box, mem_image_rot, mem_hex]; tauto
  have hXZ : X ∩ Z = hex B := by
    ext v; simp only [Finset.mem_inter, hX, hZ, mem_box, mem_image_rot_rot, mem_hex]; tauto
  have hYZ : Y ∩ Z = hex B := by
    ext v; simp only [Finset.mem_inter, hY, hZ, mem_image_rot, mem_image_rot_rot, mem_hex]
    tauto
  have hXYZ : (X ∪ Y) ∩ Z = hex B := by
    rw [Finset.union_inter_distrib_right, hXZ, hYZ, Finset.union_self]
  have h1 := Finset.card_union_add_card_inter X Y
  have h2 := Finset.card_union_add_card_inter (X ∪ Y) Z
  rw [closure_eq_union, ← hX, ← hY, ← hZ]
  rw [hXY, card_hex, card_box, card_image_rot] at h1
  rw [hXYZ, card_hex, card_image_rot_rot] at h2
  have hsq : (2 * B + 1) ^ 2 = 4 * B ^ 2 + 4 * B + 1 := by ring
  omega

/-- The hexagon and the closure have cardinality `≡ 1 (mod 6)`, so the term-count
    formula `(|S_A| − 1)/6` of `OrderSix.card_v5_mod` applies to both. -/
theorem card_hex_mod_six (B : ℕ) : (hex B).card % 6 = 1 := by
  rw [card_hex]
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self B
  have : 3 * B ^ 2 + 3 * B = 6 * k := by
    rw [show 3 * B ^ 2 + 3 * B = 3 * (B * (B + 1)) by ring, hk]; ring
  omega

theorem card_closure_mod_six (B : ℕ) : (closure B).card % 6 = 1 := by
  rw [card_closure]; omega

end Counting

end DigitLattice
