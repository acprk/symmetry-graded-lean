/-
  Coverage.lean

  Formal verification (Lean 4 + Mathlib) of

    Corollary "Coverage, independent of the region"  (Appendix "Proofs for the scalar axis")
    Corollary "Closed-form selector"                 (Section "The scalar axis")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".  Both are
  assembled from statements proved elsewhere in this development: the feasibility
  constants `c₄ = 8`, `c₆ = 4`, `c_Ω = 12` of `LatticeMin.box_constants`,
  `LatticeMin.hex_constants` and `Closure.closure_constants`, the availability table of
  `Radix.available_orders_seven`, and the cost monotonicity `Unify.gcost_antitone`.
  With no unproved placeholders:

  * `order_four_feasible_imp_order_six`
        order six on the hexagon is feasible wherever order four on the box is:
        box-injective ⟹ `4B² < p` ⟹ hexagon-injective.
  * `coverage_dichotomy`, `coverage_band`
        at every `(p, B)` either order six is feasible on the hexagon or order four is
        infeasible on the box; and the threshold `4B²` separates the two sides.
  * `order_six_closure_feasible_imp`, `coverage_band_closure`
        the same comparison against the box closure, at the constant `12`.
  * `no_order_four_mod_twelve_seven`
        for `p ≡ 7 (mod 12)` no order-four radix exists at all — a condition on `p`
        alone, hence failing at every digit bound `B` — while orders `2, 3, 6` do.
  * `exists_argmax_tiebreak`
        the selector `r⋆ = argmax ρ` with ties broken by `ν`, as a statement about a
        nonempty `Finset`.
  * `selector_max'_mem`, `selector_gcost`
        the cost consequence: the largest usable order minimises the graded cost.
  * `max'_two_three_six`, `selector_mod_twelve_seven`
        the instance `p ≡ 7 (mod 12)`: available orders `{2, 3, 6}`, optimum `r⋆ = 6`.
  * `rho_hex`, `rho_closure_bounds`
        the effective orders quoted by the corollary: `ρ = 6` on the hexagon (a stable
        region) and `4 < ρ ≤ 6` on the box closure.
-/
import Mathlib
import SymmetryGraded.LatticeMin
import SymmetryGraded.Closure
import SymmetryGraded.Radix
import SymmetryGraded.Unify
import SymmetryGraded.PSCount

namespace Coverage

open DigitLattice

/-! ## 1. Coverage: order six is feasible wherever order four is -/

section Regions
variable {A₄ A₆ : ℤ} {p : ℕ} {B : ℤ}

/-- (Corollary "Coverage", inclusion of the feasible regions.)  If the digit map of an
    order-four radix is injective on the box `[−B, B]²`, then the digit map of an
    order-six radix is injective on the hexagon `T_B`.  The chain is
    `box-injective ⟹ 4B² < p ⟹ hexagon-injective`: the necessary constant of the box
    dominates the sufficient constant of the hexagon, both being `4`. -/
theorem order_four_feasible_imp_order_six (hp : p.Prime) (hA₄ : (p : ℤ) ∣ A₄ ^ 2 + 1)
    (hA₆ : (p : ℤ) ∣ A₆ ^ 2 - A₆ + 1) (hB : 0 ≤ B)
    (h : Set.InjOn (phi (A₄ : ZMod p)) (box B)) :
    Set.InjOn (phi (A₆ : ZMod p)) (hex B) :=
  (LatticeMin.hex_constants hp hA₆ hB).1 ((LatticeMin.box_constants hp hA₄ hB).2 h)

/-- (Corollary "Coverage", dichotomy form.)  At every pair `(p, B)`, either order six is
    feasible on the hexagon or order four is infeasible on the box: there is no pair at
    which order four works and order six does not. -/
theorem coverage_dichotomy (hp : p.Prime) (hA₄ : (p : ℤ) ∣ A₄ ^ 2 + 1)
    (hA₆ : (p : ℤ) ∣ A₆ ^ 2 - A₆ + 1) (hB : 0 ≤ B) :
    Set.InjOn (phi (A₆ : ZMod p)) (hex B) ∨ ¬ Set.InjOn (phi (A₄ : ZMod p)) (box B) := by
  by_cases h : Set.InjOn (phi (A₄ : ZMod p)) (box B)
  · exact Or.inl (order_four_feasible_imp_order_six hp hA₄ hA₆ hB h)
  · exact Or.inr h

/-- (Corollary "Coverage", the band.)  The threshold `4B²` separates the two orders:
    above it order six is feasible on the hexagon, and at or below it order four is
    infeasible on the box.  The paper's band `4B² ≲ p ≲ 8B²` is the gap between the
    necessary constant `4` and the sufficient constant `8` of the box, inside which
    order four may or may not be injective depending on the instance; what is proved
    here is the rigorous part, namely the two implications at the threshold `4B²`. -/
theorem coverage_band (hp : p.Prime) (hA₄ : (p : ℤ) ∣ A₄ ^ 2 + 1)
    (hA₆ : (p : ℤ) ∣ A₆ ^ 2 - A₆ + 1) (hB : 0 ≤ B) :
    (4 * B ^ 2 < (p : ℤ) → Set.InjOn (phi (A₆ : ZMod p)) (hex B)) ∧
      ((p : ℤ) ≤ 4 * B ^ 2 → ¬ Set.InjOn (phi (A₄ : ZMod p)) (box B)) := by
  refine ⟨(LatticeMin.hex_constants hp hA₆ hB).1, fun hle hinj => ?_⟩
  exact absurd ((LatticeMin.box_constants hp hA₄ hB).2 hinj) (not_lt.mpr hle)

/-- Injectivity on the box closure `Ω_B` restricts to injectivity on the hexagon
    `T_B ⊆ [−B, B]² ⊆ Ω_B`. -/
theorem order_six_closure_feasible_imp
    (h : Set.InjOn (phi (A₆ : ZMod p)) (DigitLattice.closure B)) :
    Set.InjOn (phi (A₆ : ZMod p)) (hex B) := by
  apply Set.InjOn.mono _ h
  intro v hv
  exact Finset.mem_coe.mpr (box_subset_closure B (hex_subset_box B (Finset.mem_coe.mp hv)))

/-- (Corollary "Coverage", box-closure side.)  Above `12B²` order six is feasible on the
    box closure, while at or below `4B²` order four is infeasible on the box; this is the
    "order six on the region the pipeline supplies" half of the corollary. -/
theorem coverage_band_closure (hp : p.Prime) (hA₄ : (p : ℤ) ∣ A₄ ^ 2 + 1)
    (hA₆ : (p : ℤ) ∣ A₆ ^ 2 - A₆ + 1) (hB : 0 ≤ B) :
    (12 * B ^ 2 < (p : ℤ) → Set.InjOn (phi (A₆ : ZMod p)) (DigitLattice.closure B)) ∧
      ((p : ℤ) ≤ 4 * B ^ 2 → ¬ Set.InjOn (phi (A₄ : ZMod p)) (box B)) :=
  ⟨(Closure.closure_constants hp hA₆ hB).1, (coverage_band hp hA₄ hA₆ hB).2⟩

end Regions

/-! ## 2. The residue class `p ≡ 7 (mod 12)`: order four never exists -/

/-- (Corollary "Coverage", the class `p ≡ 7 (mod 12)`.)  For a prime `p ≡ 7 (mod 12)` no
    order-four radix exists, and orders `2, 3, 6` all do.  The nonexistence is a
    condition on `p` alone — there is not even a square root of `−1` in `ZMod p` — so no
    choice of digit bound `B` can repair it. -/
theorem no_order_four_mod_twelve_seven (p : ℕ) [Fact p.Prime] (h : p % 12 = 7) :
    ¬ Radix.HasOrder p 4 ∧ (¬ ∃ A : ZMod p, A ^ 2 = -1) ∧
      Radix.HasOrder p 2 ∧ Radix.HasOrder p 3 ∧ Radix.HasOrder p 6 := by
  obtain ⟨h2, h3, h6, h4⟩ := Radix.available_orders_seven p h
  refine ⟨h4, ?_, h2, h3, h6⟩
  rintro ⟨A, hA⟩
  have hp2 : 2 < p := by omega
  have hroot : ∃ A : ZMod p, A ^ 2 + 1 = 0 := ⟨A, by rw [hA]; ring⟩
  have hmod : p % 4 = 1 := (Radix.root_Phi4_iff p hp2).mp hroot
  have hdvd : p % 12 % 4 = p % 4 := Nat.mod_mod_of_dvd p (by norm_num)
  rw [h] at hdvd
  norm_num at hdvd
  omega

/-! ## 3. The closed-form selector -/

section Selector

/-- (Corollary "Closed-form selector", the argmax with tie-break.)  For a nonempty set of
    usable orders, an effective order `ρ` and an alignment count `ν`, there is an order
    `rs` maximising `ρ` and, among the maximisers, minimising `ν`. -/
theorem exists_argmax_tiebreak (avail : Finset ℕ) (hne : avail.Nonempty)
    (ρ : ℕ → ℝ) (ν : ℕ → ℕ) :
    ∃ rs ∈ avail, (∀ r ∈ avail, ρ r ≤ ρ rs) ∧ ∀ r ∈ avail, ρ r = ρ rs → ν rs ≤ ν r := by
  classical
  obtain ⟨r₀, hr₀, hmax⟩ := Finset.exists_max_image avail ρ hne
  have hr₀M : r₀ ∈ avail.filter (fun r => ρ r = ρ r₀) := Finset.mem_filter.mpr ⟨hr₀, rfl⟩
  obtain ⟨rs, hrs, hmin⟩ :=
    Finset.exists_min_image (avail.filter (fun r => ρ r = ρ r₀)) ν ⟨r₀, hr₀M⟩
  rw [Finset.mem_filter] at hrs
  refine ⟨rs, hrs.1, fun r hr => ?_, fun r hr hρ => ?_⟩
  · rw [hrs.2]; exact hmax r hr
  · exact hmin r (Finset.mem_filter.mpr ⟨hr, hρ.trans hrs.2⟩)

/-- The maximum of a nonempty finite set of orders belongs to it and dominates it. -/
theorem selector_max'_mem (avail : Finset ℝ) (hne : avail.Nonempty) :
    avail.max' hne ∈ avail ∧ ∀ r ∈ avail, r ≤ avail.max' hne :=
  ⟨avail.max'_mem hne, fun r hr => Finset.le_max' avail r hr⟩

/-- (Corollary "Closed-form selector", the cost consequence.)  The graded cost is
    non-increasing in the order (`Unify.gcost_antitone`), so the largest usable order
    minimises it: `gcost D r⋆ d ≤ gcost D r d` for every usable `r`. -/
theorem selector_gcost {D d : ℝ} (hD : 0 < D) (hdom : d = 1 ∨ 2 ≤ d)
    (avail : Finset ℝ) (hne : avail.Nonempty) (hpos : ∀ r ∈ avail, 0 < r) :
    ∀ r ∈ avail, Unify.gcost D (avail.max' hne) d ≤ Unify.gcost D r d := by
  intro r hr
  exact Unify.gcost_antitone hD hdom (Set.mem_Ioi.mpr (hpos r hr))
    (Set.mem_Ioi.mpr (hpos _ (avail.max'_mem hne))) (Finset.le_max' avail r hr)

/-- The maximum of the available set `{2, 3, 6}` of orders is `6`. -/
theorem max'_two_three_six (hne : ({2, 3, 6} : Finset ℝ).Nonempty) :
    ({2, 3, 6} : Finset ℝ).max' hne = 6 := by
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> norm_num

/-- (Corollary "Closed-form selector", the instance `p ≡ 7 (mod 12)`.)  Orders `2, 3, 6`
    are available and order four is not; over the available set `{2, 3, 6}` the graded
    cost is minimised at `r⋆ = 6`. -/
theorem selector_mod_twelve_seven (p : ℕ) [Fact p.Prime] (h : p % 12 = 7)
    {D d : ℝ} (hD : 0 < D) (hdom : d = 1 ∨ 2 ≤ d) :
    (Radix.HasOrder p 2 ∧ Radix.HasOrder p 3 ∧ Radix.HasOrder p 6 ∧
      ¬ Radix.HasOrder p 4) ∧
      ∀ r ∈ ({2, 3, 6} : Finset ℝ), Unify.gcost D 6 d ≤ Unify.gcost D r d := by
  refine ⟨Radix.available_orders_seven p h, ?_⟩
  have hne : ({2, 3, 6} : Finset ℝ).Nonempty := ⟨6, by simp⟩
  have hpos : ∀ r ∈ ({2, 3, 6} : Finset ℝ), 0 < r := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num
  have hsel := selector_gcost hD hdom ({2, 3, 6} : Finset ℝ) hne hpos
  rwa [max'_two_three_six hne] at hsel

end Selector

/-! ## 4. The effective orders quoted by the selector -/

/-- On the hexagon, a region stable under the sixth turn, the effective order is `ρ = 6`. -/
theorem rho_hex (B : ℕ) : PSCount.rho 6 ((hex (B : ℤ)).card) ((hex (B : ℤ)).card) = 6 := by
  refine PSCount.rho_stable ?_
  have hcard : 0 < (hex (B : ℤ)).card := by rw [card_hex]; omega
  exact_mod_cast hcard

/-- On the box closure the effective order satisfies `4 < ρ ≤ 6`.  The paper quotes
    `ρ = 4` there, which is the limit as the digit bound grows; the limit itself is not
    proved here, only the two-sided bound at every `B`. -/
theorem rho_closure_bounds (B : ℕ) :
    4 < PSCount.rho 6 ((box (B : ℤ)).card) ((DigitLattice.closure (B : ℤ)).card) ∧
      PSCount.rho 6 ((box (B : ℤ)).card) ((DigitLattice.closure (B : ℤ)).card) ≤ 6 :=
  ⟨PSCount.rho_box_closure_gt_four B, PSCount.rho_box_closure_le B⟩

end Coverage
