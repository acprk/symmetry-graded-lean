/-
  Repair.lean

  Formal verification (Lean 4 + Mathlib) of

    Corollary "Removing the obstruction"
    (Appendix "The obstruction at r = 2 and its repair")

  of "Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping".
  Over a field `K`, with the fixed divisor `g` (squarefree, `g ∣ Q`, `g ∣ Γ`,
  `gcd(g, Γ/g) = 1`), write `Q = g·Q₁`, `Γ = g·Γ₁`.  With no unproved placeholders:

  * `cong_iff`                   (i)  `g^d H ≡ Q (mod Γ)  ⟺  g^{d−1} H ≡ Q₁ (mod Γ₁)`
  * `isCoprime_of_squarefree`    `Γ` squarefree, `Γ = g Γ₁` ⟹ `gcd(g, Γ₁) = 1`
  * `exists_inv_mod`, `pow_inv_mod`, `reduced_coset`, `reduced_coset_modByMonic`
                                 (ii) `g` is invertible modulo `Γ₁`; hence
                                      `H ≡ Q₁ · g^{−(d−1)} (mod Γ₁)`  (the reduced coset)
  * `eval_ne_zero_of_isCoprime`  `gcd(g, Γ₁) = 1`, `g(a) = 0` ⟹ `Γ₁(a) ≠ 0`
  * `consistency`, `consistency_iff`
                                 (iii) for a simple root `a` of `g`, the coset member
                                      `F = Q + cΓ` has `a` as a root of multiplicity `≥ 2`
                                      iff `c = −Q₁(a)/Γ₁(a)`
  * `orbProd_mul`, `orbProd_of_fixed`, `norm_form_of_reduced`
                                 `Orb_d(g·C_H) = g^d · Orb_d(C_H)`; a norm form `H` in the
                                 reduced coset lifts to the norm form `F = g^d H = Orb_d(g C_H)`
  * `pow_prod_dvd_of_forall_pow_dvd`, `g_pow_dvd_normForm`
                                 conversely every norm form in the coset is divisible by `g^d`
  * `natDegree_C_eq`, `le_mul_ceil`, `padded_degree`
                                 (iv) `deg C = B + ⌈(n − B)/d⌉`, with `⌈m/d⌉ = (m + d − 1)/d`
  * `natDegree_Γ₁`, `B_le_n`, `padded_degree'`
                                 (round 5) `deg Γ₁ = n − B` derived from `Γ = gΓ₁`, `deg Γ = n`,
                                 `deg g = B`; the padded-degree statement without that hypothesis
-/
import Mathlib
import SymmetryGraded.Doubling
import SymmetryGraded.Obstruction

namespace Repair

open Polynomial

section Coset
variable {K : Type*} [Field K]

/-! ## (i) Cancelling the fixed divisor from the congruence -/

/-- (Corollary "Removing the obstruction", (i).)  With `Q = g Q₁`, `Γ = g Γ₁`, `g ≠ 0`:
    `g^d H ≡ Q (mod Γ)  ⟺  g^{d−1} H ≡ Q₁ (mod Γ₁)`. -/
theorem cong_iff {g Q Γ H Q₁ Γ₁ : K[X]} (hQ : Q = g * Q₁) (hΓ : Γ = g * Γ₁) (hg0 : g ≠ 0)
    {d : ℕ} (hd : 1 ≤ d) : Γ ∣ g ^ d * H - Q ↔ Γ₁ ∣ g ^ (d - 1) * H - Q₁ := by
  have h : g ^ d * H - Q = g * (g ^ (d - 1) * H - Q₁) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [hQ, Nat.add_sub_cancel, pow_succ]; ring
  rw [h, hΓ]
  exact mul_dvd_mul_iff_left hg0

/-- `Γ` squarefree and `Γ = g Γ₁` give `gcd(g, Γ₁) = 1`. -/
theorem isCoprime_of_squarefree {g Γ Γ₁ : K[X]} (hsq : Squarefree Γ) (hΓ : Γ = g * Γ₁) :
    IsCoprime g Γ₁ := by
  rw [hΓ, squarefree_mul_iff] at hsq
  exact hsq.1.isCoprime

/-! ## (ii) `g` is invertible modulo `Γ₁`: the reduced coset -/

/-- `gcd(g, Γ₁) = 1` ⟹ `g` has an inverse modulo `Γ₁`. -/
theorem exists_inv_mod {g Γ₁ : K[X]} (hcop : IsCoprime g Γ₁) :
    ∃ ginv : K[X], Γ₁ ∣ g * ginv - 1 := by
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u, -v, ?_⟩
  rw [← huv]; ring

/-- Powers of an inverse modulo `Γ₁` are inverses of the powers. -/
theorem pow_inv_mod {g Γ₁ ginv : K[X]} (h : Γ₁ ∣ g * ginv - 1) (m : ℕ) :
    Γ₁ ∣ g ^ m * ginv ^ m - 1 := by
  rw [← mul_pow]
  have := sub_dvd_pow_sub_pow (g * ginv) 1 m
  rw [one_pow] at this
  exact dvd_trans h this

/-- (Corollary "Removing the obstruction", (ii).)  With `g·ginv ≡ 1 (mod Γ₁)`:
    `g^{d−1} H ≡ Q₁ (mod Γ₁)  ⟺  H ≡ Q₁ · ginv^{d−1} (mod Γ₁)`, i.e. the reduced coset
    is `H ≡ H₀ := Q₁ g^{−(d−1)} (mod Γ₁)`. -/
theorem reduced_coset {g Γ₁ ginv H Q₁ : K[X]} (hinv : Γ₁ ∣ g * ginv - 1) (m : ℕ) :
    Γ₁ ∣ g ^ m * H - Q₁ ↔ Γ₁ ∣ H - Q₁ * ginv ^ m := by
  have hm := pow_inv_mod hinv m
  constructor
  · intro h
    have := (h.mul_left (ginv ^ m)).sub (hm.mul_left H)
    convert this using 1; ring
  · intro h
    have := (h.mul_left (g ^ m)).add (hm.mul_left Q₁)
    convert this using 1; ring

/-- Two polynomials congruent modulo a monic `Γ₁` have the same remainder `%ₘ Γ₁`. -/
theorem modByMonic_eq_of_dvd_sub {Γ₁ a b : K[X]} (hmo : Γ₁.Monic) (h : Γ₁ ∣ a - b) :
    a %ₘ Γ₁ = b %ₘ Γ₁ := by
  have hdiff : Γ₁ ∣ a %ₘ Γ₁ - b %ₘ Γ₁ := by
    rw [modByMonic_eq_sub_mul_div a Γ₁, modByMonic_eq_sub_mul_div b Γ₁]
    have := (h.sub (dvd_mul_right Γ₁ (a /ₘ Γ₁))).add (dvd_mul_right Γ₁ (b /ₘ Γ₁))
    convert this using 1; ring
  have hlt : (a %ₘ Γ₁ - b %ₘ Γ₁).degree < Γ₁.degree :=
    lt_of_le_of_lt (degree_sub_le _ _)
      (max_lt (degree_modByMonic_lt _ hmo) (degree_modByMonic_lt _ hmo))
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hdiff hlt)

/-- The reduced coset in remainder form: for monic `Γ₁`,
    `g^{d−1} H ≡ Q₁ (mod Γ₁)` ⟹ `H %ₘ Γ₁ = (Q₁ · ginv^{d−1}) %ₘ Γ₁`. -/
theorem reduced_coset_modByMonic {g Γ₁ ginv H Q₁ : K[X]} (hmo : Γ₁.Monic)
    (hinv : Γ₁ ∣ g * ginv - 1) (m : ℕ) (h : Γ₁ ∣ g ^ m * H - Q₁) :
    H %ₘ Γ₁ = (Q₁ * ginv ^ m) %ₘ Γ₁ :=
  modByMonic_eq_of_dvd_sub hmo ((reduced_coset hinv m).mp h)

/-! ## (iii) The explicit consistency condition at a simple root of `g` -/

/-- `gcd(g, Γ₁) = 1` and `g(a) = 0` force `Γ₁(a) ≠ 0`. -/
theorem eval_ne_zero_of_isCoprime {g Γ₁ : K[X]} (hcop : IsCoprime g Γ₁) {a : K}
    (hga : g.eval a = 0) : Γ₁.eval a ≠ 0 := by
  intro h0
  obtain ⟨u, v, huv⟩ := hcop
  have := congrArg (Polynomial.eval a) huv
  rw [eval_add, eval_mul, eval_mul, hga, h0, eval_one] at this
  simp at this

/-- The coset member factors through the fixed divisor: `Q + cΓ = g (Q₁ + c Γ₁)`. -/
theorem coset_factor {g Q Γ Q₁ Γ₁ : K[X]} (hQ : Q = g * Q₁) (hΓ : Γ = g * Γ₁) (c : K) :
    Q + C c * Γ = g * (Q₁ + C c * Γ₁) := by
  rw [hQ, hΓ]; ring

/-- (Corollary "Removing the obstruction", (iii): the consistency condition.)
    Let `a` be a simple root of `g` (`rootMultiplicity a g = 1`) with `Γ₁(a) ≠ 0`.
    If the coset member `F = Q + cΓ` has `a` as a root of multiplicity `≥ 2`, then
    `c = −Q₁(a)/Γ₁(a)`. -/
theorem consistency {g Q Γ Q₁ Γ₁ F : K[X]} (hQ : Q = g * Q₁) (hΓ : Γ = g * Γ₁)
    {a : K} (hsimple : g.rootMultiplicity a = 1) (hΓ₁a : Γ₁.eval a ≠ 0) {c : K}
    (hF : F = Q + C c * Γ) (hmult : 2 ≤ F.rootMultiplicity a) :
    c = -(Q₁.eval a) / Γ₁.eval a := by
  set R := Q₁ + C c * Γ₁ with hR
  have hFR : F = g * R := by rw [hF, coset_factor hQ hΓ]
  have hF0 : F ≠ 0 := by
    intro h; rw [h, rootMultiplicity_zero] at hmult; omega
  have hgR : g * R ≠ 0 := hFR ▸ hF0
  have hRroot : R.IsRoot a := by
    have h := rootMultiplicity_mul (x := a) hgR
    rw [← hFR, hsimple] at h
    have hpos : 0 < R.rootMultiplicity a := by omega
    exact (rootMultiplicity_pos (right_ne_zero_of_mul hgR)).mp hpos
  have heval : Q₁.eval a + c * Γ₁.eval a = 0 := by
    have := hRroot
    rw [IsRoot.def, hR, eval_add, eval_mul, eval_C] at this
    exact this
  rw [eq_div_iff hΓ₁a]; linear_combination heval

/-- Conversely, `c = −Q₁(a)/Γ₁(a)` makes `a` a root of `F = Q + cΓ` of multiplicity `≥ 2`
    (only `g(a) = 0` is needed for this direction). -/
theorem sq_dvd_of_consistency {g Q Γ Q₁ Γ₁ F : K[X]} (hQ : Q = g * Q₁) (hΓ : Γ = g * Γ₁)
    {a : K} (hga : g.eval a = 0) (hΓ₁a : Γ₁.eval a ≠ 0) {c : K}
    (hF : F = Q + C c * Γ) (hc : c = -(Q₁.eval a) / Γ₁.eval a) :
    (X - C a) ^ 2 ∣ F := by
  rw [hF, coset_factor hQ hΓ, pow_two]
  apply mul_dvd_mul
  · rw [dvd_iff_isRoot]; exact hga
  · rw [dvd_iff_isRoot, IsRoot.def, eval_add, eval_mul, eval_C, hc]
    field_simp; ring

/-- The consistency condition as an equivalence: for a simple root `a` of `g` with
    `Γ₁(a) ≠ 0`, the coset member `F = Q + cΓ` has `(X − a)² ∣ F` iff `c = −Q₁(a)/Γ₁(a)`. -/
theorem consistency_iff {g Q Γ Q₁ Γ₁ F : K[X]} (hQ : Q = g * Q₁) (hΓ : Γ = g * Γ₁)
    {a : K} (hsimple : g.rootMultiplicity a = 1) (hΓ₁a : Γ₁.eval a ≠ 0) {c : K}
    (hF : F = Q + C c * Γ) (hF0 : F ≠ 0) :
    (X - C a) ^ 2 ∣ F ↔ c = -(Q₁.eval a) / Γ₁.eval a := by
  constructor
  · intro h
    exact consistency hQ hΓ hsimple hΓ₁a hF ((le_rootMultiplicity_iff hF0).mpr h)
  · intro hc
    have hga : g.eval a = 0 := by
      have hpos : 0 < g.rootMultiplicity a := by omega
      have hg0 : g ≠ 0 := by rintro rfl; simp at hsimple
      exact (rootMultiplicity_pos hg0).mp hpos
    exact sq_dvd_of_consistency hQ hΓ hga hΓ₁a hF hc

end Coset

/-! ## Norm forms: lifting from the reduced coset and the converse -/
section NormForm
variable {K : Type*} [Field K]

/-- Orbit products are multiplicative. -/
theorem orbProd_mul (π : K[X] →+* K[X]) (d : ℕ) (a b : K[X]) :
    Galois.orbProd π d (a * b) = Galois.orbProd π d a * Galois.orbProd π d b := by
  unfold Galois.orbProd
  simp [map_mul, Finset.prod_mul_distrib]

/-- A `π`-fixed polynomial `g` (base-field coefficients) has `Orb_d(g) = g^d`. -/
theorem orbProd_of_fixed (π : K[X] →+* K[X]) {g : K[X]} (hg : π g = g) (d : ℕ) :
    Galois.orbProd π d g = g ^ d := by
  unfold Galois.orbProd
  rw [Finset.prod_eq_pow_card (b := g), Finset.card_range]
  intro i _
  rw [RingHom.coe_pow]; exact Function.iterate_fixed hg i

/-- (Corollary "Removing the obstruction", lifting.)  If `H = Orb_d(C_H)` is a norm form
    in the reduced coset, then `C := g·C_H` has `Orb_d(C) = g^d H`, because `g` is fixed by
    `π`. -/
theorem norm_form_of_reduced (π : K[X] →+* K[X]) {g CH H : K[X]} (hg : π g = g) {d : ℕ}
    (hH : Galois.orbProd π d CH = H) : Galois.orbProd π d (g * CH) = g ^ d * H := by
  rw [orbProd_mul, orbProd_of_fixed π hg, hH]

/-- If `g = ∏_{i∈t} (X − s i)` with pairwise distinct `s i`, and `(X − s i)^d ∣ F` for
    every `i`, then `g^d ∣ F`. -/
theorem pow_prod_dvd_of_forall_pow_dvd {ι : Type*} (t : Finset ι) (s : ι → K)
    (hdist : ∀ i ∈ t, ∀ j ∈ t, s i = s j → i = j) (d : ℕ) {F : K[X]}
    (hmult : ∀ i ∈ t, (X - C (s i)) ^ d ∣ F) :
    (∏ i ∈ t, (X - C (s i))) ^ d ∣ F := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply IsCoprime.pow
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    exact fun h => hij (hdist i hi j hj h)
  · exact hmult

/-- (Corollary "Removing the obstruction", forward direction.)  Every norm form
    `F = Orb_d(C)` (with `π^d = id`, `π` fixing the linear factors of `g`) that vanishes
    on the pairwise distinct roots `s i` of `g = ∏ (X − s i)` is divisible by `g^d`. -/
theorem g_pow_dvd_normForm (π : K[X] →+* K[X]) {ι : Type*} (t : Finset ι) (s : ι → K)
    (hdist : ∀ i ∈ t, ∀ j ∈ t, s i = s j → i = j)
    (hπ : ∀ i ∈ t, π (X - C (s i)) = X - C (s i)) {d : ℕ} (hd : π ^ d = 1)
    {Cp F : K[X]} (hF : F = Galois.orbProd π d Cp) (hF0 : F ≠ 0)
    (hroot : ∀ i ∈ t, F.eval (s i) = 0) :
    (∏ i ∈ t, (X - C (s i))) ^ d ∣ F := by
  apply pow_prod_dvd_of_forall_pow_dvd t s hdist d
  intro i hi
  rw [← le_rootMultiplicity_iff hF0]
  exact Obstruction.rootMultiplicity_orbProd_ge π (hπ i hi) hd hF hF0 (hroot i hi)

end NormForm

/-! ## (iv) Degree bookkeeping -/
section Degree
variable {K : Type*} [Field K]

/-- `m ≤ d·⌈m/d⌉` with `⌈m/d⌉ = (m + d − 1)/d` (`d ≥ 1`): padding to a multiple of `d`. -/
theorem le_mul_ceil (m d : ℕ) (hd : 1 ≤ d) : m ≤ d * ((m + d - 1) / d) := by
  have h1 := Nat.div_add_mod (m + d - 1) d
  have h2 := Nat.mod_lt (m + d - 1) (by omega : d > 0)
  omega

/-- The padded degree `d·⌈m/d⌉` is less than `m + d`. -/
theorem mul_ceil_lt (m d : ℕ) (hd : 1 ≤ d) : d * ((m + d - 1) / d) < m + d := by
  have h1 := Nat.div_add_mod (m + d - 1) d
  omega

/-- (Corollary "Removing the obstruction", (iv).)  With `deg g = B` and
    `deg C_H = ⌈(n − B)/d⌉`, the lifted polynomial `C = g·C_H` has
    `deg C = B + ⌈(n − B)/d⌉`. -/
theorem natDegree_C_eq {g CH : K[X]} (hg0 : g ≠ 0) (hCH0 : CH ≠ 0) {B n d : ℕ}
    (hgB : g.natDegree = B) (hCH : CH.natDegree = (n - B + d - 1) / d) :
    (g * CH).natDegree = B + (n - B + d - 1) / d := by
  rw [natDegree_mul hg0 hCH0, hgB, hCH]

/-- The reduced coset is padded to `deg H = d·⌈(n − B)/d⌉ ≥ n − B = deg Γ₁`, and then
    `deg F = deg (g^d H) = dB + d⌈(n − B)/d⌉ = d·deg C`. -/
theorem padded_degree {g H : K[X]} (hg0 : g ≠ 0) (hH0 : H ≠ 0) {B n d : ℕ} (hd : 1 ≤ d)
    (hgB : g.natDegree = B) (hH : H.natDegree = d * ((n - B + d - 1) / d)) :
    n - B ≤ H.natDegree ∧
      (g ^ d * H).natDegree = d * (B + (n - B + d - 1) / d) := by
  refine ⟨hH ▸ le_mul_ceil _ _ hd, ?_⟩
  rw [natDegree_mul (pow_ne_zero _ hg0) hH0, natDegree_pow, hgB, hH]; ring

/-- (Round 5.)  The identity `deg Γ₁ = n − B` is *derived* from `Γ = g·Γ₁`, `deg Γ = n`,
    `deg g = B` (`g, Γ₁ ≠ 0`), by `natDegree_mul`. -/
theorem natDegree_Γ₁ {g Γ Γ₁ : K[X]} (hΓ : Γ = g * Γ₁) (hg0 : g ≠ 0) (hΓ₁0 : Γ₁ ≠ 0)
    {B n : ℕ} (hgB : g.natDegree = B) (hΓn : Γ.natDegree = n) : Γ₁.natDegree = n - B := by
  rw [hΓ, natDegree_mul hg0 hΓ₁0, hgB] at hΓn
  omega

/-- `B ≤ n` is forced by `Γ = g·Γ₁` (`deg g = B`, `deg Γ = n`). -/
theorem B_le_n {g Γ Γ₁ : K[X]} (hΓ : Γ = g * Γ₁) (hg0 : g ≠ 0) (hΓ₁0 : Γ₁ ≠ 0)
    {B n : ℕ} (hgB : g.natDegree = B) (hΓn : Γ.natDegree = n) : B ≤ n := by
  rw [hΓ, natDegree_mul hg0 hΓ₁0, hgB] at hΓn
  omega

/-- (Corollary "Removing the obstruction", (iv), round-5 form without the hypothesis
    `deg Γ₁ = n − B`.)  From `Γ = g·Γ₁`, `deg Γ = n`, `deg g = B`, and the padded reduced
    coset `deg H = d·⌈(n − B)/d⌉`:  `deg Γ₁ ≤ deg H`,  `deg (g^d H) = d(B + ⌈(n − B)/d⌉)`,
    and `deg (g^d H) = d · deg (g·C_H)` whenever `deg H = d · deg C_H`. -/
theorem padded_degree' {g Γ Γ₁ H CH : K[X]} (hΓ : Γ = g * Γ₁) (hg0 : g ≠ 0) (hΓ₁0 : Γ₁ ≠ 0)
    (hH0 : H ≠ 0) (hCH0 : CH ≠ 0) {B n d : ℕ} (hd : 1 ≤ d)
    (hgB : g.natDegree = B) (hΓn : Γ.natDegree = n)
    (hH : H.natDegree = d * ((n - B + d - 1) / d)) (hHC : H.natDegree = d * CH.natDegree) :
    Γ₁.natDegree ≤ H.natDegree ∧
      (g ^ d * H).natDegree = d * (B + (n - B + d - 1) / d) ∧
      (g ^ d * H).natDegree = d * (g * CH).natDegree := by
  have hΓ₁ := natDegree_Γ₁ hΓ hg0 hΓ₁0 hgB hΓn
  obtain ⟨h1, h2⟩ := padded_degree hg0 hH0 hd hgB hH
  refine ⟨hΓ₁ ▸ h1, h2, ?_⟩
  rw [natDegree_mul (pow_ne_zero _ hg0) hH0, natDegree_pow, natDegree_mul hg0 hCH0, hHC]
  ring

end Degree

end Repair
