# Machine-Checked Lean 4 Formalization
### *Symmetry-Graded Digit Extraction for Faster BGV/BFV Bootstrapping*

This directory contains a **Lean 4 + Mathlib** formalization of the algebraic core
of the paper, in the style of the author's earlier formalization of the order-four
filter (which is included here as the `r = 4` instance).  Every result below is
proved with **zero `sorry`, zero `admit`, zero user axioms**; `lake build` completes
with no errors, and `#print axioms` on every main theorem reports only the three
standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`.

## Build / reproduce

```bash
# Lean toolchain is pinned in lean-toolchain (leanprover/lean4:v4.31.0-rc2),
# Mathlib is pinned in lake-manifest.json
lake exe cache get          # fetch prebuilt Mathlib oleans
lake build                  # builds every module listed in SymmetryGraded.lean
grep -rn "sorry\|admit\|axiom " SymmetryGraded/   # prints nothing
```

A green build is the certificate: it re-checks every proof from the Mathlib
kernel up.

## Files

| file | contents |
|---|---|
| `SymmetryGraded/OrderFour.lean` | (inherited, `r = 4`) order-four element, support stability, the character filter, the **Order-Four Character Filter** theorem, factored form |
| `SymmetryGraded/Character.lean` | (inherited) **Isotypic decomposition** and **Monomial Support Constraint** at the coefficient level |
| `SymmetryGraded/Tightness.lean` | (inherited, `r = 4`) tight term count, box injectivity, asymptotic cost ratio |
| `SymmetryGraded/OrderR.lean` | **unified order-`r` filter**: `Aᵏ − A⁻¹ = 0 ↔ k ≡ r−1`, covariance ⟹ support `{1} ∪ {k ≡ r−1 (mod r)}`, `c₁ = 1/(1−A²)`, **factored form** `P = c₁X + X^{r−1}Q(X^r)` with a genuine polynomial `Q`, isotypic support, the `r = 4` instance check |
| `SymmetryGraded/OrderSix.lean` | the **order-six instance**: `A² = A−1 ⟹ A³ = −1, A⁶ = 1`, hexagon norm invariance, `M₆`/`M₄` matrix orders, the **Order-six character filter** theorem (coefficient and polynomial form), factored form, oddness, term count, the `r = 6` instance check |
| `SymmetryGraded/Lattice.lean` | the digit lattice: intertwining `φ_A ∘ M_A = A·φ_A`, **injectivity criterion** (kernel form and the sufficient condition `2B < |A|`, `2B(|A|+1) < p`), box/hexagon/closure regions and their stability, **cardinalities** `(2B+1)²`, `3B²+3B+1`, `6B²+6B+1` symbolically in `B` |
| `SymmetryGraded/Crystallographic.lean` | **Crystallographic restriction in rank two**: `det M = ±1`, `|tr M| ≤ 2` (fully proved, no extra hypothesis), the case analysis, `orderOf M ∈ {1,2,3,4,6}`, exact orders `3, 4, 6` of the companion matrices |
| `SymmetryGraded/Doubling.lean` | the Galois axis: orbit products, **doubling lemma**, Frobenius invariance of the norm, evaluation at fixed points, **correctness** of the coset construction and of ComposedEval |
| `SymmetryGraded/Obstruction.lean` | **obstruction at `r = 2`**: the fixed divisor `g ∣ Q`, and the norm-criterion consequence that an orbit product of length `d ≥ 2` has no simple root |
| `SymmetryGraded/Cost.lean` | **cost monotonicity** (strict antitonicity in `r`), the quantified composed speedup, alignment counts `ν(r)` |
| `SymmetryGraded/Noise.lean` | **noise and level model** of the composed digit extraction (Appendix C.5): abstract ciphertexts `⟨noise, level⟩`, the five primitives (13)–(17) as definitions, straight-line programs for ComposedEval / the literal Algorithm 2 / the baseline, **exact level counts**, the paper's `L_comp`, `L_base` and their relation to the program levels, the Case IV instance, phase noise bounds, key-switch counts, plaintext-level correctness of Algorithm 3; (round 5) the **phase table** of Appendix C.5 (`phaseTable`, `phase_table`, `L_comp_eq_phase_sum`, `composedEval_ks_eq_phase_sum`) |
| `SymmetryGraded/Example.lean` | the paper's worked examples over `ZMod 31`, verified by `decide`: hexagon `p=31, A=6, B=2`; composed evaluation `d=3`; the `r=2` obstruction `A=5, B=2`; (round 4) the root `α ∈ F_{31³} = AdjoinRoot F` with `α³¹, α⁹⁶¹` computed explicitly and **`F = Orb₃(Y − α)`** for the Frobenius `x ↦ x³¹` |
| `SymmetryGraded/Commute.lean` | (round 3) **scalar and Galois actions commute** (Appendix B.2): `σ_A` as `compRingHom (C A * X)` with coefficientwise action `cₖ ↦ Aᵏcₖ`, `Frob ∘ σ_A = σ_A ∘ Frob`, descent to `R[X]/(G_S)` for both operators, the direct-product claim, the **bigraded decomposition** by the idempotents `π_j` (eigen-relation, partition of unity, orthogonality, `Frob`-stability) |
| `SymmetryGraded/Interpolation.lean` | (round 3) **functional equation from interpolation**: existence and uniqueness of the interpolant on an injective region (`Lagrange.interpolate`), `P(AX) = A⁻¹(P(X) − X)` from stability + injectivity + uniqueness, the order-`r` support/factored theorems **without** the functional-equation hypothesis, hexagon (`r = 6`) and box (`r = 4`) instances |
| `SymmetryGraded/Radix.lean` | (round 3) **existence of radices**: order-`r` element in `(ZMod p)ˣ` iff `r ∣ p − 1`, roots of `Φ₃, Φ₄, Φ₆` iff `p ≡ 1 (mod 3)`, `(mod 4)`, `(mod 3)`, the four residue classes mod 12 (Proposition "Available orders by the residue class of p") |
| `SymmetryGraded/NormCriterion.lean` | (round 3/4) **norm criterion** over `F_{p^d} = GaloisField p d` with its Frobenius: irreducible `F` of degree `d` is `Orb_d(Y − α)`; products of degree-`d` irreducibles are norm forms; conversely a squarefree norm form has all its (rooted-in-`L`) irreducible factors of degree exactly `d`; (round 4) **sufficiency for irreducible factors of degree `kd`**: `h = Orb_d(C)` with `C = minpoly_{F_{p^d}} β` of degree `k`, via the tower `F_p ⊂ F_{p^d} ⊂ F_{p^{kd}}`; (round 5) the **general multiplicity criterion**: a monic irreducible `h` of degree `m` splits over `F_{p^d}` into `t = gcd(m,d)` Frobenius conjugates of degree `m/t` (`period_eq_gcd_galoisField`), `h^μ` is a norm form iff `d ∣ m μ` (`pow_eq_orbProd_galoisField_iff`), necessity for non-squarefree `F` by multiplicity counting, and the full criterion `∏ hᵢ^{μᵢ}` is a norm form ⟺ `∀ i, d ∣ mᵢ μᵢ` (`normForm_iff_galoisField`) |
| `SymmetryGraded/Repair.lean` | (round 3) **removing the obstruction**: `g^d H ≡ Q (mod Γ) ↔ g^{d−1} H ≡ Q₁ (mod Γ₁)`, `g` invertible mod `Γ₁`, the reduced coset `H ≡ Q₁ g^{−(d−1)}`, the consistency condition `c = −Q₁(a)/Γ₁(a)` as an iff, `g^d ∣ F` for norm forms, the lift `Orb_d(g C_H) = g^d H`, degree bookkeeping `deg C = B + ⌈(n−B)/d⌉`; (round 5) `deg Γ₁ = n − B` derived from `Γ = gΓ₁` (`natDegree_Γ₁`, `padded_degree'`) |
| `SymmetryGraded/RadixCeiling.lean` | (round 4) **Corollary "Admissible radix orders"**: an intertwining `φ_A ∘ M = A·φ_A` with `M ∈ M₂(ℤ)`, `M^s = 1` forces `A^s = 1`, `ord A ∣ ord M`, hence `ord A ∈ {1,2,3,4,6}`; converse for the companion matrices `M_A`, `τ ∈ {−1,0,1}`: `ord A = ord M_A = 3, 4, 6` |
| `SymmetryGraded/TermCount.lean` | (round 4) **Theorem "The term count is generically attained"**: the coefficient functional `λ ↦ [X^k] P_λ` on interpolation data is nonzero for every `k < |S|`, its kernel is a hyperplane (`dim = |S| − 1`), covector formula `([X^k] L_s)_s` |
| `SymmetryGraded/PSCount.lean` | (round 4) **Paterson–Stockmeyer counts**: `PS(m) = (k−2)+⌈log₂g⌉+(g−1) ≤ 2√m + log₂(√m+2) + 1`, the factored count `C_r = chain + PS(deg Q) + 1` (`4` at `r = 6`), the **effective order** `ρ = r|T|/|Ω|` with `2√(deg Q) ≤ 2√(|T|/ρ)`, the box-closure value `ρ = 4 + 2/(6B²+6B+1)`, and the phase sum of Prop. "Cost of ComposedEval" as an identity tied to the `Noise.lean` program count |
| `SymmetryGraded/LatticeMin.lean` | (round 4) **Injectivity as a lattice minimum**, second equivalence: `T − T = 2T` for the box and the hexagon, `φ_A` injective on `T_B` ⟺ `N_T(w) > 2B` on `L_A ∖ {0}`; the Gaussian bound (`A² ≡ −1`: `p ∣ u²+v²`, `‖w‖∞ ≥ √(p/2)`, so `8B² < p` suffices, `c₄ = 8`) and the Eisenstein bound (`A² ≡ A−1`: `p ∣ u²+uv+v²`, `u²+uv+v² ≤ N(w)²`, `N(w) ≥ √p`, so `4B² < p` suffices, `c₆ = 4`); (round 5) the **upper bounds**: a kernel vector of norm exactly `p` (Fermat for `ℤ[i]`; a self-contained Thue/pigeonhole argument for `ℤ[ω]`), hence `√(p/2) ≤ λ₁^∞ ≤ √p`, `√p ≤ λ₁^hex ≤ (2/√3)√p`, and the necessary conditions `4B² < p` (box), `3B² < p` (hexagon): `4 ≤ c₄ ≤ 8`, `3 ≤ c₆ ≤ 4` |
| `SymmetryGraded/Unify.lean` | (round 3) **prior evaluators as corners**: the three-branch `(r,d)`-graded cost `gcost`, the five corner identities, interior branch `= Cost.cost`, **cost monotonicity** with the saturated-branch tie and the downward jump `2 + log₂ d > log₂ d` at `D/r = d` |

## Modelling conventions

Everything is formalized at the **coefficient / polynomial level** over an abstract
field `K` (or commutative ring `R`) — `ZMod p` is an instance.  The substitution
operator `σ_A : X^k ↦ A^k X^k` is modelled by its action `cₖ ↦ Aᵏ·cₖ` on a
coefficient sequence `c : ℕ → K`, and — for the polynomial statements — by
`P.comp (C A * X)` on `Polynomial K`.  "`A` has exact order `r`" is expressed as
`A ^ r = 1` together with `∀ j, 0 < j → j < r → A ^ j ≠ 1` (equivalent to
`orderOf A = r`, see `OrderR.exact_order_of_orderOf`).  `Q(X^r)` is Mathlib's
`expand K r Q`.  The Frobenius is an arbitrary ring endomorphism `φ : R →+* R`
acting on polynomials coefficientwise via `Polynomial.mapRingHom φ`.  The digit
lattice is `ℤ × ℤ`, the encoding is `DigitLattice.phi A (η, λ) = η·A + λ`, the
companion action is `DigitLattice.rot τ (η, λ) = (τη + λ, −η)`.

## Interface: paper statement ↔ Lean name

### `OrderR.lean`  (namespace `OrderR`) — the unified order-`r` statements

Hypotheses throughout: `[Field K]`, `hAr : A ^ r = 1`, `hord : ∀ j, 0 < j → j < r → A ^ j ≠ 1`, and `hr : 3 ≤ r` where stated.

| paper statement | Lean name |
|---|---|
| `orderOf A = r ⟹` exact order hypotheses | `exact_order_of_orderOf` |
| `A⁻¹ = A^{r−1}` | `inv_eq_pow_pred` |
| `Aᵏ = A⁻¹ ⟺ k ≡ r−1 (mod r)` (exact order `r`) | `pow_eq_inv_iff`, `filter_factor_zero_iff` |
| `r ≥ 3 ⟹ A ≠ A⁻¹`, `1 − A² ≠ 0` | `A_sub_inv_ne_zero`, `one_sub_sq_ne_zero` |
| **Cor. (Support of the order-r filter)**, coefficient form: `cₖAᵏ = A⁻¹cₖ − A⁻¹[k=1]` ⟹ `cₖ = 0` unless `k = 1` or `k ≡ r−1`, and `c₁ = A⁻¹/(A⁻¹−A) = 1/(1−A²)` | `order_r_filter_coeff` |
| same, polynomial form: from `P(AX) = A⁻¹(P(X) − X)` | `order_r_filter`, `support_subset` |
| generic sparse factoring `P = c₁X + X^{r−1}Q(X^r)`, `deg Q ≤ (deg P − (r−1))/r` | `sparse_factor` |
| **Cor.**, factored form from the functional equation | `factored_form_poly` |
| **Lemma (Character grading is degree reduction)**: `σ_A P = A^s P` ⟹ `supp P ⊆ {k ≡ s (mod r)}` | `isotypic_support` |
| `A² = −1`, `2 ≠ 0` ⟹ exact order 4 | `order_four_exact` |
| the order-four equation `(Aᵏ+A)cₖ = A[k=1]` is the `r=4` case of the unified one | `order_four_fe_equiv` |
| the unified theorem at `r = 4` reproduces `OrderFour.order_four_filter_coeff` (`c₁ = 1/2`) | `order_four_agrees` |

### `OrderSix.lean`  (namespace `OrderSix`) — the order-six instance

Hypotheses: `A ^ 2 = A - 1`; over a field additionally `(2 : K) ≠ 0` and `(3 : K) ≠ 0` (in `ZMod p` this is `p ∉ {2, 3}`; the paper has `p ≡ 1 (mod 3)`, `p ≥ 7`).

| paper statement | Lean name |
|---|---|
| `A² = A−1 ⟹ A³ = −1`, `A⁶ = 1`, `A⁴ = −A`, `A⁵ = 1−A` | `pow_three_eq_neg_one`, `pow_six_eq_one`, `pow_four_eq_neg`, `pow_five_eq_one_sub` |
| `Aᵏ = A^{k mod 6}` | `pow_mod_six` |
| `A·(1−A) = 1`; `A⁻¹ = 1−A = A⁵` | `mul_one_sub`, `inv_eq_one_sub`, `inv_eq_pow_five` |
| **Lemma (Order-six stability)**, pointwise: `A(ηA+λ) = (η+λ)A − η` | `stability_pointwise` |
| hexagon norm `N = max{|η|,|λ|,|η+λ|}` and `N ∘ M_A = N` | `hexNorm`, `hexNorm_rot`, `hex_stable` |
| `M_A = [[1,1],[−1,0]]`: `M_A² = [[0,1],[−1,−1]]`, `M_A³ = −I`, `M_A⁶ = I`, `M_Aᵏ ≠ I` for `1 ≤ k ≤ 5`, `ord M_A = 6` | `M6`, `M6_sq`, `M6_pow_three`, `M6_pow_six`, `M6_pow_ne_one`, `orderOf_M6`, `M6_mulVec` |
| `τ = 0`: `M_A² = −I`, `M_A⁴ = I` | `M4`, `M4_pow_two`, `M4_pow_four` |
| the filter *passes* `k ≡ 5 (mod 6)`: `Aᵏ − A⁻¹ = 0` | `filter_factor_eq_zero` |
| the filter *kills* `k ≢ 5 (mod 6)`: `Aᵏ − A⁻¹ ≠ 0` | `filter_factor_ne_zero` |
| character filter as an iff | `filter_factor_zero_iff` |
| `k = 1`: `A − A⁻¹ ≠ 0` | `A_ne_inv`, `filter_factor_one_ne_zero` |
| **Thm (Order-six character filter)**, coefficient form: `cₖAᵏ = A⁻¹cₖ − A⁻¹[k=1]` ⟹ support `{1} ∪ {k ≡ 5 (mod 6)}`, `c₁ = A⁻¹/(A⁻¹−A) = 1/(1−A²)` | `order_six_filter_coeff` |
| **Thm**, polynomial form: from `P(AX) = A⁻¹(P(X) − X)` | `order_six_filter`, `support_subset` |
| factored form, coefficient statement | `factored_form` |
| factored form `P = c₁X + X⁵Q(X⁶)`, `deg Q ≤ (deg P − 5)/6`, with an explicit polynomial `Q` | `factored_form_poly` |
| **oddness**: even coefficients vanish; `P(−X) = −P(X)` | `coeff_even_eq_zero`, `odd_poly` |
| term count: exactly `t` exponents `k < 6t+1` with `k ≡ 5`; for `n ≡ 1 (mod 6)` the count is `(n−1)/6` | `card_v5`, `card_v5_mod` |
| **term count bound** `|T| ≤ (|S_A|−1)/6 + 1` | `support_card_le`, `term_count_bound` |
| `A² = A−1`, `2 ≠ 0 ≠ 3` ⟹ exact order 6 | `order_six_exact` |
| the unified theorem at `r = 6` reproduces `order_six_filter_coeff` | `order_six_agrees` |

### `Lattice.lean`  (namespace `DigitLattice`)

| paper statement | Lean name |
|---|---|
| encoding `φ_A(η,λ) = ηA + λ`; companion action `M_A(η,λ) = (τη+λ, −η)` | `phi`, `rot` |
| **intertwining** `φ_A ∘ M_A = A·φ_A` for `A² = τA − 1` (any commutative ring) | `phi_rot`, `phi_rot_iterate` |
| `M_A = [[τ,1],[−1,0]]` acts as `rot τ`; `det M_A = 1`, `tr M_A = τ`; `M_A` is a bijection of `ℤ²` | `MA`, `MA_mulVec`, `MA_det`, `MA_trace`, `rotInv`, `rot_bijective` |
| **Lemma (Injectivity as a lattice minimum)**: `φ_A` injective on finite `T` ⟺ `L_A ∩ (T − T) = {0}` | `injOn_iff_kernel` |
| **Lemma (Injectivity criterion)**, kernel form: `2B < |A|`, `2B(|A|+1) < p` ⟹ `L_A ∩ [−2B,2B]² = {0}` | `kernel_box_trivial` |
| same, injectivity on the box over `ℤ` / into `ZMod p` | `box_injective_int`, `box_injective_zmod` |
| box `[−B,B]²`, hexagon `T_B`, closure `Ω_B` (as `Finset (ℤ × ℤ)`) and membership | `box`, `hex`, `closure`, `mem_box`, `mem_hex`, `mem_closure`, `mem_hex_iff_hexNorm` |
| the sixth turn maps `T_B` onto itself; the quarter turn maps the box onto itself; the sixth turn maps `Ω_B` onto itself | `hex_rot_iff`, `box_rot_iff`, `closure_rot_iff` |
| the box is not stable under the sixth turn (`(B,B) ↦ (2B,−B)`) | `box_not_rot_stable` |
| **Lemma (order-six filter on the closed box)**: `Ω_B = ⋃_{i<3} M_Aⁱ[−B,B]²` | `closure_eq_union`, `mem_image_rot`, `mem_image_rot_rot` |
| `|[−B,B]²| = (2B+1)²` | `card_box` |
| `|T_B| = 3B² + 3B + 1` (symbolic in `B`) | `card_hex` (via `card_hex_fiber`, `sum_abs_Icc`) |
| `|Ω_B| = 6B² + 6B + 1` (symbolic, inclusion–exclusion) | `card_closure` |
| `|T_B| ≡ |Ω_B| ≡ 1 (mod 6)` | `card_hex_mod_six`, `card_closure_mod_six` |

### `Crystallographic.lean`  (namespace `Crystallographic`)

`M : Matrix (Fin 2) (Fin 2) ℤ`, `hr : 1 ≤ r`, `hM : M ^ r = 1`.

| paper statement | Lean name |
|---|---|
| Cayley–Hamilton `M² = (tr M)M − (det M)I` | `cayley_hamilton` |
| `Mⁿ⁺¹ = aₙ₊₁M − (d·aₙ)I`, `a` the Lucas sequence `aₙ₊₂ = t·aₙ₊₁ − d·aₙ` | `lucas`, `pow_succ_eq_lucas` |
| **Thm**: finite order ⟹ `det M = ±1` | `det_eq_one_or_neg_one` |
| growth of `aₙ` for `t ≥ 2, |d| ≤ 1` and for `t ≥ 1, d ≤ 0`; sign symmetry | `lucas_pos_of_two_le`, `lucas_pos_of_one_le_of_nonpos`, `lucas_neg`, `lucas_ne_zero_of_two_le_abs`, `lucas_ne_zero_of_det_neg` |
| `M^r = 1` ⟹ `M = ±I` or `a_r = 0` | `scalar_of_smul_sub`, `scalar_or_lucas_eq_zero`, `scalar_pow_eq_one`, `pm_one_or_lucas_eq_zero` |
| **Thm**: finite order ⟹ `|tr M| ≤ 2` (no extra hypothesis) | `abs_trace_le_two` |
| `(t,d) = (−1,1) ⟹ M³ = 1`; `(0,1) ⟹ M² = −1, M⁴ = 1`; `(1,1) ⟹ M³ = −1, M⁶ = 1`; `(0,−1) ⟹ M² = 1` | `pow_three_eq_one_of`, `pow_two_eq_neg_one_of`, `pow_four_eq_one_of`, `pow_three_eq_neg_one_of`, `pow_six_eq_one_of`, `pow_two_eq_one_of_det_neg` |
| `(±2,1) ⟹ (M ∓ I)² = 0`; unipotent of finite order ⟹ `M = ±I` | `unipotent_of`, `unipotent_of_neg`, `eq_one_of_trace_two`, `eq_neg_one_of_trace_neg_two` |
| **Thm (Crystallographic restriction)**, full case analysis | `classification` |
| `orderOf M ∈ {1,2,3,4,6}` | `orderOf_mem`, `no_order_five_or_ge_seven` |
| `det M = −1 ⟹ r = 2`; `tr = −1,0,1` with `det = 1` ⟹ order exactly `3,4,6` | `orderOf_eq_two_of_det_neg_one`, `orderOf_eq_three`, `orderOf_eq_four`, `orderOf_eq_six` |
| the companion matrices of `Φ₃, Φ₄, Φ₆` have orders `3, 4, 6` | `MA_orderOf_three`, `MA_orderOf_four`, `MA_orderOf_six` |

### `Doubling.lean`  (namespace `Galois`)

`φ : R →+* R` a ring endomorphism of a commutative ring (the Frobenius).

| paper statement | Lean name |
|---|---|
| `Orb_n(x) = ∏_{i<n} φⁱ(x)` | `orbProd`, `orbProd_zero`, `orbProd_one`, `orbProd_succ` |
| `Orb_{m+n}(x) = Orb_m(x)·φ^m(Orb_n(x))` (block splitting for general `d`) | `map_orbProd`, `orbProd_add` |
| **Lemma (Sub-orbit products from doubling)**: `N₀ = x`, `N_{j+1} = N_j·φ^{2^j}(N_j)` ⟹ `N_j = Orb_{2^j}(x)` | `doubling`, `doubling_schedule` |
| `φ^d = id ⟹ φ(Orb_d(x)) = Orb_d(x)` (the norm is Frobenius-fixed) | `orbProd_fixed`, `orbProd_fixed_pow` |
| `(mapRingHom φ)ⁱ = mapRingHom (φⁱ)` | `mapRingHom_pow` |
| `φ(y) = y ⟹ (φC)(y) = φ(C(y))` | `eval_map_of_fixed` |
| `(Orb_d C)(y) = Orb_d(C(y))` for Frobenius-fixed `y` | `eval_orbProd` |
| `c·F = Q + Γ·H`, `Γ(y) = 0` ⟹ `Q(y) = c·F(y)` | `eval_coset` |
| **Lemma (Correctness of the construction)**: `c·Orb_d(C) ≡ Q (mod Γ)` ⟹ `Q(y) = c·∏ φⁱ(C(y))` on roots of `Γ` | `construction_correct` |
| **Lemma (Correctness of ComposedEval)**: `P(x) = c₁x + x^{r−1}·c·∏_{i<d} φⁱ(C(x^r))` | `composed_correct` |

### `Obstruction.lean`  (namespace `Obstruction`)

| paper statement | Lean name |
|---|---|
| odd filter `P = X·Q(X²)`: `P(x) = x·Q(x²)`; `P(x) = 0, x ≠ 0 ⟹ Q(x²) = 0` | `eval_odd_filter`, `root_of_odd_filter` |
| **Thm (Obstruction)**, fixed divisor: distinct squares of nonzero roots ⟹ `∏(Y − (s i)²) ∣ Q` | `fixed_divisor` |
| the points `(ηA)²`, `1 ≤ η ≤ B`, are distinct in `ZMod p` for `2B < p`, `A ≠ 0` | `sq_injective_zmod` |
| **Thm (Obstruction)** on the box: `g = ∏_{η=1}^{B}(Y − (ηA)²) ∣ Q` | `fixed_divisor_box` |
| `(Y−a) ∣ C ⟹ (Y−a)^d ∣ Orb_d(C)` (`π` fixing `Y − a`) | `pow_dvd_orbProd` |
| `π^d = id`, `(Y−a) ∣ Orb_d(C) ⟹ (Y−a) ∣ C`, hence `(Y−a)^d ∣ Orb_d(C)` | `dvd_of_dvd_orbProd`, `pow_dvd_orbProd_of_root` |
| **norm criterion, `m_h = 1`**: every root of an orbit product of length `d` has multiplicity `≥ d`; for `d ≥ 2` no simple root | `rootMultiplicity_orbProd_ge`, `no_simple_root_of_orbProd` |
| **Thm (Obstruction)**, multiplicity part: a coset member `F = Q + ΓH` that is an orbit product (`d ≥ 2`) has every common root of `Q, Γ` with multiplicity `≥ 2` | `obstruction` |

### `Cost.lean`  (namespace `Cost`)

| paper statement | Lean name |
|---|---|
| `cost(D;r,d) = 2√(D/(rd)) + log₂(D/r)`; the `d = 1` branch `2√(D/r)` | `cost`, `sqrtCost` |
| **Prop. (Cost monotonicity)**: strictly decreasing in `r > 0` (`D, d > 0`) | `cost_lt_of_lt`, `cost_strictAntiOn`, `sqrtCost_strictAntiOn` |
| **Prop. (Composed cost, quantified)**: `2√D/cost = √(rd)/(1 + √(rd)log₂(D/r)/(2√D))`, `< √(rd)` for `D > r` | `speedup_eq`, `speedup_lt_sqrt` |
| **Prop. (Base-two alignment cost)**: `ν(2) = ν(3) = ν(4) = 0`, `ν(6) = 1`, `ν ≤ 1` | `chainLen`, `squarings`, `nu`, `nu_two`, `nu_three`, `nu_four`, `nu_six`, `nu_le_one` |

### `Example.lean`  (namespace `Example`, `F := ZMod 31`)

| paper claim | Lean name |
|---|---|
| `6² = 6 − 1`, `6⁻¹ = 26`, `2 ≠ 0 ≠ 3` in `F₃₁` | `A_sq`, `A_inv`, `two_ne_zero'`, `three_ne_zero'` |
| the 19 hexagon pairs (sound and complete); `φ_A` injective on them; `S_A = {0,1,2,4,5,6,7,10,11,12,19,20,21,24,25,26,27,29,30}` | `hexPairs`, `hexPairs_length`, `hexPairs_sound`, `hexPairs_complete`, `phi_injective_on_hex`, `support_eq` |
| `P = 23X + 29X⁵ + 12X¹¹ + 30X¹⁷` interpolates the low digit on all 19 pairs | `P`, `eval_P`, `P_interpolates` |
| functional equation at every support point; *polynomial* equation `P(6X) = 6⁻¹(P(X) − X)` | `fe_on_support`, `P_fe` |
| the Order-six theorem applied: support `{1} ∪ {k ≡ 5}`, `c₁ = (1−6²)⁻¹ = 23` | `P_filter`, `c1_eq` |
| `P = 23X + X⁵Q(X⁶)`, `Q = 29 + 12Y + 30Y²` | `Qhex`, `P_factored` |
| folded support `{1,2,4}`; `Γ = (Y−1)(Y−2)(Y−4) = Y³+24Y²+14Y+23`; `Γ` vanishes on it | `folded_support`, `Γ`, `Γ_eq`, `Γ_vanishes` |
| `F = Γ + 16Q = Y³+8Y²+20Y+22`, no root in `F₃₁`, `deg F = 3`, hence irreducible | `Fpoly`, `Fpoly_eq`, `Fpoly_no_root`, `Fpoly_natDegree`, `Fpoly_irreducible` |
| `2F = Q` on `{1,2,4}`; coset identity `2F = Q + 2Γ`; `P(x) = 23x + x⁵·2F(x⁶)` | `two_F_eq_Q`, `coset_identity`, `P_eval_via_F` |
| `r = 2`, `A = 5`, `B = 2`: 25 box pairs, injective; `P = XQ(X²)` with the degree-11 `Q` interpolates all 25 points | `boxPairs`, `phi5_injective_on_box`, `Qodd`, `Podd_interpolates` |
| `g = Y²+30Y+20 = (Y−25)(Y−7)`; `g ∣ Q` (explicit quotient `H`) and via the theorem `fixed_divisor_box` | `g`, `g_eq`, `H`, `Qodd_eq_g_mul_H`, `g_dvd_Qodd`, `g_dvd_Qodd'`, `Qodd_roots` |
| (round 4) `L = F₃₁[Y]/(F) = F_{31³}` is a field, `[L : F₃₁] = 3`, `α` the class of `Y`, `31 = 0` in `L` | `L`, `α`, `finrank_L`, `h31L`, instances `Fact (Irreducible Fpoly)`, `Module.Finite`, `Finite`, `CharP L 31` |
| (round 4) `α³ = 23α²+11α+9`; `α⁴, α⁸, α¹⁶`; `α³¹ = 4+7α+17α²`; `α⁹⁶¹ = (α³¹)³¹ = 19+23α+14α²` (Frobenius additivity, `c³¹ = c` on constants) | `α_cube`, `α_pow_four`, `α_pow_eight`, `α_pow_sixteen`, `α_pow_31`, `const_pow_31`, `α_pow_961` |
| (round 4) symmetric functions `α+α³¹+α⁹⁶¹ = −8`, `e₂ = 20`, `α·α³¹·α⁹⁶¹ = −22`; **`F = ∏_{i<3}(Y − α^{31ⁱ})`** | `conj_sum`, `conj_e2`, `conj_prod`, `Fpoly_C_form`, `Fpoly_eq_conjProd` |
| (round 4) the Frobenius of `L/F₃₁` is `x ↦ x³¹`; `F = conjProd frob 3 α = Orb₃(Y − α)`; `F(α) = 0` | `frob_apply_L`, `frob_pow_apply_L`, `conjProd_eq`, `Fpoly_orbProd`, `aeval_α_Fpoly` |

### `Noise.lean`  (namespace `BGVNoise`, primitives and programs in `BGVNoise.NoiseModel`) — the noise and level model

**Modelling assumptions (all explicit).**  A ciphertext is an abstract pair
`Ct = ⟨noise : ℝ, level : ℕ⟩`; `level` counts modulus switches consumed.  The ring
constants `δ_R`, `E_ks`, `B_scale` and the switch ratio `ρ = q'/q` are abstract reals
(`NoiseModel`, with `0 ≤ δ, E_ks, B_scale, ρ` and `ρ ≤ 1`); no numeric values are
assumed anywhere.  Noise is **worst-case**: each primitive is a *definition* returning
the right-hand side of the corresponding displayed inequality, so the noise of a
program's output *is* the recursive bound (the inequalities (13)–(17) hold as
equalities of the model).  `mul := modSwitch ∘ mulRaw` consumes one level, `aut`
none, `ptct` and `add` none.  A plaintext constant of norm `c` is the trivial
ciphertext `triv c` at level 0.  Programs are Lean functions composing the
primitives in the order of Algorithm 2; every phase also returns the number of
key-switch-bearing operations `(products, automorphisms)` it issues, computed by the
same definitions as the values (each table entry is built once).  `⌈log₂ n⌉` is
`Nat.clog 2 n` throughout.  Nothing about lattices, RLWE, or actual BGV ciphertexts is
formalized: the model is the abstract bound calculus of Appendix C.5.

| paper statement | Lean name |
|---|---|
| ring constants `δ_R, E_ks, B_scale`, ratio `q'/q ≤ 1`; abstract ciphertext `(ν, level)` | `NoiseModel`, `Ct` |
| (13) `ν(ct₁+ct₂) ≤ ν₁+ν₂`, no level | `add`, `add_noise`, `add_level` |
| (14) `ν(c·ct) ≤ ‖c‖₁ν`, no level | `ptct`, `ptct_noise`, `ptct_level` |
| (15) `ν(Mul) ≤ δ_R ν₁ν₂ + E_ks` (relinearised product) | `mulRaw`, `mulRaw_noise`, `mulRaw_level` |
| (16) `ν(τ(ct)) ≤ ν + E_ks`, no level | `aut`, `aut_noise`, `aut_level`, `aut_consumes_none` |
| (17) `ν(ModSwitch) ≤ (q'/q)ν + B_scale`, one level | `modSwitch`, `modSwitch_noise`, `modSwitch_level` |
| product followed by a switch consumes one level | `mul`, `mul_noise`, `mul_level`, `mul_consumes_one`, `mul_noise_le` |
| every primitive is monotone in its input noises; nonnegativity preserved | `add_mono`, `ptct_mono`, `mulRaw_mono`, `aut_mono`, `modSwitch_mono`, `mul_mono`, `*_nonneg` |
| `⌈log₂ i⌉ = ⌈log₂⌈i/2⌉⌉ + 1`; `⌈log₂ d⌉ ≤ d−1` (`d ≥ 1`), `<` for `d ≥ 4`; `⌈log₂(k−1)⌉ = ⌈log₂ k⌉ ⟺ k−1` not a power of two | `clog_two_half`, `clog_le_pred`, `clog_lt_pred`, `clog_three`, `clog_pred_le`, `clog_pred_eq_iff` |
| Phase 1, power chain `x², x³, x⁶, x⁵` (`r=6`) / `x², x⁴, x³` (`r=4`); `δ₄ = 2`, `δ₆ = 3` levels; `4` resp. `3` products | `chain4`, `chain6`, `powerChain`, `deltaR`, `chainMuls`, `powerChain_Y_level`, `powerChain_u_level`, `powerChain_ks` |
| Phase 2, baby steps `Y^1..Y^{k−1}` as a table (balanced tree `bal`, or sequential `seq` = literal Algorithm 2); `k−2` products; `T i` at level `+⌈log₂ i⌉` (balanced) / `+(i−1)` (sequential) | `powTable`, `bal`, `seq`, `powTable_ks`, `powTable_level`, `powTable_bal_level`, `powTable_seq_level` |
| Phase 3, `Z = Y^{k−1}·Y`, squarings `Z^{2^i}` at level `+i` | `giantPow`, `giantPow_level` |
| Phase 4, block sums `Σ_{i<k} C_{jk+i}·Y^i` (plaintext–ciphertext); PS recursion on `g` blocks: `g−1` products, exact level `+⌈log₂ g⌉` above `Z` | `sumCt`, `block`, `block_noise`, `psRec`, `psRec_ks`, `psRec_level_le`, `psRec_level_ge`, `psRec_level` |
| Phase 5, orbit doubling `N ↦ Mul(N, τ(N))`, `⌈log₂ d⌉` steps, `⌈log₂ d⌉` levels, `(⌈log₂ d⌉, ⌈log₂ d⌉)` operations | `orbitStep`, `orbit`, `orbit_level`, `orbit_ks` |
| sequential product of the `d` conjugates costs `d−1` levels; doubling costs `⌈log₂ d⌉ ≤ d−1`, strictly less for `d ≥ 4` | `seqOrbit`, `seqOrbit_level`, `doubling_saves_levels`, `doubling_saves_levels_strict` |
| **ComposedEval** as a straight-line program (Phases 1–6 in the order of Algorithm 2) | `composedEval` |
| **exact level of ComposedEval** (balanced baby steps, `k, g ≥ 2`): `δ_r + ⌈log₂(k−1)⌉ + 1 + ⌈log₂ g⌉ + ⌈log₂ d⌉ + 1` | `L_prog`, `composedEval_level` |
| exact level of the literal Algorithm 2 (sequential baby steps): `δ_r + (k−1) + ⌈log₂ g⌉ + ⌈log₂ d⌉ + 1` | `L_seq`, `composedEvalSeq_level`, `L_seq_eq` |
| the paper's `L_comp = δ_r + ⌈log₂ k⌉ + ⌈log₂ g⌉ + 1 + ⌈log₂ d⌉ + 1`, `k = ⌈√deg C⌉`, `g = ⌈(deg C+1)/k⌉` | `L_comp'`, `L_comp`, `L_comp_eq`, `kOf`, `gOf`, `le_kOf_sq`, `kOf_pred_sq_lt`, `gOf_spec` |
| program level `≤ L_comp`; equality iff `k−1` is not a power of two | `L_prog_le_L_comp'`, `L_prog_le_L_comp`, `L_prog_eq_L_comp'_iff` |
| **baseline** `X·Q₀(X²)` by PS: program, exact level `1 + ⌈log₂(k₀−1)⌉ + 1 + ⌈log₂ g₀⌉ + 1`, the paper's `L_base = 1 + ⌈log₂ k₀⌉ + ⌈log₂ g₀⌉ + 2`, relation | `baselineEval`, `L_baseProg`, `baselineEval_level`, `L_base`, `L_baseProg_le_L_base`, `L_baseProg_eq_L_base_iff` |
| **instance** (Case IV, `deg C = 22`, `d = 14`, `r = 6`): `k = g = 5`; `L_comp = 15`; `L_base = 13` (`k₀ = g₀ = 25`); `L_comp − L_base = 2` | `kOf_instance`, `gOf_instance`, `L_comp_instance`, `L_base_instance`, `L_comp_sub_L_base_instance` |
| instance at program level: literal Algorithm 2 consumes exactly `15`; balanced-tree program `14`; baseline `13` | `L_seq_instance`, `composedEvalSeq_level_instance`, `L_prog_instance`, `composedEval_level_instance`, `L_baseProg_instance`, `baselineEval_level_instance` |
| (a) `ν(x²) ≤ δ_R ν_in² + E_ks` (+`B_scale` after the switch); `ν(x⁶) ≤ δ_R ν(x³)² + E_ks` | `sq_noise_raw`, `sq_noise_le`, `chain6_Y_noise_le`, `chain4_Y_noise_le` |
| (b) `ν(ct_{C^{(j)}}·Z^j) ≤ δ_R(Σ_{i<k}‖C_{jk+i}‖₁ν(Y^i))ν(Z^j) + E_ks` | `giant_step_noise_raw`, `giant_step_noise_le` |
| (c) `ν(N_{j+1}) ≤ δ_R ν(N_j)(ν(N_j)+E_ks) + E_ks` before the switch | `orbit_step_noise_raw`, `orbit_step_noise_le` |
| (d) `ν_out ≤ δ_R ν(x^{r−1})ν(ct_o) + \|c₁\|ν_in + E_ks` (for `‖c‖₁ ≤ 1`); exact form with `‖c‖₁` | `assembly_noise_raw`, `assembly_noise_le`, `assembly_noise_le'` |
| decryption correct iff `ν < q/2`; capacity `κ = log₂(q/ν)`, correct iff `κ > 1` | `correct`, `correct_iff`, `capacity`, `correct_iff_capacity` |
| **sufficiency**: chain with `L ≥ L_prog` levels, recursive bound `< q_L/2` ⟹ the output decrypts correctly at a level covered by the chain | `composedEval_correct_of_bound` |
| **key-switch count** `(chainMuls r + (k−2) + ⌈log₂ g⌉ + (g−1) + ⌈log₂ d⌉ + 1, ⌈log₂ d⌉)`, total `… + 2⌈log₂ d⌉ + 1`; instance `(19, 4)`, total `23`; baseline `54` | `composedEval_ks`, `ksTotal`, `composedEval_ksTotal`, `composedEval_ks_instance`, `composedEval_ksTotal_instance`, `baselineEval_ks`, `baselineEval_ks_instance` |
| each product / automorphism adds one `E_ks` | `mulRaw_adds_E_ks`, `aut_adds_E_ks` |
| Step 6: `A⁻¹((A m + q I) − q I) = m` (`A` a unit, any commutative ring) | `recover` |
| Step 5 returns `P_A(w_i) = I_i` on every slot ⟹ Step 6 returns `m_i` | `step6_of_step5` |
| **Correctness of Algorithm 3 on the slots**, assembled from `Galois.composed_correct` and `recover` | `full_boot_slots` |

**Two accounting remarks proved by the model** (not stated in the paper).
(i) The paper's `L_comp` bounds the baby-step depth by `⌈log₂ k⌉`, whereas a balanced
product tree reaches `Y^{k−1}` at depth `⌈log₂(k−1)⌉`; hence `L_prog ≤ L_comp` with
equality iff `k−1` is not a power of two (`L_prog_eq_L_comp'_iff`).  In the Case IV
instance `k−1 = 4`, so the balanced-tree program consumes `14` levels while the literal
Algorithm 2 (sequential baby steps `Y^i = Y^{i−1}·Y`) consumes exactly the paper's `15`
(`composedEvalSeq_level_instance`); the baseline value `13` is exact for both.
(ii) The power chain at `r = 6` has `4` products (`x⁶ = (x³)²`, `x⁵ = x²·x³`), not `r−1 = 5`
(`chainMuls_six`); with this the instance count is `19` products and `4` automorphisms,
`23` in total, as the paper states.

**The phase table (round 5, section 9).**  `PhaseRow = ⟨muls, auts, levels⟩`;
`phaseTable r k g d = [row1 r, row24 k g, row5 d, row6]` with rows
`(chainMuls r, 0, δ_r)`, `((k−2)+⌈log₂g⌉+(g−1), 0, ⌈log₂k⌉+⌈log₂g⌉+1)`,
`(⌈log₂d⌉, ⌈log₂d⌉, ⌈log₂d⌉)`, `(1, 0, 1)`.

| paper statement | Lean name |
|---|---|
| Phases 2–4 and Phase 6 of the program isolated; `composedEval` is their composition | `psPhase`, `assembly`, `composedEval_eq_phases` |
| Phases 2–4: exact level `⌈log₂(k−1)⌉ + 1 + ⌈log₂g⌉ ≤ ⌈log₂k⌉ + ⌈log₂g⌉ + 1`; `(k−2)+⌈log₂g⌉+(g−1)` products | `psPhase_level`, `psPhase_level_le`, `psPhase_ks` |
| Phase 6: one product, one level | `assembly_level`, `assembly_ks` |
| **the table, row by row**, against the program (`k, g ≥ 2`) | `phase_table` |
| `L_comp = Σ levels`; `(products, automorphisms) = (Σ muls, Σ auts)`; program level `≤ Σ levels` | `L_comp_eq_phase_sum`, `L_comp_eq_phase_sum'`, `composedEval_ks_eq_phase_sum`, `composedEval_level_le_phase_sum` |
| Case IV rows `(4,0,3), (10,0,7), (4,4,4), (1,0,1)`; sums `19, 4, 15` | `phaseTable_instance`, `phaseTable_instance_sums` |

### `Commute.lean`  (namespace `GaloisCommute`) — Appendix B.2, commutation and bigrading

`R` a commutative ring, `φ : R →+* R` (the Frobenius), `A : R`, `S : Finset R`; the idempotent part is over a field `K` with `(r : K) ≠ 0` and `A` of exact order `r`.

| paper statement | Lean name |
|---|---|
| `σ_A : R[X] → R[X]`, `σ_A(p) = p(AX)`; coefficientwise `cₖ ↦ Aᵏcₖ` | `sigma`, `sigma_eq_comp`, `sigma_coeff`, `sigma_X`, `sigma_C` |
| **Lemma (Scalar rotation is a diagonal automorphism)**: `σ_A σ_B = σ_{AB}`, `σ_A^ℓ = σ_{A^ℓ}`, `A^r = 1 ⟹ σ_A^r = id`, inverse `σ_{A⁻¹}` | `sigma_sigma`, `sigma_pow`, `sigma_pow_eq_one`, `sigma_inv_sigma` |
| **Lemma (commutation)**: `φ(A) = A ⟹ Frob ∘ σ_A = σ_A ∘ Frob` | `map_sigma`, `mapRingHom_comp_sigma` |
| `G_S = ∏_{a∈S}(X − a)`; `φ` fixes `S` ⟹ `Frob(G_S) = G_S` | `G`, `map_G` |
| `A` a unit, `A·S = S` ⟹ `σ_A(G_S) = A^{|S|} G_S` | `sigma_G` |
| both operators preserve the ideal `(G_S)` (descent to `V = R[X]/(G_S)`) | `dvd_sigma_of_dvd`, `dvd_map_of_dvd`, `span_G_map_sigma_le`, `span_G_map_le` |
| **direct product**: `σ_A^a = Frob^b ⟹ A^a = 1 ∧ φ^b = 1` | `direct_product`, `direct_product_hom` |
| `π_j = (1/r) Σ_{ℓ<r} A^{−jℓ} σ_A^ℓ`; its coefficient formula `(π_j p)_k = [Aᵏ = Aʲ] pₖ` | `pi`, `pi_coeff_geom`, `pi_coeff`, `geom_sum_root` |
| **Prop. (Bigraded decomposition)**: `σ_A π_j = A^j π_j`; `Σ_j π_j = id`; `π_j π_{j'} = [j = j'] π_j`; `X^k ∈ V_{k mod r}` | `sigma_pi`, `sum_pi`, `pi_pi`, `pi_X_pow`, `pow_eq_pow_iff` |
| every `V_j` is `Frob`-stable: `Frob ∘ π_j = π_j ∘ Frob` | `map_pi`, `map_mem_range_pi` |

### `Interpolation.lean`  (namespace `Interpolation`) — the functional equation from interpolation

`[Field K]`, `A : K`, `τ : ℤ`, `hA : A ^ 2 = τ * A - 1`, `T : Finset (ℤ × ℤ)`.

| paper statement | Lean name |
|---|---|
| `M_A`-stability as `M_A(T) = T` vs. pointwise `∀ v ∈ T, M_A v ∈ T` | `rot_mem_of_image_eq`, `image_rot_eq_of_iff` |
| existence and uniqueness of `P_A` of degree `< |T|` with `P_A(φ_A v) = λ` on an injective region | `exists_unique_interpolant` |
| **Thm (Unified order-r functional equation)**: stability + injectivity + interpolation + `2 ≤ |T|` ⟹ `P(AX) = A⁻¹(P(X) − X)` | `functional_equation` |
| support `{1} ∪ {k ≡ r−1 (mod r)}`, `c₁ = 1/(1−A²)`, and `P = c₁X + X^{r−1}Q(X^r)` — no functional-equation hypothesis | `order_r_support`, `order_r_factored` |
| `M_A(T_B) = T_B` (τ = 1) and `M_A([−B,B]²) = [−B,B]²` (τ = 0) as image identities; `|T_B|, |box| ≥ 2` for `B ≥ 1` | `hex_image_rot`, `box_image_rot`, `two_le_card_hex`, `two_le_card_box` |
| hexagon instance (`A² = A − 1`, `2, 3 ≠ 0`): functional equation, support `{1} ∪ {k ≡ 5 (mod 6)}`, `P = c₁X + X⁵Q(X⁶)` | `hex_functional_equation`, `hex_support`, `hex_factored` |
| box instance (`A² = −1`, `2 ≠ 0`): functional equation, support `{1} ∪ {k ≡ 3 (mod 4)}`, `c₁ = 1/2` | `box_functional_equation`, `box_support` |

### `Radix.lean`  (namespace `Radix`) — existence of radices

`p` prime (`[Fact p.Prime]`); "exact order `r`" is the `OrderR` convention `A ^ r = 1 ∧ ∀ j, 0 < j → j < r → A ^ j ≠ 1`.

| paper statement | Lean name |
|---|---|
| `|F_p^×| = p − 1`; an element of order `r` exists in `F_p^×` iff `r ∣ p − 1` | `natCard_units`, `exists_orderOf_eq_iff`, `exists_exact_order_iff` |
| `r ∣ p − 1 ⟺ p ≡ 1 (mod r)` | `dvd_pred_iff_mod` |
| `Φ₄(A) = 0 ⟺` exact order 4; `Φ₃(A) = 0 ⟺` exact order 3; `Φ₆(A) = 0 ⟺` exact order 6; `−1` has order 2 | `exact_order_four_iff`, `exact_order_three_iff`, `exact_order_six_iff`, `neg_one_exact_order_two` |
| a root of `Φ₄` exists in `F_p` iff `p ≡ 1 (mod 4)`; of `Φ₃`, `Φ₆` iff `p ≡ 1 (mod 3)` (`p > 3`); order 2 always | `root_Phi4_iff`, `root_Phi3_iff`, `root_Phi6_iff`, `exists_order_two` |
| `p > 3 ⟹ p mod 12 ∈ {1, 5, 7, 11}` | `prime_mod_twelve`, `prime_odd` |
| **Prop. (Available orders by the residue class of p)**: `HasOrder p r ↔ p % r = 1`; the four rows `{2,3,4,6}`, `{2,4}`, `{2,3,6}`, `{2}` | `HasOrder`, `hasOrder_iff`, `available_orders`, `available_orders_one`, `available_orders_five`, `available_orders_seven`, `available_orders_eleven` |

### `NormCriterion.lean`  (namespace `NormCriterion`) — Lemma "Norm criterion"

Two layers.  Abstract: `K, L` fields, `[Algebra K L] [FiniteDimensional K L] [IsGalois K L]`, `σ : L ≃ₐ[K] L` generating the Galois group (`hgen : ∀ τ, ∃ i, σ ^ i = τ`) with `σ ^ d = 1`.  Finite fields: `[Fintype K] [Finite L]`, `σ = frob` (the Frobenius `x ↦ x^{|K|}`, `FiniteField.frobeniusAlgEquivOfAlgebraic`), `d = finrank K L`.  Concrete: `K = ZMod p`, `L = GaloisField p d`.  The coefficientwise action is `mapRingHom (toHom σ)`, so `Orb_d` is literally `Galois.orbProd` of `Doubling.lean`.

| paper statement | Lean name |
|---|---|
| `Orb_d` is multiplicative; `π g = g ⟹ Orb_d(g) = g^d` | `orbProd_mul`, `orbProd_prod`, `orbProd_of_fixed` |
| conjugate product `∏_{i<d}(Y − σⁱα) = Orb_d(Y − α)`, monic of degree `d`, `α` a root | `conjProd`, `conjProd_eq_orbProd`, `conjProd_monic`, `conjProd_natDegree`, `eval_conjProd` |
| `Orb_d(Y − α)` is `σ`-fixed, hence has coefficients in `K` | `conjProd_map_eq`, `mem_range_algebraMap_of_fixed`, `mem_range_algebraMap_of_fixed_gen`, `conjProd_lifts` |
| `deg minpoly α = d ⟹ minpoly α = Orb_d(Y − α)` | `minpoly_map_eq_conjProd` |
| Frobenius: `frob^{[L:K]} = 1`, generates `Gal(L/K)`, has order `[L:K]` | `frob`, `frob_apply`, `frob_pow_finrank`, `frob_gen`, `orderOf_frob` |
| an irreducible of degree `[L:K]` has a root in `L` | `exists_root_of_irreducible` |
| **Norm criterion, irreducible case**: `F` monic irreducible of degree `d` ⟹ `F = Orb_d(Y − α)` for a root `α ∈ F_{p^d}` | `irreducible_eq_orbProd`, `irreducible_eq_orbProd_galoisField` |
| **(⇐), degree-`d` factors**: `h_i` monic irreducible of degree `d` ⟹ `∏ h_i = Orb_d(C)` with `C` monic of degree `#factors` | `norm_form_of_factors`, `prod_irreducible_eq_orbProd`, `prod_irreducible_eq_orbProd_galoisField` |
| a root of `Orb_d(C)` is a root of some `σʲC`; two distinct conjugates at one root give `(Y − β)² ∣ Orb_d(C)` | `exists_conj_root`, `conj_root_shift`, `sq_dvd_orbProd_of_two_roots` |
| **(⇒), squarefree**: `F` separable, `F = Orb_d(C)`, `F(β) = 0` ⟹ the `σ`-orbit of `β` has `d` elements | `orbit_full_of_separable_orbProd` |
| hence `deg minpoly β = [L:K]`; every monic irreducible factor of a squarefree norm form with a root in `L` has degree exactly `d` | `minpoly_natDegree_eq_of_orbit_full`, `natDegree_eq_finrank_of_squarefree_orbProd`, `factor_natDegree_eq_finrank_of_squarefree_orbProd`, `factor_natDegree_eq_galoisField` |
| `[GaloisField p d : ZMod p] = d` | `finrank_galoisField` |
| (round 4) `Orb_d(C)` is monic of degree `d·deg C` for monic `C`; `C ∣ Orb_d(C)`; `Orb_d(C)` is `σ`-fixed and lifts to a monic `g ∈ K[Y]` | `orbProd_monic`, `natDegree_orbProd_of_monic`, `toHom_pow_eq_one`, `dvd_orbProd_self`, `orbProd_lifts` |
| (round 4) **(⇐), factors of degree `kd`**, tower form `K ⊆ L ⊆ M` finite fields, `h` monic irreducible of degree `[M:K]` ⟹ `h = Orb_{[L:K]}(C)` with `C = minpoly_L β` monic of degree `[M:L]`; products thereof | `irreducible_eq_orbProd_of_tower`, `prod_irreducible_eq_orbProd_of_tower` |
| (round 4) concretely: `h ∈ F_p[Y]` monic irreducible of degree `k·d` ⟹ `h = Orb_d(C)` over `GaloisField p d`, `C` monic of degree `k` (tower `M = GaloisField p (k·d)`); products | `irreducible_eq_orbProd_galoisField_of_dvd`, `prod_irreducible_eq_orbProd_galoisField_of_dvd` |
| (round 5) `Orb_{tq}(x) = Orb^{φ^t}_q(Orb_t x)`; `Orb_d(x^e) = Orb_d(x)^e`; `Orb_t(x)` is `φ`-fixed when `φ^t x = x` | `orbProd_mul_eq`, `orbProd_pow`, `orbProd_fixed_of_period` |
| (round 5) the Frobenius **period** `t` of a factor `h₁` over `L` (`Function.minimalPeriod`); `t ∣ d`, `t > 0`; distinct conjugates `σʲh₁` are pairwise coprime | `period`, `act_pow_period`, `period_pos`, `period_dvd`, `isCoprime_act_pow`, `pairwise_isCoprime_act_pow` |
| (round 5) **splitting**: `h = Orb_t(h₁) = ∏_{j<t} σʲh₁`, `deg h = t·deg h₁`; `Orb_d(h₁) = h^{d/t}` | `orbProd_lifts_of_period`, `map_eq_orbProd_period`, `orbProd_eq_map_pow` |
| (round 5) **(⇐), general**: `d/t ∣ μ ⟹ h^μ = Orb_d(h₁^{μ/(d/t)})`; the case `m ∣ d` with `h₁ = Y − β` | `pow_eq_orbProd_of_dvd`, `pow_eq_orbProd_of_dvd_finite`, `pow_eq_orbProd_of_natDegree_dvd`, `pow_eq_orbProd_galoisField`, `pow_eq_orbProd_galoisField_of_natDegree_dvd` |
| (round 5) multiplicity bookkeeping: `mult_{h₁}(σⁿD) = mult_{h₁}(D)` when `σⁿh₁ = h₁`; `mult_{h₁}(Orb_d C) = (d/t)·mult_{h₁}(Orb_t C)`; `mult_{h₁}(h) = 1`; `h ∤ G ⟹ h₁ ∤ G` | `emultiplicity_act_pow`, `emultiplicity_orbProd`, `orbProd_ne_zero`, `emultiplicity_map_irreducible`, `not_dvd_map_of_not_dvd` |
| (round 5) **(⇒), non-squarefree `F`**: `F = Orb_d(C)`, `h^μ ∥ F ⟹ d/t ∣ μ`, hence `d ∣ m_h μ` | `period_div_dvd_of_orbProd`, `dvd_natDegree_mul_of_orbProd`, `dvd_natDegree_mul_of_orbProd_finite`, `dvd_natDegree_mul_galoisField` |
| (round 5) `minpoly_K β = ∏_{i<n}(Y − β^{\|K\|^i})` over any finite field, roots pairwise distinct; `σⁱβ = σ^{i mod n}β` | `conjProd_map_eq_of_fixed`, `minpoly_map_eq_conjProd_of_fixed`, `frob_pow_apply`, `pow_card_pow_natDegree_minpoly`, `minpoly_map_eq_conjProd_finite`, `frob_pow_apply_injOn`, `frob_pow_apply_mod` |
| (round 5) **`t = gcd(m_h, d)`** (tower `K ⊆ L ⊆ M ∋ β`; over `F_p` with `M = F_{p^{d·deg h₁}}`) | `period_eq_gcd_of_tower`, `period_eq_gcd_galoisField` |
| (round 5) **the paper's form**: `d ∣ m μ ⟹ h^μ = Orb_d(C)`, `deg C = mμ/d`; `h^μ` norm form ⟺ `d ∣ m μ` | `pow_eq_orbProd_galoisField_of_dvd_mul`, `pow_eq_orbProd_galoisField_iff` |
| (round 5) **full criterion**: `F = ∏ hᵢ^{μᵢ}` (distinct monic irreducibles) is a norm form over `F_{p^d}` ⟺ `∀ i, d ∣ mᵢ μᵢ`; `deg C = Σ mᵢμᵢ/d` | `exact_multiplicity_of_prod`, `normForm_iff_galoisField`, `normForm_of_dvd_galoisField` |

### `Repair.lean`  (namespace `Repair`) — Corollary "Removing the obstruction"

`[Field K]`, `g Q Γ H Q₁ Γ₁ : K[X]`, `hQ : Q = g * Q₁`, `hΓ : Γ = g * Γ₁`; `a ≡ b (mod m)` is written `m ∣ a − b`.

| paper statement | Lean name |
|---|---|
| (i) `g^d H ≡ Q (mod Γ) ⟺ g^{d−1} H ≡ Q₁ (mod Γ₁)` (`g ≠ 0`, `d ≥ 1`) | `cong_iff` |
| `gcd(g, Γ/g) = 1` from `Γ` squarefree | `isCoprime_of_squarefree` |
| (ii) `g` (and `g^m`) invertible mod `Γ₁`; reduced coset `H ≡ Q₁ g^{−(d−1)} (mod Γ₁)`; remainder form `H %ₘ Γ₁ = (Q₁ g^{−m}) %ₘ Γ₁` | `exists_inv_mod`, `pow_inv_mod`, `reduced_coset`, `modByMonic_eq_of_dvd_sub`, `reduced_coset_modByMonic` |
| (iii) `g(a) = 0`, `gcd(g,Γ₁) = 1 ⟹ Γ₁(a) ≠ 0`; `Q + cΓ = g(Q₁ + cΓ₁)` | `eval_ne_zero_of_isCoprime`, `coset_factor` |
| **explicit consistency condition**: `a` a simple root of `g`, `F = Q + cΓ` with `mult_a F ≥ 2` ⟹ `c = −Q₁(a)/Γ₁(a)`; converse; as an iff | `consistency`, `sq_dvd_of_consistency`, `consistency_iff` |
| every norm form in the coset is divisible by `g^d` (`g` a product of distinct linear factors) | `pow_prod_dvd_of_forall_pow_dvd`, `g_pow_dvd_normForm` |
| lift: `Orb_d(C_H) = H ⟹ Orb_d(g C_H) = g^d H = F` | `orbProd_of_fixed`, `norm_form_of_reduced` |
| (iv) `⌈m/d⌉ = (m + d − 1)/d` bounds; `deg C = B + ⌈(n−B)/d⌉`; padded `deg H = d⌈(n−B)/d⌉ ≥ n − B`, `deg(g^d H) = d·deg C` | `le_mul_ceil`, `mul_ceil_lt`, `natDegree_C_eq`, `padded_degree` |
| (round 5) `deg Γ₁ = n − B` and `B ≤ n` derived from `Γ = gΓ₁`, `deg Γ = n`, `deg g = B`; `padded_degree` without the hypothesis `deg Γ₁ = n − B` (`deg Γ₁ ≤ deg H`, `deg(g^d H) = d(B + ⌈(n−B)/d⌉) = d·deg(g C_H)`) | `natDegree_Γ₁`, `B_le_n`, `padded_degree'` |

### `Unify.lean`  (namespace `Unify`) — Theorem "Prior evaluators as corners" and Proposition "Cost monotonicity"

| paper statement | Lean name |
|---|---|
| **Def. (`(r,d)`-graded cost)**, three branches: `2√(D/r)` (`d = 1`), `log₂ d` (`D/r ≤ d`), `2√(D/(rd)) + log₂(D/r)` | `gcost` |
| corners: `(1,1) ↦ 2√D`; `(2,1) ↦ 2√(D/2)`; `(4,1) ↦ √D`; `(1, d ≥ D) ↦ log₂ d`; `(1, 2 ≤ d < D) ↦ 2√(D/d) + log₂ D` | `gcost_one_one`, `gcost_two_one`, `gcost_four_one`, `gcost_norm_saturated`, `gcost_norm_extended`, `corners` |
| interior point `d < D/r` ↦ `2√(D/(rd)) + log₂(D/r) = Cost.cost` | `gcost_interior`, `interior_eq_cost` |
| **Prop. (Cost monotonicity)**: non-increasing in `r > 0`; strict unless the smaller order is already saturated; saturated orders tie | `gcost_antitone`, `gcost_strict_lt`, `gcost_saturated_tie`, `logb_le_interior` |
| at the boundary `D/r = d` the interior formula equals `2 + log₂ d > log₂ d` (downward jump) | `interior_at_boundary`, `saturation_jump` |

### `RadixCeiling.lean`  (namespace `RadixCeiling`) — Corollary "Admissible radix orders"

`M : Matrix (Fin 2) (Fin 2) ℤ` acts on `ℤ²` by `act M v = M·v`; the intertwining hypothesis is `hint : ∀ v, phi A (act M v) = A * phi A v`.

| paper statement | Lean name |
|---|---|
| the action of `M₂(ℤ)` on digit pairs; `M N` acts as the composite; `Mⁿ` as the `n`-fold iterate; `M_A` acts as `rot τ` | `act`, `act_one`, `act_mul`, `act_pow`, `act_MA` |
| `φ_A(Mⁿ v) = Aⁿ φ_A(v)`; `M^s = 1 ⟹ A^s = 1` (evaluate at `(0,1)`) | `phi_act_iterate`, `pow_eq_one_of_intertwine` |
| `ord A ∣ s`, `ord A ∣ ord M` | `orderOf_dvd_of_intertwine`, `orderOf_dvd_orderOf_matrix` |
| **Cor. (Admissible radix orders)**: `M^s = 1`, `s ≥ 1`, intertwining ⟹ `ord A ∈ {1,2,3,4,6}`; no order `5` or `≥ 7`; exact-order form | `orderOf_mem`, `no_order_five_or_ge_seven`, `exact_order_mem` |
| converse: `A² = τA − 1 ⟹ M_A` intertwines; `ord A = ord M_A = 6, 4, 3` for `τ = 1, 0, −1` (with `2, 3 ≠ 0`) | `MA_intertwines`, `orderOf_eq_six`, `orderOf_eq_four`, `orderOf_eq_three`, `orderOf_eq_orderOf_MA` |

### `TermCount.lean`  (namespace `TermCount`) — Theorem "The term count is generically attained"

`[Field K]`; general form: `s : Finset ι`, nodes `v : ι → K` injective on `s`, `k < s.card`; the support form takes `S : Finset K` with `ι = ↥S`, `v = Subtype.val`.

| paper statement | Lean name |
|---|---|
| `c_k : λ ↦ [X^k] P_λ` as a linear functional on the data `λ : s → K`; covector `([X^k] L_i)_i` | `coeffFunctional`, `coeffFunctional_apply`, `coeff_eq_zero_iff_mem_ker` |
| the Lagrange basis reproduces `X^k` for `k < |s|` | `interpolate_monomial` |
| `ℓ_k ≠ 0`; some data has `c_k ≠ 0`; `{c_k = 0}` is proper; `c_k` is onto | `coeffFunctional_ne_zero`, `exists_data_coeff_ne_zero`, `ker_ne_top`, `range_eq_top` |
| `{c_k = 0}` is a hyperplane: `dim ker c_k = |ι| − 1` | `finrank_ker` |
| the same on the support `S ⊆ K`: `dim ker c_k = |S| − 1` | `nodes`, `nodes_injOn`, `coeffFunctionalS`, `coeffFunctionalS_apply`, `coeffFunctionalS_ne_zero`, `exists_data_coeff_ne_zero_S`, `ker_ne_top_S`, `finrank_ker_S` |
| digit setting: on an injective region `T` the interpolant `Lagrange.interpolate T (φ_A) λ` has nonzero `k`-th coefficient for some data, `k < |T|` | `exists_digit_data_coeff_ne_zero` |

### `PSCount.lean`  (namespace `PSCount`) — Paterson–Stockmeyer counts, effective order, Prop. "Cost of ComposedEval"

`k = kOf m = ⌈√m⌉`, `g = gOf m = ⌈(m+1)/k⌉` from `Noise.lean`; `⌈log₂ ·⌉ = Nat.clog 2`.

| paper statement | Lean name |
|---|---|
| `PS(k,g) = (k−2)+⌈log₂g⌉+(g−1)`; `PS(m) = PS(⌈√m⌉, ⌈(m+1)/k⌉)` | `psCount'`, `psCount`, `psCount_def` |
| `1 ≤ k, g`; `g ≤ k+1`; `k ≤ √m + 1`; `⌈log₂ m⌉ ≤ log₂ m + 1` | `kOf_pos`, `gOf_pos`, `gOf_le_kOf_succ`, `kOf_le_sqrt_add_one`, `clog_le_logb_add_one` |
| **`PS(m) = 2√m + O(log m)`**, explicitly `PS(m) ≤ 2√m + log₂(√m + 2) + 1` (`m ≥ 1`); nat form `≤ 2k − 2 + ⌈log₂ g⌉` | `psCount_le`, `psCount_le_nat` |
| `PS + 3 = k + g + ⌈log₂ g⌉` | `psCount_eq`, `psCount'_eq` |
| **Thm (Factored order-r evaluation)**: `C_r = chain_r + PS(deg Q) + 1`; `chain_r ≤ r − 1` on `{4,6}`; `4` at `r = 6`, `3` at `r = 4`; `C_r ≤ (r−1) + 2√m + log₂(√m+2) + 2` | `factoredCount`, `chainMuls_le_pred`, `factoredCount_six`, `factoredCount_four`, `factoredCount_le`, `factoredCount_le_real` |
| **Def. (Effective order)** `ρ = r|T|/|Ω|`; `ρ = r` on a stable region; `|Ω|/r = |T|/ρ` | `rho`, `rho_stable`, `div_r_eq_div_rho` |
| **Prop. (The evaluator spends ρ)**: `deg Q ≤ |Ω|/r ⟹ 2√(deg Q) ≤ 2√(|T|/ρ)` | `sqrt_degQ_le` |
| box closure at `r = 6`: `ρ = 6(2B+1)²/(6B²+6B+1) = 4 + 2/(6B²+6B+1)`, `4 < ρ ≤ 6` | `rho_box_closure`, `rho_box_closure_gt_four`, `rho_box_closure_le` |
| **Prop. (Cost of ComposedEval)**, phase sum `(r−1)+(k−2)+⌈log₂g⌉+(g−1)+⌈log₂d⌉+1 = (r−1)+PS(k,g)+⌈log₂d⌉+1 = k+g+⌈log₂g⌉+⌈log₂d⌉+r−3` | `composedCount`, `composedCount_phases`, `composedCount_eq` |
| the product count of the `Noise.lean` program equals `chain_r + PS(k,g) + ⌈log₂d⌉ + 1` and is `≤` the phase sum | `composedCount_eq_ks`, `ks_eq_phases`, `ks_le_composedCount` |
| Case IV: phase sum `20` with `r−1 = 5`, `19` with the actual chain `4`; `k = g = 5`, `PS(22) = 10` | `composedCount_instance`, `composedCount_instance_chain`, `kOf_instance'`, `gOf_instance'`, `psCount_instance` |

### `LatticeMin.lean`  (namespace `LatticeMin`) — Lemma "Injectivity as a lattice minimum" and the feasibility constants

`A : R` any commutative ring for the equivalences; `A p u v : ℤ` with `p ∣ A² + 1` (resp. `p ∣ A² − A + 1`) and the kernel condition `p ∣ uA + v` for the bounds; the `ZMod` forms take `A : ℤ`, `p : ℕ`, `0 ≤ B`.

| paper statement | Lean name |
|---|---|
| `‖(η,λ)‖∞ = max{|η|,|λ|}`; `[−B,B]² = {‖·‖∞ ≤ B}`; kernel lattice `L_A = {φ_A = 0}` | `boxNorm`, `mem_box_iff_boxNorm`, `kernelLattice`, `mem_kernelLattice` |
| `T − T = 2T`: `[−B,B]² − [−B,B]² = [−2B,2B]²`, `T_B − T_B = T_{2B}` | `box_sub_box`, `hex_sub_hex` |
| **Lemma (Injectivity as a lattice minimum)**, second equivalence: injective on the box ⟺ `‖w‖∞ > 2B` on `L_A∖{0}`; on the hexagon ⟺ `N(w) > 2B` | `injOn_box_iff`, `injOn_hex_iff`, `injOn_box_iff_kernel`, `injOn_hex_iff_kernel` |
| `φ_A(w) = 0` in `ZMod p` ⟺ `p ∣ uA + v` | `phi_zmod_eq_zero_iff` |
| `A² ≡ −1`: `p ∣ u² + v²` on `L_A`; nonzero ⟹ `u² + v² ≥ p`, `2‖w‖∞² ≥ p`, `‖w‖∞ ≥ √(p/2)` | `dvd_sq_add_sq`, `sq_add_sq_pos`, `sq_add_sq_ge`, `boxNorm_sq_ge`, `sqrt_half_p_le_boxNorm` |
| **Thm (Feasibility), box, `c₄ = 8`**: `8B² < p` (i.e. `B < √(p/8)`) ⟹ `φ_A` injective on `[−B,B]²` | `box_injective_of_lt`, `box_injective_of_lt_sqrt` |
| `A² ≡ A − 1`: `p ∣ u² + uv + v²` on `L_A` (the Eisenstein norm, not `u² − uv + v²`); positive definite; `u² + uv + v² ≤ N(u,v)²`; `N(w)² ≥ p`, `N(w) ≥ √p` | `dvd_eisenstein`, `eisenstein_pos`, `eisenstein_le_hexNorm_sq`, `eisenstein_ge`, `hexNorm_sq_ge`, `hexNorm_nonneg`, `sqrt_p_le_hexNorm` |
| **Thm (Feasibility), hexagon, `c₆ = 4`**: `4B² < p` (i.e. `B < √p/2`) ⟹ `φ_A` injective on `T_B` | `hex_injective_of_lt`, `hex_injective_of_lt_sqrt` |
| instances `p = 31, A = 6, B = 2` (hexagon), `p = 29, A = 12, B = 1` (box) | two `example`s |
| (round 5) `A² ≡ −1`, `p` prime: `−1` is a square mod `p`, Fermat gives `p = a² + b²`, and `(b, ±a) ∈ L_A`: a kernel vector with `u² + v² = p`, `‖w‖∞² ≤ p` | `isSquare_neg_one_of_dvd`, `exists_kernel_sq_add_sq_eq`, `boxNorm_sq_le_of_sq_add_sq` |
| (round 5) **Lemma (Injective packing), box**: `√(p/2) ≤ λ₁^∞(L_A) ≤ √p`; injective on `[−B,B]²` ⟹ `4B² < p`; `4 ≤ c₄ ≤ 8` | `exists_kernel_boxNorm_le_sqrt`, `lambda1_box_bounds`, `box_injective_imp`, `box_constants` |
| (round 5) `A² ≡ A − 1`, `p` prime: `p` odd; `u² + uv + v² ≢ 2 (mod 4)`; `⌊√p⌋² < p`; pigeonhole on `{0..⌊√p⌋}²` gives a nonzero kernel vector with `\|u\|,\|v\| ≤ ⌊√p⌋`; hence one with `u² + uv + v² = p` (Thue) | `odd_of_dvd_eisenstein`, `eisenstein_ne_two_mul_odd`, `sqrt_sq_lt_of_prime`, `exists_kernel_small`, `exists_kernel_eisenstein_eq` |
| (round 5) `u² + uv + v² = p ⟹ 3N(w)² ≤ 4p`; **Lemma (Injective packing), hexagon**: `√p ≤ λ₁^hex ≤ (2/√3)√p`; injective on `T_B` ⟹ `3B² < p`; `3 ≤ c₆ ≤ 4` | `three_mul_hexNorm_sq_le`, `exists_kernel_hexNorm_le`, `lambda1_hex_bounds`, `hex_injective_imp`, `hex_constants` |

## Exact hypotheses (summary)

* Order six (`OrderSix`): `A ^ 2 = A - 1` in a field `K` with `(2 : K) ≠ 0` and
  `(3 : K) ≠ 0`.  Both are necessary: in characteristic 2 the relation gives an
  element of order 3, in characteristic 3 an element of order 2.
* Unified order `r` (`OrderR`): `A ^ r = 1`, `∀ j, 0 < j → j < r → A ^ j ≠ 1`, `3 ≤ r`.
  In `OrderR` the functional equation is a hypothesis; `Interpolation.lean` derives
  it from `∀ v ∈ T, M_A v ∈ T`, `Set.InjOn (phi A) T`, `2 ≤ |T|`, `P.degree < |T|`
  and `P(φ_A v) = λ` on `T` (uniqueness of Lagrange interpolation).
* Crystallographic: `M ^ r = 1` with `1 ≤ r`; nothing else.
* Injectivity criterion: `2 * B < |A|` and `2 * B * (|A| + 1) < p` over `ℤ`, with
  `A` any integer representative.
* Galois axis: `φ` any ring endomorphism; `φ ^ d = 1` where the norm is claimed
  invariant; `φ y = y` where evaluation is claimed to commute.
* Obstruction: `π` any ring endomorphism of `K[X]` fixing `X − C a`, `π ^ d = 1`,
  `2 ≤ d`.
* Commutation (`GaloisCommute`): `φ A = A` for the commutation; `IsUnit A` and
  `S.image (A * ·) = S` for the descent of `σ_A`; `∀ a ∈ S, φ a = a` for the descent of
  `Frob`; the idempotents are over a field with `(r : K) ≠ 0` and `A` of exact order `r`.
* Radices (`Radix`): `p` prime; `2 < p` for order 2 / `Φ₄`, `3 < p` for `Φ₃`, `Φ₆` and the
  mod-12 table.
* Norm criterion (`NormCriterion`): `L/K` finite Galois with a generator `σ` of the
  Galois group, `σ ^ d = 1`; for finite fields `[Fintype K] [Finite L]` only; concretely
  `ZMod p`, `GaloisField p d`, `d ≠ 0`.  Squarefree necessity (round 3) needs
  `Squarefree F` and a root of the factor in `L`; the round-5 necessity needs only
  `C ≠ 0`, `[PerfectField K]` (automatic for finite fields) and the exact multiplicity
  `h^μ ∣ F`, `h^{μ+1} ∤ F`.
* Repair (`Repair`): `Q = g Q₁`, `Γ = g Γ₁`, `g ≠ 0`, `IsCoprime g Γ₁` (derived from
  `Squarefree Γ`), and a *simple* root `rootMultiplicity a g = 1` for the consistency
  condition; `padded_degree'` needs `Γ₁ ≠ 0`, `H ≠ 0`, `C_H ≠ 0` and `deg H = d·deg C_H`.
* Graded cost (`Unify`): `0 < D`, `d = 1 ∨ 2 ≤ d`, `0 < r`; the paper's interior range
  bound `D/r < d log₂ p` is not part of the formula.
* Radix ceiling (`RadixCeiling`): `M ^ s = 1` with `1 ≤ s` and the pointwise intertwining
  `∀ v, phi A (act M v) = A * phi A v`; `A` in a field for the `orderOf` statements (any
  commutative ring for `A ^ s = 1`); the converse needs `2 ≠ 0`, `3 ≠ 0` as in `Radix`.
* Term count (`TermCount`): `[Field K]`, nodes injective on `s`, `k < s.card`; `[Fintype ι]`
  for the dimension count.
* PS counts (`PSCount`): `1 ≤ m` for the real bound; `2 ≤ k` for the closed form; `0 < r, T, Ω`
  for the effective order; `2 ≤ k`, `2 ≤ g` for the link to the `Noise.lean` program.
* Lattice minimum (`LatticeMin`): no hypothesis on `B` for the equivalences and difference
  sets; `p ∣ A² + 1` resp. `p ∣ A² − A + 1`, `0 ≤ B` and `8B² < p` resp. `4B² < p` for the
  sufficient conditions; `p` prime for the upper bounds and the necessary conditions.
* Norm criterion, degree `kd` (`NormCriterion`, section 8): finite fields `K ⊆ L ⊆ M` with
  `[IsScalarTower K L M]`, `h` monic irreducible of degree `[M : K]`; concretely `d ≠ 0`,
  `k ≠ 0`.
* Norm criterion, general multiplicity (`NormCriterion`, sections 9–12): abstractly `σ`
  generating `Gal(L/K)`, `σ^d = 1`, `0 < d`, `h` monic irreducible, `h₁` monic irreducible
  with `h₁ ∣ h` over `L` (the period `t` is defined from `h₁`); `t = gcd(m, d)` needs a
  root `β ∈ M` of `h₁` in a finite-field tower `K ⊆ L ⊆ M` with `[Fintype L]`; over `F_p`
  only `d ≠ 0`.  The full criterion takes `F = ∏ hᵢ^{μᵢ}` with the `hᵢ` monic irreducible
  and pairwise distinct (`h i = h j → i = j`).
* Noise model (`BGVNoise`): `0 ≤ δ, E_ks, B_scale, ρ`, `ρ ≤ 1`; level theorems need
  `2 ≤ k`, `2 ≤ g`; the power chain is defined for `r ∈ {4, 6}` (`r = 4` selects `chain4`,
  every other `r` selects `chain6`); noise-bound lemmas take nonnegativity of the input
  noises and norms as hypotheses.

## Not formalized / weakened

After round 5 the list of statements of the paper that are **not** machine-checked is:

* **Chebotarev density / monodromy** (the success probability `Π_d(n')` of the coset
  search and the random-matrix heuristics): out of scope by directive.
* **Latimer–MacDuffee / `GL₂(ℤ)`-conjugacy** of intertwiners to `M_A` (class number one):
  out of scope by directive.  The order and trace/determinant classification, the
  admissible orders `{1,2,3,4,6}` and their converse are complete
  (`Crystallographic.lean`, `RadixCeiling.lean`).
* **The numerical closure constant `12`** for the box closure: computed, not proved, in
  the paper; the sufficient sides `c₄ = 8`, `c₆ = 4` and (round 5) the necessary sides
  `4B² < p`, `3B² < p` are proved, so `4 ≤ c₄ ≤ 8` and `3 ≤ c₆ ≤ 4` (`LatticeMin.lean`).
* **The noise primitives are a model**: `add`, `ptct`, `mulRaw`, `aut`, `modSwitch` are
  *definitions* returning the worst-case bounds (13)–(17), not theorems about RLWE
  ciphertexts; the reduction from BGV ciphertexts to these inequalities, the linear
  transforms of Steps 1 and 4, the overflow bounds of Steps 2–3 and the HElib
  modulus-chain construction are not modelled.  The level/operation counts, the phase
  table (round 5) and the decryption criterion are proved *inside* the model.
* **Norm criterion, what remains**: only the Hensel lift of the criterion from `F_p` to
  the Galois ring `GR(p^e, d)` (`e > 1`).  Everything over `F_p` is now proved
  (`NormCriterion.normForm_iff_galoisField`: `∏ hᵢ^{μᵢ}` is a norm form over `F_{p^d}`
  ⟺ `∀ i, d ∣ mᵢ μᵢ`, with `t = gcd(mᵢ, d)` conjugates of degree `mᵢ/t` per factor).

Closed in earlier rounds (kept for the record): uniqueness of interpolation (round 3),
existence of radices (round 3; the count `φ(r)` of order-`r` elements is not stated),
admissible radix orders (round 4), the second equivalence of the lattice minimum
(round 4), the term count generically attained (round 4), the repair of the obstruction
(round 3) with the explicit example `F = Orb₃(Y − α)` over `F₃₁` (round 4), commutation
and bigrading (round 3; the idempotent part is stated over a field), the cost corner
table and the Paterson–Stockmeyer counts (rounds 3–4).  Closed in round 5: the lattice
upper bounds `λ₁ ≤ √p` (box) and `λ₁ ≤ (2/√3)√p` (hexagon), the derived identity
`deg Γ₁ = n − B` in the repair bookkeeping, the multiplicative-depth column of the phase
table, and the general multiplicity form of the norm criterion (necessity for
non-squarefree `F`, sufficiency for `d ∤ m_h`, `t = gcd(m_h, d)`).

Minor weakenings that remain: the idempotents of `Commute.lean` are stated over a field
(`ZMod p`), not over `GR(p^e, d)` with `e > 1`; the `O(1)` limit `ρ → 4` is replaced by the
exact value `4 + 2/(6B²+6B+1)`; orbit doubling is modelled for the power-of-two schedule.

## Notes

* The crystallographic trace bound `|tr M| ≤ 2` is proved *without* complex
  eigenvalues: Cayley–Hamilton gives `Mⁿ⁺¹ = aₙ₊₁M − d·aₙ I` with a Lucas-type
  integer sequence, and if `M ≠ ±I` then `M^r = I` forces `a_r = 0`, which the growth
  lemmas exclude for `|t| ≥ 2, det = 1` and for `t ≠ 0, det = −1`.
* The counting theorems `card_hex` and `card_closure` are proved symbolically in
  `B` (fibrewise count plus `Σ|η| = B(B+1)`, then inclusion–exclusion over the three
  box images), not by `decide` for finitely many `B`.
* All `decide` calls in `Example.lean` are kernel evaluations in `ZMod 31`; no
  `native_decide` is used anywhere.  The powers `α³¹`, `α⁹⁶¹` in `F₃₁[Y]/(F)` are
  verified by `linear_combination` against the relation `α³ = 23α² + 11α + 9` and
  `31 = 0`, with the integer coefficient polynomials computed offline; `α⁹⁶¹ = (α³¹)³¹`
  uses the additivity of the Frobenius in characteristic `31` (`add_pow_char`).
