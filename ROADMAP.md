# Roadmap

Part I now contains proofs of the first prime representation theorems, Gauss
reduction, and Dirichlet composition. The main remaining work is genus theory,
residue characters and reciprocity, followed by the constructions in Parts II
and III.

## Current implementation

| Area | Implemented | Remaining work |
| --- | --- | --- |
| Fermat and quadratic reciprocity | The `x²+y²`, `x²+2y²`, and `x²+3y²` prime criteria, descent, and the `−3` residue criterion | Euler’s general reciprocity statement and the general character construction |
| Binary quadratic forms | Integral coefficients, the matrix action, proper equivalence, Gauss reduction and uniqueness, and finiteness of reduced forms | Landau’s class-number-one theorem |
| Form class group | Congruence lemmas, Dirichlet composition, its group laws, and the `CommGroup` instance for admissible negative discriminants | Finiteness of the class group and the two-torsion count |
| Representation and genera | Corrected residue criteria, several §2 representation results, and the order-two criterion | Genus definitions, the genus map, principal genus theorem, and representation counts |
| Cubic and biquadratic reciprocity | Eisenstein arithmetic and Euclidean division; prime splitting in the Eisenstein and Gaussian integers | Residue characters, finite-field steps, reciprocity and supplementary laws |
| Exercises §§1–4 | Many proofs and concrete examples | Several proofs, enumerations, and corrections to earlier signatures |
| Class field theory | Provisional interfaces for orders, ideals, class fields, and splitting | The underlying constructions and proofs |
| Complex multiplication | Provisional interfaces for elliptic, modular, and Weber functions | Analytic constructions, CM theory, and reciprocity |

Some older statements have missing hypotheses or conclusions that do not yet
express the intended theorem. The source documents these cases, including
counterexamples and corrected representation criteria in `Genus.lean`. Keep the
unproved versions separate from the completed results when extending the project.
A build alone does not establish that a theorem is free of `sorry` dependencies.

## Mathlib coverage

The audit below concerns Mathlib `v4.31.0`, commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Its coverage labels describe what the
pinned dependency provides, not whether this project has finished a proof:

- **In Mathlib:** the result, or a directly usable version, is available.
- **Partial:** useful foundations are available, but the stated result needs more work.
- **Not in Mathlib:** definitions and results to develop within this project.
- **Deferred theory:** substantial reciprocity, class field theory, Čebotarev, or CM
  machinery is still needed.

### Available foundations

| Topic searched | Found? | Location |
| --- | --- | --- |
| Sum of two squares (Fermat) | **Yes** | `Nat.Prime.sq_add_sq` in `NumberTheory/SumTwoSquares.lean` (`p % 4 ≠ 3 → ∃ a b, p = a²+b²`) |
| Quadratic reciprocity / Legendre / Jacobi | **Yes** | `NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`, `Zsqrtd/QuadraticReciprocity.lean` |
| Gaussian integers / `ℤ√d` | **Yes** | `NumberTheory/Zsqrtd/{Basic,GaussianInt}.lean` |
| `ZMod`, `IsSquare`, residues | **Yes** | `Data/ZMod/*`, used throughout |
| General quadratic forms | **Yes** | `LinearAlgebra/QuadraticForm/*` (not specialized to binary integral forms) |
| **Binary** quadratic forms (a,b,c), reduction, proper equiv. | **No** | - |
| Form class group, Dirichlet composition | **No** | - |
| Genus theory | **No** | - |
| Ideal class group (Dedekind / ring of integers) | **Yes** | `RingTheory/ClassGroup.lean`, `NumberTheory/NumberField/ClassNumber.lean`, `NumberTheory/ClassNumber/*` |
| Ideal class group of a **non-maximal order** (conductor `f`) | **No** | - |
| Dirichlet's theorem (primes in AP) | **Yes** | `NumberTheory/PrimesCongruentOne.lean`, `NumberTheory/LSeries/Dirichlet.lean` |
| Hilbert / ring class field, Artin reciprocity, Čebotarev | **No** | - (no class field theory in Mathlib) |
| `SL(2,ℤ)` action on `ℍ`, fundamental domain | **Yes** | `NumberTheory/Modular.lean`, `Analysis/Complex/UpperHalfPlane/*` |
| Modular forms, Eisenstein series, `Δ`, Dedekind `η`, q-expansions | **Yes** | `NumberTheory/ModularForms/*` (incl. `EisensteinSeries/*`, `Delta.lean`, `DedekindEta.lean`) |
| Weierstrass `℘` (analytic), `℘'`, periodicity, analyticity | **Yes** | `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (`PeriodPair.weierstrassP`, `derivWeierstrassP`, …) |
| Algebraic `j`-invariant of an elliptic curve | **Yes** | `AlgebraicGeometry/EllipticCurve/{ModelsWithJ,IsomOfJ}.lean` |
| Modular **`j`-function** `j(τ)` on `ℍ` (as a modular function) | **No** | - (Eisenstein/`Δ` present; `j = E₄³/Δ` not assembled) |
| Complex multiplication; CM values of `j` are algebraic integers | **No** | - |
| Weber functions; Shimura reciprocity | **No** | - |

## Blueprint reference

### Part I - From Fermat to Gauss

| Node (blueprint label) | Lean decl | Mathlib coverage | Notes |
| --- | --- | --- | --- |
| `thm:descent` | `Fermat.descent_step` | **Not in Mathlib** | Proved here; the audit found no packaged descent lemma. |
| `thm:fermat_two_squares` | `Fermat.prime_sq_add_sq` | **In Mathlib** | Proved using `Nat.Prime.sq_add_sq`. |
| `thm:fermat_x2_2y2` | `Fermat.prime_sq_add_two_sq` | **Partial** | Proved here using reduction and quadratic reciprocity. |
| `thm:fermat_x2_3y2` | `Fermat.prime_sq_add_three_sq` | **Partial** | Proved here using the same reduction machinery. |
| `def:binary_qf` | `Forms.BinaryQF` | **Not in Mathlib** | The project uses explicit coefficients `(a,b,c)`. |
| `def:discriminant` | `Forms.BinaryQF.discr` | **Not in Mathlib** | Defined from the three coefficients. |
| `def:proper_equiv` | `Forms.ProperlyEquivalent` | **Partial** | Mathlib supplies `Matrix.SpecialLinearGroup`; the action on forms is implemented here. |
| `def:reduced` / `thm:reduction` | `Forms.BinaryQF.Reduced`, `Forms.exists_unique_reduced` | **Not in Mathlib** | Existence and uniqueness are proved here. |
| `thm:finite_class_number` | `Forms.finite_reduced_of_discr` | **Not in Mathlib** | Follows from reduction bounds. |
| `def:form_class_group` / `def:dirichlet_composition` / `thm:form_class_group_is_group` | `Forms.FormClassGroup`, `Forms.compose`, `Forms.isCommGroup` | **Not in Mathlib** | Composition and its group laws are proved in `Genus.lean`. |
| `def:represents` / `def:genus` / `def:principal_genus` | `Genus.*` | **Not in Mathlib** | - |
| `thm:representation_residue` | `Genus.properlyRepresents_iff_isSquare` | **Partial** | The original signature needs additional hypotheses; see the corrected variants in `Genus.lean`. |
| `thm:genus_congruence` | `Genus.represents_principal_iff_congruence` | **Not in Mathlib** | Genus theory; partly congruences + Dirichlet (in Mathlib). |

#### §3 - Composition, genera, convenient numbers

| Node (blueprint label) | Lean decl | Mathlib coverage | Notes |
| --- | --- | --- | --- |
| `lem:l3_2` / `lem:l3_5` | `Forms.lemma_3_2`, `Forms.lemma_3_5` | **Not in Mathlib** | Simultaneous congruences used in composition. |
| `def:dirichlet_form` / `prop:p3_8` | `Forms.dirichletForm`, `Forms.prop_3_8` | **Not in Mathlib** | Explicit composition formula (3.7) and its well-definedness. |
| `thm:form_class_group_is_group` | `Forms.isCommGroup` | **Not in Mathlib** | The theorem proves the laws for `compose`; a `CommGroup` instance is also defined for admissible negative discriminants. `DiscrForms` contains primitive forms with `a > 0`. |
| `thm:t3_9_inverse` | `Forms.thm_3_9_inverse` | **Not in Mathlib** | The inverse is the opposite class; this is proved. |
| `lem:l3_10` / `def:mu` / `prop:p3_11` | `Forms.lemma_3_10`, `Forms.mu`, `Forms.prop_3_11` | **Not in Mathlib** | The order-two criterion is proved. The exponent `μ` is defined; the `2^{μ−1}` two-torsion count remains unproved. |
| `def:assigned_characters` / `def:genus_map` | `Genera.Psi`, `Genera.genusVector` | **Not in Mathlib** | Cox (3.16)/(3.12); `δ`, `ε` defined concretely. |
| `lem:l3_13` / `cor:c3_14_i` / `cor:c3_14_ii` | `Genera.lemma_3_13`, `Genera.cor_3_14_i`, `…_ii` | **Not in Mathlib** | Genus map is a homomorphism; genera equinumerous; count a power of two. |
| `lem:l3_17` / `thm:t3_15_i` / `thm:t3_15_ii` | `Genera.lemma_3_17`, `Genera.thm_3_15_i`, `…_ii` | **Not in Mathlib** | `Ψ` surjective, kernel `H`; `2^{μ−1}` genera; principal genus `= C(D)²`. |
| `lem:l3_20` | `Genera.lemma_3_20` | **Not in Mathlib** | Complete character determines the genus. |
| `thm:t3_21` | `Genera.thm_3_21` | **Not in Mathlib** | The signature covers Cox’s conditions (i)⟺(ii), with proof still pending. Conditions (iii)–(vi), concerning equivalence modulo `m`, over `ℤ_p`, and over `ℚ`, need the corresponding actions on forms. |
| `thm:t3_22` | `Genera.thm_3_22` | **Not in Mathlib** | Four of Cox’s five conditions are stated. The condition `C(-4n) ≅ (ℤ/2ℤ)^k` is still omitted; the required `CommGroup` instance is now available. |
| `def:convenient_number` / `prop:p3_24` | `Genera.ConvenientNumber`, `Genera.prop_3_24` | **Not in Mathlib** | Euler's idoneal numbers; one-class-per-genus characterization. |
| `lem:l3_25` / `cor:c3_26` | `Genera.lemma_3_25`, `Genera.cor_3_26` | **Not in Mathlib** | Representation counts `2∏(1+(-n/p))` and `2^{r+1}`. Cox derives them via Exercise 3.20; the Lean proofs remain unfinished. |

The blueprint leaves several finite enumerations as `\notready`: Exercises
2.9(b), 2.19 (discriminants `-3,-15,-24,-31,-52`), 3.14 (discriminant `-164`),
and 3.25(b). These can be handled by enumerating reduced forms with `Finset`
or `Decidable` once their statements are added.

Other §3 exercise nodes still need separate formalizations: 3.3, 3.10, 3.11,
3.15, and 3.20(b–f) supply proofs of chapter results; 3.2 and 3.6 concern direct
composition; 3.17, 3.18, and part of 3.21 need actions over `ℚ` and `ℤ_p`;
3.9, 3.19, and 3.25(a,c) concern the abstract class group; 3.24 needs the
Kronecker symbol. Direct composition and the class-group instance are now
available, so some of these can build on the existing development. None of the
omitted exercise statements is introduced as an axiom.

#### §4 - Cubic and biquadratic reciprocity

The audited Mathlib version has no Eisenstein integers. Section 4.A therefore
uses `EisensteinInt`, with coefficients for `a + bω`, norm `a²−ab+b²`, and
explicit `IsUnitE`, `IsPrimeE`, `AssociatedE`, and `ModEq` predicates. There is
no registered `CommRing` instance. `Zsqrtd (-3)` would give the different order
`ℤ[√−3]`, of conductor 2, rather than the maximal order `ℤ[ω]`. Exercise 4.6
uses that distinction to prove that `ℤ[√−3]` is neither a PID nor a UFD.
Section 4.B uses Mathlib’s `GaussianInt = Zsqrtd (-1)` and its existing ring
structure; the quartic character remains to be constructed.

`IsPrimary` follows Cox’s convention `π ≡ ±1 (mod 3)`. Two of the six
associates are primary. The cubic character is unchanged by sign because
`χ_π(−1) = (−1/π)₃ = 1`: a cube root of unity whose square is 1 equals 1.
Thus `thm_4_12` and `eq_4_14` use this convention, while
`supplementary_4_13` chooses the `−1` representative
`π = −1 + 3m + 3nω`. Ireland–Rosen instead uses `π ≡ −1 (mod 3)` throughout.

| Node (blueprint label) | Lean decl | Mathlib coverage | Notes |
| --- | --- | --- | --- |
| `def:eisenstein_int` / `def:eisenstein_norm` / `lem:eisenstein_norm_mul` | `CubicReciprocity.EisensteinInt{,.norm,.norm_mul}` | **Not in Mathlib** | Explicit arithmetic with norm `a²−ab+b²`. |
| `prop:p4_3` / `cor:c4_4` | `…prop_4_3`, `…cor_4_4` | **Not in Mathlib** | Euclidean ⇒ PID/UFD (irreducible ⟺ prime). |
| `lem:l4_5_i` / `lem:l4_5_ii` / `lem:l4_6` | `…lemma_4_5_i`, `…_ii`, `…lemma_4_6` | **Not in Mathlib** | Units `{±1,±ω,±ω²}`; norm-prime ⇒ prime. |
| `prop:p4_7_*` / `lem:l4_8` / `cor:c4_9` | `…prop_4_7_{ramified,split,inert}`, `…lemma_4_8`, `…cor_4_9` | **Not in Mathlib** | Split/inert/ramified (`3=−ω²(1−ω)²`); residue field; Fermat. |
| `def:cubic_char` / `lem:cubic_char_*` / `lem:cubic_residue_iff` | `…cubicChar`, `…cubicChar_{spec,mul}`, `…cubicChar_eq_one_iff` | **Not in Mathlib** | Cubic residue character (4.10)/(4.11). |
| `def:primary_eisenstein` | `…IsPrimary` | **Not in Mathlib** | `π ≡ ±1 (mod 3)`, following Cox’s convention above. |
| `thm:cubic_reciprocity` | `…thm_4_12` | **Deferred theory** | Cubic reciprocity; `\notready`; proof pending. |
| `lem:cubic_supplementary` | `…supplementary_4_13` | **Deferred theory** | Supplementary laws (4.13). `\notready`. |
| `lem:cubic_int_residue` | `…eq_4_14` | **Not in Mathlib** | Integer cubic-residue criterion. |
| `thm:x2_27y2` | `…thm_4_15` | **Deferred theory** | `p = x²+27y²`; `\notready`; proof pending. |
| `def:gaussian_primary` / `prop:p4_18_*` / `lem:gaussian_fermat` | `BiquadraticReciprocity.{IsPrimaryG,prop_4_18_*,eq_4_19}` | **Partial (Mathlib `GaussianInt`)** | Prime classification uses Mathlib’s Gaussian integers; primary means `π≡1 mod 2+2i`. |
| `def:quartic_char` / `lem:quartic_char_*` / `lem:quartic_residue_iff` | `…quarticChar`, `…quarticChar_{spec,mul}`, `…quarticChar_eq_one_iff` | **Not in Mathlib** | Quartic residue character (4.20). |
| `thm:biquadratic_reciprocity` | `…thm_4_21` | **Deferred theory** | Biquadratic reciprocity; `\notready`; proof pending. |
| `lem:biquadratic_supplementary` / `thm:quartic_char_two` | `…supplementary_4_22`, `…thm_4_23_i` | **Deferred theory** | Supplementary laws (4.22); `(2/π)₄=i^{ab/2}`. `\notready`. |
| `thm:x2_64y2` | `…thm_4_23_ii` | **Deferred theory** | `p = x²+64y²`; `\notready`; proof pending. |

The remaining reciprocity results use `sorry` and retain `\notready`:
cubic reciprocity (4.12), its supplementary laws (4.13), `x²+27y²` (4.15),
biquadratic reciprocity (4.21), its supplementary laws (4.22), `(2/π)₄`
(4.23(i)), `x²+64y²` (4.23(ii)), and Exercise 4.15(d), concerning `x²+243y²`.
These require the reciprocity machinery used by Cox beyond Chapter 1; they
are not introduced as axioms.

The omitted §4 exercise nodes include separate proofs of chapter results
(4.5, 4.7, 4.8, 4.11, 4.13, 4.16, 4.18(a,c), 4.22, 4.23), Gaussian periods
and cubic Gauss sums (4.28, 4.29), the embedding into `ℂ` (4.1), multivariate
polynomial ideals (4.3), and calculations with the residue characters
(4.9(b), 4.12, 4.19, 4.20, 4.24(a,c–f), 4.25, 4.26, 4.27).

### Part II - Class Field Theory

| Node | Lean decl | Mathlib coverage | Notes |
| --- | --- | --- | --- |
| `def:quad_order` / `def:order_discriminant` | `Order.QuadOrder`, `Order.QuadOrder.discr` | **Partial** | Orders not packaged; `ℤ√d`, `NumberField`, Dedekind theory exist. |
| `def:ideal_class_group_order` / `thm:ideal_class_group_finite` | `Order.QuadOrder.idealClassGroup`, `…idealClassGroup_finite` | **Partial** | Class group + finiteness exist for the **maximal** order; non-maximal needs work. |
| `thm:form_ideal_bridge` (Cox 7.7) | `Bridge.formClassGroup_equiv_idealClassGroup` | **Not in Mathlib** | Depends on Part I + orders. |
| `thm:bridge_composition` | `Bridge.bridge_respects_composition` | **Not in Mathlib** | - |
| `def:hilbert_class_field` / `def:ring_class_field` | `RingClassField.{hilbertClassField,ringClassField}` | **Deferred theory** | No class field theory in Mathlib. |
| `thm:artin_reciprocity` | `RingClassField.artinReciprocity` | **Deferred theory** | - |
| `def:splits_completely` / `thm:chebotarev` | `RingClassField.{SplitsCompletely,chebotarev_splitting}` | **Deferred theory** | Čebotarev not in Mathlib (Dirichlet's theorem is). |
| `def:class_polynomial` / `thm:main_splitting` / `thm:main_class_poly` | `MainTheorem.*` | **Deferred theory** | Depends on the form–ideal correspondence and class field theory. |

### Part III - Complex Multiplication

| Node | Lean decl | Mathlib coverage | Notes |
| --- | --- | --- | --- |
| `def:lattice` | `Elliptic.Lattice` | **Partial** | Mathlib uses period pairs / `ℤ`-lattices in `ℂ`. |
| `def:weierstrass_p` | `Elliptic.weierstrassP` | **In Mathlib** | `PeriodPair.weierstrassP`. |
| `thm:weierstrass_ode` | `Elliptic.weierstrassP_differential_eq` | **Partial** | `℘`, `℘'`, periodicity present; the algebraic ODE `(℘')²=4℘³−g₂℘−g₃` not assembled. |
| `def:j_invariant_lattice` | `Elliptic.jInvariant` | **Partial** | Needs lattice definitions of `g₂,g₃`; Eisenstein `E₄,E₆` are available. |
| `def:j_function` | `Modular.jFunction` | **Not in Mathlib** | `j(τ)` as a modular function not in Mathlib. |
| `def:modular_function` / `thm:j_modular` | `Modular.{IsModularFunction,jFunction_modular}` | **Partial** | `SL(2,ℤ)` action + modular forms exist; meromorphic modular *functions* not packaged. |
| `def:cm_point` / `thm:cm_integral` / `thm:j_generates` | `Modular.{IsCMPoint,isIntegral_jFunction_of_cm,jFunction_generates_ringClassField}` | **Deferred theory** | Core CM theory; not in Mathlib. |
| `def:weber_function` / `def:weber_class_polynomial` / `thm:weber_root` | `Weber.*` | **Not in Mathlib** | Weber functions absent. |
| `thm:shimura` | `Weber.shimuraReciprocity` | **Deferred theory** | 2nd-ed. addition; idele-theoretic. |

## Next steps

1. Finish the genus constructions and the remaining character and counting
   arguments in Part I. Reuse the existing reduction and composition proofs.
2. Resolve the known signature issues before attempting their proofs. Several
   earlier unrestricted statements have counterexamples documented in the source.
3. Formalize the deferred finite enumerations and exercise statements, starting
   with those whose supporting theory is now available.
4. Construct quadratic orders and their ideal class groups, extending Mathlib’s
   treatment of maximal orders to non-maximal orders. Then develop Cox’s
   form–ideal correspondence (Theorem 7.7).
5. Build the lattice `j`-invariant and the `℘` differential equation from
   Mathlib’s elliptic functions and Eisenstein series.
6. Develop class field theory, Čebotarev, and complex multiplication as separate
   prerequisites for the later chapters. Keep the unfinished statements explicit
   until those foundations are available.
