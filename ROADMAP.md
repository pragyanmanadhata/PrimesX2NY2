# Roadmap & Mathlib audit

Status of each blueprint node against **Mathlib `v4.31.0`** (commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`), which was searched directly for the
relevant theory. Legend:

- **[In Mathlib]** — the result (or an immediately usable form) already exists.
- **[Partial]** — substantial building blocks exist; the specific statement does not.
- **[Needs formalizing]** — not in Mathlib; standard but real work.
- **[Deep: cite-or-defer]** — downstream of theory Mathlib does not yet have
  (class field theory, Čebotarev); state and assume/cite for now.

## What was actually found in Mathlib

| Topic searched | Found? | Location |
| --- | --- | --- |
| Sum of two squares (Fermat) | **Yes** | `Nat.Prime.sq_add_sq` in `NumberTheory/SumTwoSquares.lean` (`p % 4 ≠ 3 → ∃ a b, p = a²+b²`) |
| Quadratic reciprocity / Legendre / Jacobi | **Yes** | `NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`, `Zsqrtd/QuadraticReciprocity.lean` |
| Gaussian integers / `ℤ√d` | **Yes** | `NumberTheory/Zsqrtd/{Basic,GaussianInt}.lean` |
| `ZMod`, `IsSquare`, residues | **Yes** | `Data/ZMod/*`, used throughout |
| General quadratic forms | **Yes** | `LinearAlgebra/QuadraticForm/*` (not specialized to binary integral forms) |
| **Binary** quadratic forms (a,b,c), reduction, proper equiv. | **No** | — |
| Form class group, Dirichlet composition | **No** | — |
| Genus theory | **No** | — |
| Ideal class group (Dedekind / ring of integers) | **Yes** | `RingTheory/ClassGroup.lean`, `NumberTheory/NumberField/ClassNumber.lean`, `NumberTheory/ClassNumber/*` |
| Ideal class group of a **non-maximal order** (conductor `f`) | **No** | — |
| Dirichlet's theorem (primes in AP) | **Yes** | `NumberTheory/PrimesCongruentOne.lean`, `NumberTheory/LSeries/Dirichlet.lean` |
| Hilbert / ring class field, Artin reciprocity, Čebotarev | **No** | — (no class field theory in Mathlib) |
| `SL(2,ℤ)` action on `ℍ`, fundamental domain | **Yes** | `NumberTheory/Modular.lean`, `Analysis/Complex/UpperHalfPlane/*` |
| Modular forms, Eisenstein series, `Δ`, Dedekind `η`, q-expansions | **Yes** | `NumberTheory/ModularForms/*` (incl. `EisensteinSeries/*`, `Delta.lean`, `DedekindEta.lean`) |
| Weierstrass `℘` (analytic), `℘'`, periodicity, analyticity | **Yes** | `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (`PeriodPair.weierstrassP`, `derivWeierstrassP`, …) |
| Algebraic `j`-invariant of an elliptic curve | **Yes** | `AlgebraicGeometry/EllipticCurve/{ModelsWithJ,IsomOfJ}.lean` |
| Modular **`j`-function** `j(τ)` on `ℍ` (as a modular function) | **No** | — (Eisenstein/`Δ` present; `j = E₄³/Δ` not assembled) |
| Complex multiplication; CM values of `j` are algebraic integers | **No** | — |
| Weber functions; Shimura reciprocity | **No** | — |

## Node-by-node status

### Part I — From Fermat to Gauss

| Node (blueprint label) | Lean decl | Status | Notes |
| --- | --- | --- | --- |
| `thm:descent` | `Fermat.descent_step` | **Needs formalizing** | Classic, but no packaged descent lemma. |
| `thm:fermat_two_squares` | `Fermat.prime_sq_add_sq` | **In Mathlib** | Reduce to `Nat.Prime.sq_add_sq`. |
| `thm:fermat_x2_2y2` | `Fermat.prime_sq_add_two_sq` | **Partial** | Provable via `Zsqrtd`/reciprocity; not stated in Mathlib. |
| `thm:fermat_x2_3y2` | `Fermat.prime_sq_add_three_sq` | **Partial** | Same machinery as above. |
| `def:binary_qf` | `Forms.BinaryQF` | **Needs formalizing** | Mathlib `QuadraticForm` is more general; want `(a,b,c)`. |
| `def:discriminant` | `Forms.BinaryQF.discr` | **Needs formalizing** | Trivial once `BinaryQF` exists. |
| `def:proper_equiv` | `Forms.BinaryQF.ProperlyEquivalent` | **Partial** | `SL(2,ℤ)` exists (`Matrix.SpecialLinearGroup`); the action on forms does not. |
| `def:reduced` / `thm:reduction` | `Forms.BinaryQF.Reduced`, `Forms.exists_unique_reduced` | **Needs formalizing** | Gauss reduction; uniqueness is the work. |
| `thm:finite_class_number` | `Forms.finite_reduced_of_discr` | **Needs formalizing** | Follows from reduction bounds. |
| `def:form_class_group` / `def:dirichlet_composition` / `thm:form_class_group_is_group` | `Forms.FormClassGroup`, `Forms.compose`, `Forms.FormClassGroup.isCommGroup` | **Needs formalizing** | The hard classical core of Part I. |
| `def:represents` / `def:genus` / `def:principal_genus` | `Genus.*` | **Needs formalizing** | — |
| `thm:representation_residue` | `Genus.properlyRepresents_iff_isSquare` | **Partial** | Residue criterion sits on quadratic reciprocity (in Mathlib). |
| `thm:genus_congruence` | `Genus.represents_principal_iff_congruence` | **Needs formalizing** | Genus theory; partly congruences + Dirichlet (in Mathlib). |

#### §3 — Composition, genera, convenient numbers

| Node (blueprint label) | Lean decl | Status | Notes |
| --- | --- | --- | --- |
| `lem:l3_2` / `lem:l3_5` | `Forms.lemma_3_2`, `Forms.lemma_3_5` | **Needs formalizing** | CRT-style; building blocks of composition. |
| `def:dirichlet_form` / `prop:p3_8` | `Forms.dirichletForm`, `Forms.prop_3_8` | **Needs formalizing** | Explicit composition formula (3.7) and its well-definedness. |
| `thm:form_class_group_is_group` | `Forms.isCommGroup` | **Needs formalizing** | **Faithful rewrite**: the old `Nonempty (CommGroup …)` was vacuous (true for any nonempty type). Now states assoc/comm/identity/inverse on `compose`. Carrier `DiscrForms` tightened to *primitive, `a>0`* forms. |
| `thm:t3_9_inverse` | `Forms.thm_3_9_inverse` | **Needs formalizing** | Inverse = opposite class. |
| `lem:l3_10` / `def:mu` / `prop:p3_11` | `Forms.lemma_3_10`, `Forms.mu`, `Forms.prop_3_11` | **Needs formalizing** | Order-≤2 forms; the exponent `μ` and `2^{μ−1}` two-torsion count. |
| `def:assigned_characters` / `def:genus_map` | `Genera.Psi`, `Genera.genusVector` | **Needs formalizing** | Cox (3.16)/(3.12); `δ`, `ε` defined concretely. |
| `lem:l3_13` / `cor:c3_14_i` / `cor:c3_14_ii` | `Genera.lemma_3_13`, `Genera.cor_3_14_i`, `…_ii` | **Needs formalizing** | Genus map is a homomorphism; genera equinumerous; count a power of two. |
| `lem:l3_17` / `thm:t3_15_i` / `thm:t3_15_ii` | `Genera.lemma_3_17`, `Genera.thm_3_15_i`, `…_ii` | **Needs formalizing** | `Ψ` surjective, kernel `H`; `2^{μ−1}` genera; principal genus `= C(D)²`. |
| `lem:l3_20` | `Genera.lemma_3_20` | **Needs formalizing** | Complete character determines the genus. |
| `thm:t3_21` | `Genera.thm_3_21` | **GAP (partial statement)** | Only Cox's conditions (i)⟺(ii) are formalized. Conditions (iii)–(vi) (equivalence mod `m`, over `ℤ_p`, over `ℚ`) need a `ZMod`/`PadicInt`/`ℚ` action on forms not yet built — deferred, *not* axiomatized. |
| `thm:t3_22` | `Genera.thm_3_22` | **GAP (partial statement)** | Four of Cox's five conditions formalized; the group-isomorphism condition `C(-4n) ≅ (ℤ/2ℤ)^k` is deferred (needs a registered `CommGroup` instance on `FormClassGroup`). |
| `def:convenient_number` / `prop:p3_24` | `Genera.ConvenientNumber`, `Genera.prop_3_24` | **Needs formalizing** | Euler's idoneal numbers; one-class-per-genus characterization. |
| `lem:l3_25` / `cor:c3_26` | `Genera.lemma_3_25`, `Genera.cor_3_26` | **Needs formalizing (deep counting)** | Representation counts `2∏(1+(-n/p))`, `2^{r+1}`; proved in §3 via Exercise 3.20. Statements typecheck; proofs are the hard analytic-counting part. |

**Deferred computational enumerations** (stated as `\notready` blueprint nodes, *not*
un-formalizable — good early proof targets once stated as `Decidable`/`Finset`
decls): Exercise **2.9(b)** and Exercise **2.19** (reduced forms / genera of the
discriminants `-3,-15,-24,-31,-52`), and the §3 analogues Exercise **3.14**
(genera of disc `-164`) and **3.25(b)**. These enumerate the finite set of reduced
forms of a fixed discriminant; each is a concrete `Finset`/`Decidable` computation
deferred to a later proof pass.

**§3 exercise gaps** (`\notready`, no Lean decl): sub-parts that *prove* a spine
lemma (3.3, 3.10, 3.11, 3.15, 3.20(b–f)), need the **direct-composition predicate**
(3.2, 3.6), the **`ℚ`/`ℤ_p` form action** (3.17, 3.18, part of 3.21), the abstract
**group structure on `C(D)`** (3.9, 3.19, 3.25(a,c)), or the **Kronecker symbol**
(3.24). None are axiomatized.

### Part II — Class Field Theory

| Node | Lean decl | Status | Notes |
| --- | --- | --- | --- |
| `def:quad_order` / `def:order_discriminant` | `Order.QuadOrder`, `Order.QuadOrder.discr` | **Partial** | Orders not packaged; `ℤ√d`, `NumberField`, Dedekind theory exist. |
| `def:ideal_class_group_order` / `thm:ideal_class_group_finite` | `Order.QuadOrder.idealClassGroup`, `…isCommGroup` | **Partial** | Class group + finiteness exist for the **maximal** order; non-maximal needs work. |
| `thm:form_ideal_bridge` (Cox 7.7) | `Bridge.formClassGroup_equiv_idealClassGroup` | **Needs formalizing** | Depends on Part I + orders. |
| `thm:bridge_composition` | `Bridge.bridge_respects_composition` | **Needs formalizing** | — |
| `def:hilbert_class_field` / `def:ring_class_field` | `RingClassField.{hilbertClassField,ringClassField}` | **Deep: cite-or-defer** | No class field theory in Mathlib. |
| `thm:artin_reciprocity` | `RingClassField.artinReciprocity` | **Deep: cite-or-defer** | — |
| `def:splits_completely` / `thm:chebotarev` | `RingClassField.{SplitsCompletely,chebotarev_splitting}` | **Deep: cite-or-defer** | Čebotarev not in Mathlib (Dirichlet's theorem is). |
| `def:class_polynomial` / `thm:main_splitting` / `thm:main_class_poly` | `MainTheorem.*` | **Deep: cite-or-defer** | The main theorem; downstream of nodes 6–7. |

### Part III — Complex Multiplication

| Node | Lean decl | Status | Notes |
| --- | --- | --- | --- |
| `def:lattice` | `Elliptic.Lattice` | **Partial** | Mathlib uses period pairs / `ℤ`-lattices in `ℂ`. |
| `def:weierstrass_p` | `Elliptic.weierstrassP` | **In Mathlib** | `PeriodPair.weierstrassP`. |
| `thm:weierstrass_ode` | `Elliptic.weierstrassP_differential_eq` | **Partial** | `℘`, `℘'`, periodicity present; the algebraic ODE `(℘')²=4℘³−g₂℘−g₃` not assembled. |
| `def:j_invariant_lattice` | `Elliptic.jInvariant` | **Partial** | Needs `g₂,g₃` (Eisenstein `E₄,E₆` exist) wired to the lattice. |
| `def:j_function` | `Modular.jFunction` | **Needs formalizing** | `j(τ)` as a modular function not in Mathlib. |
| `def:modular_function` / `thm:j_modular` | `Modular.{IsModularFunction,jFunction_modular}` | **Partial** | `SL(2,ℤ)` action + modular forms exist; meromorphic modular *functions* not packaged. |
| `def:cm_point` / `thm:cm_integral` / `thm:j_generates` | `Modular.{IsCMPoint,isIntegral_jFunction_of_cm,jFunction_generates_ringClassField}` | **Deep: cite-or-defer** | Core CM theory; not in Mathlib. |
| `def:weber_function` / `def:weber_class_polynomial` / `thm:weber_root` | `Weber.*` | **Needs formalizing** | Weber functions absent. |
| `thm:shimura` | `Weber.shimuraReciprocity` | **Deep: cite-or-defer** | 2nd-ed. addition; idele-theoretic. |

## Suggested order of attack

1. **Part I, node 1** — wire `Fermat.prime_sq_add_sq` to `Nat.Prime.sq_add_sq`
   (nearly free), then the descent lemma and `x²+2y²`, `x²+3y²`.
2. **Part I, nodes 2–4** — `BinaryQF`, the `SL(2,ℤ)` action, reduction, the form
   class group, genus criteria. This is self-contained and the largest pure-Mathlib
   win; nothing here needs class field theory.
3. **Part II, node 5** — orders and their ideal class groups, building on Mathlib's
   Dedekind-domain class group, extending to non-maximal orders.
4. **Bridge (node 6)** — Cox Thm 7.7, once 2–5 exist.
5. **Part III, node 9** — lattice `j`-invariant and the `℘` differential equation,
   reusing Mathlib's `℘` and Eisenstein series.
6. **Deep nodes (7, 8, 10, 11)** — keep as cited/assumed statements until Mathlib
   gains class field theory, Čebotarev, and CM; revisit then.
