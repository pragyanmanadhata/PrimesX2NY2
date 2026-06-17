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
