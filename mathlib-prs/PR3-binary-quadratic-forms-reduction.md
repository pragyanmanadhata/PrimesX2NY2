# Proposed Mathlib series: binary quadratic forms and Gauss reduction

[Design notes](PR3-NOTES.md) · [Contribution overview](README.md)

The results are proved in `PrimesX2NY2/PartI_Forms/Forms.lean` without `sorryAx`.
Because the development runs from basic definitions through reduction and finiteness,
I expect to split it across several PRs and ask for feedback on the design first.

## Possible PR sequence

1. `feat(NumberTheory): binary quadratic forms — definition, discriminant, SL₂(ℤ) action`
2. `feat(NumberTheory): proper equivalence of binary quadratic forms`
3. `feat(NumberTheory): reduced positive definite forms and Gauss reduction`
4. `feat(NumberTheory): finiteness of reduced forms of fixed discriminant`

## Possible file layout

I would put these files in a new
`Mathlib/NumberTheory/BinaryQuadraticForm/` directory: `Defs.lean`,
`Equivalence.lean`, `Reduction.lean`, and `Finiteness.lean`.

## Motivation

I could not find an existing Mathlib development of binary quadratic forms in the
classical Gauss sense:

- `Mathlib/LinearAlgebra/QuadraticForm/*` develops abstract quadratic forms over
  modules. These files do not appear to cover integral binary forms, their
  discriminant `b² − 4ac`, the `SL₂(ℤ)` action, reduction, or class numbers.
- `Mathlib/NumberTheory/ClassNumber/*` and `Mathlib/RingTheory/ClassGroup/*` develop
  class numbers and ideal class groups for Dedekind domains, including rings of
  integers in number fields. I did not find the corresponding classical theory of
  forms.
- A text search found a brief mention in `LegendreSymbol/Basic.lean`, but no
  development of the subject.

This proposal formalizes the basic definitions and reduction theory used in Gauss's
*Disquisitiones*, Art. 171 ff., and Cox, *Primes of the Form x²+ny²*, §2. I already
use the results for small-discriminant calculations and representation theorems.
They could later support work on class numbers, ideal classes, genus theory, and
representation by forms.

## Contents

Below are the main statements I would like to contribute. I have expanded `BinaryQF`
to `BinaryQuadraticForm` and shortened some arguments, so the snippets show the
proposed API rather than a standalone Lean file.

### 1. Definitions

```lean
/-- An integral binary quadratic form `a x² + b x y + c y²`. -/
structure BinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ

def BinaryQuadraticForm.eval (f : BinaryQuadraticForm) (x y : ℤ) : ℤ :=
  f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

def BinaryQuadraticForm.discr (f : BinaryQuadraticForm) : ℤ := f.b ^ 2 - 4 * f.a * f.c

def BinaryQuadraticForm.Primitive (f : BinaryQuadraticForm) : Prop :=
  Int.gcd (Int.gcd f.a f.b) f.c = 1

def BinaryQuadraticForm.PosDef (f : BinaryQuadraticForm) : Prop := 0 < f.a ∧ f.discr < 0

def BinaryQuadraticForm.Reduced (f : BinaryQuadraticForm) : Prop :=
  |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ ((|f.b| = f.a ∨ f.a = f.c) → 0 ≤ f.b)
```

### 2. The action and its invariants

```lean
def action (M : Matrix (Fin 2) (Fin 2) ℤ) (f : BinaryQuadraticForm) : BinaryQuadraticForm

theorem eval_action (M) (f) (x y) : (action M f).eval x y = f.eval (…) (…)
theorem action_mul (M N) (f) : action N (action M f) = action (M * N) f
theorem discr_action (M) (f) : (action M f).discr = M.det ^ 2 * f.discr

def ProperlyEquivalent (f g) : Prop := ∃ M, M.det = 1 ∧ action M f = g
def Equivalent (f g) : Prop := ∃ M, (M.det = 1 ∨ M.det = -1) ∧ action M f = g

theorem properlyEquivalent_equivalence : Equivalence ProperlyEquivalent
theorem equivalent_equivalence : Equivalence Equivalent
theorem discr_eq_of_properlyEquivalent {f g} (h : ProperlyEquivalent f g) : f.discr = g.discr
theorem primitive_action_iff (M) (f) (hM : M.det = 1) : (action M f).Primitive ↔ f.Primitive
```

### 3. Reduction (Gauss; Cox Thm 2.8)

```lean
/-- Every positive definite form is properly equivalent to a *unique* reduced form. -/
theorem exists_unique_reduced (f : BinaryQuadraticForm) (hf : f.PosDef) :
    ∃! g, g.Reduced ∧ ProperlyEquivalent f g
```

The project also proves the uniqueness theorem and the two elementary equivalences
separately:

```lean
theorem reduced_eq_of_properlyEquivalent (f g) (hf : f.Reduced) (hg : g.Reduced)
    (hfp : f.PosDef) (h : ProperlyEquivalent f g) : f = g
theorem translate_equiv (a b c t : ℤ) :
    ProperlyEquivalent ⟨a, b, c⟩ ⟨a, b + 2 * a * t, a * t ^ 2 + b * t + c⟩
theorem swap_equiv (a b c : ℤ) : ProperlyEquivalent ⟨a, b, c⟩ ⟨c, -b, a⟩
```

For existence, translate by `T = !![1, t; 0, 1]` to obtain `|b| ≤ a`, then swap by
`S = !![0, -1; 1, 0]` whenever `c < a`. The proof uses strong induction on
`a.natAbs`. Uniqueness follows by comparing the values of `f.eval` at `±(1,0)`
and `±(0,1)`.

### 4. Finiteness

```lean
theorem finite_reduced_of_discr (D : ℤ) (hD : D < 0) :
    {f : BinaryQuadraticForm | f.discr = D ∧ f.Reduced}.Finite
```

Together with reduction, this is the finiteness result needed to define the form
class number `h(D)`.

## Uses in this project

I already use these lemmas in the following results, whose axiom checks do not
include `sorryAx`:

- `p = x² + 2y² ↔ p ≡ 1, 3 (mod 8)` for odd primes `p`;
- `p = x² + 3y² ↔ p ≡ 1 (mod 3)` for primes `p > 3`;
- for `D ≡ 0` or `1 (mod 4)` and an odd prime `p ∤ D`, `D` is a square modulo `p`
  exactly when `p` is represented by a primitive form of discriminant `D`
  (Cox, Exercise 2.5);
- three explicit non-equivalence results among four forms of discriminant `−1076`
  (Cox, Exercise 2.26).

The first two use reduction together with an enumeration of the reduced forms of
discriminants `−8` and `−12`. Working through those examples also helped me test the
interface, though it still needs upstream feedback.

## Proof check

The code is currently in `PrimesX2NY2/PartI_Forms/Forms.lean`. The only `sorry` in
that file is in `class_number_one`, which is outside this series. For the results
listed here, `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`.

I also tested the extracted core against Mathlib commit `1055fdaf` with Lean
v4.34.0-rc2. That revision uses `Int.emod_add_mul_ediv` in place of
`Int.emod_add_ediv`. After that one name change, all 23 `#print axioms` checks passed
without `sorryAx`. I still need to split and rename the code into the proposed
Mathlib files.

## Questions I would like feedback on

- Should `BinaryQuadraticForm` be a standalone coefficient structure, or should it
  be built on `QuadraticForm ℤ (Fin 2 → ℤ)` with an API for `a`, `b`, and `c`?
- Should the change of variables be a right action, an action of the opposite group,
  or a conventional left `MulAction`?
- Is the boundary condition in `Reduced` best kept in the definition, or should it
  be a separate normalization?
- Should this positive-definite reduction predicate be called `Reduced`, or something
  like `PosDef.Reduced` to leave room for reduction of indefinite forms?
- I would start with the definitions, action, and proper equivalence, then add
  reduction later. Does that seem like the right first slice?
