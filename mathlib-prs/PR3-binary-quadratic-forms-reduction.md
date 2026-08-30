# Mathlib PR draft #3 — Gauss reduction theory of binary quadratic forms

**Status:** Draft; not submitted. The proposed results are proved in
`PrimesX2NY2/PartI_Forms/Forms.lean` without `sorryAx` dependencies. The contribution
would add definitions, equivalence, reduction, and finiteness results across a series
of PRs. Its design needs discussion and human review before submission.

## Titles (a series, in dependency order)

1. `feat(NumberTheory): binary quadratic forms — definition, discriminant, SL₂(ℤ) action`
2. `feat(NumberTheory): proper equivalence of binary quadratic forms`
3. `feat(NumberTheory): reduced positive definite forms and Gauss reduction`
4. `feat(NumberTheory): finiteness of reduced forms of fixed discriminant`

## Target files

New directory `Mathlib/NumberTheory/BinaryQuadraticForm/` with `Defs.lean`,
`Equivalence.lean`, `Reduction.lean`, `Finiteness.lean`.

## Motivation

The search of the pinned Mathlib tree found no treatment of binary quadratic forms
in the classical Gauss sense:

- `Mathlib/LinearAlgebra/QuadraticForm/*` — abstract quadratic forms over modules.
  Nothing about integral binary forms, their discriminant `b² − 4ac`, the
  `SL₂(ℤ)`-action, reduction, or class numbers.
- `Mathlib/NumberTheory/ClassNumber/*`, `Mathlib/RingTheory/ClassGroup/*` — class
  groups of Dedekind domains (i.e. *maximal* orders), via ideals. This is the
  ideal-theoretic side of the correspondence; the form-theoretic side is absent.
- A search for "binary quadratic" found only an unrelated comment in
  `LegendreSymbol/Basic.lean`.

This proposal covers the classical theory in Gauss's *Disquisitiones*, Art. 171 ff.,
and Cox, *Primes of the Form x²+ny²*, §2.

This provides a basis for computable class numbers `h(D)`, the form/ideal class
group correspondence with Mathlib's `ClassGroup`, genus theory, and representation
theorems `p = x² + ny²`. The project already uses the reduction results to prove two
such representation theorems, listed below.

## Contents

The statements below summarize results proved in the project, with proposed
Mathlib names (`BinaryQF` → `BinaryQuadraticForm`, namespaced lemmas). Some snippets
abbreviate arguments and definitions; they are an API outline, not a standalone
Lean file.

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

The uniqueness result and the elementary equivalences are also available separately:

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
    {f : BinaryQuadraticForm | f.discr = D ∧ f.Reduced ∧ f.PosDef}.Finite
```

Together with reduction, this gives finiteness of the class number `h(D)`, the
form-side analogue of Mathlib's `NumberField.classNumber` finiteness.

## Uses in this project

The project uses these lemmas in the following results, all checked without
`sorryAx` dependencies:

- `p = x² + 2y² ↔ p ≡ 1, 3 (mod 8)` for odd primes `p`;
- `p = x² + 3y² ↔ p ≡ 1 (mod 3)` for primes `p > 3`;
- `(D/p) = 1 ↔ p` is represented by a primitive form of discriminant `D` (Cox Lemma 2.3);
- distinctness of the four composition classes of discriminant `−1076`.

The first two combine reduction with an enumeration of reduced forms of
discriminant `−8` and `−12`. They exercise the proposed interface in concrete
representation proofs, though the interface still needs upstream review.

## Verification status

The proposed `Mathlib/NumberTheory/BinaryQuadraticForm/` content comes from
`PrimesX2NY2/PartI_Forms/Forms.lean`. That file still contains one `sorry`, in
Landau's theorem `class_number_one` (`h(−4n) = 1 ↔ n ∈ {1,2,3,4,7}`), which is
outside this proposed series. The supporting results listed here compile in the
project; their recorded `#print axioms` checks report
`[propext, Classical.choice, Quot.sound]`. The renamed and reorganized upstream
files have not yet been prepared or checked.

## Open questions for the reviewer

1. **Structure vs. abstract `QuadraticForm`.** Should `BinaryQuadraticForm` be a
   standalone structure (as here, matching the classical literature and keeping
   `a, b, c` accessible for `decide`/`omega`-style arguments), or a bundled
   `QuadraticForm ℤ (Fin 2 → ℤ)` with an API layer? The standalone version made the
   reduction proofs tractable; the bundled version integrates with existing
   `LinearAlgebra` machinery. A conversion between the two may be useful, but the
   choice of primary definition still matters for naming and the interface.
2. **The action's variance.** This project uses
   `action N (action M f) = action (M * N) f` (contravariant). Mathlib may prefer a
   `MulAction` of `SL(2, ℤ)` (or its opposite) on forms; that means either
   changing the convention or acting through `Mᵀ`. This needs settling before the
   first PR because it affects downstream proofs.
3. **`Reduced`'s boundary condition.** The `((|b| = a ∨ a = c) → 0 ≤ b)` clause is
   what makes the reduced representative *unique*. Some sources fold this into a
   normalization instead. The definition needs to make this convention clear
   whichever formulation is chosen.
4. **Indefinite forms.** This project's `Reduced` is the positive-definite notion.
   The indefinite theory (period/cycle of reduced forms, continued fractions) is a
   separate and larger development, not proposed here — but the naming should leave
   room for it (`Reduced` vs. `PosDef.Reduced`?).
5. **Scope of the first PR.** Probably (1) + (2) only, to settle conventions before
   the reduction proofs land.
