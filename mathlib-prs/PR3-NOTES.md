# Notes on binary quadratic forms

[Proposed series](PR3-binary-quadratic-forms-reduction.md) · [All proposals](README.md)

I could not find a Mathlib development of binary quadratic forms in the classical
Gauss sense. This proposal covers the basic definitions, equivalence, reduction,
and finiteness of reduced forms.

## What I am proposing

I developed the definitions and proof structure in this project, with Claude
helping me work through technical details. Since this would introduce a fairly
large new API, I would first ask in `#mathlib` about its scope and conventions.

## Design choices I would like feedback on

### How should a form be represented?

The project uses a standalone `BinaryQF` structure with fields `a b c : ℤ`. Direct
access to the coefficients is useful for the `omega`, `interval_cases`, and `decide`
arguments in the reduction proofs. Using `QuadraticForm ℤ (Fin 2 → ℤ)` would connect
the development to Mathlib's linear-algebra library, but it would need a convenient
coefficient API. I am not sure which should be the primary definition.

### Which action convention fits Mathlib best?

The project proves

```
action_mul : action N (action M f) = action (M * N) f
```

This is a right action. A conventional `MulAction` of
`Matrix.SpecialLinearGroup (Fin 2) ℤ` is a left action, so I could change the
convention, act through the opposite group, or transpose the matrices. I would like
to settle this before moving the proofs because it affects the later development.

### Should the matrices be bundled?

At present, `action` accepts any `Matrix (Fin 2) (Fin 2) ℤ`, and
`ProperlyEquivalent` separately asks for determinant `1`. Taking an element of the
special linear group instead would put that condition in the type.

### Boundary convention for reduced forms

The project defines reduction by
`|b| ≤ a ∧ a ≤ c ∧ ((|b| = a ∨ a = c) → 0 ≤ b)`. The last condition chooses one
representative on the boundary and is needed for uniqueness. For example, it
distinguishes `⟨3,2,3⟩` from `⟨3,-2,3⟩`. Some texts treat this as a separate
normalization step.

### How should positive definiteness be defined?

I currently use `0 < f.a ∧ f.discr < 0` and prove that every nonzero input has
positive value. Another reasonable choice is to define positivity through evaluation
and prove the coefficient condition as an equivalence.

### How should primitiveness be expressed?

The current definition is `Int.gcd (Int.gcd f.a f.b) f.c = 1`. Because `Int.gcd`
returns a natural number, this introduces coercions later. `IsCoprime` or
`Finset.gcd` may give a cleaner interface.

### What belongs in the first PR?

I would probably begin with the definitions, action, and equivalence. The reduction
proofs can follow after the conventions are settled.

## Proof check

I first checked these results with the project's pinned Lean v4.31.0 toolchain and
Mathlib revision. I then tested the extracted core against Mathlib commit `1055fdaf`
with Lean v4.34.0-rc2. That revision uses `Int.emod_add_mul_ediv` in place of
`Int.emod_add_ediv`; after that one change, all 23 `#print axioms` checks passed
without `sorryAx`. `class_number_one` is unfinished and is not part of this proposal.
