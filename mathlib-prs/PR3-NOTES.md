# PR3 notes — Binary quadratic forms

[Proposed series](PR3-binary-quadratic-forms-reduction.md) · [All proposals](README.md)

**Claim.** The pinned Mathlib revision has no binary quadratic forms in the classical
Gauss sense; this proposal covers definitions and reduction theory.
**Risk: high.** The proposed library design needs discussion with the Mathlib community.

## Scope and review

This proposal adds a library of definitions and theorems. I developed its
structure and proof approach, with technical input from Claude.
Discuss the scope and conventions in `#mathlib` on Zulip. An RFC can be used
for unresolved design questions; review and maintainer approval are part of
the PR process.

## Design choices and unresolved questions

**D3.1 — Standalone `structure BinaryQF` with fields `a b c : ℤ`.** Direct coefficient
access supports the `omega`, `interval_cases`, and `decide` arguments used throughout
the reduction proofs. A bundled `QuadraticForm ℤ (Fin 2 → ℤ)` would connect to
`LinearAlgebra.QuadraticForm` but would need an interface for those arguments. The
choice of primary definition remains unresolved and is a first question for Zulip.

**D3.2 — Action convention.** The project proves

```
action_mul : action N (action M f) = action (M * N) f
```

This is a right action. A `MulAction` of `SpecialLinearGroup (Fin 2) ℤ` is a left
action, so that interface would require changing the convention or acting through
`Mᵀ`. Such a change affects downstream proofs. This is the second unresolved
question for Zulip.

**D3.3 — `action` takes an arbitrary `Matrix (Fin 2) (Fin 2) ℤ`.** Consequently
`ProperlyEquivalent` carries `M.det = 1` as a side condition rather than using
`Matrix.SpecialLinearGroup`. Bundling the matrices in the group would be a separate
change to the interface.

**D3.4 — `Reduced` includes the boundary condition.**
`|b| ≤ a ∧ a ≤ c ∧ ((|b| = a ∨ a = c) → 0 ≤ b)`. The third clause is exactly what makes
the reduced representative unique; without it `exists_unique_reduced` is false. Some
textbooks use a separate normalization step. The clause distinguishes `⟨3,2,3⟩` from
`⟨3,-2,3⟩`, the boundary case in the calculation `h(−32) = 2`.

**D3.5 — `PosDef f := 0 < f.a ∧ f.discr < 0`.** The project defines positive
definiteness by a coefficient criterion. `eval_pos_of_posDef` proves that it implies
`f(x,y) > 0` for `(x,y) ≠ 0`. A reviewer may prefer positivity as the definition,
with the coefficient criterion stated as an equivalence lemma.

**D3.6 — `Primitive f := Int.gcd (Int.gcd f.a f.b) f.c = 1`.** Nested `Int.gcd`, which
returns `ℕ`, so downstream proofs need coercions. Alternatives based on `IsCoprime`
or `Finset.gcd` are available.

**D3.7 — Scope of a first PR.** Definitions, action, and equivalence. Reduction proofs
would follow once the conventions are settled.

## Recorded verification

The results proposed for this series have recorded axiom checks listing
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`, under the pinned
Lean v4.31.0 / Mathlib setup. `class_number_one` remains outside the series.
These checks establish proof completeness for the proposed results, while
library integration and suitability remain matters for Mathlib review.
