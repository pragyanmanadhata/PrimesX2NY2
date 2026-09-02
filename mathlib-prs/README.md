# Possible Mathlib contributions

This folder contains four possible Mathlib contributions that came out of my Lean
formalization of Cox's *Primes of the Form x² + ny²*. Each draft explains the
result, where its proof lives, and the choices that may need discussion.

I developed the mathematics and Lean code and made the main choices about the
statements, proofs, and interfaces. I used Claude (Fable/Opus 5) during development
to discuss ideas and refine parts of the code.

Nothing here has been submitted. The proofs work, but the names, interfaces, and
file locations still need discussion. Mathlib's
[contribution guide](https://leanprover-community.github.io/contribute/index.html)
explains the process.

| # | Contribution | Proof status | Notes |
|---|---|---|---|
| [1](PR1-exists_sq_eq_neg_three_iff.md) | `ZMod.exists_sq_eq_neg_three_iff`: `−3` is a square mod a prime `p ≠ 2, 3` iff `p ≡ 1 mod 3` | Proved with no `sorryAx` | [PR1 notes](PR1-NOTES.md) |
| [2](PR2-jacobiSym-discriminant-periodicity.md) | The Jacobi symbol of `D` has period equal to the absolute value of `D` on odd arguments when `D ≡ 0, 1 mod 4` | Proved with no `sorryAx` | [PR2 notes](PR2-NOTES.md) |
| [3](PR3-binary-quadratic-forms-reduction.md) | Definitions and Gauss reduction for binary quadratic forms | Proposed results proved with no `sorryAx` | [PR3 notes](PR3-NOTES.md) |
| 4 | A Gaussian integer whose norm is a rational prime is prime | Proved for `ℤ[i]` with no `sorryAx` | [PR4 notes](PR4-NOTES.md) |

I checked the extracted proofs against Mathlib commit `1055fdaf` with Lean
v4.34.0-rc2. PR1, PR2, and PR4 passed unchanged. PR3 needed one renamed Mathlib
lemma, `Int.emod_add_mul_ediv`; after that, all 23 checked results passed.

## The Gaussian norm lemma

Cox's Proposition 4.18 uses the fact that a Gaussian integer whose norm is a
rational prime is itself prime. Mathlib already provides the `EuclideanDomain ℤ[i]`
instance and `Zsqrtd.norm_eq_one_iff'`, but I did not find a named lemma with this
statement. My proof is in `PrimesX2NY2/PartI_Forms/BiquadraticReciprocity.lean` and
uses `irreducible_iff_prime` together with multiplicativity of the norm.

This argument applies to `ℤ[i]`, and more generally to `ℤ√d` when the ring is known
to be a UFD. It does not automatically apply for every `d ≤ 0`, because
`irreducible_iff_prime` needs a `[DecompositionMonoid]` instance. For example,
`ex_4_6_b` shows that `2` is irreducible but not prime in `ℤ[√−3]`. I have not tried
to settle whether the norm statement has a different proof in that ring.

## How this relates to the rest of the project

None of these contributions is needed to continue Part I; their proofs already live
in the project. Moving them into Mathlib would make them available to other
formalizations.

The remaining `sorry`s in `PartII_ClassFieldTheory/` and
`PartIII_ComplexMultiplication/` involve separate, much larger developments. Some
are project definitions that still need to be built using Mathlib's existing work on
Dedekind domains, class groups, number fields, and Galois theory. Others depend on
the following subjects, which I did not find in the project's pinned Mathlib
version (v4.31.0):

- global class field theory, including Artin reciprocity and the existence theorem;
- Chebotarev density;
- the modular `j`-invariant and complex multiplication.

The project leaves these pieces marked with `sorry` rather than replacing them with
axioms, as described in [CONVENTIONS.md](../CONVENTIONS.md). They are outside the
scope of the four proposals in this folder.
