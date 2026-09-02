# Notes on `ZMod.exists_sq_eq_neg_three_iff`

[Proposal and proof](PR1-exists_sq_eq_neg_three_iff.md) · [All proposals](README.md)

The proposed lemma says that `-3` is a square modulo a prime `p ≠ 2, 3` exactly
when `p ≡ 1 (mod 3)`. The project version is
`PrimesX2NY2.Fermat.neg_three_isSquare_iff`.

## Why this lemma

Mathlib already has `exists_sq_eq_neg_one_iff`, `exists_sq_eq_two_iff`, and
`exists_sq_eq_neg_two_iff`. I could not find the corresponding result for `-3` in
the Mathlib version I checked. It comes up naturally for Eisenstein integers,
cubic reciprocity, and representations by `x² + 3y²`.

## Statement and assumptions

Both exclusions are needed:

- If `p = 2`, then `-3 ≡ 1 = 1²`, but `2 % 3 = 2`.
- If `p = 3`, then `-3 ≡ 0 = 0²`, but `3 % 3 = 0`.

The project uses `Odd p`, while the draft uses `p ≠ 2` to match the nearby Mathlib
lemmas. These are equivalent when `p` is prime.

In the project I write `IsSquare ((-3 : ℤ) : ZMod p)` because the surrounding code
uses integer-valued discriminants. The draft uses `IsSquare (-3 : ZMod p)`, matching
the existing small-value lemmas, and handles the cast with `push_cast`.

## Proof idea

My proof uses quadratic reciprocity for the Legendre symbol. It rewrites
`(-3/p)` as `(-1/p)(3/p)`. Reciprocity shows that the two sign factors cancel, so
`(-3/p) = (p/3)`. The last symbol is then determined by `p mod 3` using the two
nonzero elements of `ZMod 3`.

Another possible route would be to prove `quadraticChar_neg_three` and
`FiniteField.isSquare_neg_three_iff` first, then derive the `ZMod` statement. That
would fit the existing finite-field treatment of `2` and `-2`, although the exact
statement would need to exclude characteristics `2` and `3`.

## Placement and naming

The natural file is
`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`. The proof must appear
after `legendreSym.quadratic_reciprocity'`, which it uses, rather than directly beside
the earlier `2` and `-2` lemmas.

I used `exists_sq_eq_neg_three_iff` to match the nearby theorem names, even though
the theorem is phrased with `IsSquare` rather than an explicit existential equation.

## Proof check

I checked the exact draft proof against Mathlib commit `1055fdaf` with Lean
v4.34.0-rc2. It compiled without warnings or `sorryAx`; its axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound`. The final location in the
Mathlib file still needs to be chosen with the dependency order in mind.
