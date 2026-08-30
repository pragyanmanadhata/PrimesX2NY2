# PR1 notes — `ZMod.exists_sq_eq_neg_three_iff`

[Proposal and proof](PR1-exists_sq_eq_neg_three_iff.md) · [All proposals](README.md)

**Claim.** `-3` is a square mod a prime `p ≠ 2, 3` iff `p ≡ 1 (mod 3)`.
**In-repo:** `PrimesX2NY2.Fermat.neg_three_isSquare_iff`.
**Risk: low.** A single lemma with a proposed interface matching an existing family.

## Decisions

**D1.1 — Fill a gap in an existing family.** Mathlib has `exists_sq_eq_neg_one_iff`,
`exists_sq_eq_two_iff`, `exists_sq_eq_neg_two_iff` and no `-3` in the pinned revision.
The proposed statement follows that family's shape. The `-3` discriminant case is
used for `ℤ[ω]`, cubic reciprocity, and `p = x²+3y²`.

**D1.2 — Hypotheses `p ≠ 2` and `p ≠ 3`.** Both exclusions are necessary:

- `p = 2`: `-3 ≡ 1 = 1²` is a square, but `2 % 3 = 2`. Statement fails.
- `p = 3`: `-3 ≡ 0 = 0²` is a square, but `3 % 3 = 0`. Statement fails.

`3 < p` would also work, but two `≠` hypotheses match the neighbours' style
(`exists_sq_eq_two_iff` takes `hp : p ≠ 2`).

**D1.3 — The in-repo version uses `Odd p`; the draft uses `p ≠ 2`.** These are equivalent
given `p` prime. The draft was restated for Mathlib because the neighbours use `p ≠ 2`.
The adaptation needs checking in the target Mathlib context.

**D1.4 — Cast form.** The project states
`IsSquare ((-3 : ℤ) : ZMod p)` — an integer cast into `ZMod p`, because the surrounding
project code manipulates `ℤ`-valued discriminants. Mathlib's neighbours state
`IsSquare (-2 : ZMod p)`, a numeral directly in `ZMod p`. The draft uses that form
for consistency and bridges the cast with `push_cast`. This bridge needs verifying
when the proof is placed upstream.

**D1.5 — Proof through quadratic reciprocity.** Mathlib proves
`-1`, `2`, `-2` via `FiniteField.isSquare_*_iff` plus `card p`, i.e. through
`quadraticChar`. The project proof uses `legendreSym` and
`legendreSym.quadratic_reciprocity'` with `q = 3`, using that `3 / 2 = 1` in `ℕ` so the
two sign factors multiply to `(-1)^(2·(p/2)) = 1`, leaving `(-3/p) = (p/3)`; then `(p/3)`
is decided by `p mod 3` via `decide` over `ZMod 3`.

An alternative that matches the existing family more closely is to add
`quadraticChar_neg_three` and `FiniteField.isSquare_neg_three_iff` first, then derive the
`ZMod` statement. That choice would require a new proof at the character level and
remains a question for review.

**D1.6 — Placement.** `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`,
in the existing `namespace ZMod`, immediately after `exists_sq_eq_neg_two_iff`.

**D1.7 — Name.** `exists_sq_eq_neg_three_iff`, following the family, even though the
`exists_sq_eq_` prefix does not literally describe an `IsSquare` statement. The
proposed name follows the existing convention.

## Recorded verification

The supporting project proof was checked with Lean v4.31.0 and the pinned Mathlib
revision. Its recorded axiom report is `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`. The proposed upstream adaptation still needs checking in its
target context.
