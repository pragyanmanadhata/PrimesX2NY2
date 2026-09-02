# Notes on `jacobiSym.mod_right_of_discr`

[Proposal and proof](PR2-jacobiSym-discriminant-periodicity.md) · [All proposals](README.md)

For `D ≡ 0` or `1 (mod 4)`, the proposed lemma says that `J(D | ·)` has period
`|D|` on odd arguments. Mathlib's existing theorem gives the coarser period
`4|D|`. The project version is `PrimesX2NY2.PartI.S1.mod_right_of_discr`.

## Why I use a congruence statement

I state the result as
`(h : (m : ℤ) ≡ (n : ℤ) [ZMOD D]) : J(D | m) = J(D | n)` instead of using
`b % D.natAbs`, as `jacobiSym.mod_right` does.

When `D ≡ 1 (mod 4)`, `D.natAbs` is odd, so `b % D.natAbs` can be even. The
remainder then fails the oddness assumption. The congruence statement avoids this
problem and is the form used by the project. A remainder version would need an
extra condition or a different formulation.

## How the proof works

Write `|D| = 2^e · d` with `d` odd, then split the Jacobi symbol into factors from
the sign of `D`, the power of `2`, and `d`. The proof compares those factors one at
a time.

The case `e = 1` is impossible: it would give `D ≡ 2 (mod 4)`. Once that is ruled
out, the even case splits naturally into `e = 2` and `e ≥ 3`. For the odd factor I
use `qrSign`, which makes the reciprocity sign depend directly on the argument
modulo `4`.

The remaining cases are:

- If `D > 0` and `D ≡ 1 (mod 4)`, the reciprocity sign is trivial.
- If `D < 0` and `D ≡ 1 (mod 4)`, the sign from `-1` cancels the reciprocity sign.
- If `e = 2`, the square of `J(2 | m)` is `1`, and congruence modulo `4`
  determines the remaining sign.
- If `e ≥ 3`, congruence modulo `8` determines the `χ₈` factor.

The case `D = 0` forces `m = n`. Arguments that are not coprime to `D` do not need
separate handling because the corresponding zero factors agree on both sides.

## Questions about the API

The proof currently has five private helpers: `chi4_congr`, `chi8_congr`,
`gcd_two_odd`, `jac_recip_congr`, and `case_neg_odd`. I am not sure whether the first
two should become public lemmas or whether equivalent results already exist under
different names.

The draft makes `D` implicit because Lean can infer it from the hypotheses. Mathlib's
nearby `mod_right` theorem takes its first argument explicitly, so matching that
convention may be better.

The verification file opens `ZMod`, which lets it write `χ₄` and `χ₈` without a
prefix. Their names may need to be qualified in the final file. The proof itself
depends only on Mathlib, not on definitions from this project.

## Proof check

I checked the exact proof in the draft against Mathlib commit `1055fdaf` with Lean
v4.34.0-rc2. It passed without warnings or `sorryAx`; its axiom report contains only
`propext`, `Classical.choice`, and `Quot.sound`.
