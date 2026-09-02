# Notes on `prime_of_norm_prime`

[All proposals](README.md)

The project proves that a Gaussian integer whose norm is a rational prime is prime.
The theorem is `PrimesX2NY2.BiquadraticReciprocity.prime_of_norm_prime`.

## Scope

The proof works for `ℤ[i]` because `irreducible_iff_prime` is available there through
the `EuclideanDomain → PID → UFD` instances. The same argument works for a `ℤ√d`
that is known to be a UFD, but it does not automatically apply for every `d ≤ 0`.

The project theorem `ex_4_6_b` shows why the assumption matters: `2` is irreducible
but not prime in `ℤ[√−3]`. I have not settled whether the norm statement itself has
a different proof in that ring.

## Statement

The project uses `q : ℕ`, a hypothesis `q.Prime`, and
`Zsqrtd.norm π = (q : ℤ)` because its call sites already have a natural prime. A
version stated directly with `Prime (Zsqrtd.norm π)` in `ℤ` would avoid the cast and
may fit Mathlib better.

## Proof idea

The proof first shows that `π` is not a unit because its norm is the prime `q`, not
`1`. If `π` factors, multiplicativity of the norm and
`Nat.Prime.eq_one_or_self_of_dvd` force one factor to have norm `1`, so that factor
is a unit.

## Possible location

With an explicit `DecompositionMonoid` assumption, the lemma could sit in
`Mathlib/NumberTheory/Zsqrtd/Basic.lean` near `norm_eq_one_iff'`. For a statement only
about Gaussian integers, `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean` is the more
natural location.

The proof is short enough to inline, but a named lemma could still be useful anywhere
a prime norm is used to prove primality.

## Proof check

I checked the existing Gaussian-integer proof against Mathlib commit `1055fdaf` with
Lean v4.34.0-rc2. It passed without warnings or `sorryAx`; its axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound`.
