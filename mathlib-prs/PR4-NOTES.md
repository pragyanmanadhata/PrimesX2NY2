# PR4 notes — `prime_of_norm_prime`

[Proposal overview](README.md)

**Claim as drafted.** An element of `ℤ[i]` whose norm is a rational prime is prime.
**In-repo:** `PrimesX2NY2.BiquadraticReciprocity.prime_of_norm_prime`.

## Correction to the proposed generalization

An earlier version of `mathlib-prs/README.md` claimed that this proof "generalizes
verbatim to any `ℤ√d` with `d ≤ 0`". That claim was incorrect.

The proof opens with `rw [← irreducible_iff_prime]`. In the pinned Mathlib revision,
`irreducible_iff_prime` requires a `[DecompositionMonoid M]` instance. `ℤ[i]` has it, via
`EuclideanDomain → PID → UFD`. A general `ℤ√d` with `d ≤ 0` need not have it.
The project proves a counterexample: `ex_4_6_b` shows `2` is irreducible but not prime
in `ℤ[√−3]`, so `ℤ[√−3]` is not a UFD and `irreducible_iff_prime` fails there.

The correct scope of this proof is `ℤ[i]`, or a `ℤ√d` known to be a UFD. Whether
the statement still holds in `ℤ[√−3]` by another proof remains unresolved here.
The README now records this correction.

## Decisions

**D4.1 — Hypothesis shape `(hq : q.Prime) (h : Zsqrtd.norm π = (q : ℤ))` with `q : ℕ`.**
The alternative `(h : Prime (Zsqrtd.norm π))` stated in `ℤ` avoids the cast. The `ℕ`
version was chosen because the call sites had `p : ℕ` prime in hand. For Mathlib the
`ℤ`-native form is another option for review.

**D4.2 — Proof structure.** The element is not a unit by `Zsqrtd.norm_eq_one_iff'`
(norm `q ≠ 1`). The factorization case uses multiplicativity of the norm plus
`Nat.Prime.eq_one_or_self_of_dvd` to force one factor to have norm 1.

**D4.3 — Placement.** `Mathlib/NumberTheory/Zsqrtd/Basic.lean` beside `norm_eq_one_iff'`
**only if** the UFD hypothesis is made explicit; otherwise
`Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean` where the instance is available.

The argument is short enough that a reviewer may prefer to inline it at the use site.
A separate lemma would support other arguments from a prime norm and sit alongside
`norm_eq_one_iff'`. Whether that warrants an addition remains a review question.

## Recorded verification

The existing `prime_of_norm_prime` proof was checked for `ℤ[i]` with the pinned
Lean v4.31.0 / Mathlib versions. Its recorded axioms are
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. This verification
does not extend its scope to arbitrary `ℤ√d`.
