# Mathlib contribution drafts

[AI-DISCLOSURE-AND-DECISIONS.md](AI-DISCLOSURE-AND-DECISIONS.md) records the provenance,
design choices, and submission requirements for these proposals. The quoted Mathlib
policy requires disclosure of AI use and an unaided understanding of each design decision.

Nothing here has been submitted. All four proposals have supporting proofs in this
project with no `sorryAx` dependency. That verification does not establish that the
drafts are ready for upstream review; API choices, placement, and human review remain.

| # | Contribution | In-project verification | Needed to continue? |
|---|---|---|---|
| [1](PR1-exists_sq_eq_neg_three_iff.md) | `ZMod.exists_sq_eq_neg_three_iff` — `−3` is a square mod a prime `p ≠ 2, 3` iff `p ≡ 1 mod 3` | Proved; no `sorryAx` | No |
| [2](PR2-jacobiSym-discriminant-periodicity.md) | `J(D \| ·)` has period `\|D\|` on odd arguments for `D ≡ 0, 1 mod 4` | Proved using only Mathlib; no `sorryAx` | No |
| [3](PR3-binary-quadratic-forms-reduction.md) | Gauss reduction theory of binary quadratic forms (a series) | Proposed results proved; no `sorryAx` | No |
| 4 | `Zsqrtd.prime_of_norm_prime` — an element of `ℤ[i]` whose norm is a rational prime is prime | Proved for `ℤ[i]`; no `sorryAx` (see correction) | No |

**PR4.** Cox's Proposition 4.18 uses "norm is a rational prime ⟹ the element is prime"
for `ℤ[i]`. The pinned Mathlib revision has the `EuclideanDomain ℤ[i]` instance and
`Zsqrtd.norm_eq_one_iff'`, but the draft's search found no corresponding lemma. The
proof (`PrimesX2NY2/PartI_Forms/BiquadraticReciprocity.lean`, `prime_of_norm_prime`)
uses `irreducible_iff_prime` and multiplicativity of the norm.

**Correction.** An earlier version of this file claimed the proof "generalizes verbatim to
any `ℤ√d` with `d ≤ 0`." That claim was incorrect. `irreducible_iff_prime` needs a
`[DecompositionMonoid]` instance, which `ℤ[i]` has (via `EuclideanDomain → PID → UFD`) but
a general `ℤ√d` does not. The project supplies a counterexample: `ex_4_6_b`
proves `2` is irreducible but not prime in `ℤ[√−3]`, so that ring is not a UFD. The
correct scope is `ℤ[i]`, or any `ℤ√d` known to be a UFD. Whether the *statement* still
holds in non-UFD cases is a separate question, not settled here.

## Relation to the remaining work

None of these contributions is a prerequisite for continuing Part I. Their proofs
already live in the project. Upstreaming would make the results available to other
formalizations without changing what this project can currently prove.

## Dependencies in Parts II and III

The remaining `sorry`s in `PartII_ClassFieldTheory/` and
`PartIII_ComplexMultiplication/` fall into two groups.

**Project definitions.** `QuadOrder.ProperIdeal`,
`QuadOrder.idealClassGroup`, `orderOfDiscr`, `hilbertClassField`, `ringClassField`,
`galoisGroup`, `SplitsCompletely`, `classPolynomial` are all `sorry`-bodied *`def`s*.
These need implementations using Mathlib's existing `IsDedekindDomain`, `ClassGroup`,
`NumberField`, and Galois theory. The downstream statements depend on those
definitions; the contribution drafts here do not address them.

**Larger library developments.** The search of the pinned Mathlib tree recorded
in these drafts identified the following gaps:

- **Global class field theory.** No Artin reciprocity, no existence theorem.
  The search for Artin reciprocity found only unrelated Tate-cohomology files.
  These are central to Cox's Part II and require a substantial development.
- **Chebotarev density.** The search found no theorem.
- **The modular `j`-invariant and complex multiplication.** Mathlib has a
  modular-forms library (`EisensteinSeries`, `Delta`, `DedekindEta`,
  `Discriminant`, level-one theory) but no `j`, and no CM theory. Part III needs
  both.

Until those developments are available, the project keeps the corresponding
statements as explicit `sorry`-bodied theorems rather than adding axioms, as described
in [CONVENTIONS.md](../CONVENTIONS.md).
Any work on these larger dependencies needs a separate scope from the four
contributions listed here.

## Preparation for submission

PR1 is a small candidate for initial review: a single lemma intended to fit the
family in `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`. Its draft
still raises questions about placement, hypotheses, and a possible finite-field
generalization. The submitter also needs to complete the review and disclosure
checklist in the decision record.

PR2's proof was developed in a file importing only `Mathlib`. It has no project
dependencies, but its statement, helper lemmas, and namespace assumptions still
need review in the target file.

PR3 needs a design discussion in `#mathlib4` on Zulip before a code submission.
The main questions are whether `BinaryQuadraticForm` should be a standalone
structure or a layer over `QuadraticForm`, and how the `SL₂(ℤ)` action should
compose. Its proposed series begins with definitions and equivalence; reduction
would follow once those conventions are settled.
