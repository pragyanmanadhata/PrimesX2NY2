# Mathlib PR drafts — and what actually blocks this project

Drafts only. Nothing here has been submitted, and PR2 is not yet proved.

| # | Contribution | Proved? | Blocks us? |
|---|---|---|---|
| [1](PR1-exists_sq_eq_neg_three_iff.md) | `ZMod.exists_sq_eq_neg_three_iff` — `−3` is a QR mod `p` iff `p ≡ 1 mod 3` | Yes, axiom-clean | No |
| [2](PR2-jacobiSym-discriminant-periodicity.md) | `J(D \| ·)` has period `\|D\|` for `D ≡ 0, 1 mod 4` | **No** — plan only | No |
| [3](PR3-binary-quadratic-forms-reduction.md) | Gauss reduction theory of binary quadratic forms (a series) | Yes, axiom-clean | No |
| 4 | `Zsqrtd.prime_of_norm_prime` — an element of `ℤ√d` whose norm is a rational prime is prime | Yes, axiom-clean (for `ℤ[i]`) | No |

**PR4 (new, small).** While proving Cox's Proposition 4.18 we needed "norm is a rational
prime ⟹ the element is prime" for `ℤ[i]` and found Mathlib has no such lemma, despite
having the `EuclideanDomain ℤ[i]` instance and `Zsqrtd.norm_eq_one_iff'` next door. Our
proof (`PrimesX2NY2/PartI_Forms/BiquadraticReciprocity.lean`, `prime_of_norm_prime`) is
six lines over `irreducible_iff_prime` plus multiplicativity of the norm, and generalizes
verbatim to any `ℤ√d` with `d ≤ 0`. Natural home:
`Mathlib/NumberTheory/Zsqrtd/Basic.lean`, beside `norm_eq_one_iff'`.

## The honest summary

**No Mathlib PR is a prerequisite for any work remaining in Part I.** Every gap we
hit was derivable in-project from existing Mathlib, and we derived it. PRs 1 and 3
are things Mathlib is *missing that we happen to have built*, not things we were
waiting on. Upstreaming them would help the next person; it would not unblock us.

That answers the question directly: the PR-shaped opportunities are worth filing,
but "we need a Mathlib PR to continue" is not currently true of Part I.

## What actually blocks Parts II and III (and is *not* PR-shaped)

The remaining `sorry`s in `PartII_ClassFieldTheory/` and
`PartIII_ComplexMultiplication/` are of two kinds, neither fixable by a small PR:

**(a) Project scaffolding we must write ourselves.** `QuadOrder.ProperIdeal`,
`QuadOrder.idealClassGroup`, `orderOfDiscr`, `hilbertClassField`, `ringClassField`,
`galoisGroup`, `SplitsCompletely`, `classPolynomial` are all `sorry`-bodied *`def`s*.
These are definitions this project owes, buildable on Mathlib's existing
`IsDedekindDomain`, `ClassGroup`, `NumberField`, and Galois theory. No upstream
change is required — just work. Roughly 30 downstream theorems are gated behind
them, so this is the highest-leverage direction after Part I.

**(b) Genuine Mathlib absences far too large for a PR from here.** Verified by
searching the tree:

- **Global class field theory.** No Artin reciprocity, no existence theorem.
  (`grep -rli "artin.*reciprocity" Mathlib/` finds only unrelated Tate-cohomology
  files.) Cox's Part II is *about* this; Mathlib not having it is a known,
  multi-year gap.
- **Chebotarev density.** Absent entirely (`grep -rli chebotarev` → nothing).
- **The modular `j`-invariant and complex multiplication.** Mathlib has a real
  modular-forms library (`EisensteinSeries`, `Delta`, `DedekindEta`,
  `Discriminant`, level-one theory) but no `j`, and no CM theory. Part III needs
  both.

For (b) the right posture is to keep the statements as faithful `sorry`-bodied
theorems (never axioms — see the project's GAP-NOT-AXIOM rule) and revisit as
Mathlib grows, or to contribute to those efforts separately rather than as a
side-quest of this formalization.

## If you want to file these

PR1 is ready to open as-is: single lemma, complete proof, fits an existing family in
`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`. Start there — it is
small enough to settle the naming/placement questions cheaply, and it is a
self-contained win.

PR3 is the valuable one but needs a design conversation first (see its "Open
questions" — chiefly whether `BinaryQuadraticForm` should be a standalone structure
or a layer over `QuadraticForm`, and which way the `SL₂(ℤ)`-action should compose).
Best opened as a Zulip thread in `#mathlib4` before any code.

PR2 should not be opened until its Lean proof exists.
