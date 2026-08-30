# PR2 notes — `jacobiSym.mod_right_of_discr`

[Proposal and proof](PR2-jacobiSym-discriminant-periodicity.md) · [All proposals](README.md)

**Claim.** For `D ≡ 0, 1 (mod 4)`, `J(D | ·)` has period `|D|` on odd arguments — not
just the `4|D|` given by the pinned Mathlib revision.
**In-repo:** `PrimesX2NY2.PartI.S1.mod_right_of_discr`.
**Risk: medium.** A longer proof with several helper lemmas and interface choices.

## Decisions

**D2.1 — Congruence form.** Stated as
`(h : (m : ℤ) ≡ (n : ℤ) [ZMOD D]) : J(D | m) = J(D | n)` rather than mirroring
`mod_right`'s `J(a | b) = J(a | b % (4 * a.natAbs))`.

For `D ≡ 1 (mod 4)`, the modulus `D.natAbs` is odd, so `b % D.natAbs` can be even.
The `Odd` hypothesis then fails on the right-hand side. A `%` version without the
appropriate side condition is not valid as stated. The congruence form avoids that
problem and is used by the project's applications. A `%` version may still be useful
alongside `mod_right`, but it has not been proved here.

**D2.2 — The `2`-adic split.** Write `|D| = 2^e · d` with `d` odd
(`Nat.exists_eq_pow_mul_and_not_dvd`), then decompose
`J(D | m) = J(ε | m) · J(2 | m)^e · J(d | m)` by `mul_left` and `pow_left`. The proof
compares these three factors separately.

**D2.3 — Excluding `e = 1`.** If `e = 1` then
`D = ±2d` with `d` odd, so `D ≡ 2 (mod 4)`, contradicting the hypothesis. Discharging
this early means the `e ≥ 2` branch is uniform in the sign of `D`, and only `e = 2` vs
`e ≥ 3` needs splitting.

**D2.4 — Reciprocity sign through `qrSign`.** Mathlib's
`qrSign m d = J(χ₄ m | d)` expresses the sign as a function of `m mod 4`, which the
hypothesis controls. The exponent form `(-1)^(d/2 · m/2)` requires arithmetic on
the parity of quotients that `omega` does not handle well. Using `qrSign` simplified
the original proof plan.

**D2.5 — Cases under the discriminant hypothesis.**

- `D ≡ 1 (mod 4)`, `D > 0`: `e = 0`, `d ≡ 1 (mod 4)`, reciprocity sign trivial.
- `D ≡ 1 (mod 4)`, `D < 0`: `d ≡ 3 (mod 4)`; the `χ₄` factor from `ε = -1` cancels the
  reciprocity sign.
- `D ≡ 0 (mod 4)`, `e = 2`: `J(2|m)² = 1` because `J(2|m) = ±1` for odd `m`; the residual
  `χ₄` factor is pinned by `m ≡ n (mod 4)`, which follows from `4 ∣ D`.
- `D ≡ 0 (mod 4)`, `e ≥ 3`: `8 ∣ D`, so `m ≡ n (mod 8)` pins the `χ₈` factor.

**D2.6 — Degenerate cases.** `D = 0` forces `m = n` and is handled first. Arguments not
coprime to `D` need no special treatment: every factor matches, including the
zero case, because `mod_left` holds unconditionally.

**D2.7 — Five private helpers.** `chi4_congr`, `chi8_congr`, `gcd_two_odd`,
`jac_recip_congr`, `case_neg_odd`. An open review question is whether `chi4_congr` and
`chi8_congr` (that `χ₄`/`χ₈` on naturals depend only on the argument mod 4 / mod 8)
should be public lemmas. They may already exist under other names; that needs checking
before submission.

**D2.8 — Implicit binders `{D} {m n}`.** Mathlib's `mod_right` takes `(a : ℤ)` explicit.
The draft makes `D` implicit since it is determined by `h`. A reviewer may prefer
consistency with the neighbour.

**D2.9 — `open ZMod` dependency.** The verified file has `open ZMod`, so the helpers read
`χ₄ …`. The target file may need the qualified name `ZMod.χ₄`.

**D2.10 — Imports.** The proof was developed and verified in a file importing only
`Mathlib`. It has no dependencies on project definitions.

## Recorded verification

The project result compiles with the pinned Lean v4.31.0 / Mathlib setup. The
recorded `#print axioms` check lists `[propext, Classical.choice, Quot.sound]` and
no `sorryAx`. This establishes the proof's dependencies; it does not settle the
API and placement questions above.
