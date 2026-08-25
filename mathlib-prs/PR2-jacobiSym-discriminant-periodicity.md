# Mathlib PR draft #2 — sharp periodicity of `J(D | ·)` for discriminants

**Status:** DRAFT — not submitted, but now **complete and axiom-clean**. Proved in this
project as `PrimesX2NY2.PartI.S1.mod_right_of_discr` (with `ex_1_11` its explicit-binder
restatement), `PrimesX2NY2/PartI_Forms/Exercises/S1.lean`. The proof below uses **only
Mathlib** — it was developed and verified in a file importing nothing but `Mathlib`, so
it lifts into `JacobiSymbol.lean` verbatim. `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]`.

Downstream in this project it yields Cox Exercise 1.12(a) — that `m ↦ J(D | m)` is a
Dirichlet character mod `|D|` — and Exercise 1.14, the mod-`n` (rather than mod-`4n`)
criterion for `n ≡ 3 (mod 4)`. Those are the applications that motivate it.

## Title

`feat(NumberTheory/LegendreSymbol): J(D | ·) has period |D| for D ≡ 0, 1 mod 4`

## Target file

`Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean`, in `namespace jacobiSym`,
after `mod_right` (currently line 480–486), which is the coarse version of the same
fact.

## Motivation

Mathlib's current periodicity-in-the-denominator lemma is

```lean
theorem mod_right (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs))
```

i.e. `J(a | ·)` has period `4|a|` on odd arguments. That factor of `4` is necessary
in general (`J(2 | ·)` genuinely has period `8`), but it is *not* necessary for the
case that matters in number theory: when `D ≡ 0` or `1 mod 4` — that is, when `D` is
a **discriminant** — the symbol `J(D | ·)` already has period `|D|`.

This sharp form is exactly what makes `χ_D(m) := J(D | m)` a Dirichlet character
mod `|D|` (the Kronecker symbol attached to a quadratic field), which is the
statement one actually needs for:

- genus theory of binary quadratic forms (the congruence conditions "`p = x² + ny²`
  iff `p ≡ …  mod 4n`" are all instances),
- the class-number formula and quadratic `L`-functions,
- the Kronecker symbol as a character (Mathlib has `kroneckerSym`/`jacobiSym` but no
  statement that it is `|D|`-periodic).

With only `mod_right`, every such application is off by a factor of 4 and must be
patched by hand.

## Statement

```lean
/-- For a discriminant `D` (i.e. `D ≡ 0` or `1` mod `4`), the Jacobi symbol
`J(D | ·)` depends only on its argument mod `D`: it has period `|D|`, not just
`4|D|`. -/
theorem mod_right_of_discr {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {m n : ℕ}
    (hm : Odd m) (hn : Odd n) (h : (m : ℤ) ≡ (n : ℤ) [ZMOD D]) :
    J(D | m) = J(D | n)
```

A `%`-form matching the existing `mod_right` should probably ship alongside it:

```lean
theorem mod_right_discr {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {b : ℕ} (hb : Odd b) :
    J(D | b) = J(D | b % D.natAbs)
```

(the second follows from the first, given `Odd (b % D.natAbs)` — which needs `D`
even, so the `%`-form may need care in the `D ≡ 1 mod 4` case where `D.natAbs` is
odd and `b % D.natAbs` can be even. The congruence form above avoids this wrinkle
and is the one to prove first.)

## Proof plan

Write `D = ε · 2^e · D₀` with `D₀` odd positive and `ε = ±1`. Then
`J(D | m) = J(ε | m) · J(2 | m)^e · J(D₀ | m)` by `jacobiSym.mul_left` and
`jacobiSym.pow_left`. Each factor is analysed:

- `J(D₀ | m)` flips by Jacobi reciprocity (`jacobiSym.quadratic_reciprocity'`) to
  `qrSign · J(m | D₀)`, and `J(m | D₀)` depends only on `m mod D₀`
  (`jacobiSym.mod_left`) — the numerator-periodicity Mathlib already has.
- `J(ε | m)` is `1` or `χ₄ m` (`jacobiSym.at_neg_one`), depending on `m mod 4`.
- `J(2 | m)^e` is `χ₈ m ^ e` (`jacobiSym.at_two`), depending on `m mod 8`.
- `qrSign` depends on `m mod 4` and `D₀ mod 4`.

The hypothesis `D ≡ 0, 1 mod 4` is what makes the leftover sign factors collapse:

| case | why the signs cancel |
|---|---|
| `D ≡ 1 mod 4`, `D > 0` | `e = 0`, `ε = 1`, and `(D-1)/2` is even so `qrSign = 1`; left with `J(m \| D)`, periodic mod `D`. |
| `D ≡ 1 mod 4`, `D < 0` | `\|D\| ≡ 3 mod 4`; the `χ₄` factor from `ε = -1` cancels the odd `qrSign` exponent. |
| `D ≡ 0 mod 4`, `e = 2` | `J(2 \| m)² = 1` since `J(2 \| m) = ±1` for odd `m`; remaining `χ₄` factor is fixed by `m ≡ n mod 4`, which follows from `4 ∣ D`. |
| `D ≡ 0 mod 4`, `e ≥ 3` | `8 ∣ D`, so `m ≡ n mod 8` and the `χ₈` factor matches. |

Degenerate cases: `D = 0` (then `m ≡ n mod 0` forces `m = n`); and arguments not
coprime to `D`, where both sides are `0` — handled automatically because each factor
above matches, `J(m | D₀) = J(n | D₀)` by `mod_left` including the zero case.

## Status of the proof

Not yet formalized. A first formalization attempt in this project was cut short by
an infrastructure limit before producing a verified proof; no partial results are
being claimed. The plan above is the classical argument and each ingredient it names
(`mul_left`, `pow_left`, `mod_left`, `at_two`, `at_neg_one`,
`quadratic_reciprocity'`, `qrSign` lemmas, `Nat.exists_eq_pow_mul_and_not_dvd` for
the `2`-adic split) has been confirmed present in the pinned Mathlib.

**Before this PR is opened:** finish the Lean proof, confirm
`#print axioms mod_right_of_discr` is exactly `[propext, Classical.choice, Quot.sound]`,
and re-check the `%`-form's edge cases.

## Open questions for the reviewer

1. **Which form is canonical** — the `Int.ModEq` version, the `b % D.natAbs`
   version, or a `Function.Periodic`-flavoured statement about
   `fun m => J(D | m)` restricted to odds?
2. **Should this be phrased via the Kronecker symbol** (`kroneckerSym`) instead,
   where the discriminant condition is more natural, and specialized to `jacobiSym`?
3. **Is a `ZMod |D|`-valued character the real target?** The most reusable form may
   be `∃ χ : DirichletCharacter ℤ D.natAbs, ∀ m, Odd m → χ m = J(D | m)`, i.e. the
   quadratic character attached to a discriminant, which Mathlib also lacks. That is
   a larger contribution; this lemma is its main ingredient.
