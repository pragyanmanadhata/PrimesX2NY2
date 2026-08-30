# Mathlib PR draft #1 — `ZMod.exists_sq_eq_neg_three_iff`

[Design notes](PR1-NOTES.md) · [Contribution overview](README.md)

**Status:** Draft; not submitted. The project proves the result as
`PrimesX2NY2.Fermat.neg_three_isSquare_iff` in `PrimesX2NY2/PartI_Forms/Fermat.lean`,
with no `sorryAx` dependency. `PrimesX2NY2.PartI.S1.neg_three_isSquare_iff`
re-exports it. It is used in `prime_sq_add_three_sq` (`p = x² + 3y²` iff
`p ≡ 1 mod 3`) and Cox Exercises 1.5, 1.9(a), and 1.4(b).

## Title

`feat(NumberTheory/LegendreSymbol): -3 is a square mod p iff p % 3 = 1`

## Target file

`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`, in the existing
`namespace ZMod` block of the `Values` section — immediately after
`exists_sq_eq_neg_two_iff`, so the four small-value characterizations sit together.

## Motivation

The pinned Mathlib revision characterizes several small quadratic residues modulo
an odd prime:

| value | lemma | location |
|---|---|---|
| `-1` | `ZMod.exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3` | `LegendreSymbol/Basic.lean:285` |
| `2` | `ZMod.exists_sq_eq_two_iff (hp : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7` | `QuadraticReciprocity.lean:74` |
| `-2` | `ZMod.exists_sq_eq_neg_two_iff (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3` | `QuadraticReciprocity.lean:80` |
| `-3` | **missing** | — |

The corresponding result for `-3` is missing. This discriminant case is used for the
Eisenstein integers `ℤ[ω]`, the representation `p = x² + 3y²`, cubic reciprocity,
and (via `p ≡ 1 mod 3`) the theory of cubic residues. This project derives it from
`legendreSym.quadratic_reciprocity'`.

The pinned revision also lacks `FiniteField.isSquare_neg_three_iff`;
`-1`, `2`, `-2` all have `FiniteField.isSquare_*_iff` counterparts
(`FiniteField.isSquare_two_iff`, `FiniteField.isSquare_neg_two_iff`). A reviewer may
prefer the general finite-field version first, with the `ZMod p` statement derived
from it — see "Open questions" below.

## Statement

```lean
/-- `-3` is a square modulo a prime `p ≠ 2, 3` iff `p` is congruent to `1` mod `3`. -/
theorem exists_sq_eq_neg_three_iff (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    IsSquare (-3 : ZMod p) ↔ p % 3 = 1
```

`p` is the section variable `(p : ℕ) [Fact p.Prime]`, matching the neighbouring
lemmas. Both hypotheses are necessary: for `p = 2`, `-3 = 1` is a square while
`2 % 3 = 2`; for `p = 3`, `-3 = 0` is a square while `3 % 3 = 0`.

## Proof sketch

`(-3/p) = (-1/p)·(3/p)`. By quadratic reciprocity with `q = 3`,
`(3/p) = (-1)^((p/2)·(3/2))·(p/3) = (-1)^(p/2)·(p/3)` since `3/2 = 1` in `ℕ`.
The supplementary law gives `(-1/p) = (-1)^(p/2)`. The two sign factors multiply to
`(-1)^(2·(p/2)) = 1`, so `(-3/p) = (p/3)`. Finally `(p/3) = 1` iff `p ≡ 1 mod 3`
and `= -1` iff `p ≡ 2 mod 3`, by `decide` on `ZMod 3`.

## Proof

The project proof was verified with Lean v4.31.0 and the pinned Mathlib revision;
its `#print axioms` check reports `[propext, Classical.choice, Quot.sound]`.
The version below restates the hypotheses in the style of the neighbouring `ZMod`
lemmas, using `p ≠ 2` in place of `Odd p`. The adapted statement, casts, and proof
still need checking in the proposed target file.

```lean
/-- `-3` is a square modulo a prime `p ≠ 2, 3` iff `p` is congruent to `1` mod `3`. -/
theorem exists_sq_eq_neg_three_iff (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    IsSquare (-3 : ZMod p) ↔ p % 3 = 1 := by
  have hp : p.Prime := Fact.out
  have hcast : ((-3 : ℤ) : ZMod p) = (-3 : ZMod p) := by push_cast; ring
  have ha : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have h3' : p ∣ 3 := by exact_mod_cast (dvd_neg).mp h
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three p h3') with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hp3 h1
  rw [← hcast, ← legendreSym.eq_one_iff p ha]
  have hm1 : legendreSym p (-1) = (-1 : ℤ) ^ (p / 2) := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow (hp.eq_two_or_odd.resolve_left hp2)]
  have hQR : legendreSym p (3 : ℤ) = (-1 : ℤ) ^ (3 / 2 * (p / 2)) * legendreSym 3 (p : ℤ) := by
    exact_mod_cast legendreSym.quadratic_reciprocity' (p := 3) (q := p) (by norm_num) hp2
  have key : legendreSym p (-3) = legendreSym 3 (p : ℤ) := by
    calc legendreSym p (-3) = legendreSym p (-1) * legendreSym p 3 := by
          rw [← legendreSym.mul]; norm_num
      _ = (-1 : ℤ) ^ (p / 2) * ((-1 : ℤ) ^ (3 / 2 * (p / 2)) * legendreSym 3 (p : ℤ)) := by
          rw [hm1, hQR]
      _ = legendreSym 3 (p : ℤ) := by
          rw [show (3 : ℕ) / 2 = 1 from rfl, one_mul, ← mul_assoc, ← pow_add]
          rw [Even.neg_one_pow ⟨p / 2, rfl⟩, one_mul]
  rw [key]
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have h30 : ¬ (3 ∣ p) := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    omega
  rcases hmod with h1 | h2
  · have hc : ((p : ℤ) : ZMod 3) = 1 := by
      rw [Int.cast_natCast, ← ZMod.natCast_mod, h1, Nat.cast_one]
    simp only [h1, iff_true]
    exact (legendreSym.eq_one_iff 3 (by rw [hc]; exact one_ne_zero)).mpr (by rw [hc]; decide)
  · have hc : ((p : ℤ) : ZMod 3) = 2 := by
      rw [Int.cast_natCast, ← ZMod.natCast_mod, h2]; norm_num
    have hneg : legendreSym 3 ((p : ℕ) : ℤ) = -1 :=
      (legendreSym.eq_neg_one_iff 3).mpr (by rw [hc]; decide)
    rw [hneg]
    omega
```

The proof uses existing Mathlib declarations: `legendreSym.eq_one_iff`,
`legendreSym.eq_neg_one_iff`, `legendreSym.mul`, `legendreSym.at_neg_one`,
`legendreSym.quadratic_reciprocity'`, `ZMod.χ₄_eq_neg_one_pow`,
`ZMod.intCast_zmod_eq_zero_iff_dvd`, `ZMod.natCast_mod`, and the global instance
`Nat.fact_prime_three`.

## Open questions for the reviewer

1. **Placement/shape.** Should this instead be `FiniteField.isSquare_neg_three_iff`
   over a general finite field (matching `isSquare_two_iff` / `isSquare_neg_two_iff`,
   which are stated in `Mathlib/FieldTheory/Finite/Basic.lean` in terms of
   `Fintype.card F % 8`), with the `ZMod p` version derived? The `-3` condition is
   `card F % 3 = 1`, and the proof would go through `quadraticChar_neg_three` — a
   character-level lemma that would also need adding.
2. **Hypothesis style.** Neighbours use `(hp : p ≠ 2)`; `-3` needs `p ≠ 3` as well.
   Two separate hypotheses (as here) or a single `3 < p`?
3. **Naming.** `exists_sq_eq_neg_three_iff` follows the existing family, though the
   `exists_sq_eq_` prefix is now a slight misnomer for an `IsSquare` statement — the
   proposed name keeps the family consistent.
