# Proposed Mathlib contribution: `ZMod.exists_sq_eq_neg_three_iff`

[Design notes](PR1-NOTES.md) · [Contribution overview](README.md)

This result is already proved in the project as
`PrimesX2NY2.Fermat.neg_three_isSquare_iff`, with no `sorryAx` dependency. I use it
in `prime_sq_add_three_sq` and several of Cox's exercises. This page sketches how
the lemma might fit into Mathlib.

## Title

`feat(NumberTheory/LegendreSymbol): -3 is a square mod p iff p % 3 = 1`

## Target file

`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`, in a `ZMod` section
after `legendreSym.quadratic_reciprocity'` has been defined. The proof uses that
theorem, so it cannot sit directly beside the earlier `2` and `-2` lemmas.

## Motivation

Mathlib already has similar results for several small values modulo an odd prime:

| value | lemma | location |
|---|---|---|
| `-1` | `ZMod.exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3` | `LegendreSymbol/Basic.lean:285` |
| `2` | `ZMod.exists_sq_eq_two_iff (hp : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7` | `QuadraticReciprocity.lean:74` |
| `-2` | `ZMod.exists_sq_eq_neg_two_iff (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3` | `QuadraticReciprocity.lean:80` |
| `-3` | **missing** | — |

I could not find the corresponding result for `-3`. It comes up naturally for
Eisenstein integers, representations by `x² + 3y²`, and cubic reciprocity. My proof
uses `legendreSym.quadratic_reciprocity'`.

Mathlib's finite-field treatment of `2` and `-2` lives in
`Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean`. It may make more
sense to prove a finite-field result for `-3` there first and derive the `ZMod`
statement from it.

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

I checked the proof below against Mathlib commit `1055fdaf` with Lean v4.34.0-rc2.
It compiles unchanged, without warnings or `sorryAx`. I use `p ≠ 2` instead of
`Odd p` to match the nearby `ZMod` lemmas.

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

The main inputs are quadratic reciprocity for `legendreSym` and the supplementary
law for `-1`.

## Questions I would like feedback on

- Would a finite-field theorem be a better starting point? The expected condition is
  `Fintype.card F % 3 = 1`, with suitable exclusions for characteristics `2` and `3`.
- Should the assumptions be `p ≠ 2` and `p ≠ 3`, or simply `3 < p`?
- I used `exists_sq_eq_neg_three_iff` to match the nearby names. Is that still the
  preferred convention?
