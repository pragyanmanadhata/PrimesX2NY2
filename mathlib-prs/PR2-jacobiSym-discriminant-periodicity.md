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

## The proof (verified)

Two simplifications over the plan above are worth noting. (a) The reciprocity sign is
handled through `qrSign m d = J(χ₄ m | d)` rather than `(-1) ^ (d / 2 * (m / 2))`, which
makes it visibly depend only on `m mod 4` and avoids all parity-of-quotient arithmetic.
(b) `e = 1` is impossible given `D ≡ 0, 1 (mod 4)` and is discharged directly, so the
`e ≥ 2` branch is uniform in the sign of `D`; only `e = 2` versus `e ≥ 3` needs splitting
(`J(2 | m)² = 1` versus `m ≡ n mod 8`).

The file this was verified in has `open ZMod`, so the two χ-helpers appear as `χ₄ …`
below; qualify them as `ZMod.χ₄` if dropping into a context without that `open`.

```lean
private theorem chi4_congr {m n : ℕ} (h : m % 4 = n % 4) :
    χ₄ (m : ZMod 4) = χ₄ (n : ZMod 4) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₄_nat_eq_if_mod_four, h,
    show m % 2 = n % 2 by omega]

/-- `χ₈` on naturals depends only on the argument mod `8`. -/
private theorem chi8_congr {m n : ℕ} (h : m % 8 = n % 8) :
    χ₈ (m : ZMod 8) = χ₈ (n : ZMod 8) := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight, h,
    show m % 2 = n % 2 by omega]

private theorem gcd_two_odd {k : ℕ} (hk : Odd k) : Int.gcd 2 (k : ℤ) = 1 := by
  have h : Nat.gcd 2 k = 1 := Nat.coprime_two_left.mpr hk
  simpa [Int.gcd] using h

/-- For odd `d`, `J(d | ·)` depends only on the argument mod `4` and mod `d`. -/
private theorem jac_recip_congr {d m n : ℕ} (hd : Odd d) (hm : Odd m) (hn : Odd n)
    (h4 : m % 4 = n % 4) (hmod : (m : ℤ) % (d : ℤ) = (n : ℤ) % (d : ℤ)) :
    jacobiSym (d : ℤ) m = jacobiSym (d : ℤ) n := by
  rw [jacobiSym.quadratic_reciprocity' hd hm, jacobiSym.quadratic_reciprocity' hd hn,
    jacobiSym.mod_left' hmod]
  simp only [qrSign]
  rw [chi4_congr h4]

/-- For `d % 4 = 3` and odd `m`, `J(-d | m) = J(m | d)`. -/
private theorem case_neg_odd {d m : ℕ} (hd3 : d % 4 = 3) (hm : Odd m) :
    jacobiSym (-(d : ℤ)) m = jacobiSym (m : ℤ) d := by
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hm, jacobiSym.quadratic_reciprocity' hdodd hm]
  simp only [qrSign]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1]
    simp
  · rw [ZMod.χ₄_nat_three_mod_four h3,
      jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_three_mod_four hd3]
    ring

/-- **Sharp periodicity of the Jacobi symbol for discriminants.**
For `D ≡ 0` or `1 mod 4` the symbol `J(D | ·)` has period `|D|` on odd arguments. -/
theorem mod_right_of_discr {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {m n : ℕ}
    (hm : Odd m) (hn : Odd n) (h : (m : ℤ) ≡ (n : ℤ) [ZMOD D]) :
    jacobiSym D m = jacobiSym D n := by
  rcases eq_or_ne D 0 with rfl | hD0
  · have h' : ((n : ℤ)) - (m : ℤ) = 0 := zero_dvd_iff.mp h.dvd
    have hmn : m = n := by omega
    rw [hmn]
  have hN0 : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
  obtain ⟨e, d, hd2, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 2 (by norm_num)
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd2' : d % 2 = 1 := Nat.odd_iff.mp hdodd
  have hcast : ((D.natAbs : ℕ) : ℤ) = 2 ^ e * (d : ℤ) := by rw [hNe]; push_cast; ring
  have hdvd : (2 : ℤ) ^ e * (d : ℤ) ∣ ((n : ℤ) - (m : ℤ)) := by
    rw [← hcast]; exact dvd_trans (Int.natAbs_dvd.mpr dvd_rfl) h.dvd
  have hmodd : (m : ℤ) % (d : ℤ) = (n : ℤ) % (d : ℤ) :=
    Int.modEq_iff_dvd.mpr ((dvd_mul_left ((d : ℤ)) ((2 : ℤ) ^ e)).trans hdvd)
  have hDsplit : D = 2 ^ e * (d : ℤ) ∨ D = -(2 ^ e * (d : ℤ)) := by
    rcases Int.natAbs_eq D with h1 | h1
    · exact Or.inl (h1.trans hcast)
    · exact Or.inr (h1.trans (congrArg Neg.neg hcast))
  have he1 : e ≠ 1 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hdodd
    rcases hDsplit with hs | hs <;> rw [ht] at hs <;> push_cast [pow_one] at hs <;> omega
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · subst he0
    simp only [pow_zero, one_mul] at hDsplit
    rcases hDsplit with hs | hs
    · have hd1 : d % 4 = 1 := by rw [hs] at hD; omega
      rw [hs, jacobiSym.quadratic_reciprocity_one_mod_four hd1 hm,
        jacobiSym.quadratic_reciprocity_one_mod_four hd1 hn]
      exact jacobiSym.mod_left' hmodd
    · have hd3 : d % 4 = 3 := by rw [hs] at hD; omega
      rw [hs, case_neg_odd hd3 hm, case_neg_odd hd3 hn]
      exact jacobiSym.mod_left' hmodd
  · have he : 2 ≤ e := by omega
    have h4p : (4 : ℤ) ∣ (2 : ℤ) ^ e :=
      ⟨2 ^ (e - 2), by rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
    have h4z : (4 : ℤ) ∣ ((n : ℤ) - (m : ℤ)) := (h4p.mul_right _).trans hdvd
    have h4 : m % 4 = n % 4 := by obtain ⟨k, hk⟩ := h4z; omega
    have hjd : jacobiSym (d : ℤ) m = jacobiSym (d : ℤ) n :=
      jac_recip_congr hdodd hm hn h4 hmodd
    have hj2 : jacobiSym 2 m ^ e = jacobiSym 2 n ^ e := by
      rcases Nat.lt_or_ge e 3 with he3 | he3
      · have he2 : e = 2 := by omega
        rw [he2, jacobiSym.sq_one (gcd_two_odd hm), jacobiSym.sq_one (gcd_two_odd hn)]
      · have h8p : (8 : ℤ) ∣ (2 : ℤ) ^ e :=
          ⟨2 ^ (e - 3), by rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega⟩
        have h8z : (8 : ℤ) ∣ ((n : ℤ) - (m : ℤ)) := (h8p.mul_right _).trans hdvd
        have h8 : m % 8 = n % 8 := by obtain ⟨k, hk⟩ := h8z; omega
        rw [jacobiSym.at_two hm, jacobiSym.at_two hn, chi8_congr h8]
    rcases hDsplit with hs | hs
    · rw [hs, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left,
        jacobiSym.pow_left, hj2, hjd]
    · rw [hs, jacobiSym.neg _ hm, jacobiSym.neg _ hn, jacobiSym.mul_left, jacobiSym.mul_left,
        jacobiSym.pow_left, jacobiSym.pow_left, hj2, hjd, chi4_congr h4]
```

The `%`-form `mod_right_discr` sketched above was **not** proved: for `D ≡ 1 mod 4` the
modulus `D.natAbs` is odd, so `b % D.natAbs` can be even and the statement needs care.
The congruence form is what every application uses, so that is what is offered here.

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
