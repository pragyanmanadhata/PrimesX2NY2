/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part II, Chapter 5 - Orders in imaginary quadratic fields

Cox, *Primes of the Form x² + ny²*, §7.

An order `𝒪` of conductor `f` in an imaginary quadratic field `K = ℚ(√(d_K))` is
`ℤ + f·𝒪_K`; its proper (invertible) fractional ideals form a group, and the
ideal class group `C(𝒪)` is finite.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.Order

/-- An **order** in an imaginary quadratic field, recorded for the scaffold by the
fundamental discriminant `d_K` of the field `K` and the conductor `f` (so the
order is `ℤ + f·𝒪_K`). (Cox, §7.) -/
structure QuadOrder where
  /-- The (negative) fundamental discriminant of the field `K = ℚ(√(d_K))`. -/
  fieldDisc : ℤ
  /-- The conductor `f` of the order. -/
  conductor : ℕ
  /-- The conductor is positive. -/
  conductor_pos : 0 < conductor

/-- The **discriminant of the order**, `D = f² · d_K`. (Cox, §7.) -/
def QuadOrder.discr (O : QuadOrder) : ℤ := (O.conductor : ℤ) ^ 2 * O.fieldDisc

/-- A **proper (invertible) fractional `𝒪`-ideal**. Temporary carrier; the full
definition uses fractional ideals of `K` whose ring of multipliers is exactly
`𝒪`. (Cox, §7.) -/
def QuadOrder.ProperIdeal (O : QuadOrder) : Type := sorry

/-- The **ideal class group** `C(𝒪)` of the order: proper fractional ideals modulo
principal ideals. Temporary carrier; the group law is ideal multiplication.
(Cox, §7.) -/
def QuadOrder.idealClassGroup (O : QuadOrder) : Type := sorry

/-- **`C(𝒪)` is a finite abelian group** (Cox, Prop 7.19, Thm 7.7 for the order
class number). Stated as the existence of a `CommGroup` structure. -/
theorem QuadOrder.idealClassGroup_isCommGroup (O : QuadOrder) :
    Nonempty (CommGroup O.idealClassGroup) := sorry

/-- The ideal class group of an order is finite. (Cox, §7.) -/
theorem QuadOrder.idealClassGroup_finite (O : QuadOrder) :
    Nonempty (Fintype O.idealClassGroup) := sorry

end PrimesX2NY2.Order
