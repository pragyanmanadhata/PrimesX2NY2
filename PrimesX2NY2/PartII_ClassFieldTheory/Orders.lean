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

The order data and discriminant are defined below. The ideal and class-group
carriers, their group structure, and finiteness still use `sorry`.
-/

namespace PrimesX2NY2.Order

/-- Provisional data for an order `ℤ + f·𝒪_K`: the field discriminant `d_K` and
the positive conductor `f`. The structure does not yet require `d_K` to be a
negative fundamental discriminant. (Cox, §7.) -/
structure QuadOrder where
  /-- Intended field discriminant `d_K`; its defining conditions are not yet included. -/
  fieldDisc : ℤ
  /-- The conductor `f` of the order. -/
  conductor : ℕ
  /-- The conductor is positive. -/
  conductor_pos : 0 < conductor

/-- The **discriminant of the order**, `D = f² · d_K`. (Cox, §7.) -/
def QuadOrder.discr (O : QuadOrder) : ℤ := (O.conductor : ℤ) ^ 2 * O.fieldDisc

/-- Placeholder for proper invertible fractional `𝒪`-ideals. The intended
definition uses fractional ideals of `K` whose ring of multipliers is exactly
`𝒪`. (Cox, §7.) -/
def QuadOrder.ProperIdeal (O : QuadOrder) : Type := sorry

/-- Placeholder for the ideal class group `C(𝒪)`: proper fractional ideals modulo
principal ideals, with multiplication induced by ideal multiplication. (Cox, §7.) -/
def QuadOrder.idealClassGroup (O : QuadOrder) : Type := sorry

/-- The ideal class group admits a commutative group structure. Finiteness is
stated separately below. (Cox, Prop 7.19; Thm 7.7 for the order class number.) -/
theorem QuadOrder.idealClassGroup_isCommGroup (O : QuadOrder) :
    Nonempty (CommGroup O.idealClassGroup) := sorry

/-- The ideal class group of an order is finite. (Cox, §7.) -/
theorem QuadOrder.idealClassGroup_finite (O : QuadOrder) :
    Nonempty (Fintype O.idealClassGroup) := sorry

end PrimesX2NY2.Order
