/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part I, Chapter 2 — Binary quadratic forms, proper equivalence, reduction

Cox, *Primes of the Form x² + ny²*, §2.

Integral binary quadratic forms, the action of `SL₂(ℤ)`, proper equivalence, and
the reduction theory of positive definite forms.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.Forms

/-- An integral **binary quadratic form** `f(x, y) = a x² + b x y + c y²`,
recorded by its coefficient triple `(a, b, c)`. (Cox, §2.) -/
structure BinaryQF where
  /-- Coefficient of `x²`. -/
  a : ℤ
  /-- Coefficient of `x y`. -/
  b : ℤ
  /-- Coefficient of `y²`. -/
  c : ℤ

/-- The **discriminant** `b² − 4ac` of a binary quadratic form. (Cox, §2.) -/
def BinaryQF.discr (f : BinaryQF) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- Evaluation `f(x, y) = a x² + b x y + c y²`. -/
def BinaryQF.eval (f : BinaryQF) (x y : ℤ) : ℤ :=
  f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- A form is **primitive** when `gcd(a, b, c) = 1`. (Cox, §2.) -/
def BinaryQF.Primitive (f : BinaryQF) : Prop := Int.gcd (Int.gcd f.a f.b) f.c = 1

/-- A form is **positive definite** when `a > 0` and the discriminant is negative.
(Cox, §2.) -/
def BinaryQF.PosDef (f : BinaryQF) : Prop := 0 < f.a ∧ f.discr < 0

/-- The (right) action of an integer matrix `M = (p q; r s)` on a form by the
change of variables `(x, y) ↦ (p x + q y, r x + s y)`. Restricting to
`det M = 1` gives the action of `SL₂(ℤ)`. (Cox, §2.) -/
def action (M : Matrix (Fin 2) (Fin 2) ℤ) (f : BinaryQF) : BinaryQF := sorry

/-- Two forms are **properly equivalent** when related by a determinant-one
integer change of variables, i.e. by an element of `SL₂(ℤ)`. (Cox, §2.) -/
def ProperlyEquivalent (f g : BinaryQF) : Prop :=
  ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 1 ∧ action M f = g

/-- Proper equivalence is an equivalence relation. (Cox, §2.) -/
theorem properlyEquivalent_equivalence : Equivalence ProperlyEquivalent := sorry

/-- Proper equivalence preserves the discriminant. (Cox, §2.) -/
theorem discr_eq_of_properlyEquivalent {f g : BinaryQF} (h : ProperlyEquivalent f g) :
    f.discr = g.discr := sorry

/-- A positive definite form `(a, b, c)` is **reduced** when `|b| ≤ a ≤ c`, with
`b ≥ 0` whenever `|b| = a` or `a = c`. (Cox, §2.3.) -/
def BinaryQF.Reduced (f : BinaryQF) : Prop :=
  |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ ((|f.b| = f.a ∨ f.a = f.c) → 0 ≤ f.b)

/-- **Reduction theorem** (Cox, Thm 2.8). Every positive definite form is
properly equivalent to a unique reduced form. -/
theorem exists_unique_reduced (f : BinaryQF) (hf : f.PosDef) :
    ∃! g : BinaryQF, g.Reduced ∧ ProperlyEquivalent f g := sorry

/-- **Finiteness of class number** (Cox, Thm 2.13). For each discriminant `D < 0`
there are only finitely many reduced forms, hence finitely many proper
equivalence classes. -/
theorem finite_reduced_of_discr (D : ℤ) (hD : D < 0) :
    {f : BinaryQF | f.discr = D ∧ f.Reduced}.Finite := sorry

end PrimesXNY2.Forms
