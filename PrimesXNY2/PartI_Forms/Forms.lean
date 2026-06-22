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
def action (M : Matrix (Fin 2) (Fin 2) ℤ) (f : BinaryQF) : BinaryQF :=
  ⟨f.a * M 0 0 ^ 2 + f.b * M 0 0 * M 1 0 + f.c * M 1 0 ^ 2,
   2 * f.a * M 0 0 * M 0 1 + f.b * (M 0 0 * M 1 1 + M 0 1 * M 1 0) + 2 * f.c * M 1 0 * M 1 1,
   f.a * M 0 1 ^ 2 + f.b * M 0 1 * M 1 1 + f.c * M 1 1 ^ 2⟩

/-- The identity matrix acts trivially. -/
theorem action_one (f : BinaryQF) : action 1 f = f := by
  obtain ⟨a, b, c⟩ := f
  have e00 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by simp
  have e01 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by simp
  have e10 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simp
  have e11 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by simp
  simp only [action, e00, e01, e10, e11, BinaryQF.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `-I` (determinant `1` as well, via `(-1)² = 1`) acts trivially. -/
theorem action_neg_one (f : BinaryQF) : action (-1) f = f := by
  obtain ⟨a, b, c⟩ := f
  have e00 : (-1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -1 := by simp
  have e01 : (-1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by simp
  have e10 : (-1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simp
  have e11 : (-1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1 := by simp
  simp only [action, e00, e01, e10, e11, BinaryQF.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- The action is contravariant in the matrix: `N · (M · f) = (M*N) · f`. (Both sides
substitute `(x,y) ↦ M(N(x,y))`.) -/
theorem action_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (f : BinaryQF) :
    action N (action M f) = action (M * N) f := by
  simp only [action, Matrix.mul_apply, Fin.sum_univ_two, BinaryQF.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- The action scales the discriminant by `(det M)²`. -/
theorem discr_action (M : Matrix (Fin 2) (Fin 2) ℤ) (f : BinaryQF) :
    (action M f).discr = M.det ^ 2 * f.discr := by
  simp only [BinaryQF.discr, action, Matrix.det_fin_two]; ring

/-- Two forms are **properly equivalent** when related by a determinant-one
integer change of variables, i.e. by an element of `SL₂(ℤ)`. (Cox, §2.) -/
def ProperlyEquivalent (f g : BinaryQF) : Prop :=
  ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 1 ∧ action M f = g

/-- Proper equivalence is an equivalence relation. (Cox, §2.) -/
theorem properlyEquivalent_equivalence : Equivalence ProperlyEquivalent := by
  refine ⟨fun f => ⟨1, Matrix.det_one, action_one f⟩, ?_, ?_⟩
  · rintro f g ⟨M, hM, rfl⟩
    exact ⟨M.adjugate, by rw [Matrix.det_adjugate, hM]; simp,
      by rw [action_mul, Matrix.mul_adjugate, hM, one_smul, action_one]⟩
  · rintro f g h ⟨M, hM, rfl⟩ ⟨N, hN, rfl⟩
    exact ⟨M * N, by rw [Matrix.det_mul, hM, hN]; ring, (action_mul M N f).symm⟩

/-- Proper equivalence preserves the discriminant. (Cox, §2.) -/
theorem discr_eq_of_properlyEquivalent {f g : BinaryQF} (h : ProperlyEquivalent f g) :
    f.discr = g.discr := by
  obtain ⟨M, hM, rfl⟩ := h
  rw [discr_action, hM]; ring

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

/-- **Full equivalence** (`GL₂(ℤ)`; Cox §2, (2.2)). Two forms are equivalent when
related by an integer change of variables of determinant `±1`. -/
def Equivalent (f g : BinaryQF) : Prop :=
  ∃ M : Matrix (Fin 2) (Fin 2) ℤ, (M.det = 1 ∨ M.det = -1) ∧ action M f = g

/-- Full (`GL₂(ℤ)`) equivalence is an equivalence relation. (Cox §2.) -/
theorem equivalent_equivalence : Equivalence Equivalent := by
  refine ⟨fun f => ⟨1, Or.inl Matrix.det_one, action_one f⟩, ?_, ?_⟩
  · rintro f g ⟨M, hM, rfl⟩
    refine ⟨M.adjugate, ?_, ?_⟩
    · rw [Matrix.det_adjugate]; rcases hM with h | h <;> rw [h] <;> simp
    · rw [action_mul, Matrix.mul_adjugate]
      rcases hM with h | h <;> rw [h]
      · rw [one_smul, action_one]
      · rw [neg_one_smul, action_neg_one]
  · rintro f g h ⟨M, hM, rfl⟩ ⟨N, hN, rfl⟩
    refine ⟨M * N, ?_, (action_mul M N f).symm⟩
    rw [Matrix.det_mul]; rcases hM with h | h <;> rcases hN with k | k <;> rw [h, k] <;> omega

/-- A form is **indefinite** when its discriminant is positive. (Cox §2.) -/
def BinaryQF.Indefinite (f : BinaryQF) : Prop := 0 < f.discr

/-- **(2.4).** `4a·f(x,y) = (2ax + by)² − D y²`. (Cox §2.) -/
theorem four_mul_eval (f : BinaryQF) (x y : ℤ) :
    4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 - f.discr * y ^ 2 := by
  simp only [BinaryQF.eval, BinaryQF.discr]
  ring

/-- The **principal form** of discriminant `D ≡ 0, 1 (mod 4)`:
`x² − (D/4)y²` if `D ≡ 0`, and `x² + xy + ((1−D)/4)y²` if `D ≡ 1`. (Cox §2.) -/
def principalForm (D : ℤ) : BinaryQF :=
  if D % 4 = 0 then ⟨1, 0, -(D / 4)⟩ else ⟨1, 1, (1 - D) / 4⟩

/-- **Composition identity (2.30)** for the form `2x² + 2xy + 3y²` (used to prove
the conjectures on `x² + 5y²`). (Cox §2.) -/
theorem comp_identity_2_30 (x y z w : ℤ) :
    (2 * x ^ 2 + 2 * x * y + 3 * y ^ 2) * (2 * z ^ 2 + 2 * z * w + 3 * w ^ 2)
      = (2 * x * z + x * w + y * z + 3 * y * w) ^ 2 + 5 * (x * w - y * z) ^ 2 := by
  ring

/-- **Composition identity (2.31)** for forms `ax² + 2bxy + cy²` of discriminant
`−4n`, where `n = ac − b²`. (Cox §2.) -/
theorem comp_identity_2_31 (a b c x y z w : ℤ) :
    (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) * (a * z ^ 2 + 2 * b * z * w + c * w ^ 2)
      = (a * x * z + b * x * w + b * y * z + c * y * w) ^ 2
        + (a * c - b ^ 2) * (x * w - y * z) ^ 2 := by
  ring

/-- **Landau's theorem** (Cox, Thm 2.18): `h(−4n) = 1` iff `n ∈ {1,2,3,4,7}`, where
`h(−4n)` is the number of primitive reduced forms of discriminant `−4n`. -/
theorem class_number_one (n : ℕ) (hn : 0 < n) :
    {f : BinaryQF | f.discr = -4 * (n : ℤ) ∧ f.Reduced ∧ f.Primitive}.ncard = 1
      ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 7 := by
  sorry

end PrimesXNY2.Forms
