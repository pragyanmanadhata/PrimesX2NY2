/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part I, Chapter 2 - Binary quadratic forms, proper equivalence, reduction

Cox, *Primes of the Form x² + ny²*, §2.

Integral binary quadratic forms, the action of `SL₂(ℤ)`, proper equivalence, and
the reduction theory of positive definite forms.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.Forms

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

/-- The content `gcd(a,b,c)` divides the content of `action M f`: each coefficient of
`action M f` is a `ℤ`-linear combination of `a, b, c`. -/
theorem content_dvd_action (M : Matrix (Fin 2) (Fin 2) ℤ) (f : BinaryQF) :
    Int.gcd (Int.gcd f.a f.b) f.c
      ∣ Int.gcd (Int.gcd (action M f).a (action M f).b) (action M f).c := by
  have hca : (Int.gcd (Int.gcd f.a f.b) f.c : ℤ) ∣ f.a :=
    (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left f.a f.b)
  have hcb : (Int.gcd (Int.gcd f.a f.b) f.c : ℤ) ∣ f.b :=
    (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right f.a f.b)
  have hcc : (Int.gcd (Int.gcd f.a f.b) f.c : ℤ) ∣ f.c := Int.gcd_dvd_right _ _
  have dAa : (Int.gcd (Int.gcd f.a f.b) f.c : ℤ) ∣ (action M f).a := by
    simp only [action]
    exact dvd_add (dvd_add (hca.mul_right _) ((hcb.mul_right _).mul_right _)) (hcc.mul_right _)
  have dAb : (Int.gcd (Int.gcd f.a f.b) f.c : ℤ) ∣ (action M f).b := by
    simp only [action]
    exact dvd_add (dvd_add (((hca.mul_left 2).mul_right _).mul_right _) (hcb.mul_right _))
      (((hcc.mul_left 2).mul_right _).mul_right _)
  have dAc : (Int.gcd (Int.gcd f.a f.b) f.c : ℤ) ∣ (action M f).c := by
    simp only [action]
    exact dvd_add (dvd_add (hca.mul_right _) ((hcb.mul_right _).mul_right _)) (hcc.mul_right _)
  apply Int.dvd_gcd _ dAc
  exact_mod_cast Int.dvd_gcd dAa dAb

/-- The `SL₂(ℤ)`-action preserves primitivity (the content is an invariant). -/
theorem primitive_action_iff (M : Matrix (Fin 2) (Fin 2) ℤ) (f : BinaryQF) (hM : M.det = 1) :
    (action M f).Primitive ↔ f.Primitive := by
  unfold BinaryQF.Primitive
  have h1 := content_dvd_action M f
  have h2 : Int.gcd (Int.gcd (action M f).a (action M f).b) (action M f).c
      ∣ Int.gcd (Int.gcd f.a f.b) f.c := by
    have := content_dvd_action M.adjugate (action M f)
    rwa [action_mul, Matrix.mul_adjugate, hM, one_smul, action_one] at this
  exact ⟨fun h => Nat.dvd_one.mp (h ▸ h1), fun h => Nat.dvd_one.mp (h ▸ h2)⟩

/-- Proper equivalence preserves primitivity. (Cox, §2.) -/
theorem primitive_of_properlyEquivalent {f g : BinaryQF} (h : ProperlyEquivalent f g) :
    f.Primitive ↔ g.Primitive := by
  obtain ⟨M, hM, rfl⟩ := h
  exact (primitive_action_iff M f hM).symm

/-- A positive definite form `(a, b, c)` is **reduced** when `|b| ≤ a ≤ c`, with
`b ≥ 0` whenever `|b| = a` or `a = c`. (Cox, §2.3.) -/
def BinaryQF.Reduced (f : BinaryQF) : Prop :=
  |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ ((|f.b| = f.a ∨ f.a = f.c) → 0 ≤ f.b)

/-- The elementary lower bound behind reduction theory: if `f` is reduced, then
`(a - |b| + c) min(x²,y²) ≤ f(x,y)`. (Cox §2, (2.9).) -/
theorem reduced_eval_lower_bound (f : BinaryQF) (hr : f.Reduced) (x y : ℤ) :
    (f.a - |f.b| + f.c) * min (x ^ 2) (y ^ 2) ≤ f.eval x y := by
  obtain ⟨h1, h2, -⟩ := hr
  cases abs_cases f.b <;> simp_all +decide [BinaryQF.eval]
  · cases le_total (x ^ 2) (y ^ 2) <;> simp_all +decide [abs_of_nonneg]
    · nlinarith [sq_nonneg (x + y), sq_nonneg (x - y),
        mul_le_mul_of_nonneg_left ‹x ^ 2 ≤ y ^ 2› (show 0 ≤ f.c by linarith)]
    · nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
  · cases le_total (x ^ 2) (y ^ 2) <;> simp +decide [*]
    all_goals rw [abs_of_nonpos] <;>
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

/-- In the strict interior of the reduced region, the two coordinate values are
rigid at primitive inputs: `a` occurs only at `±(1,0)`, and `c` only at
`±(0,1)`. (Cox §2, (2.11).) -/
theorem reduced_strict_value_rigidity (f : BinaryQF) (hr : f.Reduced)
    (hba : |f.b| < f.a) (hac : f.a < f.c) (x y : ℤ) (hcop : IsCoprime x y) :
    (f.eval x y = f.a ↔ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0)) ∧
      (f.eval x y = f.c ↔ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · have hxunit : IsUnit x := isCoprime_zero_right.mp hcop
    rcases Int.isUnit_iff.mp hxunit with rfl | rfl <;>
      simp [BinaryQF.eval, hac.ne]
  · rcases eq_or_ne x 0 with rfl | hx
    · have hyunit : IsUnit y := isCoprime_zero_left.mp hcop
      rcases Int.isUnit_iff.mp hyunit with rfl | rfl <;>
        simp [BinaryQF.eval, hac.ne']
    · have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hy2pos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      have hx2 : (1 : ℤ) ≤ x ^ 2 := by omega
      have hy2 : (1 : ℤ) ≤ y ^ 2 := by omega
      have hmin : (1 : ℤ) ≤ min (x ^ 2) (y ^ 2) := le_min hx2 hy2
      have hcoeff : 0 ≤ f.a - |f.b| + f.c := by
        linarith [abs_nonneg f.b]
      have hcoeff_le :
          f.a - |f.b| + f.c ≤
            (f.a - |f.b| + f.c) * min (x ^ 2) (y ^ 2) := by
        simpa using mul_le_mul_of_nonneg_left hmin hcoeff
      have hlower := reduced_eval_lower_bound f hr x y
      have hgap : f.c < f.a - |f.b| + f.c := by linarith
      have hceval : f.c < f.eval x y :=
        lt_of_lt_of_le hgap (hcoeff_le.trans hlower)
      have hne_a : f.eval x y ≠ f.a := by linarith
      have hne_c : f.eval x y ≠ f.c := by linarith
      simp [hne_a, hne_c, hx, hy]

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

/-- The values of `action M f` are the values of `f` after the linear change of
variables `M`: `(action M f)(x,y) = f(M₀₀ x + M₀₁ y, M₁₀ x + M₁₁ y)`. (Cox §2, (2.2).) -/
theorem eval_action (M : Matrix (Fin 2) (Fin 2) ℤ) (f : BinaryQF) (x y : ℤ) :
    (action M f).eval x y
      = f.eval (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) := by
  simp only [action, BinaryQF.eval]; ring

/-- A positive definite form takes strictly positive values at every nonzero `(x,y)`.
From `4 a f(x,y) = (2ax+by)² − D y²` with `a > 0` and `D < 0`. (Cox, §2.) -/
theorem eval_pos_of_posDef (f : BinaryQF) (hf : f.PosDef) (x y : ℤ)
    (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < f.eval x y := by
  obtain ⟨ha, hD⟩ := hf
  have key : 4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 + (-f.discr) * y ^ 2 := by
    rw [four_mul_eval]; ring
  have hpos : 0 < 4 * f.a * f.eval x y := by
    rw [key]
    rcases eq_or_ne y 0 with hy0 | hy0
    · subst hy0
      have hx : x ≠ 0 := by tauto
      have h2ax : 2 * f.a * x ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') hx
      have heq : (2 * f.a * x + f.b * 0) ^ 2 + (-f.discr) * (0 : ℤ) ^ 2 = (2 * f.a * x) ^ 2 := by
        ring
      rw [heq]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2ax))
    · have hy2 : (0 : ℤ) < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy0))
      nlinarith [sq_nonneg (2 * f.a * x + f.b * y),
        mul_pos (show (0 : ℤ) < -f.discr by linarith) hy2]
  nlinarith [hpos, ha]

/-- The **principal form** of discriminant `D ≡ 0, 1 (mod 4)`:
`x² − (D/4)y²` if `D ≡ 0`, and `x² + xy + ((1−D)/4)y²` if `D ≡ 1`. (Cox §2.) -/
def principalForm (D : ℤ) : BinaryQF :=
  if D % 4 = 0 then ⟨1, 0, -(D / 4)⟩ else ⟨1, 1, (1 - D) / 4⟩

/-- Every discriminant is `≡ 0` or `1 (mod 4)` (since `b² ≡ 0,1` and `4ac ≡ 0`). -/
theorem discr_mod_four (f : BinaryQF) : f.discr % 4 = 0 ∨ f.discr % 4 = 1 := by
  obtain ⟨a, b, c⟩ := f
  simp only [BinaryQF.discr]
  rcases Int.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
  · left
    have h : (k + k) ^ 2 - 4 * a * c = 4 * (k ^ 2 - a * c) := by ring
    omega
  · right
    have h : (2 * k + 1) ^ 2 - 4 * a * c = 4 * (k ^ 2 + k - a * c) + 1 := by ring
    omega

/-- The principal form has discriminant `D` (for valid discriminants `D ≡ 0,1`). -/
theorem principalForm_discr (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (principalForm D).discr = D := by
  simp only [principalForm]
  rcases hD with h | h
  · rw [if_pos h]; simp only [BinaryQF.discr]; omega
  · rw [if_neg (by omega : ¬ D % 4 = 0)]; simp only [BinaryQF.discr]; omega

/-- The principal form is primitive (its leading coefficient is `1`). -/
theorem principalForm_primitive (D : ℤ) : (principalForm D).Primitive := by
  simp only [principalForm, BinaryQF.Primitive]
  split <;> simp

/-- The principal form has positive leading coefficient `a = 1`. -/
theorem principalForm_pos (D : ℤ) : 0 < (principalForm D).a := by
  simp only [principalForm]; split <;> norm_num

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

end PrimesX2NY2.Forms
