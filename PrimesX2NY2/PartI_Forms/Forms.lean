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

The reduction theorem and finiteness of reduced forms are proved here. Landau's
classification of discriminants with class number one remains unproved.
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

/-- A reduced positive form has its leading coefficient as its least nonzero value. -/
theorem reduced_le_eval (f : BinaryQF) (hr : f.Reduced) (ha : 0 < f.a)
    (x y : ℤ) (hxy : x ≠ 0 ∨ y ≠ 0) : f.a ≤ f.eval x y := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : y ≠ 0 := by tauto
    have hy2pos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    have hy2 : (1 : ℤ) ≤ y ^ 2 := by omega
    have hc : 0 ≤ f.c := le_trans (le_of_lt ha) hr.2.1
    calc
      f.a ≤ f.c := hr.2.1
      _ = f.c * 1 := by ring
      _ ≤ f.c * y ^ 2 := mul_le_mul_of_nonneg_left hy2 hc
      _ = f.eval 0 y := by simp [BinaryQF.eval]
  · rcases eq_or_ne y 0 with rfl | hy
    · have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hx2 : (1 : ℤ) ≤ x ^ 2 := by omega
      calc
        f.a = f.a * 1 := by ring
        _ ≤ f.a * x ^ 2 := mul_le_mul_of_nonneg_left hx2 (le_of_lt ha)
        _ = f.eval x 0 := by simp [BinaryQF.eval]
    · have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hy2pos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      have hx2 : (1 : ℤ) ≤ x ^ 2 := by omega
      have hy2 : (1 : ℤ) ≤ y ^ 2 := by omega
      have hmin : (1 : ℤ) ≤ min (x ^ 2) (y ^ 2) := le_min hx2 hy2
      have hcoeff : f.a ≤ f.a - |f.b| + f.c := by linarith [hr.1, hr.2.1]
      have hcoeff0 : 0 ≤ f.a - |f.b| + f.c :=
        le_trans (le_of_lt ha) hcoeff
      calc
        f.a = f.a * 1 := by ring
        _ ≤ (f.a - |f.b| + f.c) * 1 :=
          mul_le_mul_of_nonneg_right hcoeff (by norm_num)
        _ ≤ (f.a - |f.b| + f.c) * min (x ^ 2) (y ^ 2) :=
          mul_le_mul_of_nonneg_left hmin hcoeff0
        _ ≤ f.eval x y := reduced_eval_lower_bound f hr x y

/-- Equality at the minimum in a reduced positive form can use the second
coordinate only on the boundary `a = c`. -/
theorem eq_c_of_reduced_eval_eq_a_of_right_ne_zero (f : BinaryQF)
    (hr : f.Reduced) (ha : 0 < f.a) (x y : ℤ) (hy : y ≠ 0)
    (heval : f.eval x y = f.a) : f.a = f.c := by
  have hy2pos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hy2 : (1 : ℤ) ≤ y ^ 2 := by omega
  rcases eq_or_ne x 0 with rfl | hx
  · have hc : 0 ≤ f.c := le_trans (le_of_lt ha) hr.2.1
    have hcy : f.c ≤ f.c * y ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hy2 hc
    have hca : f.c ≤ f.a := by
      rw [← heval]
      simpa [BinaryQF.eval] using hcy
    exact le_antisymm hr.2.1 hca
  · have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hx2 : (1 : ℤ) ≤ x ^ 2 := by omega
    have hmin : (1 : ℤ) ≤ min (x ^ 2) (y ^ 2) := le_min hx2 hy2
    have hc_le_coeff : f.c ≤ f.a - |f.b| + f.c := by linarith [hr.1]
    have hcoeff0 : 0 ≤ f.a - |f.b| + f.c := by
      linarith [ha, hr.1, hr.2.1]
    have hc_le_eval : f.c ≤ f.eval x y := calc
      f.c ≤ f.a - |f.b| + f.c := hc_le_coeff
      _ = (f.a - |f.b| + f.c) * 1 := by ring
      _ ≤ (f.a - |f.b| + f.c) * min (x ^ 2) (y ^ 2) :=
        mul_le_mul_of_nonneg_left hmin hcoeff0
      _ ≤ f.eval x y := reduced_eval_lower_bound f hr x y
    rw [heval] at hc_le_eval
    exact le_antisymm hr.2.1 hc_le_eval

/-- A reduced middle coefficient is unique in its residue class modulo `2a`.
The endpoint convention excludes the only two possible wraparounds. -/
private theorem reduced_middle_eq_of_two_mul_dvd
    {a b b' : ℤ} (ha : 0 < a) (hb : |b| ≤ a) (hb' : |b'| ≤ a)
    (htie : |b| = a → 0 ≤ b) (htie' : |b'| = a → 0 ≤ b')
    (hdvd : 2 * a ∣ b' - b) : b' = b := by
  have hb_bounds : -a ≤ b ∧ b ≤ a := abs_le.mp hb
  have hb'_bounds : -a ≤ b' ∧ b' ≤ a := abs_le.mp hb'
  have hb_lower : -a < b := by
    rcases eq_or_lt_of_le hb_bounds.1 with heq | hlt
    · have habs : |b| = a := by
        rw [← heq, abs_neg, abs_of_nonneg (le_of_lt ha)]
      have := htie habs
      omega
    · exact hlt
  have hb'_lower : -a < b' := by
    rcases eq_or_lt_of_le hb'_bounds.1 with heq | hlt
    · have habs : |b'| = a := by
        rw [← heq, abs_neg, abs_of_nonneg (le_of_lt ha)]
      have := htie' habs
      omega
    · exact hlt
  have habs_sub : |b' - b| < 2 * a := by
    rw [abs_lt]
    constructor <;> omega
  have hz : b' - b = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs_sub
  omega

private theorem binaryQF_eq_of_coeff_eq (f g : BinaryQF)
    (ha : f.a = g.a) (hb : f.b = g.b) (hc : f.c = g.c) : f = g := by
  obtain ⟨fa, fb, fc⟩ := f
  obtain ⟨ga, gb, gc⟩ := g
  simp_all

/-- Two properly equivalent reduced positive definite forms coincide, including
the square and hexagonal boundary cases. This is the uniqueness half of reduction. -/
theorem reduced_eq_of_properlyEquivalent (f g : BinaryQF)
    (hf : f.Reduced) (hg : g.Reduced) (hfp : f.PosDef)
    (h : ProperlyEquivalent f g) : f = g := by
  obtain ⟨M, hM, hMf⟩ := h
  have hcolM : M 0 0 ≠ 0 ∨ M 1 0 ≠ 0 := by
    by_contra hzero
    simp only [not_or, not_not] at hzero
    have : M.det = 0 := by simp [Matrix.det_fin_two, hzero.1, hzero.2]
    omega
  have hga_eval : g.a = f.eval (M 0 0) (M 1 0) := by
    rw [← hMf]
    simp [action, BinaryQF.eval]
  have haf_le : f.a ≤ g.a := by
    rw [hga_eval]
    exact reduced_le_eval f hf hfp.1 _ _ hcolM
  have hgD : g.discr < 0 := by
    rw [← discr_eq_of_properlyEquivalent ⟨M, hM, hMf⟩]
    exact hfp.2
  have hga0 : 0 ≤ g.a := le_trans (abs_nonneg g.b) hg.1
  have hga_pos : 0 < g.a := by
    by_contra hnot
    have hga_zero : g.a = 0 := by omega
    simp only [BinaryQF.discr, hga_zero, mul_zero, zero_mul, sub_zero] at hgD
    nlinarith [sq_nonneg g.b]
  have hsym : ProperlyEquivalent g f :=
    properlyEquivalent_equivalence.symm ⟨M, hM, hMf⟩
  obtain ⟨N, hN, hNg⟩ := hsym
  have hcolN : N 0 0 ≠ 0 ∨ N 1 0 ≠ 0 := by
    by_contra hzero
    simp only [not_or, not_not] at hzero
    have : N.det = 0 := by simp [Matrix.det_fin_two, hzero.1, hzero.2]
    omega
  have hfa_eval : f.a = g.eval (N 0 0) (N 1 0) := by
    rw [← hNg]
    simp [action, BinaryQF.eval]
  have hga_le : g.a ≤ f.a := by
    rw [hfa_eval]
    exact reduced_le_eval g hg hga_pos _ _ hcolN
  have haeq : f.a = g.a := le_antisymm haf_le hga_le
  have hminM : f.eval (M 0 0) (M 1 0) = f.a := by rw [← hga_eval, ← haeq]
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hM
  have hgb : g.b =
      2 * f.a * M 0 0 * M 0 1 +
        f.b * (M 0 0 * M 1 1 + M 0 1 * M 1 0) +
          2 * f.c * M 1 0 * M 1 1 := by
    rw [← hMf]
    rfl
  rcases eq_or_ne (M 1 0) 0 with hr0 | hr0
  · have hdiv : 2 * f.a ∣ g.b - f.b := by
      simp only [hr0, mul_zero, zero_mul, add_zero] at hdet hgb
      refine ⟨M 0 0 * M 0 1, ?_⟩
      rw [hgb]
      linear_combination f.b * hdet
    have hb_eq : g.b = f.b := reduced_middle_eq_of_two_mul_dvd hfp.1 hf.1
      (by simpa only [haeq] using hg.1) (fun heq ↦ hf.2.2 (Or.inl heq))
      (fun heq ↦ hg.2.2 (Or.inl (by rwa [← haeq]))) hdiv
    have hdisc := discr_eq_of_properlyEquivalent ⟨M, hM, hMf⟩
    simp only [BinaryQF.discr] at hdisc
    rw [hb_eq, ← haeq] at hdisc
    have hprod_eq : f.a * (g.c - f.c) = 0 := by nlinarith
    have hceq : f.c = g.c := by
      rcases mul_eq_zero.mp hprod_eq with ha0 | hca0
      · omega
      · omega
    exact binaryQF_eq_of_coeff_eq f g haeq hb_eq.symm hceq
  · have hac : f.a = f.c :=
      eq_c_of_reduced_eval_eq_a_of_right_ne_zero f hf hfp.1 _ _ hr0 hminM
    rcases eq_or_lt_of_le hf.1 with hhex | hstrict
    · have hfb0 : 0 ≤ f.b := hf.2.2 (Or.inl hhex)
      have hfb : f.b = f.a := by
        rw [abs_of_nonneg hfb0] at hhex
        exact hhex
      have hgb_bounds : -f.a ≤ g.b ∧ g.b ≤ f.a := by
        have := abs_le.mp hg.1
        omega
      have hgc_lower : f.a ≤ g.c := by
        rw [haeq]
        exact hg.2.1
      have hgb_sq : g.b ^ 2 ≤ f.a ^ 2 := by
        have hsum : 0 ≤ f.a + g.b := by omega
        have hmul : 0 ≤ (f.a - g.b) * (f.a + g.b) :=
          mul_nonneg (sub_nonneg.mpr hgb_bounds.2) hsum
        nlinarith
      have hdisc := discr_eq_of_properlyEquivalent ⟨M, hM, hMf⟩
      simp only [BinaryQF.discr] at hdisc
      rw [hfb, ← hac, ← haeq] at hdisc
      have hprod0 : 0 ≤ f.a * (g.c - f.a) :=
        mul_nonneg (le_of_lt hfp.1) (sub_nonneg.mpr hgc_lower)
      have hprod_eq : f.a * (g.c - f.a) = 0 := by
        nlinarith [hgb_sq, hprod0]
      have hgc : g.c = f.a := by
        rcases mul_eq_zero.mp hprod_eq with ha0 | hca0
        · omega
        · omega
      rw [hgc] at hdisc
      have hgb_sq_eq : g.b ^ 2 = f.a ^ 2 := by nlinarith
      have hgb0 : 0 ≤ g.b := hg.2.2 (Or.inr (by omega))
      have hgb_eq : g.b = f.a := by
        rcases eq_or_eq_neg_of_sq_eq_sq g.b f.a hgb_sq_eq with heq | heq
        · exact heq
        · omega
      exact binaryQF_eq_of_coeff_eq f g haeq (by omega) (by omega)
    · have hp0 : M 0 0 = 0 := by
        by_contra hp0
        have hp2pos : 0 < M 0 0 ^ 2 := sq_pos_of_ne_zero hp0
        have hr2pos : 0 < M 1 0 ^ 2 := sq_pos_of_ne_zero hr0
        have hp2 : (1 : ℤ) ≤ M 0 0 ^ 2 := by omega
        have hr2 : (1 : ℤ) ≤ M 1 0 ^ 2 := by omega
        have hmin : (1 : ℤ) ≤ min (M 0 0 ^ 2) (M 1 0 ^ 2) := le_min hp2 hr2
        have hcoeff_pos : 0 < f.a - |f.b| + f.c := by linarith
        have hcoeff_le : f.a - |f.b| + f.c ≤
            (f.a - |f.b| + f.c) * min (M 0 0 ^ 2) (M 1 0 ^ 2) := by
          simpa using mul_le_mul_of_nonneg_left hmin (le_of_lt hcoeff_pos)
        have hlower := reduced_eval_lower_bound f hf (M 0 0) (M 1 0)
        have : f.a < f.eval (M 0 0) (M 1 0) := by
          calc
            f.a < f.a - |f.b| + f.c := by linarith
            _ ≤ _ := hcoeff_le
            _ ≤ _ := hlower
        omega
      have hdiv : 2 * f.a ∣ g.b - (-f.b) := by
        rw [← hac] at hgb
        simp only [hp0, mul_zero, zero_mul, zero_add] at hdet hgb
        refine ⟨M 1 0 * M 1 1, ?_⟩
        rw [hgb]
        linear_combination -f.b * hdet
      have hneg_tie : |-f.b| = f.a → 0 ≤ -f.b := by
        intro heq
        have : |f.b| = f.a := by simpa only [abs_neg] using heq
        omega
      have hgb_eq : g.b = -f.b := reduced_middle_eq_of_two_mul_dvd hfp.1
        (by simpa only [abs_neg] using le_of_lt hstrict)
        (by simpa only [haeq] using hg.1) hneg_tie
        (fun heq ↦ hg.2.2 (Or.inl (by rwa [← haeq]))) hdiv
      have hgb_sq : g.b ^ 2 = f.b ^ 2 := by rw [hgb_eq]; ring
      have hdisc := discr_eq_of_properlyEquivalent ⟨M, hM, hMf⟩
      simp only [BinaryQF.discr] at hdisc
      rw [hgb_sq, ← hac, ← haeq] at hdisc
      have hprod_eq : f.a * (g.c - f.a) = 0 := by nlinarith
      have hgc : g.c = f.a := by
        rcases mul_eq_zero.mp hprod_eq with ha0 | hca0
        · omega
        · omega
      have hfb0 : 0 ≤ f.b := hf.2.2 (Or.inr hac)
      have hgb0 : 0 ≤ g.b := hg.2.2 (Or.inr (by omega))
      have hfb : f.b = 0 := by omega
      have hgb' : g.b = 0 := by omega
      exact binaryQF_eq_of_coeff_eq f g haeq (by omega) (by omega)

/-- Translation by `t`: `⟨a,b,c⟩ ~ ⟨a, b+2at, at²+bt+c⟩` (the `SL₂` matrix `!![1,t;0,1]`). -/
theorem translate_equiv (a b c t : ℤ) :
    ProperlyEquivalent (⟨a, b, c⟩ : BinaryQF) ⟨a, b + 2 * a * t, a * t ^ 2 + b * t + c⟩ := by
  refine ⟨!![1, t; 0, 1], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; ring
  · simp only [action, BinaryQF.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const]
    refine ⟨by ring, by ring, by ring⟩

/-- The quarter-turn `⟨a,b,c⟩ ~ ⟨c,-b,a⟩` (the `SL₂` matrix `!![0,-1;1,0]`). -/
theorem swap_equiv (a b c : ℤ) :
    ProperlyEquivalent (⟨a, b, c⟩ : BinaryQF) ⟨c, -b, a⟩ := by
  refine ⟨!![0, -1; 1, 0], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; ring
  · simp only [action, BinaryQF.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const]
    refine ⟨by ring, by ring, by ring⟩

/-- Reduce the middle coefficient into `(-a, a]` by a translation. -/
theorem normalize_b (a b c : ℤ) (ha : 0 < a) :
    ∃ B C : ℤ, ProperlyEquivalent (⟨a, b, c⟩ : BinaryQF) ⟨a, B, C⟩ ∧ |B| ≤ a := by
  have h2a : (0 : ℤ) < 2 * a := by positivity
  have hmod : 0 ≤ b % (2 * a) ∧ b % (2 * a) < 2 * a :=
    ⟨Int.emod_nonneg b (by positivity), Int.emod_lt_of_pos b h2a⟩
  have hid : b % (2 * a) + (2 * a) * (b / (2 * a)) = b := Int.emod_add_ediv b (2 * a)
  set k := if b % (2 * a) ≤ a then -(b / (2 * a)) else -(b / (2 * a)) - 1 with hkdef
  have hBle : |b + 2 * a * k| ≤ a := by
    by_cases h : b % (2 * a) ≤ a
    · have hB : b + 2 * a * k = b % (2 * a) := by rw [hkdef, if_pos h]; linear_combination -hid
      rw [hB, abs_le]; exact ⟨by linarith [hmod.1], h⟩
    · have hB : b + 2 * a * k = b % (2 * a) - 2 * a := by rw [hkdef, if_neg h]; linear_combination -hid
      rw [hB, abs_le]; have h' := not_le.mp h; exact ⟨by linarith, by linarith [hmod.2]⟩
  exact ⟨b + 2 * a * k, a * k ^ 2 + b * k + c, translate_equiv a b c k, hBle⟩

/-- **Reduction theorem** (Cox, Thm 2.8). Every positive definite form is properly
equivalent to a unique reduced form. Existence is the reduction algorithm (translate the
middle coefficient into `(-a,a]`, then swap when `c < a`, strong induction on `a.natAbs`);
uniqueness is `reduced_eq_of_properlyEquivalent`. -/
theorem exists_unique_reduced (f : BinaryQF) (hf : f.PosDef) :
    ∃! g : BinaryQF, g.Reduced ∧ ProperlyEquivalent f g := by
  -- existence via strong induction on the leading coefficient
  have exred : ∀ (n : ℕ) (g : BinaryQF), g.PosDef → g.a.natAbs = n →
      ∃ h, h.Reduced ∧ ProperlyEquivalent g h := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro g hg hn
      have hga : 0 < g.a := hg.1
      have hgd : g.discr < 0 := hg.2
      obtain ⟨B, C, hBC, hBle⟩ := normalize_b g.a g.b g.c hga
      have hd1 : (⟨g.a, B, C⟩ : BinaryQF).discr = g.discr :=
        (discr_eq_of_properlyEquivalent hBC).symm
      have hCpos : 0 < C := by
        have hlt : (⟨g.a, B, C⟩ : BinaryQF).discr < 0 := by rw [hd1]; exact hgd
        simp only [BinaryQF.discr] at hlt; nlinarith [sq_nonneg B, hga]
      by_cases hca : g.a ≤ C
      · by_cases hred : (⟨g.a, B, C⟩ : BinaryQF).Reduced
        · exact ⟨_, hred, hBC⟩
        · have hbnd : ¬ ((|B| = g.a ∨ g.a = C) → 0 ≤ B) := fun h => hred ⟨hBle, hca, h⟩
          push_neg at hbnd
          obtain ⟨hbound, hBneg⟩ := hbnd
          rcases hbound with hBa | haC
          · -- |B| = g.a with B < 0 ⇒ B = -g.a; translate to ⟨a, a, C⟩
            have hBeq : B = -g.a := by
              have := abs_of_neg hBneg; rw [this] at hBa; linarith
            have htr : ProperlyEquivalent (⟨g.a, B, C⟩ : BinaryQF) ⟨g.a, g.a, C⟩ := by
              have h := translate_equiv g.a B C 1
              rw [hBeq] at h ⊢
              convert h using 2 <;> ring
            have hredF : (⟨g.a, g.a, C⟩ : BinaryQF).Reduced :=
              ⟨by rw [abs_of_nonneg hga.le], hca, fun _ => hga.le⟩
            exact ⟨_, hredF, properlyEquivalent_equivalence.trans hBC htr⟩
          · -- g.a = C with B < 0 ⇒ swap ⟨a,B,a⟩ → ⟨a,-B,a⟩
            have hswap : ProperlyEquivalent (⟨g.a, B, C⟩ : BinaryQF) ⟨C, -B, g.a⟩ :=
              swap_equiv g.a B C
            have hredF : (⟨C, -B, g.a⟩ : BinaryQF).Reduced := by
              rw [← haC]
              exact ⟨by rw [abs_neg]; exact hBle, le_refl _, fun _ => by linarith⟩
            exact ⟨_, hredF, properlyEquivalent_equivalence.trans hBC hswap⟩
      · -- C < g.a : swap and recurse on the smaller leading coefficient
        push_neg at hca
        have hswap : ProperlyEquivalent (⟨g.a, B, C⟩ : BinaryQF) ⟨C, -B, g.a⟩ :=
          swap_equiv g.a B C
        have hdsw : (⟨C, -B, g.a⟩ : BinaryQF).discr = g.discr := by
          have : (⟨C, -B, g.a⟩ : BinaryQF).discr = (⟨g.a, B, C⟩ : BinaryQF).discr := by
            simp only [BinaryQF.discr]; ring
          rw [this, hd1]
        have hposC : (⟨C, -B, g.a⟩ : BinaryQF).PosDef := ⟨hCpos, by rw [hdsw]; exact hgd⟩
        have hlt : (⟨C, -B, g.a⟩ : BinaryQF).a.natAbs < n := by
          rw [← hn]; show C.natAbs < g.a.natAbs; omega
        obtain ⟨h, hred, hh⟩ := ih _ hlt ⟨C, -B, g.a⟩ hposC rfl
        exact ⟨h, hred, properlyEquivalent_equivalence.trans hBC
          (properlyEquivalent_equivalence.trans hswap hh)⟩
  obtain ⟨g0, hg0red, hg0eq⟩ := exred f.a.natAbs f hf rfl
  refine ⟨g0, ⟨hg0red, hg0eq⟩, ?_⟩
  rintro g' ⟨hg'red, hg'eq⟩
  have hgg : ProperlyEquivalent g' g0 :=
    properlyEquivalent_equivalence.trans (properlyEquivalent_equivalence.symm hg'eq) hg0eq
  have hg'pos : g'.PosDef := by
    have hb := hg'red.1
    have ha0 : 0 ≤ g'.a := le_trans (abs_nonneg _) hb
    have hdlt : g'.discr < 0 := by rw [← discr_eq_of_properlyEquivalent hg'eq]; exact hf.2
    refine ⟨?_, hdlt⟩
    rcases eq_or_lt_of_le ha0 with h | h
    · exfalso
      have hb0 : g'.b = 0 := by rw [← h] at hb; exact abs_nonpos_iff.mp hb
      have hz : g'.discr = 0 := by simp only [BinaryQF.discr, ← h, hb0]; ring
      rw [hz] at hdlt; exact absurd hdlt (lt_irrefl 0)
    · exact h
  exact reduced_eq_of_properlyEquivalent g' g0 hg'red hg0red hg'pos hgg

/-- **Finiteness of class number** (Cox, Thm 2.13). For each discriminant `D < 0`
there are only finitely many reduced forms, hence finitely many proper
equivalence classes. -/
theorem finite_reduced_of_discr (D : ℤ) (hD : D < 0) :
    {f : BinaryQF | f.discr = D ∧ f.Reduced}.Finite := by
  set N : ℤ := -D with hN
  refine Set.Finite.of_finite_image (f := fun f : BinaryQF => (f.a, f.b)) ?_ ?_
  · -- the image lands in a finite box `1 ≤ a ≤ N`, `-N ≤ b ≤ N`
    apply Set.Finite.subset (Finset.Icc ((1 : ℤ), (-N)) (N, N)).finite_toSet
    rintro y ⟨f, ⟨hfd, hfr⟩, rfl⟩
    obtain ⟨hb, hac, _⟩ := hfr
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb            -- -f.a ≤ f.b ≤ f.a
    have ha0 : 0 ≤ f.a := le_trans (abs_nonneg f.b) hb
    have hane : f.a ≠ 0 := by
      rintro h0
      have hb0 : f.b = 0 := by rw [h0] at hb; exact abs_nonpos_iff.mp hb
      have hD0 : D = 0 := by rw [← hfd]; simp [BinaryQF.discr, h0, hb0]
      omega
    have ha1 : 1 ≤ f.a := by omega
    have hdd : 4 * f.a * f.c - f.b ^ 2 = N := by
      have : f.b ^ 2 - 4 * f.a * f.c = D := hfd
      omega
    have hbsq : f.b ^ 2 ≤ f.a ^ 2 := by nlinarith [hb1, hb2]
    have h3a2 : 3 * f.a ^ 2 ≤ N := by nlinarith [hdd, hac, ha0, hbsq]
    have haN : f.a ≤ N := by nlinarith [h3a2, ha1]
    simp only [Finset.coe_Icc, Set.mem_Icc, Prod.mk_le_mk]
    exact ⟨⟨ha1, by omega⟩, ⟨haN, by omega⟩⟩
  · -- injective on the set: `(a, b)` and `discr = D` determine `c`, hence `f`
    rintro f ⟨hfd, hfr⟩ g ⟨hgd, hgr⟩ hfg
    have haeq : f.a = g.a := congrArg Prod.fst hfg
    have hbeq : f.b = g.b := congrArg Prod.snd hfg
    obtain ⟨hb, _, _⟩ := hfr
    have ha0 : 0 ≤ f.a := le_trans (abs_nonneg f.b) hb
    have hane : f.a ≠ 0 := by
      rintro h0
      have hb0 : f.b = 0 := by rw [h0] at hb; exact abs_nonpos_iff.mp hb
      have hD0 : D = 0 := by rw [← hfd]; simp [BinaryQF.discr, h0, hb0]
      omega
    have hapos : 0 < f.a := lt_of_le_of_ne ha0 (Ne.symm hane)
    have hceq : f.c = g.c := by
      have e1 : f.b ^ 2 - 4 * f.a * f.c = D := hfd
      have e2 : g.b ^ 2 - 4 * g.a * g.c = D := hgd
      rw [← haeq, ← hbeq] at e2
      have h4 : (4 * f.a) * f.c = (4 * f.a) * g.c := by linear_combination e2 - e1
      exact mul_left_cancel₀ (by positivity) h4
    exact binaryQF_eq_of_coeff_eq f g haeq hbeq hceq

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
