/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.Genus

/-!
# Part I, §2 - Exercises

Faithful `sorry`-bodied statements of the exercises of Cox §2 (Exercises 2.1-2.27),
one node per sub-part, cited by number only.

Flagged in the blueprint as `\notready` (no Lean signature): 2.9(a), 2.9(b),
2.17(d), 2.19, 2.20 - see the §2 FLAG LIST in the report.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.PartI.S2

open PrimesX2NY2.Forms PrimesX2NY2.Genus

/-- **Exercise 2.1.** If `f` represents `m`, then `m = d²m'` with `f` properly
representing `m'`. -/
theorem ex_2_1 (f : BinaryQF) (m : ℤ) (h : Represents f m) :
    ∃ d m' : ℤ, m = d ^ 2 * m' ∧ ProperlyRepresents f m' := by
  sorry

/-- **Exercise 2.2(a).** Equivalence and proper equivalence are equivalence
relations. -/
theorem ex_2_2_a : Equivalence Equivalent ∧ Equivalence ProperlyEquivalent :=
  ⟨equivalent_equivalence, properlyEquivalent_equivalence⟩

/-- **Exercise 2.2(b).** Improper equivalence (`det = −1`) is not an equivalence
relation. -/
theorem ex_2_2_b :
    ¬ Equivalence (fun f g : BinaryQF =>
      ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = -1 ∧ action M f = g) := by
  sorry

/-- **Exercise 2.2(c).** Equivalent forms represent the same numbers. -/
theorem ex_2_2_c (f g : BinaryQF) (h : Equivalent f g) (m : ℤ) :
    Represents f m ↔ Represents g m := by
  have fwd : ∀ f' g' : BinaryQF, Equivalent f' g' → Represents g' m → Represents f' m := by
    rintro f' g' ⟨M, _, rfl⟩ ⟨x, y, hxy⟩
    rw [eval_action] at hxy
    exact ⟨_, _, hxy⟩
  exact ⟨fwd g f (equivalent_equivalence.symm h), fwd f g h⟩

/-- **Exercise 2.2(d).** Any form equivalent to a primitive form is primitive. -/
theorem ex_2_2_d (f g : BinaryQF) (h : Equivalent f g) (hf : f.Primitive) :
    g.Primitive := by
  obtain ⟨M, hdet, rfl⟩ := h
  rcases hdet with hd | hd
  · exact (primitive_action_iff M f hd).mpr hf
  · have hMD : (M * !![1, 0; 0, -1]).det = 1 := by
      rw [Matrix.det_mul, hd, Matrix.det_fin_two_of]; ring
    have hact : action (M * !![1, 0; 0, -1]) f
        = ⟨(action M f).a, -(action M f).b, (action M f).c⟩ := by
      rw [← action_mul]
      simp only [action, BinaryQF.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons, Matrix.head_fin_const]
      refine ⟨by ring, by ring, by ring⟩
    have hprim := (primitive_action_iff (M * !![1, 0; 0, -1]) f hMD).mpr hf
    rw [hact] at hprim
    simpa [BinaryQF.Primitive, Int.gcd, Int.natAbs_neg] using hprim

/-- **Exercise 2.3.** Under `f = g(px+qy, rx+sy)`, `D_f = (ps−qr)² D_g`. -/
theorem ex_2_3 (M : Matrix (Fin 2) (Fin 2) ℤ) (g : BinaryQF) :
    (action M g).discr = M.det ^ 2 * g.discr :=
  discr_action M g

/-- **Exercise 2.4(a).** A form of positive discriminant represents both positive
and negative integers. -/
theorem ex_2_4_a (f : BinaryQF) (h : 0 < f.discr) :
    (∃ x y : ℤ, 0 < f.eval x y) ∧ (∃ x y : ℤ, f.eval x y < 0) := by
  obtain ⟨a, b, c⟩ := f
  simp only [BinaryQF.discr] at h
  simp only [BinaryQF.eval]
  by_cases ha : a = 0
  · subst ha
    by_cases hc : c = 0
    · subst hc
      have hb : b ≠ 0 := by rintro rfl; norm_num at h
      rcases lt_or_gt_of_ne hb with hb' | hb'
      · exact ⟨⟨1, -1, by nlinarith [hb']⟩, ⟨1, 1, by nlinarith [hb']⟩⟩
      · exact ⟨⟨1, 1, by nlinarith [hb']⟩, ⟨1, -1, by nlinarith [hb']⟩⟩
    · rcases lt_or_gt_of_ne hc with hc' | hc'
      · exact ⟨⟨-2 * c, b, by nlinarith [mul_pos (neg_pos.mpr hc') h]⟩,
              ⟨0, 1, by nlinarith [hc']⟩⟩
      · exact ⟨⟨0, 1, by nlinarith [hc']⟩,
              ⟨-2 * c, b, by nlinarith [mul_pos hc' h]⟩⟩
  · rcases lt_or_gt_of_ne ha with ha' | ha'
    · exact ⟨⟨b, -2 * a, by nlinarith [mul_pos (neg_pos.mpr ha') h]⟩,
            ⟨1, 0, by nlinarith [ha']⟩⟩
    · exact ⟨⟨1, 0, by nlinarith [ha']⟩,
            ⟨b, -2 * a, by nlinarith [mul_pos ha' h]⟩⟩

/-- **Exercise 2.4(b).** A form of negative discriminant represents only positive
(resp. only negative) values according to the sign of `a`. -/
theorem ex_2_4_b (f : BinaryQF) (h : f.discr < 0) :
    (0 < f.a → ∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) → 0 < f.eval x y) ∧
      (f.a < 0 → ∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) → f.eval x y < 0) := by
  refine ⟨fun ha x y hxy => eval_pos_of_posDef f ⟨ha, h⟩ x y hxy, fun ha x y hxy => ?_⟩
  have hgd : (⟨-f.a, -f.b, -f.c⟩ : BinaryQF).discr = f.discr := by simp only [BinaryQF.discr]; ring
  have hg : (⟨-f.a, -f.b, -f.c⟩ : BinaryQF).PosDef := ⟨by linarith, by rw [hgd]; exact h⟩
  have hp := eval_pos_of_posDef ⟨-f.a, -f.b, -f.c⟩ hg x y hxy
  simp only [BinaryQF.eval] at hp ⊢
  linarith

/-- **Exercise 2.5.** Corollary 2.6 for arbitrary discriminant: for `D ≡ 0,1
(mod 4)` and an odd prime `p ∤ D`, `(D/p) = 1` iff `p` is represented by a
primitive form of discriminant `D`. -/
theorem ex_2_5 (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hpD : ¬ (p : ℤ) ∣ D) :
    IsSquare (D : ZMod p)
      ↔ ∃ f : BinaryQF, f.discr = D ∧ f.Primitive ∧ Represents f (p : ℤ) := by
  sorry

/-- **Exercise 2.6.** There is a reduced form properly equivalent to
`126x² + 74xy + 13y²`. -/
theorem ex_2_6 : ∃ f : BinaryQF, f.Reduced ∧ ProperlyEquivalent ⟨126, 74, 13⟩ f := by
  have hpd : (⟨126, 74, 13⟩ : BinaryQF).PosDef := by
    refine ⟨by norm_num, ?_⟩
    show (⟨126, 74, 13⟩ : BinaryQF).discr < 0
    simp only [BinaryQF.discr]; norm_num
  obtain ⟨g, ⟨hred, heq⟩, _⟩ := exists_unique_reduced ⟨126, 74, 13⟩ hpd
  exact ⟨g, hred, heq⟩

/-- **Exercise 2.7.** The bound (2.9): for `|b| ≤ a ≤ c`,
`(a − |b| + c)·min(x², y²) ≤ f(x,y)`. -/
theorem ex_2_7 (f : BinaryQF) (h1 : |f.b| ≤ f.a) (h2 : f.a ≤ f.c) (x y : ℤ) :
    (f.a - |f.b| + f.c) * min (x ^ 2) (y ^ 2) ≤ f.eval x y := by
  cases abs_cases f.b <;> simp_all +decide [ BinaryQF.eval ];
  · cases le_total ( x ^ 2 ) ( y ^ 2 ) <;> simp_all +decide [ abs_of_nonneg ];
    · nlinarith [ sq_nonneg ( x + y ), sq_nonneg ( x - y ), mul_le_mul_of_nonneg_left ‹x ^ 2 ≤ y ^ 2› ( show 0 ≤ f.c by linarith ) ];
    · nlinarith [ sq_nonneg ( x + y ), sq_nonneg ( x - y ) ];
  · cases le_total ( x ^ 2 ) ( y ^ 2 ) <;> simp +decide [ * ]; all_goals rw [ abs_of_nonpos ] <;> nlinarith [ sq_nonneg ( x + y ), sq_nonneg ( x - y ) ]

/-- **Exercise 2.8(a).** Proof of (2.11): for a reduced form with `|b| < a < c`,
`f` takes the value `a` (resp. `c`) primitively only at `±(1,0)` (resp.
`±(0,1)`). -/
theorem ex_2_8_a (f : BinaryQF) (hr : f.Reduced) (h1 : |f.b| < f.a) (h2 : f.a < f.c)
    (x y : ℤ) (hcop : IsCoprime x y) :
    (f.eval x y = f.a ↔ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0)) ∧
      (f.eval x y = f.c ↔ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)) := by
  exact reduced_strict_value_rigidity f hr h1 h2 x y hcop

/-- **Exercise 2.8(b).** Uniqueness part of Theorem 2.8 (incl. the exceptional
cases `|b| = a`, `a = c`): two properly equivalent reduced positive definite
forms are equal. -/
theorem ex_2_8_b (f g : BinaryQF) (hf : f.Reduced) (hg : g.Reduced) (hfp : f.PosDef)
    (h : ProperlyEquivalent f g) : f = g := by
  exact reduced_eq_of_properlyEquivalent f g hf hg hfp h

/-- **Exercise 2.10(a).** For indefinite nonsquare discriminant, every form is
properly equivalent to one with `|b| ≤ |a| ≤ |c|`. -/
theorem ex_2_10_a (g : BinaryQF) (h : 0 < g.discr) (hns : ¬ IsSquare g.discr) :
    ∃ f : BinaryQF, ProperlyEquivalent g f ∧ |f.b| ≤ |f.a| ∧ |f.a| ≤ |f.c| := by
  sorry

/-- **Exercise 2.10(b).** Such a form satisfies `4a² ≤ D` (i.e. `|a| ≤ √D/2`). -/
theorem ex_2_10_b (f : BinaryQF) (h1 : |f.b| ≤ |f.a|) (h2 : |f.a| ≤ |f.c|)
    (hD : 0 < f.discr) (hns : ¬ IsSquare f.discr) : 4 * f.a ^ 2 ≤ f.discr := by
  sorry

/-- **Exercise 2.10(c).** Hence there are finitely many such reduced forms, so the
class number `h(D)` is finite for indefinite `D`. -/
theorem ex_2_10_c (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    {f : BinaryQF | f.discr = D ∧ |f.b| ≤ |f.a| ∧ |f.a| ≤ |f.c|}.Finite := by
  sorry

/-- **Exercise 2.11.** The result (2.17): for a prime `p ≠ 7`, `p = x² + 7y²` iff
`p ≡ 1,9,11,15,23,25 (mod 28)`. -/
theorem ex_2_11 (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hp7 : p ≠ 7) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 7 * y ^ 2) ↔
      p % 28 = 1 ∨ p % 28 = 9 ∨ p % 28 = 11 ∨ p % 28 = 15 ∨ p % 28 = 23
        ∨ p % 28 = 25 := by
  sorry

/-- **Exercise 2.12(a).** An integer `> 1` that is not a prime power factors as
`m = ac` with `1 < a < c` and `gcd(a,c) = 1`. -/
theorem ex_2_12_a (m : ℕ) (hm : 1 < m) (hnp : ¬ ∃ p k : ℕ, p.Prime ∧ m = p ^ k) :
    ∃ a c : ℕ, 1 < a ∧ a < c ∧ m = a * c ∧ Nat.Coprime a c := by
  sorry

/-- **Exercise 2.12(b).** `h(−32) = 2` and `h(−124) = 3`. -/
theorem ex_2_12_b :
    {f : BinaryQF | f.discr = -32 ∧ f.Reduced ∧ f.Primitive}.ncard = 2 ∧
      {f : BinaryQF | f.discr = -124 ∧ f.Reduced ∧ f.Primitive}.ncard = 3 := by
  sorry

/-- **Exercise 2.13.** The result (2.19): for an odd prime `p ∤ 5`,
`p ≡ 1,3,7,9 (mod 20)` iff `(−5/p) = 1`. -/
theorem ex_2_13 (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hp5 : ¬ (p : ℤ) ∣ 5) :
    (p % 20 = 1 ∨ p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 9)
      ↔ IsSquare ((-5 : ℤ) : ZMod p) := by
  sorry

/-- **Exercise 2.14.** The result (2.20): in `(ℤ/20ℤ)ˣ`, the form `x²+5y²`
represents only `1, 9` and `2x²+2xy+3y²` represents only `3, 7`. -/
theorem ex_2_14 (m : ℤ) (hco : IsCoprime m 20) :
    (Represents ⟨1, 0, 5⟩ m → (m : ZMod 20) = 1 ∨ (m : ZMod 20) = 9) ∧
      (Represents ⟨2, 2, 3⟩ m → (m : ZMod 20) = 3 ∨ (m : ZMod 20) = 7) := by
  sorry

/-- **Exercise 2.15.** The result (2.23): for a prime `p ≠ 7`, `p = x²+14y²` or
`2x²+7y²` iff `p ≡ 1,9,15,23,25,39 (mod 56)`. -/
theorem ex_2_15 (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hp7 : p ≠ 7) :
    ((∃ x y : ℤ, (p : ℤ) = x ^ 2 + 14 * y ^ 2)
        ∨ (∃ x y : ℤ, (p : ℤ) = 2 * x ^ 2 + 7 * y ^ 2)) ↔
      p % 56 = 1 ∨ p % 56 = 9 ∨ p % 56 = 15 ∨ p % 56 = 23 ∨ p % 56 = 25
        ∨ p % 56 = 39 := by
  sorry

/-- **Exercise 2.16.** For `D ≡ 1 (mod 4)`, the form `x² + xy + ((1−D)/4)y²` has
discriminant `D` and is reduced when `D < 0`. -/
theorem ex_2_16 (D : ℤ) (hD : D % 4 = 1) :
    (principalForm D).discr = D ∧ (D < 0 → (principalForm D).Reduced) := by
  have hpf : principalForm D = ⟨1, 1, (1 - D) / 4⟩ := by
    simp only [principalForm]; rw [if_neg (by omega)]
  have h4 : (4 : ℤ) ∣ (1 - D) := by omega
  have he : 4 * ((1 - D) / 4) = 1 - D := Int.mul_ediv_cancel' h4
  refine ⟨?_, ?_⟩
  · rw [hpf]; simp only [BinaryQF.discr]; linear_combination -he
  · intro hDneg; rw [hpf]
    refine ⟨?_, ?_, ?_⟩
    · show |(1 : ℤ)| ≤ 1; norm_num
    · show (1 : ℤ) ≤ (1 - D) / 4; omega
    · intro _; show (0 : ℤ) ≤ 1; norm_num

/-- **Exercise 2.17(a).** For `D ≡ 1 (mod 4)`, an even number properly represented
by a form of discriminant `D` forces `D ≡ 1 (mod 8)`. -/
theorem ex_2_17_a (D : ℤ) (hD : D % 4 = 1) (f : BinaryQF) (hf : f.discr = D)
    (m : ℤ) (hm : Even m) (h : ProperlyRepresents f m) : D % 8 = 1 := by
  sorry

/-- **Exercise 2.17(b).** For `D ≡ 1 (mod 4)`, an odd `m` prime to `D` represented
by a form of discriminant `D` has `(D/m) = 1`. -/
theorem ex_2_17_b (D : ℤ) (hD : D % 4 = 1) (m : ℤ) (hm : Odd m) (hco : IsCoprime m D)
    (f : BinaryQF) (hf : f.discr = D) (h : Represents f m) :
    jacobiSym D m.natAbs = 1 := by
  sorry

/-- **Exercise 2.17(c).** For negative `D ≡ 1 (mod 4)`, the residues represented by
the principal form are exactly the squares in `(ℤ/Dℤ)ˣ`. -/
theorem ex_2_17_c (D : ℤ) (hD : D % 4 = 1) (hDneg : D < 0) (u : (ZMod D.natAbs)ˣ) :
    (∃ x y : ℤ, IsCoprime x y ∧
        ((principalForm D).eval x y : ZMod D.natAbs) = (u : ZMod D.natAbs))
      ↔ IsSquare u := by
  sorry

/-- **Exercise 2.18(a).** For a primitive form and a prime `p`, at least one of
`f(1,0), f(0,1), f(1,1)` is prime to `p`. -/
theorem ex_2_18_a (f : BinaryQF) (hf : f.Primitive) (p : ℕ) (hp : p.Prime) :
    ¬ (p : ℤ) ∣ f.eval 1 0 ∨ ¬ (p : ℤ) ∣ f.eval 0 1 ∨ ¬ (p : ℤ) ∣ f.eval 1 1 := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have e1 : f.eval 1 0 = f.a := by simp [BinaryQF.eval]
  have e2 : f.eval 0 1 = f.c := by simp [BinaryQF.eval]
  have e3 : f.eval 1 1 = f.a + f.b + f.c := by simp only [BinaryQF.eval]; ring
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  have hpb : (p : ℤ) ∣ f.b := by
    have hrw : f.b = (f.a + f.b + f.c) - f.a - f.c := by ring
    rw [hrw]; exact dvd_sub (dvd_sub h3 h1) h2
  have d1 : p ∣ f.a.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h1
  have d2 : p ∣ f.b.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hpb
  have d3 : p ∣ f.c.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h2
  have dgg : p ∣ Int.gcd (Int.gcd f.a f.b) f.c := Nat.dvd_gcd (Nat.dvd_gcd d1 d2) d3
  rw [hf] at dgg
  exact hp.ne_one (Nat.dvd_one.mp dgg)

/-- **Exercise 2.18(b).** Proof of Lemma 2.25. -/
theorem ex_2_18_b (f : BinaryQF) (M : ℤ) :
    ∃ x y : ℤ, IsCoprime x y ∧ IsCoprime (f.eval x y) M := by
  sorry

/-- **Exercise 2.21.** The first theorem of (2.28): for a prime `p ≠ 3`,
`p = x² + 6y²` iff `p ≡ 1, 7 (mod 24)`. -/
theorem ex_2_21 (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hp3 : p ≠ 3) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 6 * y ^ 2) ↔ p % 24 = 1 ∨ p % 24 = 7 := by
  sorry

/-- **Exercise 2.22.** The composition identity (2.31) (and its special case
(2.30)). -/
theorem ex_2_22 (a b c x y z w : ℤ) :
    (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) * (a * z ^ 2 + 2 * b * z * w + c * w ^ 2)
      = (a * x * z + b * x * w + b * y * z + c * y * w) ^ 2
        + (a * c - b ^ 2) * (x * w - y * z) ^ 2 := by
  ring

/-- **Exercise 2.23(c).** Any form of discriminant `8` is properly equivalent to
`±(x² − 2y²)`. -/
theorem ex_2_23_c (f : BinaryQF) (hf : f.discr = 8) :
    ProperlyEquivalent f ⟨1, 0, -2⟩ ∨ ProperlyEquivalent f ⟨-1, 0, 2⟩ := by
  sorry

/-- **Exercise 2.23(d).** An odd prime `p = ±(x² − 2y²)` satisfies `p ≡ ±1
(mod 8)`. -/
theorem ex_2_23_d (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (h : (∃ x y : ℤ, (p : ℤ) = x ^ 2 - 2 * y ^ 2)
        ∨ (∃ x y : ℤ, (p : ℤ) = -(x ^ 2 - 2 * y ^ 2))) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  rw [← ZMod.exists_sq_eq_two_iff hp2]
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  -- Key: from  x² − 2y² = ±p  derive that 2 is a square mod p.
  have key : ∀ (x y : ℤ), x ^ 2 - 2 * y ^ 2 = (p : ℤ) ∨ x ^ 2 - 2 * y ^ 2 = -(p : ℤ) →
      IsSquare (2 : ZMod p) := by
    intro x y hpm
    -- Step 1: p ∤ y.
    have hydvd : ¬ (p : ℤ) ∣ y := by
      intro hy
      have hx2 : (p : ℤ) ∣ x ^ 2 := by
        rcases hpm with hpm | hpm
        · have he : x ^ 2 = 2 * y ^ 2 + (p : ℤ) := by linarith
          rw [he]; exact dvd_add (Dvd.dvd.mul_left (dvd_pow hy two_ne_zero) 2) (dvd_refl _)
        · have he : x ^ 2 = 2 * y ^ 2 - (p : ℤ) := by linarith
          rw [he]; exact dvd_sub (Dvd.dvd.mul_left (dvd_pow hy two_ne_zero) 2) (dvd_refl _)
      have hpx : (p : ℤ) ∣ x := hpZ.dvd_of_dvd_pow hx2
      obtain ⟨a, ha⟩ := hpx
      obtain ⟨b, hb⟩ := hy
      have hpK : (p : ℤ) ∣ 1 := by
        rcases hpm with hpm | hpm
        · have key2 : (p : ℤ) ^ 2 * (a ^ 2 - 2 * b ^ 2) = (p : ℤ) := by
            rw [ha, hb] at hpm; linear_combination hpm
          have h2 : (p : ℤ) * ((p : ℤ) * (a ^ 2 - 2 * b ^ 2)) = (p : ℤ) * 1 := by
            linear_combination key2
          exact ⟨a ^ 2 - 2 * b ^ 2, (mul_left_cancel₀ hpne h2).symm⟩
        · have key2 : (p : ℤ) ^ 2 * (a ^ 2 - 2 * b ^ 2) = -(p : ℤ) := by
            rw [ha, hb] at hpm; linear_combination hpm
          have h2 : (p : ℤ) * ((p : ℤ) * (a ^ 2 - 2 * b ^ 2)) = (p : ℤ) * (-1) := by
            linear_combination key2
          have h3 := mul_left_cancel₀ hpne h2
          exact dvd_neg.mp ⟨a ^ 2 - 2 * b ^ 2, h3.symm⟩
      have hle := Int.le_of_dvd one_pos hpK
      have hge : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      omega
    -- Step 2: x² = 2 y² in ZMod p, with y ≠ 0.
    have hY : (y : ZMod p) ≠ 0 := fun hy0 =>
      hydvd ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy0)
    have hcast : (x : ZMod p) ^ 2 - 2 * (y : ZMod p) ^ 2 = 0 := by
      rcases hpm with hpm | hpm <;>
        · have hc := congrArg (fun t : ℤ => (t : ZMod p)) hpm
          push_cast at hc
          simpa [ZMod.natCast_self] using hc
    have hXY : (x : ZMod p) ^ 2 = 2 * (y : ZMod p) ^ 2 := by linear_combination hcast
    -- Step 3: 2 = (x·y⁻¹)².
    refine ⟨(x : ZMod p) * (y : ZMod p)⁻¹, ?_⟩
    have hYinv : (y : ZMod p) * (y : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hY
    calc (2 : ZMod p)
        = 2 * ((y : ZMod p) * (y : ZMod p)⁻¹) ^ 2 := by rw [hYinv]; ring
      _ = (2 * (y : ZMod p) ^ 2) * ((y : ZMod p)⁻¹) ^ 2 := by ring
      _ = (x : ZMod p) ^ 2 * ((y : ZMod p)⁻¹) ^ 2 := by rw [← hXY]
      _ = ((x : ZMod p) * (y : ZMod p)⁻¹) * ((x : ZMod p) * (y : ZMod p)⁻¹) := by ring
  rcases h with ⟨x, y, hxy⟩ | ⟨x, y, hxy⟩
  · exact key x y (Or.inl hxy.symm)
  · exact key x y (Or.inr (by linarith))

/-- **Exercise 2.24.** Legendre's theorem: for nonzero `a,b,c` with `abc`
squarefree, `ax²+by²+cz² = 0` has a nontrivial solution iff `a,b,c` are not all
of the same sign and `−bc, −ac, −ab` are squares mod `|a|, |b|, |c|`. -/
theorem ex_2_24 (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsf : Squarefree (a * b * c)) :
    (∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0)
      ↔ ((0 < a ∨ 0 < b ∨ 0 < c) ∧ (a < 0 ∨ b < 0 ∨ c < 0))
          ∧ IsSquare ((-b * c : ℤ) : ZMod a.natAbs)
          ∧ IsSquare ((-a * c : ℤ) : ZMod b.natAbs)
          ∧ IsSquare ((-a * b : ℤ) : ZMod c.natAbs) := by
  sorry

/-- **Exercise 2.24(a).** With `p ≡ 1 (mod 4)`, `q ≡ 3 (mod 4)`, `(p/q) = −1`,
`(q/p) = 1`, the form `x² + py² − qz² = 0` has a nontrivial solution. -/
theorem ex_2_24_a (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p % 4 = 1)
    (hq : q % 4 = 3) (h1 : legendreSym q (p : ℤ) = -1) (h2 : legendreSym p (q : ℤ) = 1) :
    ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ x ^ 2 + (p : ℤ) * y ^ 2 - (q : ℤ) * z ^ 2 = 0 := by
  sorry

/-- **Exercise 2.24(b).** Working modulo `4`, `x² + py² − qz² = 0` has no
nontrivial primitive solution (yielding the contradiction). -/
theorem ex_2_24_b (p q : ℕ) (hp : p % 4 = 1) (hq : q % 4 = 3) :
    ¬ ∃ x y z : ℤ, (x, y, z) ≠ (0, 0, 0) ∧ Int.gcd (Int.gcd x y) z = 1
      ∧ x ^ 2 + (p : ℤ) * y ^ 2 - (q : ℤ) * z ^ 2 = 0 := by
  sorry

/-- **Exercise 2.25.** Two forms are properly equivalent iff their opposites
(`ax² − bxy + cy²`) are. -/
theorem ex_2_25 (f g : BinaryQF) :
    ProperlyEquivalent f g ↔
      ProperlyEquivalent ⟨f.a, -f.b, f.c⟩ ⟨g.a, -g.b, g.c⟩ := by
  have key : ∀ (p : BinaryQF) (M : Matrix (Fin 2) (Fin 2) ℤ),
      action (!![M 0 0, -(M 0 1); -(M 1 0), M 1 1]) ⟨p.a, -p.b, p.c⟩
        = ⟨(action M p).a, -(action M p).b, (action M p).c⟩ := by
    intro p M
    simp only [action, BinaryQF.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const]
    refine ⟨by ring, by ring, by ring⟩
  have opp : ∀ (p q : BinaryQF), ProperlyEquivalent p q →
      ProperlyEquivalent ⟨p.a, -p.b, p.c⟩ ⟨q.a, -q.b, q.c⟩ := by
    rintro p q ⟨M, hdet, rfl⟩
    refine ⟨!![M 0 0, -(M 0 1); -(M 1 0), M 1 1], ?_, key p M⟩
    rw [Matrix.det_fin_two_of]
    have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
    linear_combination hd
  refine ⟨opp f g, fun h => ?_⟩
  have := opp _ _ h
  simpa using this

/-- **Exercise 2.26.** The four compositions `126x² ± 74xy + 13y²`,
`126x² ± 38xy + 5y²` lie in distinct classes (pairwise non-properly-equivalent). -/
theorem ex_2_26 :
    ¬ ProperlyEquivalent ⟨126, 74, 13⟩ ⟨126, -74, 13⟩ ∧
      ¬ ProperlyEquivalent ⟨126, 74, 13⟩ ⟨126, 38, 5⟩ ∧
        ¬ ProperlyEquivalent ⟨126, 38, 5⟩ ⟨126, -38, 5⟩ := by
  sorry

/-- **Exercise 2.27(a).** An odd prime represented by two forms `f, g` of the same
discriminant forces `f` and `g` to be equivalent.

Note: Cox's exercise text states this without an oddness hypothesis, but his proof
(examining the middle coefficient mod `p` via Lemma 2.3) uses `p` odd, so we keep
the hypothesis `Odd p` and flag the divergence. -/
theorem ex_2_27_a (f g : BinaryQF) (hfg : f.discr = g.discr) (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hf : Represents f (p : ℤ)) (hg : Represents g (p : ℤ)) :
    Equivalent f g := by
  sorry

/-- **Exercise 2.27(b).** A reduced form equivalent to `x² + ny²` equals it. -/
theorem ex_2_27_b (n : ℤ) (g : BinaryQF) (hg : g.Reduced) (h : Equivalent ⟨1, 0, n⟩ g) :
    g = ⟨1, 0, n⟩ := by
  sorry

end PrimesX2NY2.PartI.S2
