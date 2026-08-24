/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.Genus
import PrimesX2NY2.PartI_Forms.Fermat

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
  obtain ⟨x, y, hxy⟩ := h
  by_cases hxy0 : x = 0 ∧ y = 0
  · obtain ⟨hx0, hy0⟩ := hxy0
    subst hx0; subst hy0
    have hm : m = 0 := by rw [← hxy]; simp [BinaryQF.eval]
    exact ⟨0, f.eval 1 0, by rw [hm]; ring, 1, 0, rfl, isCoprime_one_left⟩
  · have hg : 0 < Int.gcd x y :=
      Nat.pos_of_ne_zero (fun hz => hxy0 (Int.gcd_eq_zero_iff.mp hz))
    obtain ⟨x', y', hcop, hx, hy⟩ := Int.exists_gcd_one hg
    set g : ℤ := (Int.gcd x y : ℤ) with hgdef
    refine ⟨g, f.eval x' y', ?_, x', y', rfl, ?_⟩
    · have hme : m = f.eval (x' * g) (y' * g) := by rw [← hx, ← hy]; exact hxy.symm
      rw [hme]; simp only [BinaryQF.eval]; ring
    · exact Int.isCoprime_iff_gcd_eq_one.mpr hcop

/-- **Exercise 2.2(a).** Equivalence and proper equivalence are equivalence
relations. -/
theorem ex_2_2_a : Equivalence Equivalent ∧ Equivalence ProperlyEquivalent :=
  ⟨equivalent_equivalence, properlyEquivalent_equivalence⟩

/-- **Exercise 2.2(b).** Improper equivalence (`det = −1`) is not an equivalence
relation. -/
theorem ex_2_2_b :
    ¬ Equivalence (fun f g : BinaryQF =>
      ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = -1 ∧ action M f = g) := by
  intro h
  obtain ⟨M, hM, hMf⟩ := h.refl (⟨3, 1, 5⟩ : BinaryQF)
  have e00 : (!![(1 : ℤ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by simp
  have e01 : (!![(1 : ℤ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by simp
  have e10 : (!![(1 : ℤ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simp
  have e11 : (!![(1 : ℤ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1 := by simp
  have hJ : action (!![(1 : ℤ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ) ⟨3, 1, 5⟩
      = ⟨3, -1, 5⟩ := by
    simp only [action, e00, e01, e10, e11, BinaryQF.mk.injEq]
    refine ⟨by norm_num, by norm_num, by norm_num⟩
  have hpe : ProperlyEquivalent (⟨3, 1, 5⟩ : BinaryQF) ⟨3, -1, 5⟩ := by
    refine ⟨M * !![(1 : ℤ), 0; 0, -1], ?_, ?_⟩
    · rw [Matrix.det_mul, hM, Matrix.det_fin_two_of]; ring
    · rw [← action_mul, hMf, hJ]
  have hr1 : (⟨3, 1, 5⟩ : BinaryQF).Reduced := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro hh; norm_num at hh
  have hr2 : (⟨3, -1, 5⟩ : BinaryQF).Reduced := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro hh; norm_num at hh
  have hp : (⟨3, 1, 5⟩ : BinaryQF).PosDef := ⟨by norm_num, by norm_num [BinaryQF.discr]⟩
  have heq := reduced_eq_of_properlyEquivalent _ _ hr1 hr2 hp hpe
  have hb := congrArg BinaryQF.b heq
  norm_num at hb

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
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hsq
    obtain ⟨b, c, hdiscr, hprim⟩ :=
      PrimesX2NY2.Fermat.exists_form_of_isSquare D hD p hp hodd hpD hsq
    exact ⟨⟨(p : ℤ), b, c⟩, hdiscr, hprim, 1, 0, by simp [BinaryQF.eval]⟩
  · rintro ⟨f, hdiscr, hprim, hrep⟩
    obtain ⟨d, m', hm', hpr⟩ := ex_2_1 f (p : ℤ) hrep
    have hdvd : d ^ 2 ∣ (p : ℤ) := ⟨m', hm'⟩
    have hdn : d.natAbs ^ 2 ∣ p := by
      have h := Int.natAbs_dvd_natAbs.mpr hdvd
      rwa [Int.natAbs_pow, Int.natAbs_natCast] at h
    have hd1 : d.natAbs = 1 := by
      rcases hp.eq_one_or_self_of_dvd d.natAbs
          ((dvd_pow_self d.natAbs two_ne_zero).trans hdn) with h | h
      · exact h
      · exfalso
        rw [h] at hdn
        have hle := Nat.le_of_dvd hp.pos hdn
        nlinarith [hp.two_le]
    have hd2 : d ^ 2 = 1 := by
      rcases Int.natAbs_eq d with he | he <;> rw [he, hd1] <;> norm_num
    have hm'p : m' = (p : ℤ) := by
      rw [hm', hd2, one_mul]
    rw [hm'p] at hpr
    obtain ⟨B, C, hBC⟩ := (properlyRepresents_iff_properlyEquivalent f (p : ℤ)).mp hpr
    have hdBC := discr_eq_of_properlyEquivalent hBC
    rw [hdiscr] at hdBC
    simp only [BinaryQF.discr] at hdBC
    refine ⟨(B : ZMod p), ?_⟩
    have hcast := congrArg (fun t : ℤ => (t : ZMod p)) hdBC
    push_cast at hcast
    rw [ZMod.natCast_self] at hcast
    rw [hcast]
    ring

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

private theorem qf_ext {f g : BinaryQF} (ha : f.a = g.a) (hb : f.b = g.b) (hc : f.c = g.c) :
    f = g := by
  cases f; cases g; simp_all

private theorem not_all_even {a b c : ℤ} (hp : Int.gcd (Int.gcd a b) c = 1) :
    ¬ ((2:ℤ) ∣ a ∧ (2:ℤ) ∣ b ∧ (2:ℤ) ∣ c) := by
  rintro ⟨d1, d2, d3⟩
  have e1 : 2 ∣ a.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr d1
    simpa using h
  have e2 : 2 ∣ b.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr d2
    simpa using h
  have e3 : 2 ∣ c.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr d3
    simpa using h
  have g1 : 2 ∣ Int.gcd a b := Nat.dvd_gcd e1 e2
  have g2 : 2 ∣ Int.gcd ((Int.gcd a b : ℕ) : ℤ) c := Nat.dvd_gcd (by simpa using g1) e3
  rw [hp] at g2
  omega

private theorem not_isSquare_eight : ¬ IsSquare (8 : ℤ) := by
  rintro ⟨r, hr⟩
  have h1 : r * r = 8 := hr.symm
  have h2 : r ≤ 3 := by nlinarith [sq_nonneg (r - 3)]
  have h3 : -3 ≤ r := by nlinarith [sq_nonneg (r + 3)]
  interval_cases r <;> omega

/-- Translate the middle coefficient into `|B| ≤ |a|` (the indefinite normalization). -/
private theorem normalize_b' (a b c : ℤ) (ha : a ≠ 0) :
    ∃ B C : ℤ, ProperlyEquivalent (⟨a, b, c⟩ : BinaryQF) ⟨a, B, C⟩ ∧ |B| ≤ |a| := by
  have hA : 0 < |a| := abs_pos.mpr ha
  obtain ⟨m, hm, hmpos⟩ : ∃ m : ℤ, m = 2 * |a| ∧ 0 < m := ⟨2 * |a|, rfl, by linarith⟩
  obtain ⟨u, hu⟩ : ∃ u : ℤ, 2 * a * u = -m := by
    rcases lt_or_gt_of_ne ha with h | h
    · exact ⟨1, by rw [hm, abs_of_neg h]; ring⟩
    · exact ⟨-1, by rw [hm, abs_of_pos h]; ring⟩
  have hr1 : 0 ≤ b % m := Int.emod_nonneg b (ne_of_gt hmpos)
  have hr2 : b % m < m := Int.emod_lt_of_pos b hmpos
  have hid : b % m + m * (b / m) = b := Int.emod_add_ediv b m
  by_cases hcase : b % m ≤ |a|
  · refine ⟨b + 2 * a * (u * (b / m)), a * (u * (b / m)) ^ 2 + b * (u * (b / m)) + c,
      translate_equiv a b c (u * (b / m)), ?_⟩
    have hB : b + 2 * a * (u * (b / m)) = b % m := by
      have h2 : 2 * a * (u * (b / m)) = -(m * (b / m)) := by
        linear_combination (b / m) * hu
      rw [h2]; linarith [hid]
    rw [hB, abs_of_nonneg hr1]
    exact hcase
  · replace hcase : |a| < b % m := not_le.mp hcase
    refine ⟨b + 2 * a * (u * (b / m + 1)), a * (u * (b / m + 1)) ^ 2 + b * (u * (b / m + 1)) + c,
      translate_equiv a b c (u * (b / m + 1)), ?_⟩
    have hB : b + 2 * a * (u * (b / m + 1)) = b % m - m := by
      have h2 : 2 * a * (u * (b / m + 1)) = -(m * (b / m)) - m := by
        linear_combination (b / m + 1) * hu
      rw [h2]; linarith [hid]
    rw [hB, abs_of_nonpos (by linarith)]
    linarith

/-- **Exercise 2.10(a).** For indefinite nonsquare discriminant, every form is
properly equivalent to one with `|b| ≤ |a| ≤ |c|`. -/
theorem ex_2_10_a (g : BinaryQF) (h : 0 < g.discr) (hns : ¬ IsSquare g.discr) :
    ∃ f : BinaryQF, ProperlyEquivalent g f ∧ |f.b| ≤ |f.a| ∧ |f.a| ≤ |f.c| := by
  have key : ∀ (n : ℕ) (q : BinaryQF), ¬ IsSquare q.discr → q.a.natAbs = n →
      ∃ f : BinaryQF, ProperlyEquivalent q f ∧ |f.b| ≤ |f.a| ∧ |f.a| ≤ |f.c| := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro q hq hn
      have ha : q.a ≠ 0 := by
        intro h0
        refine hq ⟨q.b, ?_⟩
        simp only [BinaryQF.discr, h0]; ring
      obtain ⟨B, C, hBC, hBle⟩ := normalize_b' q.a q.b q.c ha
      have hBC' : ProperlyEquivalent q ⟨q.a, B, C⟩ := hBC
      have hdBC : (⟨q.a, B, C⟩ : BinaryQF).discr = q.discr :=
        (discr_eq_of_properlyEquivalent hBC').symm
      by_cases hle : |q.a| ≤ |C|
      · exact ⟨⟨q.a, B, C⟩, hBC', hBle, hle⟩
      · replace hle : |C| < |q.a| := not_le.mp hle
        have hswap : ProperlyEquivalent (⟨q.a, B, C⟩ : BinaryQF) ⟨C, -B, q.a⟩ :=
          swap_equiv q.a B C
        have hchain : ProperlyEquivalent q (⟨C, -B, q.a⟩ : BinaryQF) :=
          properlyEquivalent_equivalence.trans hBC' hswap
        have hd2 : (⟨C, -B, q.a⟩ : BinaryQF).discr = q.discr :=
          (discr_eq_of_properlyEquivalent hchain).symm
        have hlt : (⟨C, -B, q.a⟩ : BinaryQF).a.natAbs < n := by
          rw [← hn]
          show C.natAbs < q.a.natAbs
          rcases abs_cases C with ⟨e1, s1⟩ | ⟨e1, s1⟩ <;>
            rcases abs_cases q.a with ⟨e2, s2⟩ | ⟨e2, s2⟩ <;>
              rw [e1, e2] at hle <;> omega
        obtain ⟨f, hf1, hf2, hf3⟩ := ih _ hlt ⟨C, -B, q.a⟩ (by rw [hd2]; exact hq) rfl
        exact ⟨f, properlyEquivalent_equivalence.trans hchain hf1, hf2, hf3⟩
  exact key g.a.natAbs g hns rfl

/-- **Exercise 2.10(b).** Such a form satisfies `4a² ≤ D` (i.e. `|a| ≤ √D/2`). -/
theorem ex_2_10_b (f : BinaryQF) (h1 : |f.b| ≤ |f.a|) (h2 : |f.a| ≤ |f.c|)
    (hD : 0 < f.discr) (hns : ¬ IsSquare f.discr) : 4 * f.a ^ 2 ≤ f.discr := by
  simp only [BinaryQF.discr] at hD ⊢
  have hb2 : f.b ^ 2 ≤ f.a ^ 2 := by
    nlinarith [mul_le_mul h1 h1 (abs_nonneg f.b) (abs_nonneg f.a), sq_abs f.b, sq_abs f.a]
  have habs : f.a ^ 2 ≤ |f.a| * |f.c| := by
    nlinarith [mul_le_mul_of_nonneg_left h2 (abs_nonneg f.a), sq_abs f.a]
  rcases lt_trichotomy (f.a * f.c) 0 with hlt | heq | hgt
  · have hle : f.a ^ 2 ≤ -(f.a * f.c) := by
      calc f.a ^ 2 ≤ |f.a| * |f.c| := habs
        _ = |f.a * f.c| := (abs_mul _ _).symm
        _ = -(f.a * f.c) := abs_of_neg hlt
    nlinarith [hle, sq_nonneg f.b]
  · exfalso
    have ha : f.a = 0 := by
      rcases mul_eq_zero.mp heq with h | h
      · exact h
      · have hle0 : |f.a| ≤ 0 := by rw [h] at h2; simpa using h2
        exact abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _))
    have hb : f.b = 0 := by
      have hle0 : |f.b| ≤ 0 := by rw [ha] at h1; simpa using h1
      exact abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _))
    rw [ha, hb] at hD; norm_num at hD
  · exfalso
    have hle : f.a ^ 2 ≤ f.a * f.c := by
      calc f.a ^ 2 ≤ |f.a| * |f.c| := habs
        _ = |f.a * f.c| := (abs_mul _ _).symm
        _ = f.a * f.c := abs_of_pos hgt
    nlinarith [hle, hb2, hD, hgt]

/-- **Exercise 2.10(c).** Hence there are finitely many such reduced forms, so the
class number `h(D)` is finite for indefinite `D`. -/
theorem ex_2_10_c (D : ℤ) (hD : 0 < D) (hns : ¬ IsSquare D) :
    {f : BinaryQF | f.discr = D ∧ |f.b| ≤ |f.a| ∧ |f.a| ≤ |f.c|}.Finite := by
  have hane : ∀ f : BinaryQF, f.discr = D → |f.b| ≤ |f.a| → f.a ≠ 0 := by
    intro f hfd h1 h0
    have hb0 : f.b = 0 := by
      have hle : |f.b| ≤ 0 := by rw [h0] at h1; simpa using h1
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    have hz : D = 0 := by rw [← hfd]; simp only [BinaryQF.discr, h0, hb0]; ring
    omega
  refine Set.Finite.of_finite_image (f := fun f : BinaryQF => (f.a, f.b)) ?_ ?_
  · apply Set.Finite.subset (Finset.Icc ((-D : ℤ), (-D : ℤ)) ((D : ℤ), (D : ℤ))).finite_toSet
    rintro y ⟨f, ⟨hfd, h1, h2⟩, rfl⟩
    have hb := ex_2_10_b f h1 h2 (by rw [hfd]; exact hD) (by rw [hfd]; exact hns)
    rw [hfd] at hb
    have h0 := hane f hfd h1
    have hA1 : 1 ≤ |f.a| := by
      rcases abs_cases f.a with ⟨e, s⟩ | ⟨e, s⟩ <;> rw [e] <;> omega
    have hAD : |f.a| ≤ D := by
      nlinarith [sq_abs f.a, sq_nonneg f.a, abs_nonneg f.a,
        mul_le_mul_of_nonneg_left hA1 (abs_nonneg f.a)]
    have hBD : |f.b| ≤ D := le_trans h1 hAD
    obtain ⟨hb1, hb2⟩ := abs_le.mp hBD
    obtain ⟨ha1, ha2⟩ := abs_le.mp hAD
    simp only [Finset.coe_Icc, Set.mem_Icc, Prod.mk_le_mk]
    exact ⟨⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩
  · rintro f ⟨hfd, h1, h2⟩ g ⟨hgd, hg1, hg2⟩ hfg
    have ha : f.a = g.a := congrArg Prod.fst hfg
    have hbq : f.b = g.b := congrArg Prod.snd hfg
    have h0 := hane f hfd h1
    have hc : f.c = g.c := by
      have e1 : f.b ^ 2 - 4 * f.a * f.c = D := hfd
      have e2 : g.b ^ 2 - 4 * g.a * g.c = D := hgd
      rw [← ha, ← hbq] at e2
      have h4 : (4 * f.a) * f.c = (4 * f.a) * g.c := by linear_combination e2 - e1
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num) h0) h4
    exact qf_ext ha hbq hc

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
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hm1
  have hpm : p ∣ m := Nat.minFac_dvd m
  obtain ⟨e, n', hnd, hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
  have hcop_p : Nat.Coprime p n' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  have hcop : Nat.Coprime (p ^ e) n' := hcop_p.pow_left e
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · exfalso; rw [h0, pow_zero, one_mul] at hme; rw [hme] at hpm; exact hnd hpm
    · exact h0
  have ha1 : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
  have hn'pos : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hme; omega)
  have hc1 : 1 < n' := by
    rcases Nat.lt_or_ge n' 2 with h | h
    · have hn1 : n' = 1 := by omega
      exfalso; rw [hn1, mul_one] at hme; exact hnp ⟨p, e, hp, hme⟩
    · exact h
  have hne : p ^ e ≠ n' := by
    intro heq
    have hcc : Nat.Coprime n' n' := heq ▸ hcop
    have hn1 : n' = 1 := by unfold Nat.Coprime at hcc; rwa [Nat.gcd_self] at hcc
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨p ^ e, n', ha1, hlt, hme, hcop⟩
  · exact ⟨n', p ^ e, hc1, hgt, by rw [hme]; ring, hcop.symm⟩

private theorem set32 : {f : BinaryQF | f.discr = -32 ∧ f.Reduced ∧ f.Primitive}
    = ({⟨1, 0, 8⟩, ⟨3, 2, 3⟩} : Set BinaryQF) := by
  ext f
  obtain ⟨a, b, c⟩ := f
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, BinaryQF.mk.injEq,
    BinaryQF.discr, BinaryQF.Reduced, BinaryQF.Primitive]
  constructor
  · rintro ⟨hd, ⟨hr1, hr2, hr3⟩, hp⟩
    have ha0 : 0 ≤ a := le_trans (abs_nonneg b) hr1
    obtain ⟨hl, hu⟩ := abs_le.mp hr1
    have hsign : (b ≠ a ∧ b ≠ -a ∧ a ≠ c) ∨ 0 ≤ b := by
      by_cases hb0' : 0 ≤ b
      · exact Or.inr hb0'
      · have hb0 : b < 0 := not_le.mp hb0'
        refine Or.inl ⟨by omega, ?_, ?_⟩
        · intro heq
          have hba : |b| = a := by rw [heq, abs_neg, abs_of_nonneg ha0]
          linarith [hr3 (Or.inl hba)]
        · intro heq
          linarith [hr3 (Or.inr heq)]
    have hev := not_all_even hp
    have hd' : 4 * a * c = b * b + 32 := by linear_combination -hd
    have hbb : b * b ≤ a * a := by
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ a - b) (by linarith : (0:ℤ) ≤ a + b)]
    have hac : a * a ≤ a * c := mul_le_mul_of_nonneg_left hr2 ha0
    have ha1 : 1 ≤ a := by
      rcases ha0.lt_or_eq with h | h
      · omega
      · exfalso
        have hb0 : b = 0 := by omega
        rw [hb0, ← h] at hd'
        omega
    have h3a : 3 * (a * a) ≤ 32 := by linarith
    have ha3 : a ≤ 3 := by nlinarith [sq_nonneg (a - 4)]
    clear hr1 hr3 hd hp hbb hac h3a
    interval_cases a <;> interval_cases b <;> omega
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

private theorem set124 : {f : BinaryQF | f.discr = -124 ∧ f.Reduced ∧ f.Primitive}
    = ({⟨1, 0, 31⟩, ⟨5, 4, 7⟩, ⟨5, -4, 7⟩} : Set BinaryQF) := by
  ext f
  obtain ⟨a, b, c⟩ := f
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, BinaryQF.mk.injEq,
    BinaryQF.discr, BinaryQF.Reduced, BinaryQF.Primitive]
  constructor
  · rintro ⟨hd, ⟨hr1, hr2, hr3⟩, hp⟩
    have ha0 : 0 ≤ a := le_trans (abs_nonneg b) hr1
    obtain ⟨hl, hu⟩ := abs_le.mp hr1
    have hsign : (b ≠ a ∧ b ≠ -a ∧ a ≠ c) ∨ 0 ≤ b := by
      by_cases hb0' : 0 ≤ b
      · exact Or.inr hb0'
      · have hb0 : b < 0 := not_le.mp hb0'
        refine Or.inl ⟨by omega, ?_, ?_⟩
        · intro heq
          have hba : |b| = a := by rw [heq, abs_neg, abs_of_nonneg ha0]
          linarith [hr3 (Or.inl hba)]
        · intro heq
          linarith [hr3 (Or.inr heq)]
    have hev := not_all_even hp
    have hd' : 4 * a * c = b * b + 124 := by linear_combination -hd
    have hbb : b * b ≤ a * a := by
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ a - b) (by linarith : (0:ℤ) ≤ a + b)]
    have hac : a * a ≤ a * c := mul_le_mul_of_nonneg_left hr2 ha0
    have ha1 : 1 ≤ a := by
      rcases ha0.lt_or_eq with h | h
      · omega
      · exfalso
        have hb0 : b = 0 := by omega
        rw [hb0, ← h] at hd'
        omega
    have h3a : 3 * (a * a) ≤ 124 := by linarith
    have ha3 : a ≤ 6 := by nlinarith [sq_nonneg (a - 7)]
    clear hr1 hr3 hd hp hbb hac h3a
    interval_cases a <;> interval_cases b <;> omega
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

/-- **Exercise 2.12(b).** `h(−32) = 2` and `h(−124) = 3`. -/
theorem ex_2_12_b :
    {f : BinaryQF | f.discr = -32 ∧ f.Reduced ∧ f.Primitive}.ncard = 2 ∧
      {f : BinaryQF | f.discr = -124 ∧ f.Reduced ∧ f.Primitive}.ncard = 3 := by
  constructor
  · rw [set32, Set.ncard_pair (by norm_num)]
  · rw [set124]
    have hfin : ({(⟨5, 4, 7⟩ : BinaryQF), (⟨5, -4, 7⟩ : BinaryQF)} : Set BinaryQF).Finite :=
      (Set.finite_singleton _).insert _
    have h : ({(⟨1, 0, 31⟩ : BinaryQF), ⟨5, 4, 7⟩, ⟨5, -4, 7⟩} : Set BinaryQF).ncard = 2 + 1 := by
      rw [Set.ncard_insert_of_notMem (by norm_num) hfin, Set.ncard_pair (by norm_num)]
    omega

/-- **Exercise 2.13.** The result (2.19): for an odd prime `p ∤ 5`,
`p ≡ 1,3,7,9 (mod 20)` iff `(−5/p) = 1`. -/
theorem ex_2_13 (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hp5 : ¬ (p : ℤ) ∣ 5) :
    (p % 20 = 1 ∨ p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 9)
      ↔ IsSquare ((-5 : ℤ) : ZMod p) := by
  sorry

-- The values of `x² + 5y²` on units of `ℤ/20ℤ` are exactly `1, 9`.
set_option maxRecDepth 40000 in
private theorem key1 : ∀ X Y : ZMod 20, (∃ w : ZMod 20, (X * X + 5 * (Y * Y)) * w = 1) →
    X * X + 5 * (Y * Y) = 1 ∨ X * X + 5 * (Y * Y) = 9 := by decide

-- The values of `2x² + 2xy + 3y²` on units of `ℤ/20ℤ` are exactly `3, 7`.
set_option maxRecDepth 40000 in
private theorem key2 : ∀ X Y : ZMod 20,
    (∃ w : ZMod 20, (2 * (X * X) + 2 * (X * Y) + 3 * (Y * Y)) * w = 1) →
    2 * (X * X) + 2 * (X * Y) + 3 * (Y * Y) = 3 ∨
      2 * (X * X) + 2 * (X * Y) + 3 * (Y * Y) = 7 := by decide

/-- **Exercise 2.14.** The result (2.20): in `(ℤ/20ℤ)ˣ`, the form `x²+5y²`
represents only `1, 9` and `2x²+2xy+3y²` represents only `3, 7`. -/
theorem ex_2_14 (m : ℤ) (hco : IsCoprime m 20) :
    (Represents ⟨1, 0, 5⟩ m → (m : ZMod 20) = 1 ∨ (m : ZMod 20) = 9) ∧
      (Represents ⟨2, 2, 3⟩ m → (m : ZMod 20) = 3 ∨ (m : ZMod 20) = 7) := by
  obtain ⟨u, v, huv⟩ := hco
  have hdvd : ((20 : ℕ) : ℤ) ∣ (u * m - 1) := ⟨-v, by push_cast; linarith⟩
  have hz : ((u * m - 1 : ℤ) : ZMod 20) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 20).mpr hdvd
  push_cast at hz
  have hu : (m : ZMod 20) * (u : ZMod 20) = 1 := by linear_combination hz
  constructor
  · rintro ⟨x, y, hxy⟩
    have hm : (x : ZMod 20) * (x : ZMod 20) + 5 * ((y : ZMod 20) * (y : ZMod 20))
        = (m : ZMod 20) := by
      have hc := congrArg (fun z : ℤ => (z : ZMod 20)) hxy
      simp only [BinaryQF.eval] at hc
      push_cast at hc
      linear_combination hc
    have hw : ∃ w : ZMod 20,
        ((x : ZMod 20) * (x : ZMod 20) + 5 * ((y : ZMod 20) * (y : ZMod 20))) * w = 1 :=
      ⟨(u : ZMod 20), by rw [hm]; exact hu⟩
    rcases key1 (x : ZMod 20) (y : ZMod 20) hw with h | h
    · exact Or.inl (by rw [← hm]; exact h)
    · exact Or.inr (by rw [← hm]; exact h)
  · rintro ⟨x, y, hxy⟩
    have hm : 2 * ((x : ZMod 20) * (x : ZMod 20)) + 2 * ((x : ZMod 20) * (y : ZMod 20))
          + 3 * ((y : ZMod 20) * (y : ZMod 20)) = (m : ZMod 20) := by
      have hc := congrArg (fun z : ℤ => (z : ZMod 20)) hxy
      simp only [BinaryQF.eval] at hc
      push_cast at hc
      linear_combination hc
    have hw : ∃ w : ZMod 20,
        (2 * ((x : ZMod 20) * (x : ZMod 20)) + 2 * ((x : ZMod 20) * (y : ZMod 20))
          + 3 * ((y : ZMod 20) * (y : ZMod 20))) * w = 1 :=
      ⟨(u : ZMod 20), by rw [hm]; exact hu⟩
    rcases key2 (x : ZMod 20) (y : ZMod 20) hw with h | h
    · exact Or.inl (by rw [← hm]; exact h)
    · exact Or.inr (by rw [← hm]; exact h)

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
  obtain ⟨B, C, hBC⟩ := (properlyRepresents_iff_properlyEquivalent f m).mp h
  have hd : (⟨m, B, C⟩ : BinaryQF).discr = D := by
    rw [← discr_eq_of_properlyEquivalent hBC]; exact hf
  have hD' : B ^ 2 - 4 * m * C = D := hd
  obtain ⟨k, hk⟩ := hm
  have hBodd : ¬ (2 ∣ B) := by
    rintro ⟨t, ht⟩
    rw [ht, hk] at hD'
    have : D = 4 * (t ^ 2 - 2 * k * C) := by linear_combination -hD'
    omega
  obtain ⟨u, hu⟩ : ∃ u, B = 2 * u + 1 := by
    rcases Int.even_or_odd B with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact absurd ⟨t, by omega⟩ hBodd
    · exact ⟨t, ht⟩
  have hD8 : ∃ s : ℤ, D = 8 * s + 1 := by
    rcases Int.even_or_odd u with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨2 * t ^ 2 + t - k * C, by rw [← hD', hu, hk, ht]; ring⟩
    · exact ⟨2 * t ^ 2 + 3 * t + 1 - k * C, by rw [← hD', hu, hk, ht]; ring⟩
  obtain ⟨s, hs⟩ := hD8
  omega

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
  -- FLAG (under-hypothesized): FALSE as stated — Cox's Lemma 2.25 assumes `f` primitive
  -- and `M ≠ 0`. See `ex_2_18_b_FALSE` for a proof that the unrestricted statement fails
  -- (take `f = ⟨2,0,2⟩`, `M = 2`: every value `2(x²+y²)` is even), and
  -- `ex_2_18_b_correct` for the faithful version.
  sorry

/-- The unrestricted form of Exercise 2.18(b) is false: without primitivity of `f`
(and `M ≠ 0`) no value of `f` need be coprime to `M`. -/
theorem ex_2_18_b_FALSE :
    ¬ (∀ (f : BinaryQF) (M : ℤ), ∃ x y : ℤ, IsCoprime x y ∧ IsCoprime (f.eval x y) M) := by
  intro h
  obtain ⟨x, y, -, hcop⟩ := h ⟨2, 0, 2⟩ 2
  obtain ⟨u, v, huv⟩ := hcop
  have hval : (⟨2, 0, 2⟩ : BinaryQF).eval x y = 2 * (x ^ 2 + y ^ 2) := by
    simp only [BinaryQF.eval]; ring
  rw [hval] at huv
  have : (2 : ℤ) ∣ 1 := ⟨u * (x ^ 2 + y ^ 2) + v, by linarith⟩
  norm_num at this

/-- **Exercise 2.18(b)**, faithful form (Cox, Lemma 2.25): a *primitive* form properly
represents some value coprime to a *nonzero* `M`. -/
theorem ex_2_18_b_correct (f : BinaryQF) (hf : f.Primitive) (M : ℤ) (hM : M ≠ 0) :
    ∃ x y : ℤ, IsCoprime x y ∧ IsCoprime (f.eval x y) M := by
  obtain ⟨x, y, hcop⟩ := exists_eval_coprime f hf M hM
  by_cases hxy0 : x = 0 ∧ y = 0
  · obtain ⟨hx0, hy0⟩ := hxy0
    subst hx0; subst hy0
    have hz : f.eval 0 0 = 0 := by simp [BinaryQF.eval]
    rw [hz] at hcop
    have hMu : IsUnit M := isCoprime_zero_left.mp hcop
    obtain ⟨w, hw⟩ := hMu
    exact ⟨1, 0, isCoprime_one_left, 0, (↑w⁻¹ : ℤ), by rw [← hw]; simp⟩
  · have hg : 0 < Int.gcd x y :=
      Nat.pos_of_ne_zero (fun hz => hxy0 (Int.gcd_eq_zero_iff.mp hz))
    obtain ⟨x', y', hcop', hx, hy⟩ := Int.exists_gcd_one hg
    set g : ℤ := (Int.gcd x y : ℤ) with hgdef
    refine ⟨x', y', Int.isCoprime_iff_gcd_eq_one.mpr hcop', ?_⟩
    have hval : f.eval x y = g ^ 2 * f.eval x' y' := by
      rw [hx, hy]; simp only [BinaryQF.eval]; ring
    rw [hval] at hcop
    exact IsCoprime.of_isCoprime_of_dvd_left hcop ⟨g ^ 2, by ring⟩

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

private theorem discr8_classify (a b c : ℤ) (hd : b ^ 2 - 4 * a * c = 8)
    (h1 : |b| ≤ |a|) (hab : 4 * a ^ 2 ≤ 8) :
    (a = 1 ∧ b = 0 ∧ c = -2) ∨ (a = -1 ∧ b = 0 ∧ c = 2) := by
  have hd' : b * b - 4 * a * c = 8 := by linear_combination hd
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
  have haa : |a| ≤ 1 := by
    rcases abs_cases a with ⟨e, s⟩ | ⟨e, s⟩ <;> rw [e] <;> linarith
  obtain ⟨hb1, hb2⟩ := abs_le.mp h1
  have hbl : -1 ≤ b := by linarith
  have hbu : b ≤ 1 := by linarith
  clear h1 hb1 hb2 haa hd hab
  interval_cases a <;> interval_cases b <;> omega

/-- **Exercise 2.23(c).** Any form of discriminant `8` is properly equivalent to
`±(x² − 2y²)`. -/
theorem ex_2_23_c (f : BinaryQF) (hf : f.discr = 8) :
    ProperlyEquivalent f ⟨1, 0, -2⟩ ∨ ProperlyEquivalent f ⟨-1, 0, 2⟩ := by
  have hns : ¬ IsSquare f.discr := by rw [hf]; exact not_isSquare_eight
  obtain ⟨g, hg, h1, h2⟩ := ex_2_10_a f (by rw [hf]; norm_num) hns
  have hgd : g.discr = 8 := by rw [← discr_eq_of_properlyEquivalent hg]; exact hf
  have hbound := ex_2_10_b g h1 h2 (by rw [hgd]; norm_num)
    (by rw [hgd]; exact not_isSquare_eight)
  rw [hgd] at hbound
  have hd : g.b ^ 2 - 4 * g.a * g.c = 8 := hgd
  rcases discr8_classify g.a g.b g.c hd h1 hbound with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · have hge : g = (⟨1, 0, -2⟩ : BinaryQF) := qf_ext e1 e2 e3
    exact Or.inl (hge ▸ hg)
  · have hge : g = (⟨-1, 0, 2⟩ : BinaryQF) := qf_ext e1 e2 e3
    exact Or.inr (hge ▸ hg)

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
  rintro ⟨x, y, z, -, hg, heq⟩
  have hev : ¬ ((2:ℤ) ∣ x ∧ (2:ℤ) ∣ y ∧ (2:ℤ) ∣ z) := by
    rintro ⟨d1, d2, d3⟩
    have e1 : 2 ∣ x.natAbs := by have h := Int.natAbs_dvd_natAbs.mpr d1; simpa using h
    have e2 : 2 ∣ y.natAbs := by have h := Int.natAbs_dvd_natAbs.mpr d2; simpa using h
    have e3 : 2 ∣ z.natAbs := by have h := Int.natAbs_dvd_natAbs.mpr d3; simpa using h
    have g1 : 2 ∣ Int.gcd x y := Nat.dvd_gcd e1 e2
    have g2 : 2 ∣ Int.gcd ((Int.gcd x y : ℕ) : ℤ) z := Nat.dvd_gcd (by simpa using g1) e3
    rw [hg] at g2
    omega
  have hp4 : ((p : ℤ)) % 4 = 1 := by omega
  have hq4 : ((q : ℤ)) % 4 = 3 := by omega
  have key : (4 : ℤ) ∣ (x ^ 2 + y ^ 2 + z ^ 2) := by
    obtain ⟨kp, hkp⟩ : (4 : ℤ) ∣ ((p : ℤ) - 1) := by omega
    obtain ⟨kq, hkq⟩ : (4 : ℤ) ∣ ((q : ℤ) + 1) := by omega
    exact ⟨-(kp * y ^ 2) + kq * z ^ 2, by linear_combination heq - y ^ 2 * hkp + z ^ 2 * hkq⟩
  have sq4 : ∀ w : ℤ, w ^ 2 % 4 = 0 ∨ w ^ 2 % 4 = 1 := by
    intro w
    rcases Int.even_or_odd w with ⟨m, hm⟩ | ⟨m, hm⟩
    · left; rw [hm]; have : (m + m) ^ 2 = 4 * m ^ 2 := by ring
      rw [this]; omega
    · right; rw [hm]; have : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
      rw [this]; omega
  have hx2 := sq4 x; have hy2 := sq4 y; have hz2 := sq4 z
  have par : ∀ w : ℤ, w ^ 2 % 4 = 0 → (2:ℤ) ∣ w := by
    intro w hw
    rcases Int.even_or_odd w with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m, by omega⟩
    · exfalso; rw [hm] at hw
      have : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
      rw [this] at hw; omega
  have hall : x ^ 2 % 4 = 0 ∧ y ^ 2 % 4 = 0 ∧ z ^ 2 % 4 = 0 := by omega
  exact hev ⟨par x hall.1, par y hall.2.1, par z hall.2.2⟩

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

/-- Package a unimodular substitution as a proper equivalence, given the three
transformed coefficients. -/
private theorem pe_of_matrix (f : BinaryQF) (a' b' c' p q r s : ℤ) (hdet : p * s - q * r = 1)
    (h1 : f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2 = a')
    (h2 : 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s = b')
    (h3 : f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2 = c') :
    ProperlyEquivalent f ⟨a', b', c'⟩ := by
  refine ⟨!![p, q; r, s], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linarith
  · have e00 : (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by simp
    have e01 : (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q := by simp
    have e10 : (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by simp
    have e11 : (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = s := by simp
    simp only [action, e00, e01, e10, e11, BinaryQF.mk.injEq]
    exact ⟨h1, h2, h3⟩

private theorem red1 : ProperlyEquivalent (⟨126, 74, 13⟩ : BinaryQF) ⟨13, 4, 21⟩ :=
  pe_of_matrix ⟨126, 74, 13⟩ 13 4 21 0 (-1) 1 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

private theorem red2 : ProperlyEquivalent (⟨126, -74, 13⟩ : BinaryQF) ⟨13, -4, 21⟩ :=
  pe_of_matrix ⟨126, -74, 13⟩ 13 (-4) 21 0 (-1) 1 (-3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

private theorem red3 : ProperlyEquivalent (⟨126, 38, 5⟩ : BinaryQF) ⟨5, 2, 54⟩ :=
  pe_of_matrix ⟨126, 38, 5⟩ 5 2 54 0 (-1) 1 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

private theorem red4 : ProperlyEquivalent (⟨126, -38, 5⟩ : BinaryQF) ⟨5, -2, 54⟩ :=
  pe_of_matrix ⟨126, -38, 5⟩ 5 (-2) 54 0 (-1) 1 (-4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

private theorem rd1 : (⟨13, 4, 21⟩ : BinaryQF).Reduced := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro h; norm_num at h

private theorem rd2 : (⟨13, -4, 21⟩ : BinaryQF).Reduced := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro h; norm_num at h

private theorem rd3 : (⟨5, 2, 54⟩ : BinaryQF).Reduced := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro h; norm_num at h

private theorem rd4 : (⟨5, -2, 54⟩ : BinaryQF).Reduced := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro h; norm_num at h

private theorem pd1 : (⟨13, 4, 21⟩ : BinaryQF).PosDef := ⟨by norm_num, by norm_num [BinaryQF.discr]⟩

private theorem pd3 : (⟨5, 2, 54⟩ : BinaryQF).PosDef := ⟨by norm_num, by norm_num [BinaryQF.discr]⟩

/-- **Exercise 2.26.** The four compositions `126x² ± 74xy + 13y²`,
`126x² ± 38xy + 5y²` lie in distinct classes (pairwise non-properly-equivalent). -/
theorem ex_2_26 :
    ¬ ProperlyEquivalent ⟨126, 74, 13⟩ ⟨126, -74, 13⟩ ∧
      ¬ ProperlyEquivalent ⟨126, 74, 13⟩ ⟨126, 38, 5⟩ ∧
        ¬ ProperlyEquivalent ⟨126, 38, 5⟩ ⟨126, -38, 5⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h' : ProperlyEquivalent (⟨13, 4, 21⟩ : BinaryQF) ⟨13, -4, 21⟩ :=
      properlyEquivalent_equivalence.trans (properlyEquivalent_equivalence.symm red1)
        (properlyEquivalent_equivalence.trans h red2)
    have heq := reduced_eq_of_properlyEquivalent _ _ rd1 rd2 pd1 h'
    have hb := congrArg BinaryQF.b heq
    norm_num at hb
  · intro h
    have h' : ProperlyEquivalent (⟨13, 4, 21⟩ : BinaryQF) ⟨5, 2, 54⟩ :=
      properlyEquivalent_equivalence.trans (properlyEquivalent_equivalence.symm red1)
        (properlyEquivalent_equivalence.trans h red3)
    have heq := reduced_eq_of_properlyEquivalent _ _ rd1 rd3 pd1 h'
    have ha := congrArg BinaryQF.a heq
    norm_num at ha
  · intro h
    have h' : ProperlyEquivalent (⟨5, 2, 54⟩ : BinaryQF) ⟨5, -2, 54⟩ :=
      properlyEquivalent_equivalence.trans (properlyEquivalent_equivalence.symm red3)
        (properlyEquivalent_equivalence.trans h red4)
    have heq := reduced_eq_of_properlyEquivalent _ _ rd3 rd4 pd3 h'
    have hb := congrArg BinaryQF.b heq
    norm_num at hb

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
  -- FLAG (under-hypothesized): FALSE as stated for `n = 0`, where `⟨0,0,1⟩` is reduced and
  -- equivalent to `⟨1,0,0⟩` (via the determinant `−1` swap) yet different from it; see
  -- `ex_2_27_b_FALSE`. Cox's context supplies `n > 0`, i.e. positive definiteness.
  sorry

/-- Exercise 2.27(b) fails without positivity of `n`: at `n = 0` the reduced form
`⟨0,0,1⟩` is equivalent to `⟨1,0,0⟩` but not equal to it. -/
theorem ex_2_27_b_FALSE :
    ¬ (∀ (n : ℤ) (g : BinaryQF), g.Reduced → Equivalent ⟨1, 0, n⟩ g → g = ⟨1, 0, n⟩) := by
  intro h
  have hred : (⟨0, 0, 1⟩ : BinaryQF).Reduced := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro _
    norm_num
  have hequiv : Equivalent (⟨1, 0, 0⟩ : BinaryQF) ⟨0, 0, 1⟩ := by
    refine ⟨!![0, 1; 1, 0], Or.inr ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]; ring
    · simp only [action, BinaryQF.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const]
      refine ⟨by ring, by ring, by ring⟩
  have := h 0 ⟨0, 0, 1⟩ hred hequiv
  simp only [BinaryQF.mk.injEq] at this
  norm_num at this

end PrimesX2NY2.PartI.S2
