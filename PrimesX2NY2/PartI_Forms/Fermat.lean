/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.Forms

/-!
# Part I, §1 - Fermat, Euler, and Quadratic Reciprocity

Cox, *Primes of the Form x² + ny²*, §1.

Representation by `x² + ny²` for `n = 1, 2, 3`, Euler's descent, Lemmas 1.4 and
1.7, and quadratic reciprocity in its Euler and Legendre forms. Lemma 1.14 and
Corollary 1.19 describe the reciprocity step in terms of congruence classes.

The representation and descent results are proved, as are Legendre reciprocity
and its supplements. Euler's formulation, Lemma 1.14, and Corollary 1.19 still
have `sorry` proofs.
-/

namespace PrimesX2NY2.Fermat

open PrimesX2NY2.Forms

/-- **Theorem 1.2** (Fermat, two squares). An odd prime `p` is a sum of two
squares iff `p ≡ 1 (mod 4)`. -/
theorem prime_sq_add_sq (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2) ↔ p % 4 = 1 := by
  haveI := Fact.mk hp
  constructor
  · rintro ⟨x, y, hxy⟩
    have key : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
    have hp24 : p % 4 = 1 ∨ p % 4 = 3 := by have := Nat.odd_iff.mp hodd; omega
    rcases hp24 with h | h
    · exact h
    · exfalso
      have hcast : (p : ZMod 4) = (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 := by
        have h0 : ((p : ℤ) : ZMod 4) = ((x ^ 2 + y ^ 2 : ℤ) : ZMod 4) := by rw [hxy]
        push_cast at h0
        exact h0
      have hp3z : (p : ZMod 4) = 3 := by
        have hp43 : p = 4 * (p / 4) + 3 := by omega
        rw [hp43]; push_cast; rw [show (4 : ZMod 4) = 0 from by decide]; ring
      rw [hp3z] at hcast
      exact key _ _ hcast.symm
  · intro h
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (show p % 4 ≠ 3 by omega)
    exact ⟨a, b, by exact_mod_cast hab.symm⟩

/-- `−3` is a quadratic residue mod an odd prime `p ≠ 3` iff `p ≡ 1 (mod 3)`.

The pinned Mathlib version supplies the analogous `−1`, `2`, and `−2` criteria.
The `−3` case follows here from quadratic reciprocity; an upstream draft named
`ZMod.exists_sq_eq_neg_three_iff` is in `mathlib-prs/`. -/
theorem neg_three_isSquare_iff (p : ℕ) [Fact p.Prime] (hodd : Odd p) (hp3 : p ≠ 3) :
    IsSquare ((-3 : ℤ) : ZMod p) ↔ p % 3 = 1 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  have ha : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have h3 : (p : ℤ) ∣ (3 : ℤ) := (dvd_neg).mp h
    have h3' : p ∣ 3 := by exact_mod_cast h3
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three p h3') with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hp3 h1
  rw [← legendreSym.eq_one_iff p ha]
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
    have h30 : ¬ (3 ∣ p) := by
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    omega
  rcases hmod with h1 | h2
  · have hc : ((p : ℤ) : ZMod 3) = 1 := by
      rw [Int.cast_natCast, ← ZMod.natCast_mod, h1, Nat.cast_one]
    simp only [h1, iff_true]
    exact (legendreSym.eq_one_iff 3 (by rw [hc]; exact one_ne_zero)).mpr
      (by rw [hc]; decide)
  · have hc : ((p : ℤ) : ZMod 3) = 2 := by
      rw [Int.cast_natCast, ← ZMod.natCast_mod, h2]
      norm_num
    have hneg : legendreSym 3 ((p : ℕ) : ℤ) = -1 :=
      (legendreSym.eq_neg_one_iff 3).mpr (by rw [hc]; decide)
    rw [hneg]
    omega

/-- If a prime `p = x² + n y²`, then `−n` is a square mod `p`. -/
theorem isSquare_neg_of_repr (n : ℤ) (p : ℕ) (hp : p.Prime) (x y : ℤ)
    (hxy : (p : ℤ) = x ^ 2 + n * y ^ 2) : IsSquare ((-n : ℤ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpy : ¬ (p : ℤ) ∣ y := by
    intro hy
    have he : x ^ 2 = (p : ℤ) - n * y ^ 2 := by linarith
    have hx2 : (p : ℤ) ∣ x ^ 2 := by
      rw [he]
      exact dvd_sub dvd_rfl ((dvd_pow hy two_ne_zero).mul_left n)
    have hx : (p : ℤ) ∣ x := hpZ.dvd_of_dvd_pow hx2
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    have hpp : (p : ℤ) * ((p : ℤ) * (u ^ 2 + n * v ^ 2)) = (p : ℤ) * 1 := by
      linear_combination -hxy
    have h1 : (p : ℤ) * (u ^ 2 + n * v ^ 2) = 1 :=
      mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) hpp
    have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨u ^ 2 + n * v ^ 2, h1.symm⟩
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega
  have hy0 : ((y : ZMod p)) ≠ 0 := fun h => hpy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp h)
  have h0 : (x : ZMod p) ^ 2 + (n : ZMod p) * (y : ZMod p) ^ 2 = 0 := by
    have hc := congrArg (fun t : ℤ => (t : ZMod p)) hxy
    push_cast at hc
    rw [ZMod.natCast_self] at hc
    linear_combination -hc
  refine ⟨(x : ZMod p) * (y : ZMod p)⁻¹, ?_⟩
  have hyi : (y : ZMod p) * (y : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have hX : (x : ZMod p) ^ 2 = -(n : ZMod p) * (y : ZMod p) ^ 2 := by
    linear_combination h0
  calc ((-n : ℤ) : ZMod p)
      = -(n : ZMod p) * ((y : ZMod p) * (y : ZMod p)⁻¹) ^ 2 := by
        rw [hyi]; push_cast; ring
    _ = (x : ZMod p) ^ 2 * ((y : ZMod p)⁻¹) ^ 2 := by rw [hX]; ring
    _ = ((x : ZMod p) * (y : ZMod p)⁻¹) * ((x : ZMod p) * (y : ZMod p)⁻¹) := by ring

/-- Forward construction of Cox's Lemma 2.3: from `(D/p) = 1` build a primitive form
`⟨p, b, c⟩` of discriminant `D`. -/
theorem exists_form_of_isSquare (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) (p : ℕ)
    (hp : p.Prime) (hodd : Odd p) (hpD : ¬ (p : ℤ) ∣ D)
    (hsq : IsSquare ((D : ZMod p))) :
    ∃ b c : ℤ, (⟨(p : ℤ), b, c⟩ : BinaryQF).discr = D
      ∧ (⟨(p : ℤ), b, c⟩ : BinaryQF).Primitive := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨x, hx⟩ := hsq
  have hxcast : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_rightInverse x
  have hdvd₀ : (p : ℤ) ∣ ((x.val : ℤ)) ^ 2 - D := by
    have h0 : ((((x.val : ℤ)) ^ 2 - D : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hxcast, hx]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  obtain ⟨b, hb_par, hb_dvd⟩ :
      ∃ b : ℤ, (b - D) % 2 = 0 ∧ (p : ℤ) ∣ b ^ 2 - D := by
    by_cases hpar : ((x.val : ℤ) - D) % 2 = 0
    · exact ⟨(x.val : ℤ), hpar, hdvd₀⟩
    · refine ⟨(x.val : ℤ) + p, ?_, ?_⟩
      · have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
        omega
      · obtain ⟨k, hk⟩ := hdvd₀
        exact ⟨k + 2 * (x.val : ℤ) + p, by linear_combination hk⟩
  have hdvd4 : (4 : ℤ) ∣ b ^ 2 - D := by
    rcases Int.even_or_odd b with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hD0 : D % 4 = 0 := by
        rcases hD with h | h
        · exact h
        · exfalso; omega
      rw [show b ^ 2 - D = 4 * m ^ 2 - D from by rw [hm]; ring]
      exact dvd_sub (dvd_mul_right 4 (m ^ 2)) (by omega)
    · have hD1 : D % 4 = 1 := by
        rcases hD with h | h
        · exfalso; omega
        · exact h
      rw [show b ^ 2 - D = 4 * (m ^ 2 + m) - (D - 1) from by rw [hm]; ring]
      exact dvd_sub (dvd_mul_right 4 (m ^ 2 + m)) (by omega)
  have hcop : IsCoprime (4 : ℤ) ((p : ℕ) : ℤ) := by
    have h2 : ¬ 2 ∣ p := by
      have := Nat.odd_iff.mp hodd
      omega
    have hco2 : Nat.Coprime 2 p := (Nat.prime_two.coprime_iff_not_dvd).mpr h2
    have hco4 : Nat.Coprime 4 p := by
      have h := Nat.Coprime.pow_left 2 hco2
      norm_num at h
      exact h
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using hco4
  obtain ⟨c, hc⟩ := (hcop.mul_dvd hdvd4 hb_dvd : (4 * ((p : ℕ) : ℤ)) ∣ b ^ 2 - D)
  refine ⟨b, c, ?_, ?_⟩
  · simp only [BinaryQF.discr]
    linear_combination hc
  · have hpb : ¬ (p : ℤ) ∣ b := by
      intro hbdvd
      apply hpD
      have hb2 : (p : ℤ) ∣ b ^ 2 := dvd_pow hbdvd two_ne_zero
      have := dvd_sub hb2 hb_dvd
      simpa using this
    have hnb : ¬ p ∣ b.natAbs := by
      intro h
      apply hpb
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      exact h
    have hgcd1 : Int.gcd ((p : ℕ) : ℤ) b = 1 := by
      have hco : Nat.Coprime p b.natAbs := hp.coprime_iff_not_dvd.mpr hnb
      simpa [Int.gcd, Int.natAbs_natCast] using hco
    show Int.gcd ((Int.gcd ((p : ℕ) : ℤ) b : ℕ) : ℤ) c = 1
    rw [hgcd1]
    simp [Int.gcd]

/-- The only reduced form of discriminant `−8` is `x² + 2y²`. -/
theorem reduced_neg_eight (g : BinaryQF) (hred : g.Reduced) (hd : g.discr = -8) :
    g = ⟨1, 0, 2⟩ := by
  obtain ⟨a, b, c⟩ := g
  simp only [BinaryQF.Reduced, BinaryQF.discr] at hred hd
  obtain ⟨h1, h2, h3⟩ := hred
  obtain ⟨hb1, hb2⟩ := abs_le.mp h1
  have ha0' : 0 ≤ a := le_trans (abs_nonneg b) h1
  have ha0 : 0 < a := by
    rcases eq_or_lt_of_le ha0' with h | h
    · rw [← h] at hd; exfalso; nlinarith [sq_nonneg b]
    · exact h
  have hbsq : b ^ 2 ≤ a ^ 2 := sq_le_sq' hb1 hb2
  have hac : a * a ≤ a * c := mul_le_mul_of_nonneg_left h2 ha0.le
  have h3a : 3 * a ^ 2 ≤ 8 := by nlinarith
  have ha_lt : a < 2 := by nlinarith [sq_nonneg (a - 1)]
  have ha1 : a = 1 := by omega
  subst ha1
  have hd' : b * b - 4 * c = -8 := by linear_combination hd
  obtain ⟨rfl, rfl⟩ : b = 0 ∧ c = 2 := by
    rcases (show b = -1 ∨ b = 0 ∨ b = 1 by omega) with rfl | rfl | rfl <;> omega
  rfl

/-- The only reduced *primitive* form of discriminant `−12` is `x² + 3y²`. -/
theorem reduced_neg_twelve (g : BinaryQF) (hred : g.Reduced) (hprim : g.Primitive)
    (hd : g.discr = -12) : g = ⟨1, 0, 3⟩ := by
  obtain ⟨a, b, c⟩ := g
  simp only [BinaryQF.Reduced, BinaryQF.discr, BinaryQF.Primitive] at hred hd hprim
  obtain ⟨h1, h2, h3⟩ := hred
  obtain ⟨hb1, hb2⟩ := abs_le.mp h1
  have ha0' : 0 ≤ a := le_trans (abs_nonneg b) h1
  have ha0 : 0 < a := by
    rcases eq_or_lt_of_le ha0' with h | h
    · rw [← h] at hd; exfalso; nlinarith [sq_nonneg b]
    · exact h
  have hbsq : b ^ 2 ≤ a ^ 2 := sq_le_sq' hb1 hb2
  have hac : a * a ≤ a * c := mul_le_mul_of_nonneg_left h2 ha0.le
  have h3a : 3 * a ^ 2 ≤ 12 := by nlinarith
  have ha_le : a ≤ 2 := by nlinarith [sq_nonneg (a - 2)]
  have hd' : b * b - 4 * (a * c) = -12 := by linear_combination hd
  rcases (show a = 1 ∨ a = 2 by omega) with rfl | rfl
  · obtain ⟨rfl, rfl⟩ : b = 0 ∧ c = 3 := by
      rcases (show b = -1 ∨ b = 0 ∨ b = 1 by omega) with rfl | rfl | rfl <;> omega
    rfl
  · exfalso
    rcases (show b = -2 ∨ b = -1 ∨ b = 0 ∨ b = 1 ∨ b = 2 by omega)
      with rfl | rfl | rfl | rfl | rfl
    · have := h3 (Or.inl (by norm_num))
      omega
    · omega
    · omega
    · omega
    · have hc2 : c = 2 := by omega
      subst hc2
      norm_num [Int.gcd] at hprim

/-- Primes represented by `x² + 2y²` (Cox, §1). For an odd prime `p`, solvable
iff `p ≡ 1, 3 (mod 8)`. -/
theorem prime_sq_add_two_sq (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 2 * y ^ 2) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [← ZMod.exists_sq_eq_neg_two_iff (p := p) hp2]
    have h := isSquare_neg_of_repr 2 p hp x y hxy
    push_cast at h
    exact h
  · intro h8
    have hsqm2 : IsSquare (-2 : ZMod p) :=
      (ZMod.exists_sq_eq_neg_two_iff (p := p) hp2).mpr h8
    have hsq : IsSquare ((-8 : ℤ) : ZMod p) := by
      obtain ⟨s, hs⟩ := hsqm2
      refine ⟨2 * s, ?_⟩
      push_cast
      linear_combination (4 : ZMod p) * hs
    have hpD : ¬ (p : ℤ) ∣ (-8 : ℤ) := by
      intro hdvd
      have h8' : (p : ℤ) ∣ 8 := (dvd_neg).mp hdvd
      have h8'' : p ∣ 8 := by exact_mod_cast h8'
      have h23 : p ∣ 2 ^ 3 := by
        have he : (2 : ℕ) ^ 3 = 8 := by norm_num
        rw [he]
        exact h8''
      have h2d : p ∣ 2 := hp.dvd_of_dvd_pow h23
      have hle := Nat.le_of_dvd (by norm_num) h2d
      have hp2' := Nat.odd_iff.mp hodd
      have h2le := hp.two_le
      omega
    obtain ⟨b, c, hdiscr, hprim⟩ :=
      exists_form_of_isSquare (-8) (Or.inl (by decide)) p hp hodd hpD hsq
    have hpos : (⟨(p : ℤ), b, c⟩ : BinaryQF).PosDef := by
      constructor
      · show (0 : ℤ) < (p : ℤ)
        exact_mod_cast hp.pos
      · rw [hdiscr]
        norm_num
    obtain ⟨g, ⟨hgred, hgequiv⟩, -⟩ := exists_unique_reduced _ hpos
    have hgdiscr : g.discr = -8 := by
      rw [← discr_eq_of_properlyEquivalent hgequiv]
      exact hdiscr
    have hg2 : g = ⟨1, 0, 2⟩ := reduced_neg_eight g hgred hgdiscr
    obtain ⟨N, hN, hNg⟩ := properlyEquivalent_equivalence.symm hgequiv
    have hev := eval_action N g 1 0
    rw [hNg] at hev
    have hf10 : (⟨(p : ℤ), b, c⟩ : BinaryQF).eval 1 0 = (p : ℤ) := by
      simp [BinaryQF.eval]
    refine ⟨N 0 0 * 1 + N 0 1 * 0, N 1 0 * 1 + N 1 1 * 0, ?_⟩
    rw [← hf10, hev, hg2]
    simp only [BinaryQF.eval]
    ring

/-- Primes represented by `x² + 3y²` (Cox, §1). For a prime `p > 3`, solvable iff
`p ≡ 1 (mod 3)`. -/
theorem prime_sq_add_three_sq (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 3 * y ^ 2) ↔ p % 3 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3' : p ≠ 3 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [← neg_three_isSquare_iff p hodd hp3']
    exact isSquare_neg_of_repr 3 p hp x y hxy
  · intro h3
    have hsqm3 : IsSquare ((-3 : ℤ) : ZMod p) :=
      (neg_three_isSquare_iff p hodd hp3').mpr h3
    have hsq : IsSquare ((-12 : ℤ) : ZMod p) := by
      obtain ⟨s, hs⟩ := hsqm3
      refine ⟨2 * s, ?_⟩
      push_cast at hs ⊢
      linear_combination (4 : ZMod p) * hs
    have hpD : ¬ (p : ℤ) ∣ (-12 : ℤ) := by
      intro hdvd
      have h12 : (p : ℤ) ∣ 12 := (dvd_neg).mp hdvd
      have h12' : p ∣ 12 := by exact_mod_cast h12
      have h223 : p ∣ 2 ^ 2 * 3 := by
        have he : (2 : ℕ) ^ 2 * 3 = 12 := by norm_num
        rw [he]
        exact h12'
      rcases (Nat.Prime.dvd_mul hp).mp h223 with h4 | h3d
      · have h2d : p ∣ 2 := hp.dvd_of_dvd_pow h4
        have := Nat.le_of_dvd (by norm_num) h2d
        omega
      · have := Nat.le_of_dvd (by norm_num) h3d
        omega
    obtain ⟨b, c, hdiscr, hprim⟩ :=
      exists_form_of_isSquare (-12) (Or.inl (by decide)) p hp hodd hpD hsq
    have hpos : (⟨(p : ℤ), b, c⟩ : BinaryQF).PosDef := by
      constructor
      · show (0 : ℤ) < (p : ℤ)
        exact_mod_cast hp.pos
      · rw [hdiscr]
        norm_num
    obtain ⟨g, ⟨hgred, hgequiv⟩, -⟩ := exists_unique_reduced _ hpos
    have hgdiscr : g.discr = -12 := by
      rw [← discr_eq_of_properlyEquivalent hgequiv]
      exact hdiscr
    have hgprim : g.Primitive := (primitive_of_properlyEquivalent hgequiv).mp hprim
    have hg3 : g = ⟨1, 0, 3⟩ := reduced_neg_twelve g hgred hgprim hgdiscr
    obtain ⟨N, hN, hNg⟩ := properlyEquivalent_equivalence.symm hgequiv
    have hev := eval_action N g 1 0
    rw [hNg] at hev
    have hf10 : (⟨(p : ℤ), b, c⟩ : BinaryQF).eval 1 0 = (p : ℤ) := by
      simp [BinaryQF.eval]
    refine ⟨N 0 0 * 1 + N 0 1 * 0, N 1 0 * 1 + N 1 1 * 0, ?_⟩
    rw [← hf10, hev, hg3]
    simp only [BinaryQF.eval]
    ring

/-- **(1.3)** Brahmagupta-Fibonacci identity expressing a product of sums of two
squares as a sum of two squares. -/
theorem mul_sq_add_sq (x y z w : ℤ) :
    (x ^ 2 + y ^ 2) * (z ^ 2 + w ^ 2) = (x * z - y * w) ^ 2 + (x * w + y * z) ^ 2 := by
  ring

/-- **(1.6)** The analogous identity for the form `x² + n y²`. -/
theorem mul_sq_add_nsq (n x y z w : ℤ) :
    (x ^ 2 + n * y ^ 2) * (z ^ 2 + n * w ^ 2)
      = (x * z - n * y * w) ^ 2 + n * (x * w + y * z) ^ 2 := by
  ring

/-- **Descent Step** (Cox §1, case `n = 1`). If an odd prime `p` divides `x²+y²`
with `gcd(x,y)=1`, then `p` is itself a sum of two squares. -/
theorem descent_step (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ)
    (hcop : IsCoprime x y) (hdvd : (p : ℤ) ∣ x ^ 2 + y ^ 2) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpy : ¬ (p : ℤ) ∣ y := by
    intro hdy
    have hy2 : (p : ℤ) ∣ y ^ 2 := hdy.trans (dvd_pow_self y two_ne_zero)
    have hdx2 : (p : ℤ) ∣ x ^ 2 := by
      have h := dvd_sub hdvd hy2
      rwa [show x ^ 2 + y ^ 2 - y ^ 2 = x ^ 2 from by ring] at h
    have hdx : (p : ℤ) ∣ x := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hdx2
    have hu : IsUnit (p : ℤ) := hcop.isUnit_of_dvd' hdx hdy
    have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    rcases Int.isUnit_iff.mp hu with h | h <;> omega
  have hy0 : (y : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hxy : (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 = 0 := by
    have h0 : ((x ^ 2 + y ^ 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at h0; exact h0
  have hX : (x : ZMod p) ^ 2 = -(y : ZMod p) ^ 2 := by linear_combination hxy
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(x : ZMod p) * (y : ZMod p)⁻¹, ?_⟩
    have hz : ((x : ZMod p) * (y : ZMod p)⁻¹) ^ 2 = -1 := by
      rw [mul_pow, inv_pow, hX, neg_mul, mul_inv_cancel₀ (pow_ne_zero 2 hy0)]
    rw [← hz]; ring
  rw [ZMod.exists_sq_eq_neg_one_iff] at hsq
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hsq
  exact ⟨a, b, by exact_mod_cast hab.symm⟩

/-- **Lemma 1.4.** If `N` is a sum of two relatively prime squares and the prime
`q = x²+y²` divides `N`, then `N/q` is again a sum of two relatively prime
squares. This gives the induction step in the descent argument. -/
theorem descent_lemma (N a b x y : ℤ) (q : ℕ) (hq : q.Prime)
    (hN : N = a ^ 2 + b ^ 2) (hcop : IsCoprime a b)
    (hqf : (q : ℤ) = x ^ 2 + y ^ 2) (hdvd : (q : ℤ) ∣ N) :
    ∃ c d : ℤ, N = (q : ℤ) * (c ^ 2 + d ^ 2) ∧ IsCoprime c d := by
  have hqprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.pos.ne'
  have hkey : (q : ℤ) ∣ (x * b - a * y) * (x * b + a * y) := by
    have e : (x * b - a * y) * (x * b + a * y) = x ^ 2 * N - a ^ 2 * (q : ℤ) := by
      rw [hN, hqf]; ring
    rw [e]
    exact dvd_sub (hdvd.mul_left (x ^ 2)) (dvd_mul_left (q : ℤ) (a ^ 2))
  rcases hqprime.dvd_or_dvd hkey with h1 | h1
  · obtain ⟨d, hd⟩ : (q : ℤ) ∣ a * y - b * x := by
      have e : a * y - b * x = -(x * b - a * y) := by ring
      rw [e]; exact (dvd_neg).mpr h1
    have hdiv2 : (q : ℤ) ∣ (a * x + b * y) ^ 2 := by
      refine ⟨N - (q : ℤ) * d ^ 2, ?_⟩
      have hNq : N * (q : ℤ) = (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 := by
        rw [hN, hqf]; ring
      have e : (a * x + b * y) ^ 2 = N * (q : ℤ) - (a * y - b * x) ^ 2 := by
        rw [hNq]; ring
      rw [e, hd]; ring
    obtain ⟨c, hc⟩ := hqprime.dvd_of_dvd_pow hdiv2
    have ha_eq : a = c * x + d * y := by
      have h2 : a * (q : ℤ) = (c * x + d * y) * (q : ℤ) := by
        have e1 : a * (q : ℤ) = x * (a * x + b * y) + y * (a * y - b * x) := by
          rw [hqf]; ring
        rw [e1, hc, hd]; ring
      exact mul_right_cancel₀ hq0 h2
    have hb_eq : b = c * y - d * x := by
      have h2 : b * (q : ℤ) = (c * y - d * x) * (q : ℤ) := by
        have e1 : b * (q : ℤ) = y * (a * x + b * y) - x * (a * y - b * x) := by
          rw [hqf]; ring
        rw [e1, hc, hd]; ring
      exact mul_right_cancel₀ hq0 h2
    refine ⟨c, d, ?_, ?_⟩
    · have hNq : N * (q : ℤ) = (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 := by
        rw [hN, hqf]; ring
      have hcancel : N * (q : ℤ) = ((q : ℤ) * (c ^ 2 + d ^ 2)) * (q : ℤ) := by
        rw [hNq, hc, hd]; ring
      exact mul_right_cancel₀ hq0 hcancel
    · obtain ⟨u, v, huv⟩ := hcop
      refine ⟨u * x + v * y, u * y - v * x, ?_⟩
      have e : (u * x + v * y) * c + (u * y - v * x) * d
          = u * (c * x + d * y) + v * (c * y - d * x) := by ring
      rw [e, ← ha_eq, ← hb_eq]; exact huv
  · obtain ⟨d, hd⟩ : (q : ℤ) ∣ a * y + b * x := by
      have e : a * y + b * x = x * b + a * y := by ring
      rw [e]; exact h1
    have hdiv2 : (q : ℤ) ∣ (a * x - b * y) ^ 2 := by
      refine ⟨N - (q : ℤ) * d ^ 2, ?_⟩
      have hNq : N * (q : ℤ) = (a * x - b * y) ^ 2 + (a * y + b * x) ^ 2 := by
        rw [hN, hqf]; ring
      have e : (a * x - b * y) ^ 2 = N * (q : ℤ) - (a * y + b * x) ^ 2 := by
        rw [hNq]; ring
      rw [e, hd]; ring
    obtain ⟨c, hc⟩ := hqprime.dvd_of_dvd_pow hdiv2
    have ha_eq : a = c * x + d * y := by
      have h2 : a * (q : ℤ) = (c * x + d * y) * (q : ℤ) := by
        have e1 : a * (q : ℤ) = x * (a * x - b * y) + y * (a * y + b * x) := by
          rw [hqf]; ring
        rw [e1, hc, hd]; ring
      exact mul_right_cancel₀ hq0 h2
    have hb_eq : b = d * x - c * y := by
      have h2 : b * (q : ℤ) = (d * x - c * y) * (q : ℤ) := by
        have e1 : b * (q : ℤ) = x * (a * y + b * x) - y * (a * x - b * y) := by
          rw [hqf]; ring
        rw [e1, hc, hd]; ring
      exact mul_right_cancel₀ hq0 h2
    refine ⟨c, d, ?_, ?_⟩
    · have hNq : N * (q : ℤ) = (a * x - b * y) ^ 2 + (a * y + b * x) ^ 2 := by
        rw [hN, hqf]; ring
      have hcancel : N * (q : ℤ) = ((q : ℤ) * (c ^ 2 + d ^ 2)) * (q : ℤ) := by
        rw [hNq, hc, hd]; ring
      exact mul_right_cancel₀ hq0 hcancel
    · obtain ⟨u, v, huv⟩ := hcop
      refine ⟨u * x - v * y, u * y + v * x, ?_⟩
      have e : (u * x - v * y) * c + (u * y + v * x) * d
          = u * (c * x + d * y) + v * (d * x - c * y) := by ring
      rw [e, ← ha_eq, ← hb_eq]; exact huv
/-- **Lemma 1.7.** For nonzero `n` and an odd prime `p ∤ n`, `p` divides a
primitively represented value `x²+ny²` iff `−n` is a quadratic residue mod `p`,
i.e. `(−n/p) = 1`. -/
theorem dvd_sq_add_nsq_iff_isSquare (n : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hpn : ¬ (p : ℤ) ∣ n) :
    (∃ x y : ℤ, IsCoprime x y ∧ (p : ℤ) ∣ x ^ 2 + n * y ^ 2)
      ↔ IsSquare ((-n : ℤ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨x, y, hcop, hdvd⟩
    have hpy : ¬ (p : ℤ) ∣ y := by
      intro hdy
      have hy2 : (p : ℤ) ∣ n * y ^ 2 :=
        (hdy.trans (dvd_pow_self y two_ne_zero)).mul_left n
      have hdx2 : (p : ℤ) ∣ x ^ 2 := by
        have h := dvd_sub hdvd hy2
        rwa [show x ^ 2 + n * y ^ 2 - n * y ^ 2 = x ^ 2 from by ring] at h
      have hdx : (p : ℤ) ∣ x := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hdx2
      have hu : IsUnit (p : ℤ) := hcop.isUnit_of_dvd' hdx hdy
      have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      rcases Int.isUnit_iff.mp hu with h | h <;> omega
    have hy0 : (y : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hxy : (x : ZMod p) ^ 2 + (n : ZMod p) * (y : ZMod p) ^ 2 = 0 := by
      have h0 : ((x ^ 2 + n * y ^ 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
      push_cast at h0; exact h0
    refine ⟨(x : ZMod p) * (y : ZMod p)⁻¹, ?_⟩
    have hz : ((x : ZMod p) * (y : ZMod p)⁻¹) ^ 2 = ((-n : ℤ) : ZMod p) := by
      have hX : (x : ZMod p) ^ 2 = -(n : ZMod p) * (y : ZMod p) ^ 2 := by
        linear_combination hxy
      rw [mul_pow, inv_pow, hX, mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero 2 hy0), mul_one]
      push_cast; ring
    rw [← hz]; ring
  · rintro ⟨r, hr⟩
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨a, 1, isCoprime_one_right, ?_⟩
    have hcast : ((a ^ 2 + n * 1 ^ 2 : ℤ) : ZMod p) = 0 := by
      push_cast
      push_cast at hr
      linear_combination -hr
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
/-- **Conjecture 1.9** (Euler's form of reciprocity). For distinct odd primes
`p, q`, `(q/p) = 1` iff `p ≡ ±β² (mod 4q)` for some odd integer `β`. -/
theorem euler_reciprocity (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    IsSquare ((q : ℤ) : ZMod p)
      ↔ ∃ β : ℤ, Odd β ∧
          ((p : ℤ) ≡ β ^ 2 [ZMOD (4 * q)] ∨ (p : ℤ) ≡ -β ^ 2 [ZMOD (4 * q)]) := by
  sorry

/-- **Proposition 1.10** (Law of Quadratic Reciprocity). For *distinct* odd primes
`p, q`, `(p/q)(q/p) = (−1)^((p−1)/2·(q−1)/2)`. (The hypothesis `p ≠ q` is part of
Cox's statement - "distinct odd primes"; without it the claim is false at `p = q`,
where the left side is `0`.) -/
theorem quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p (q : ℤ) * legendreSym q (p : ℤ) = (-1) ^ (p / 2 * (q / 2)) := by
  rw [mul_comm (legendreSym p (q : ℤ)) (legendreSym q (p : ℤ))]
  exact legendreSym.quadratic_reciprocity hp hq hpq

/-- **First supplement** to quadratic reciprocity: `(−1/p) = (−1)^((p−1)/2)`.
(This is the first line of Cox's (1.11); Cox pairs it with multiplicativity
`(ab/p) = (a/p)(b/p)`, not with the second supplement below.) -/
theorem legendreSym_first_supplement (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = (-1) ^ ((p - 1) / 2) := by
  have hp2 : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp
  rw [legendreSym.at_neg_one hp, ZMod.χ₄_eq_neg_one_pow hp2]
  congr 1
  omega

/-- **Second supplement** to quadratic reciprocity: `(2/p) = (−1)^((p²−1)/8)`.
(A standard supplement used in §1; *not* part of Cox's numbered (1.11).)

Rewrite `(2/p) = χ₈ p` using `legendreSym.at_two`, then check the parity of
`(p²−1)/8` according to the residue of `p` modulo 16. -/
theorem legendreSym_second_supplement (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  rw [ legendreSym.at_two hp ];
  rw [ ZMod.χ₈_nat_eq_if_mod_eight ];
  rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
  · exact absurd ( Nat.Prime.eq_two_or_odd ( Fact.out : Nat.Prime ( 2 * k ) ) ) ( by omega );
  · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> ring_nf <;> norm_num [ Nat.add_mod, Nat.mul_mod ];
    · norm_num [ add_assoc, Nat.add_div ];
      rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> ring_nf <;> norm_num [ Nat.add_mod, Nat.mul_mod ];
      · norm_num [ show k ^ 2 * 64 / 8 = k ^ 2 * 8 by rw [ Nat.div_eq_of_eq_mul_left ] <;> linarith ];
      · norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.add_mod, Nat.pow_mod ];
        norm_num [ pow_add, pow_mul' ];
    · norm_num [ show 9 + k * 24 + k ^ 2 * 16 - 1 = 8 * ( 1 + k * 3 + k ^ 2 * 2 ) by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
      rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> ring_nf <;> norm_num [ Nat.add_mod, Nat.mul_mod ]

/-- **Lemma 1.14.** For nonzero `D ≡ 0,1 (mod 4)` there is a homomorphism
`χ : (ℤ/Dℤ)ˣ → {±1}` whose value on the class of an odd `m` prime to `D` is the
Jacobi symbol `(D/m)`. (Equivalent to quadratic reciprocity.) -/
theorem exists_quadraticChar (D : ℤ) (hD0 : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ χ : (ZMod D.natAbs)ˣ →* ℤˣ,
      ∀ (m : ℕ) (_ : Odd m) (hco : Nat.Coprime m D.natAbs),
        (χ (ZMod.unitOfCoprime m hco) : ℤ) = jacobiSym D m := by
  sorry

/-- **Corollary 1.19.** For each `n > 0` there is a set of residue classes modulo
`4n` characterizing the odd primes `p ∤ n` that divide a primitive `x²+ny²` (the
solution of the Reciprocity Step by congruences). -/
theorem reciprocity_step (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset (ZMod (4 * n)),
      ∀ (p : ℕ), p.Prime → Odd p → ¬ (p : ℤ) ∣ (n : ℤ) →
        ((∃ x y : ℤ, IsCoprime x y ∧ (p : ℤ) ∣ x ^ 2 + n * y ^ 2)
          ↔ (p : ZMod (4 * n)) ∈ S) := by
  sorry

end PrimesX2NY2.Fermat
