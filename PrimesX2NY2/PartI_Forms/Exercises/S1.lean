/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.Fermat

/-!
# Part I, §1 - Exercises

Faithful `sorry`-bodied statements of the exercises of Cox §1 (Exercises 1.1-1.16).
Cited by number only; statements are paraphrased.

A handful of sub-parts (1.12(b), 1.12(c), 1.16) are recorded in the blueprint as
`\notready` flagged nodes rather than Lean signatures - see the FLAG LIST in the
project report - because a faithful self-contained statement requires fixing a
specific homomorphism / subgroup that the exercise only pins down implicitly.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.PartI.S1

/-- Forward difference operator `Δg(x) = g(x+1) − g(x)`, used in Exercise 1.2. -/
def diff (g : ℤ → ℤ) : ℤ → ℤ := fun x => g (x + 1) - g x

/-- **Exercise 1.1(a).** The identity `(1.3)`. -/
theorem ex_1_1_a (x y z w : ℤ) :
    (x ^ 2 + y ^ 2) * (z ^ 2 + w ^ 2) = (x * z - y * w) ^ 2 + (x * w + y * z) ^ 2 := by ring

/-- **Exercise 1.1(b).** Euler's generalization to `(ax²+cy²)(az²+cw²)`. -/
theorem ex_1_1_b (a c x y z w : ℤ) :
    (a * x ^ 2 + c * y ^ 2) * (a * z ^ 2 + c * w ^ 2)
      = (a * x * z - c * y * w) ^ 2 + a * c * (x * w + y * z) ^ 2 := by ring

/-- **Exercise 1.2(a).** For `k ≥ 1`, `Δᵏg` is an integral linear combination of
`g(x), g(x+1), …, g(x+k)`. -/
theorem ex_1_2_a (k : ℕ) (g : ℤ → ℤ) :
    ∃ c : ℕ → ℤ, ∀ x : ℤ,
      diff^[k] g x = ∑ i ∈ Finset.range (k + 1), c i * g (x + (i : ℤ)) := by
  sorry

/-- **Exercise 1.2(b).** For a monic `f` of degree `d`, `Δᵈf = d!`. -/
theorem ex_1_2_b (f : Polynomial ℤ) (hf : f.Monic) :
    ∀ x : ℤ, diff^[f.natDegree] (fun n => f.eval n) x = (Nat.factorial f.natDegree : ℤ) := by
  sorry

/-- **Exercise 1.2(c).** Euler's lemma: a monic integer polynomial of degree
`< p` is not identically zero modulo a prime `p`. -/
theorem ex_1_2_c (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) (hf : f.Monic)
    (hd : f.natDegree < p) : ∃ x : ℤ, ¬ (p : ℤ) ∣ f.eval x := by
  sorry

/-- **Exercise 1.3(a).** Lemma 1.4 for the form `x²+ny²`. -/
theorem ex_1_3_a (n N a b x y : ℤ) (q : ℕ) (hq : q.Prime)
    (hN : N = a ^ 2 + n * b ^ 2) (hcop : IsCoprime a b)
    (hqf : (q : ℤ) = x ^ 2 + n * y ^ 2) (hdvd : (q : ℤ) ∣ N) :
    ∃ c d : ℤ, N = (q : ℤ) * (c ^ 2 + n * d ^ 2) ∧ IsCoprime c d := by
  sorry

/-- **Exercise 1.3(b).** The same descent works for `n = 3` and `q = 4 = 1²+3·1²`. -/
theorem ex_1_3_b (N a b : ℤ) (hN : N = a ^ 2 + 3 * b ^ 2) (hcop : IsCoprime a b)
    (hdvd : (4 : ℤ) ∣ N) :
    ∃ c d : ℤ, N = 4 * (c ^ 2 + 3 * d ^ 2) ∧ IsCoprime c d := by
  sorry

/-- **Exercise 1.4(a).** Descent Step for `x²+2y²`. -/
theorem ex_1_4_a (p : ℕ) (hp : p.Prime) (x y : ℤ) (hcop : IsCoprime x y)
    (hdvd : (p : ℤ) ∣ x ^ 2 + 2 * y ^ 2) : ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 2 * b ^ 2 := by
  sorry

/-- **Exercise 1.4(b).** Descent Step for `x²+3y²` (odd `p`). -/
theorem ex_1_4_b (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ)
    (hcop : IsCoprime x y) (hdvd : (p : ℤ) ∣ x ^ 2 + 3 * y ^ 2) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 3 * b ^ 2 := by
  sorry

/-- Helper: `−3` is a quadratic residue mod an odd prime `p ≠ 3` iff `p ≡ 1 (mod 3)`. -/
theorem neg_three_isSquare_iff (p : ℕ) [Fact p.Prime] (hodd : Odd p) (hp3 : p ≠ 3) :
    IsSquare ((-3 : ℤ) : ZMod p) ↔ p % 3 = 1 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  -- `(-3 : ZMod p) ≠ 0` since `p ∤ 3`
  have ha : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have h3 : (p : ℤ) ∣ (3 : ℤ) := (dvd_neg).mp h
    have h3' : p ∣ 3 := by exact_mod_cast h3
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three p h3') with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hp3 h1
  rw [← legendreSym.eq_one_iff p ha]
  -- `(−3/p) = (−1/p)(3/p) = (−1)^(p/2) · (−1)^(p/2) · (p/3) = (p/3)`
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
  -- Evaluate `(p/3)` by the residue of `p` mod 3
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

/-- **Exercise 1.5.** If `p = 3k+1` is prime then `(−3/p) = 1`. -/
theorem ex_1_5 (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : p = 3 * k + 1) :
    IsSquare ((-3 : ℤ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := by
    rcases hp.eq_two_or_odd' with rfl | h
    · exact absurd hk (by omega)
    · exact h
  exact (neg_three_isSquare_iff p hodd (by omega)).mpr (by omega)

/-- **Exercise 1.6.** Prove Lemma 1.7. -/
theorem ex_1_6 (n : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpn : ¬ (p : ℤ) ∣ n) :
    (∃ x y : ℤ, IsCoprime x y ∧ (p : ℤ) ∣ x ^ 2 + n * y ^ 2)
      ↔ IsSquare ((-n : ℤ) : ZMod p) :=
  PrimesX2NY2.Fermat.dvd_sq_add_nsq_iff_isSquare n p hp hodd hpn

/-- **Exercise 1.7.** Quadratic reciprocity in the form `(1.12)`:
`(p*/q) = (q/p)` with `p* = (−1)^((p−1)/2)·p`. -/
theorem ex_1_7 (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q ((-1) ^ ((p - 1) / 2) * (p : ℤ)) = legendreSym p (q : ℤ) := by
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hq1 : q % 2 = 1 := Nat.odd_iff.mp ((Fact.out : q.Prime).odd_of_ne_two hq)
  have hpow : ∀ k : ℕ, legendreSym q ((-1 : ℤ) ^ k) = (legendreSym q (-1)) ^ k := by
    intro k
    induction k with
    | zero => simp [legendreSym.at_one]
    | succ n ih => rw [pow_succ, pow_succ, legendreSym.mul, ih]
  rw [legendreSym.mul, hpow, legendreSym.at_neg_one hq, ZMod.χ₄_eq_neg_one_pow hq1,
    legendreSym.quadratic_reciprocity' hp hq, ← pow_mul, ← mul_assoc, ← pow_add]
  have hdiv : (p - 1) / 2 = p / 2 := by omega
  rw [hdiv, show q / 2 * (p / 2) + p / 2 * (q / 2) = 2 * (p / 2 * (q / 2)) by ring,
    pow_mul, neg_one_sq, one_pow, one_mul]

/-- **Exercise 1.8.** The reciprocity statement `(1.13)`:
`(p*/q) = 1 ↔ p ≡ ±β² (mod 4q)` for some odd `β`. -/
theorem ex_1_8 (p q : ℕ) (hp : p.Prime) [Fact q.Prime] (hq : q ≠ 2) :
    legendreSym q ((-1) ^ ((p - 1) / 2) * (p : ℤ)) = 1
      ↔ ∃ β : ℤ, Odd β ∧
          ((p : ℤ) ≡ β ^ 2 [ZMOD (4 * q)] ∨ (p : ℤ) ≡ -β ^ 2 [ZMOD (4 * q)]) := by
  sorry

/-- **Exercise 1.9(a).** For `p > 3`, the representability `p ≡ 1 (mod 3)` matches
the reciprocity instance `(−3/p) = (p/3)`. -/
theorem ex_1_9_a (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    IsSquare ((-3 : ℤ) : ZMod p) ↔ p % 3 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact neg_three_isSquare_iff p (hp.odd_of_ne_two (by omega)) (by omega)

/-- **Exercise 1.9(b).** The cases `x²+y²`, `x²+2y²` correspond to the
supplementary laws for `(−1/p)` and `(2/p)`. -/
theorem ex_1_9_b (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = (-1) ^ ((p - 1) / 2) ∧
      legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  refine ⟨?_, ?_⟩
  · have hp2 : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp
    rw [legendreSym.at_neg_one hp, ZMod.χ₄_eq_neg_one_pow hp2]; congr 1; omega
  · rw [legendreSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight]
    rcases Nat.even_or_odd' p with ⟨k, rfl | rfl⟩ <;> norm_num at *
    · exact absurd (Nat.Prime.eq_two_or_odd (Fact.out : Nat.Prime (2 * k))) (by omega)
    · rcases Nat.even_or_odd' k with ⟨k, rfl | rfl⟩ <;> ring_nf <;> norm_num [Nat.add_mod, Nat.mul_mod]
      · norm_num [add_assoc, Nat.add_div]
        rcases Nat.even_or_odd' k with ⟨k, rfl | rfl⟩ <;> ring_nf <;> norm_num [Nat.add_mod, Nat.mul_mod]
        · norm_num [show k ^ 2 * 64 / 8 = k ^ 2 * 8 by rw [Nat.div_eq_of_eq_mul_left] <;> linarith]
        · norm_num [Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.add_mod, Nat.pow_mod]
          norm_num [pow_add, pow_mul']
      · norm_num [show 9 + k * 24 + k ^ 2 * 16 - 1 = 8 * (1 + k * 3 + k ^ 2 * 2) by
          rw [Nat.sub_eq_of_eq_add]; ring]
        rcases Nat.even_or_odd' k with ⟨k, rfl | rfl⟩ <;> ring_nf <;> norm_num [Nat.add_mod, Nat.mul_mod]

/-- **Exercise 1.10(a).** The Jacobi symbol depends only on the numerator mod the
denominator. -/
theorem ex_1_10_a (M N : ℤ) (m : ℕ) (h : M ≡ N [ZMOD m]) :
    jacobiSym M m = jacobiSym N m :=
  jacobiSym.mod_left' h

/-- **Exercise 1.10(b).** Multiplicativity of the Jacobi symbol `(1.15)`. -/
theorem ex_1_10_b (M N : ℤ) (m n : ℕ) :
    jacobiSym (M * N) m = jacobiSym M m * jacobiSym N m ∧
      jacobiSym M (m * n) = jacobiSym M m * jacobiSym M n := by
  -- FLAG (under-hypothesized): the second conjunct is FALSE for m = 0 or n = 0, since
  -- Mathlib defines `jacobiSym a 0 = 1`: with M = N = 2, m = 3, n = 0 the LHS is
  -- `jacobiSym 2 0 = 1` while the RHS is `jacobiSym 2 3 * jacobiSym 2 0 = -1`.
  -- Cox implicitly takes the moduli positive (indeed odd). The salvageable statements
  -- are `ex_1_10_b_left` and `ex_1_10_b_right` below.
  sorry

/-- The first conjunct of Exercise 1.10(b), which holds unconditionally
(`jacobiSym.mul_left`). -/
theorem ex_1_10_b_left (M N : ℤ) (m : ℕ) :
    jacobiSym (M * N) m = jacobiSym M m * jacobiSym N m :=
  jacobiSym.mul_left M N m

/-- The second conjunct of Exercise 1.10(b), under the (implicit in Cox) hypothesis
that the moduli are nonzero. -/
theorem ex_1_10_b_right (M : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    jacobiSym M (m * n) = jacobiSym M m * jacobiSym M n :=
  jacobiSym.mul_right' M hm hn

/-- **Exercise 1.10(c).** The supplementary laws for the Jacobi symbol `(1.16)`. -/
theorem ex_1_10_c (m : ℕ) (hm : Odd m) :
    jacobiSym (-1) m = (-1) ^ ((m - 1) / 2) ∧
      jacobiSym 2 m = (-1) ^ ((m ^ 2 - 1) / 8) := by
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  refine ⟨?_, ?_⟩
  · rw [jacobiSym.at_neg_one hm, ZMod.χ₄_eq_neg_one_pow hm2]; congr 1; omega
  · rw [jacobiSym.at_two hm, ZMod.χ₈_nat_eq_if_mod_eight]
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · simp at hm2
    · rcases Nat.even_or_odd' k with ⟨k, rfl | rfl⟩ <;> ring_nf <;> norm_num [Nat.add_mod, Nat.mul_mod]
      · norm_num [add_assoc, Nat.add_div]
        rcases Nat.even_or_odd' k with ⟨k, rfl | rfl⟩ <;> ring_nf <;> norm_num [Nat.add_mod, Nat.mul_mod]
        · norm_num [show k ^ 2 * 64 / 8 = k ^ 2 * 8 by rw [Nat.div_eq_of_eq_mul_left] <;> linarith]
        · norm_num [Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.add_mod, Nat.pow_mod]
          norm_num [pow_add, pow_mul']
      · norm_num [show 9 + k * 24 + k ^ 2 * 16 - 1 = 8 * (1 + k * 3 + k ^ 2 * 2) by
          rw [Nat.sub_eq_of_eq_add]; ring]
        rcases Nat.even_or_odd' k with ⟨k, rfl | rfl⟩ <;> ring_nf <;> norm_num [Nat.add_mod, Nat.mul_mod]

/-- **Exercise 1.10(d).** If `M` is a quadratic residue mod `m` (and prime to it)
then `(M/m) = 1` (the converse fails). -/
theorem ex_1_10_d (M : ℤ) (m : ℕ) (hm : Odd m) (hco : IsCoprime M (m : ℤ))
    (h : IsSquare (M : ZMod m)) : jacobiSym M m = 1 := by
  have hm0 : m ≠ 0 := by rcases hm with ⟨k, hk⟩; omega
  haveI : NeZero m := ⟨hm0⟩
  obtain ⟨x, hx⟩ := h
  have hbx : ((x.val : ℕ) : ZMod m) = x := ZMod.natCast_rightInverse x
  have hcong : (M : ZMod m) = (((x.val : ℤ) ^ 2 : ℤ) : ZMod m) := by
    push_cast
    rw [hbx, hx]
    ring
  have hmod : jacobiSym M m = jacobiSym ((x.val : ℤ)) m ^ 2 := by
    rw [jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff _ _ _).mp hcong),
      jacobiSym.pow_left]
  have hMne : jacobiSym M m ≠ 0 :=
    jacobiSym.ne_zero (Int.isCoprime_iff_gcd_eq_one.mp hco)
  rcases jacobiSym.trichotomy (x.val : ℤ) m with h0 | h1 | h1
  · rw [h0] at hmod
    norm_num at hmod
    exact absurd hmod hMne
  · rw [h1] at hmod
    simpa using hmod
  · rw [h1] at hmod
    simpa using hmod

/-- **Exercise 1.11.** Completion of `(1.17)`: for `D ≡ 0,1 (mod 4)` and odd
`m ≡ n (mod D)`, `(D/m) = (D/n)`. -/
theorem ex_1_11 (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) (m n : ℕ)
    (hm : Odd m) (hn : Odd n) (h : (m : ℤ) ≡ (n : ℤ) [ZMOD D]) :
    jacobiSym D m = jacobiSym D n := by
  sorry

/-- **Exercise 1.12(a).** The map `χ([m]) = (D/m)` is a well-defined homomorphism
`(ℤ/Dℤ)ˣ → {±1}`. -/
theorem ex_1_12_a (D : ℤ) (hD0 : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ χ : (ZMod D.natAbs)ˣ →* ℤˣ,
      ∀ (m : ℕ) (_ : Odd m) (hco : Nat.Coprime m D.natAbs),
        (χ (ZMod.unitOfCoprime m hco) : ℤ) = jacobiSym D m := by
  sorry

/-- **Exercise 1.13(a).** Quadratic reciprocity, assuming Lemma 1.14. -/
theorem ex_1_13_a (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym p (q : ℤ) * legendreSym q (p : ℤ) = (-1) ^ (p / 2 * (q / 2)) := by
  -- FLAG (under-hypothesized): FALSE for p = q, since legendreSym p p = 0 while the RHS is +/-1.
  -- Mathlib's legendreSym.quadratic_reciprocity requires the missing hypothesis `p != q`.
  sorry

/-- **Exercise 1.13(b).** The supplementary laws, assuming Lemma 1.14. -/
theorem ex_1_13_b (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = (-1) ^ ((p - 1) / 2) ∧
      legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) :=
  ex_1_9_b p hp

/-- **Exercise 1.14.** When `n ≡ 3 (mod 4)` the congruence characterizing the
Reciprocity Step can be taken modulo `n` (rather than `4n`). -/
theorem ex_1_14 (n : ℕ) (hn : n % 4 = 3) :
    ∃ S : Finset (ZMod n),
      ∀ (p : ℕ), p.Prime → Odd p → ¬ (p : ℤ) ∣ (n : ℤ) →
        ((∃ x y : ℤ, IsCoprime x y ∧ (p : ℤ) ∣ x ^ 2 + n * y ^ 2)
          ↔ (p : ZMod n) ∈ S) := by
  sorry

/-- **Exercise 1.15.** The residue classes in `(ℤ/84ℤ)ˣ` with `(−21/p) = 1`
(solving the Reciprocity Step for `n = 21`). -/
theorem ex_1_15 :
    ∃ S : Finset (ZMod 84),
      ∀ (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ 21 →
        (IsSquare ((-21 : ℤ) : ZMod p) ↔ (p : ZMod 84) ∈ S) := by
  sorry

end PrimesX2NY2.PartI.S1
