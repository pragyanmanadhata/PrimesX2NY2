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

/-- `diff` is Mathlib's forward difference at step `1`, definitionally. -/
lemma diff_eq_fwdDiff : diff = fwdDiff (1 : ℤ) := rfl

/-- The core descent step of Cox's Lemma 1.4, in the branch where `q ∣ ay − bx`. -/
theorem key13a (n N a b x y : ℤ) (q : ℕ) (hq : q.Prime)
    (hN : N = a ^ 2 + n * b ^ 2) (hcop : IsCoprime a b)
    (hqf : (q : ℤ) = x ^ 2 + n * y ^ 2)
    (h1 : (q : ℤ) ∣ a * y - b * x) :
    ∃ c d : ℤ, N = (q : ℤ) * (c ^ 2 + n * d ^ 2) ∧ IsCoprime c d := by
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq0 : (q : ℤ) ≠ 0 := hqp.ne_zero
  obtain ⟨d, hd⟩ := h1
  have hsq : (a * x + n * b * y) ^ 2 = (q : ℤ) * (N - n * (q : ℤ) * d ^ 2) := by
    linear_combination (-(x ^ 2 + n * y ^ 2)) * hN + (-N) * hqf
      + (-(n * ((a * y - b * x) + (q : ℤ) * d))) * hd
  obtain ⟨c, hc⟩ := hqp.dvd_of_dvd_pow (n := 2) ⟨_, hsq⟩
  have ha : c * x + n * d * y = a := by
    refine mul_left_cancel₀ hq0 ?_
    linear_combination (-x) * hc + (-(n * y)) * hd + (-a) * hqf
  have hb : c * y - d * x = b := by
    refine mul_left_cancel₀ hq0 ?_
    linear_combination (-y) * hc + x * hd + (-b) * hqf
  refine ⟨c, d, ?_, ?_⟩
  · refine (mul_left_cancel₀ hq0 ?_).symm
    linear_combination hsq - ((a * x + n * b * y) + (q : ℤ) * c) * hc
  · obtain ⟨u, v, huv⟩ := hcop
    exact ⟨u * x + v * y, u * n * y - v * x, by linear_combination huv + u * ha + v * hb⟩

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
  refine ⟨fun i => (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ), fun x => ?_⟩
  rw [diff_eq_fwdDiff, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- **Exercise 1.2(b).** For a monic `f` of degree `d`, `Δᵈf = d!`. -/
theorem ex_1_2_b (f : Polynomial ℤ) (hf : f.Monic) :
    ∀ x : ℤ, diff^[f.natDegree] (fun n => f.eval n) x = (Nat.factorial f.natDegree : ℤ) := by
  intro x
  have h := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial (R := ℤ) f) x
  rw [hf.leadingCoeff] at h
  rw [diff_eq_fwdDiff]
  simpa using h

/-- **Exercise 1.2(c).** Euler's lemma: a monic integer polynomial of degree
`< p` is not identically zero modulo a prime `p`. -/
theorem ex_1_2_c (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) (hf : f.Monic)
    (hd : f.natDegree < p) : ∃ x : ℤ, ¬ (p : ℤ) ∣ f.eval x := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have key : (p : ℤ) ∣ (Nat.factorial f.natDegree : ℤ) := by
    rw [← ex_1_2_b f hf 0, diff_eq_fwdDiff, fwdDiff_iter_eq_sum_shift]
    refine Finset.dvd_sum fun i _ => ?_
    rw [smul_eq_mul]
    exact Dvd.dvd.mul_left (hcon _) _
  have hpd : p ∣ Nat.factorial f.natDegree := by exact_mod_cast key
  have := (Nat.Prime.dvd_factorial hp).mp hpd
  omega

/-- **Exercise 1.3(a).** Lemma 1.4 for the form `x²+ny²`. -/
theorem ex_1_3_a (n N a b x y : ℤ) (q : ℕ) (hq : q.Prime)
    (hN : N = a ^ 2 + n * b ^ 2) (hcop : IsCoprime a b)
    (hqf : (q : ℤ) = x ^ 2 + n * y ^ 2) (hdvd : (q : ℤ) ∣ N) :
    ∃ c d : ℤ, N = (q : ℤ) * (c ^ 2 + n * d ^ 2) ∧ IsCoprime c d := by
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  obtain ⟨m, hm⟩ := hdvd
  have key : (q : ℤ) ∣ (a * y - b * x) * (a * y + b * x) :=
    ⟨y ^ 2 * m - b ^ 2, by linear_combination (y ^ 2) * hm - (y ^ 2) * hN + (b ^ 2) * hqf⟩
  rcases hqp.dvd_mul.mp key with h | h
  · exact key13a n N a b x y q hq hN hcop hqf h
  · refine key13a n N a b (-x) y q hq hN hcop (by linear_combination hqf) ?_
    rw [show a * y - b * (-x) = a * y + b * x by ring]
    exact h

/-- **Exercise 1.3(b).** The same descent works for `n = 3` and `q = 4 = 1²+3·1²`. -/
theorem ex_1_3_b (N a b : ℤ) (hN : N = a ^ 2 + 3 * b ^ 2) (hcop : IsCoprime a b)
    (hdvd : (4 : ℤ) ∣ N) :
    ∃ c d : ℤ, N = 4 * (c ^ 2 + 3 * d ^ 2) ∧ IsCoprime c d := by
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨s, hs⟩ := Int.even_or_odd' a
  obtain ⟨t, ht⟩ := Int.even_or_odd' b
  rcases hs with hs | hs <;> rcases ht with ht | ht <;> subst hs <;> subst ht
  · exfalso
    have hu : IsUnit (2 : ℤ) := hcop.isUnit_of_dvd' ⟨s, rfl⟩ ⟨t, rfl⟩
    rw [Int.isUnit_iff] at hu
    omega
  · exfalso
    have h : 4 * m = 4 * (s ^ 2) + 12 * (t ^ 2 + t) + 3 := by rw [← hm, hN]; ring
    have hq : ∀ u v w : ℤ, 4 * w ≠ 4 * u + 12 * v + 3 := by intro u v w; omega
    exact hq _ _ _ h
  · exfalso
    have h : 4 * m = 4 * (s ^ 2 + s) + 12 * (t ^ 2) + 1 := by rw [← hm, hN]; ring
    have hq : ∀ u v w : ℤ, 4 * w ≠ 4 * u + 12 * v + 1 := by intro u v w; omega
    exact hq _ _ _ h
  · obtain ⟨u, v, huv⟩ := hcop
    obtain ⟨k, hk⟩ := Int.even_or_odd' (s - t)
    rcases hk with hk | hk
    · exact ⟨2 * t + k + 1, k, by linear_combination hN + (4 * (s + t + 2 * k) + 4) * hk,
        u + v, 3 * u - v, by linear_combination huv - 2 * u * hk⟩
    · exact ⟨k - t, k + t + 1, by linear_combination hN + (4 * (s + t + 2 * k + 1) + 4) * hk,
        u - v, 3 * u + v, by linear_combination huv - 2 * u * hk⟩

/-- **Exercise 1.4(a).** Descent Step for `x²+2y²`. -/
theorem ex_1_4_a (p : ℕ) (hp : p.Prime) (x y : ℤ) (hcop : IsCoprime x y)
    (hdvd : (p : ℤ) ∣ x ^ 2 + 2 * y ^ 2) : ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 2 * b ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · exact ⟨0, 1, by norm_num⟩
  · have hodd : Odd p := hp.odd_of_ne_two hp2
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpn : ¬ (p : ℤ) ∣ (2 : ℤ) := by
      intro hd
      have h2 : p ∣ 2 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hsq : IsSquare ((-2 : ℤ) : ZMod p) :=
      (PrimesX2NY2.Fermat.dvd_sq_add_nsq_iff_isSquare 2 p hp hodd hpn).mp ⟨x, y, hcop, hdvd⟩
    have hsq2 : IsSquare (-2 : ZMod p) := by
      have h := hsq; push_cast at h; exact h
    have hmod : p % 8 = 1 ∨ p % 8 = 3 := (ZMod.exists_sq_eq_neg_two_iff hp2).mp hsq2
    exact (PrimesX2NY2.Fermat.prime_sq_add_two_sq p hp hodd).mpr hmod

/-- **Exercise 1.4(b).** Descent Step for `x²+3y²` (odd `p`). -/
theorem ex_1_4_b (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ)
    (hcop : IsCoprime x y) (hdvd : (p : ℤ) ∣ x ^ 2 + 3 * y ^ 2) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 3 * b ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 3 with rfl | hp3
  · exact ⟨0, 1, by norm_num⟩
  · have hp2 : p ≠ 2 := by
      rintro rfl
      rcases hodd with ⟨k, hk⟩; omega
    have hlt : 3 < p := by have := hp.two_le; omega
    have hpn : ¬ (p : ℤ) ∣ (3 : ℤ) := by
      intro hd
      have h3 : p ∣ 3 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    have hsq : IsSquare ((-3 : ℤ) : ZMod p) :=
      (PrimesX2NY2.Fermat.dvd_sq_add_nsq_iff_isSquare 3 p hp hodd hpn).mp ⟨x, y, hcop, hdvd⟩
    have hmod : p % 3 = 1 := (PrimesX2NY2.Fermat.neg_three_isSquare_iff p hodd hp3).mp hsq
    exact (PrimesX2NY2.Fermat.prime_sq_add_three_sq p hp hlt).mpr hmod

/-- Helper: `−3` is a quadratic residue mod an odd prime `p ≠ 3` iff `p ≡ 1 (mod 3)`.
Proved in `PrimesX2NY2.Fermat`; Mathlib has only the `−1`, `2`, `−2` cases. -/
theorem neg_three_isSquare_iff (p : ℕ) [Fact p.Prime] (hodd : Odd p) (hp3 : p ≠ 3) :
    IsSquare ((-3 : ℤ) : ZMod p) ↔ p % 3 = 1 :=
  PrimesX2NY2.Fermat.neg_three_isSquare_iff p hodd hp3

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
  -- FLAG (under-hypothesized): FALSE as stated, in two independent ways.
  -- (i) p = 2 with q ≡ ±1 (mod 8) (smallest q = 7): the left side is
  --     legendreSym 7 2 = 1, but the right side is unsatisfiable, since β odd makes
  --     ±β² − 2 odd and hence never divisible by the even modulus 4q.
  -- (ii) p = q: the left side is 0, while the right side holds with β = q.
  -- With p odd and p ≠ q the ± statement is correct (checked numerically for all
  -- odd p ≠ q < 120). See `ex_1_8_FALSE` for a machine-checked instance of (i).
  sorry

private theorem ne0_2_7 : ((2 : ℤ) : ZMod 7) ≠ 0 := by decide

private theorem sq2_7 : IsSquare ((2 : ℤ) : ZMod 7) := by decide

local instance factSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem leg7_two : legendreSym 7 2 = 1 :=
  (legendreSym.eq_one_iff 7 ne0_2_7).mpr sq2_7

/-- Cox (1.13) as literally stated in `ex_1_8` is FALSE: it fails at `p = 2`, `q = 7`
(and also whenever `p = q`). -/
theorem ex_1_8_FALSE :
    ¬ (∀ (p q : ℕ), p.Prime → ∀ [Fact q.Prime], q ≠ 2 →
        (legendreSym q ((-1) ^ ((p - 1) / 2) * (p : ℤ)) = 1
          ↔ ∃ β : ℤ, Odd β ∧
              ((p : ℤ) ≡ β ^ 2 [ZMOD (4 * q)] ∨ (p : ℤ) ≡ -β ^ 2 [ZMOD (4 * q)]))) := by
  intro h
  have h2 := (h 2 7 (by norm_num) (by norm_num)).mp (by
    have harg : ((-1 : ℤ) ^ ((2 - 1) / 2) * ((2 : ℕ) : ℤ)) = 2 := by norm_num
    rw [harg]
    exact leg7_two)
  obtain ⟨β, hβ, hcase⟩ := h2
  obtain ⟨m, hm⟩ := (hβ.pow : Odd (β ^ 2))
  rcases hcase with hc | hc
  · obtain ⟨t, ht⟩ := hc.dvd
    rw [hm] at ht
    push_cast at ht
    omega
  · obtain ⟨t, ht⟩ := hc.dvd
    rw [hm] at ht
    push_cast at ht
    omega

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
private theorem chi4_congr {m n : ℕ} (h : m % 4 = n % 4) :
    ZMod.χ₄ (m : ZMod 4) = ZMod.χ₄ (n : ZMod 4) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₄_nat_eq_if_mod_four, h,
    show m % 2 = n % 2 by omega]

private theorem chi8_congr {m n : ℕ} (h : m % 8 = n % 8) :
    ZMod.χ₈ (m : ZMod 8) = ZMod.χ₈ (n : ZMod 8) := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight, h,
    show m % 2 = n % 2 by omega]

private theorem gcd_two_odd {k : ℕ} (hk : Odd k) : Int.gcd 2 (k : ℤ) = 1 := by
  have h : Nat.gcd 2 k = 1 := Nat.coprime_two_left.mpr hk
  simpa [Int.gcd] using h

private theorem jac_recip_congr {d m n : ℕ} (hd : Odd d) (hm : Odd m) (hn : Odd n)
    (h4 : m % 4 = n % 4) (hmod : (m : ℤ) % (d : ℤ) = (n : ℤ) % (d : ℤ)) :
    jacobiSym (d : ℤ) m = jacobiSym (d : ℤ) n := by
  rw [jacobiSym.quadratic_reciprocity' hd hm, jacobiSym.quadratic_reciprocity' hd hn,
    jacobiSym.mod_left' hmod]
  simp only [qrSign]
  rw [chi4_congr h4]

private theorem case_neg_odd {d m : ℕ} (hd3 : d % 4 = 3) (hm : Odd m) :
    jacobiSym (-(d : ℤ)) m = jacobiSym (m : ℤ) d := by
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hm, jacobiSym.quadratic_reciprocity' hdodd hm]
  simp only [qrSign]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1]
    simp
  · rw [ZMod.χ₄_nat_three_mod_four h3,
      jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_three_mod_four hd3]
    ring

theorem mod_right_of_discr {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {m n : ℕ}
    (hm : Odd m) (hn : Odd n) (h : (m : ℤ) ≡ (n : ℤ) [ZMOD D]) :
    jacobiSym D m = jacobiSym D n := by
  rcases eq_or_ne D 0 with rfl | hD0
  · have h' : ((n : ℤ)) - (m : ℤ) = 0 := zero_dvd_iff.mp h.dvd
    have hmn : m = n := by omega
    rw [hmn]
  have hN0 : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
  obtain ⟨e, d, hd2, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 2 (by norm_num)
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd2' : d % 2 = 1 := Nat.odd_iff.mp hdodd
  have hcast : ((D.natAbs : ℕ) : ℤ) = 2 ^ e * (d : ℤ) := by rw [hNe]; push_cast; ring
  have hdvd : (2 : ℤ) ^ e * (d : ℤ) ∣ ((n : ℤ) - (m : ℤ)) := by
    rw [← hcast]; exact dvd_trans (Int.natAbs_dvd.mpr dvd_rfl) h.dvd
  have hmodd : (m : ℤ) % (d : ℤ) = (n : ℤ) % (d : ℤ) :=
    Int.modEq_iff_dvd.mpr ((dvd_mul_left ((d : ℤ)) ((2 : ℤ) ^ e)).trans hdvd)
  have hDsplit : D = 2 ^ e * (d : ℤ) ∨ D = -(2 ^ e * (d : ℤ)) := by
    rcases Int.natAbs_eq D with h1 | h1
    · exact Or.inl (h1.trans hcast)
    · exact Or.inr (h1.trans (congrArg Neg.neg hcast))
  have he1 : e ≠ 1 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hdodd
    rcases hDsplit with hs | hs <;> rw [ht] at hs <;> push_cast [pow_one] at hs <;> omega
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · subst he0
    simp only [pow_zero, one_mul] at hDsplit
    rcases hDsplit with hs | hs
    · have hd1 : d % 4 = 1 := by rw [hs] at hD; omega
      rw [hs, jacobiSym.quadratic_reciprocity_one_mod_four hd1 hm,
        jacobiSym.quadratic_reciprocity_one_mod_four hd1 hn]
      exact jacobiSym.mod_left' hmodd
    · have hd3 : d % 4 = 3 := by rw [hs] at hD; omega
      rw [hs, case_neg_odd hd3 hm, case_neg_odd hd3 hn]
      exact jacobiSym.mod_left' hmodd
  · have he : 2 ≤ e := by omega
    have h4p : (4 : ℤ) ∣ (2 : ℤ) ^ e :=
      ⟨2 ^ (e - 2), by rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
    have h4z : (4 : ℤ) ∣ ((n : ℤ) - (m : ℤ)) := (h4p.mul_right _).trans hdvd
    have h4 : m % 4 = n % 4 := by obtain ⟨k, hk⟩ := h4z; omega
    have hjd : jacobiSym (d : ℤ) m = jacobiSym (d : ℤ) n :=
      jac_recip_congr hdodd hm hn h4 hmodd
    have hj2 : jacobiSym 2 m ^ e = jacobiSym 2 n ^ e := by
      rcases Nat.lt_or_ge e 3 with he3 | he3
      · have he2 : e = 2 := by omega
        rw [he2, jacobiSym.sq_one (gcd_two_odd hm), jacobiSym.sq_one (gcd_two_odd hn)]
      · have h8p : (8 : ℤ) ∣ (2 : ℤ) ^ e :=
          ⟨2 ^ (e - 3), by rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega⟩
        have h8z : (8 : ℤ) ∣ ((n : ℤ) - (m : ℤ)) := (h8p.mul_right _).trans hdvd
        have h8 : m % 8 = n % 8 := by obtain ⟨k, hk⟩ := h8z; omega
        rw [jacobiSym.at_two hm, jacobiSym.at_two hn, chi8_congr h8]
    rcases hDsplit with hs | hs
    · rw [hs, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left,
        jacobiSym.pow_left, hj2, hjd]
    · rw [hs, jacobiSym.neg _ hm, jacobiSym.neg _ hn, jacobiSym.mul_left, jacobiSym.mul_left,
        jacobiSym.pow_left, jacobiSym.pow_left, hj2, hjd, chi4_congr h4]

/-! ### Odd representatives of residue classes -/

/-- An odd natural number representing the class `x` in `ZMod N` (for odd `N`, or for `x` a
unit and `N` even). -/
private def oddRep (N : ℕ) (x : ZMod N) : ℕ :=
  if x.val % 2 = 1 then x.val else x.val + N

private theorem oddRep_cast {N : ℕ} [NeZero N] (x : ZMod N) :
    ((oddRep N x : ℕ) : ZMod N) = x := by
  unfold oddRep
  by_cases hx : x.val % 2 = 1
  · rw [if_pos hx]; exact ZMod.natCast_rightInverse x
  · rw [if_neg hx]
    push_cast
    rw [ZMod.natCast_self, add_zero]
    exact ZMod.natCast_rightInverse x

private theorem oddRep_odd_of_odd {N : ℕ} (hN : N % 2 = 1) (x : ZMod N) :
    Odd (oddRep N x) := by
  unfold oddRep
  by_cases hx : x.val % 2 = 1
  · rw [if_pos hx]; exact Nat.odd_iff.mpr hx
  · rw [if_neg hx]; exact Nat.odd_iff.mpr (by omega)

private theorem oddRep_odd_unit {N : ℕ} (u : (ZMod N)ˣ) :
    Odd (oddRep N (u : ZMod N)) := by
  have hco : Nat.gcd ((u : ZMod N)).val N = 1 := ZMod.val_coe_unit_coprime u
  unfold oddRep
  by_cases hx : ((u : ZMod N)).val % 2 = 1
  · rw [if_pos hx]; exact Nat.odd_iff.mpr hx
  · rw [if_neg hx]
    have hN : N % 2 = 1 := by
      by_contra hN
      have h2 : (2 : ℕ) ∣ Nat.gcd ((u : ZMod N)).val N := Nat.dvd_gcd (by omega) (by omega)
      rw [hco] at h2
      omega
    exact Nat.odd_iff.mpr (by omega)

private theorem modeq_of_zmod {D : ℤ} {N : ℕ} (hDN : D ∣ (N : ℤ)) {a b : ℕ}
    (h : ((a : ℕ) : ZMod N) = ((b : ℕ) : ZMod N)) : (a : ℤ) ≡ (b : ℤ) [ZMOD D] := by
  have h1 : a ≡ b [MOD N] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  exact Int.modEq_iff_dvd.mpr (hDN.trans h1.dvd)

/-! ### Target 2 -/

private def jacUnit (D : ℤ) (k : ℕ) : ℤˣ :=
  if jacobiSym D k = -1 then -1 else 1

private theorem jacUnit_val {D : ℤ} {k : ℕ}
    (h : jacobiSym D k = 1 ∨ jacobiSym D k = -1) :
    ((jacUnit D k : ℤˣ) : ℤ) = jacobiSym D k := by
  unfold jacUnit
  rcases h with h | h <;> rw [h] <;> norm_num

private theorem jacUnit_mul {D : ℤ} {a b c : ℕ}
    (ha : jacobiSym D a = 1 ∨ jacobiSym D a = -1)
    (hb : jacobiSym D b = 1 ∨ jacobiSym D b = -1)
    (h : jacobiSym D c = jacobiSym D a * jacobiSym D b) :
    jacUnit D c = jacUnit D a * jacUnit D b := by
  unfold jacUnit
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [h, ha, hb] <;> norm_num

theorem ex_1_11 (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) (m n : ℕ)
    (hm : Odd m) (hn : Odd n) (h : (m : ℤ) ≡ (n : ℤ) [ZMOD D]) :
    jacobiSym D m = jacobiSym D n :=
  mod_right_of_discr hD hm hn h

/-- **Exercise 1.12(a).** The map `χ([m]) = (D/m)` is a well-defined homomorphism
`(ℤ/Dℤ)ˣ → {±1}`. -/
theorem ex_1_12_a (D : ℤ) (hD0 : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ χ : (ZMod D.natAbs)ˣ →* ℤˣ,
      ∀ (m : ℕ) (_ : Odd m) (hco : Nat.Coprime m D.natAbs),
        (χ (ZMod.unitOfCoprime m hco) : ℤ) = jacobiSym D m := by
  classical
  haveI : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  have hDN : D ∣ ((D.natAbs : ℕ) : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have hgcd : ∀ u : (ZMod D.natAbs)ˣ,
      Int.gcd D ((oddRep D.natAbs (u : ZMod D.natAbs) : ℕ) : ℤ) = 1 := by
    intro u
    have h1 : Nat.Coprime (oddRep D.natAbs (u : ZMod D.natAbs)) D.natAbs :=
      (ZMod.isUnit_iff_coprime _ _).mp (by rw [oddRep_cast]; exact u.isUnit)
    have h2 : Nat.gcd D.natAbs (oddRep D.natAbs (u : ZMod D.natAbs)) = 1 := h1.symm
    simpa [Int.gcd] using h2
  have hpm : ∀ u : (ZMod D.natAbs)ˣ,
      jacobiSym D (oddRep D.natAbs (u : ZMod D.natAbs)) = 1 ∨
        jacobiSym D (oddRep D.natAbs (u : ZMod D.natAbs)) = -1 :=
    fun u => jacobiSym.eq_one_or_neg_one (hgcd u)
  have hmulhom : ∀ u v : (ZMod D.natAbs)ˣ,
      jacUnit D (oddRep D.natAbs ((u * v : (ZMod D.natAbs)ˣ) : ZMod D.natAbs))
        = jacUnit D (oddRep D.natAbs (u : ZMod D.natAbs))
          * jacUnit D (oddRep D.natAbs (v : ZMod D.natAbs)) := by
    intro u v
    refine jacUnit_mul (hpm u) (hpm v) ?_
    have hodd1 := oddRep_odd_unit u
    have hodd2 := oddRep_odd_unit v
    have hodd3 := oddRep_odd_unit (u * v)
    have hcong : ((oddRep D.natAbs ((u * v : (ZMod D.natAbs)ˣ) : ZMod D.natAbs) : ℕ) : ℤ)
        ≡ ((oddRep D.natAbs (u : ZMod D.natAbs)
            * oddRep D.natAbs (v : ZMod D.natAbs) : ℕ) : ℤ) [ZMOD D] := by
      refine modeq_of_zmod hDN ?_
      push_cast
      rw [oddRep_cast, oddRep_cast, oddRep_cast]
    rw [mod_right_of_discr hD4 hodd3 (hodd1.mul hodd2) hcong,
      jacobiSym.mul_right' D hodd1.pos.ne' hodd2.pos.ne']
  refine ⟨MonoidHom.mk' (fun u : (ZMod D.natAbs)ˣ =>
    jacUnit D (oddRep D.natAbs (u : ZMod D.natAbs))) hmulhom, ?_⟩
  intro m hm hco
  have happ : ((MonoidHom.mk' (fun u : (ZMod D.natAbs)ˣ =>
      jacUnit D (oddRep D.natAbs (u : ZMod D.natAbs))) hmulhom)
      (ZMod.unitOfCoprime m hco))
      = jacUnit D (oddRep D.natAbs
          ((ZMod.unitOfCoprime m hco : (ZMod D.natAbs)ˣ) : ZMod D.natAbs)) := rfl
  rw [happ, jacUnit_val (hpm (ZMod.unitOfCoprime m hco))]
  refine mod_right_of_discr hD4 (oddRep_odd_unit _) hm ?_
  refine modeq_of_zmod hDN ?_
  rw [oddRep_cast, ZMod.coe_unitOfCoprime]

/-! ### Target 3 -/

/-- **Exercise 1.13(a).** Quadratic reciprocity, assuming Lemma 1.14. -/
theorem ex_1_13_a (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym p (q : ℤ) * legendreSym q (p : ℤ) = (-1) ^ (p / 2 * (q / 2)) := by
  -- FLAG (under-hypothesized): FALSE for p = q, since legendreSym p p = 0 while the RHS is +/-1.
  -- Mathlib's legendreSym.quadratic_reciprocity requires the missing hypothesis `p ≠ q`.
  -- See `ex_1_13_a_FALSE` for a proof that the stated form fails, and `ex_1_13_a_fixed`
  -- for the faithful version.
  sorry

/-- Exercise 1.13(a) as stated is false: at `p = q = 3` the left side is `0`. -/
theorem ex_1_13_a_FALSE :
    ¬ (∀ (p q : ℕ) (_ : Fact p.Prime) (_ : Fact q.Prime), p ≠ 2 → q ≠ 2 →
      legendreSym p (q : ℤ) * legendreSym q (p : ℤ) = (-1) ^ (p / 2 * (q / 2))) := by
  intro h
  have h3 := h 3 3 ⟨Nat.prime_three⟩ ⟨Nat.prime_three⟩ (by norm_num) (by norm_num)
  rw [show ((3 : ℕ) : ℤ) = 3 from rfl] at h3
  have hz : legendreSym 3 (3 : ℤ) = 0 := by
    rw [legendreSym.eq_zero_iff]
    decide
  rw [hz, mul_zero] at h3
  norm_num at h3

/-- **Exercise 1.13(a)**, faithful form: quadratic reciprocity for *distinct* odd primes. -/
theorem ex_1_13_a_fixed (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2)
    (hpq : p ≠ q) :
    legendreSym p (q : ℤ) * legendreSym q (p : ℤ) = (-1) ^ (p / 2 * (q / 2)) := by
  rw [mul_comm]
  exact legendreSym.quadratic_reciprocity hp hq hpq

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
  classical
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨Finset.univ.filter (fun x : ZMod n => jacobiSym (-(n : ℤ)) (oddRep n x) = 1), ?_⟩
  intro p hp hodd hpn
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hD4 : (-(n : ℤ)) % 4 = 0 ∨ (-(n : ℤ)) % 4 = 1 := by omega
  have hne0 : ((-(n : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    exact hpn (dvd_neg.mp hd)
  have hrep : jacobiSym (-(n : ℤ)) p = jacobiSym (-(n : ℤ)) (oddRep n (p : ZMod n)) := by
    refine mod_right_of_discr hD4 hodd (oddRep_odd_of_odd (by omega) _) ?_
    refine modeq_of_zmod (D := -(n : ℤ)) ⟨-1, by ring⟩ ?_
    exact (oddRep_cast _).symm
  rw [PrimesX2NY2.Fermat.dvd_sq_add_nsq_iff_isSquare (n : ℤ) p hp hodd hpn,
    ← legendreSym.eq_one_iff p hne0, jacobiSym.legendreSym.to_jacobiSym p (-(n : ℤ)), hrep]

/-- **Exercise 1.15.** The residue classes in `(ℤ/84ℤ)ˣ` with `(−21/p) = 1`
(solving the Reciprocity Step for `n = 21`). -/
private theorem sq_neg21_mod2 : IsSquare ((-21 : ℤ) : ZMod 2) := by decide

private theorem val_two_84 : (2 : ZMod 84).val = 2 := by decide

theorem ex_1_15 :
    ∃ S : Finset (ZMod 84),
      ∀ (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ 21 →
        (IsSquare ((-21 : ℤ) : ZMod p) ↔ (p : ZMod 84) ∈ S) := by
  classical
  refine ⟨Finset.univ.filter (fun x : ZMod 84 => x = 2 ∨ jacobiSym (-21) x.val = 1), ?_⟩
  intro p hp hp21
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hval : ((p : ZMod 84)).val = p % 84 := ZMod.val_natCast 84 p
  rcases eq_or_ne p 2 with rfl | hp2
  · exact ⟨fun _ => Or.inl (by norm_num), fun _ => sq_neg21_mod2⟩
  · have hodd : Odd p := hp.odd_of_ne_two hp2
    have hne0 : ((-21 : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h
      exact hp21 (dvd_neg.mp h)
    have hnot2 : ((p : ZMod 84)) ≠ 2 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [hval, val_two_84] at hv
      obtain ⟨j, hj⟩ := hodd
      omega
    have h84 : 4 * (-21 : ℤ).natAbs = 84 := by norm_num
    have hmr : jacobiSym (-21) p = jacobiSym (-21) (p % 84) := by
      rw [jacobiSym.mod_right (-21 : ℤ) hodd, h84]
    rw [← legendreSym.eq_one_iff p hne0, jacobiSym.legendreSym.to_jacobiSym p (-21), hmr, hval]
    exact ⟨Or.inr, fun h => h.resolve_left hnot2⟩

/-! ## Target 3 : ex_1_8 is FALSE as stated -/

end PrimesX2NY2.PartI.S1
