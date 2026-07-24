/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part I, §1 - Fermat, Euler, and Quadratic Reciprocity

Cox, *Primes of the Form x² + ny²*, §1.

The first representation theorems, Euler's Descent and Reciprocity Steps, the
key Lemmas 1.4 and 1.7, quadratic reciprocity (Euler's form and the Legendre
form), and the character-theoretic Lemma 1.14 / Corollary 1.19 that solve the
Reciprocity Step by congruences.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.Fermat

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

/-- Primes represented by `x² + 2y²` (Cox, §1). For an odd prime `p`, solvable
iff `p ≡ 1, 3 (mod 8)`. -/
theorem prime_sq_add_two_sq (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 2 * y ^ 2) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  sorry

/-- Primes represented by `x² + 3y²` (Cox, §1). For a prime `p > 3`, solvable iff
`p ≡ 1 (mod 3)`. -/
theorem prime_sq_add_three_sq (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 3 * y ^ 2) ↔ p % 3 = 1 := by
  sorry

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
squares. This is the inductive heart of the Descent Step. -/
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

Proof: rewrite `(2/p) = χ₈ p` via `legendreSym.at_two`, then bridge to the closed
form `(−1)^((p²−1)/8)` by a `Nat`-division parity argument on `(p²−1)/8`,
reducing to the residue of `p` modulo 16. -/
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
