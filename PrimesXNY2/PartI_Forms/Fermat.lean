/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part I, §1 — Fermat, Euler, and Quadratic Reciprocity

Cox, *Primes of the Form x² + ny²*, §1.

The first representation theorems, Euler's Descent and Reciprocity Steps, the
key Lemmas 1.4 and 1.7, quadratic reciprocity (Euler's form and the Legendre
form), and the character-theoretic Lemma 1.14 / Corollary 1.19 that solve the
Reciprocity Step by congruences.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.Fermat

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

/-- **(1.3)** Brahmagupta–Fibonacci identity expressing a product of sums of two
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
  sorry

/-- **Lemma 1.4.** If `N` is a sum of two relatively prime squares and the prime
`q = x²+y²` divides `N`, then `N/q` is again a sum of two relatively prime
squares. This is the inductive heart of the Descent Step. -/
theorem descent_lemma (N a b x y : ℤ) (q : ℕ) (hq : q.Prime)
    (hN : N = a ^ 2 + b ^ 2) (hcop : IsCoprime a b)
    (hqf : (q : ℤ) = x ^ 2 + y ^ 2) (hdvd : (q : ℤ) ∣ N) :
    ∃ c d : ℤ, N = (q : ℤ) * (c ^ 2 + d ^ 2) ∧ IsCoprime c d := by
  sorry

/-- **Lemma 1.7.** For nonzero `n` and an odd prime `p ∤ n`, `p` divides a
primitively represented value `x²+ny²` iff `−n` is a quadratic residue mod `p`,
i.e. `(−n/p) = 1`. -/
theorem dvd_sq_add_nsq_iff_isSquare (n : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hpn : ¬ (p : ℤ) ∣ n) :
    (∃ x y : ℤ, IsCoprime x y ∧ (p : ℤ) ∣ x ^ 2 + n * y ^ 2)
      ↔ IsSquare ((-n : ℤ) : ZMod p) := by
  sorry

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
Cox's statement — "distinct odd primes"; without it the claim is false at `p = q`,
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

UNVERIFIED proof: Mathlib provides `legendreSym.at_two : (2/p) = χ₈ p` (a value by
`p mod 8`), but no closed form `(−1)^((p²−1)/8)`. Bridging needs a nonlinear
`Nat`-division parity argument on `(p²−1)/8` — a tracked C-bucket target, not a
leaf. -/
theorem legendreSym_second_supplement (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  sorry

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

end PrimesXNY2.Fermat
