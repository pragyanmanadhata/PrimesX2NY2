/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part I, §1 — Exercises

Faithful `sorry`-bodied statements of the exercises of Cox §1 (Exercises 1.1–1.16).
Cited by number only; statements are paraphrased.

A handful of sub-parts (1.12(b), 1.12(c), 1.16) are recorded in the blueprint as
`\notready` flagged nodes rather than Lean signatures — see the FLAG LIST in the
project report — because a faithful self-contained statement requires fixing a
specific homomorphism / subgroup that the exercise only pins down implicitly.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.PartI.S1

/-- Forward difference operator `Δg(x) = g(x+1) − g(x)`, used in Exercise 1.2. -/
def diff (g : ℤ → ℤ) : ℤ → ℤ := fun x => g (x + 1) - g x

/-- **Exercise 1.1(a).** The identity `(1.3)`. -/
theorem ex_1_1_a (x y z w : ℤ) :
    (x ^ 2 + y ^ 2) * (z ^ 2 + w ^ 2) = (x * z - y * w) ^ 2 + (x * w + y * z) ^ 2 := by
  sorry

/-- **Exercise 1.1(b).** Euler's generalization to `(ax²+cy²)(az²+cw²)`. -/
theorem ex_1_1_b (a c x y z w : ℤ) :
    (a * x ^ 2 + c * y ^ 2) * (a * z ^ 2 + c * w ^ 2)
      = (a * x * z - c * y * w) ^ 2 + a * c * (x * w + y * z) ^ 2 := by
  sorry

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

/-- **Exercise 1.5.** If `p = 3k+1` is prime then `(−3/p) = 1`. -/
theorem ex_1_5 (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : p = 3 * k + 1) :
    IsSquare ((-3 : ℤ) : ZMod p) := by
  sorry

/-- **Exercise 1.6.** Prove Lemma 1.7. -/
theorem ex_1_6 (n : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpn : ¬ (p : ℤ) ∣ n) :
    (∃ x y : ℤ, IsCoprime x y ∧ (p : ℤ) ∣ x ^ 2 + n * y ^ 2)
      ↔ IsSquare ((-n : ℤ) : ZMod p) := by
  sorry

/-- **Exercise 1.7.** Quadratic reciprocity in the form `(1.12)`:
`(p*/q) = (q/p)` with `p* = (−1)^((p−1)/2)·p`. -/
theorem ex_1_7 (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q ((-1) ^ ((p - 1) / 2) * (p : ℤ)) = legendreSym p (q : ℤ) := by
  sorry

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
  sorry

/-- **Exercise 1.9(b).** The cases `x²+y²`, `x²+2y²` correspond to the
supplementary laws for `(−1/p)` and `(2/p)`. -/
theorem ex_1_9_b (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = (-1) ^ ((p - 1) / 2) ∧
      legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  sorry

/-- **Exercise 1.10(a).** The Jacobi symbol depends only on the numerator mod the
denominator. -/
theorem ex_1_10_a (M N : ℤ) (m : ℕ) (h : M ≡ N [ZMOD m]) :
    jacobiSym M m = jacobiSym N m := by
  sorry

/-- **Exercise 1.10(b).** Multiplicativity of the Jacobi symbol `(1.15)`. -/
theorem ex_1_10_b (M N : ℤ) (m n : ℕ) :
    jacobiSym (M * N) m = jacobiSym M m * jacobiSym N m ∧
      jacobiSym M (m * n) = jacobiSym M m * jacobiSym M n := by
  sorry

/-- **Exercise 1.10(c).** The supplementary laws for the Jacobi symbol `(1.16)`. -/
theorem ex_1_10_c (m : ℕ) (hm : Odd m) :
    jacobiSym (-1) m = (-1) ^ ((m - 1) / 2) ∧
      jacobiSym 2 m = (-1) ^ ((m ^ 2 - 1) / 8) := by
  sorry

/-- **Exercise 1.10(d).** If `M` is a quadratic residue mod `m` (and prime to it)
then `(M/m) = 1` (the converse fails). -/
theorem ex_1_10_d (M : ℤ) (m : ℕ) (hm : Odd m) (hco : IsCoprime M (m : ℤ))
    (h : IsSquare (M : ZMod m)) : jacobiSym M m = 1 := by
  sorry

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
  sorry

/-- **Exercise 1.13(b).** The supplementary laws, assuming Lemma 1.14. -/
theorem ex_1_13_b (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = (-1) ^ ((p - 1) / 2) ∧
      legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  sorry

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

end PrimesXNY2.PartI.S1
