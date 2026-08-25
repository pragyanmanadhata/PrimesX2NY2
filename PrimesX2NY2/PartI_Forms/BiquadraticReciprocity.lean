/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part I, Chapter 4.B - Gaussian integers and biquadratic reciprocity

Cox, *Primes of the Form x² + ny²*, §4.B.

Unlike the Eisenstein case, the relevant ring is Mathlib's `GaussianInt`
(`= Zsqrtd (-1) = ℤ[i]`), which **is** the maximal order, so we reuse its
`CommRing`/`EuclideanDomain` structure (units, primes, `Associated`, `∣`, `norm`)
directly. Only the quartic residue character is hand-rolled.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.BiquadraticReciprocity

/-- The Gaussian integer `i`. -/
def gaussI : GaussianInt := ⟨0, 1⟩

/-- Complex conjugation `a + bi ↦ a − bi` on `ℤ[i]`. -/
def conj (π : GaussianInt) : GaussianInt := ⟨π.re, -π.im⟩

/-- A prime `π` of `ℤ[i]` is **primary** if `π ≡ 1 (mod 2 + 2i)`. -/
def IsPrimaryG (π : GaussianInt) : Prop := (⟨2, 2⟩ : GaussianInt) ∣ (π - 1)

/-- The **quartic residue character** `(α/π)₄ ∈ {1, i, −1, −i}` (Cox (4.20)): the
unique fourth root of unity with `α^{(N(π)−1)/4} ≡ (α/π)₄ (mod π)`. -/
def quarticChar (π α : GaussianInt) : GaussianInt := sorry

/-- `a` is a **biquadratic residue** mod `p` if `x⁴ ≡ a` is solvable in `ℤ/pℤ`. -/
def IsBiquadraticResidue (a : ℤ) (p : ℕ) : Prop := ∃ x : ZMod p, x ^ 4 = (a : ZMod p)

/-- **Proposition 4.18(i).** For `p = 2`, `1 + i` is prime and `2 = i³(1 + i)²`. -/
theorem dle : (-1 : ℤ) ≤ 0 := by norm_num

/-- An element of `ℤ[i]` whose norm is a rational prime is prime. -/
theorem prime_of_norm_prime {π : GaussianInt} {q : ℕ} (hq : q.Prime)
    (h : Zsqrtd.norm π = (q : ℤ)) : Prime π := by
  rw [← irreducible_iff_prime]
  constructor
  · intro hu
    have h1 := (Zsqrtd.norm_eq_one_iff' dle π).mpr hu
    rw [h] at h1
    have : q = 1 := by exact_mod_cast h1
    exact hq.one_lt.ne' this
  · intro a b hab
    have hn : Zsqrtd.norm a * Zsqrtd.norm b = (q : ℤ) := by
      rw [← Zsqrtd.norm_mul, ← hab, h]
    have ha := Zsqrtd.norm_nonneg dle a
    have hb := Zsqrtd.norm_nonneg dle b
    have hA : (Zsqrtd.norm a).toNat * (Zsqrtd.norm b).toNat = q := by
      have := congrArg Int.toNat hn
      rwa [Int.toNat_mul ha hb, Int.toNat_natCast] at this
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq (Zsqrtd.norm a).toNat
      ⟨(Zsqrtd.norm b).toNat, hA.symm⟩) with h1 | h1
    · left
      refine (Zsqrtd.norm_eq_one_iff' dle a).mp ?_
      omega
    · right
      refine (Zsqrtd.norm_eq_one_iff' dle b).mp ?_
      have hqpos := hq.pos
      have : (Zsqrtd.norm b).toNat = 1 := by
        rw [h1] at hA
        have : q * (Zsqrtd.norm b).toNat = q * 1 := by omega
        exact Nat.eq_of_mul_eq_mul_left hqpos this
      omega

theorem norm_one_one : Zsqrtd.norm (⟨1, 1⟩ : GaussianInt) = 2 := by decide

/-- **Proposition 4.18(i).** For `p = 2`, `1 + i` is prime and `2 = i³(1 + i)²`. -/
theorem prop_4_18_ramified :
    Prime (⟨1, 1⟩ : GaussianInt) ∧ (2 : GaussianInt) = gaussI ^ 3 * (⟨1, 1⟩ : GaussianInt) ^ 2 := by
  refine ⟨prime_of_norm_prime Nat.prime_two (by rw [norm_one_one]; norm_num), ?_⟩
  decide

/-- **Proposition 4.18(ii).** For `p ≡ 1 (mod 4)`, `p = π·π̄` splits into nonassociate
primes. -/
theorem prop_4_18_split (p : ℕ) (hp : p.Prime) (h1 : p % 4 = 1) :
    ∃ π : GaussianInt, Prime π ∧ (p : GaussianInt) = π * conj π
      ∧ ¬ Associated π (conj π) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hple := hp.two_le
  have hp5 : 5 ≤ p := by omega
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have hp2 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hab
  have hprod : ((p : ℕ) : GaussianInt) = (⟨a, b⟩ : GaussianInt) * conj ⟨a, b⟩ := by
    rw [Zsqrtd.ext_iff]
    refine ⟨?_, ?_⟩
    · simp only [Zsqrtd.re_mul, conj, Zsqrtd.re_natCast]
      linear_combination -hp2
    · simp only [Zsqrtd.im_mul, conj, Zsqrtd.im_natCast]
      ring
  -- a and b are nonzero, since p is not a perfect square
  have hsq : ∀ c : ℕ, p = c * c → False := by
    intro c hc
    have h2 := hp.two_le
    rcases Nat.Prime.eq_one_or_self_of_dvd hp c ⟨c, hc⟩ with h | h
    · rw [h] at hc; omega
    · rw [h] at hc; nlinarith [h2, hc]
  have hane : a ≠ 0 := by
    intro hz; rw [hz] at hp2
    exact hsq b (by exact_mod_cast (by linear_combination hp2 : (b:ℤ) * (b:ℤ) = (p:ℤ)).symm)
  have hbne : b ≠ 0 := by
    intro hz; rw [hz] at hp2
    exact hsq a (by exact_mod_cast (by linear_combination hp2 : (a:ℤ) * (a:ℤ) = (p:ℤ)).symm)
  refine ⟨⟨a, b⟩, ?_, hprod, ?_⟩
  · refine prime_of_norm_prime hp ?_
    rw [Zsqrtd.norm_def]
    linear_combination hp2
  · rintro ⟨u, hu⟩
    -- π² · u = π · (π · u) = π · conj π = p
    have key : ((⟨a, b⟩ : GaussianInt) * ⟨a, b⟩) * (u : GaussianInt) = (p : GaussianInt) := by
      rw [mul_assoc, hu, ← hprod]
    -- hence π² = p · u⁻¹, so p divides both components of π²
    have hinv : ((u : GaussianInt)) * ((↑u⁻¹ : GaussianInt)) = 1 := u.mul_inv
    have hsq2 : (⟨a, b⟩ : GaussianInt) * ⟨a, b⟩
        = (p : GaussianInt) * ((↑u⁻¹ : GaussianInt)) := by
      rw [← key, mul_assoc, hinv, mul_one]
    have him2 := congrArg Zsqrtd.im hsq2
    simp only [Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast] at him2
    -- p ∣ 2ab
    have hdvd : (p : ℤ) ∣ 2 * ((a : ℤ) * (b : ℤ)) :=
      ⟨((↑u⁻¹ : GaussianInt)).im, by linarith [him2]⟩
    have hdvdN : p ∣ 2 * (a * b) := by exact_mod_cast hdvd
    -- p is odd, so p ∣ a or p ∣ b
    have hp2' : p ≠ 2 := by omega
    have hpab : p ∣ a * b := by
      rcases (Nat.Prime.dvd_mul hp).mp hdvdN with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      · exact h
    -- but 0 < a, b < p
    have halt : a < p := by nlinarith [hp2, hab, Nat.one_le_iff_ne_zero.mpr hane,
      Nat.one_le_iff_ne_zero.mpr hbne]
    have hblt : b < p := by nlinarith [hp2, hab, Nat.one_le_iff_ne_zero.mpr hane,
      Nat.one_le_iff_ne_zero.mpr hbne]
    rcases (Nat.Prime.dvd_mul hp).mp hpab with h | h
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hane) h) (by omega)
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hbne) h) (by omega)

/-- **Proposition 4.18(iii).** For `p ≡ 3 (mod 4)`, `p` remains prime in `ℤ[i]`. -/
theorem prop_4_18_inert (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) :
    Prime (p : GaussianInt) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr h3

/-- **(4.19)** (Fermat's little theorem in `ℤ[i]`). If `π ∤ α` then
`α^{N(π)−1} ≡ 1 (mod π)`. -/
theorem eq_4_19 (π α : GaussianInt) (hπ : Prime π) (h : ¬ π ∣ α) :
    π ∣ (α ^ (Zsqrtd.norm π - 1).toNat - 1) := by
  sorry

/-- **Quartic character, defining property** (Cox (4.20)). -/
theorem quarticChar_spec (π α : GaussianInt) (hπ : Prime π)
    (h : ¬ Associated π ⟨1, 1⟩) (hα : ¬ π ∣ α) :
    π ∣ (α ^ ((Zsqrtd.norm π - 1) / 4).toNat - quarticChar π α)
      ∧ (quarticChar π α = 1 ∨ quarticChar π α = -1
          ∨ quarticChar π α = gaussI ∨ quarticChar π α = -gaussI) := by
  sorry

/-- **Quartic character is multiplicative** (Cox (4.20)). -/
theorem quarticChar_mul (π α β : GaussianInt) :
    quarticChar π (α * β) = quarticChar π α * quarticChar π β := by
  sorry

/-- **Quartic residue criterion.** `(α/π)₄ = 1` iff `x⁴ ≡ α (mod π)` is solvable. -/
theorem quarticChar_eq_one_iff (π α : GaussianInt) (hπ : Prime π) (hα : ¬ π ∣ α) :
    quarticChar π α = 1 ↔ ∃ x : GaussianInt, π ∣ (x ^ 4 - α) := by
  sorry

/-- **Theorem 4.21** (Biquadratic Reciprocity). For distinct primary primes `π, θ`,
`(π/θ)₄ = (θ/π)₄ · (−1)^{(N(π)−1)(N(θ)−1)/16}`. **Deep / GAP** - `notready`, never an
axiom. -/
theorem thm_4_21 (π θ : GaussianInt) (hπ : Prime π) (hθ : Prime θ)
    (hpπ : IsPrimaryG π) (hpθ : IsPrimaryG θ) (hne : ¬ Associated π θ) :
    quarticChar θ π
      = quarticChar π θ
        * (-1 : GaussianInt) ^ ((Zsqrtd.norm π - 1) * (Zsqrtd.norm θ - 1) / 16).toNat := by
  sorry

/-- **(4.22)** Supplementary laws. For primary `π = a + bi`,
`(i/π)₄ = i^{−(a−1)/2}` and `((1+i)/π)₄ = i^{(a−b−1−b²)/4}`. **Deep / GAP** -
`notready`. -/
theorem supplementary_4_22 (a b : ℤ) (hpr : IsPrimaryG ⟨a, b⟩) :
    quarticChar ⟨a, b⟩ gaussI = gaussI ^ (((-(a - 1)) / 2 % 4).toNat)
      ∧ quarticChar ⟨a, b⟩ ⟨1, 1⟩ = gaussI ^ (((a - b - 1 - b ^ 2) / 4 % 4).toNat) := by
  sorry

/-- **Theorem 4.23(i).** For primary `π = a + bi`, `(2/π)₄ = i^{ab/2}`. **Deep /
GAP** - `notready`. -/
theorem thm_4_23_i (a b : ℤ) (hpr : IsPrimaryG ⟨a, b⟩) :
    quarticChar ⟨a, b⟩ (2 : GaussianInt) = gaussI ^ ((a * b / 2 % 4).toNat) := by
  sorry

/-- **Theorem 4.23(ii)** (Euler's conjecture). `p = x² + 64y²` iff `p ≡ 1 (mod 4)`
and `2` is a biquadratic residue mod `p`. **Deep / GAP** - `notready`, never an
axiom. -/
theorem thm_4_23_ii (p : ℕ) (hp : p.Prime) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 64 * y ^ 2)
      ↔ (p % 4 = 1 ∧ IsBiquadraticResidue 2 p) := by
  sorry

end PrimesX2NY2.BiquadraticReciprocity
