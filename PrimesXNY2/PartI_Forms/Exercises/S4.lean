/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesXNY2.PartI_Forms.CubicReciprocity
import PrimesXNY2.PartI_Forms.BiquadraticReciprocity

/-!
# Part I, §4 — Exercises (Cox, *Primes of the Form x² + ny²*, §4.D)

Faithful statements for the concrete, self-contained parts of Exercises 4.1–4.29.
Sub-parts that *prove* a spine result, complete a proof, or require machinery not
yet built (Gaussian periods/sums, the quotient residue fields, the full character
constructions) are recorded as `\notready` blueprint nodes only — see ROADMAP.

Exercise 4.6 (that `ℤ[√−3]` is neither a PID nor a UFD) is formalized over
Mathlib's `Zsqrtd (-3)` — precisely the ring we must *not* use for `ℤ[ω]`.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.PartI.S4

open PrimesXNY2.CubicReciprocity PrimesXNY2.BiquadraticReciprocity

/-- **Exercise 4.2(i).** `N(a + bω) = a² − ab + b²`. -/
theorem ex_4_2_a (a b : ℤ) :
    EisensteinInt.norm (⟨a, b⟩ : EisensteinInt) = a ^ 2 - a * b + b ^ 2 := by
  rfl

/-- **Exercise 4.2(ii).** The norm is multiplicative. -/
theorem ex_4_2_b (x y : EisensteinInt) :
    EisensteinInt.norm (x * y) = EisensteinInt.norm x * EisensteinInt.norm y := by
  exact EisensteinInt.norm_mul x y

/-- **Exercise 4.4.** In a PID, for `α ≠ 0` the notions irreducible, prime, prime
ideal `(α)`, and maximal ideal `(α)` coincide. -/
theorem ex_4_4 {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (α : R) (hα : α ≠ 0) :
    [Irreducible α, Prime α, (Ideal.span {α}).IsPrime, (Ideal.span {α}).IsMaximal].TFAE := by
  tfae_have 1 ↔ 2 := UniqueFactorizationMonoid.irreducible_iff_prime
  tfae_have 2 ↔ 3 := (Ideal.span_singleton_prime hα).symm
  tfae_have 3 → 4 := by
    intro h
    haveI := h
    exact IsPrime.to_maximal_ideal (mt Ideal.span_singleton_eq_bot.mp hα)
  tfae_have 4 → 3 := fun h => h.isPrime
  tfae_finish

/-- **Exercise 4.6(a).** The only units of `ℤ[√−3]` are `±1`. -/
theorem ex_4_6_a (x : Zsqrtd (-3)) : IsUnit x ↔ (x = 1 ∨ x = -1) := by
  rw [← Zsqrtd.norm_eq_one_iff]
  constructor
  · intro hn
    obtain ⟨re, im⟩ := x
    have hval : (⟨re, im⟩ : Zsqrtd (-3)).norm = re * re + 3 * (im * im) := by
      simp only [Zsqrtd.norm_def]; ring
    rw [hval] at hn
    have hge : (0 : ℤ) ≤ re * re + 3 * (im * im) := by
      nlinarith [mul_self_nonneg re, mul_self_nonneg im]
    have h1 : re * re + 3 * (im * im) = 1 := by omega
    have him0 : im * im = 0 := by
      have hle : 3 * (im * im) ≤ 1 := by nlinarith [mul_self_nonneg re]
      have hnn : 0 ≤ im * im := mul_self_nonneg im
      omega
    have him : im = 0 := mul_self_eq_zero.mp him0
    have hre : re * re = 1 := by rw [him] at h1; linarith [h1]
    rcases mul_self_eq_one_iff.mp hre with hr | hr
    · left; rw [Zsqrtd.ext_iff]; exact ⟨by simpa using hr, by simpa using him⟩
    · right; rw [Zsqrtd.ext_iff]; exact ⟨by simpa using hr, by simpa using him⟩
  · rintro (rfl | rfl) <;> decide

/-- **Exercise 4.6(b).** `2` is irreducible but not prime in `ℤ[√−3]` (so `ℤ[√−3]`
is not a UFD). -/
theorem ex_4_6_b : Irreducible (2 : Zsqrtd (-3)) ∧ ¬ Prime (2 : Zsqrtd (-3)) := by
  sorry

/-- **Exercise 4.6(c).** The ideal `(2, 1 + √−3)` of `ℤ[√−3]` is not principal (so
`ℤ[√−3]` is not a PID). -/
theorem ex_4_6_c :
    ¬ (Ideal.span {(2 : Zsqrtd (-3)), (⟨1, 1⟩ : Zsqrtd (-3))}).IsPrincipal := by
  sorry

/-- **Exercise 4.9(a).** For a prime `π` not associate to `1 − ω`, `3 ∣ N(π) − 1`. -/
theorem ex_4_9_a (π : EisensteinInt) (hπ : EisensteinInt.IsPrimeE π)
    (h : ¬ EisensteinInt.AssociatedE π (1 - EisensteinInt.omega)) :
    (3 : ℤ) ∣ (EisensteinInt.norm π - 1) := by
  sorry

/-- **Exercise 4.10(a).** The cubic character is multiplicative. -/
theorem ex_4_10_a (π α β : EisensteinInt) :
    EisensteinInt.cubicChar π (α * β)
      = EisensteinInt.cubicChar π α * EisensteinInt.cubicChar π β := by
  sorry

/-- **Exercise 4.10(b).** The cubic character depends only on the residue mod `π`. -/
theorem ex_4_10_b (π α β : EisensteinInt) (hπ : EisensteinInt.IsPrimeE π)
    (h : EisensteinInt.ModEq π α β) :
    EisensteinInt.cubicChar π α = EisensteinInt.cubicChar π β := by
  sorry

/-- **Exercise 4.14.** For `p ≡ 2 (mod 3)`, every `a` is a cube modulo `p`. -/
theorem ex_4_14 (p : ℕ) (hp : p.Prime) (h2 : p % 3 = 2) (a : ℤ) :
    ∃ x : ZMod p, x ^ 3 = (a : ZMod p) := by
  sorry

/-- **Exercise 4.15(d).** `4p = x² + 243y²` iff `p ≡ 1 (mod 3)` and `3` is a cubic
residue mod `p` (Euler). **Deep / GAP** — `notready`. -/
theorem ex_4_15_d (p : ℕ) (hp : p.Prime) :
    (∃ x y : ℤ, 4 * (p : ℤ) = x ^ 2 + 243 * y ^ 2)
      ↔ (p % 3 = 1 ∧ EisensteinInt.IsCubicResidue 3 p) := by
  sorry

/-- **Exercise 4.17.** For a prime `π` of `ℤ[i]` not associate to `1 + i`,
`4 ∣ N(π) − 1`. -/
theorem ex_4_17 (π : GaussianInt) (hπ : Prime π) (h : ¬ Associated π ⟨1, 1⟩) :
    (4 : ℤ) ∣ (Zsqrtd.norm π - 1) := by
  sorry

/-- **Exercise 4.18(b).** The quartic character is multiplicative. -/
theorem ex_4_18_b (π α β : GaussianInt) :
    quarticChar π (α * β) = quarticChar π α * quarticChar π β := by
  sorry

/-- **Exercise 4.24(b).** `2(a² + b²) = (a + b)² + (a − b)²` (the step `2p = (a+b)²
+ (a−b)²` in Dirichlet's proof). -/
theorem ex_4_24_b (a b : ℤ) :
    2 * (a ^ 2 + b ^ 2) = (a + b) ^ 2 + (a - b) ^ 2 := by
  ring

end PrimesXNY2.PartI.S4
