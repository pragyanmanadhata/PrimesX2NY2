/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part I, Chapter 4.A - Eisenstein integers and cubic reciprocity

Cox, *Primes of the Form x² + ny²*, §4.A.

Mathlib has no Eisenstein integers, so we define a **lightweight** `EisensteinInt`
structure `{a + bω}` (`ω = e^{2πi/3}`, a root of `x² + x + 1`) with explicit
arithmetic and norm. We deliberately do **not** use `Zsqrtd (-3)`: that is the
order `ℤ[√−3]` of conductor `2`, *not* the maximal order `ℤ[ω] = ℤ[(−1+√−3)/2]`
(see Exercise 4.6, which shows `ℤ[√−3]` is neither a PID nor a UFD).

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.CubicReciprocity

/-- An **Eisenstein integer** `a + bω`, `ω = e^{2πi/3}`. -/
structure EisensteinInt where
  /-- Rational-integer part. -/
  a : ℤ
  /-- Coefficient of `ω`. -/
  b : ℤ
deriving DecidableEq

namespace EisensteinInt

instance : Zero EisensteinInt := ⟨⟨0, 0⟩⟩
instance : One EisensteinInt := ⟨⟨1, 0⟩⟩
instance : Add EisensteinInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg EisensteinInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub EisensteinInt := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
/-- Multiplication using `ω² = −1 − ω`:
`(a+bω)(c+dω) = (ac − bd) + (ad + bc − bd)ω`. -/
instance : Mul EisensteinInt :=
  ⟨fun x y => ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a - x.b * y.b⟩⟩
instance : Dvd EisensteinInt := ⟨fun π α => ∃ γ : EisensteinInt, α = π * γ⟩

/-- The integer `n` as an Eisenstein integer. -/
def ofInt (n : ℤ) : EisensteinInt := ⟨n, 0⟩

/-- `ω = e^{2πi/3}`. -/
def omega : EisensteinInt := ⟨0, 1⟩

/-- The **norm** `N(a + bω) = a² − ab + b²`. -/
def norm (x : EisensteinInt) : ℤ := x.a ^ 2 - x.a * x.b + x.b ^ 2

/-- Complex conjugation: `conj(a + bω) = (a − b) − bω`. -/
def conj (x : EisensteinInt) : EisensteinInt := ⟨x.a - x.b, -x.b⟩

/-- The `n`-th power (our `EisensteinInt` is not registered as a `Monoid`). -/
def power (x : EisensteinInt) : ℕ → EisensteinInt
  | 0 => 1
  | n + 1 => x * power x n

/-- A **unit**: an element with a multiplicative inverse. -/
def IsUnitE (x : EisensteinInt) : Prop := ∃ y : EisensteinInt, x * y = 1

/-- `x` and `y` are **associates**: `y = u·x` for a unit `u`. -/
def AssociatedE (x y : EisensteinInt) : Prop := ∃ u : EisensteinInt, IsUnitE u ∧ y = u * x

/-- An **irreducible**: a non-unit not expressible as a product of two non-units. -/
def IsIrreducibleE (x : EisensteinInt) : Prop :=
  ¬ IsUnitE x ∧ ∀ y z : EisensteinInt, x = y * z → IsUnitE y ∨ IsUnitE z

/-- A **prime**: a nonzero non-unit `π` with `π ∣ αβ → π ∣ α ∨ π ∣ β`. -/
def IsPrimeE (π : EisensteinInt) : Prop :=
  ¬ IsUnitE π ∧ π ≠ 0 ∧ ∀ α β : EisensteinInt, π ∣ α * β → π ∣ α ∨ π ∣ β

/-- `α ≡ β (mod π)`. -/
def ModEq (π α β : EisensteinInt) : Prop := π ∣ (α - β)

/-- A prime `π` is **primary** if `π ≡ ±1 (mod 3)`. (This is Cox's normalization;
Ireland-Rosen use `π ≡ −1 (mod 3)`, which since `(−1/π)₃ = 1` does not affect cubic
reciprocity. See the report's FLAG LIST.) -/
def IsPrimary (π : EisensteinInt) : Prop :=
  ModEq (ofInt 3) π 1 ∨ ModEq (ofInt 3) π (-1)

/-- The **cubic residue character** `(α/π)₃ ∈ {1, ω, ω²}` (Cox (4.10)): the unique
cube root of unity with `α^{(N(π)−1)/3} ≡ (α/π)₃ (mod π)`. -/
def cubicChar (π α : EisensteinInt) : EisensteinInt := sorry

/-- `2` is a **cubic residue** mod `p` if `x³ ≡ a` is solvable in `ℤ/pℤ`. -/
def IsCubicResidue (a : ℤ) (p : ℕ) : Prop := ∃ x : ZMod p, x ^ 3 = (a : ZMod p)

/-- **Norm is multiplicative.** (Cox §4.A.) -/
theorem norm_mul (x y : EisensteinInt) : norm (x * y) = norm x * norm y := by
  have ha : (x * y).a = x.a * y.a - x.b * y.b := rfl
  have hb : (x * y).b = x.a * y.b + x.b * y.a - x.b * y.b := rfl
  simp only [norm, ha, hb]
  ring

/-- Componentwise formula for multiplication. -/
theorem mul_def (x y : EisensteinInt) :
    x * y = ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a - x.b * y.b⟩ := rfl

theorem add_def (x y : EisensteinInt) : x + y = ⟨x.a + y.a, x.b + y.b⟩ := rfl

theorem sub_def (x y : EisensteinInt) : x - y = ⟨x.a - y.a, x.b - y.b⟩ := rfl

/-- Componentwise formula for the norm. -/
theorem norm_def (x : EisensteinInt) : norm x = x.a ^ 2 - x.a * x.b + x.b ^ 2 := rfl

theorem mul_comm' (x y : EisensteinInt) : x * y = y * x := by
  rw [mul_def, mul_def]; simp only [EisensteinInt.mk.injEq]; constructor <;> ring

theorem mul_one' (x : EisensteinInt) : x * 1 = x := by
  rw [mul_def]
  have e1 : (1 : EisensteinInt).a = 1 := rfl
  have e2 : (1 : EisensteinInt).b = 0 := rfl
  rw [e1, e2]
  obtain ⟨p, q⟩ := x
  simp only [EisensteinInt.mk.injEq]
  constructor <;> ring

/-- The norm is nonnegative: `4·N(a+bω) = (2a−b)² + 3b²`. -/
theorem norm_nonneg (x : EisensteinInt) : 0 ≤ norm x := by
  rw [norm_def]; nlinarith [sq_nonneg (2 * x.a - x.b), sq_nonneg x.b]

theorem eq_zero_of_norm_eq_zero (x : EisensteinInt) (h : norm x = 0) : x = 0 := by
  obtain ⟨p, q⟩ := x
  rw [norm_def] at h
  simp only [] at h
  have hq : q = 0 := by nlinarith [sq_nonneg (2 * p - q), sq_nonneg q]
  have hp : p = 0 := by rw [hq] at h; nlinarith [h]
  subst hp; subst hq; rfl

theorem norm_ne_zero (x : EisensteinInt) (h : x ≠ 0) : norm x ≠ 0 :=
  fun hz => h (eq_zero_of_norm_eq_zero x hz)

theorem norm_one : norm (1 : EisensteinInt) = 1 := by decide

theorem norm_one_sub_omega : norm (1 - omega) = 3 := by decide

theorem mul_conj_self (x : EisensteinInt) : x * ⟨x.a - x.b, -x.b⟩ = ⟨norm x, 0⟩ := by
  rw [mul_def, norm_def]
  simp only [EisensteinInt.mk.injEq]
  constructor <;> ring

/-- `3 ∣ a² − ab + b²` exactly when `3 ∣ a + b`. -/
theorem norm_zmod3 (u v : ℤ) :
    ((3:ℤ) ∣ (u ^ 2 - u * v + v ^ 2)) ↔ ((3:ℤ) ∣ (u + v)) := by
  have key : ∀ A B : ZMod 3, (A ^ 2 - A * B + B ^ 2 = 0 ↔ A + B = 0) := by decide
  constructor
  · intro hdvd
    have h1 : ((u ^ 2 - u * v + v ^ 2 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hdvd)
    push_cast at h1
    have h2 := (key (u : ZMod 3) (v : ZMod 3)).mp h1
    have h3 : ((u + v : ℤ) : ZMod 3) = 0 := by push_cast; exact h2
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h3
  · intro hdvd
    have h1 : ((u + v : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hdvd)
    push_cast at h1
    have h2 := (key (u : ZMod 3) (v : ZMod 3)).mpr h1
    have h3 : ((u ^ 2 - u * v + v ^ 2 : ℤ) : ZMod 3) = 0 := by push_cast; exact h2
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h3

/-- A norm not divisible by `3` is congruent to `1` mod `3`. -/
theorem norm_mod3_cases (u v : ℤ) (h : ¬ ((3:ℤ) ∣ (u ^ 2 - u * v + v ^ 2))) :
    (3:ℤ) ∣ (u ^ 2 - u * v + v ^ 2 - 1) := by
  have key : ∀ A B : ZMod 3,
      ¬ (A ^ 2 - A * B + B ^ 2 = 0) → A ^ 2 - A * B + B ^ 2 - 1 = 0 := by decide
  have h1 : ¬ (((u ^ 2 - u * v + v ^ 2 : ℤ) : ZMod 3) = 0) := by
    intro hc
    exact h (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hc)
  push_cast at h1
  have h2 := key (u : ZMod 3) (v : ZMod 3) h1
  have h3 : ((u ^ 2 - u * v + v ^ 2 - 1 : ℤ) : ZMod 3) = 0 := by push_cast; exact h2
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h3

/-- Conjugation preserves the norm. -/
theorem norm_conj (x : EisensteinInt) :
    EisensteinInt.norm ⟨x.a - x.b, -x.b⟩ = EisensteinInt.norm x := by
  rw [norm_def, norm_def]; ring

/-- Nearest-integer rounding: `|2(A − n·m)| ≤ n` for a suitable `m`. -/
theorem round_bound (A n : ℤ) (hn : 0 < n) :
    ∃ m : ℤ, -n ≤ 2 * (A - n * m) ∧ 2 * (A - n * m) ≤ n := by
  have h2n : (0:ℤ) < 2 * n := by omega
  refine ⟨(2 * A + n) / (2 * n), ?_, ?_⟩ <;>
    · have hdm := Int.ediv_add_emod (2 * A + n) (2 * n)
      have hr0 : 0 ≤ (2 * A + n) % (2 * n) := Int.emod_nonneg _ (by omega)
      have hr1 : (2 * A + n) % (2 * n) < 2 * n := Int.emod_lt_of_pos _ h2n
      nlinarith [hdm, hr0, hr1]

/-- **Proposition 4.3.** `ℤ[ω]` is a Euclidean ring: division with smaller-norm
remainder. -/
theorem prop_4_3 (α β : EisensteinInt) (hβ : β ≠ 0) :
    ∃ γ δ : EisensteinInt, α = β * γ + δ ∧ norm δ < norm β := by
  have hnpos : 0 < EisensteinInt.norm β :=
    lt_of_le_of_ne (norm_nonneg β) (Ne.symm (norm_ne_zero β hβ))
  obtain ⟨m, hm1, hm2⟩ := round_bound (α * ⟨β.a - β.b, -β.b⟩).a (EisensteinInt.norm β) hnpos
  obtain ⟨k, hk1, hk2⟩ := round_bound (α * ⟨β.a - β.b, -β.b⟩).b (EisensteinInt.norm β) hnpos
  refine ⟨⟨m, k⟩, α - β * ⟨m, k⟩, ?_, ?_⟩
  · rw [add_def, sub_def]
    obtain ⟨pa, pb⟩ := α
    simp only [EisensteinInt.mk.injEq]
    constructor <;> ring
  · set n : ℤ := EisensteinInt.norm β with hn
    set u : ℤ := (α * ⟨β.a - β.b, -β.b⟩).a - n * m with hu
    set v : ℤ := (α * ⟨β.a - β.b, -β.b⟩).b - n * k with hv
    have hprod : (α - β * ⟨m, k⟩) * ⟨β.a - β.b, -β.b⟩ = ⟨u, v⟩ := by
      have hnb : n = β.a ^ 2 - β.a * β.b + β.b ^ 2 := by rw [hn, norm_def]
      rw [hu, hv, mul_def, mul_def, sub_def, mul_def]
      simp only [EisensteinInt.mk.injEq]
      constructor <;> · rw [hnb]; ring
    have hnorms := congrArg EisensteinInt.norm hprod
    have hRHS : EisensteinInt.norm (⟨u, v⟩ : EisensteinInt) = u ^ 2 - u * v + v ^ 2 := rfl
    rw [EisensteinInt.norm_mul, norm_conj, hRHS] at hnorms
    have hu2 : (2 * u) ^ 2 ≤ n ^ 2 := by nlinarith [hm1, hm2]
    have hv2 : (2 * v) ^ 2 ≤ n ^ 2 := by nlinarith [hk1, hk2]
    have huvl : -(n ^ 2) ≤ 4 * (u * v) := by nlinarith [sq_nonneg (2 * u + 2 * v), hu2, hv2]
    have h4 : 4 * (EisensteinInt.norm (α - β * ⟨m, k⟩) * n) ≤ 3 * (n * n) := by
      nlinarith [hnorms, hu2, hv2, huvl]
    have hn2 : 0 < n * n := mul_pos hnpos hnpos
    have hlt : EisensteinInt.norm (α - β * ⟨m, k⟩) * n < n * n := by linarith [h4, hn2]
    exact lt_of_mul_lt_mul_right hlt (le_of_lt hnpos)

/-- **Corollary 4.4.** `ℤ[ω]` is a PID and a UFD; in particular irreducible
elements coincide with primes. -/
theorem cor_4_4 (x : EisensteinInt) (hx : x ≠ 0) : IsIrreducibleE x ↔ IsPrimeE x := by
  sorry

/-- **Lemma 4.5(i).** `x` is a unit iff `N(x) = 1`. -/
theorem lemma_4_5_i (x : EisensteinInt) : IsUnitE x ↔ norm x = 1 := by
  constructor
  · rintro ⟨y, hy⟩
    have h : norm x * norm y = 1 := by rw [← EisensteinInt.norm_mul, hy, norm_one]
    have hd : norm x ∣ 1 := ⟨norm y, h.symm⟩
    have hle : norm x ≤ 1 := Int.le_of_dvd one_pos hd
    have hx := norm_nonneg x
    rcases (by omega : norm x = 0 ∨ norm x = 1) with h0 | h1
    · rw [h0, zero_mul] at h; omega
    · exact h1
  · intro h
    refine ⟨⟨x.a - x.b, -x.b⟩, ?_⟩
    rw [mul_conj_self, h]
    rfl

/-- **Lemma 4.5(ii).** The units of `ℤ[ω]` are `{±1, ±ω, ±ω²}`. -/
theorem lemma_4_5_ii (x : EisensteinInt) :
    IsUnitE x ↔ x = 1 ∨ x = -1 ∨ x = omega ∨ x = -omega
      ∨ x = omega * omega ∨ x = -(omega * omega) := by
  rw [lemma_4_5_i, norm_def]
  have e2 : (-1 : EisensteinInt) = ⟨-1, 0⟩ := rfl
  have e4 : (-omega : EisensteinInt) = ⟨0, -1⟩ := rfl
  have e6 : (-(omega * omega) : EisensteinInt) = ⟨1, 1⟩ := rfl
  have e5 : (omega * omega : EisensteinInt) = ⟨-1, -1⟩ := rfl
  have e1 : (1 : EisensteinInt) = ⟨1, 0⟩ := rfl
  have e3 : (omega : EisensteinInt) = ⟨0, 1⟩ := rfl
  rw [e2, e4, e6, e5, e1, e3]
  obtain ⟨p, q⟩ := x
  simp only [EisensteinInt.mk.injEq]
  constructor
  · intro h
    have h4 : (2 * p - q) ^ 2 + 3 * q ^ 2 = 4 := by nlinarith [h]
    have hq1 : q ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * p - q)]
    have hqa : -1 ≤ q := by nlinarith [hq1]
    have hqb : q ≤ 1 := by nlinarith [hq1]
    have hpq : (2 * p - q) ^ 2 ≤ 4 := by nlinarith [sq_nonneg q]
    have hpa : -1 ≤ p := by nlinarith [hpq, hqa, hqb]
    have hpb : p ≤ 1 := by nlinarith [hpq, hqa, hqb]
    interval_cases p <;> interval_cases q <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num

/-- **Lemma 4.6.** If `N(α)` is a rational prime then `α` is prime in `ℤ[ω]`. -/
theorem lemma_4_6 (α : EisensteinInt) (p : ℕ) (hp : p.Prime) (h : norm α = (p : ℤ)) :
    IsPrimeE α := by
  sorry

/-- **Proposition 4.7(i).** For `p = 3`, `1 − ω` is prime and `3 = −ω²(1 − ω)²`. -/
theorem prop_4_7_ramified :
    IsPrimeE (1 - omega) ∧ ofInt 3 = -(omega * omega) * (1 - omega) * (1 - omega) := by
  sorry

/-- **Proposition 4.7(ii).** For `p ≡ 1 (mod 3)`, `p = π·π̄` splits into nonassociate
primes. -/
theorem prop_4_7_split (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ π : EisensteinInt, IsPrimeE π ∧ ofInt (p : ℤ) = π * conj π
      ∧ ¬ AssociatedE π (conj π) := by
  sorry

/-- **Proposition 4.7(iii).** For `p ≡ 2 (mod 3)`, `p` remains prime in `ℤ[ω]`. -/
theorem prop_4_7_inert (p : ℕ) (hp : p.Prime) (h2 : p % 3 = 2) :
    IsPrimeE (ofInt (p : ℤ)) := by
  sorry

/-- **Lemma 4.8.** For a prime `π` lying over `p`, `N(π) = p` or `p²` (and the
residue field `ℤ[ω]/π` has `N(π)` elements). The residue-field cardinality is
deferred; here the norm dichotomy. -/
theorem lemma_4_8 (π : EisensteinInt) (hπ : IsPrimeE π) (p : ℕ) (hp : p.Prime)
    (hover : π ∣ ofInt (p : ℤ)) : norm π = (p : ℤ) ∨ norm π = (p : ℤ) ^ 2 := by
  sorry

/-- **Corollary 4.9** (Fermat's little theorem in `ℤ[ω]`). If `π ∤ α` then
`α^{N(π)−1} ≡ 1 (mod π)`. -/
theorem cor_4_9 (π α : EisensteinInt) (hπ : IsPrimeE π) (h : ¬ π ∣ α) :
    ModEq π (power α (norm π - 1).toNat) 1 := by
  sorry

/-- **Cubic character, defining property** (Cox (4.10)). -/
theorem cubicChar_spec (π α : EisensteinInt) (hπ : IsPrimeE π)
    (h3 : ¬ AssociatedE π (1 - omega)) (hα : ¬ π ∣ α) :
    ModEq π (power α ((norm π - 1) / 3).toNat) (cubicChar π α)
      ∧ (cubicChar π α = 1 ∨ cubicChar π α = omega ∨ cubicChar π α = omega * omega) := by
  sorry

/-- **Cubic character is multiplicative** (Cox (4.10)). -/
theorem cubicChar_mul (π α β : EisensteinInt) :
    cubicChar π (α * β) = cubicChar π α * cubicChar π β := by
  sorry

/-- **(4.11).** `(α/π)₃ = 1` iff `x³ ≡ α (mod π)` is solvable in `ℤ[ω]`. -/
theorem cubicChar_eq_one_iff (π α : EisensteinInt) (hπ : IsPrimeE π) (hα : ¬ π ∣ α) :
    cubicChar π α = 1 ↔ ∃ x : EisensteinInt, ModEq π (x * x * x) α := by
  sorry

/-- **Theorem 4.12** (Cubic Reciprocity). For primary primes `π, θ` of unequal norm,
`(π/θ)₃ = (θ/π)₃`. **Deep / GAP** - `notready`, never an axiom. -/
theorem thm_4_12 (π θ : EisensteinInt) (hπ : IsPrimeE π) (hθ : IsPrimeE θ)
    (hpπ : IsPrimary π) (hpθ : IsPrimary θ) (hne : norm π ≠ norm θ) :
    cubicChar θ π = cubicChar π θ := by
  sorry

/-- **(4.13)** Supplementary laws. For `π = −1 + 3m + 3nω` primary,
`(ω/π)₃ = ω^{m+n}` and `((1−ω)/π)₃ = ω^{2m}`. **Deep / GAP** - `notready`. -/
theorem supplementary_4_13 (m n : ℤ) :
    cubicChar ⟨-1 + 3 * m, 3 * n⟩ omega = power omega (((m + n) % 3).toNat)
      ∧ cubicChar ⟨-1 + 3 * m, 3 * n⟩ (1 - omega) = power omega ((2 * m % 3).toNat) := by
  sorry

/-- **(4.14).** For `p ≡ 1 (mod 3)` with `p = π·π̄`, `x³ ≡ a (mod p)` is solvable in
`ℤ` iff `(a/π)₃ = 1`. -/
theorem eq_4_14 (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1) (a : ℤ) (hpa : ¬ (p : ℤ) ∣ a)
    (π : EisensteinInt) (hπ : IsPrimeE π) (hsplit : ofInt (p : ℤ) = π * conj π) :
    (∃ x : ℤ, x ^ 3 ≡ a [ZMOD (p : ℤ)]) ↔ cubicChar π (ofInt a) = 1 := by
  sorry

/-- **Theorem 4.15** (Euler's conjecture). `p = x² + 27y²` iff `p ≡ 1 (mod 3)` and
`2` is a cubic residue mod `p`. **Deep / GAP** - `notready`, never an axiom. -/
theorem thm_4_15 (p : ℕ) (hp : p.Prime) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 27 * y ^ 2) ↔ (p % 3 = 1 ∧ IsCubicResidue 2 p) := by
  sorry

end EisensteinInt

end PrimesX2NY2.CubicReciprocity
