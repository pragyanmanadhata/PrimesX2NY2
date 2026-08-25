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

theorem neg_three_isSquare_iff' (p : ℕ) [Fact p.Prime] (hodd : Odd p) (hp3 : p ≠ 3) :
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

/-! ### Small arithmetic helpers (kept context-free so `omega` is safe) -/

theorem int_eq_one_of_toNat (n : ℤ) (h0 : 0 ≤ n) (h : n.toNat = 1) : n = 1 := by omega

theorem int_eq_natCast_of_toNat (n : ℤ) (p : ℕ) (h0 : 0 ≤ n) (h : n.toNat = p) :
    n = (p : ℤ) := by omega

theorem not_three_dvd_of_mod_two (p : ℕ) (h2 : p % 3 = 2) (c : ℤ) (hc : (p : ℤ) = 3 * c) :
    False := by omega

theorem not_three_dvd_sub_one_of_mod_two (p : ℕ) (h2 : p % 3 = 2) (c : ℤ)
    (hc : (p : ℤ) - 1 = 3 * c) : False := by omega

theorem not_three_dvd_of_mod_one (p : ℕ) (h1 : p % 3 = 1) (t : ℤ) (hc : (p : ℤ) = 3 * t) :
    False := by omega

theorem emod_two_cases (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 := by omega

theorem odd_shift' (u q : ℤ) (hu : u % 2 = 0) (hq : q % 2 = 1) : (u + q) % 2 = 1 := by omega

theorem exists_half' (x : ℤ) (hx : x % 2 = 1) : ∃ a : ℤ, x = 2 * a - 1 := ⟨(x + 1) / 2, by omega⟩

theorem natCast_odd' (p k : ℕ) (hk : p = 2 * k + 1) : (p : ℤ) % 2 = 1 := by omega

theorem p_eq_four' (p : ℕ) (h1 : p % 3 = 1) (h2 : 2 ≤ p) (h4 : p ≤ 4) : p = 4 := by omega

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

theorem eis_ext (x y : EisensteinInt) : x = y ↔ x.a = y.a ∧ x.b = y.b := by
  obtain ⟨p, q⟩ := x
  obtain ⟨r, s⟩ := y
  constructor
  · rintro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have h1' : p = r := h1
    have h2' : q = s := h2
    rw [h1', h2']

theorem mul_a (x y : EisensteinInt) : (x * y).a = x.a * y.a - x.b * y.b := rfl
theorem mul_b (x y : EisensteinInt) : (x * y).b = x.a * y.b + x.b * y.a - x.b * y.b := rfl
theorem add_a (x y : EisensteinInt) : (x + y).a = x.a + y.a := rfl
theorem add_b (x y : EisensteinInt) : (x + y).b = x.b + y.b := rfl
theorem sub_a (x y : EisensteinInt) : (x - y).a = x.a - y.a := rfl
theorem sub_b (x y : EisensteinInt) : (x - y).b = x.b - y.b := rfl
theorem neg_a (x : EisensteinInt) : (-x).a = -x.a := rfl
theorem neg_b (x : EisensteinInt) : (-x).b = -x.b := rfl
theorem one_a : (1 : EisensteinInt).a = 1 := rfl
theorem one_b : (1 : EisensteinInt).b = 0 := rfl
theorem zero_a : (0 : EisensteinInt).a = 0 := rfl
theorem zero_b : (0 : EisensteinInt).b = 0 := rfl
theorem ofInt_a (n : ℤ) : (ofInt n).a = n := rfl
theorem ofInt_b (n : ℤ) : (ofInt n).b = 0 := rfl
theorem conj_a (x : EisensteinInt) : (conj x).a = x.a - x.b := rfl
theorem conj_b (x : EisensteinInt) : (conj x).b = -x.b := rfl
theorem omega_a : omega.a = 0 := rfl
theorem omega_b : omega.b = 1 := rfl
theorem norm_mk (A B : ℤ) : EisensteinInt.norm ⟨A, B⟩ = A ^ 2 - A * B + B ^ 2 := rfl
theorem norm_zero' : EisensteinInt.norm 0 = 0 := by decide

macro "eis_ring" : tactic =>
  `(tactic| (rw [eis_ext]; refine ⟨?_, ?_⟩ <;>
      simp only [mul_a, mul_b, add_a, add_b, sub_a, sub_b, neg_a, neg_b,
        one_a, one_b, zero_a, zero_b, ofInt_a, ofInt_b, conj_a, conj_b,
        omega_a, omega_b] <;> ring))

theorem one_mul' (x : EisensteinInt) : 1 * x = x := by eis_ring
theorem zero_mul' (x : EisensteinInt) : 0 * x = 0 := by eis_ring
theorem mul_zero' (x : EisensteinInt) : x * 0 = 0 := by eis_ring
theorem mul_assoc' (x y z : EisensteinInt) : x * y * z = x * (y * z) := by eis_ring
theorem mul_add' (x y z : EisensteinInt) : x * (y + z) = x * y + x * z := by eis_ring
theorem mul_sub' (x y z : EisensteinInt) : x * (y - z) = x * y - x * z := by eis_ring
theorem sub_self' (x : EisensteinInt) : x - x = 0 := by eis_ring

theorem sub_eq_zero' (x y : EisensteinInt) : x - y = 0 ↔ x = y := by
  rw [eis_ext, eis_ext]
  simp only [sub_a, sub_b, zero_a, zero_b, sub_eq_zero]

theorem norm_ofInt (n : ℤ) : EisensteinInt.norm (ofInt n) = n ^ 2 := by
  rw [norm_def, ofInt_a, ofInt_b]; ring

theorem ofInt_mul (m n : ℤ) : ofInt (m * n) = ofInt m * ofInt n := by eis_ring

theorem ofInt_ne_zero (n : ℤ) (hn : n ≠ 0) : ofInt n ≠ 0 := by
  intro h0
  exact hn (by rw [← ofInt_a n, h0]; rfl)

theorem mul_conj' (x : EisensteinInt) : x * conj x = ofInt (EisensteinInt.norm x) :=
  mul_conj_self x

/-- Cancellation. -/
theorem mul_left_cancel' (x u v : EisensteinInt) (hx : x ≠ 0) (h : x * u = x * v) : u = v := by
  have h0 : x * (u - v) = 0 := by rw [mul_sub', h, sub_self']
  have hn : EisensteinInt.norm x * EisensteinInt.norm (u - v) = 0 := by
    rw [← EisensteinInt.norm_mul, h0, norm_zero']
  have hx0 := norm_ne_zero x hx
  have h2 : EisensteinInt.norm (u - v) = 0 := by
    rcases mul_eq_zero.mp hn with h' | h'
    · exact absurd h' hx0
    · exact h'
  exact (sub_eq_zero' u v).mp (eq_zero_of_norm_eq_zero _ h2)

/-! ### Divisibility helpers -/

theorem dvd_refl' (x : EisensteinInt) : x ∣ x := ⟨1, (mul_one' x).symm⟩

theorem dvd_trans' (x y z : EisensteinInt) (h1 : x ∣ y) (h2 : y ∣ z) : x ∣ z := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  exact ⟨c * d, by rw [hd, hc, mul_assoc']⟩

theorem dvd_add' (d x y : EisensteinInt) (h1 : d ∣ x) (h2 : d ∣ y) : d ∣ (x + y) := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨e, he⟩ := h2
  exact ⟨c + e, by rw [hc, he, mul_add']⟩

theorem dvd_mul_right' (d x y : EisensteinInt) (h : d ∣ x) : d ∣ (x * y) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c * y, by rw [hc, mul_assoc']⟩

/-! ### Bezout via the Euclidean algorithm -/

theorem bezout_aux : ∀ (n : ℕ) (x y : EisensteinInt), (EisensteinInt.norm y).natAbs < n →
    ∃ d s t : EisensteinInt, d = s * x + t * y ∧ d ∣ x ∧ d ∣ y := by
  intro n
  induction n with
  | zero => intro x y h; omega
  | succ n ih =>
    intro x y hn
    by_cases hy : y = 0
    · subst hy
      exact ⟨x, 1, 0, by eis_ring, dvd_refl' x, ⟨0, by eis_ring⟩⟩
    · obtain ⟨q, r, hqr, hr⟩ := prop_4_3 x y hy
      have hr0 := norm_nonneg r
      have hlt : (EisensteinInt.norm r).natAbs < n := by omega
      obtain ⟨d, s, t, hd, hdy, hdr⟩ := ih y r hlt
      subst hqr
      refine ⟨d, t, s - t * q, ?_, ?_, hdy⟩
      · rw [hd]; eis_ring
      · exact dvd_add' d (y * q) r (dvd_mul_right' d y q hdy) hdr

theorem bezout (x y : EisensteinInt) :
    ∃ d s t : EisensteinInt, d = s * x + t * y ∧ d ∣ x ∧ d ∣ y :=
  bezout_aux ((EisensteinInt.norm y).natAbs + 1) x y (by omega)

/-! ### Corollary 4.4 -/

/-- **Corollary 4.4.** `ℤ[ω]` is a PID and a UFD; in particular irreducible
elements coincide with primes. -/
theorem cor_4_4 (x : EisensteinInt) (hx : x ≠ 0) : IsIrreducibleE x ↔ IsPrimeE x := by
  constructor
  · rintro ⟨hnu, hfac⟩
    refine ⟨hnu, hx, ?_⟩
    intro α β hdvd
    by_cases ha : x ∣ α
    · exact Or.inl ha
    · right
      obtain ⟨d, s, t, hd, hdx, hda⟩ := bezout x α
      obtain ⟨c, hc⟩ := hdx
      rcases hfac d c hc with hu | hu
      · obtain ⟨e, he⟩ := hu
        obtain ⟨g, hg⟩ := hdvd
        have h1 : (1 : EisensteinInt) = (s * e) * x + (t * e) * α := by
          rw [← he, hd]; eis_ring
        have h2 : β = x * ((s * e) * β) + (t * e) * (α * β) := by
          have hkey : ((s * e) * x + (t * e) * α) * β
              = x * ((s * e) * β) + (t * e) * (α * β) := by eis_ring
          rw [← hkey, ← h1, one_mul']
        rw [hg] at h2
        refine ⟨(s * e) * β + (t * e) * g, ?_⟩
        refine h2.trans ?_
        eis_ring
      · exfalso
        obtain ⟨e, he⟩ := hu
        apply ha
        refine dvd_trans' x d α ⟨e, ?_⟩ hda
        rw [hc, mul_assoc', he, mul_one']
  · rintro ⟨hnu, hne, hprime⟩
    refine ⟨hnu, ?_⟩
    intro y z hyz
    have hdvd : x ∣ y * z := ⟨1, by rw [mul_one']; exact hyz.symm⟩
    rcases hprime y z hdvd with h | h
    · right
      obtain ⟨w, hw⟩ := h
      have hkey : x * (w * z) = x * 1 := by
        rw [← mul_assoc', ← hw, ← hyz, mul_one']
      have hwz : w * z = 1 := mul_left_cancel' x _ _ hne hkey
      exact ⟨w, by rw [mul_comm']; exact hwz⟩
    · left
      obtain ⟨w, hw⟩ := h
      have e1 : x * (y * w) = y * (x * w) := by eis_ring
      have hkey : x * (y * w) = x * 1 := by
        rw [e1, ← hw, ← hyz, mul_one']
      exact ⟨w, mul_left_cancel' x _ _ hne hkey⟩

/-! ### Lemma 4.6 -/

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
theorem norm_eq_p_of_factor (p : ℕ) (hp : p.Prime) (y z : EisensteinInt)
    (hprod : EisensteinInt.norm y * EisensteinInt.norm z = (p : ℤ) ^ 2)
    (hy : EisensteinInt.norm y ≠ 1) (hz : EisensteinInt.norm z ≠ 1) :
    EisensteinInt.norm y = (p : ℤ) := by
  have hy0 := norm_nonneg y
  have hz0 := norm_nonneg z
  have hmn : (EisensteinInt.norm y).toNat * (EisensteinInt.norm z).toNat = p ^ 2 := by
    have hc : (((EisensteinInt.norm y).toNat * (EisensteinInt.norm z).toNat : ℕ) : ℤ)
        = ((p ^ 2 : ℕ) : ℤ) := by
      push_cast [Int.toNat_of_nonneg hy0, Int.toNat_of_nonneg hz0]
      exact hprod
    exact_mod_cast hc
  obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow hp).mp ⟨_, hmn.symm⟩
  interval_cases i
  · rw [pow_zero] at hmi
    exact absurd (int_eq_one_of_toNat _ hy0 hmi) hy
  · rw [pow_one] at hmi
    exact int_eq_natCast_of_toNat _ _ hy0 hmi
  · rw [hmi] at hmn
    have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
    have hz1 : (EisensteinInt.norm z).toNat = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hmn)
    exact absurd (int_eq_one_of_toNat _ hz0 hz1) hz

/-! ### Proposition 4.7(i) -/

theorem lemma_4_6 (α : EisensteinInt) (p : ℕ) (hp : p.Prime)
    (h : EisensteinInt.norm α = (p : ℤ)) : IsPrimeE α := by
  have hne : α ≠ 0 := by
    intro h0
    rw [h0, norm_zero'] at h
    exact hp.ne_zero (by exact_mod_cast h.symm)
  have hnu : ¬ IsUnitE α := by
    rw [lemma_4_5_i, h]
    intro hc
    have hc1 : p = 1 := by exact_mod_cast hc
    exact hp.one_lt.ne' hc1
  rw [← cor_4_4 α hne]
  refine ⟨hnu, ?_⟩
  intro y z hyz
  have hprod : EisensteinInt.norm y * EisensteinInt.norm z = (p : ℤ) := by
    rw [← EisensteinInt.norm_mul, ← hyz, h]
  have hy0 := norm_nonneg y
  have hz0 := norm_nonneg z
  have hmn : (EisensteinInt.norm y).toNat * (EisensteinInt.norm z).toNat = p := by
    have hc : (((EisensteinInt.norm y).toNat * (EisensteinInt.norm z).toNat : ℕ) : ℤ)
        = ((p : ℕ) : ℤ) := by
      push_cast [Int.toNat_of_nonneg hy0, Int.toNat_of_nonneg hz0]
      exact hprod
    exact_mod_cast hc
  rcases hp.eq_one_or_self_of_dvd _ ⟨_, hmn.symm⟩ with h1 | h1
  · exact Or.inl ((lemma_4_5_i y).mpr (int_eq_one_of_toNat _ hy0 h1))
  · rw [h1] at hmn
    have hz1 : (EisensteinInt.norm z).toNat = 1 :=
      Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hmn)
    exact Or.inr ((lemma_4_5_i z).mpr (int_eq_one_of_toNat _ hz0 hz1))

/-! ### Norm of a nontrivial factor of `p` -/

/-- **Proposition 4.7(i).** For `p = 3`, `1 − ω` is prime and `3 = −ω²(1 − ω)²`. -/
theorem prop_4_7_ramified :
    IsPrimeE (1 - omega) ∧ ofInt 3 = -(omega * omega) * (1 - omega) * (1 - omega) := by
  refine ⟨lemma_4_6 (1 - omega) 3 (by norm_num) ?_, by decide⟩
  rw [norm_one_sub_omega]; norm_num

/-! ### Proposition 4.7(iii) -/

/-- **Proposition 4.7(ii).** For `p ≡ 1 (mod 3)`, `p = π·π̄` splits into nonassociate
primes. -/
theorem not_associated_conj (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1)
    (y : EisensteinInt) (hny : EisensteinInt.norm y = (p : ℤ)) :
    ¬ AssociatedE y (conj y) := by
  have hsq : ∀ t : ℤ, (p : ℤ) ≠ t ^ 2 := by
    intro t ht
    have h2 : t.natAbs * t.natAbs = p := by
      have hc : ((t.natAbs * t.natAbs : ℕ) : ℤ) = ((p : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Int.natAbs_mul_self', ht]; ring
      exact_mod_cast hc
    rcases hp.eq_one_or_self_of_dvd t.natAbs ⟨t.natAbs, h2.symm⟩ with h | h
    · rw [h, one_mul] at h2
      exact hp.one_lt.ne' h2.symm
    · rw [h] at h2
      exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact h2))
  have h3d : ∀ t : ℤ, (p : ℤ) ≠ 3 * t := fun t ht => not_three_dvd_of_mod_one p h1 t ht
  obtain ⟨A, B⟩ := y
  rw [norm_mk] at hny
  rintro ⟨u, hu, heq⟩
  rw [lemma_4_5_ii] at hu
  have e1 := congrArg EisensteinInt.a heq
  have e2 := congrArg EisensteinInt.b heq
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [conj_a, conj_b, mul_a, mul_b, one_a, one_b] at e1 e2
    have hh : B = 0 := by linarith
    exact hsq A (by rw [← hny, hh]; ring)
  · simp only [conj_a, conj_b, mul_a, mul_b, neg_a, neg_b, one_a, one_b] at e1 e2
    have hh : B = 2 * A := by linarith
    exact h3d (A ^ 2) (by rw [← hny, hh]; ring)
  · simp only [conj_a, conj_b, mul_a, mul_b, omega_a, omega_b] at e1 e2
    have hh : A = 0 := by linarith
    exact hsq B (by rw [← hny, hh]; ring)
  · simp only [conj_a, conj_b, mul_a, mul_b, neg_a, neg_b, omega_a, omega_b] at e1 e2
    have hh : A = 2 * B := by linarith
    exact h3d (B ^ 2) (by rw [← hny, hh]; ring)
  · simp only [conj_a, conj_b, mul_a, mul_b, omega_a, omega_b] at e1 e2
    have hh : A = B := by linarith
    exact hsq B (by rw [← hny, hh]; ring)
  · simp only [conj_a, conj_b, mul_a, mul_b, neg_a, neg_b, omega_a, omega_b] at e1 e2
    have hh : A = -B := by linarith
    exact h3d (B ^ 2) (by rw [← hny, hh]; ring)

/-! ### Proposition 4.7(ii) -/

theorem prop_4_7_split (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ π : EisensteinInt, IsPrimeE π ∧ ofInt (p : ℤ) = π * conj π
      ∧ ¬ AssociatedE π (conj π) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 := hp.two_le
  have hpzz : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hsq3 : IsSquare ((-3 : ℤ) : ZMod p) := (neg_three_isSquare_iff' p hodd (by omega)).mpr h1
  obtain ⟨s, hs⟩ := hsq3
  have hv : ((s.val : ℕ) : ZMod p) = s := by simp
  have hdvd0 : (p : ℤ) ∣ ((s.val : ℤ) ^ 2 + 3) := by
    have hz : ((((s.val : ℤ)) ^ 2 + 3 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hv]
      have h3 : ((-3 : ℤ) : ZMod p) = s * s := hs
      push_cast at h3
      linear_combination -h3
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  have hpodd : (p : ℤ) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact natCast_odd' p k hk
  obtain ⟨x, hxodd, hxdvd⟩ : ∃ x : ℤ, x % 2 = 1 ∧ (p : ℤ) ∣ (x ^ 2 + 3) := by
    rcases emod_two_cases (s.val : ℤ) with he | ho
    · refine ⟨(s.val : ℤ) + (p : ℤ), odd_shift' _ _ he hpodd, ?_⟩
      obtain ⟨c, hc⟩ := hdvd0
      exact ⟨c + 2 * (s.val : ℤ) + (p : ℤ), by linear_combination hc⟩
    · exact ⟨(s.val : ℤ), ho, hdvd0⟩
  obtain ⟨a, ha⟩ := exists_half' x hxodd
  have hNa : (p : ℤ) ∣ (a ^ 2 - a + 1) := by
    have h4 : (p : ℤ) ∣ 4 * (a ^ 2 - a + 1) := by
      obtain ⟨c, hc⟩ := hxdvd
      rw [ha] at hc
      exact ⟨c, by linear_combination hc⟩
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpz.dvd_mul.mp h4 with h | h
    · exfalso
      have hle : (p : ℤ) ≤ 4 := Int.le_of_dvd (by norm_num) h
      have hp4 : p ≤ 4 := by exact_mod_cast hle
      have hpe : p = 4 := p_eq_four' p h1 hp2 hp4
      rw [hpe] at hp; norm_num at hp
    · exact h
  have hbn : EisensteinInt.norm (⟨a, 1⟩ : EisensteinInt) = a ^ 2 - a + 1 := by
    rw [norm_mk]; ring
  have hdvdb : ofInt (p : ℤ) ∣ (⟨a, 1⟩ : EisensteinInt) * conj ⟨a, 1⟩ := by
    obtain ⟨k, hk⟩ := hNa
    exact ⟨ofInt k, by rw [mul_conj', hbn, hk, ofInt_mul]⟩
  have hnotprime : ¬ IsPrimeE (ofInt (p : ℤ)) := by
    rintro ⟨-, -, hpr⟩
    rcases hpr (⟨a, 1⟩ : EisensteinInt) (conj ⟨a, 1⟩) hdvdb with h | h
    · obtain ⟨c, hc⟩ := h
      have hb := congrArg EisensteinInt.b hc
      simp only [mul_b, ofInt_a, ofInt_b] at hb
      have hdd : (p : ℤ) ∣ 1 := ⟨c.b, by linear_combination hb⟩
      have hle := Int.le_of_dvd one_pos hdd
      linarith
    · obtain ⟨c, hc⟩ := h
      have hb := congrArg EisensteinInt.b hc
      simp only [conj_b, mul_b, ofInt_a, ofInt_b] at hb
      have hdd : (p : ℤ) ∣ 1 := ⟨-c.b, by linear_combination -hb⟩
      have hle := Int.le_of_dvd one_pos hdd
      linarith
  have hnorm : EisensteinInt.norm (ofInt (p : ℤ)) = (p : ℤ) ^ 2 := norm_ofInt _
  have hne : ofInt (p : ℤ) ≠ 0 := ofInt_ne_zero _ (by linarith)
  have hnu : ¬ IsUnitE (ofInt (p : ℤ)) := by
    rw [lemma_4_5_i, hnorm]
    intro hc
    nlinarith [hc, hpzz]
  have hnotirr : ¬ IsIrreducibleE (ofInt (p : ℤ)) := fun h => hnotprime ((cor_4_4 _ hne).mp h)
  have hfac : ∃ y z : EisensteinInt, ofInt (p : ℤ) = y * z ∧ ¬ IsUnitE y ∧ ¬ IsUnitE z := by
    by_contra hcc
    push_neg at hcc
    refine hnotirr ⟨hnu, fun y z hyz => ?_⟩
    by_cases hu : IsUnitE y
    · exact Or.inl hu
    · exact Or.inr (hcc y z hyz hu)
  obtain ⟨y, z, hyz, hy, hz⟩ := hfac
  rw [lemma_4_5_i] at hy hz
  have hprod : EisensteinInt.norm y * EisensteinInt.norm z = (p : ℤ) ^ 2 := by
    rw [← EisensteinInt.norm_mul, ← hyz, hnorm]
  have hny : EisensteinInt.norm y = (p : ℤ) := norm_eq_p_of_factor p hp y z hprod hy hz
  exact ⟨y, lemma_4_6 y p hp hny, by rw [mul_conj', hny], not_associated_conj p hp h1 y hny⟩

/-- **Proposition 4.7(iii).** For `p ≡ 2 (mod 3)`, `p` remains prime in `ℤ[ω]`. -/
theorem prop_4_7_inert (p : ℕ) (hp : p.Prime) (h2 : p % 3 = 2) :
    IsPrimeE (ofInt (p : ℤ)) := by
  have hp2 := hp.two_le
  have hpz : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
  have hnorm : EisensteinInt.norm (ofInt (p : ℤ)) = (p : ℤ) ^ 2 := norm_ofInt _
  have hne : ofInt (p : ℤ) ≠ 0 := ofInt_ne_zero _ (by linarith)
  have hnu : ¬ IsUnitE (ofInt (p : ℤ)) := by
    rw [lemma_4_5_i, hnorm]
    intro hc
    nlinarith [hc, hpz]
  rw [← cor_4_4 _ hne]
  refine ⟨hnu, ?_⟩
  intro y z hyz
  by_contra hcon
  push_neg at hcon
  obtain ⟨hy, hz⟩ := hcon
  rw [lemma_4_5_i] at hy hz
  have hprod : EisensteinInt.norm y * EisensteinInt.norm z = (p : ℤ) ^ 2 := by
    rw [← EisensteinInt.norm_mul, ← hyz, hnorm]
  have hnp : EisensteinInt.norm y = (p : ℤ) := norm_eq_p_of_factor p hp y z hprod hy hz
  rw [norm_def] at hnp
  by_cases h3 : (3 : ℤ) ∣ (y.a ^ 2 - y.a * y.b + y.b ^ 2)
  · rw [hnp] at h3
    obtain ⟨c, hc⟩ := h3
    exact not_three_dvd_of_mod_two p h2 c hc
  · have hm := norm_mod3_cases y.a y.b h3
    rw [hnp] at hm
    obtain ⟨c, hc⟩ := hm
    exact not_three_dvd_sub_one_of_mod_two p h2 c hc

/-! ### Lemma 4.8 -/

/-- **Lemma 4.8.** For a prime `π` lying over `p`, `N(π) = p` or `p²` (and the
residue field `ℤ[ω]/π` has `N(π)` elements). The residue-field cardinality is
deferred; here the norm dichotomy. -/
theorem lemma_4_8 (π : EisensteinInt) (hπ : IsPrimeE π) (p : ℕ) (hp : p.Prime)
    (hover : π ∣ ofInt (p : ℤ)) :
    EisensteinInt.norm π = (p : ℤ) ∨ EisensteinInt.norm π = (p : ℤ) ^ 2 := by
  obtain ⟨γ, hγ⟩ := hover
  have hnorm : EisensteinInt.norm π * EisensteinInt.norm γ = (p : ℤ) ^ 2 := by
    rw [← EisensteinInt.norm_mul, ← hγ, norm_ofInt]
  have hπ1 : EisensteinInt.norm π ≠ 1 := fun h => hπ.1 ((lemma_4_5_i π).mpr h)
  by_cases hγ1 : EisensteinInt.norm γ = 1
  · right
    rw [hγ1, mul_one] at hnorm
    exact hnorm
  · left
    exact norm_eq_p_of_factor p hp π γ hnorm hπ1 hγ1

/-! ### Non-associate conjugates -/

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
