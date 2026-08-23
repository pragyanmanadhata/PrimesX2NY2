/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.Genera

/-!
# Part I, §3 - Exercises (Cox, *Primes of the Form x² + ny²*, §3.E)

Faithful statements for the concrete, self-contained parts of Exercises 3.1-3.25.
Sub-parts that merely ask to *prove* a spine lemma, *complete a proof*, *enumerate*
forms of a given discriminant, or that need machinery not yet built (the
direct-composition predicate, `ℚ`/`ℤ_p`-equivalence, the abstract group structure
on `C(D)`, or the Kronecker symbol) are recorded as `\notready` blueprint nodes
only - see ROADMAP.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.PartI.S3

open PrimesX2NY2.Forms PrimesX2NY2.Genus PrimesX2NY2.Genera

/-- **Exercise 3.1(a).** Gauss's coefficient formulas for a composition
`f(x,y) g(z,w) = F(a₁xz+b₁xw+c₁yz+d₁yw, a₂xz+b₂xw+c₂yz+d₂yw)`. -/
theorem ex_3_1_a (a b c a' b' c' A B C a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (h : ∀ x y z w : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2) * (a' * z ^ 2 + b' * z * w + c' * w ^ 2)
        = A * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w) ^ 2
          + B * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
              * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w)
          + C * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w) ^ 2) :
    a * a' = A * a₁ ^ 2 + B * a₁ * a₂ + C * a₂ ^ 2
      ∧ a * c' = A * b₁ ^ 2 + B * b₁ * b₂ + C * b₂ ^ 2
      ∧ a * b' = 2 * A * a₁ * b₁ + B * (a₁ * b₂ + a₂ * b₁) + 2 * C * a₂ * b₂ := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h 1 0 1 0
  · linear_combination h 1 0 0 1
  · linear_combination h 1 0 1 1 - h 1 0 1 0 - h 1 0 0 1

/-- **Exercise 3.1(b).** `a²(b'² − 4a'c') = (a₁b₂ − a₂b₁)²(B² − 4AC)`. -/
theorem ex_3_1_b (a b c a' b' c' A B C a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (h : ∀ x y z w : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2) * (a' * z ^ 2 + b' * z * w + c' * w ^ 2)
        = A * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w) ^ 2
          + B * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
              * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w)
          + C * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w) ^ 2) :
    a ^ 2 * (b' ^ 2 - 4 * a' * c') = (a₁ * b₂ - a₂ * b₁) ^ 2 * (B ^ 2 - 4 * A * C) := by
  have e1 : a * a' = A * a₁ ^ 2 + B * a₁ * a₂ + C * a₂ ^ 2 := by linear_combination h 1 0 1 0
  have e2 : a * c' = A * b₁ ^ 2 + B * b₁ * b₂ + C * b₂ ^ 2 := by linear_combination h 1 0 0 1
  have e3 : a * b' = 2 * A * a₁ * b₁ + B * (a₁ * b₂ + a₂ * b₁) + 2 * C * a₂ * b₂ := by
    linear_combination h 1 0 1 1 - h 1 0 1 0 - h 1 0 0 1
  have key : a ^ 2 * (b' ^ 2 - 4 * a' * c') = (a * b') ^ 2 - 4 * (a * a') * (a * c') := by ring
  rw [key, e1, e2, e3]; ring

/-- **Exercise 3.1(c).** `a' = ±(a₁c₂ − a₂c₁)`. -/
theorem ex_3_1_c (a b c a' b' c' A B C a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (h : ∀ x y z w : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2) * (a' * z ^ 2 + b' * z * w + c' * w ^ 2)
        = A * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w) ^ 2
          + B * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
              * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w)
          + C * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w) ^ 2) :
    a' = a₁ * c₂ - a₂ * c₁ ∨ a' = -(a₁ * c₂ - a₂ * c₁) := by
  -- FLAG (under-hypothesized): FALSE as stated. The composition hypothesis alone does not
  -- pin `a'` down to sign; one must also know the two discriminants agree and are nonzero.
  -- Counterexample: `f = x² − y²`, `g = z² − w²`, `F(X,Y) = X·Y` with
  -- `X = (x−y)(z−w)`, `Y = (x+y)(z+w)` — i.e. `a₁=1, b₁=c₁=−1, d₁=1`, `a₂=b₂=c₂=d₂=1`,
  -- `A=C=0, B=1`. Then `h` holds identically but `a' = 1` while `a₁c₂ − a₂c₁ = 2`.
  -- (Here `disc f = 4` but `disc F = 1`.) See `ex_3_1_c_fixed` for the faithful version.
  sorry

/-- **Exercise 3.1(c)**, faithful form: `a' = ±(a₁c₂ − a₂c₁)` once the two discriminants
are known to agree and be nonzero. The identity `key` below is the symmetric partner of
`ex_3_1_b` and holds unconditionally. -/
theorem ex_3_1_c_fixed (a b c a' b' c' A B C a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (h : ∀ x y z w : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2) * (a' * z ^ 2 + b' * z * w + c' * w ^ 2)
        = A * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w) ^ 2
          + B * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
              * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w)
          + C * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w) ^ 2)
    (hdisc : b ^ 2 - 4 * a * c = B ^ 2 - 4 * A * C)
    (hne : b ^ 2 - 4 * a * c ≠ 0) :
    a' = a₁ * c₂ - a₂ * c₁ ∨ a' = -(a₁ * c₂ - a₂ * c₁) := by
  have e1 : a * a' = A * a₁ ^ 2 + B * a₁ * a₂ + C * a₂ ^ 2 := by linear_combination h 1 0 1 0
  have e2 : c * a' = A * c₁ ^ 2 + B * c₁ * c₂ + C * c₂ ^ 2 := by linear_combination h 0 1 1 0
  have e3 : b * a' = 2 * A * a₁ * c₁ + B * (a₁ * c₂ + a₂ * c₁) + 2 * C * a₂ * c₂ := by
    linear_combination h 1 1 1 0 - h 1 0 1 0 - h 0 1 1 0
  have key : a' ^ 2 * (b ^ 2 - 4 * a * c)
      = (a₁ * c₂ - a₂ * c₁) ^ 2 * (B ^ 2 - 4 * A * C) := by
    have expand : a' ^ 2 * (b ^ 2 - 4 * a * c)
        = (b * a') ^ 2 - 4 * (a * a') * (c * a') := by ring
    rw [expand, e1, e2, e3]; ring
  have hcancel : a' ^ 2 = (a₁ * c₂ - a₂ * c₁) ^ 2 := by
    have hz : (a' ^ 2 - (a₁ * c₂ - a₂ * c₁) ^ 2) * (b ^ 2 - 4 * a * c) = 0 := by
      linear_combination key - (a₁ * c₂ - a₂ * c₁) ^ 2 * hdisc
    rcases mul_eq_zero.mp hz with h' | h'
    · linarith
    · exact absurd h' hne
  have hfac : (a' - (a₁ * c₂ - a₂ * c₁)) * (a' + (a₁ * c₂ - a₂ * c₁)) = 0 := by
    linear_combination hcancel
  rcases mul_eq_zero.mp hfac with h' | h'
  · left; linarith
  · right; linarith

/-- **Exercise 3.5(b).** With `X = xz − Cyw` and `Y = axw + a'yz + Byw`,
`(a x²+B xy+a'C y²)(a' z²+B zw+a C w²) = a a' X² + B X Y + C Y²`. -/
theorem ex_3_5_b (a a' B C : ℤ) : ∀ x y z w : ℤ,
    (a * x ^ 2 + B * x * y + a' * C * y ^ 2) * (a' * z ^ 2 + B * z * w + a * C * w ^ 2)
      = a * a' * (x * z - C * y * w) ^ 2
        + B * (x * z - C * y * w) * (a * x * w + a' * y * z + B * y * w)
        + C * (a * x * w + a' * y * z + B * y * w) ^ 2 := by
  intro x y z w
  ring

/-- **Exercise 3.5(e).** The Dirichlet composition of two primitive forms is
primitive. -/
theorem ex_3_5_e (f g : BinaryQF) (hfp : f.Primitive) (hgp : g.Primitive)
    (hcop : Int.gcd (Int.gcd f.a g.a) ((f.b + g.b) / 2) = 1) :
    (dirichletForm f g).Primitive := by
  sorry

/-- **Exercise 3.7.** `a c x² + b x y + y²` is properly equivalent to the principal
form of its discriminant. -/
theorem ex_3_7 (a b c : ℤ) :
    ProperlyEquivalent (⟨a * c, b, 1⟩ : BinaryQF)
      (principalForm ((⟨a * c, b, 1⟩ : BinaryQF).discr)) := by
  have hdiscr : (⟨a * c, b, 1⟩ : BinaryQF).discr = (⟨1, -b, a * c⟩ : BinaryQF).discr := by
    simp only [BinaryQF.discr]; ring
  have hinv : ProperlyEquivalent (⟨a * c, b, 1⟩ : BinaryQF) (⟨1, -b, a * c⟩ : BinaryQF) := by
    refine ⟨!![0, -1; 1, 0], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]; ring
    · simp only [action, BinaryQF.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons, Matrix.head_fin_const]
      refine ⟨by ring, by ring, by ring⟩
  have hprin : ProperlyEquivalent (⟨1, -b, a * c⟩ : BinaryQF)
      (principalForm ((⟨1, -b, a * c⟩ : BinaryQF).discr)) :=
    principal_of_a_one _ (⟨1, -b, a * c⟩ : BinaryQF) rfl rfl
  rw [hdiscr]
  exact properlyEquivalent_equivalence.trans hinv hprin

/-- The reflection matrix `S = diag(1, −1)`; it has determinant `−1` and sends a
form to its opposite. -/
private def refl2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

private theorem refl2_det : refl2.det = -1 := by
  simp [refl2, Matrix.det_fin_two_of]

private theorem refl2_mul_refl2 : refl2 * refl2 = 1 := by
  rw [refl2, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

private theorem action_refl2 (f : BinaryQF) : action refl2 f = f.opposite := by
  obtain ⟨a, b, c⟩ := f
  have e00 : refl2 0 0 = 1 := rfl
  have e01 : refl2 0 1 = 0 := rfl
  have e10 : refl2 1 0 = 0 := rfl
  have e11 : refl2 1 1 = -1 := rfl
  simp only [action, BinaryQF.opposite, e00, e01, e10, e11, BinaryQF.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

private theorem opposite_opposite (f : BinaryQF) : f.opposite.opposite = f := by
  simp [BinaryQF.opposite]

/-- **Exercise 3.8(a).** The Lagrangian (full-equivalence) class of `f` is the union
of the proper class of `f` and the proper class of its opposite. -/
theorem ex_3_8_a (f : BinaryQF) :
    {g : BinaryQF | Equivalent f g}
      = {g : BinaryQF | ProperlyEquivalent f g}
        ∪ {g : BinaryQF | ProperlyEquivalent f.opposite g} := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨M, hdet | hdet, rfl⟩
    · exact Or.inl ⟨M, hdet, rfl⟩
    · refine Or.inr ⟨refl2 * M, ?_, ?_⟩
      · rw [Matrix.det_mul, refl2_det, hdet]; ring
      · rw [← action_refl2, action_mul, ← Matrix.mul_assoc, refl2_mul_refl2, Matrix.one_mul]
  · rintro (⟨M, hdet, rfl⟩ | ⟨M, hdet, rfl⟩)
    · exact ⟨M, Or.inl hdet, rfl⟩
    · refine ⟨refl2 * M, Or.inr ?_, ?_⟩
      · rw [Matrix.det_mul, refl2_det, hdet]; ring
      · rw [← action_mul, action_refl2]

/-- **Exercise 3.8(b).** Equivalence of: the Lagrangian class equals the proper
class; `f` is properly equivalent to its opposite; `f` is (properly and) improperly
equivalent to itself. (Cox's fourth condition - class order `≤ 2` - is deferred.) -/
theorem ex_3_8_b (f : BinaryQF) :
    [ {g : BinaryQF | Equivalent f g} = {g : BinaryQF | ProperlyEquivalent f g},
      ProperlyEquivalent f f.opposite,
      ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = -1 ∧ action M f = f ].TFAE := by
  tfae_have 1 → 2 := by
    intro h
    have hmem : f.opposite ∈ {g : BinaryQF | Equivalent f g} :=
      ⟨refl2, Or.inr refl2_det, action_refl2 f⟩
    rw [h] at hmem
    exact hmem
  tfae_have 2 → 3 := by
    rintro ⟨N, hN, hact⟩
    refine ⟨N * refl2, by rw [Matrix.det_mul, hN, refl2_det]; ring, ?_⟩
    rw [← action_mul, hact, action_refl2, opposite_opposite]
  tfae_have 3 → 1 := by
    rintro ⟨M, hM, hMf⟩
    ext g
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, hdet | hdet, rfl⟩
      · exact ⟨N, hdet, rfl⟩
      · refine ⟨M * N, by rw [Matrix.det_mul, hM, hdet]; ring, ?_⟩
        rw [← action_mul, hMf]
    · rintro ⟨N, hdet, rfl⟩
      exact ⟨N, Or.inl hdet, rfl⟩
  tfae_finish

/-- **Exercise 3.12(b).** The number of genera of forms of a negative discriminant
`D` is at most `2^{μ−1}` (the bound preceding the equality of Theorem 3.15). -/
theorem ex_3_12_b (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (Set.range (genusVector D)).ncard ≤ 2 ^ (mu D - 1) := by
  sorry

/-- **Exercise 3.13(e).** Gauss's derivation of the second supplement:
`(2/p) = (−1)^{(p²−1)/8}`, i.e. `+1` iff `p ≡ ±1 (mod 8)`. -/
theorem ex_3_13_e (p : ℕ) [Fact p.Prime] (hodd : Odd p) :
    legendreSym p 2 = if p % 8 = 1 ∨ p % 8 = 7 then (1 : ℤ) else -1 := by
  have h2 : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hodd
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  rw [legendreSym.at_two h2, ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ p % 2 = 0)]

/-- **Exercise 3.16.** `x² + 18y²` and `2x² + 9y²` have the same discriminant `−72`
but lie in different genera (so genus is not a rational-equivalence invariant). -/
theorem ex_3_16 :
    (⟨1, 0, 18⟩ : BinaryQF).discr = (⟨2, 0, 9⟩ : BinaryQF).discr
      ∧ genus (-72) (⟨1, 0, 18⟩ : BinaryQF) ≠ genus (-72) (⟨2, 0, 9⟩ : BinaryQF) := by
  sorry

/-- **Exercise 3.20(a).** For odd `m` coprime to `n`, the number of solutions of
`x² ≡ −n (mod m)` is `∏_{p ∣ m} (1 + (−n/p))`. -/
theorem ex_3_20_a (n m : ℕ) [NeZero m] (hn : 0 < n) (hm : Odd m) (hco : Nat.Coprime m n) :
    ((Finset.univ.filter (fun x : ZMod m => x ^ 2 = ((-(n : ℤ) : ℤ) : ZMod m))).card : ℤ)
      = ∏ p ∈ m.primeFactors, (1 + jacobiSym (-(n : ℤ)) p) := by
  sorry

/-- **Exercise 3.21(b).** If `m = a² + 2b²` then
`m³ = (a³ − 6ab²)² + 2(3a²b − 2b³)²` (norm-cubing in `ℤ[√−2]`). -/
theorem ex_3_21_b (a b : ℤ) :
    (a ^ 2 + 2 * b ^ 2) ^ 3
      = (a ^ 3 - 6 * a * b ^ 2) ^ 2 + 2 * (3 * a ^ 2 * b - 2 * b ^ 3) ^ 2 := by
  ring

/-- `P² + 2Q² = 0` forces `P = Q = 0` over `ℤ` (the norm form of `ℤ[√-2]`). -/
theorem norm_eq_zero_aux (P Q : ℤ) (h : P ^ 2 + 2 * Q ^ 2 = 0) : P = 0 ∧ Q = 0 := by
  constructor
  · have hP : P ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg Q]) (sq_nonneg P)
    exact sq_eq_zero_iff.mp hP
  · have hQ : Q ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg P]) (sq_nonneg Q)
    exact sq_eq_zero_iff.mp hQ

/-- Descent: `x² = 6y²` forces `x = y = 0` (6 is not a square). -/
theorem sq_eq_six_sq_aux :
    ∀ (n : ℕ) (x z : ℤ), z.natAbs ≤ n → x ^ 2 = 6 * z ^ 2 → x = 0 ∧ z = 0 := by
  intro n
  induction n with
  | zero =>
    intro x z hz h
    have hz0 : z = 0 := by omega
    subst hz0
    refine ⟨?_, rfl⟩
    have hx : x ^ 2 = 0 := by linear_combination h
    exact sq_eq_zero_iff.mp hx
  | succ n ih =>
    intro x z hz h
    rcases eq_or_ne z 0 with rfl | hz0
    · refine ⟨?_, rfl⟩
      have hx : x ^ 2 = 0 := by linear_combination h
      exact sq_eq_zero_iff.mp hx
    · exfalso
      have hxx : (2 : ℤ) ∣ x ^ 2 := ⟨3 * z ^ 2, by linear_combination h⟩
      have hx2 : (2 : ℤ) ∣ x := Int.prime_two.dvd_of_dvd_pow hxx
      obtain ⟨t, ht⟩ := hx2
      have h4 : (2 : ℤ) * (2 * t ^ 2) = 2 * (3 * z ^ 2) := by
        rw [ht] at h; linear_combination h
      have h2 : 2 * t ^ 2 = 3 * z ^ 2 := mul_left_cancel₀ two_ne_zero h4
      have hzz : (2 : ℤ) ∣ z := by
        have hd : (2 : ℤ) ∣ 3 * z ^ 2 := ⟨t ^ 2, by linear_combination -h2⟩
        rcases Int.prime_two.dvd_mul.mp hd with h' | h'
        · norm_num at h'
        · exact Int.prime_two.dvd_of_dvd_pow h'
      obtain ⟨u, hu⟩ := hzz
      have h5 : (2 : ℤ) * t ^ 2 = 2 * (6 * u ^ 2) := by
        rw [hu] at h2; linear_combination h2
      have h6 : t ^ 2 = 6 * u ^ 2 := mul_left_cancel₀ two_ne_zero h5
      have hu0 : u ≠ 0 := by
        rintro rfl
        exact hz0 (by simpa using hu)
      have hna : z.natAbs = 2 * u.natAbs := by
        rw [hu]; simp [Int.natAbs_mul]
      have hun : u.natAbs ≠ 0 := by simpa using hu0
      have hle : u.natAbs ≤ n := by omega
      obtain ⟨-, hu2⟩ := ih t u hle h6
      exact hu0 hu2

theorem sq_eq_six_sq (x z : ℤ) (h : x ^ 2 = 6 * z ^ 2) : x = 0 ∧ z = 0 :=
  sq_eq_six_sq_aux z.natAbs x z le_rfl h

/-- **Exercise 3.21(c).** The cubing map `(a,b) ↦ (a³ − 6ab², 3a²b − 2b³)` on
`ℤ[√−2]` is injective. -/
theorem ex_3_21_c :
    Function.Injective
      (fun p : ℤ × ℤ => (p.1 ^ 3 - 6 * p.1 * p.2 ^ 2, 3 * p.1 ^ 2 * p.2 - 2 * p.2 ^ 3)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hEq
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨E1, E2⟩ := hEq
  -- `z³ = w³` in `ℤ[√-2]`; factor `z³ - w³ = (z-w)(z²+zw+w²)` and take norms.
  have hnorm : ((a - c) ^ 2 + 2 * (b - d) ^ 2) *
      (((a ^ 2 - 2 * b ^ 2) + (a * c - 2 * b * d) + (c ^ 2 - 2 * d ^ 2)) ^ 2
        + 2 * (2 * a * b + (a * d + b * c) + 2 * c * d) ^ 2) = 0 := by
    have key : ∀ P Q R S : ℤ,
        (P ^ 2 + 2 * Q ^ 2) * (R ^ 2 + 2 * S ^ 2)
          = (P * R - 2 * Q * S) ^ 2 + 2 * (P * S + Q * R) ^ 2 := by
      intro P Q R S; ring
    rw [key]
    have h1 : (a - c) * ((a ^ 2 - 2 * b ^ 2) + (a * c - 2 * b * d) + (c ^ 2 - 2 * d ^ 2))
        - 2 * (b - d) * (2 * a * b + (a * d + b * c) + 2 * c * d) = 0 := by
      linear_combination E1
    have h2 : (a - c) * (2 * a * b + (a * d + b * c) + 2 * c * d)
        + (b - d) * ((a ^ 2 - 2 * b ^ 2) + (a * c - 2 * b * d) + (c ^ 2 - 2 * d ^ 2)) = 0 := by
      linear_combination E2
    rw [h1, h2]; ring
  rcases mul_eq_zero.mp hnorm with h | h
  · obtain ⟨hac, hbd⟩ := norm_eq_zero_aux _ _ h
    simp only [Prod.mk.injEq]
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨hV1, hV2⟩ := norm_eq_zero_aux _ _ h
    -- `4(z²+zw+w²) = (2z+w)² + 3w²`, so `(2z+w)² = -3w²`
    have hA : (2 * a + c) ^ 2 - 2 * (2 * b + d) ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 := by
      linear_combination 4 * hV1
    have hB : (2 * a + c) * (2 * b + d) + 3 * (c * d) = 0 := by
      linear_combination 2 * hV2
    have hsq : ((2 * a + c) ^ 2 + 2 * (2 * b + d) ^ 2) ^ 2 = (3 * (c ^ 2 + 2 * d ^ 2)) ^ 2 := by
      linear_combination ((2 * a + c) ^ 2 - 2 * (2 * b + d) ^ 2 - 3 * c ^ 2 + 6 * d ^ 2) * hA
        + (8 * ((2 * a + c) * (2 * b + d) - 3 * (c * d))) * hB
    have hXY : ((2 * a + c) ^ 2 + 2 * (2 * b + d) ^ 2 - 3 * (c ^ 2 + 2 * d ^ 2))
        * ((2 * a + c) ^ 2 + 2 * (2 * b + d) ^ 2 + 3 * (c ^ 2 + 2 * d ^ 2)) = 0 := by
      linear_combination hsq
    have hEq2 : (2 * a + c) ^ 2 + 2 * (2 * b + d) ^ 2 = 3 * (c ^ 2 + 2 * d ^ 2) := by
      rcases mul_eq_zero.mp hXY with h' | h'
      · linarith
      · linarith [sq_nonneg (2 * a + c), sq_nonneg (2 * b + d), sq_nonneg c, sq_nonneg d]
    have h6a : (2 * a + c) ^ 2 = 6 * d ^ 2 := by linarith
    have h6b : (2 * (2 * b + d)) ^ 2 = 6 * c ^ 2 := by linear_combination hEq2 - hA
    obtain ⟨hS1, hd0⟩ := sq_eq_six_sq _ _ h6a
    obtain ⟨hS2, hc0⟩ := sq_eq_six_sq _ _ h6b
    simp only [Prod.mk.injEq]
    exact ⟨by omega, by omega⟩

/-- **Exercise 3.22.** Fermat's result: the only integer solutions of `x³ = y² + 2`
are `(x, y) = (3, ±5)`. -/
theorem ex_3_22 (x y : ℤ) (h : x ^ 3 = y ^ 2 + 2) : x = 3 ∧ (y = 5 ∨ y = -5) := by
  sorry

/-- **Exercise 3.23.** An odd prime `p` of the form `x² + n y²` (`n > 1`) has a
unique representation `p = x² + n y²` with `x, y ≥ 0`. -/
theorem ex_3_23 (n p : ℕ) (hn : 1 < n) (hp : p.Prime) (hodd : Odd p)
    (hrep : ∃ x y : ℤ, x ^ 2 + (n : ℤ) * y ^ 2 = (p : ℤ)) :
    ∃! q : ℕ × ℕ, (q.1 : ℤ) ^ 2 + (n : ℤ) * (q.2 : ℤ) ^ 2 = (p : ℤ) := by
  sorry

end PrimesX2NY2.PartI.S3
