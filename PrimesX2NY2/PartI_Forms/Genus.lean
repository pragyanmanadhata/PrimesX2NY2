/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.FormClassGroup

/-!
# Part I, Chapter 4 - Genus theory and representation

Cox, *Primes of the Form x² + ny²*, §3 (genus theory).

Genus theory partitions the form class group; the principal genus is the subgroup
of squares, and genus characters decide which primes a form represents.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.Genus

open PrimesX2NY2.Forms

/-- A form `f` **represents** an integer `m` if `m = f(x, y)` for some integers
`x, y`. (Cox, §1-2.) -/
def Represents (f : BinaryQF) (m : ℤ) : Prop := ∃ x y : ℤ, f.eval x y = m

/-- A form `f` **properly represents** `m` if `m = f(x, y)` with `gcd(x, y) = 1`.
(Cox, §2.) -/
def ProperlyRepresents (f : BinaryQF) (m : ℤ) : Prop :=
  ∃ x y : ℤ, f.eval x y = m ∧ IsCoprime x y

/-- The **genus** of a form of discriminant `D`: the set of residues in
`(ℤ/Dℤ)` represented by the form, which is constant on a genus. (Cox, §3.) -/
def genus (D : ℤ) (f : BinaryQF) : Set (ZMod D.natAbs) := sorry

/-- The **principal genus**: the genus of the principal form, equivalently the
subgroup of squares in `C(D)`. (Cox, Thm 3.15.) -/
def principalGenus (D : ℤ) : Set (ZMod D.natAbs) := sorry

/-- **Representation criterion via residues** (Cox, Thm 2.16 / §3). A prime `p`
not dividing `D` is properly represented by some form of discriminant `D` iff `D`
is a quadratic residue mod `p`. -/
theorem properlyRepresents_iff_isSquare (D : ℤ) (p : ℕ) (hp : p.Prime)
    (hpD : ¬ (p : ℤ) ∣ D) :
    (∃ f : BinaryQF, f.discr = D ∧ ProperlyRepresents f p) ↔ IsSquare (D : ZMod p) := by
  sorry

/-- **Lemma 2.3.** A form `f` properly represents `m` iff `f` is properly
equivalent to a form `m x² + b x y + c y²` for some `b, c`. (Cox §2.) -/
theorem properlyRepresents_iff_properlyEquivalent (f : BinaryQF) (m : ℤ) :
    ProperlyRepresents f m ↔ ∃ b c : ℤ, ProperlyEquivalent f ⟨m, b, c⟩ := by
  constructor
  · rintro ⟨p, q, hpq, hcop⟩
    obtain ⟨u, v, huv⟩ := hcop
    set M : Matrix (Fin 2) (Fin 2) ℤ := !![p, -v; q, u] with hM
    have hdet : M.det = 1 := by rw [hM, Matrix.det_fin_two_of]; linear_combination huv
    have ha : (action M f).a = m := by
      rw [← hpq]
      simp only [action, BinaryQF.eval, hM, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_fin_const]
    exact ⟨(action M f).b, (action M f).c, M, hdet, by rw [← ha]⟩
  · rintro ⟨b, c, M, hdet, hMf⟩
    refine ⟨M 0 0, M 1 0, ?_, ?_⟩
    · have h := eval_action M f 1 0
      rw [hMf] at h
      simpa [BinaryQF.eval] using h.symm
    · exact ⟨M 1 1, -(M 0 1), by rw [Matrix.det_fin_two] at hdet; linear_combination hdet⟩

/-- Per-prime foundation of Cox Lemma 2.25: a primitive form takes, at one of the
coprime points `(1,0), (0,1), (1,1)`, a value not divisible by a given prime `p`
(else `p` would divide `a`, `c`, and `a+b+c`, hence `b`, hence `gcd(a,b,c)=1`). The full
Lemma 2.25 combines these per-prime witnesses across `p ∣ M` by CRT. -/
theorem represents_not_dvd_prime (f : BinaryQF) (hf : f.Primitive) (p : ℕ) (hp : p.Prime) :
    ∃ x y : ℤ, IsCoprime x y ∧ ¬ (p : ℤ) ∣ f.eval x y := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have ha : (p : ℤ) ∣ f.a := by
    have := hcon 1 0 isCoprime_one_left; simpa [BinaryQF.eval] using this
  have hc : (p : ℤ) ∣ f.c := by
    have := hcon 0 1 isCoprime_one_right; simpa [BinaryQF.eval] using this
  have hac : (p : ℤ) ∣ f.a + f.b + f.c := by
    have := hcon 1 1 isCoprime_one_left; simpa [BinaryQF.eval] using this
  have hb : (p : ℤ) ∣ f.b := by
    have e : f.b = (f.a + f.b + f.c) - f.a - f.c := by ring
    rw [e]; exact dvd_sub (dvd_sub hac ha) hc
  have hpc : p ∣ Int.gcd (Int.gcd f.a f.b) f.c :=
    Int.dvd_gcd (by exact_mod_cast Int.dvd_gcd ha hb) hc
  rw [hf] at hpc
  exact absurd (Nat.dvd_one.mp hpc) hp.one_lt.ne'


/-- **Lemma 2.5.** For `D ≡ 0,1 (mod 4)` and odd `m` prime to `D`, `m` is properly
represented by a primitive form of discriminant `D` iff `D` is a quadratic
residue mod `m`. (Cox §2; the general odd-`m` form of which
`properlyRepresents_iff_isSquare` is the prime case.) -/
theorem properlyRepresents_iff_isSquare_general (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (m : ℤ) (hm : Odd m) (hco : IsCoprime m D) :
    (∃ f : BinaryQF, f.discr = D ∧ f.Primitive ∧ ProperlyRepresents f m)
      ↔ IsSquare (D : ZMod m.natAbs) := by
  sorry

/-- **Corollary 2.6.** For an odd prime `p ∤ n`, `(−n/p) = 1` iff `p` is
represented by a primitive form of discriminant `−4n`. (Cox §2.) -/
theorem cor_2_6 (n : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpn : ¬ (p : ℤ) ∣ n) :
    IsSquare ((-n : ℤ) : ZMod p)
      ↔ ∃ f : BinaryQF, f.discr = -4 * n ∧ f.Primitive ∧ Represents f (p : ℤ) := by
  sorry

/-- **Proposition 2.15.** For an odd prime `p ∤ n`, `(−n/p) = 1` iff `p` is
represented by one of the reduced forms of discriminant `−4n`. (Cox §2.) -/
theorem prop_2_15 (n : ℕ) (hn : 0 < n) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hpn : ¬ (p : ℤ) ∣ (n : ℤ)) :
    IsSquare ((-(n : ℤ)) : ZMod p)
      ↔ ∃ f : BinaryQF, f.discr = -4 * (n : ℤ) ∧ f.Reduced ∧ f.Primitive
          ∧ Represents f (p : ℤ) := by
  sorry

/-- **Theorem 2.16.** For negative `D ≡ 0,1 (mod 4)` and an odd prime `p ∤ D`,
`(D/p) = 1` (equivalently `[p] ∈ ker χ`) iff `p` is represented by one of the
reduced forms of discriminant `D`. (Cox §2.) -/
theorem thm_2_16 (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) (hDneg : D < 0)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpD : ¬ (p : ℤ) ∣ D) :
    IsSquare (D : ZMod p)
      ↔ ∃ f : BinaryQF, f.discr = D ∧ f.Reduced ∧ f.Primitive ∧ Represents f (p : ℤ) := by
  sorry

/-- **Lemma 2.24** (part i). For negative `D ≡ 0,1 (mod 4)`, the residues in
`(ℤ/Dℤ)ˣ` represented by the principal form constitute a subgroup `H`. (Cox §2.) -/
theorem principalForm_values_subgroup (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (hDneg : D < 0) :
    ∃ H : Subgroup (ZMod D.natAbs)ˣ,
      ∀ u : (ZMod D.natAbs)ˣ,
        (u ∈ H ↔ ∃ x y : ℤ, IsCoprime x y ∧
          ((principalForm D).eval x y : ZMod D.natAbs) = (u : ZMod D.natAbs)) := by
  sorry

/-- **Lemma 2.25** (Gauss). Every form properly represents some value relatively
prime to a given integer `M`. (Cox §2.) -/
theorem properlyRepresents_coprime (f : BinaryQF) (M : ℤ) :
    ∃ x y : ℤ, IsCoprime x y ∧ IsCoprime (f.eval x y) M := by
  sorry

/-- **Theorem 2.26.** For negative `D ≡ 0,1 (mod 4)`, an odd prime `p ∤ D` lies in
the genus of a form `g` of discriminant `D` iff `p` is represented by a reduced
form of discriminant `D` in the same genus as `g`. (Cox §2.) -/
theorem thm_2_26 (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) (hDneg : D < 0)
    (g : BinaryQF) (hg : g.discr = D) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hpD : ¬ (p : ℤ) ∣ D) :
    (p : ZMod D.natAbs) ∈ genus D g
      ↔ ∃ f : BinaryQF, f.discr = D ∧ f.Reduced ∧ f.Primitive
          ∧ Represents f (p : ℤ) ∧ genus D f = genus D g := by
  sorry

/-- **Corollary 2.27.** For `n > 0` and an odd prime `p ∤ n`, `p` is represented by
a form of discriminant `−4n` in the principal genus iff `p ≡ β²` or `β² + n`
`(mod 4n)` for some `β`. (Cox §2.)

(Replaces an earlier vacuous statement whose right-hand side `∃ S, p ∈ S` was
always true.) -/
theorem represents_principal_iff_congruence (n : ℕ) (hn : 0 < n) (p : ℕ)
    (hp : p.Prime) (hodd : Odd p) (hpn : ¬ (p : ℤ) ∣ (n : ℤ)) :
    (p : ZMod ((-4 * (n : ℤ)).natAbs)) ∈ principalGenus (-4 * (n : ℤ))
      ↔ ∃ β : ℤ, ((p : ℤ) ≡ β ^ 2 [ZMOD (4 * n)]) ∨
          ((p : ℤ) ≡ β ^ 2 + (n : ℤ) [ZMOD (4 * n)]) := by
  sorry

end PrimesX2NY2.Genus
