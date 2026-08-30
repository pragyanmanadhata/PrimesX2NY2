/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.FormClassGroup
import PrimesX2NY2.PartI_Forms.Fermat

/-!
# Part I, Chapters 2-3 - Representation, composition, and genus theory

Cox, *Primes of the Form x² + ny²*, §2-3.

Representation criteria, direct composition, and the commutative group structure
on proper classes of positive definite forms. The later genus results describe
representation by forms within a genus; genus alone does not distinguish the
individual classes in general.

The composition and group-law proofs are complete. The genus definitions, some
representation statements, and the count in Proposition 3.11 still contain
`sorry`. The unrestricted residue criterion below is known to need additional
hypotheses; counterexamples and a corrected theorem are included.
-/

namespace PrimesX2NY2.Genus

open PrimesX2NY2.Forms
open scoped Int

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
is a quadratic residue mod `p`.

This statement is false without `D ≡ 0, 1 (mod 4)` and `Odd p`.
The counterexamples below use `D = 3, p = 11` (no form has discriminant `3`) and
`D = 5, p = 2`; see `properlyRepresents_iff_isSquare_counterexample` and
`properlyRepresents_iff_isSquare_counterexample_two`.
The corrected theorem is `properlyRepresents_iff_isSquare_repaired`.
The forward direction needs no further hypotheses:
`properlyRepresents_isSquare_forward'`. -/
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

/-- A primitive form has a value not divisible by `p` at one of the coprime
points `(1,0), (0,1), (1,1)`. Otherwise `p` would divide `a`, `c`, and `a+b+c`,
contradicting primitivity. Lemma 2.25 combines these choices for the prime factors
of `M` by the Chinese remainder theorem. (Cox §2.) -/
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

/-- Congruent inputs give congruent values of a binary quadratic form. -/
theorem eval_cong (f : BinaryQF) (x x' y y' p : ℤ) (hx : x ≡ x' [ZMOD p]) (hy : y ≡ y' [ZMOD p]) :
    f.eval x y ≡ f.eval x' y' [ZMOD p] := by
  simp only [BinaryQF.eval]
  exact (((hx.pow 2).mul_left f.a).add ((hx.mul_left f.b).mul hy)).add ((hy.pow 2).mul_left f.c)

/-- An integer divisible by no prime factor of `M` is coprime to `M`. -/
theorem coprime_of_all_primes (n M : ℤ) (h : ∀ p : ℕ, p.Prime → (p:ℤ) ∣ M → ¬ (p:ℤ) ∣ n) :
    IsCoprime n M := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpc : (p:ℤ) ∣ (Int.gcd n M : ℤ) := Int.natCast_dvd_natCast.mpr hpd
  exact h p hp (hpc.trans (Int.gcd_dvd_right n M)) (hpc.trans (Int.gcd_dvd_left n M))

/-- A primitive form takes a value coprime to any nonzero `M`. Apply the Chinese
remainder theorem to the choices `(1,0), (0,1), (1,1)` for each prime factor of `M`.
This is the congruence step in Cox's Lemma 2.25. -/
theorem exists_eval_coprime (f : BinaryQF) (hf : f.Primitive) (M : ℤ) (hM : M ≠ 0) :
    ∃ x y : ℤ, IsCoprime (f.eval x y) M := by
  set wx : ℕ → ℕ := fun p => if (p:ℤ) ∣ f.a then (if (p:ℤ) ∣ f.c then 1 else 0) else 1 with hwxdef
  set wy : ℕ → ℕ := fun p => if (p:ℤ) ∣ f.a then 1 else 0 with hwydef
  have hpair : (M.natAbs.primeFactors.toList).Pairwise (Function.onFun Nat.Coprime id) := by
    apply List.Nodup.pairwise_of_forall_ne M.natAbs.primeFactors.nodup_toList
    intro a ha b hb hab
    simp only [Finset.mem_toList] at ha hb
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
      (Nat.prime_of_mem_primeFactors hb)).mpr hab
  obtain ⟨kx, hkx⟩ := Nat.chineseRemainderOfList wx id M.natAbs.primeFactors.toList hpair
  obtain ⟨ky, hky⟩ := Nat.chineseRemainderOfList wy id M.natAbs.primeFactors.toList hpair
  refine ⟨(kx:ℤ), (ky:ℤ), coprime_of_all_primes _ M (fun p hp hpM hd => ?_)⟩
  -- A prime divisor of `M` occurs in the finite set used for CRT.
  have hpmem : p ∈ M.natAbs.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, Int.natAbs_ne_zero.mpr hM⟩
    have := Int.natAbs_dvd_natAbs.mpr hpM
    simpa using this
  have hmemL := Finset.mem_toList.mpr hpmem
  -- Read the two CRT congruences in `ℤ`.
  have hkxp : (kx:ℤ) ≡ (wx p : ℤ) [ZMOD (p:ℤ)] := by exact_mod_cast hkx p hmemL
  have hkyp : (ky:ℤ) ≡ (wy p : ℤ) [ZMOD (p:ℤ)] := by exact_mod_cast hky p hmemL
  have hcong := eval_cong f (kx:ℤ) (wx p : ℤ) (ky:ℤ) (wy p : ℤ) (p:ℤ) hkxp hkyp
  -- The chosen value at this prime is nonzero modulo `p`.
  have hwit : ¬ (p:ℤ) ∣ f.eval (wx p : ℤ) (wy p : ℤ) := by
    simp only [hwxdef, hwydef]
    by_cases ha : (p:ℤ) ∣ f.a
    · by_cases hc : (p:ℤ) ∣ f.c
      · simp only [if_pos ha, if_pos hc, Nat.cast_one]
        have hb : ¬ (p:ℤ) ∣ f.b := by
          intro hbd
          have hgg : p ∣ Int.gcd (Int.gcd f.a f.b) f.c :=
            Int.dvd_gcd (by exact_mod_cast Int.dvd_gcd ha hbd) hc
          rw [hf] at hgg; exact absurd (Nat.dvd_one.mp hgg) hp.one_lt.ne'
        intro hd2; apply hb
        have he : f.b = f.eval 1 1 - f.a - f.c := by simp only [BinaryQF.eval]; ring
        rw [he]; exact dvd_sub (dvd_sub hd2 ha) hc
      · simp only [if_pos ha, if_neg hc, Nat.cast_one, Nat.cast_zero]
        simpa [BinaryQF.eval] using hc
    · simp only [if_neg ha, Nat.cast_one, Nat.cast_zero]
      simpa [BinaryQF.eval] using ha
  apply hwit
  have := dvd_add (Int.modEq_iff_dvd.mp hcong) hd
  simpa using this

/-- **Lemma 2.25** (Cox §2, Exercise 2.18). A primitive form `f` properly represents
a value coprime to any nonzero `M`. Divide the coordinates of the CRT construction
by their gcd to obtain a proper representation. -/
theorem lemma_2_25 (f : BinaryQF) (hf : f.Primitive) (M : ℤ) (hM : M ≠ 0) :
    ∃ x y : ℤ, IsCoprime x y ∧ IsCoprime (f.eval x y) M := by
  obtain ⟨x, y, hcop⟩ := exists_eval_coprime f hf M hM
  rcases eq_or_ne (Int.gcd x y) 0 with hg0 | hg0
  · rw [Int.gcd_eq_zero_iff] at hg0
    obtain ⟨hx0, hy0⟩ := hg0; subst hx0; subst hy0
    have h00 : f.eval 0 0 = 0 := by simp [BinaryQF.eval]
    rw [h00] at hcop
    have hu : IsUnit M := isCoprime_zero_left.mp hcop
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    exact ⟨1, 0, isCoprime_one_left, 0, v, by rw [zero_mul, zero_add, mul_comm]; exact hv⟩
  · obtain ⟨x', hx'⟩ := Int.gcd_dvd_left x y
    obtain ⟨y', hy'⟩ := Int.gcd_dvd_right x y
    have hbez : (↑(Int.gcd x y) : ℤ) = x * Int.gcdA x y + y * Int.gcdB x y := Int.gcd_eq_gcd_ab x y
    set d : ℤ := (↑(Int.gcd x y) : ℤ) with hddef
    have hd0 : d ≠ 0 := by rw [hddef]; exact_mod_cast hg0
    refine ⟨x', y', ?_, ?_⟩
    · set A := Int.gcdA x y with hA
      set B := Int.gcdB x y with hB
      have h1 : (1:ℤ) = x' * A + y' * B := by
        apply mul_left_cancel₀ hd0
        linear_combination hbez + A * hx' + B * hy'
      exact ⟨A, B, by linear_combination -h1⟩
    · have hfe : f.eval x y = d ^ 2 * f.eval x' y' := by
        rw [hx', hy']; simp only [BinaryQF.eval]; ring
      rw [hfe] at hcop
      exact (IsCoprime.mul_left_iff.mp hcop).2

/-- **Concordance reduction** (Cox Thm 3.9). For a negative discriminant `D`, any primitive
positive form `g` is properly equivalent to one whose leading coefficient is coprime to `f.a`
as needed for Dirichlet composition. This follows from Lemmas 2.25 and 2.3. -/
theorem concordance (f g : BinaryQF) (D : ℤ) (hD : D < 0)
    (hfa : 0 < f.a) (hg : g.discr = D) (hgp : g.Primitive) (hga : 0 < g.a) :
    ∃ g' : BinaryQF, ProperlyEquivalent g g' ∧ g'.discr = D ∧ g'.Primitive ∧ 0 < g'.a
        ∧ Int.gcd f.a g'.a = 1 := by
  obtain ⟨x, y, hxy, hcopval⟩ := lemma_2_25 g hgp f.a hfa.ne'
  set m := g.eval x y with hm
  have hpr : ProperlyRepresents g m := ⟨x, y, rfl, hxy⟩
  obtain ⟨b', c', heq⟩ := (properlyRepresents_iff_properlyEquivalent g m).mp hpr
  have hne : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h; push_neg at h; obtain ⟨hx0, hy0⟩ := h
    rw [hx0, hy0] at hxy; exact (isCoprime_zero_left.mp hxy).ne_zero rfl
  refine ⟨⟨m, b', c'⟩, heq, ?_, ?_, ?_, ?_⟩
  · rw [← discr_eq_of_properlyEquivalent heq]; exact hg
  · exact (primitive_of_properlyEquivalent heq).mp hgp
  · show 0 < m
    rw [hm]; exact eval_pos_of_posDef g ⟨hga, by rw [hg]; exact hD⟩ x y hne
  · show Int.gcd f.a m = 1
    rw [Int.gcd_comm]; exact Int.isCoprime_iff_gcd_eq_one.mp hcopval

/-- **Gauss composition identity** (Cox §3, (3.1)). For the concordant shapes
`f = ⟨a, B, a'C⟩`, `g = ⟨a', B, aC⟩`, `F = ⟨a a', B, C⟩`, the bilinear substitution
`X = x₁x₂ − C y₁y₂`, `Y = a x₁y₂ + a' x₂y₁ + B y₁y₂` realises `F` as the direct
composition of `f` and `g`: `f(x₁,y₁)·g(x₂,y₂) = F(X,Y)`. -/
theorem dirichlet_compose_repr (a a' B C x₁ y₁ x₂ y₂ : ℤ) :
    (⟨a, B, a' * C⟩ : BinaryQF).eval x₁ y₁ * (⟨a', B, a * C⟩ : BinaryQF).eval x₂ y₂
      = (⟨a * a', B, C⟩ : BinaryQF).eval
          (x₁ * x₂ - C * y₁ * y₂) (a * x₁ * y₂ + a' * x₂ * y₁ + B * y₁ * y₂) := by
  simp only [BinaryQF.eval]; ring

/-- Dirichlet composition on representatives `F, G : DiscrForms D`, for `D < 0`.
Choose a representative `g'` of `G` whose leading coefficient is coprime to `F.a`,
then form `dirichletForm F.1 g'`. Proposition 3.8 gives its primitivity, positivity,
and discriminant. Independence of the choice is proved below in
`concordant_choice_invariant_of_neg`; `composeForm_respects` descends it to classes.
(Cox, Thm 3.9.) -/
noncomputable def composeForm (D : ℤ) (hD : D < 0) (F G : DiscrForms D) : DiscrForms D :=
  let hc := concordance F.1 G.1 D hD F.2.2.2 G.2.1 G.2.2.1 G.2.2.2
  ⟨dirichletForm F.1 hc.choose,
    prop_3_8 F.1 hc.choose D F.2.1 hc.choose_spec.2.1 F.2.2.1 hc.choose_spec.2.2.1
      F.2.2.2 hc.choose_spec.2.2.2.1
      (by rw [hc.choose_spec.2.2.2.2]; simp)⟩

theorem composeForm_discr (D : ℤ) (hD : D < 0) (F G : DiscrForms D) :
    (composeForm D hD F G).1.discr = D := (composeForm D hD F G).2.1

theorem composeForm_primitive (D : ℤ) (hD : D < 0) (F G : DiscrForms D) :
    (composeForm D hD F G).1.Primitive := (composeForm D hD F G).2.2.1

theorem composeForm_pos (D : ℤ) (hD : D < 0) (F G : DiscrForms D) :
    0 < (composeForm D hD F G).1.a := (composeForm D hD F G).2.2.2

/-- The discriminant is unchanged under `b ↦ −b` (the opposite/inverse form). -/
theorem opposite_discr (f : BinaryQF) : f.opposite.discr = f.discr := by
  simp only [BinaryQF.opposite, BinaryQF.discr]; ring

/-- The opposite form is primitive iff the form is (the content `gcd` is unchanged by `b ↦ −b`). -/
theorem opposite_primitive (f : BinaryQF) : f.opposite.Primitive ↔ f.Primitive := by
  simp only [BinaryQF.opposite, BinaryQF.Primitive, Int.gcd]; rw [Int.natAbs_neg]

/-- The opposite form has the same leading coefficient. -/
theorem opposite_pos (f : BinaryQF) : 0 < f.opposite.a ↔ 0 < f.a := by
  simp only [BinaryQF.opposite]

/-- **Translation equivalence.** Two forms `⟨a,b,c⟩`, `⟨a,B,C⟩` with the same nonzero leading
coefficient, the same discriminant, and `B ≡ b (mod 2a)` are properly equivalent — via the
unimodular translation `x ↦ x + t y`, `t = (B-b)/2a`. (Cox §2.) -/
theorem translation_equiv (a b c B C : ℤ) (ha : a ≠ 0) (ht : 2 * a ∣ (B - b))
    (hd : b ^ 2 - 4 * a * c = B ^ 2 - 4 * a * C) :
    ProperlyEquivalent (⟨a, b, c⟩ : BinaryQF) ⟨a, B, C⟩ := by
  obtain ⟨t, htt⟩ := ht
  have hB' : B = b + 2 * a * t := by linarith
  have hC' : a * t ^ 2 + b * t + c = C := by
    have h4 : 4 * a * (a * t ^ 2 + b * t + c) = 4 * a * C := by rw [hB'] at hd; linear_combination -hd
    exact mul_left_cancel₀ (by simp [ha] : (4 * a : ℤ) ≠ 0) h4
  refine ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring, ?_⟩
  simp only [action, BinaryQF.mk.injEq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  exact ⟨by ring, by linarith, by linarith [hC']⟩

/-- **Composing with the principal form is the identity up to proper equivalence.** For any form
`g'` of discriminant `D` with `0 < g'.a`, `dirichletForm (principalForm D) g' ~ g'` (the composite
is a translation of `g'`, since the principal form has leading coefficient `1`). -/
theorem dirichletForm_principal_equiv (D : ℤ) (g' : BinaryQF) (hg : g'.discr = D) (hga : 0 < g'.a) :
    ProperlyEquivalent (dirichletForm (principalForm D) g') g' := by
  have hD4 : D % 4 = 0 ∨ D % 4 = 1 := hg ▸ discr_mod_four g'
  have hpa : (principalForm D).a = 1 := by simp only [principalForm]; split <;> rfl
  have hpd : (principalForm D).discr = D := principalForm_discr D hD4
  have hcop : Int.gcd (Int.gcd (principalForm D).a g'.a) (((principalForm D).b + g'.b) / 2) = 1 := by
    rw [hpa]; simp
  have hBspec : dirichletB (principalForm D) g' ≡ g'.b [ZMOD 2 * g'.a] :=
    dirichletB_spec2 (principalForm D) g' D hpd hg hcop
  have hBsq0 := dirichletB_spec (principalForm D) g' D hpd hg hcop
  rw [hpd, hpa] at hBsq0
  have hBsq : dirichletB (principalForm D) g' ^ 2 ≡ D [ZMOD 4 * g'.a] := by simpa using hBsq0
  set B := dirichletB (principalForm D) g' with hBdef
  have hdvd : (4 * g'.a) ∣ (B ^ 2 - D) := Int.modEq_iff_dvd.mp hBsq.symm
  have hcomp : dirichletForm (principalForm D) g' = ⟨g'.a, B, (B ^ 2 - D) / (4 * g'.a)⟩ := by
    simp only [dirichletForm, hpa, hpd, ← hBdef, one_mul, mul_one]
  rw [hcomp]
  refine properlyEquivalent_equivalence.symm ?_
  have hgeta : g' = (⟨g'.a, g'.b, g'.c⟩ : BinaryQF) := rfl
  rw [hgeta]
  apply translation_equiv g'.a g'.b g'.c B ((B ^ 2 - D) / (4 * g'.a)) hga.ne'
  · exact Int.modEq_iff_dvd.mp hBspec.symm
  · have hmul : 4 * g'.a * ((B ^ 2 - D) / (4 * g'.a)) = B ^ 2 - D := Int.mul_ediv_cancel' hdvd
    have hgd : g'.b ^ 2 - 4 * g'.a * g'.c = D := hg
    rw [hmul]; linarith

/-- Composing a principal-form representative `P` with `F` gives a form properly
equivalent to `F`. The composition is a translation for any chosen concordant
representative. (Cox, Thm 3.9.) -/
theorem composeForm_principal_left (D : ℤ) (hD : D < 0) (F P : DiscrForms D)
    (hP : P.1 = principalForm D) :
    ProperlyEquivalent (composeForm D hD P F).1 F.1 := by
  have hc := concordance P.1 F.1 D hD P.2.2.2 F.2.1 F.2.2.1 F.2.2.2
  have hgd : hc.choose.discr = D := hc.choose_spec.2.1
  have hga : 0 < hc.choose.a := hc.choose_spec.2.2.2.1
  have hgF : ProperlyEquivalent F.1 hc.choose := hc.choose_spec.1
  have key : (composeForm D hD P F).1 = dirichletForm P.1 hc.choose := rfl
  rw [key]
  set g' := hc.choose with hg'def
  rw [hP]
  exact properlyEquivalent_equivalence.trans
    (dirichletForm_principal_equiv D g' hgd hga)
    (properlyEquivalent_equivalence.symm hgF)

/-- A version of `translation_equiv` stated using the coefficient projections:
two forms with equal nonzero leading coefficient, equal discriminant, and
`g.b ≡ f.b (mod 2 f.a)` are properly equivalent. -/
theorem translation_equiv_proj (f g : BinaryQF) (ha : f.a ≠ 0) (haa : f.a = g.a)
    (ht : 2 * f.a ∣ (g.b - f.b)) (hd : f.discr = g.discr) : ProperlyEquivalent f g := by
  obtain ⟨fa, fb, fc⟩ := f
  obtain ⟨ga, gb, gc⟩ := g
  simp only [BinaryQF.discr] at hd
  subst haa
  exact translation_equiv fa fb fc gb gc ha ht hd

/-- A form of discriminant `D` with leading coefficient `1` is properly equivalent to the
principal form (Cox §2 / the `a = 1` case of Exercise 3.7). -/
theorem principal_of_a_one (D : ℤ) (f : BinaryQF) (hd : f.discr = D) (ha : f.a = 1) :
    ProperlyEquivalent f (principalForm D) := by
  have hD4 : D % 4 = 0 ∨ D % 4 = 1 := hd ▸ discr_mod_four f
  have hpa : (principalForm D).a = 1 := by simp only [principalForm]; split <;> rfl
  have hpd : (principalForm D).discr = D := principalForm_discr D hD4
  have hfd : f.b ^ 2 - 4 * f.a * f.c = D := hd
  have hppd : (principalForm D).b ^ 2 - 4 * (principalForm D).a * (principalForm D).c = D := hpd
  have h4 : (4 : ℤ) ∣ (f.b ^ 2 - (principalForm D).b ^ 2) :=
    ⟨f.c - (principalForm D).c, by rw [ha, hpa] at *; linarith⟩
  have hpar : (2 : ℤ) ∣ ((principalForm D).b - f.b) := by
    obtain ⟨k, hk⟩ := two_dvd_sub_of_four_dvd_sq_sub_sq f.b (principalForm D).b h4
    exact ⟨-k, by linarith⟩
  apply translation_equiv_proj f (principalForm D) (by rw [ha]; norm_num) (ha.trans hpa.symm)
  · rw [ha]; simpa using hpar
  · rw [hd, hpd]

-- Independence of the concordant representative is proved below as
-- `concordant_choice_invariant_of_neg`. Its hypothesis `D < 0` comes from Cox's
-- Theorem 3.9 and supplies the nonzero discriminant needed for the minor relations
-- of Exercise 3.1; see the counterexample at `directlyComposes_minors`.
-- This replaces an earlier statement that omitted the discriminant hypothesis.

/-- **Direct composition** (Cox §3.A, (3.1)). `F` is the *direct composition* of `f` and `g`
if there is an integral bilinear substitution `Bᵢ = aᵢxz+bᵢxw+cᵢyz+dᵢyw` with
`f(x,y)·g(z,w) = F(B₁,B₂)`, whose leading-coefficient minors take the `+` sign of Gauss's
formulas (3.1): `a₁b₂−a₂b₁ = f(1,0)`, `a₁c₂−a₂c₁ = g(1,0)`. The definition uses only the
values of the forms, so it is independent of how their coefficients are stored. -/
def DirectlyComposes (f g F : BinaryQF) : Prop :=
  ∃ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ,
    (∀ x y z w : ℤ, f.eval x y * g.eval z w
      = F.eval (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
               (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w))
    ∧ a₁ * b₂ - a₂ * b₁ = f.eval 1 0
    ∧ a₁ * c₂ - a₂ * c₁ = g.eval 1 0

/-- **Cox 3.5(d) (concordant-shape).** The Gauss composite of the concordant forms
`⟨a,B,a'C⟩`, `⟨a',B,aC⟩` is their *direct* composition `⟨aa',B,C⟩` (the `+` sign of (3.1) holds).
The substitution is `(1,0,0,-C ; 0,a,a',B)`, with identity `dirichlet_compose_repr`.
The extension to arbitrary concordant forms uses `translation_equiv` and
`directlyComposes_of_properlyEquivalent_left` (Cox 3.5(c), below). -/
theorem dirichletForm_directlyComposes_concordant (a a' B C : ℤ) :
    DirectlyComposes (⟨a, B, a' * C⟩ : BinaryQF) ⟨a', B, a * C⟩ ⟨a * a', B, C⟩ :=
  ⟨1, 0, 0, -C, 0, a, a', B,
    fun x y z w => by simp only [BinaryQF.eval]; ring,
    by simp only [BinaryQF.eval]; ring,
    by simp only [BinaryQF.eval]; ring⟩

/-- A form and its opposite directly compose to the discriminant-preserving form
`⟨1, b, ac⟩`. Its leading coefficient is `1`, so `principal_of_a_one` identifies its class
with the principal class. This is the norm identity underlying the inverse in Cox Theorem 3.9. -/
theorem directlyComposes_opposite_one (f : BinaryQF) :
    DirectlyComposes f f.opposite (⟨1, f.b, f.a * f.c⟩ : BinaryQF) := by
  refine ⟨f.a, -f.b, 0, -f.c, 0, 1, 1, 0, ?_, ?_, ?_⟩
  · intro x y z w
    simp only [BinaryQF.eval, BinaryQF.opposite]
    ring
  · simp only [BinaryQF.eval]
    ring
  · simp only [BinaryQF.eval, BinaryQF.opposite]
    ring

/-- **Commutativity of Dirichlet composition up to proper equivalence.** `dirichletForm f g ~
dirichletForm g f`: the two composites have equal leading coefficient `f.a·g.a` and their
`B`-values agree modulo `2 f.a g.a` by the uniqueness in Lemma 3.2. A translation
therefore identifies the two forms. This symmetry is used to prove that composition
respects proper equivalence in both arguments. -/
theorem dirichletForm_comm_equiv (f g : BinaryQF) (D : ℤ) (hf : f.discr = D) (hg : g.discr = D)
    (hfa : 0 < f.a) (hga : 0 < g.a)
    (hcop_fg : Int.gcd (Int.gcd f.a g.a) ((f.b + g.b) / 2) = 1)
    (hcop_gf : Int.gcd (Int.gcd g.a f.a) ((g.b + f.b) / 2) = 1) :
    ProperlyEquivalent (dirichletForm f g) (dirichletForm g f) := by
  obtain ⟨B₀, _, _, _, huniq⟩ := lemma_3_2 f.a f.b f.c g.a g.b g.c D hf hg hcop_fg
  have hfg : dirichletB f g ≡ B₀ [ZMOD 2 * f.a * g.a] := by
    refine huniq _ ⟨dirichletB_spec1 f g D hf hg hcop_fg, dirichletB_spec2 f g D hf hg hcop_fg, ?_⟩
    have := dirichletB_spec f g D hf hg hcop_fg; rwa [hf] at this
  have hgf : dirichletB g f ≡ B₀ [ZMOD 2 * f.a * g.a] := by
    refine huniq _ ⟨dirichletB_spec2 g f D hg hf hcop_gf, dirichletB_spec1 g f D hg hf hcop_gf, ?_⟩
    have := dirichletB_spec g f D hg hf hcop_gf
    rw [hg] at this; rwa [show (4 * g.a * f.a : ℤ) = 4 * f.a * g.a from by ring] at this
  have hBcong : dirichletB f g ≡ dirichletB g f [ZMOD 2 * f.a * g.a] := hfg.trans hgf.symm
  apply translation_equiv_proj (dirichletForm f g) (dirichletForm g f)
  · show f.a * g.a ≠ 0; exact mul_ne_zero hfa.ne' hga.ne'
  · show f.a * g.a = g.a * f.a; ring
  · show 2 * (f.a * g.a) ∣ (dirichletB g f - dirichletB f g)
    rw [show 2 * (f.a * g.a) = 2 * f.a * g.a from by ring]; exact Int.modEq_iff_dvd.mp hBcong
  · rw [dirichletForm_discr f g D hf hg hcop_fg, dirichletForm_discr g f D hg hf hcop_gf]

/-- **Gauss' minor relations (Cox Exercise 3.1 / [Gauss §235]).** If `G` is a direct composition
of `h` and `k` with bilinear coefficients `a₁ … d₂` — the `+` sign `a₁b₂−a₂b₁ = h.a` of (3.1)
holding — and the two forms `k`, `G` share a **nonzero** discriminant, then the remaining Gauss
minors satisfy `(a₁d₂−a₂d₁)−(b₁c₂−b₂c₁) = h.b` and `c₁d₂−c₂d₁ = h.c`.

The nonzero-discriminant hypothesis is essential, as in Cox's Exercise 3.1. The
degenerate `h=k=G=⟨1,0,0⟩` with witness
`(1,0,0,0,0,1,1,5)` is a direct composition for which `(a₁d₂−a₂d₁)−(b₁c₂−b₂c₁)=5≠0=h.b`.

Viewing the composition identity as a form in `(z,w)` gives, for every `x,y`, the
discriminant identity `(h(x,y))²·disc k = Ψ(x,y)²·disc G` with `Ψ = (a₁b₂−a₂b₁)x² +
((a₁d₂−a₂d₁)−(b₁c₂−b₂c₁))xy + (c₁d₂−c₂d₁)y²` (Cox 3.1(a),(b)); cancelling the common nonzero
discriminant yields `h(x,y)² = Ψ(x,y)²` as a polynomial identity, and comparing the `x³y`- and
`x²y²`-coefficients (evaluating at `x∈{−2,…,2}, y=1`) determines the two minors. The
sign is fixed by `a₁b₂−a₂b₁ = h.a`. -/
theorem directlyComposes_minors (h k G : BinaryQF) (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (hid : ∀ x y z w : ℤ, h.eval x y * k.eval z w
      = G.eval (a₁*x*z+b₁*x*w+c₁*y*z+d₁*y*w) (a₂*x*z+b₂*x*w+c₂*y*z+d₂*y*w))
    (hsign : a₁*b₂ - a₂*b₁ = h.a)
    (hha : h.a ≠ 0) (hkG : k.discr = G.discr) (hG0 : G.discr ≠ 0) :
    ((a₁*d₂-a₂*d₁) - (b₁*c₂-b₂*c₁) = h.b) ∧ (c₁*d₂-c₂*d₁ = h.c) := by
  have hD' : ∀ x y : ℤ, (h.eval x y)^2 * k.discr
      = ((a₁*b₂-a₂*b₁)*x^2 + ((a₁*d₂-a₂*d₁)-(b₁*c₂-b₂*c₁))*x*y + (c₁*d₂-c₂*d₁)*y^2)^2 * G.discr := by
    intro x y
    have hka : h.eval x y * k.a = G.eval (a₁*x+c₁*y) (a₂*x+c₂*y) := by
      have hh := hid x y 1 0; simp only [BinaryQF.eval] at hh ⊢; linear_combination hh
    have hkc : h.eval x y * k.c = G.eval (b₁*x+d₁*y) (b₂*x+d₂*y) := by
      have hh := hid x y 0 1; simp only [BinaryQF.eval] at hh ⊢; linear_combination hh
    have qall : h.eval x y * (k.a+k.b+k.c) = G.eval ((a₁+b₁)*x+(c₁+d₁)*y) ((a₂+b₂)*x+(c₂+d₂)*y) := by
      have hh := hid x y 1 1; simp only [BinaryQF.eval] at hh ⊢; linear_combination hh
    have expand : (h.eval x y)^2 * k.discr
        = (h.eval x y * (k.a+k.b+k.c) - h.eval x y * k.a - h.eval x y * k.c)^2
          - 4*(h.eval x y * k.a)*(h.eval x y * k.c) := by
      simp only [BinaryQF.discr]; ring
    rw [expand, qall, hka, hkc]
    simp only [BinaryQF.eval, BinaryQF.discr]; ring
  have key2 : ∀ x y : ℤ, (h.eval x y)^2
      = ((a₁*b₂-a₂*b₁)*x^2 + ((a₁*d₂-a₂*d₁)-(b₁*c₂-b₂*c₁))*x*y + (c₁*d₂-c₂*d₁)*y^2)^2 := by
    intro x y
    have := hD' x y; rw [hkG] at this; exact mul_right_cancel₀ hG0 this
  have k0 := key2 0 1; have k1 := key2 1 1; have km1 := key2 (-1) 1
  have k2 := key2 2 1; have km2 := key2 (-2) 1
  simp only [BinaryQF.eval] at k0 k1 km1 k2 km2
  have h24 : (24:ℤ)*h.a ≠ 0 := mul_ne_zero (by norm_num) hha
  have c3 : 24*h.a*h.b = 24*(a₁*b₂-a₂*b₁)*((a₁*d₂-a₂*d₁)-(b₁*c₂-b₂*c₁)) := by
    linear_combination (-km2) + 2*km1 - 2*k1 + k2
  rw [hsign] at c3
  have hbe : (24*h.a)*h.b = (24*h.a)*((a₁*d₂-a₂*d₁)-(b₁*c₂-b₂*c₁)) := by linear_combination c3
  have hbeq : h.b = (a₁*d₂-a₂*d₁)-(b₁*c₂-b₂*c₁) := mul_left_cancel₀ h24 hbe
  refine ⟨hbeq.symm, ?_⟩
  have c2 : 24*(h.b^2+2*h.a*h.c)
      = 24*(((a₁*d₂-a₂*d₁)-(b₁*c₂-b₂*c₁))^2 + 2*(a₁*b₂-a₂*b₁)*(c₁*d₂-c₂*d₁)) := by
    linear_combination 16*k1 + 16*km1 - 30*k0 - k2 - km2
  rw [hsign, ← hbeq] at c2
  have h48 : (48:ℤ)*h.a ≠ 0 := mul_ne_zero (by norm_num) hha
  have hce : (48*h.a)*h.c = (48*h.a)*(c₁*d₂-c₂*d₁) := by linear_combination c2
  exact (mul_left_cancel₀ h48 hce).symm

/-- **Cox 3.5(c) — representative-invariance of direct composition (discriminant version).**
If `G` is the direct composition of `h` and `k`, `h` is properly equivalent to `h'`, and the
forms have the nonzero common discriminant of Cox's setting (`h.a ≠ 0`, `k.discr = G.discr ≠ 0`),
then `G` is also the direct composition of `h'` and `k`.

Cox's §3.A works with primitive positive definite forms of fixed discriminant
`D < 0`, so the hypotheses hold there. Pre-compose the bilinear substitution with
the `SL₂(ℤ)` matrix `M` carrying `h` to `h'`; the new coefficients include
`āᵢ = aᵢ·M₀₀ + cᵢ·M₁₀`. The determinant condition preserves the `k`-side sign in
(3.1). For the `h`-side sign, `directlyComposes_minors` identifies the new minor
with `M₀₀²·h.a + M₀₀M₁₀·h.b + M₁₀²·h.c = h'(1,0)`. -/
theorem directlyComposes_of_properlyEquivalent_left_of_discr (h k G h' : BinaryQF)
    (hDC : DirectlyComposes h k G) (he : ProperlyEquivalent h h')
    (hha : h.a ≠ 0) (hkG : k.discr = G.discr) (hG0 : G.discr ≠ 0) :
    DirectlyComposes h' k G := by
  obtain ⟨a₁, b₁, c₁, d₁, a₂, b₂, c₂, d₂, hid, hb, hc⟩ := hDC
  obtain ⟨M, hdet, hM⟩ := he
  have hsign : a₁*b₂ - a₂*b₁ = h.a := by rw [hb]; simp [BinaryQF.eval]
  obtain ⟨hbmin, hcmin⟩ := directlyComposes_minors h k G a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ hid hsign hha hkG hG0
  have hdet2 : M 0 0*M 1 1 - M 0 1*M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  refine ⟨a₁*(M 0 0)+c₁*(M 1 0), b₁*(M 0 0)+d₁*(M 1 0), a₁*(M 0 1)+c₁*(M 1 1), b₁*(M 0 1)+d₁*(M 1 1),
          a₂*(M 0 0)+c₂*(M 1 0), b₂*(M 0 0)+d₂*(M 1 0), a₂*(M 0 1)+c₂*(M 1 1), b₂*(M 0 1)+d₂*(M 1 1),
          ?_, ?_, ?_⟩
  · intro x y z w
    rw [← hM, eval_action]
    have := hid (M 0 0*x+M 0 1*y) (M 1 0*x+M 1 1*y) z w
    rw [this]; congr 1 <;> ring
  · rw [← hM, eval_action]; simp only [BinaryQF.eval]
    linear_combination (M 0 0^2)*hsign + (M 0 0*M 1 0)*hbmin + (M 1 0^2)*hcmin
  · linear_combination (M 0 0*M 1 1 - M 0 1*M 1 0)*hc + (k.eval 1 0)*hdet2

/-- **Gauss' minor relations in the second argument (Cox Exercise 3.1 / [Gauss §235]).**
The companion
of `directlyComposes_minors`: reading the composition identity as a form in `(x,y)` (rather than
`(z,w)`) gives `(k(z,w))²·disc h = Φ(z,w)²·disc G` with `Φ = m₁₃·z² + (m₁₄+m₂₃)·zw + m₂₄·w²`;
cancelling the common nonzero discriminant and comparing coefficients determines the
remaining two minors. Here `m₁₄+m₂₃ = k.b`, whereas `m₁₄−m₂₃ = h.b` in the first
argument. The cancelled discriminant is `disc h`.

Together with `directlyComposes_minors` and the two `(3.1)` sign conditions, this completes the
Plücker vector: all six `2×2` minors of the substitution matrix are determined by `(h,k)` alone —
`m₁₂ = h.a`, `m₁₃ = k.a`, `m₁₄ = (h.b+k.b)/2`, `m₂₃ = (k.b−h.b)/2`, `m₂₄ = k.c`, `m₃₄ = h.c`. -/
theorem directlyComposes_minors_right (h k G : BinaryQF) (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (hid : ∀ x y z w : ℤ, h.eval x y * k.eval z w
      = G.eval (a₁*x*z+b₁*x*w+c₁*y*z+d₁*y*w) (a₂*x*z+b₂*x*w+c₂*y*z+d₂*y*w))
    (hsign : a₁*c₂ - a₂*c₁ = k.a)
    (hka : k.a ≠ 0) (hhG : h.discr = G.discr) (hG0 : G.discr ≠ 0) :
    ((a₁*d₂-a₂*d₁) + (b₁*c₂-b₂*c₁) = k.b) ∧ (b₁*d₂-b₂*d₁ = k.c) := by
  have hD' : ∀ z w : ℤ, (k.eval z w)^2 * h.discr
      = ((a₁*c₂-a₂*c₁)*z^2 + ((a₁*d₂-a₂*d₁)+(b₁*c₂-b₂*c₁))*z*w + (b₁*d₂-b₂*d₁)*w^2)^2 * G.discr := by
    intro z w
    have hha : k.eval z w * h.a = G.eval (a₁*z+b₁*w) (a₂*z+b₂*w) := by
      have hh := hid 1 0 z w; simp only [BinaryQF.eval] at hh ⊢; linear_combination hh
    have hhc : k.eval z w * h.c = G.eval (c₁*z+d₁*w) (c₂*z+d₂*w) := by
      have hh := hid 0 1 z w; simp only [BinaryQF.eval] at hh ⊢; linear_combination hh
    have qall : k.eval z w * (h.a+h.b+h.c)
        = G.eval ((a₁+c₁)*z+(b₁+d₁)*w) ((a₂+c₂)*z+(b₂+d₂)*w) := by
      have hh := hid 1 1 z w; simp only [BinaryQF.eval] at hh ⊢; linear_combination hh
    have expand : (k.eval z w)^2 * h.discr
        = (k.eval z w * (h.a+h.b+h.c) - k.eval z w * h.a - k.eval z w * h.c)^2
          - 4*(k.eval z w * h.a)*(k.eval z w * h.c) := by
      simp only [BinaryQF.discr]; ring
    rw [expand, qall, hha, hhc]
    simp only [BinaryQF.eval, BinaryQF.discr]; ring
  have key2 : ∀ z w : ℤ, (k.eval z w)^2
      = ((a₁*c₂-a₂*c₁)*z^2 + ((a₁*d₂-a₂*d₁)+(b₁*c₂-b₂*c₁))*z*w + (b₁*d₂-b₂*d₁)*w^2)^2 := by
    intro z w
    have := hD' z w; rw [hhG] at this; exact mul_right_cancel₀ hG0 this
  have k0 := key2 0 1; have k1 := key2 1 1; have km1 := key2 (-1) 1
  have k2 := key2 2 1; have km2 := key2 (-2) 1
  simp only [BinaryQF.eval] at k0 k1 km1 k2 km2
  have h24 : (24:ℤ)*k.a ≠ 0 := mul_ne_zero (by norm_num) hka
  have c3 : 24*k.a*k.b = 24*(a₁*c₂-a₂*c₁)*((a₁*d₂-a₂*d₁)+(b₁*c₂-b₂*c₁)) := by
    linear_combination (-km2) + 2*km1 - 2*k1 + k2
  rw [hsign] at c3
  have hbe : (24*k.a)*k.b = (24*k.a)*((a₁*d₂-a₂*d₁)+(b₁*c₂-b₂*c₁)) := by linear_combination c3
  have hbeq : k.b = (a₁*d₂-a₂*d₁)+(b₁*c₂-b₂*c₁) := mul_left_cancel₀ h24 hbe
  refine ⟨hbeq.symm, ?_⟩
  have c2 : 24*(k.b^2+2*k.a*k.c)
      = 24*(((a₁*d₂-a₂*d₁)+(b₁*c₂-b₂*c₁))^2 + 2*(a₁*c₂-a₂*c₁)*(b₁*d₂-b₂*d₁)) := by
    linear_combination 16*k1 + 16*km1 - 30*k0 - k2 - km2
  rw [hsign, ← hbeq] at c2
  have h48 : (48:ℤ)*k.a ≠ 0 := mul_ne_zero (by norm_num) hka
  have hce : (48*k.a)*k.c = (48*k.a)*(b₁*d₂-b₂*d₁) := by linear_combination c2
  exact (mul_left_cancel₀ h48 hce).symm

/-- Componentwise extensionality for `BinaryQF`. -/
theorem binaryQF_ext (p q : BinaryQF) (h1 : p.a = q.a) (h2 : p.b = q.b) (h3 : p.c = q.c) : p = q := by
  obtain ⟨pa,pb,pc⟩ := p; obtain ⟨qa,qb,qc⟩ := q; simp_all

/-- **Cox 3.5(c) — representative-invariance of direct composition.** If `G` is the direct
composition of `h` and `k`, and `h` is properly equivalent to `h'`, then `G` is also the direct
composition of `h'` and `k`.

The nonzero-discriminant hypotheses come from Cox's Exercise 3.1; the example at
`directlyComposes_minors` explains why they cannot be omitted. They hold for the
primitive positive definite forms in §3.A. This is a specialization of
`directlyComposes_of_properlyEquivalent_left_of_discr`. -/
theorem directlyComposes_of_properlyEquivalent_left (h k G h' : BinaryQF)
    (hDC : DirectlyComposes h k G) (he : ProperlyEquivalent h h')
    (hha : h.a ≠ 0) (hkG : k.discr = G.discr) (hG0 : G.discr ≠ 0) :
    DirectlyComposes h' k G :=
  directlyComposes_of_properlyEquivalent_left_of_discr h k G h' hDC he hha hkG hG0

/-- **Uniqueness of direct composition up to proper equivalence** (Cox 4b / [Gauss §§236–240];
Cox defers this result to §7 in the proof of Theorem 3.9).

Two direct compositions `F`, `F'` of the same pair `(f,g)` of discriminant `D < 0` with
`gcd(f.a, g.a) = 1` are properly equivalent.

By `directlyComposes_minors` and `directlyComposes_minors_right`, all six minors of
the substitution matrix are determined by `(f,g)`. The two witnesses `M`, `M'`
therefore have identical Plücker vectors (in particular
`m₂₃ = m₂₃'`, obtained by halving `(m₁₄+m₂₃) − (m₁₄−m₂₃) = g.b − f.b`). Setting `y = 0` collapses
the composition identity onto the first two columns, so it suffices to produce `S` with `S·T = T'`
for `T = !![a₁,b₁;a₂,b₂]` (`det T = m₁₂ = f.a`). Bézout `u·f.a + v·g.a = 1` gives the *integral*
`S := u·(T'·adj T) + v·(U'·adj U)` (`U` = columns 1,3, `det U = m₁₃ = g.a`); the four identities
`S·T = T'` follow from the sign conditions, `m₂₃ = m₂₃'` and the Plücker/Cramer relation
`m₂₃'·p₁ − m₁₃'·q₁ + m₁₂'·r₁ = 0`. Then `det S · f.a = f.a` forces `det S = 1`, and
`E := F − action S F'` vanishes at `(a₁,a₂)`, `(b₁,b₂)`, `(a₁+b₁,a₂+b₂)`, whose Cramer combination
gives `f.a²·E = 0`, hence `E = 0` and `action S F' = F`. -/
theorem directlyComposes_unique_of_coprime (f g F F' : BinaryQF) (D : ℤ)
    (hD : D < 0) (hf : f.discr = D) (hg : g.discr = D) (hcop : IsCoprime f.a g.a)
    (hF : DirectlyComposes f g F) (hFd : F.discr = D)
    (hF' : DirectlyComposes f g F') (hF'd : F'.discr = D) :
    ProperlyEquivalent F F' := by
  have hD0 : D ≠ 0 := ne_of_lt hD
  have hfa : f.a ≠ 0 := by
    intro h0
    have hb : f.discr = f.b^2 := by simp [BinaryQF.discr, h0]
    rw [hf] at hb; nlinarith [sq_nonneg f.b]
  have hga : g.a ≠ 0 := by
    intro h0
    have hb : g.discr = g.b^2 := by simp [BinaryQF.discr, h0]
    rw [hg] at hb; nlinarith [sq_nonneg g.b]
  obtain ⟨a₁,b₁,c₁,d₁,a₂,b₂,c₂,d₂, hid, hsb, hsc⟩ := hF
  obtain ⟨p₁,q₁,r₁,s₁,p₂,q₂,r₂,s₂, hid', hsb', hsc'⟩ := hF'
  have hm12 : a₁*b₂ - a₂*b₁ = f.a := by rw [hsb]; simp [BinaryQF.eval]
  have hm13 : a₁*c₂ - a₂*c₁ = g.a := by rw [hsc]; simp [BinaryQF.eval]
  have hm12' : p₁*q₂ - p₂*q₁ = f.a := by rw [hsb']; simp [BinaryQF.eval]
  have hm13' : p₁*r₂ - p₂*r₁ = g.a := by rw [hsc']; simp [BinaryQF.eval]
  have hgF : g.discr = F.discr := by rw [hg, hFd]
  have hfF : f.discr = F.discr := by rw [hf, hFd]
  have hF0 : F.discr ≠ 0 := by rw [hFd]; exact hD0
  have hgF' : g.discr = F'.discr := by rw [hg, hF'd]
  have hfF' : f.discr = F'.discr := by rw [hf, hF'd]
  have hF'0 : F'.discr ≠ 0 := by rw [hF'd]; exact hD0
  obtain ⟨hL1, _⟩ := directlyComposes_minors f g F a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ hid hm12 hfa hgF hF0
  obtain ⟨hR1, _⟩ := directlyComposes_minors_right f g F a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ hid hm13 hga hfF hF0
  obtain ⟨hL1', _⟩ := directlyComposes_minors f g F' p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ hid' hm12' hfa hgF' hF'0
  obtain ⟨hR1', _⟩ :=
    directlyComposes_minors_right f g F' p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ hid' hm13' hga hfF' hF'0
  have hm23 : b₁*c₂ - b₂*c₁ = q₁*r₂ - q₂*r₁ := by linarith [hL1, hR1, hL1', hR1']
  obtain ⟨u, v, huv⟩ := hcop
  set S00 := u*(p₁*b₂ - q₁*a₂) + v*(p₁*c₂ - r₁*a₂) with hS00def
  set S01 := u*(q₁*a₁ - p₁*b₁) + v*(r₁*a₁ - p₁*c₁) with hS01def
  set S10 := u*(p₂*b₂ - q₂*a₂) + v*(p₂*c₂ - r₂*a₂) with hS10def
  set S11 := u*(q₂*a₁ - p₂*b₁) + v*(r₂*a₁ - p₂*c₁) with hS11def
  have G1 : S00*a₁ + S01*a₂ = p₁ := by
    rw [hS00def, hS01def]
    linear_combination (u*p₁)*hm12 + (v*p₁)*hm13 + p₁*huv
  have G2 : S10*a₁ + S11*a₂ = p₂ := by
    rw [hS10def, hS11def]
    linear_combination (u*p₂)*hm12 + (v*p₂)*hm13 + p₂*huv
  have G3 : S00*b₁ + S01*b₂ = q₁ := by
    rw [hS00def, hS01def]
    linear_combination (u*q₁ + v*r₁)*hm12 + (v*p₁)*hm23 + q₁*huv - (v*r₁)*hm12' + (v*q₁)*hm13'
  have G4 : S10*b₁ + S11*b₂ = q₂ := by
    rw [hS10def, hS11def]
    linear_combination (u*q₂ + v*r₂)*hm12 + (v*p₂)*hm23 + q₂*huv - (v*r₂)*hm12' + (v*q₂)*hm13'
  have hkey : (S00*S11 - S01*S10) * f.a = f.a := by
    calc (S00*S11 - S01*S10) * f.a
        = (S00*S11 - S01*S10) * (a₁*b₂ - a₂*b₁) := by rw [hm12]
      _ = p₁*q₂ - p₂*q₁ := by rw [← G1, ← G2, ← G3, ← G4]; ring
      _ = f.a := hm12'
  have hdet1 : S00*S11 - S01*S10 = 1 :=
    mul_right_cancel₀ hfa (hkey.trans (one_mul f.a).symm)
  refine properlyEquivalent_equivalence.symm ⟨!![S00, S01; S10, S11], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; exact hdet1
  · have hM00 : (!![S00, S01; S10, S11] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = S00 := rfl
    have hM01 : (!![S00, S01; S10, S11] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = S01 := rfl
    have hM10 : (!![S00, S01; S10, S11] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = S10 := rfl
    have hM11 : (!![S00, S01; S10, S11] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = S11 := rfl
    have hEval : ∀ z w : ℤ,
        (action (!![S00, S01; S10, S11] : Matrix (Fin 2) (Fin 2) ℤ) F').eval
            (a₁*z + b₁*w) (a₂*z + b₂*w)
          = F.eval (a₁*z + b₁*w) (a₂*z + b₂*w) := by
      intro z w
      rw [eval_action, hM00, hM01, hM10, hM11]
      have harg1 : S00*(a₁*z + b₁*w) + S01*(a₂*z + b₂*w) = p₁*z + q₁*w := by
        linear_combination z*G1 + w*G3
      have harg2 : S10*(a₁*z + b₁*w) + S11*(a₂*z + b₂*w) = p₂*z + q₂*w := by
        linear_combination z*G2 + w*G4
      rw [harg1, harg2]
      have e1 := hid' 1 0 z w
      have e2 := hid 1 0 z w
      simp only [BinaryQF.eval] at e1 e2 ⊢
      linear_combination e2 - e1
    set H := action (!![S00, S01; S10, S11] : Matrix (Fin 2) (Fin 2) ℤ) F' with hHdef
    have E1 := hEval 1 0
    have E2 := hEval 0 1
    have E3 := hEval 1 1
    simp only [BinaryQF.eval] at E1 E2 E3
    have eq1 : (F.a - H.a)*a₁^2 + (F.b - H.b)*a₁*a₂ + (F.c - H.c)*a₂^2 = 0 := by
      linear_combination -E1
    have eq2 : (F.a - H.a)*b₁^2 + (F.b - H.b)*b₁*b₂ + (F.c - H.c)*b₂^2 = 0 := by
      linear_combination -E2
    have eq3 : 2*(F.a - H.a)*a₁*b₁ + (F.b - H.b)*(a₁*b₂ + a₂*b₁) + 2*(F.c - H.c)*a₂*b₂ = 0 := by
      linear_combination -E3 - eq1 - eq2
    have hfa2 : f.a^2 ≠ 0 := pow_ne_zero 2 hfa
    have hA : f.a^2 * (F.a - H.a) = 0 := by
      rw [← hm12]; linear_combination b₂^2*eq1 + a₂^2*eq2 - a₂*b₂*eq3
    have hB : f.a^2 * (F.b - H.b) = 0 := by
      rw [← hm12]
      linear_combination (-2*b₁*b₂)*eq1 + (-2*a₁*a₂)*eq2 + (a₁*b₂ + a₂*b₁)*eq3
    have hC : f.a^2 * (F.c - H.c) = 0 := by
      rw [← hm12]; linear_combination b₁^2*eq1 + a₁^2*eq2 - a₁*b₁*eq3
    have hAa : F.a = H.a := by have := (mul_eq_zero.mp hA).resolve_left hfa2; linarith
    have hBb : F.b = H.b := by have := (mul_eq_zero.mp hB).resolve_left hfa2; linarith
    have hCc : F.c = H.c := by have := (mul_eq_zero.mp hC).resolve_left hfa2; linarith
    exact (binaryQF_ext F H hAa hBb hCc).symm

/-- **Uniqueness of direct composition up to proper equivalence** (Cox 4b). Two direct
compositions of the same pair are properly equivalent.

The hypotheses `D < 0` and `gcd(f.a,g.a)=1` are explicit here. Cox's §3.A works
with negative discriminants and, in the proof of Theorem 3.9, replaces `g` by a
properly equivalent form with coprime leading coefficient. Nonzero discriminant
is needed for the minor relations (see `directlyComposes_minors`); coprimality
makes the transition matrix integral by Bézout. No primitivity or positivity
assumption on `F` is needed. The proof is `directlyComposes_unique_of_coprime`. -/
theorem directlyComposes_unique (f g F F' : BinaryQF) (D : ℤ)
    (hD : D < 0) (hcop : IsCoprime f.a g.a)
    (hf : f.discr = D) (hg : g.discr = D)
    (hF : DirectlyComposes f g F) (hFd : F.discr = D)
    (hF' : DirectlyComposes f g F') (hF'd : F'.discr = D) :
    ProperlyEquivalent F F' :=
  directlyComposes_unique_of_coprime f g F F' D hD hf hg hcop hF hFd hF' hF'd



/-- **Lemma 2.5.** For `D ≡ 0,1 (mod 4)` and odd `m` prime to `D`, `m` is properly
represented by a primitive form of discriminant `D` iff `D` is a quadratic
residue mod `m`. (Cox §2; the general odd-`m` form of which
`properlyRepresents_iff_isSquare` is the prime case.) -/
private theorem represents_of_properlyEquivalent' {f g : BinaryQF} (h : ProperlyEquivalent f g)
    (m : ℤ) (hf : Represents f m) : Represents g m := by
  obtain ⟨M, hdet, rfl⟩ := h
  obtain ⟨x, y, hxy⟩ := hf
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet; linarith
  refine ⟨M 1 1 * x - M 0 1 * y, -(M 1 0) * x + M 0 0 * y, ?_⟩
  rw [eval_action]
  have e1 : M 0 0 * (M 1 1 * x - M 0 1 * y) + M 0 1 * (-(M 1 0) * x + M 0 0 * y) = x := by
    linear_combination x * hd
  have e2 : M 1 0 * (M 1 1 * x - M 0 1 * y) + M 1 1 * (-(M 1 0) * x + M 0 0 * y) = y := by
    linear_combination y * hd
  rw [e1, e2]; exact hxy

/-- Exercise 2.1, repeated here because `Exercises/S2.lean` imports this file:
every represented integer is a square times a properly represented integer. -/
private theorem rep_eq_sq_mul' (f : BinaryQF) (m : ℤ) (h : Represents f m) :
    ∃ d m' : ℤ, m = d ^ 2 * m' ∧ ProperlyRepresents f m' := by
  obtain ⟨x, y, hxy⟩ := h
  by_cases hxy0 : x = 0 ∧ y = 0
  · obtain ⟨hx0, hy0⟩ := hxy0
    subst hx0; subst hy0
    have hm : m = 0 := by rw [← hxy]; simp [BinaryQF.eval]
    exact ⟨0, f.eval 1 0, by rw [hm]; ring, 1, 0, rfl, isCoprime_one_left⟩
  · have hg : 0 < Int.gcd x y :=
      Nat.pos_of_ne_zero (fun hz => hxy0 (Int.gcd_eq_zero_iff.mp hz))
    obtain ⟨x', y', hcop, hx, hy⟩ := Int.exists_gcd_one hg
    set g : ℤ := (Int.gcd x y : ℤ) with hgdef
    refine ⟨g, f.eval x' y', ?_, x', y', rfl, ?_⟩
    · have hme : m = f.eval (x' * g) (y' * g) := by rw [← hx, ← hy]; exact hxy.symm
      rw [hme]; simp only [BinaryQF.eval]; ring
    · exact Int.isCoprime_iff_gcd_eq_one.mpr hcop

/-- If a form of discriminant `D` properly represents a natural number `p`, then
`D` is a square mod `p`. Primality and parity assumptions are unnecessary. -/
private theorem isSquare_of_properlyRepresents' (D : ℤ) (p : ℕ) (f : BinaryQF)
    (hdiscr : f.discr = D) (hrep : ProperlyRepresents f (p : ℤ)) :
    IsSquare (D : ZMod p) := by
  obtain ⟨B, C, hBC⟩ := (properlyRepresents_iff_properlyEquivalent f (p : ℤ)).mp hrep
  have hdBC := discr_eq_of_properlyEquivalent hBC
  rw [hdiscr] at hdBC
  simp only [BinaryQF.discr] at hdBC
  refine ⟨(B : ZMod p), ?_⟩
  have hcast := congrArg (fun t : ℤ => (t : ZMod p)) hdBC
  push_cast at hcast
  rw [ZMod.natCast_self] at hcast
  rw [hcast]
  ring

/-- If a form of discriminant `D` represents a prime `p`, then `D` is a square mod `p`. -/
private theorem isSquare_of_represents' (D : ℤ) (p : ℕ) (hp : p.Prime) (f : BinaryQF)
    (hdiscr : f.discr = D) (hrep : Represents f (p : ℤ)) : IsSquare (D : ZMod p) := by
  obtain ⟨d, m', hm', hpr⟩ := rep_eq_sq_mul' f (p : ℤ) hrep
  have hdvd : d ^ 2 ∣ (p : ℤ) := ⟨m', hm'⟩
  have hdn : d.natAbs ^ 2 ∣ p := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at h
  have hd1 : d.natAbs = 1 := by
    rcases hp.eq_one_or_self_of_dvd d.natAbs
        ((dvd_pow_self d.natAbs two_ne_zero).trans hdn) with h | h
    · exact h
    · exfalso
      rw [h] at hdn
      have hle := Nat.le_of_dvd hp.pos hdn
      nlinarith [hp.two_le]
  have hd2 : d ^ 2 = 1 := by
    rcases Int.natAbs_eq d with he | he <;> rw [he, hd1] <;> norm_num
  have hm'p : m' = (p : ℤ) := by rw [hm', hd2, one_mul]
  rw [hm'p] at hpr
  exact isSquare_of_properlyRepresents' D p f hdiscr hpr

/-- In `ZMod p` for an odd prime `p`, multiplying by `4` does not change squareness. -/
private theorem isSquare_four_mul' (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x : ZMod p) :
    IsSquare (4 * x) ↔ IsSquare x := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z * (2 : ZMod p)⁻¹, ?_⟩
    have hinv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
    have hz' : (2 : ZMod p) * (2 : ZMod p) * x = z * z := by
      rw [← hz]; ring
    calc x = ((2 : ZMod p) * (2 : ZMod p) * x) * ((2 : ZMod p)⁻¹ * (2 : ZMod p)⁻¹) := by
            rw [show ((2 : ZMod p) * (2 : ZMod p) * x) * ((2 : ZMod p)⁻¹ * (2 : ZMod p)⁻¹)
                  = ((2 : ZMod p) * (2 : ZMod p)⁻¹) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) * x from by
                ring, hinv]
            ring
      _ = z * (2 : ZMod p)⁻¹ * (z * (2 : ZMod p)⁻¹) := by rw [hz']; ring
  · rintro ⟨z, hz⟩
    exact ⟨2 * z, by rw [hz]; ring⟩

/-! ## The residue criterion and its necessary hypotheses -/

/-- The forward implication of the residue criterion needs no further hypotheses. -/

theorem properlyRepresents_isSquare_forward' (D : ℤ) (p : ℕ)
    (h : ∃ f : BinaryQF, f.discr = D ∧ ProperlyRepresents f (p : ℤ)) :
    IsSquare (D : ZMod p) := by
  obtain ⟨f, hd, hrep⟩ := h
  exact isSquare_of_properlyRepresents' D p f hd hrep

/-- The unrestricted residue criterion fails at `D = 3`, `p = 11`:
`3` is a square mod `11`, but no binary quadratic form has discriminant `3`. -/

theorem properlyRepresents_iff_isSquare_counterexample :
    IsSquare (((3 : ℤ)) : ZMod 11) ∧
      ¬ (∃ f : BinaryQF, f.discr = 3 ∧ ProperlyRepresents f ((11 : ℕ) : ℤ)) := by
  constructor
  · refine ⟨5, ?_⟩
    have h3 : (((3 : ℤ)) : ZMod 11) = (3 : ZMod 11) := by push_cast; ring
    rw [h3]; decide
  · rintro ⟨f, hd, -⟩
    have h := discr_mod_four f
    rw [hd] at h
    norm_num at h

/-- The residue criterion also needs `Odd p`, as shown by `D = 5`, `p = 2`. -/

theorem properlyRepresents_iff_isSquare_counterexample_two :
    IsSquare (((5 : ℤ)) : ZMod 2) ∧
      ¬ (∃ f : BinaryQF, f.discr = 5 ∧ ProperlyRepresents f ((2 : ℕ) : ℤ)) := by
  constructor
  · refine ⟨1, ?_⟩
    have h5 : (((5 : ℤ)) : ZMod 2) = (1 : ZMod 2) := by decide
    rw [h5]; decide
  · rintro ⟨f, hd, hrep⟩
    obtain ⟨B, C, hBC⟩ := (properlyRepresents_iff_properlyEquivalent f ((2 : ℕ) : ℤ)).mp hrep
    have hdBC := discr_eq_of_properlyEquivalent hBC
    rw [hd] at hdBC
    simp only [BinaryQF.discr] at hdBC
    have hcast : ((5 : ℤ) : ZMod 8) = ((B : ZMod 8)) ^ 2 := by
      have h := congrArg (fun t : ℤ => (t : ZMod 8)) hdBC
      push_cast at h
      rw [show ((8 : ZMod 8)) = 0 from by decide] at h
      simpa using h
    have hkey : ∀ b : ZMod 8, b ^ 2 ≠ ((5 : ℤ) : ZMod 8) := by decide
    exact hkey _ hcast.symm

/-- The residue criterion with the missing assumptions `D ≡ 0,1 (mod 4)` and `Odd p`. -/

theorem properlyRepresents_iff_isSquare_repaired (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpD : ¬ (p : ℤ) ∣ D) :
    (∃ f : BinaryQF, f.discr = D ∧ ProperlyRepresents f (p : ℤ)) ↔ IsSquare (D : ZMod p) := by
  constructor
  · exact properlyRepresents_isSquare_forward' D p
  · intro hsq
    obtain ⟨b, c, hdiscr, -⟩ :=
      PrimesX2NY2.Fermat.exists_form_of_isSquare D hD p hp hodd hpD hsq
    exact ⟨⟨(p : ℤ), b, c⟩, hdiscr, 1, 0, by simp [BinaryQF.eval], isCoprime_one_left⟩

/-! ## Representation of odd integers -/

theorem properlyRepresents_iff_isSquare_general (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (m : ℤ) (hm : Odd m) (hco : IsCoprime m D) :
    (∃ f : BinaryQF, f.discr = D ∧ f.Primitive ∧ ProperlyRepresents f m)
      ↔ IsSquare (D : ZMod m.natAbs) := by
  have hmne : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  have hn0 : m.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hmne
  haveI : NeZero m.natAbs := ⟨hn0⟩
  have hmzero : ((m : ℤ) : ZMod m.natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr dvd_rfl
  constructor
  · rintro ⟨f, hdiscr, -, hrep⟩
    obtain ⟨B, C, hBC⟩ := (properlyRepresents_iff_properlyEquivalent f m).mp hrep
    have hdBC := discr_eq_of_properlyEquivalent hBC
    rw [hdiscr] at hdBC
    simp only [BinaryQF.discr] at hdBC
    refine ⟨(B : ZMod m.natAbs), ?_⟩
    have hcast := congrArg (fun t : ℤ => (t : ZMod m.natAbs)) hdBC
    push_cast at hcast
    rw [hmzero] at hcast
    rw [hcast]
    ring
  · intro hsq
    obtain ⟨t, ht⟩ := hsq
    have htv : ((t.val : ℕ) : ZMod m.natAbs) = t := ZMod.natCast_rightInverse t
    have hdvd_n : ((m.natAbs : ℤ)) ∣ ((t.val : ℤ) ^ 2 - D) := by
      have hz : ((((t.val : ℤ) ^ 2 - D : ℤ)) : ZMod m.natAbs) = 0 := by
        push_cast
        rw [htv, ht]
        ring
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have hnodd : Odd m.natAbs := Int.natAbs_odd.mpr hm
    obtain ⟨j, hj⟩ := hnodd
    have hjz : ((m.natAbs : ℤ)) = 2 * (j : ℤ) + 1 := by exact_mod_cast hj
    -- Choose `b ≡ t.val (mod |m|)` with the same parity as `D`.
    obtain ⟨b, hbn, hbpar⟩ : ∃ b : ℤ, ((m.natAbs : ℤ) ∣ (b - (t.val : ℤ))) ∧ (2 ∣ (b - D)) := by
      rcases Int.even_or_odd ((t.val : ℤ) - D) with he | ho
      · obtain ⟨k, hk⟩ := he
        exact ⟨(t.val : ℤ), ⟨0, by ring⟩, ⟨k, by omega⟩⟩
      · obtain ⟨k, hk⟩ := ho
        exact ⟨(t.val : ℤ) + (m.natAbs : ℤ), ⟨1, by ring⟩, ⟨k + (j : ℤ) + 1, by omega⟩⟩
    have hdvd_n' : ((m.natAbs : ℤ)) ∣ (b ^ 2 - D) := by
      obtain ⟨s, hs⟩ := hbn
      obtain ⟨r, hr⟩ := hdvd_n
      exact ⟨r + s * (b + (t.val : ℤ)), by linear_combination hr + (b + (t.val:ℤ)) * hs⟩
    have h4 : (4 : ℤ) ∣ (b ^ 2 - D) := by
      obtain ⟨k, hk⟩ := hbpar
      rcases hD with h0 | h1
      · obtain ⟨d, hd⟩ : ∃ d : ℤ, D = 4 * d := ⟨D / 4, by omega⟩
        refine ⟨4 * d ^ 2 + 4 * d * k + k ^ 2 - d, ?_⟩
        have hb : b = 4 * d + 2 * k := by omega
        rw [hb, hd]; ring
      · obtain ⟨d, hd⟩ : ∃ d : ℤ, D = 4 * d + 1 := ⟨D / 4, by omega⟩
        refine ⟨4 * d ^ 2 + k ^ 2 + d + 4 * d * k + k, ?_⟩
        have hb : b = 4 * d + 1 + 2 * k := by omega
        rw [hb, hd]; ring
    have hc4 : Nat.Coprime 4 m.natAbs := by
      have h2d : ¬ (2 ∣ m.natAbs) := by
        have := Nat.odd_iff.mp (Int.natAbs_odd.mpr hm); omega
      have h2 : Nat.Coprime 2 m.natAbs :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2d
      simpa using h2.pow_left 2
    have hcop4 : IsCoprime (4 : ℤ) ((m.natAbs : ℤ)) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd, Int.natAbs_abs] using hc4
    have h4n : (4 * (m.natAbs : ℤ)) ∣ (b ^ 2 - D) := hcop4.mul_dvd h4 hdvd_n'
    obtain ⟨k, hk⟩ := h4n
    have hm4 : (4 * m) ∣ (b ^ 2 - D) := by
      rcases Int.natAbs_eq m with he | he
      · exact ⟨k, by rw [← he] at hk; exact hk⟩
      · refine ⟨-k, ?_⟩
        rw [he]
        linear_combination hk
    obtain ⟨c, hc⟩ := hm4
    refine ⟨⟨m, b, c⟩, ?_, ?_, ?_⟩
    · show b ^ 2 - 4 * m * c = D
      linarith [hc]
    · show Int.gcd (Int.gcd m b) c = 1
      have hGm : ((Int.gcd (Int.gcd m b) c : ℤ)) ∣ m :=
        (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
      have hGb : ((Int.gcd (Int.gcd m b) c : ℤ)) ∣ b :=
        (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
      have hGc : ((Int.gcd (Int.gcd m b) c : ℤ)) ∣ c := Int.gcd_dvd_right _ _
      have hDeq : D = b ^ 2 - 4 * m * c := by linarith [hc]
      have hGb2 : ((Int.gcd (Int.gcd m b) c : ℤ)) ∣ b ^ 2 := by
        rw [sq]; exact hGb.mul_left b
      have hG4mc : ((Int.gcd (Int.gcd m b) c : ℤ)) ∣ 4 * m * c := hGc.mul_left (4 * m)
      have hGD : ((Int.gcd (Int.gcd m b) c : ℤ)) ∣ D := by
        rw [hDeq]; exact dvd_sub hGb2 hG4mc
      have hu : IsUnit ((Int.gcd (Int.gcd m b) c : ℤ)) := hco.isUnit_of_dvd' hGm hGD
      have := Int.isUnit_iff.mp hu
      omega
    · exact ⟨1, 0, by simp [BinaryQF.eval], isCoprime_one_left⟩

/-! ## Prime representation and reduced forms -/

/-- **Corollary 2.6.** For an odd prime `p ∤ n`, `(−n/p) = 1` iff `p` is
represented by a primitive form of discriminant `−4n`. (Cox §2.) -/
private theorem not_dvd_neg_four_mul' (n : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hpn : ¬ (p : ℤ) ∣ n) : ¬ (p : ℤ) ∣ (-4 * n) := by
  intro h
  have hpp : Prime ((p : ℤ)) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  rcases hpp.dvd_mul.mp h with h1 | h1
  · have h4 : (p : ℤ) ∣ 4 := (dvd_neg.mp (by simpa using h1))
    have hpn4 : p ∣ 4 := by exact_mod_cast h4
    have hp2 : p = 2 := by
      have : p ∣ 2 ^ 2 := by simpa using hpn4
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    rw [hp2] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  · exact hpn h1

theorem cor_2_6 (n : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpn : ¬ (p : ℤ) ∣ n) :
    IsSquare ((-n : ℤ) : ZMod p)
      ↔ ∃ f : BinaryQF, f.discr = -4 * n ∧ f.Primitive ∧ Represents f (p : ℤ) := by
  have hD4 : (-4 * n) % 4 = 0 ∨ (-4 * n) % 4 = 1 := Or.inl (by omega)
  have hpD : ¬ (p : ℤ) ∣ (-4 * n) := not_dvd_neg_four_mul' n p hp hodd hpn
  have hcast : (((-4 * n : ℤ)) : ZMod p) = 4 * (((-n : ℤ)) : ZMod p) := by push_cast; ring
  have hsq4 : IsSquare (((-4 * n : ℤ)) : ZMod p) ↔ IsSquare (((-n : ℤ)) : ZMod p) := by
    rw [hcast]; exact isSquare_four_mul' p hp hodd _
  rw [← hsq4]
  constructor
  · intro hsq
    obtain ⟨b, c, hdiscr, hprim⟩ :=
      PrimesX2NY2.Fermat.exists_form_of_isSquare (-4 * n) hD4 p hp hodd hpD hsq
    exact ⟨⟨(p : ℤ), b, c⟩, hdiscr, hprim, 1, 0, by simp [BinaryQF.eval]⟩
  · rintro ⟨f, hdiscr, -, hrep⟩
    exact isSquare_of_represents' (-4 * n) p hp f hdiscr hrep

/-- **Theorem 2.16.** For negative `D ≡ 0,1 (mod 4)` and an odd prime `p ∤ D`,
`(D/p) = 1` (equivalently `[p] ∈ ker χ`) iff `p` is represented by one of the
reduced forms of discriminant `D`. (Cox §2.) -/
theorem thm_2_16 (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) (hDneg : D < 0)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpD : ¬ (p : ℤ) ∣ D) :
    IsSquare (D : ZMod p)
      ↔ ∃ f : BinaryQF, f.discr = D ∧ f.Reduced ∧ f.Primitive ∧ Represents f (p : ℤ) := by
  constructor
  · intro hsq
    obtain ⟨b, c, hdiscr, hprim⟩ :=
      PrimesX2NY2.Fermat.exists_form_of_isSquare D hD p hp hodd hpD hsq
    have hpos : ((⟨(p : ℤ), b, c⟩ : BinaryQF)).PosDef := by
      refine ⟨?_, ?_⟩
      · show (0 : ℤ) < (p : ℤ)
        exact_mod_cast hp.pos
      · rw [hdiscr]; exact hDneg
    obtain ⟨g, ⟨hred, heq⟩, -⟩ := exists_unique_reduced _ hpos
    refine ⟨g, ?_, hred, ?_, ?_⟩
    · rw [← discr_eq_of_properlyEquivalent heq]; exact hdiscr
    · exact (primitive_of_properlyEquivalent heq).mp hprim
    · exact represents_of_properlyEquivalent' heq (p : ℤ) ⟨1, 0, by simp [BinaryQF.eval]⟩
  · rintro ⟨f, hdiscr, -, -, hrep⟩
    exact isSquare_of_represents' D p hp f hdiscr hrep

/-- **Proposition 2.15.** For an odd prime `p ∤ n`, `(−n/p) = 1` iff `p` is
represented by one of the reduced forms of discriminant `−4n`. (Cox §2.) -/
theorem prop_2_15 (n : ℕ) (hn : 0 < n) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hpn : ¬ (p : ℤ) ∣ (n : ℤ)) :
    IsSquare ((-(n : ℤ)) : ZMod p)
      ↔ ∃ f : BinaryQF, f.discr = -4 * (n : ℤ) ∧ f.Reduced ∧ f.Primitive
          ∧ Represents f (p : ℤ) := by
  have hnz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hD4 : (-4 * (n : ℤ)) % 4 = 0 ∨ (-4 * (n : ℤ)) % 4 = 1 := Or.inl (by omega)
  have hDneg : (-4 * (n : ℤ)) < 0 := by linarith
  have hpD : ¬ (p : ℤ) ∣ (-4 * (n : ℤ)) := not_dvd_neg_four_mul' (n : ℤ) p hp hodd hpn
  have hcast : (((-4 * (n : ℤ) : ℤ)) : ZMod p) = 4 * (-(((n : ℤ)) : ZMod p)) := by
    push_cast; ring
  have hsq4 : IsSquare (((-4 * (n : ℤ) : ℤ)) : ZMod p) ↔ IsSquare (-(((n : ℤ)) : ZMod p)) := by
    rw [hcast]; exact isSquare_four_mul' p hp hodd _
  rw [← hsq4]
  exact thm_2_16 (-4 * (n : ℤ)) hD4 hDneg p hp hodd hpD

/-! ## Residues represented by the principal form -/

/-- A prime dividing `N` cannot divide an integer whose residue mod `N` is a unit. -/
private theorem not_prime_dvd_of_isUnit' (N : ℕ) (v : ℤ) (hv : IsUnit ((v : ℤ) : ZMod N))
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqv : (q : ℤ) ∣ v) : False := by
  haveI := Fact.mk hq
  have h := hv.map (ZMod.castHom hqN (ZMod q))
  rw [map_intCast] at h
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd v q).mpr hqv] at h
  exact not_isUnit_zero h

/-- **Primitive vectors in a residue class.** If no prime factor of `N` divides both `A` and
`B`, then some `(x, y) ≡ (A, B) (mod N)` is a primitive vector. -/
private theorem exists_coprime_congr' (A B N : ℤ)
    (h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ N → ¬ ((q : ℤ) ∣ A ∧ (q : ℤ) ∣ B)) :
    ∃ x y : ℤ, N ∣ (x - A) ∧ N ∣ (y - B) ∧ IsCoprime x y := by
  classical
  rcases eq_or_ne B 0 with rfl | hB
  · refine ⟨A, N, ⟨0, by ring⟩, ⟨1, by ring⟩, ?_⟩
    refine coprime_of_all_primes A N ?_
    intro q hq hqN hqA
    exact h q hq hqN ⟨hqA, dvd_zero _⟩
  · obtain ⟨P, hP⟩ : ∃ P : ℕ,
        P = ∏ r ∈ (B.natAbs.primeFactors.filter (fun r : ℕ => ¬ ((r : ℤ) ∣ A))), r := ⟨_, rfl⟩
    refine ⟨A + N * (P : ℤ), B, ⟨(P : ℤ), by ring⟩, ⟨0, by ring⟩, ?_⟩
    refine coprime_of_all_primes _ B ?_
    intro q hq hqB hqx
    have hqZ : Prime ((q : ℤ)) := Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
    by_cases hqA : (q : ℤ) ∣ A
    · have hqN : ¬ ((q : ℤ) ∣ N) := fun hd => h q hq hd ⟨hqA, hqB⟩
      have hqP : ¬ ((q : ℤ) ∣ (P : ℤ)) := by
        intro hd
        have hdn : q ∣ P := by exact_mod_cast hd
        rw [hP] at hdn
        obtain ⟨r, hr, hqr⟩ := (hq.prime.dvd_finsetProd_iff (fun r => r)).mp hdn
        have hrmem := Finset.mem_filter.mp hr
        have hqreq : q = r :=
          (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors hrmem.1)).mp hqr
        exact hrmem.2 (by rw [← hqreq]; exact hqA)
      have hNP : (q : ℤ) ∣ N * (P : ℤ) := by
        have hd2 : (q : ℤ) ∣ (A + N * (P : ℤ)) - A := dvd_sub hqx hqA
        simpa using hd2
      rcases hqZ.dvd_mul.mp hNP with h1 | h1
      · exact hqN h1
      · exact hqP h1
    · have hqmem : q ∈ (B.natAbs.primeFactors.filter (fun r : ℕ => ¬ ((r : ℤ) ∣ A))) := by
        refine Finset.mem_filter.mpr ⟨?_, hqA⟩
        refine Nat.mem_primeFactors.mpr ⟨hq, ?_, ?_⟩
        · simpa using Int.natAbs_dvd_natAbs.mpr hqB
        · simpa [Int.natAbs_eq_zero] using hB
      have hqP : (q : ℤ) ∣ (P : ℤ) := by
        have hdn : q ∣ P := by
          rw [hP]; exact Finset.dvd_prod_of_mem (fun r => r) hqmem
        exact_mod_cast hdn
      have hqNP : (q : ℤ) ∣ N * (P : ℤ) := hqP.mul_left N
      exact hqA (by simpa using dvd_sub hqx hqNP)

/-- The composition (Brahmagupta) identity for a form with leading coefficient `1`. -/
private theorem eval_mul_eval_of_a_one' (f : BinaryQF) (hfa : f.a = 1) (x₁ y₁ x₂ y₂ : ℤ) :
    f.eval x₁ y₁ * f.eval x₂ y₂
      = f.eval (x₁ * x₂ - f.c * y₁ * y₂) (x₁ * y₂ + x₂ * y₁ + f.b * y₁ * y₂) := by
  simp only [BinaryQF.eval, hfa, one_mul]
  ring

/-- **Lemma 2.24** (part i). For negative `D ≡ 0,1 (mod 4)`, the residues in
`(ℤ/Dℤ)ˣ` represented by the principal form constitute a subgroup `H`. (Cox §2.) -/
theorem principalForm_values_subgroup (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    (hDneg : D < 0) :
    ∃ H : Subgroup (ZMod D.natAbs)ˣ,
      ∀ u : (ZMod D.natAbs)ˣ,
        (u ∈ H ↔ ∃ x y : ℤ, IsCoprime x y ∧
          ((principalForm D).eval x y : ZMod D.natAbs) = (u : ZMod D.natAbs)) := by
  have hD0 : D ≠ 0 := ne_of_lt hDneg
  have hn0 : D.natAbs ≠ 0 := fun hh => hD0 (Int.natAbs_eq_zero.mp hh)
  haveI : NeZero D.natAbs := ⟨hn0⟩
  have hfa : (principalForm D).a = 1 := by simp only [principalForm]; split <;> rfl
  -- Use proper representation modulo `D` as the subgroup predicate.
  set P : (ZMod D.natAbs)ˣ → Prop := fun u => ∃ x y : ℤ, IsCoprime x y ∧
      (((principalForm D).eval x y : ℤ) : ZMod D.natAbs) = (u : ZMod D.natAbs) with hPdef
  have hone : P 1 := by
    refine ⟨1, 0, isCoprime_one_left, ?_⟩
    simp [BinaryQF.eval, hfa]
  have hmul : ∀ u₁ u₂ : (ZMod D.natAbs)ˣ, P u₁ → P u₂ → P (u₁ * u₂) := by
    rintro u₁ u₂ ⟨x₁, y₁, hc₁, hv₁⟩ ⟨x₂, y₂, hc₂, hv₂⟩
    set X := x₁ * x₂ - (principalForm D).c * y₁ * y₂ with hX
    set Y := x₁ * y₂ + x₂ * y₁ + (principalForm D).b * y₁ * y₂ with hY
    have hcomp : (principalForm D).eval x₁ y₁ * (principalForm D).eval x₂ y₂
        = (principalForm D).eval X Y := eval_mul_eval_of_a_one' _ hfa x₁ y₁ x₂ y₂
    have hvu : ((((principalForm D).eval X Y : ℤ)) : ZMod D.natAbs)
        = ((u₁ * u₂ : (ZMod D.natAbs)ˣ) : ZMod D.natAbs) := by
      rw [← hcomp]
      push_cast
      rw [hv₁, hv₂]
    have hUnit : IsUnit ((((principalForm D).eval X Y : ℤ)) : ZMod D.natAbs) := by
      rw [hvu]; exact Units.isUnit _
    have hside : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ ((D.natAbs : ℤ)) →
        ¬ ((q : ℤ) ∣ X ∧ (q : ℤ) ∣ Y) := by
      intro q hq hqn hqXY
      refine not_prime_dvd_of_isUnit' D.natAbs ((principalForm D).eval X Y) hUnit q hq
        (by exact_mod_cast hqn) ?_
      obtain ⟨s, hs⟩ := hqXY.1
      obtain ⟨t, ht⟩ := hqXY.2
      refine ⟨(q : ℤ) * ((principalForm D).a * s ^ 2 + (principalForm D).b * s * t
        + (principalForm D).c * t ^ 2), ?_⟩
      simp only [BinaryQF.eval]
      rw [hs, ht]; ring
    obtain ⟨x, y, hx, hy, hcop⟩ := exists_coprime_congr' X Y ((D.natAbs : ℤ)) hside
    refine ⟨x, y, hcop, ?_⟩
    have hxm : X ≡ x [ZMOD ((D.natAbs : ℤ))] := Int.modEq_iff_dvd.mpr hx
    have hym : Y ≡ y [ZMOD ((D.natAbs : ℤ))] := Int.modEq_iff_dvd.mpr hy
    have hev := eval_cong (principalForm D) X x Y y ((D.natAbs : ℤ)) hxm hym
    have hcast2 := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hev
    rw [← hcast2, hvu]
  have hpow : ∀ u : (ZMod D.natAbs)ˣ, P u → ∀ k : ℕ, P (u ^ k) := by
    intro u hu k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hu
  have hinv : ∀ u : (ZMod D.natAbs)ˣ, P u → P u⁻¹ := by
    intro u hu
    have hcard : 0 < Fintype.card (ZMod D.natAbs)ˣ := Fintype.card_pos
    have hu1 : u ^ (Fintype.card (ZMod D.natAbs)ˣ) = 1 := pow_card_eq_one
    have hstep : u * u ^ (Fintype.card (ZMod D.natAbs)ˣ - 1) = 1 := by
      rw [← pow_succ']
      rw [show Fintype.card (ZMod D.natAbs)ˣ - 1 + 1 = Fintype.card (ZMod D.natAbs)ˣ by omega]
      exact hu1
    rw [inv_eq_of_mul_eq_one_right hstep]
    exact hpow u hu _
  refine ⟨{ carrier := {u | P u}
            mul_mem' := fun {a b} ha hb => hmul a b ha hb
            one_mem' := hone
            inv_mem' := fun {a} ha => hinv a ha }, ?_⟩
  intro u
  exact Iff.rfl

/-- **Lemma 2.25** (Gauss). Every *primitive* form properly represents some value
relatively prime to a given nonzero integer `M`. The `Primitive` and `M ≠ 0` hypotheses
are required: without them the statement is false (e.g. `⟨2, 2, 2⟩` represents only even
values, so represents nothing coprime to `M = 2`). (Cox §2, Exercise 2.18.) -/
theorem properlyRepresents_coprime (f : BinaryQF) (hf : f.Primitive) (M : ℤ) (hM : M ≠ 0) :
    ∃ x y : ℤ, IsCoprime x y ∧ IsCoprime (f.eval x y) M := lemma_2_25 f hf M hM

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

This replaces an earlier statement whose condition `∃ S, p ∈ S` was always true
and therefore imposed no congruence restriction. -/
theorem represents_principal_iff_congruence (n : ℕ) (hn : 0 < n) (p : ℕ)
    (hp : p.Prime) (hodd : Odd p) (hpn : ¬ (p : ℤ) ∣ (n : ℤ)) :
    (p : ZMod ((-4 * (n : ℤ)).natAbs)) ∈ principalGenus (-4 * (n : ℤ))
      ↔ ∃ β : ℤ, ((p : ℤ) ≡ β ^ 2 [ZMOD (4 * n)]) ∨
          ((p : ℤ) ≡ β ^ 2 + (n : ℤ) [ZMOD (4 * n)]) := by
  sorry

/-- `DirectlyComposes` is **symmetric** in its two arguments: swapping the roles of `f` and `g`
swaps columns 2 and 3 of the bilinear substitution matrix, which interchanges the two `(3.1)`
sign conditions `m₁₂ ↔ m₁₃` exactly. -/
theorem directlyComposes_symm (f g F : BinaryQF) (h : DirectlyComposes f g F) :
    DirectlyComposes g f F := by
  obtain ⟨a₁,b₁,c₁,d₁,a₂,b₂,c₂,d₂, hid, hsb, hsc⟩ := h
  refine ⟨a₁, c₁, b₁, d₁, a₂, c₂, b₂, d₂, ?_, hsc, hsb⟩
  intro x y z w
  have hh := hid z w x y
  rw [mul_comm (g.eval x y) (f.eval z w), hh]
  congr 1 <;> ring

/-- **Cox 3.5(c) in the second argument.** If `G` is the direct composition of `h` and `k`, and
`k ~ k'`, then `G` is the direct composition of `h` and `k'`. (Symmetry + the left version.) -/
theorem directlyComposes_of_properlyEquivalent_right (h k G k' : BinaryQF)
    (hDC : DirectlyComposes h k G) (he : ProperlyEquivalent k k')
    (hka : k.a ≠ 0) (hhG : h.discr = G.discr) (hG0 : G.discr ≠ 0) :
    DirectlyComposes h k' G :=
  directlyComposes_symm k' h G
    (directlyComposes_of_properlyEquivalent_left k h G k' (directlyComposes_symm h k G hDC)
      he hka hhG hG0)

/-- Discriminant of the Dirichlet composite when the leading coefficients are coprime. -/
theorem dirichletForm_discr_of_coprime (f g : BinaryQF) (D : ℤ) (hf : f.discr = D)
    (hg : g.discr = D) (hcop : Int.gcd f.a g.a = 1) : (dirichletForm f g).discr = D :=
  dirichletForm_discr f g D hf hg (by rw [hcop]; simp)

/-- For concordant forms, Cox's explicit Dirichlet composite (3.7) satisfies
Gauss's direct-composition relation (3.1).

With `B := dirichletB f g` and `C := (B²−D)/(4·f.a·g.a)`, `dirichletForm f g = ⟨f.a·g.a, B, C⟩`,
and the translations `f ~ ⟨f.a, B, g.a·C⟩`, `g ~ ⟨g.a, B, f.a·C⟩` (Cox 3.5(a), via
`dirichletB_spec1/2` and `translation_equiv_proj`) put the pair into the concordant shape of
`dirichletForm_directlyComposes_concordant` (Cox 3.5(b)); transporting both arguments back by
Cox 3.5(c) gives the claim. This result is used to prove that `compose` is
well-defined and, through united forms, associative. -/
theorem dirichletForm_directlyComposes (f g : BinaryQF) (D : ℤ) (hD : D < 0)
    (hf : f.discr = D) (hg : g.discr = D) (hfa : 0 < f.a) (hga : 0 < g.a)
    (hcop : Int.gcd f.a g.a = 1) :
    DirectlyComposes f g (dirichletForm f g) := by
  have hD0 : D ≠ 0 := ne_of_lt hD
  have hcop3 : Int.gcd (Int.gcd f.a g.a) ((f.b + g.b) / 2) = 1 := by rw [hcop]; simp
  set B := dirichletB f g with hBdef
  set C := (B^2 - D) / (4 * f.a * g.a) with hCdef
  have hdf : dirichletForm f g = ⟨f.a * g.a, B, C⟩ := by
    simp only [dirichletForm, hBdef, hCdef, hf]
  have hFa : (⟨f.a, B, g.a * C⟩ : BinaryQF).a ≠ 0 := hfa.ne'
  have hdvd : (4 * f.a * g.a : ℤ) ∣ B^2 - D := by
    have := dirichletB_spec f g D hf hg hcop3
    rw [hf] at this
    exact Int.ModEq.dvd this.symm
  have hC4 : 4 * f.a * g.a * C = B^2 - D := by rw [hCdef]; exact Int.mul_ediv_cancel' hdvd
  have hdiscrF : (⟨f.a, B, g.a * C⟩ : BinaryQF).discr = D := by
    simp only [BinaryQF.discr]; linarith [hC4]
  have hdiscrG : (⟨g.a, B, f.a * C⟩ : BinaryQF).discr = D := by
    simp only [BinaryQF.discr]; linarith [hC4]
  have hdiscrFG : (⟨f.a * g.a, B, C⟩ : BinaryQF).discr = D := by
    simp only [BinaryQF.discr]; linarith [hC4]
  have hfe : ProperlyEquivalent (⟨f.a, B, g.a * C⟩ : BinaryQF) f := by
    refine translation_equiv_proj _ _ hFa rfl ?_ ?_
    · exact Int.ModEq.dvd (dirichletB_spec1 f g D hf hg hcop3)
    · rw [hdiscrF, hf]
  have hge : ProperlyEquivalent (⟨g.a, B, f.a * C⟩ : BinaryQF) g := by
    refine translation_equiv_proj _ _ hga.ne' rfl ?_ ?_
    · exact Int.ModEq.dvd (dirichletB_spec2 f g D hf hg hcop3)
    · rw [hdiscrG, hg]
  have hconc := dirichletForm_directlyComposes_concordant f.a g.a B C
  rw [hdf]
  have hG0' : (⟨f.a * g.a, B, C⟩ : BinaryQF).discr ≠ 0 := by rw [hdiscrFG]; exact hD0
  have step1 : DirectlyComposes f (⟨g.a, B, f.a * C⟩ : BinaryQF) ⟨f.a * g.a, B, C⟩ :=
    directlyComposes_of_properlyEquivalent_left _ _ _ f hconc hfe hFa
      (by rw [hdiscrG, hdiscrFG]) hG0'
  exact directlyComposes_of_properlyEquivalent_right f _ _ g step1 hge hga.ne'
    (by rw [hf, hdiscrFG]) hG0'

/-- The chosen representative-level composite is a direct composition of the original pair.
The definition first replaces the second form by a coprime properly equivalent representative;
Cox 3.5(c) transports the direct-composition identity back to the original representative. -/
theorem composeForm_directlyComposes (D : ℤ) (hD : D < 0) (F G : DiscrForms D) :
    DirectlyComposes F.1 G.1 (composeForm D hD F G).1 := by
  set hc := concordance F.1 G.1 D hD F.2.2.2 G.2.1 G.2.2.1 G.2.2.2 with hhc
  obtain ⟨he, hd, _, ha, hcop⟩ := hc.choose_spec
  have hcf : (composeForm D hD F G).1 = dirichletForm F.1 hc.choose := rfl
  rw [hcf]
  have hdc : DirectlyComposes F.1 hc.choose (dirichletForm F.1 hc.choose) :=
    dirichletForm_directlyComposes F.1 hc.choose D hD F.2.1 hd F.2.2.2 ha hcop
  have hE : (dirichletForm F.1 hc.choose).discr = D :=
    dirichletForm_discr_of_coprime F.1 hc.choose D F.2.1 hd hcop
  exact directlyComposes_of_properlyEquivalent_right F.1 hc.choose _ G.1 hdc
    (properlyEquivalent_equivalence.symm he) ha.ne'
    (by rw [F.2.1, hE]) (by rw [hE]; exact ne_of_lt hD)

/-- The Dirichlet composite is independent, up to proper equivalence, of the
concordant representative chosen. As in Cox's Theorem 3.9, the discriminant is
negative; this supplies the nonzero discriminant needed for the minor relations. -/
theorem concordant_choice_invariant_of_neg (D : ℤ) (hD : D < 0) (F : DiscrForms D)
    (g₁ g₂ : BinaryQF) (he : ProperlyEquivalent g₁ g₂)
    (hd₁ : g₁.discr = D) (ha₁ : 0 < g₁.a) (hc₁ : Int.gcd F.1.a g₁.a = 1)
    (hd₂ : g₂.discr = D) (ha₂ : 0 < g₂.a) (hc₂ : Int.gcd F.1.a g₂.a = 1) :
    ProperlyEquivalent (dirichletForm F.1 g₁) (dirichletForm F.1 g₂) := by
  have hD0 : D ≠ 0 := ne_of_lt hD
  have hFd : F.1.discr = D := F.2.1
  have hFa : 0 < F.1.a := F.2.2.2
  have hE1 : (dirichletForm F.1 g₁).discr = D := dirichletForm_discr_of_coprime F.1 g₁ D hFd hd₁ hc₁
  have hE2 : (dirichletForm F.1 g₂).discr = D := dirichletForm_discr_of_coprime F.1 g₂ D hFd hd₂ hc₂
  have hdc₁ : DirectlyComposes F.1 g₁ (dirichletForm F.1 g₁) :=
    dirichletForm_directlyComposes F.1 g₁ D hD hFd hd₁ hFa ha₁ hc₁
  have hdc₂ : DirectlyComposes F.1 g₂ (dirichletForm F.1 g₂) :=
    dirichletForm_directlyComposes F.1 g₂ D hD hFd hd₂ hFa ha₂ hc₂
  have hdc₁' : DirectlyComposes F.1 g₂ (dirichletForm F.1 g₁) :=
    directlyComposes_of_properlyEquivalent_right F.1 g₁ _ g₂ hdc₁ he ha₁.ne'
      (by rw [hFd, hE1]) (by rw [hE1]; exact hD0)
  exact directlyComposes_unique_of_coprime F.1 g₂ _ _ D hD hFd hd₂
    (Int.isCoprime_iff_gcd_eq_one.mpr hc₂) hdc₁' hE1 hdc₂ hE2

/-- Composition respects proper equivalence, as required for `Quotient.lift₂`:
`f ~ f'` and `g ~ g'` imply `composeForm f g ~ composeForm f' g'`. Proved by transporting the
direct-composition witness through both arguments (Cox 3.5(c) left and right) and then invoking
uniqueness on the common pair. -/
theorem composeForm_respects (D : ℤ) (hD : D < 0) (F₁ G₁ F₂ G₂ : DiscrForms D)
    (hF : ProperlyEquivalent F₁.1 F₂.1) (hG : ProperlyEquivalent G₁.1 G₂.1) :
    ProperlyEquivalent (composeForm D hD F₁ G₁).1 (composeForm D hD F₂ G₂).1 := by
  have hD0 : D ≠ 0 := ne_of_lt hD
  set h1 := concordance F₁.1 G₁.1 D hD F₁.2.2.2 G₁.2.1 G₁.2.2.1 G₁.2.2.2 with hh1
  set h2 := concordance F₂.1 G₂.1 D hD F₂.2.2.2 G₂.2.1 G₂.2.2.1 G₂.2.2.2 with hh2
  obtain ⟨he₁, hd₁, _, ha₁, hcop₁⟩ := h1.choose_spec
  obtain ⟨he₂, hd₂, _, ha₂, hcop₂⟩ := h2.choose_spec
  have hcf₁ : (composeForm D hD F₁ G₁).1 = dirichletForm F₁.1 h1.choose := rfl
  have hcf₂ : (composeForm D hD F₂ G₂).1 = dirichletForm F₂.1 h2.choose := rfl
  rw [hcf₁, hcf₂]
  have hF1d : F₁.1.discr = D := F₁.2.1
  have hF2d : F₂.1.discr = D := F₂.2.1
  have hE1 : (dirichletForm F₁.1 h1.choose).discr = D :=
    dirichletForm_discr_of_coprime _ _ D hF1d hd₁ hcop₁
  have hE2 : (dirichletForm F₂.1 h2.choose).discr = D :=
    dirichletForm_discr_of_coprime _ _ D hF2d hd₂ hcop₂
  have hdc₁ : DirectlyComposes F₁.1 h1.choose (dirichletForm F₁.1 h1.choose) :=
    dirichletForm_directlyComposes _ _ D hD hF1d hd₁ F₁.2.2.2 ha₁ hcop₁
  have hdc₂ : DirectlyComposes F₂.1 h2.choose (dirichletForm F₂.1 h2.choose) :=
    dirichletForm_directlyComposes _ _ D hD hF2d hd₂ F₂.2.2.2 ha₂ hcop₂
  have step1 : DirectlyComposes F₂.1 h1.choose (dirichletForm F₁.1 h1.choose) :=
    directlyComposes_of_properlyEquivalent_left F₁.1 h1.choose _ F₂.1 hdc₁ hF
      F₁.2.2.2.ne' (by rw [hd₁, hE1]) (by rw [hE1]; exact hD0)
  have hchain : ProperlyEquivalent h1.choose h2.choose :=
    properlyEquivalent_equivalence.trans
      (properlyEquivalent_equivalence.trans (properlyEquivalent_equivalence.symm he₁) hG) he₂
  have step2 : DirectlyComposes F₂.1 h2.choose (dirichletForm F₁.1 h1.choose) :=
    directlyComposes_of_properlyEquivalent_right F₂.1 h1.choose _ h2.choose step1 hchain ha₁.ne'
      (by rw [hF2d, hE1]) (by rw [hE1]; exact hD0)
  exact directlyComposes_unique_of_coprime F₂.1 h2.choose _ _ D hD hF2d hd₂
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop₂) step2 hE1 hdc₂ hE2

/-- **Commutativity of the form-level composite** (Cox Thm 3.9). -/
theorem composeForm_comm (D : ℤ) (hD : D < 0) (F G : DiscrForms D) :
    ProperlyEquivalent (composeForm D hD F G).1 (composeForm D hD G F).1 := by
  have hD0 : D ≠ 0 := ne_of_lt hD
  set h1 := concordance F.1 G.1 D hD F.2.2.2 G.2.1 G.2.2.1 G.2.2.2 with hh1
  set h2 := concordance G.1 F.1 D hD G.2.2.2 F.2.1 F.2.2.1 F.2.2.2 with hh2
  obtain ⟨he₁, hd₁, _, ha₁, hcop₁⟩ := h1.choose_spec
  obtain ⟨he₂, hd₂, _, ha₂, hcop₂⟩ := h2.choose_spec
  have hcf₁ : (composeForm D hD F G).1 = dirichletForm F.1 h1.choose := rfl
  have hcf₂ : (composeForm D hD G F).1 = dirichletForm G.1 h2.choose := rfl
  rw [hcf₁, hcf₂]
  have hFd : F.1.discr = D := F.2.1
  have hGd : G.1.discr = D := G.2.1
  have hE1 : (dirichletForm F.1 h1.choose).discr = D :=
    dirichletForm_discr_of_coprime _ _ D hFd hd₁ hcop₁
  have hE2 : (dirichletForm G.1 h2.choose).discr = D :=
    dirichletForm_discr_of_coprime _ _ D hGd hd₂ hcop₂
  have hdc₁ : DirectlyComposes F.1 h1.choose (dirichletForm F.1 h1.choose) :=
    dirichletForm_directlyComposes _ _ D hD hFd hd₁ F.2.2.2 ha₁ hcop₁
  have hdc₂ : DirectlyComposes G.1 h2.choose (dirichletForm G.1 h2.choose) :=
    dirichletForm_directlyComposes _ _ D hD hGd hd₂ G.2.2.2 ha₂ hcop₂
  have hsw : DirectlyComposes h2.choose G.1 (dirichletForm G.1 h2.choose) :=
    directlyComposes_symm _ _ _ hdc₂
  have s1 : DirectlyComposes F.1 G.1 (dirichletForm G.1 h2.choose) :=
    directlyComposes_of_properlyEquivalent_left h2.choose G.1 _ F.1 hsw
      (properlyEquivalent_equivalence.symm he₂) ha₂.ne' (by rw [hGd, hE2]) (by rw [hE2]; exact hD0)
  have s2 : DirectlyComposes F.1 h1.choose (dirichletForm G.1 h2.choose) :=
    directlyComposes_of_properlyEquivalent_right F.1 G.1 _ h1.choose s1 he₁ G.2.2.2.ne'
      (by rw [hFd, hE2]) (by rw [hE2]; exact hD0)
  exact directlyComposes_unique_of_coprime F.1 h1.choose _ _ D hD hFd hd₁
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop₁) hdc₁ hE1 s2 hE2

/-- **Dirichlet's united triple.** Any three forms of the same negative discriminant can be
replaced by properly equivalent forms whose positive leading coefficients are pairwise coprime
and whose middle coefficient is one common `B`. Their final coefficients then have the united
shape determined by one `C`, with `B² - 4a₁a₂a₃C = D`.

Choose the second leading coefficient coprime to the first by `concordance`, then choose the
third coprime to their product. The common `B` is `exists_commonB_three`; exact division gives
`C`, and `translation_equiv_proj` supplies the three proper equivalences. -/
theorem exists_united_triple (D : ℤ) (hD : D < 0) (F G H : DiscrForms D) :
    ∃ (F' G' H' : DiscrForms D) (B C : ℤ),
      ProperlyEquivalent F.1 F'.1 ∧
      ProperlyEquivalent G.1 G'.1 ∧
      ProperlyEquivalent H.1 H'.1 ∧
      Int.gcd F'.1.a G'.1.a = 1 ∧
      Int.gcd F'.1.a H'.1.a = 1 ∧
      Int.gcd G'.1.a H'.1.a = 1 ∧
      F'.1 = ⟨F'.1.a, B, G'.1.a * H'.1.a * C⟩ ∧
      G'.1 = ⟨G'.1.a, B, F'.1.a * H'.1.a * C⟩ ∧
      H'.1 = ⟨H'.1.a, B, F'.1.a * G'.1.a * C⟩ ∧
      B ^ 2 - 4 * F'.1.a * G'.1.a * H'.1.a * C = D := by
  obtain ⟨g, hGg, hgd, hgp, hga, h12⟩ :=
    concordance F.1 G.1 D hD F.2.2.2 G.2.1 G.2.2.1 G.2.2.2
  let P : BinaryQF := ⟨F.1.a * g.a, 0, 0⟩
  have hPa : 0 < P.a := by
    dsimp [P]
    exact mul_pos F.2.2.2 hga
  obtain ⟨h, hHh, hhd, hhp, hha, h123⟩ :=
    concordance P H.1 D hD hPa H.2.1 H.2.2.1 H.2.2.2
  have h123' : Int.gcd (F.1.a * g.a) h.a = 1 := by
    simpa [P] using h123
  have hi123 : IsCoprime (F.1.a * g.a) h.a :=
    Int.isCoprime_iff_gcd_eq_one.mpr h123'
  have h13 : Int.gcd F.1.a h.a = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hi123.of_mul_left_left
  have h23 : Int.gcd g.a h.a = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hi123.of_mul_left_right
  obtain ⟨B, hB1, hB2, hB3, hBsq⟩ :=
    exists_commonB_three F.1.a F.1.b F.1.c g.a g.b g.c h.a h.b h.c D
      F.2.1 hgd hhd h12 h13 h23
  set C := (B ^ 2 - D) / (4 * F.1.a * g.a * h.a) with hCdef
  have hCmul : 4 * F.1.a * g.a * h.a * C = B ^ 2 - D := by
    simpa [hCdef] using commonC_three F.1.a g.a h.a B D hBsq
  let fU : BinaryQF := ⟨F.1.a, B, g.a * h.a * C⟩
  let gU : BinaryQF := ⟨g.a, B, F.1.a * h.a * C⟩
  let hU : BinaryQF := ⟨h.a, B, F.1.a * g.a * C⟩
  have hfUd : fU.discr = D := by
    simp only [fU, BinaryQF.discr]
    linear_combination -hCmul
  have hgUd : gU.discr = D := by
    simp only [gU, BinaryQF.discr]
    linear_combination -hCmul
  have hhUd : hU.discr = D := by
    simp only [hU, BinaryQF.discr]
    linear_combination -hCmul
  have hFfU : ProperlyEquivalent F.1 fU := by
    refine translation_equiv_proj F.1 fU F.2.2.2.ne' rfl ?_ ?_
    · exact Int.ModEq.dvd hB1.symm
    · rw [F.2.1, hfUd]
  have hggU : ProperlyEquivalent g gU := by
    refine translation_equiv_proj g gU hga.ne' rfl ?_ ?_
    · exact Int.ModEq.dvd hB2.symm
    · rw [hgd, hgUd]
  have hhhU : ProperlyEquivalent h hU := by
    refine translation_equiv_proj h hU hha.ne' rfl ?_ ?_
    · exact Int.ModEq.dvd hB3.symm
    · rw [hhd, hhUd]
  have hfUp : fU.Primitive := (primitive_of_properlyEquivalent hFfU).mp F.2.2.1
  have hgUp : gU.Primitive := (primitive_of_properlyEquivalent hggU).mp hgp
  have hhUp : hU.Primitive := (primitive_of_properlyEquivalent hhhU).mp hhp
  let F' : DiscrForms D := ⟨fU, hfUd, hfUp, by simpa [fU] using F.2.2.2⟩
  let G' : DiscrForms D := ⟨gU, hgUd, hgUp, by simpa [gU] using hga⟩
  let H' : DiscrForms D := ⟨hU, hhUd, hhUp, by simpa [hU] using hha⟩
  refine ⟨F', G', H', B, C, hFfU,
    properlyEquivalent_equivalence.trans hGg hggU,
    properlyEquivalent_equivalence.trans hHh hhhU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [F', G', fU, gU] using h12
  · simpa [F', H', fU, hU] using h13
  · simpa [G', H', gU, hU] using h23
  · rfl
  · rfl
  · rfl
  · simp only [F', G', H', fU, gU, hU]
    linarith

end PrimesX2NY2.Genus

/-! ## The class group operation

The class-group operation uses `composeForm`, `concordance`, and `DirectlyComposes`,
so it is defined here after those results. Its declarations belong to
`PrimesX2NY2.Forms`, together with the quotient defined in `FormClassGroup.lean`. -/

namespace PrimesX2NY2.Forms

open PrimesX2NY2.Genus

/-- **Dirichlet composition** of two classes of forms of discriminant `D`. (Cox, §3, Thm 3.9.)

`composeForm_respects` allows `composeForm` to descend to the quotient.

Cox's Theorem 3.9 concerns negative discriminants. That assumption is used for
concordance and supplies `D ≠ 0` for Gauss's minor relations. The definition is
total: when `D < 0` it gives Dirichlet composition, and otherwise it returns its
first argument. The group-law theorems apply only to `D < 0`, so they do not use
the fallback branch. Use `compose_mk` to compute on representatives. -/
noncomputable def compose (D : ℤ) : FormClassGroup D → FormClassGroup D → FormClassGroup D :=
  if hD : D < 0 then
    Quotient.lift₂ (fun F G => Quotient.mk (properSetoid D) (composeForm D hD F G))
      (fun F₁ G₁ F₂ G₂ hF hG => Quotient.sound (composeForm_respects D hD F₁ G₁ F₂ G₂ hF hG))
  else fun a _ => a

/-- The computation rule for `compose` on the negative-discriminant branch. -/
theorem compose_mk (D : ℤ) (hD : D < 0) (F G : DiscrForms D) :
    compose D (Quotient.mk (properSetoid D) F) (Quotient.mk (properSetoid D) G)
      = Quotient.mk (properSetoid D) (composeForm D hD F G) := by
  simp only [compose, dif_pos hD]; rfl

/-- Any direct composition of a coprime pair represents the class product. The canonical
`composeForm` and the supplied direct composite are properly equivalent by uniqueness of direct
composition, so their quotient classes agree. -/
theorem compose_eq_of_directlyComposes (D : ℤ) (hD : D < 0)
    (F G P : DiscrForms D) (hcop : IsCoprime F.1.a G.1.a)
    (hP : DirectlyComposes F.1 G.1 P.1) :
    compose D (Quotient.mk (properSetoid D) F) (Quotient.mk (properSetoid D) G)
      = Quotient.mk (properSetoid D) P := by
  rw [compose_mk D hD F G]
  exact Quotient.sound
    (directlyComposes_unique_of_coprime F.1 G.1 (composeForm D hD F G).1 P.1 D
      hD F.2.1 G.2.1 hcop (composeForm_directlyComposes D hD F G)
      (composeForm_discr D hD F G) hP P.2.1)

/-- **Theorem 3.9, commutativity.** Dirichlet composition is commutative on `C(D)`. -/
theorem compose_comm (D : ℤ) (hD : D < 0) (x y : FormClassGroup D) :
    compose D x y = compose D y x := by
  induction x using Quotient.inductionOn with | _ F =>
  induction y using Quotient.inductionOn with | _ G =>
  rw [compose_mk D hD F G, compose_mk D hD G F]
  exact Quotient.sound (composeForm_comm D hD F G)

/-- **Theorem 3.9, identity.** The principal class is a (two-sided, by `compose_comm`) identity. -/
theorem compose_principalClass (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1)
    (x : FormClassGroup D) : compose D x (principalClass D hD4) = x := by
  induction x using Quotient.inductionOn with | _ F =>
  have hPeq : principalClass D hD4
      = Quotient.mk (properSetoid D) (⟨principalForm D, principalForm_discr D hD4,
          principalForm_primitive D, principalForm_pos D⟩ : DiscrForms D) := rfl
  rw [hPeq, compose_comm D hD _ _, compose_mk D hD _ F]
  exact Quotient.sound (composeForm_principal_left D hD F _ rfl)

/-- **Theorem 3.9, associativity.** Choose united representatives with pairwise coprime
leading coefficients and common middle coefficient `B`. Both bracketings then directly compose
to the same form `⟨a₁a₂a₃, B, C⟩`; uniqueness of direct composition identifies their classes. -/
theorem class_group_mul_assoc (D : ℤ) (hD : D < 0) (x y z : FormClassGroup D) :
    compose D (compose D x y) z = compose D x (compose D y z) := by
  induction x using Quotient.inductionOn with | _ F =>
  induction y using Quotient.inductionOn with | _ G =>
  induction z using Quotient.inductionOn with | _ H =>
  obtain ⟨F', G', H', B, C, hFF', hGG', hHH', h12g, h13g, h23g,
      hFshape, hGshape, hHshape, hdisc⟩ := exists_united_triple D hD F G H
  have hqF : Quotient.mk (properSetoid D) F = Quotient.mk (properSetoid D) F' :=
    Quotient.sound hFF'
  have hqG : Quotient.mk (properSetoid D) G = Quotient.mk (properSetoid D) G' :=
    Quotient.sound hGG'
  have hqH : Quotient.mk (properSetoid D) H = Quotient.mk (properSetoid D) H' :=
    Quotient.sound hHH'
  rw [hqF, hqG, hqH]
  have h12 : IsCoprime F'.1.a G'.1.a :=
    Int.isCoprime_iff_gcd_eq_one.mpr h12g
  have h13 : IsCoprime F'.1.a H'.1.a :=
    Int.isCoprime_iff_gcd_eq_one.mpr h13g
  have h23 : IsCoprime G'.1.a H'.1.a :=
    Int.isCoprime_iff_gcd_eq_one.mpr h23g
  have h12_3 : IsCoprime (F'.1.a * G'.1.a) H'.1.a := h13.mul_left h23
  have h1_23 : IsCoprime F'.1.a (G'.1.a * H'.1.a) := h12.mul_right h13

  let fgQ : BinaryQF := ⟨F'.1.a * G'.1.a, B, H'.1.a * C⟩
  let ghQ : BinaryQF := ⟨G'.1.a * H'.1.a, B, F'.1.a * C⟩
  let tQ : BinaryQF := ⟨F'.1.a * G'.1.a * H'.1.a, B, C⟩
  have hfgd : fgQ.discr = D := by
    simp only [fgQ, BinaryQF.discr]
    linear_combination hdisc
  have hghd : ghQ.discr = D := by
    simp only [ghQ, BinaryQF.discr]
    linear_combination hdisc
  have htd : tQ.discr = D := by
    simp only [tQ, BinaryQF.discr]
    linear_combination hdisc
  have hfgpos : 0 < fgQ.a := by
    simpa only [fgQ] using mul_pos F'.2.2.2 G'.2.2.2
  have hghpos : 0 < ghQ.a := by
    simpa only [ghQ] using mul_pos G'.2.2.2 H'.2.2.2
  have htpos : 0 < tQ.a := by
    simpa only [tQ] using mul_pos (mul_pos F'.2.2.2 G'.2.2.2) H'.2.2.2

  have hdcFG : DirectlyComposes F'.1 G'.1 fgQ := by
    rw [hFshape, hGshape]
    simpa only [fgQ, mul_assoc] using
      dirichletForm_directlyComposes_concordant F'.1.a G'.1.a B (H'.1.a * C)
  have heqFG : ProperlyEquivalent (composeForm D hD F' G').1 fgQ :=
    directlyComposes_unique_of_coprime F'.1 G'.1 (composeForm D hD F' G').1 fgQ D
      hD F'.2.1 G'.2.1 h12 (composeForm_directlyComposes D hD F' G')
      (composeForm_discr D hD F' G') hdcFG hfgd
  have hfgp : fgQ.Primitive :=
    (primitive_of_properlyEquivalent heqFG).mp (composeForm_primitive D hD F' G')
  let FG : DiscrForms D := ⟨fgQ, hfgd, hfgp, hfgpos⟩

  have hdcGH : DirectlyComposes G'.1 H'.1 ghQ := by
    rw [hGshape, hHshape]
    simpa only [ghQ, mul_assoc, mul_comm, mul_left_comm] using
      dirichletForm_directlyComposes_concordant G'.1.a H'.1.a B (F'.1.a * C)
  have heqGH : ProperlyEquivalent (composeForm D hD G' H').1 ghQ :=
    directlyComposes_unique_of_coprime G'.1 H'.1 (composeForm D hD G' H').1 ghQ D
      hD G'.2.1 H'.2.1 h23 (composeForm_directlyComposes D hD G' H')
      (composeForm_discr D hD G' H') hdcGH hghd
  have hghp : ghQ.Primitive :=
    (primitive_of_properlyEquivalent heqGH).mp (composeForm_primitive D hD G' H')
  let GH : DiscrForms D := ⟨ghQ, hghd, hghp, hghpos⟩

  have hdcLeft : DirectlyComposes FG.1 H'.1 tQ := by
    change DirectlyComposes fgQ H'.1 tQ
    rw [hHshape]
    simpa only [fgQ, tQ, mul_assoc] using
      dirichletForm_directlyComposes_concordant
        (F'.1.a * G'.1.a) H'.1.a B C
  have heqT : ProperlyEquivalent (composeForm D hD FG H').1 tQ :=
    directlyComposes_unique_of_coprime FG.1 H'.1 (composeForm D hD FG H').1 tQ D
      hD FG.2.1 H'.2.1 h12_3 (composeForm_directlyComposes D hD FG H')
      (composeForm_discr D hD FG H') hdcLeft htd
  have htp : tQ.Primitive :=
    (primitive_of_properlyEquivalent heqT).mp (composeForm_primitive D hD FG H')
  let T : DiscrForms D := ⟨tQ, htd, htp, htpos⟩

  have hdcRight : DirectlyComposes F'.1 GH.1 tQ := by
    change DirectlyComposes F'.1 ghQ tQ
    rw [hFshape]
    simpa only [ghQ, tQ, mul_assoc] using
      dirichletForm_directlyComposes_concordant
        F'.1.a (G'.1.a * H'.1.a) B C
  have hFGclass :
      compose D (Quotient.mk (properSetoid D) F') (Quotient.mk (properSetoid D) G') =
        Quotient.mk (properSetoid D) FG :=
    compose_eq_of_directlyComposes D hD F' G' FG h12 (by simpa only [FG] using hdcFG)
  have hGHclass :
      compose D (Quotient.mk (properSetoid D) G') (Quotient.mk (properSetoid D) H') =
        Quotient.mk (properSetoid D) GH :=
    compose_eq_of_directlyComposes D hD G' H' GH h23 (by simpa only [GH] using hdcGH)
  have hLeftclass :
      compose D (Quotient.mk (properSetoid D) FG) (Quotient.mk (properSetoid D) H') =
        Quotient.mk (properSetoid D) T :=
    compose_eq_of_directlyComposes D hD FG H' T h12_3 (by simpa only [T] using hdcLeft)
  have hRightclass :
      compose D (Quotient.mk (properSetoid D) F') (Quotient.mk (properSetoid D) GH) =
        Quotient.mk (properSetoid D) T :=
    compose_eq_of_directlyComposes D hD F' GH T h1_23 (by simpa only [T] using hdcRight)
  rw [hFGclass, hLeftclass, hGHclass, hRightclass]

/-- Taking opposite forms respects proper equivalence. The conjugated matrix
`diag(1,-1) M diag(1,-1)` still has determinant one and acts on the opposite forms. -/
theorem opposite_properlyEquivalent {f g : BinaryQF}
    (h : ProperlyEquivalent f g) : ProperlyEquivalent f.opposite g.opposite := by
  obtain ⟨M, hM, rfl⟩ := h
  refine ⟨!![M 0 0, -M 0 1; -M 1 0, M 1 1], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    have hM' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact hM
    simpa only [neg_mul, mul_neg, neg_neg] using hM'
  · simp only [action, BinaryQF.opposite, BinaryQF.mk.injEq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one]
    refine ⟨?_, ?_, ?_⟩ <;> ring

/-- The opposite form together with its discriminant, primitivity, and positivity proofs. -/
def oppositeDiscrForm (D : ℤ) (F : DiscrForms D) : DiscrForms D :=
  ⟨F.1.opposite,
    (opposite_discr F.1).trans F.2.1,
    (opposite_primitive F.1).2 F.2.2.1,
    (opposite_pos F.1).2 F.2.2.2⟩

/-- Inversion on form classes, induced by taking the opposite form. -/
def classInverse (D : ℤ) : FormClassGroup D → FormClassGroup D :=
  Quotient.map (oppositeDiscrForm D) (fun _ _ h ↦ opposite_properlyEquivalent h)

@[simp] theorem classInverse_mk (D : ℤ) (F : DiscrForms D) :
    classInverse D (Quotient.mk (properSetoid D) F) =
      Quotient.mk (properSetoid D) (oppositeDiscrForm D F) := rfl

/-- **Theorem 3.9, inverse** (Cox §3). The inverse of the class of `f` is the class
of the opposite form `a x² − b x y + c y²`. -/
theorem thm_3_9_inverse (D : ℤ) (hD : D < 0) (f : BinaryQF) (hd : f.discr = D)
    (hp : f.Primitive) (ha : 0 < f.a)
    (hd' : f.opposite.discr = D) (hp' : f.opposite.Primitive) (ha' : 0 < f.opposite.a) :
    compose D (classOf D f ⟨hd, hp, ha⟩) (classOf D f.opposite ⟨hd', hp', ha'⟩)
      = principalClass D (by rw [← hd]; exact discr_mod_four f) := by
  let F : DiscrForms D := ⟨f, hd, hp, ha⟩
  let Q : BinaryQF := ⟨1, f.b, f.a * f.c⟩
  have hQd : Q.discr = D := by
    change f.b ^ 2 - 4 * 1 * (f.a * f.c) = D
    rw [show 4 * 1 * (f.a * f.c) = 4 * f.a * f.c by ring]
    exact hd
  have hQp : Q.Primitive := by simp [Q, BinaryQF.Primitive]
  have hQa : 0 < Q.a := by simp [Q]
  let P : DiscrForms D := ⟨Q, hQd, hQp, hQa⟩
  set hc := concordance f f.opposite D hD ha hd' hp' ha' with hhc
  let G : DiscrForms D :=
    ⟨hc.choose, hc.choose_spec.2.1, hc.choose_spec.2.2.1, hc.choose_spec.2.2.2.1⟩
  have hOG : classOf D f.opposite ⟨hd', hp', ha'⟩ =
      Quotient.mk (properSetoid D) G := Quotient.sound hc.choose_spec.1
  rw [hOG]
  have hDC0 : DirectlyComposes f f.opposite Q := directlyComposes_opposite_one f
  have hDC : DirectlyComposes f G.1 Q :=
    directlyComposes_of_properlyEquivalent_right f f.opposite Q G.1 hDC0
      hc.choose_spec.1 ha'.ne' (by rw [hd, hQd]) (by rw [hQd]; exact ne_of_lt hD)
  change compose D (Quotient.mk (properSetoid D) F) (Quotient.mk (properSetoid D) G) = _
  rw [compose_eq_of_directlyComposes D hD F G P
    (Int.isCoprime_iff_gcd_eq_one.mpr hc.choose_spec.2.2.2.2) hDC]
  exact Quotient.sound (principal_of_a_one D Q hQd rfl)

/-- The class induced by the opposite form is a left inverse for every class. -/
theorem classInverse_mul (D : ℤ) (hD : D < 0)
    (hD4 : D % 4 = 0 ∨ D % 4 = 1) (x : FormClassGroup D) :
    compose D (classInverse D x) x = principalClass D hD4 := by
  induction x using Quotient.inductionOn with
  | _ F =>
    rw [compose_comm D hD]
    exact thm_3_9_inverse D hD F.1 F.2.1 F.2.2.1 F.2.2.2
      ((opposite_discr F.1).trans F.2.1)
      ((opposite_primitive F.1).2 F.2.2.1)
      ((opposite_pos F.1).2 F.2.2.2)

/-- **Theorem 3.9** (Cox §3). For `D < 0`, Dirichlet composition is associative
and commutative, the principal class is an identity, and every class has an inverse. -/
theorem isCommGroup (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (∀ x y z : FormClassGroup D, compose D (compose D x y) z = compose D x (compose D y z))
      ∧ (∀ x y : FormClassGroup D, compose D x y = compose D y x)
      ∧ (∀ x : FormClassGroup D, compose D x (principalClass D hD4) = x)
      ∧ (∀ x : FormClassGroup D, ∃ y : FormClassGroup D,
          compose D x y = principalClass D hD4) := by
  refine ⟨class_group_mul_assoc D hD, compose_comm D hD,
    compose_principalClass D hD hD4, ?_⟩
  intro x
  refine ⟨classInverse D x, ?_⟩
  rw [compose_comm D hD]
  exact classInverse_mul D hD hD4 x

/-- The commutative group structure on proper classes of positive primitive forms. -/
@[reducible] noncomputable def formClassCommGroup (D : ℤ) (hD : D < 0)
    (hD4 : D % 4 = 0 ∨ D % 4 = 1) : CommGroup (FormClassGroup D) where
  mul := compose D
  mul_assoc := class_group_mul_assoc D hD
  one := principalClass D hD4
  one_mul x := by
    change compose D (principalClass D hD4) x = x
    rw [compose_comm D hD]
    exact compose_principalClass D hD hD4 x
  mul_one := compose_principalClass D hD hD4
  inv := classInverse D
  inv_mul_cancel := classInverse_mul D hD hD4
  mul_comm := compose_comm D hD

/-- The class group instance for negative `D ≡ 0,1 (mod 4)`. -/
noncomputable instance (D : ℤ) [hneg : Fact (D < 0)]
    [hdisc : Fact (D % 4 = 0 ∨ D % 4 = 1)] : CommGroup (FormClassGroup D) :=
  formClassCommGroup D hneg.out hdisc.out

/-- **Lemma 3.10** (Cox §3). A reduced primitive form `f = a x²+ b x y + c y²` of
discriminant `D` has order `≤ 2` in `C(D)` (its class squares to the principal
class) iff `b = 0`, `a = b`, or `a = c`. -/
theorem lemma_3_10 (D : ℤ) (f : BinaryQF) (hd : f.discr = D) (hp : f.Primitive)
    (ha : 0 < f.a) (hr : f.Reduced) :
    compose D (classOf D f ⟨hd, hp, ha⟩) (classOf D f ⟨hd, hp, ha⟩)
      = principalClass D (by rw [← hd]; exact discr_mod_four f)
      ↔ (f.b = 0 ∨ f.a = f.b ∨ f.a = f.c) := by
  have hb_sq : f.b ^ 2 ≤ f.a ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg f.b) ha.le).2 hr.1
  have hac_sq : f.a ^ 2 ≤ f.a * f.c := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hr.2.1 ha.le
  have hD : D < 0 := by
    rw [← hd]
    simp only [BinaryQF.discr]
    nlinarith [hb_sq, hac_sq, sq_pos_of_pos ha]
  have hD4 : D % 4 = 0 ∨ D % 4 = 1 := by
    rw [← hd]
    exact discr_mod_four f
  have hd' : f.opposite.discr = D := (opposite_discr f).trans hd
  have hp' : f.opposite.Primitive := (opposite_primitive f).2 hp
  have ha' : 0 < f.opposite.a := (opposite_pos f).2 ha

  let F : DiscrForms D := ⟨f, hd, hp, ha⟩
  let O : DiscrForms D := ⟨f.opposite, hd', hp', ha'⟩
  let x : FormClassGroup D := Quotient.mk (properSetoid D) F
  let y : FormClassGroup D := Quotient.mk (properSetoid D) O
  let e : FormClassGroup D := principalClass D hD4
  have hinv : compose D x y = e := by
    simpa only [x, y, e, F, O, classOf] using
      thm_3_9_inverse D hD f hd hp ha hd' hp' ha'

  constructor
  · intro hsquare
    change compose D x x = e at hsquare
    have hclass : x = y := by
      calc
        x = compose D x e := (compose_principalClass D hD hD4 x).symm
        _ = compose D x (compose D x y) := congrArg (compose D x) hinv.symm
        _ = compose D (compose D x x) y := (class_group_mul_assoc D hD x x y).symm
        _ = compose D e y := congrArg (fun q => compose D q y) hsquare
        _ = y := by
          rw [compose_comm D hD]
          exact compose_principalClass D hD hD4 y
    have hfo : ProperlyEquivalent f f.opposite := by
      have hrel : ProperlyEquivalent F.1 O.1 := Quotient.exact hclass
      simpa only [F, O] using hrel

    by_cases hb0 : f.b = 0
    · exact Or.inl hb0
    by_cases hac : f.a = f.c
    · exact Or.inr (Or.inr hac)
    have hba : |f.b| = f.a := by
      by_contra hba
      have hro : f.opposite.Reduced := by
        refine ⟨?_, ?_, ?_⟩
        · simpa only [BinaryQF.opposite, abs_neg] using hr.1
        · simpa only [BinaryQF.opposite] using hr.2.1
        · intro hboundary
          rcases hboundary with hboundary | hboundary
          · exfalso
            exact hba (by
              simpa only [BinaryQF.opposite, abs_neg] using hboundary)
          · exfalso
            exact hac (by simpa only [BinaryQF.opposite] using hboundary)
      have hpos : f.PosDef := ⟨ha, by rw [hd]; exact hD⟩
      have heq : f = f.opposite :=
        reduced_eq_of_properlyEquivalent f f.opposite hr hro hpos hfo
      have hbneg : f.b = -f.b := by
        simpa only [BinaryQF.opposite] using congrArg BinaryQF.b heq
      exact hb0 (by linarith)
    have hbnonneg : 0 ≤ f.b := hr.2.2 (Or.inl hba)
    exact Or.inr (Or.inl (hba.symm.trans (abs_of_nonneg hbnonneg)))

  · intro hspecial
    have hfo : ProperlyEquivalent f f.opposite := by
      rcases hspecial with hb0 | hab | hac
      · refine ⟨1, Matrix.det_one, ?_⟩
        rw [action_one]
        exact binaryQF_ext f f.opposite (by rfl)
          (by simp [BinaryQF.opposite, hb0])
          (by rfl)
      · refine ⟨!![1, -1; 0, 1], ?_, ?_⟩
        · rw [Matrix.det_fin_two_of]
          norm_num
        · simp only [action, BinaryQF.opposite, BinaryQF.mk.injEq,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
            Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
          refine ⟨by ring, ?_, ?_⟩
          · linear_combination -2 * hab
          · linear_combination hab
      · refine ⟨!![0, -1; 1, 0], ?_, ?_⟩
        · rw [Matrix.det_fin_two_of]
          norm_num
        · simp only [action, BinaryQF.opposite, BinaryQF.mk.injEq,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
            Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
          refine ⟨?_, by ring, ?_⟩
          · linear_combination -hac
          · linear_combination hac
    have hclass : x = y := by
      apply Quotient.sound
      change ProperlyEquivalent F.1 O.1
      simpa only [F, O] using hfo
    change compose D x x = e
    calc
      compose D x x = compose D x y := congrArg (compose D x) hclass
      _ = e := hinv

/-- **Proposition 3.11** (Cox §3). For `D ≡ 0,1 (mod 4)` negative, the class group
`C(D)` has exactly `2^{μ−1}` elements of order `≤ 2`, where `μ = mu D`. -/
theorem prop_3_11 (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    {x : FormClassGroup D | compose D x x = principalClass D hD4}.ncard = 2 ^ (mu D - 1) := by
  sorry

end PrimesX2NY2.Forms
