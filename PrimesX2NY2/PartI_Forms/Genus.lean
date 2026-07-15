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

/-- Values of `f` are congruent mod `p` when the inputs are (eval is a polynomial). -/
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

/-- The CRT core of Cox Lemma 2.25: a primitive form takes a value coprime to `M` (`M ≠ 0`),
combining the per-prime witnesses `(1,0),(0,1),(1,1)` via the Chinese Remainder Theorem over
the prime factors of `M`. -/
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
  -- p ∈ primeFactors
  have hpmem : p ∈ M.natAbs.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, Int.natAbs_ne_zero.mpr hM⟩
    have := Int.natAbs_dvd_natAbs.mpr hpM
    simpa using this
  have hmemL := Finset.mem_toList.mpr hpmem
  -- congruences kx ≡ wx p, ky ≡ wy p (cast to ℤ)
  have hkxp : (kx:ℤ) ≡ (wx p : ℤ) [ZMOD (p:ℤ)] := by exact_mod_cast hkx p hmemL
  have hkyp : (ky:ℤ) ≡ (wy p : ℤ) [ZMOD (p:ℤ)] := by exact_mod_cast hky p hmemL
  have hcong := eval_cong f (kx:ℤ) (wx p : ℤ) (ky:ℤ) (wy p : ℤ) (p:ℤ) hkxp hkyp
  -- witness: ¬ p | f.eval (wx p) (wy p)
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

/-- **Lemma 2.25** (Cox §2). A primitive form `f` *properly* represents a value coprime to any
`M ≠ 0` (the per-prime/CRT value, made proper by dividing out `gcd(x,y)`). (Cox §2, Exercise 2.18.) -/
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
— the prerequisite for Dirichlet composition. (Via Lemma 2.25 + Lemma 2.3.) -/
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
composition of `f` and `g`: `f(x₁,y₁)·g(x₂,y₂) = F(X,Y)`. (Pure polynomial identity.) -/
theorem dirichlet_compose_repr (a a' B C x₁ y₁ x₂ y₂ : ℤ) :
    (⟨a, B, a' * C⟩ : BinaryQF).eval x₁ y₁ * (⟨a', B, a * C⟩ : BinaryQF).eval x₂ y₂
      = (⟨a * a', B, C⟩ : BinaryQF).eval
          (x₁ * x₂ - C * y₁ * y₂) (a * x₁ * y₂ + a' * x₂ * y₁ + B * y₁ * y₂) := by
  simp only [BinaryQF.eval]; ring

/-- **Representative-level Dirichlet composition** of `F, G : DiscrForms D` (`D < 0`):
bring `G` to a form `g'` concordant with `F` (leading coeff coprime to `F.a`, via
`concordance`), then take the Dirichlet composite `dirichletForm F.1 g'`, which is a
primitive positive form of discriminant `D` by `prop_3_8`. The concordant choice is made by
`Classical.choice`; well-definedness on classes (Cox Thm 3.9, deferred to the §7 ideal
correspondence) would neutralise that choice. -/
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

/-- **Left identity (form level).** If `P` is the principal class, `composeForm D hD P F` is
properly equivalent to `F`. Choice-robust: holds for the `Classical`-chosen concordant `g'`,
since composing with the principal form is a translation. (Cox Thm 3.9, form-level identity.) -/
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

/-- Projection-friendly form of `translation_equiv`: two forms with equal nonzero leading
coefficient, equal discriminant, and `g.b ≡ f.b (mod 2 f.a)` are properly equivalent. -/
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

/-- **(3i) — concordant-choice invariance** — *STATED, NOT PROVED* (this is the single deferred
fact unlocking class-level respect + the form-level inverse and associativity; only the
form-level identity escapes it, see `composeForm_principal_left`). The Dirichlet composite
`dirichletForm F.1 g'` is independent, up to proper equivalence, of which concordant
representative `g'` of the second class is chosen. Cox (Thm 3.9 proof) routes well-definedness
through the §7 ideal class group correspondence; the elementary direct route is Cox Exercise
3.5(c) (representative-invariance of *direct* composition), whose parts (a) `translation_equiv`
and (b) `dirichlet_compose_repr` are already in hand. -/
theorem concordant_choice_invariant (D : ℤ) (F : DiscrForms D) (g₁ g₂ : BinaryQF)
    (he : ProperlyEquivalent g₁ g₂)
    (hd₁ : g₁.discr = D) (ha₁ : 0 < g₁.a) (hc₁ : Int.gcd F.1.a g₁.a = 1)
    (hd₂ : g₂.discr = D) (ha₂ : 0 < g₂.a) (hc₂ : Int.gcd F.1.a g₂.a = 1) :
    ProperlyEquivalent (dirichletForm F.1 g₁) (dirichletForm F.1 g₂) := sorry
-- FLAG (Wave 20): under-hypothesized — missing `hD : D < 0`. The proof needs `D ≠ 0` (the minor
-- machinery of Cox Ex 3.1; see the `⟨1,0,0⟩` counterexample at `directlyComposes_minors`), and
-- `F.Primitive ∧ 0 < F.a` does not supply it. Cox's Thm 3.9 states the ambient explicitly:
-- "Let `D ≡ 0,1 mod 4` be **negative**". The fully-proved form is
-- `concordant_choice_invariant_of_neg`; restating this one with `hD` is a one-line change,
-- deliberately not made unilaterally.

/-- **Direct composition** (Cox §3.A, (3.1)). `F` is the *direct composition* of `f` and `g`
if there is an integral bilinear substitution `Bᵢ = aᵢxz+bᵢxw+cᵢyz+dᵢyw` with
`f(x,y)·g(z,w) = F(B₁,B₂)`, whose leading-coefficient minors take the `+` sign of Gauss's
formulas (3.1): `a₁b₂−a₂b₁ = f(1,0)`, `a₁c₂−a₂c₁ = g(1,0)`. Carrier-neutral (a statement about
`eval`), so it ports unchanged to any binary-quadratic-form carrier. -/
def DirectlyComposes (f g F : BinaryQF) : Prop :=
  ∃ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ,
    (∀ x y z w : ℤ, f.eval x y * g.eval z w
      = F.eval (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
               (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w))
    ∧ a₁ * b₂ - a₂ * b₁ = f.eval 1 0
    ∧ a₁ * c₂ - a₂ * c₁ = g.eval 1 0

/-- **Cox 3.5(d) (concordant-shape).** The Gauss composite of the concordant forms
`⟨a,B,a'C⟩`, `⟨a',B,aC⟩` is their *direct* composition `⟨aa',B,C⟩` (the `+` sign of (3.1) holds).
The substitution is `(1,0,0,-C ; 0,a,a',B)`, and the composition identity is the Gauss bilinear
identity `dirichlet_compose_repr`. To lift to arbitrary concordant `f,g` via `dirichletForm f g`
one bridges `f ~ ⟨a,B,a'C⟩` by `translation_equiv` + the representative-invariance
`directlyComposes_of_properlyEquivalent_left` (Cox 3.5(c), stated below). -/
theorem dirichletForm_directlyComposes_concordant (a a' B C : ℤ) :
    DirectlyComposes (⟨a, B, a' * C⟩ : BinaryQF) ⟨a', B, a * C⟩ ⟨a * a', B, C⟩ :=
  ⟨1, 0, 0, -C, 0, a, a', B,
    fun x y z w => by simp only [BinaryQF.eval]; ring,
    by simp only [BinaryQF.eval]; ring,
    by simp only [BinaryQF.eval]; ring⟩

/-- **Commutativity of Dirichlet composition up to proper equivalence.** `dirichletForm f g ~
dirichletForm g f`: the two composites have equal leading coefficient `f.a·g.a` and their
`B`-values agree modulo `2 f.a g.a` (both solve the same simultaneous congruences, so are equal
by Lemma 3.2's uniqueness), so they are related by a translation. This is the symmetry lemma
that lets first-argument invariance follow from second-argument invariance in the respect
proof. -/
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
minors are pinned: `(a₁d₂−a₂d₁)−(b₁c₂−b₂c₁) = h.b` and `c₁d₂−c₂d₁ = h.c`.

The nonzero-discriminant hypothesis is essential — Cox states it verbatim in Exercise 3.1 ("all
three forms have discriminant `D ≠ 0`"); the degenerate `h=k=G=⟨1,0,0⟩` with witness
`(1,0,0,0,0,1,1,5)` is a direct composition for which `(a₁d₂−a₂d₁)−(b₁c₂−b₂c₁)=5≠0=h.b`.

Proof: the composition identity read as a form in `(z,w)` gives, for every `x,y`, the
discriminant identity `(h(x,y))²·disc k = Ψ(x,y)²·disc G` with `Ψ = (a₁b₂−a₂b₁)x² +
((a₁d₂−a₂d₁)−(b₁c₂−b₂c₁))xy + (c₁d₂−c₂d₁)y²` (Cox 3.1(a),(b)); cancelling the common nonzero
discriminant yields `h(x,y)² = Ψ(x,y)²` as a polynomial identity, and comparing the `x³y`- and
`x²y²`-coefficients (evaluating at `x∈{−2,…,2}, y=1`) pins the two minors, the `+` sign carried
over from `a₁b₂−a₂b₁ = h.a`. -/
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

This is the faithful form of Cox's Exercise 3.5(c): §3.A works throughout with primitive positive
definite forms of a fixed discriminant `D < 0`, so `h.a > 0` and `disc = D ≠ 0` hold there. The
proof pre-composes the bilinear substitution with the `SL₂(ℤ)` matrix `M` carrying `h → h'`
(giving the new coefficients `āᵢ = aᵢ·M₀₀ + cᵢ·M₁₀`, …); the composition identity and the
`k`-side `(3.1)` sign are elementary (`eval_action`/`Matrix.det`/`ring`), while the `h`-side sign
`ā₁b̄₂−ā₂b̄₁ = h'(1,0)` reduces via `directlyComposes_minors` to `M₀₀²·h.a + M₀₀M₁₀·h.b +
M₁₀²·h.c = h(M₀₀,M₁₀) = h'(1,0)`. -/
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

/-- **Gauss' minor relations, `g`-side mirror (Cox Exercise 3.1 / [Gauss §235]).** The companion
of `directlyComposes_minors`: reading the composition identity as a form in `(x,y)` (rather than
`(z,w)`) gives `(k(z,w))²·disc h = Φ(z,w)²·disc G` with `Φ = m₁₃·z² + (m₁₄+m₂₃)·zw + m₂₄·w²`;
cancelling the common nonzero discriminant and comparing coefficients pins the remaining two
minors. Note the **`+` sign** in `m₁₄+m₂₃ = k.b` (against the `−` in `m₁₄−m₂₃ = h.b`), and that
this mirror cancels `disc h` rather than `disc k`.

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

The discriminant hypotheses match Cox's Exercise 3.1 verbatim ("all three forms have discriminant
`D ≠ 0`") and are essential — see the degenerate `⟨1,0,0⟩` counterexample recorded at
`directlyComposes_minors`. In Cox's §3.A ambient (primitive positive definite forms of a fixed
`D < 0`) both hold automatically. Discharged by
`directlyComposes_of_properlyEquivalent_left_of_discr`. -/
theorem directlyComposes_of_properlyEquivalent_left (h k G h' : BinaryQF)
    (hDC : DirectlyComposes h k G) (he : ProperlyEquivalent h h')
    (hha : h.a ≠ 0) (hkG : k.discr = G.discr) (hG0 : G.discr ≠ 0) :
    DirectlyComposes h' k G :=
  directlyComposes_of_properlyEquivalent_left_of_discr h k G h' hDC he hha hkG hG0

/-- **Uniqueness of direct composition up to proper equivalence** (Cox 4b / [Gauss §§236–240];
Cox defers this to §7, see Theorem 3.9's proof: *"we will assume that (i) and (ii) are true"*).

Two direct compositions `F`, `F'` of the same pair `(f,g)` of discriminant `D < 0` with
`gcd(f.a, g.a) = 1` are properly equivalent.

Proof (equal-Plücker → `SL₂` → transport). By `directlyComposes_minors` and
`directlyComposes_minors_right`, **all six minors of the substitution matrix are determined by
`(f,g)`**, so the two witnesses `M`, `M'` have identical Plücker vectors (in particular
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

Hypothesis divergence (resolved, Wave 20): Cox omits `D < 0` and `gcd(f.a,g.a)=1` because §3.A
carries them ambiently (Thm 3.9: "Let `D ≡ 0,1 mod 4` be **negative**"; and its proof replaces `g`
by a properly equivalent form "where `gcd(a,a') = 1`"). Both are genuinely needed — `D ≠ 0` by the
`⟨1,0,0⟩` counterexample at `directlyComposes_minors`, and coprimality by the Bézout that makes the
transition matrix integral. `F.Primitive` and `0 < F.a` turn out to be unnecessary and were dropped.
Discharged by `directlyComposes_unique_of_coprime`. -/
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

(Replaces an earlier vacuous statement whose right-hand side `∃ S, p ∈ S` was
always true.) -/
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

/-- Discriminant of the Dirichlet composite of a **two-way coprime** pair (the concordant case). -/
theorem dirichletForm_discr_of_coprime (f g : BinaryQF) (D : ℤ) (hf : f.discr = D)
    (hg : g.discr = D) (hcop : Int.gcd f.a g.a = 1) : (dirichletForm f g).discr = D :=
  dirichletForm_discr f g D hf hg (by rw [hcop]; simp)

/-- **The Dirichlet composite IS a direct composition of its (concordant) pair** — the linchpin
tying Cox's explicit formula (3.7) to Gauss's relation (3.1).

With `B := dirichletB f g` and `C := (B²−D)/(4·f.a·g.a)`, `dirichletForm f g = ⟨f.a·g.a, B, C⟩`,
and the translations `f ~ ⟨f.a, B, g.a·C⟩`, `g ~ ⟨g.a, B, f.a·C⟩` (Cox 3.5(a), via
`dirichletB_spec1/2` and `translation_equiv_proj`) put the pair into the concordant shape of
`dirichletForm_directlyComposes_concordant` (Cox 3.5(b)); transporting both arguments back by
Cox 3.5(c) gives the claim. This is on the critical path for BOTH well-definedness of `compose`
and (via united forms) associativity. -/
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

/-- **(3i) Concordant-choice invariance** — the Dirichlet composite does not depend (up to `~`) on
which concordant representative is chosen. Carries the `hD : D < 0` that the bare
`concordant_choice_invariant` lacks (see the FLAG there). -/
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

/-- **Class-level respect** — the `Quotient.lift₂` obligation for `compose`:
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

end PrimesX2NY2.Genus

/-! ## The class group operation

`compose` and the Cox §3 class-group theorems live here rather than in `FormClassGroup.lean`
because defining `compose` requires `composeForm`/`concordance`/`DirectlyComposes`, which are
downstream of that file in the import DAG. The declarations keep their fully-qualified
`PrimesX2NY2.Forms.*` names, so blueprint nodes and callers are unaffected. -/

namespace PrimesX2NY2.Forms

open PrimesX2NY2.Genus

/-- **Dirichlet composition** of two classes of forms of discriminant `D`. (Cox, §3, Thm 3.9.)

Well-defined: `composeForm` is lifted through the quotient by `composeForm_respects`.

Cox defines `C(D)` only for **negative** `D` (Thm 3.9: "Let `D ≡ 0,1 mod 4` be negative"), and the
composition genuinely needs `D < 0` (concordance, and `D ≠ 0` for the Gauss minor relations). Since
`compose`'s signature carries no `hD`, the definition branches: on `D < 0` it is the honest
Dirichlet composition, and off that domain it is the junk projection `fun a _ => a`. Every Cox
theorem about `compose` carries `hD : D < 0`, so the junk branch is never observed; use
`compose_mk` to reduce. (Junk-value convention, as with `x / 0 = 0` in Mathlib.) -/
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

/-- **Theorem 3.9, associativity** — *STATED, NOT PROVED*.

Cox postpones associativity to §7 (ideal class groups): "The proofs of (i) and (ii) can be done
directly using the definition of Dirichlet composition (see Dirichlet [28, Supplement X] or Flath
[36, §V.2]), but the argument is much easier using ideal class groups (to be studied in §7). We
will therefore postpone this part of the proof until then." Gauss's elementary route (§240) is the
notorious **28 equations**.

ROUTE (chosen, Wave 20 recon — Dirichlet's *united forms*, i.e. Flath §V.2): pick representatives
with **pairwise coprime** `a₁,a₂,a₃`, a common `B`, and a common `C` with `B² − 4a₁a₂a₃C = D`, so
`f ~ ⟨a₁,B,a₂a₃C⟩`, `g ~ ⟨a₂,B,a₁a₃C⟩`, `h ~ ⟨a₃,B,a₁a₂C⟩`. Four instantiations of
`dirichletForm_directlyComposes_concordant` then give `(f∗g)∗h = ⟨a₁a₂a₃,B,C⟩ = f∗(g∗h)` **on the
nose** — associativity is `rfl` at the form level, and the 28 equations evaporate (they are already
paid, once, inside `directlyComposes_minors`/`_right` and `directlyComposes_unique_of_coprime`).
Needs: triple concordance (clone of `concordance`), a common `B` (two applications of `lemma_3_2`),
and `compose_eq_of_directlyComposes`. Estimated 300–400 lines. -/
theorem class_group_mul_assoc (D : ℤ) (hD : D < 0) (x y z : FormClassGroup D) :
    compose D (compose D x y) z = compose D x (compose D y z) := sorry

/-- **Theorem 3.9** (Cox §3). For `D < 0`, Dirichlet composition makes `C(D)` a
finite abelian group: it is associative and commutative, the principal class is a
right identity, and every class has an inverse. (Faithful replacement of the
earlier vacuous `Nonempty (CommGroup …)`, which holds for any nonempty type.)

Commutativity and the identity are discharged (`compose_comm`, `compose_principalClass`);
associativity is `class_group_mul_assoc` (stubbed, route pinned) and the inverse is
`thm_3_9_inverse` (stubbed). -/
theorem isCommGroup (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (∀ x y z : FormClassGroup D, compose D (compose D x y) z = compose D x (compose D y z))
      ∧ (∀ x y : FormClassGroup D, compose D x y = compose D y x)
      ∧ (∀ x : FormClassGroup D, compose D x (principalClass D hD4) = x)
      ∧ (∀ x : FormClassGroup D, ∃ y : FormClassGroup D, compose D x y = principalClass D hD4) := by
  sorry

/-- **Theorem 3.9, inverse** (Cox §3). The inverse of the class of `f` is the class
of the opposite form `a x² − b x y + c y²`. -/
theorem thm_3_9_inverse (D : ℤ) (f : BinaryQF) (hd : f.discr = D)
    (hp : f.Primitive) (ha : 0 < f.a)
    (hd' : f.opposite.discr = D) (hp' : f.opposite.Primitive) (ha' : 0 < f.opposite.a) :
    compose D (classOf D f ⟨hd, hp, ha⟩) (classOf D f.opposite ⟨hd', hp', ha'⟩)
      = principalClass D (by rw [← hd]; exact discr_mod_four f) := by
  sorry

/-- **Lemma 3.10** (Cox §3). A reduced primitive form `f = a x²+ b x y + c y²` of
discriminant `D` has order `≤ 2` in `C(D)` (its class squares to the principal
class) iff `b = 0`, `a = b`, or `a = c`. -/
theorem lemma_3_10 (D : ℤ) (f : BinaryQF) (hd : f.discr = D) (hp : f.Primitive)
    (ha : 0 < f.a) (hr : f.Reduced) :
    compose D (classOf D f ⟨hd, hp, ha⟩) (classOf D f ⟨hd, hp, ha⟩)
      = principalClass D (by rw [← hd]; exact discr_mod_four f)
      ↔ (f.b = 0 ∨ f.a = f.b ∨ f.a = f.c) := by
  sorry

/-- **Proposition 3.11** (Cox §3). For `D ≡ 0,1 (mod 4)` negative, the class group
`C(D)` has exactly `2^{μ−1}` elements of order `≤ 2`, where `μ = mu D`. -/
theorem prop_3_11 (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    {x : FormClassGroup D | compose D x x = principalClass D hD4}.ncard = 2 ^ (mu D - 1) := by
  sorry

end PrimesX2NY2.Forms
