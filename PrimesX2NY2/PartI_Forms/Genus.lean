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

end PrimesX2NY2.Genus
