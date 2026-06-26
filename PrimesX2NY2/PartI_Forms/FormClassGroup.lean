/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.Forms

/-!
# Part I, Chapter 3 - The form class group and Dirichlet composition

Cox, *Primes of the Form x² + ny²*, §3.A.

Proper equivalence classes of primitive positive definite forms of a fixed
discriminant `D < 0` form a finite abelian group `C(D)` under Dirichlet
composition.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.Forms

/-- The **opposite** of `f = a x² + b x y + c y²` is `a x² − b x y + c y²`. Its class
is the inverse of the class of `f` in `C(D)`. (Cox §3, Thm 3.9.) -/
def BinaryQF.opposite (f : BinaryQF) : BinaryQF := ⟨f.a, -f.b, f.c⟩

/-- The carrier for the form class group: primitive forms of discriminant `D` with
positive leading coefficient (for `D < 0` this is exactly the primitive positive
definite forms). (Cox §3.) -/
def DiscrForms (D : ℤ) : Type := {f : BinaryQF // f.discr = D ∧ f.Primitive ∧ 0 < f.a}

/-- Proper equivalence as a `Setoid` on the forms of discriminant `D`. (Cox, §3.) -/
def properSetoid (D : ℤ) : Setoid (DiscrForms D) where
  r f g := ProperlyEquivalent f.1 g.1
  iseqv := ⟨fun f => properlyEquivalent_equivalence.refl f.1,
    fun h => properlyEquivalent_equivalence.symm h,
    fun h₁ h₂ => properlyEquivalent_equivalence.trans h₁ h₂⟩

/-- The **form class group** `C(D)` as a type: proper equivalence classes of
primitive positive definite forms of discriminant `D`. The group law is Dirichlet
composition. (Cox, §3.) -/
def FormClassGroup (D : ℤ) : Type := Quotient (properSetoid D)

/-- The class in `C(D)` of a primitive form `f` with positive leading coefficient. -/
def classOf (D : ℤ) (f : BinaryQF) (h : f.discr = D ∧ f.Primitive ∧ 0 < f.a) :
    FormClassGroup D :=
  Quotient.mk (properSetoid D) ⟨f, h⟩

/-- **Lemma 3.5** (Cox §3). For `p₁,…,pᵣ, q₁,…,qᵣ, m` with `gcd(p₁,…,pᵣ, m) = 1`,
the congruences `pᵢ B ≡ qᵢ (mod m)` have a (unique) solution `B` iff the
compatibility conditions `pᵢ qⱼ ≡ pⱼ qᵢ (mod m)` hold for all `i, j`. -/
theorem lemma_3_5 (r : ℕ) (p q : Fin r → ℤ) (m : ℤ)
    (hcop : ∃ (t : Fin r → ℤ) (s : ℤ), s * m + ∑ i, t i * p i = 1) :
    (∃ B : ℤ, ∀ i, p i * B ≡ q i [ZMOD m]) ↔ (∀ i j, p i * q j ≡ p j * q i [ZMOD m]) := by
  constructor
  · rintro ⟨B, hB⟩ i j
    have h1 : p i * q j ≡ p i * (p j * B) [ZMOD m] := (hB j).symm.mul_left (p i)
    have h2 : p j * (p i * B) ≡ p j * q i [ZMOD m] := (hB i).mul_left (p j)
    have h3 : p i * (p j * B) = p j * (p i * B) := by ring
    exact (h3 ▸ h1).trans h2
  · intro hc
    obtain ⟨t, s, hts⟩ := hcop
    refine ⟨∑ i, t i * q i, fun j => ?_⟩
    rw [Int.modEq_iff_dvd]
    have hsum : ∑ i, t i * (p j * q i - p i * q j)
              = p j * (∑ i, t i * q i) - q j * (∑ i, t i * p i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hp : ∑ i, t i * p i = 1 - s * m := by linarith [hts]
    have key : q j - p j * (∑ i, t i * q i)
             = q j * (s * m) - ∑ i, t i * (p j * q i - p i * q j) := by
      rw [hsum, hp]; ring
    rw [key]
    apply dvd_sub
    · exact (dvd_mul_left m s).mul_left (q j)
    · apply Finset.dvd_sum
      intro i _
      have hdvd : m ∣ (p j * q i - p i * q j) := by
        have := hc i j; rwa [Int.modEq_iff_dvd] at this
      exact hdvd.mul_left (t i)

/-- Auxiliary parity fact: if `4 ∣ b² − b'²` then `b, b'` have the same parity
(so `(b+b')/2` is an integer). Used by Lemma 3.2 via the equal-discriminant
hypothesis. -/
theorem two_dvd_sub_of_four_dvd_sq_sub_sq (b b' : ℤ) (h : (4:ℤ) ∣ (b^2 - b'^2)) : (2:ℤ) ∣ (b - b') := by
  have h2 : (2:ℤ) ∣ (b - b') * (b + b') := by
    have e : b^2 - b'^2 = (b - b') * (b + b') := by ring
    exact e ▸ (dvd_trans (by norm_num) h)
  rcases Int.prime_two.dvd_or_dvd h2 with h3 | h3
  · exact h3
  · obtain ⟨k, hk⟩ := h3; exact ⟨k - b', by linarith⟩

/-- **Uniqueness** for the simultaneous congruences of Lemma 3.5: under the same
Bézout/coprimality hypothesis the solution of `pᵢ B ≡ qᵢ (mod m)` is unique modulo
`m`. (The uniqueness half of Cox's Lemma 3.5; consumed by Lemma 3.2.) -/
theorem simultaneous_congruence_unique (r : ℕ) (p q : Fin r → ℤ) (m : ℤ)
    (hcop : ∃ (t : Fin r → ℤ) (s : ℤ), s * m + ∑ i, t i * p i = 1)
    (B B' : ℤ) (hB : ∀ i, p i * B ≡ q i [ZMOD m]) (hB' : ∀ i, p i * B' ≡ q i [ZMOD m]) :
    B ≡ B' [ZMOD m] := by
  obtain ⟨t, s, hts⟩ := hcop
  rw [Int.modEq_iff_dvd]
  have hps : ∑ i, t i * (p i * (B' - B)) = (∑ i, t i * p i) * (B' - B) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hp : ∑ i, t i * p i = 1 - s * m := by linarith [hts]
  have key : B' - B = (B' - B) * (s * m) + ∑ i, t i * (p i * (B' - B)) := by rw [hps, hp]; ring
  rw [key]; apply dvd_add
  · exact (dvd_mul_left m s).mul_left (B' - B)
  · apply Finset.dvd_sum; intro i _
    have hi : p i * B ≡ p i * B' [ZMOD m] := (hB i).trans (hB' i).symm
    have he : p i * (B' - B) = p i * B' - p i * B := by ring
    have hdvd : m ∣ p i * (B' - B) := by rw [he]; exact Int.modEq_iff_dvd.mp hi
    exact hdvd.mul_left (t i)

/-- **Lemma 3.2** (Cox §3). For forms `f = a x²+ b x y + c y²` and
`g = a' x²+ b' x y + c' y²` of discriminant `D` with `gcd(a, a', (b+b')/2) = 1`,
there is a `B`, unique modulo `2 a a'`, with `B ≡ b (2a)`, `B ≡ b' (2a')`, and
`B² ≡ D (4 a a')`. -/
theorem lemma_3_2 (a b c a' b' c' D : ℤ)
    (hf : b ^ 2 - 4 * a * c = D) (hg : b' ^ 2 - 4 * a' * c' = D)
    (hcop : Int.gcd (Int.gcd a a') ((b + b') / 2) = 1) :
    ∃ B : ℤ, (B ≡ b [ZMOD (2 * a)]) ∧ (B ≡ b' [ZMOD (2 * a')])
        ∧ (B ^ 2 ≡ D [ZMOD (4 * a * a')])
        ∧ ∀ B' : ℤ, (B' ≡ b [ZMOD (2 * a)]) ∧ (B' ≡ b' [ZMOD (2 * a')])
            ∧ (B' ^ 2 ≡ D [ZMOD (4 * a * a')]) → B' ≡ B [ZMOD (2 * a * a')] := by
  have hdiff : (4:ℤ) ∣ (b^2 - b'^2) := ⟨a*c - a'*c', by linear_combination hf - hg⟩
  have hsub : (2:ℤ) ∣ (b - b') := two_dvd_sub_of_four_dvd_sq_sub_sq b b' hdiff
  have hadd : (2:ℤ) ∣ (b + b') := by obtain ⟨u,hu⟩ := hsub; exact ⟨u + b', by linarith⟩
  set β := (b + b') / 2 with hβdef
  set γ := (b*b' + D) / 2 with hγdef
  have hβ : 2 * β = b + b' := Int.mul_ediv_cancel' hadd
  have hγ2 : (2:ℤ) ∣ (b*b' + D) := by
    obtain ⟨k, hk⟩ := hadd; exact ⟨b*k - 2*a*c, by rw [← hf]; linear_combination b * hk⟩
  have hγ : 2 * γ = b*b' + D := Int.mul_ediv_cancel' hγ2
  by_cases ha : a = 0
  · subst ha
    refine ⟨b, Int.ModEq.refl b, ?_, ?_, ?_⟩
    · have hcop' : Int.gcd a' β = 1 := by
        simpa [Int.gcd, Int.natAbs_natCast, Int.natAbs_abs] using hcop
      have hcoB : IsCoprime (a' : ℤ) β := Int.isCoprime_iff_gcd_eq_one.mpr hcop'
      obtain ⟨u, hu⟩ := hsub
      have e2 : b ^ 2 - b' ^ 2 = -4 * (a' * c') := by linear_combination hf - hg
      have e3 : (2 * u) * (2 * β) = b ^ 2 - b' ^ 2 := by rw [← hu, hβ]; ring
      have h4 : (4 : ℤ) * (u * β) = 4 * (a' * (-c')) := by linear_combination e3.trans e2
      have key : u * β = a' * (-c') := mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4
      have hdu : a' ∣ u := hcoB.dvd_of_dvd_mul_right ⟨-c', key⟩
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hdu
      exact ⟨-k, by rw [hk] at hu; linear_combination -hu⟩
    · have hb2 : b ^ 2 = D := by linear_combination hf
      rw [hb2]
    · intro B' hB'
      have hBb : B' = b := by
        have := Int.modEq_iff_dvd.mp hB'.1
        simpa [zero_dvd_iff, sub_eq_zero, eq_comm] using this
      rw [hBb]
  by_cases ha' : a' = 0
  · subst ha'
    refine ⟨b', ?_, Int.ModEq.refl b', ?_, ?_⟩
    · have hcop' : Int.gcd a β = 1 := by
        simpa [Int.gcd, Int.natAbs_natCast, Int.natAbs_abs] using hcop
      have hcoB : IsCoprime (a : ℤ) β := Int.isCoprime_iff_gcd_eq_one.mpr hcop'
      obtain ⟨u, hu⟩ := hsub
      have e2 : b ^ 2 - b' ^ 2 = 4 * (a * c) := by linear_combination hf - hg
      have e3 : (2 * u) * (2 * β) = b ^ 2 - b' ^ 2 := by rw [← hu, hβ]; ring
      have h4 : (4 : ℤ) * (u * β) = 4 * (a * c) := by linear_combination e3.trans e2
      have key : u * β = a * c := mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4
      have hdu : a ∣ u := hcoB.dvd_of_dvd_mul_right ⟨c, key⟩
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hdu
      exact ⟨k, by rw [hk] at hu; linear_combination hu⟩
    · have hb2 : b' ^ 2 = D := by linear_combination hg
      rw [hb2]
    · intro B' hB'
      have hBb : B' = b' := by
        have := Int.modEq_iff_dvd.mp hB'.2.1
        simpa [zero_dvd_iff, sub_eq_zero, eq_comm] using this
      rw [hBb]
  set m : ℤ := 2 * a * a' with hm
  set p : Fin 3 → ℤ := ![a', a, β] with hp
  set q : Fin 3 → ℤ := ![a'*b, a*b', γ] with hq
  have hco : IsCoprime ((Int.gcd a a' : ℤ)) β := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  obtain ⟨u, v, huv⟩ := hco
  have hgab : ((Int.gcd a a' : ℤ)) = a * Int.gcdA a a' + a' * Int.gcdB a a' := Int.gcd_eq_gcd_ab a a'
  have hbez : ∃ (t : Fin 3 → ℤ) (s : ℤ), s * m + ∑ i, t i * p i = 1 := by
    refine ⟨![u * Int.gcdB a a', u * Int.gcdA a a', v], 0, ?_⟩
    rw [Fin.sum_univ_three]
    simp only [hp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linear_combination huv - u * hgab
  have hβγb : β * b - γ = 2 * a * c := by
    have key : 2 * (β * b - γ) = 2 * (2 * a * c) := by linear_combination b * hβ - hγ + hf
    exact mul_left_cancel₀ (by norm_num : (2:ℤ) ≠ 0) key
  have hβγb' : β * b' - γ = 2 * a' * c' := by
    have key : 2 * (β * b' - γ) = 2 * (2 * a' * c') := by linear_combination b' * hβ - hγ + hg
    exact mul_left_cancel₀ (by norm_num : (2:ℤ) ≠ 0) key
  have h01 : a' * (a*b') ≡ a * (a'*b) [ZMOD m] := by
    rw [Int.modEq_iff_dvd]; obtain ⟨w,hw⟩ := hsub
    exact ⟨w, by rw [hm]; linear_combination (a*a') * hw⟩
  have h02 : a' * γ ≡ β * (a'*b) [ZMOD m] := by
    rw [Int.modEq_iff_dvd]; exact ⟨c, by rw [hm]; linear_combination a' * hβγb⟩
  have h12 : a * γ ≡ β * (a*b') [ZMOD m] := by
    rw [Int.modEq_iff_dvd]; exact ⟨c', by rw [hm]; linear_combination a * hβγb'⟩
  have hcompat : ∀ i j, p i * q j ≡ p j * q i [ZMOD m] := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [hp, hq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;>
      first
        | exact Int.ModEq.refl _
        | exact h01 | exact h01.symm
        | exact h02 | exact h02.symm
        | exact h12 | exact h12.symm
  obtain ⟨B, hBlin⟩ := (lemma_3_5 3 p q m hbez).mpr hcompat
  have e0 : a' * B ≡ a' * b [ZMOD m] := by have := hBlin 0; simpa [hp, hq] using this
  have e1 : a * B ≡ a * b' [ZMOD m] := by have := hBlin 1; simpa [hp, hq] using this
  have e2 : β * B ≡ γ [ZMOD m] := by have := hBlin 2; simpa [hp, hq] using this
  have hb : B ≡ b [ZMOD (2*a)] := by
    rw [Int.modEq_iff_dvd] at e0 ⊢
    rw [show m = a' * (2*a) from by rw [hm]; ring] at e0
    rw [show a' * b - a' * B = a' * (b - B) from by ring] at e0
    exact (mul_dvd_mul_iff_left ha').mp e0
  have hb' : B ≡ b' [ZMOD (2*a')] := by
    rw [Int.modEq_iff_dvd] at e1 ⊢
    rw [show m = a * (2*a') from by rw [hm]; ring] at e1
    rw [show a * b' - a * B = a * (b' - B) from by ring] at e1
    exact (mul_dvd_mul_iff_left ha).mp e1
  have hquad : B^2 ≡ D [ZMOD (4*a*a')] := by
    rw [Int.modEq_iff_dvd] at hb hb' e2 ⊢
    obtain ⟨s1, hs1⟩ := hb
    obtain ⟨s2, hs2⟩ := hb'
    have hprod : (4*a*a') ∣ (B - b) * (B - b') := ⟨s1 * s2, by
      rw [show B - b = -(2*a*s1) from by linarith, show B - b' = -(2*a'*s2) from by linarith]; ring⟩
    obtain ⟨s3, hs3⟩ := e2
    have hlin : (4*a*a') ∣ ((b+b')*B - (b*b' + D)) := ⟨-s3, by
      rw [show (b+b')*B - (b*b'+D) = 2*(β*B - γ) from by rw [← hβ, ← hγ]; ring,
          show β*B - γ = -(m*s3) from by linarith, hm]; ring⟩
    rw [show D - B^2 = -((B-b)*(B-b')) - ((b+b')*B - (b*b'+D)) from by ring]
    exact dvd_sub (dvd_neg.mpr hprod) hlin
  refine ⟨B, hb, hb', hquad, ?_⟩
  intro B' ⟨hB'b, hB'b', hB'q⟩
  have f0 : a' * B' ≡ a' * b [ZMOD m] := by
    rw [Int.modEq_iff_dvd] at hB'b ⊢
    rw [show m = a' * (2*a) from by rw [hm]; ring]
    obtain ⟨w,hw⟩ := hB'b; exact ⟨w, by linear_combination a' * hw⟩
  have f1 : a * B' ≡ a * b' [ZMOD m] := by
    rw [Int.modEq_iff_dvd] at hB'b' ⊢
    rw [show m = a * (2*a') from by rw [hm]; ring]
    obtain ⟨w,hw⟩ := hB'b'; exact ⟨w, by linear_combination a * hw⟩
  have f2 : β * B' ≡ γ [ZMOD m] := by
    rw [Int.modEq_iff_dvd, hm]
    rw [Int.modEq_iff_dvd] at hB'b hB'b' hB'q
    obtain ⟨s1, hs1⟩ := hB'b
    obtain ⟨s2, hs2⟩ := hB'b'
    obtain ⟨s4, hs4⟩ := hB'q
    have hprod : (4*a*a') ∣ (B' - b) * (B' - b') := ⟨s1 * s2, by
      rw [show B' - b = -(2*a*s1) from by linarith, show B' - b' = -(2*a'*s2) from by linarith]; ring⟩
    have hdvd4 : (4*a*a') ∣ ((b+b')*B' - (b*b'+D)) := by
      rw [show (b+b')*B' - (b*b'+D) = -(D - B'^2) - (B'-b)*(B'-b') from by ring]
      exact dvd_sub (dvd_neg.mpr ⟨s4, hs4⟩) hprod
    rw [show (b+b')*B' - (b*b'+D) = 2 * -(γ - β*B') from by rw [← hβ, ← hγ]; ring,
        show (4:ℤ)*a*a' = 2*(2*a*a') from by ring] at hdvd4
    exact dvd_neg.mp ((mul_dvd_mul_iff_left (by norm_num : (2:ℤ) ≠ 0)).mp hdvd4)
  have hB'lin : ∀ i, p i * B' ≡ q i [ZMOD m] := by
    intro i
    fin_cases i <;>
      simp only [hp, hq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
    · exact f0
    · exact f1
    · exact f2
  exact (simultaneous_congruence_unique 3 p q m hbez B B' hBlin hB'lin).symm

open Classical in
/-- The integer `B` of Lemma 3.2 for the pair `f, g`: chosen (via `lemma_3_2`) when the
forms share a discriminant and satisfy the coprimality condition, and an arbitrary value
otherwise. Internal to the Dirichlet composition. -/
noncomputable def dirichletB (f g : BinaryQF) : ℤ :=
  if h : ∃ B : ℤ, (B ≡ f.b [ZMOD 2 * f.a]) ∧ (B ≡ g.b [ZMOD 2 * g.a])
      ∧ (B ^ 2 ≡ f.discr [ZMOD 4 * f.a * g.a])
  then h.choose else 0

/-- The **Dirichlet composition** of two forms `f`, `g` of discriminant `D` with
`gcd(a, a', (b+b')/2) = 1`: the form `a a' x² + B x y + ((B²−D)/4 a a') y²`, where
`B` is the integer of Lemma 3.2. (Cox §3, (3.7).) -/
noncomputable def dirichletForm (f g : BinaryQF) : BinaryQF :=
  ⟨f.a * g.a, dirichletB f g, (dirichletB f g ^ 2 - f.discr) / (4 * f.a * g.a)⟩

/-- Under the discriminant/coprimality hypotheses of Lemma 3.2, the chosen `B` satisfies
`B² ≡ D (mod 4 a a')`; hence the `y²`-coefficient `(B²−D)/(4 a a')` is an exact integer. -/
theorem dirichletB_spec (f g : BinaryQF) (D : ℤ) (hf : f.discr = D) (hg : g.discr = D)
    (hcop : Int.gcd (Int.gcd f.a g.a) ((f.b + g.b) / 2) = 1) :
    dirichletB f g ^ 2 ≡ f.discr [ZMOD 4 * f.a * g.a] := by
  have hex : ∃ B : ℤ, (B ≡ f.b [ZMOD 2 * f.a]) ∧ (B ≡ g.b [ZMOD 2 * g.a])
      ∧ (B ^ 2 ≡ f.discr [ZMOD 4 * f.a * g.a]) := by
    obtain ⟨B, hB1, hB2, hB3, _⟩ := lemma_3_2 f.a f.b f.c g.a g.b g.c D hf hg hcop
    exact ⟨B, hB1, hB2, by rw [hf]; exact hB3⟩
  rw [dirichletB, dif_pos hex]
  exact hex.choose_spec.2.2

/-- The discriminant of the Dirichlet composition is `D` (Cox Prop 3.8, the discriminant
calculation). -/
theorem dirichletForm_discr (f g : BinaryQF) (D : ℤ) (hf : f.discr = D) (hg : g.discr = D)
    (hcop : Int.gcd (Int.gcd f.a g.a) ((f.b + g.b) / 2) = 1) :
    (dirichletForm f g).discr = D := by
  have hsp := dirichletB_spec f g D hf hg hcop
  have hdvd : (4 * f.a * g.a) ∣ (dirichletB f g ^ 2 - f.discr) :=
    Int.modEq_iff_dvd.mp hsp.symm
  have key : (4 * f.a * g.a) * ((dirichletB f g ^ 2 - f.discr) / (4 * f.a * g.a))
      = dirichletB f g ^ 2 - f.discr := Int.mul_ediv_cancel' hdvd
  have hdiscr : (dirichletForm f g).discr
      = dirichletB f g ^ 2
        - (4 * f.a * g.a) * ((dirichletB f g ^ 2 - f.discr) / (4 * f.a * g.a)) := by
    simp only [dirichletForm, BinaryQF.discr]; ring
  rw [hdiscr, key]; linarith [hf]

/-- The leading coefficient of the Dirichlet composition is positive when both inputs have
positive leading coefficient (Cox Prop 3.8, positivity). -/
theorem dirichletForm_pos (f g : BinaryQF) (hfa : 0 < f.a) (hga : 0 < g.a) :
    0 < (dirichletForm f g).a := by
  simp only [dirichletForm]; exact mul_pos hfa hga

/-- **Proposition 3.8** (Cox §3). The Dirichlet composition `dirichletForm f g` of
two primitive positive definite forms of discriminant `D` (with the coprimality
hypothesis) is again primitive positive definite of discriminant `D`. -/
theorem prop_3_8 (f g : BinaryQF) (D : ℤ) (hf : f.discr = D) (hg : g.discr = D)
    (hfp : f.Primitive) (hgp : g.Primitive) (hfa : 0 < f.a) (hga : 0 < g.a)
    (hcop : Int.gcd (Int.gcd f.a g.a) ((f.b + g.b) / 2) = 1) :
    (dirichletForm f g).discr = D ∧ (dirichletForm f g).Primitive
      ∧ 0 < (dirichletForm f g).a := by
  refine ⟨dirichletForm_discr f g D hf hg hcop, ?_, dirichletForm_pos f g hfa hga⟩
  -- Primitivity (Cox Prop 3.8): deferred. Cox derives `gcd(aa', B, (B²−D)/4aa') = 1`
  -- from the fact that `dirichletForm f g` is the *direct composition* of `f` and `g`
  -- (3.1): a prime dividing all of its coefficients would divide every value
  -- `f(x,y) · g(z,w)`, contradicting primitivity of `f, g` (Cox Exercise 3.6). This is the
  -- deep Gauss-composition content — the same machinery as `compose`'s well-definedness —
  -- and is deferred to a later wave.
  sorry

/-- **Dirichlet composition** of two classes of forms of discriminant `D`.
(Cox, §3, Thm 3.9.) -/
def compose (D : ℤ) : FormClassGroup D → FormClassGroup D → FormClassGroup D := sorry

/-- The class of the **principal form** of discriminant `D` (the identity of
`C(D)`). Cox's form class group is defined only for discriminants `D ≡ 0,1 (mod 4)`
(Thm 3.9): non-discriminants have no forms, so `FormClassGroup D` is empty and no
identity exists — hence the `D ≡ 0,1 (mod 4)` hypothesis. (Cox, §3.) -/
def principalClass (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) : FormClassGroup D :=
  classOf D (principalForm D)
    ⟨principalForm_discr D hD, principalForm_primitive D, principalForm_pos D⟩

/-- **Theorem 3.9** (Cox §3). For `D < 0`, Dirichlet composition makes `C(D)` a
finite abelian group: it is associative and commutative, the principal class is a
right identity, and every class has an inverse. (Faithful replacement of the
earlier vacuous `Nonempty (CommGroup …)`, which holds for any nonempty type.) -/
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

/-- The number of distinct odd primes dividing `D`. (Cox §3, Prop 3.11.) -/
def oddPrimeDivisorCount (D : ℤ) : ℕ := (D.natAbs.primeFactors.erase 2).card

/-- The exponent `μ` of Cox, Proposition 3.11: the number of *assigned characters*.
If `D ≡ 1 (mod 4)`, `μ = r`; if `D = −4n`, it is determined by `n (mod 8)` as in
Cox's table, where `r` is the number of odd primes dividing `D`. -/
def mu (D : ℤ) : ℕ :=
  let r := oddPrimeDivisorCount D
  if D % 4 = 1 then r
  else
    let n := (-D) / 4
    if n % 4 = 1 ∨ n % 4 = 2 then r + 1
    else if n % 4 = 3 then r
    else if n % 8 = 0 then r + 2 else r + 1

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

/-- The form class group of a negative discriminant is finite. (Cox, §3.) -/
theorem finite (D : ℤ) (hD : D < 0) : Nonempty (Fintype (FormClassGroup D)) := sorry

end PrimesX2NY2.Forms
