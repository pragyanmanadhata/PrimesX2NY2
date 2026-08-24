/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.CubicReciprocity
import PrimesX2NY2.PartI_Forms.BiquadraticReciprocity

/-!
# Part I, §4 - Exercises (Cox, *Primes of the Form x² + ny²*, §4.D)

Faithful statements for the concrete, self-contained parts of Exercises 4.1-4.29.
Sub-parts that *prove* a spine result, complete a proof, or require machinery not
yet built (Gaussian periods/sums, the quotient residue fields, the full character
constructions) are recorded as `\notready` blueprint nodes only - see ROADMAP.

Exercise 4.6 (that `ℤ[√−3]` is neither a PID nor a UFD) is formalized over
Mathlib's `Zsqrtd (-3)` - precisely the ring we must *not* use for `ℤ[ω]`.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.PartI.S4

open PrimesX2NY2.CubicReciprocity PrimesX2NY2.BiquadraticReciprocity

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

/-- Norm on `ℤ[√-3]` in the convenient form `a² + 3b²`. -/
lemma norm_val (a b : ℤ) : (⟨a, b⟩ : Zsqrtd (-3)).norm = a * a + 3 * (b * b) := by
  rw [Zsqrtd.norm_def]; ring

/-- No element of `ℤ[√-3]` has norm 2. -/
lemma no_norm_two (z : Zsqrtd (-3)) : z.norm ≠ 2 := by
  obtain ⟨a, b⟩ := z
  rw [norm_val]
  intro h
  have hb2 : 0 ≤ b * b := mul_self_nonneg b
  have ha2 : 0 ≤ a * a := mul_self_nonneg a
  have hb : b * b = 0 := by nlinarith
  have ha : a * a = 2 := by rw [hb] at h; linarith
  have h1 : a ≤ 2 := by nlinarith
  have h2 : -2 ≤ a := by nlinarith
  interval_cases a <;> omega

/-- `2` divides an element of `ℤ[√-3]` iff it divides both coordinates. -/
lemma two_dvd_iff (z : Zsqrtd (-3)) :
    (2 : Zsqrtd (-3)) ∣ z ↔ 2 ∣ z.re ∧ 2 ∣ z.im := by
  have h2 : (2 : Zsqrtd (-3)) = ((2 : ℤ) : Zsqrtd (-3)) := by norm_cast
  rw [h2, Zsqrtd.intCast_dvd]

lemma norm_two : (2 : Zsqrtd (-3)).norm = 4 := by decide

/-- **Exercise 4.6(b).** `2` is irreducible but not prime in `ℤ[√−3]` (so `ℤ[√−3]`
is not a UFD). -/
theorem ex_4_6_b : Irreducible (2 : Zsqrtd (-3)) ∧ ¬ Prime (2 : Zsqrtd (-3)) := by
  have hd : (-3 : ℤ) ≤ 0 := by norm_num
  constructor
  · constructor
    · intro hu
      have h1 := (Zsqrtd.norm_eq_one_iff' hd 2).mpr hu
      rw [norm_two] at h1
      norm_num at h1
    · intro a b hab
      by_contra hcon
      obtain ⟨ha, hb⟩ := not_or.mp hcon
      have hmul : a.norm * b.norm = 4 := by
        rw [← Zsqrtd.norm_mul, ← hab, norm_two]
      have hna1 : a.norm ≠ 1 := fun h => ha ((Zsqrtd.norm_eq_one_iff' hd a).mp h)
      have hnb1 : b.norm ≠ 1 := fun h => hb ((Zsqrtd.norm_eq_one_iff' hd b).mp h)
      have hna0 : 0 ≤ a.norm := Zsqrtd.norm_nonneg hd a
      have hnb0 : 0 ≤ b.norm := Zsqrtd.norm_nonneg hd b
      have hane : a.norm ≠ 0 := by
        intro h; rw [h, zero_mul] at hmul; norm_num at hmul
      have hbne : b.norm ≠ 0 := by
        intro h; rw [h, mul_zero] at hmul; norm_num at hmul
      have hna2 := no_norm_two a
      have hnb2 := no_norm_two b
      have ha3 : 3 ≤ a.norm := by omega
      have hb3 : 3 ≤ b.norm := by omega
      nlinarith
  · intro hp
    have hdvd : (2 : Zsqrtd (-3)) ∣ (⟨1, 1⟩ : Zsqrtd (-3)) * (⟨1, -1⟩ : Zsqrtd (-3)) := by
      refine ⟨2, ?_⟩
      decide
    rcases hp.2.2 _ _ hdvd with h | h
    · obtain ⟨h1, -⟩ := (two_dvd_iff _).mp h
      exact absurd h1 (by decide)
    · obtain ⟨h1, -⟩ := (two_dvd_iff _).mp h
      exact absurd h1 (by decide)

/-- **Exercise 4.6(c).** The ideal `(2, 1 + √−3)` of `ℤ[√−3]` is not principal (so
`ℤ[√−3]` is not a PID). -/
theorem ex_4_6_c :
    ¬ (Ideal.span {(2 : Zsqrtd (-3)), (⟨1, 1⟩ : Zsqrtd (-3))}).IsPrincipal := by
  intro hprin
  haveI := hprin
  set I : Ideal (Zsqrtd (-3)) :=
    Ideal.span {(2 : Zsqrtd (-3)), (⟨1, 1⟩ : Zsqrtd (-3))} with hI
  set d : Zsqrtd (-3) := Submodule.IsPrincipal.generator I with hdgen
  -- every element of the ideal has coordinates of equal parity
  have hpar : ∀ x : Zsqrtd (-3), x ∈ I → 2 ∣ (x.re + x.im) := by
    intro x hx
    rw [hI, Ideal.mem_span_pair] at hx
    obtain ⟨u, v, huv⟩ := hx
    rw [Zsqrtd.ext_iff] at huv
    obtain ⟨hre, him⟩ := huv
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_mul, Zsqrtd.im_mul,
      Zsqrtd.re_ofNat, Zsqrtd.im_ofNat] at hre him
    omega
  -- the generator divides both generators of the ideal
  have hd2 : d ∣ 2 :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span (Set.mem_insert _ _))
  have hd11 : d ∣ (⟨1, 1⟩ : Zsqrtd (-3)) :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  -- the generator's coordinates have equal parity, so 4 ∣ norm d
  have hdpar : 2 ∣ (d.re + d.im) := hpar d (Submodule.IsPrincipal.generator_mem I)
  have h4dvd : (4 : ℤ) ∣ d.norm := by
    obtain ⟨k, hk⟩ := hdpar
    refine ⟨k * k - k * d.im + d.im * d.im, ?_⟩
    have hre : d.re = 2 * k - d.im := by omega
    rw [Zsqrtd.norm_def, hre]; ring
  -- norm d divides norm 2 = 4
  obtain ⟨c, hc⟩ := hd2
  have hprod : d.norm * c.norm = 4 := by
    rw [← Zsqrtd.norm_mul, ← hc]
    decide
  have hdvd4 : d.norm ∣ 4 := ⟨c.norm, hprod.symm⟩
  -- hence norm d = 4 and c is a unit
  have hnd4 : d.norm = 4 :=
    Int.dvd_antisymm (Zsqrtd.norm_nonneg (by norm_num) d) (by norm_num) hdvd4 h4dvd
  have hnc1 : c.norm = 1 := by
    rw [hnd4] at hprod; omega
  have hcu : IsUnit c := (Zsqrtd.norm_eq_one_iff' (by norm_num) c).mp hnc1
  -- so d is an associate of 2, whence 2 ∣ ⟨1,1⟩, absurd
  obtain ⟨cu, rfl⟩ := hcu
  have hd2' : (2 : Zsqrtd (-3)) ∣ d := by
    refine ⟨(↑cu⁻¹ : Zsqrtd (-3)), ?_⟩
    rw [hc, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨h1, -⟩ := (two_dvd_iff _).mp (hd2'.trans hd11)
  exact absurd h1 (by decide)

/-- **Exercise 4.9(a).** For a prime `π` not associate to `1 − ω`, `3 ∣ N(π) − 1`. -/
theorem ex_4_9_a (π : EisensteinInt) (hπ : EisensteinInt.IsPrimeE π)
    (h : ¬ EisensteinInt.AssociatedE π (1 - EisensteinInt.omega)) :
    (3 : ℤ) ∣ (EisensteinInt.norm π - 1) := by
  open EisensteinInt in
  obtain ⟨hnu, hne, hprime⟩ := hπ
  have hnπ : norm π ≠ 0 := norm_ne_zero π hne
  have h3 : ¬ ((3 : ℤ) ∣ norm π) := by
    intro hdvd
    rw [norm_def] at hdvd
    obtain ⟨w, hw⟩ := (norm_zmod3 π.a π.b).mp hdvd
    have hdvd' : (1 - omega) ∣ π := by
      refine ⟨⟨π.a - w, w⟩, ?_⟩
      rw [mul_def]
      have e1 : (1 - omega : EisensteinInt).a = 1 := rfl
      have e2 : (1 - omega : EisensteinInt).b = -1 := rfl
      rw [e1, e2]
      obtain ⟨pa, pb⟩ := π
      simp only [] at hw ⊢
      simp only [EisensteinInt.mk.injEq]
      constructor <;> omega
    obtain ⟨γ, hγ⟩ := hdvd'
    have hpd : π ∣ (1 - omega) * γ := ⟨1, by rw [← hγ]; exact (mul_one' π).symm⟩
    have hnn := norm_nonneg π
    rcases hprime _ _ hpd with hc | hc
    · obtain ⟨u, hu⟩ := hc
      have hnorms : (3 : ℤ) = norm π * norm u := by
        rw [← norm_one_sub_omega, hu, EisensteinInt.norm_mul]
      have hπ1 : norm π ≠ 1 := fun hh => hnu ((lemma_4_5_i π).mpr hh)
      have hdvd3 : norm π ∣ (3:ℤ) := ⟨norm u, hnorms⟩
      have hle : norm π ≤ 3 := Int.le_of_dvd (by norm_num) hdvd3
      have hcases : norm π = 0 ∨ norm π = 1 ∨ norm π = 2 ∨ norm π = 3 := by omega
      have hnu' : norm u = 1 := by
        rcases hcases with h0 | h1 | h2 | h3'
        · exact absurd h0 hnπ
        · exact absurd h1 hπ1
        · rw [h2] at hnorms; omega
        · rw [h3'] at hnorms; omega
      exact h ⟨u, (lemma_4_5_i u).mpr hnu', hu.trans (mul_comm' π u)⟩
    · obtain ⟨w2, hw2⟩ := hc
      have he : norm π = 3 * (norm π * norm w2) := by
        conv_lhs => rw [hγ]
        rw [EisensteinInt.norm_mul, norm_one_sub_omega, hw2, EisensteinInt.norm_mul]
      have hz : norm π * (1 - 3 * norm w2) = 0 := by linear_combination he
      rcases mul_eq_zero.mp hz with h' | h'
      · exact hnπ h'
      · have := norm_nonneg w2
        omega
  rw [norm_def] at h3 ⊢
  exact norm_mod3_cases π.a π.b h3

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
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne (a : ZMod p) 0 with ha | ha
  · exact ⟨0, by simp [ha]⟩
  · have hcop : (Nat.card (ZMod p)ˣ).Coprime 3 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units]
      have h3 : ¬ (3 ∣ (p - 1)) := by
        have h2le := hp.two_le
        omega
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3)
    obtain ⟨u, hu⟩ := isUnit_iff_ne_zero.mpr ha
    obtain ⟨v, hv⟩ := hcop.pow_left_bijective.surjective u
    have hv' : v ^ 3 = u := hv
    exact ⟨(v : ZMod p), by rw [← Units.val_pow_eq_pow_val, hv', hu]⟩

/-- **Exercise 4.15(d).** `4p = x² + 243y²` iff `p ≡ 1 (mod 3)` and `3` is a cubic
residue mod `p` (Euler). **Deep / GAP** - `notready`. -/
theorem ex_4_15_d (p : ℕ) (hp : p.Prime) :
    (∃ x y : ℤ, 4 * (p : ℤ) = x ^ 2 + 243 * y ^ 2)
      ↔ (p % 3 = 1 ∧ EisensteinInt.IsCubicResidue 3 p) := by
  sorry

/-- **Exercise 4.17.** For a prime `π` of `ℤ[i]` not associate to `1 + i`,
`4 ∣ N(π) − 1`. -/
theorem ex_4_17 (π : GaussianInt) (hπ : Prime π) (h : ¬ Associated π ⟨1, 1⟩) :
    (4 : ℤ) ∣ (Zsqrtd.norm π - 1) := by
  have hnorm : Zsqrtd.norm π = π.re * π.re + π.im * π.im := by
    rw [Zsqrtd.norm_def]; ring
  have hkey : ¬ ((2 : ℤ) ∣ (π.re + π.im)) := by
    rintro ⟨k, hk⟩
    have hd : (⟨1, 1⟩ : GaussianInt) ∣ π := by
      refine ⟨⟨k, π.im - k⟩, ?_⟩
      ext
      · simp only [Zsqrtd.re_mul]
        omega
      · simp only [Zsqrtd.im_mul]
        omega
    obtain ⟨c, hc⟩ := hd
    rcases hπ.irreducible.isUnit_or_isUnit hc with h1 | h1
    · have h2 := (Zsqrtd.norm_eq_one_iff' (by norm_num) (⟨1, 1⟩ : GaussianInt)).mpr h1
      rw [Zsqrtd.norm_def] at h2
      norm_num at h2
    · exact h (by rw [hc]; exact associated_mul_unit_left _ _ h1)
  rcases Int.even_or_odd π.re with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    rcases Int.even_or_odd π.im with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact absurd ⟨k + m, by omega⟩ hkey
  · exact ⟨k * k + m * m + m, by rw [hnorm, hk, hm]; ring⟩
  · exact ⟨k * k + k + m * m, by rw [hnorm, hk, hm]; ring⟩
  · exact absurd ⟨k + m + 1, by omega⟩ hkey

/-- **Exercise 4.18(b).** The quartic character is multiplicative. -/
theorem ex_4_18_b (π α β : GaussianInt) :
    quarticChar π (α * β) = quarticChar π α * quarticChar π β := by
  sorry

/-- **Exercise 4.24(b).** `2(a² + b²) = (a + b)² + (a − b)²` (the step `2p = (a+b)²
+ (a−b)²` in Dirichlet's proof). -/
theorem ex_4_24_b (a b : ℤ) :
    2 * (a ^ 2 + b ^ 2) = (a + b) ^ 2 + (a - b) ^ 2 := by
  ring

end PrimesX2NY2.PartI.S4
