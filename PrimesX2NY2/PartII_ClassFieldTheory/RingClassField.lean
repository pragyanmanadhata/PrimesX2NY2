/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartII_ClassFieldTheory.Orders

/-!
# Part II, Chapter 7 - Class fields, Artin reciprocity, Čebotarev

Cox, *Primes of the Form x² + ny²*, §5, §8.

The Hilbert class field, the ring class field of an order, Artin reciprocity, and
the Čebotarev density theorem. These require class field theory beyond the
current project and its pinned Mathlib dependency; see `ROADMAP.md`.

All definitions and proofs below use `sorry`. The carriers and statements are
provisional; in particular, the full splitting criterion is not yet expressed.
-/

namespace PrimesX2NY2.RingClassField

open PrimesX2NY2.Order

/-- Placeholder for the Hilbert class field `H` of an imaginary quadratic field
`K`, its maximal unramified abelian extension. (Cox, §5.) -/
def hilbertClassField (O : QuadOrder) : Type := sorry

/-- Placeholder for the ring class field of the order `𝒪` of conductor `f`: the
abelian extension `L/K` whose Galois group is `C(𝒪)` via the Artin map. (Cox, §9.) -/
def ringClassField (O : QuadOrder) : Type := sorry

/-- Placeholder for `Gal(L/K)`, the Galois group of the ring class field over
`K`. (Cox, §8.) -/
def galoisGroup (O : QuadOrder) : Type := sorry

/-- Artin reciprocity for the ring class field (Cox, §8, Thm 8.2). The intended
isomorphism is induced by the Artin map; this unfinished statement records only
an equivalence between the provisional carriers. -/
theorem artinReciprocity (O : QuadOrder) :
    Nonempty (O.idealClassGroup ≃ galoisGroup O) := sorry

/-- Placeholder for complete splitting of `p` in the ring class field of `𝒪`
(unramified, with trivial Frobenius). (Cox, §5, §8.) -/
def SplitsCompletely (O : QuadOrder) (p : ℕ) : Prop := sorry

/-- Infinitude of primes that split completely in the ring class field, as a
consequence of the Čebotarev density theorem (Cox, §8). This unfinished statement
does not include the density calculation. -/
theorem chebotarev_splitting (O : QuadOrder) :
    {p : ℕ | p.Prime ∧ SplitsCompletely O p}.Infinite := sorry

/-- Placeholder for Cox's splitting criterion (§8): a prime splits completely
in `L` iff it splits completely in `K` and its prime divisors are principal.
The current right-hand side only asserts a carrier equivalence and does not
depend on `p`; it still needs to be replaced by the splitting conditions. -/
theorem splitsCompletely_iff (O : QuadOrder) (p : ℕ) (hp : p.Prime) :
    SplitsCompletely O p ↔ Nonempty (O.idealClassGroup ≃ galoisGroup O) := sorry

end PrimesX2NY2.RingClassField
