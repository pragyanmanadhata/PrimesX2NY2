/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/

-- Part I - From Fermat to Gauss
import PrimesX2NY2.PartI_Forms.Fermat
import PrimesX2NY2.PartI_Forms.Forms
import PrimesX2NY2.PartI_Forms.FormClassGroup
import PrimesX2NY2.PartI_Forms.Genus
import PrimesX2NY2.PartI_Forms.Genera
import PrimesX2NY2.PartI_Forms.CubicReciprocity
import PrimesX2NY2.PartI_Forms.BiquadraticReciprocity
import PrimesX2NY2.PartI_Forms.Exercises.S1
import PrimesX2NY2.PartI_Forms.Exercises.S2
import PrimesX2NY2.PartI_Forms.Exercises.S3
import PrimesX2NY2.PartI_Forms.Exercises.S4

-- Part II - Class Field Theory
import PrimesX2NY2.PartII_ClassFieldTheory.Orders
import PrimesX2NY2.PartII_ClassFieldTheory.Bridge
import PrimesX2NY2.PartII_ClassFieldTheory.RingClassField
import PrimesX2NY2.PartII_ClassFieldTheory.MainTheorem

-- Part III - Complex Multiplication
import PrimesX2NY2.PartIII_ComplexMultiplication.EllipticFunctions
import PrimesX2NY2.PartIII_ComplexMultiplication.ModularFunctions
import PrimesX2NY2.PartIII_ComplexMultiplication.WeberFunctions

/-!
# Primes of the Form `x² + ny²`

A Lean 4 formalization using Mathlib, following David A. Cox,
*Primes of the Form x² + ny²: Fermat, Class Field Theory, and Complex
Multiplication* (2nd ed., Wiley, 2013).

This root module imports every chapter for `lake build` and the blueprint's
`checkdecls`. Part I includes proofs of reduction, Dirichlet composition, and
several representation theorems. Genus theory, higher reciprocity, and Parts II
and III still contain unfinished definitions and `sorry` proofs.

See `blueprint/` for the mathematical outline and dependency graph, and
`ROADMAP.md` for the Mathlib audit.
-/
