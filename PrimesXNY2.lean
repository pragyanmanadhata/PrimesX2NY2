/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/

-- Part I — From Fermat to Gauss
import PrimesXNY2.PartI_Forms.Fermat
import PrimesXNY2.PartI_Forms.Forms
import PrimesXNY2.PartI_Forms.FormClassGroup
import PrimesXNY2.PartI_Forms.Genus

-- Part II — Class Field Theory
import PrimesXNY2.PartII_ClassFieldTheory.Orders
import PrimesXNY2.PartII_ClassFieldTheory.Bridge
import PrimesXNY2.PartII_ClassFieldTheory.RingClassField
import PrimesXNY2.PartII_ClassFieldTheory.MainTheorem

-- Part III — Complex Multiplication
import PrimesXNY2.PartIII_ComplexMultiplication.EllipticFunctions
import PrimesXNY2.PartIII_ComplexMultiplication.ModularFunctions
import PrimesXNY2.PartIII_ComplexMultiplication.WeberFunctions

/-!
# Primes of the Form `x² + ny²`

A Lean 4 + Mathlib formalization project following David A. Cox,
*Primes of the Form x² + ny²: Fermat, Class Field Theory, and Complex
Multiplication* (2nd ed., Wiley, 2013).

This root module imports every chapter so that `lake build` and the blueprint's
`checkdecls` see all declarations. The project is currently a **scaffold**: every
statement is present with a Mathlib-style signature and a `sorry` body.

See `blueprint/` for the LaTeX blueprint encoding the dependency DAG, and
`ROADMAP.md` for the Mathlib audit.
-/
