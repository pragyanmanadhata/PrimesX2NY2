# Conventions

This project follows Mathlib conventions. Summary of what that means here.

## Naming

- **Declarations** use Mathlib naming: `lowerCamelCase` for `def`s producing data
  and for functions, `UpperCamelCase` for types/structures/classes and for
  `Prop`-valued predicates (e.g. `Reduced`, `ProperlyEquivalent`, `PosDef`,
  `IsModularFunction`, `IsCMPoint`).
- **Theorem names** describe the statement in words, in `snake_case` built from
  the camelCased pieces, e.g. `prime_sq_add_sq`, `exists_unique_reduced`,
  `properlyRepresents_iff_isSquare`, `isIntegral_jFunction_of_cm`.
- **Namespaces** mirror the mathematical object, not the file. The base objects
  live in chapter namespaces: `PrimesX2NY2.Fermat`, `PrimesX2NY2.Forms`,
  `PrimesX2NY2.Genus`, `PrimesX2NY2.Order`, `PrimesX2NY2.Bridge`,
  `PrimesX2NY2.RingClassField`, `PrimesX2NY2.MainTheorem`, `PrimesX2NY2.Elliptic`,
  `PrimesX2NY2.Modular`, `PrimesX2NY2.Weber`. A structure `Foo` is declared in its
  chapter namespace and its API lives in the nested `Foo.` namespace (so e.g.
  `PrimesX2NY2.Forms.BinaryQF` and `PrimesX2NY2.Forms.BinaryQF.discr`). We avoid
  doubled names such as `Forms.Forms`.

## Layout

- One Mathlib-style **copyright header** at the top of every file, then `import`s,
  then a `/-! ... -/` **module docstring**, then the content.
- Every public declaration carries a **docstring** (`/-- ... -/`), usually citing
  the corresponding Cox section/theorem number.
- **100-column** limit on source lines (Mathlib's `linter.style.longLine`).
- Unicode math is fine (it is enabled via `unicode-math` in the blueprint and is
  standard in Mathlib).

## `sorry` policy (current phase)

- This repository is a **scaffold**. Every proof body and every "deep" definition
  body is `sorry`. `lake build` succeeds; `sorry` produces warnings, not errors.
- We deliberately do **not** set `warningAsError`, so the project builds while the
  `sorry`s remain. Do not remove a `sorry` without supplying a real proof.
- Statements are meant to be *mathematically faithful* even while unproved: we
  avoid stating anything literally false (e.g. the provisional `℘'` is a named
  `sorry` def rather than a free variable in the differential equation).
- As proofs are filled in, **narrow the imports**: files currently `import Mathlib`
  for convenience; replace with the specific modules actually used.

## Blueprint discipline

- Each blueprint node carries `\label`, `\lean{<fully-qualified Lean name>}`,
  `\uses{...}` for its DAG dependencies, and `\leanok` on the statement
  (its Lean *signature* typechecks).
- `\leanok` is **never** placed inside a `\begin{proof}`: no proof is done yet.
- `leanblueprint checkdecls` must pass, i.e. every `\lean{...}` name must resolve
  in the built Lean environment. Keep the LaTeX `\lean{...}` and the Lean
  declaration names in sync.

## Versions

Pinned; see `README.md`. Do not float onto `nightly` or Mathlib `main`.
