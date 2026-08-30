# Conventions

The project follows Mathlib’s naming and source conventions.

## Naming

Use `lowerCamelCase` for data definitions and functions, and `UpperCamelCase`
for types, structures, classes, and predicates such as `Reduced`,
`ProperlyEquivalent`, `PosDef`, `IsModularFunction`, and `IsCMPoint`.
Theorem names use `snake_case`, retaining camel case within the names they
refer to: `prime_sq_add_sq`, `exists_unique_reduced`,
`properlyRepresents_iff_isSquare`, and `isIntegral_jFunction_of_cm`.

Namespaces follow the mathematical objects. The chapter namespaces include
`PrimesX2NY2.Fermat`, `Forms`, `Genus`, `Genera`, `CubicReciprocity`,
`BiquadraticReciprocity`, `Order`, `Bridge`, `RingClassField`, `MainTheorem`,
`Elliptic`, `Modular`, and `Weber`. A structure’s API lives beneath its name:
for example, `PrimesX2NY2.Forms.BinaryQF.discr`. Avoid doubled names such as
`Forms.Forms`.

## Source layout

Start each Lean file with the Mathlib-style copyright header, followed by
imports and a module docstring. Public declarations should have docstrings
that explain the statement and cite the relevant Cox section or theorem when
applicable. Comments should explain a mathematical choice or a non-obvious
proof step, rather than repeat the code.

Keep source lines within 100 columns, as required by
`linter.style.longLine`. Unicode mathematical notation is welcome in both Lean
and the blueprint. As files become self-contained, replace broad
`import Mathlib` declarations with the modules they use.

## Unfinished proofs and definitions

Unfinished proofs and definitions use `sorry`. Replace each one with a real
proof or construction; do not hide a gap behind an axiom or a weaker statement.
Keep known problems with statement hypotheses documented until they are fixed.
The intended mathematics must remain clear even where its formalization is
incomplete.

The build allows warnings while these gaps remain, so `warningAsError` is not
set. Typechecking a statement is distinct from proving it. A proof can also
inherit an unfinished dependency: use `#print axioms` to check for `sorryAx`
before describing a result as complete.

## Blueprint annotations

Give each node a `\label`, a `\lean{...}` reference when it has a Lean
declaration, and `\uses{...}` entries for its dependencies. Use fully qualified
Lean names and keep them in sync with the source.

A statement’s `\leanok` records that its Lean signature typechecks. A
`\leanok` inside a proof records a completed formal proof; add it only after
checking the proof and its dependencies. Keep `\notready` on nodes whose
formalization is still pending, and explain any missing hypotheses or machinery
in the surrounding text.

Run `leanblueprint checkdecls` after changing declaration links. Every
`\lean{...}` reference must resolve in the built Lean environment.

## Versions

Use the versions pinned in [README.md](README.md), `lean-toolchain`, and
`lake-manifest.json`. Do not switch to `nightly` or Mathlib’s `main` branch.
