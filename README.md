# Primes of the Form `x² + ny²`

A Lean 4 formalization of David A. Cox’s *Primes of the Form x² + ny²:
Fermat, Class Field Theory, and Complex Multiplication* (2nd ed., Wiley, 2013),
built on [Mathlib](https://github.com/leanprover-community/mathlib4).
The accompanying [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
follows the book and records dependencies between the results.

Part I includes proofs of the first prime representation theorems, Gauss
reduction, Dirichlet composition, and many exercises. Genus theory and the cubic
and biquadratic reciprocity laws remain incomplete. Parts II and III contain
provisional definitions and statements for class field theory and complex
multiplication.

See [ROADMAP.md](ROADMAP.md) for completed work, remaining gaps, and the Mathlib
audit. Some unproved statements also need corrections to their hypotheses;
these are noted in the source. A successful build does not mean every result
has been proved.

## Building the project

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

Elan selects the pinned Lean toolchain. The first command downloads Mathlib’s
compiled files; the second builds the project. Warnings about the remaining
`sorry` terms are expected.

## Building the blueprint

The blueprint needs Python 3.10 or later, leanblueprint, Graphviz, and a LaTeX
installation providing `xelatex` and `latexmk`, such as
[TinyTeX](https://yihui.org/tinytex/) or TeX Live.

```sh
pip install leanblueprint==0.0.20 plasTeX==3.1
leanblueprint pdf
leanblueprint web
leanblueprint checkdecls
```

The PDF is written to `blueprint/print/print.pdf`, and the website to
`blueprint/web/index.html`. Run `leanblueprint serve` for a local preview, or
`leanblueprint all` to build both versions and the Lean project.

In `blueprint/src/content.tex`, `\lean` links a statement to its Lean declaration
and `\uses` records its dependencies. Statement and proof completion are marked
separately with `\leanok`; `\notready` marks work that still needs attention.

## Project layout

| Path | Contents |
| --- | --- |
| `PrimesX2NY2/PartI_Forms/` | Prime representations, quadratic forms, composition, genera, cubic and biquadratic reciprocity |
| `PrimesX2NY2/PartI_Forms/Exercises/` | Exercises from §§1–4 |
| `PrimesX2NY2/PartII_ClassFieldTheory/` | Quadratic orders, ideal classes, class fields, and the main representation theorem |
| `PrimesX2NY2/PartIII_ComplexMultiplication/` | Elliptic, modular, and Weber functions |
| `PrimesX2NY2.lean` | Root module importing every chapter |
| `blueprint/src/` | LaTeX exposition and dependency graph |
| `mathlib-prs/` | Notes and drafts for possible Mathlib contributions |

[CONVENTIONS.md](CONVENTIONS.md) covers naming, source layout, and proof status.

## Versions

Keep Lean and Mathlib at the pinned versions rather than switching to `nightly`
or Mathlib’s `main` branch.

| Component | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.31.0` |
| Mathlib | `v4.31.0`, commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Lake | `5.0.0`, included with Lean |
| leanblueprint | `0.0.20`, with plasTeX `3.1` |

The Lean version is set in [lean-toolchain](lean-toolchain); the full dependency
list is locked in [lake-manifest.json](lake-manifest.json).

## Continuous integration

[The GitHub Actions workflow](.github/workflows/blueprint.yml) builds Lean,
compiles the PDF and web blueprint, and deploys the website to GitHub Pages.
The repository’s Pages source must be set to **GitHub Actions** for deployment.

## License

[Apache-2.0](LICENSE), matching Mathlib.
