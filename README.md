# Primes of the Form `x² + ny²`

A Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4) formalization
project following **David A. Cox, _Primes of the Form x² + ny²: Fermat, Class Field
Theory, and Complex Multiplication_ (2nd ed., Wiley, 2013)**, organised as a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint).

> **Status: scaffold.** Every statement is present with a Mathlib-style signature
> and a `sorry` body. `lake build` and `leanblueprint all` both succeed. No proofs
> have been attempted yet. See [ROADMAP.md](ROADMAP.md) for the Mathlib audit and
> [CONVENTIONS.md](CONVENTIONS.md) for style.

## Pinned versions

These are pinned and should **not** float onto `nightly` / Mathlib `main`.

| Component | Version |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.31.0` (see [lean-toolchain](lean-toolchain)) |
| Mathlib | tag **`v4.31.0`**, commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Lake | `5.0.0` (ships with the toolchain) |
| leanblueprint | `0.0.20` (plasTeX `3.1`) |

The exact dependency graph is locked in [lake-manifest.json](lake-manifest.json).

## Repository layout

```
PrimesXNY2/                         Lean source (one directory per Part)
  PartI_Forms/                      Fermat, binary forms, form class group, genus
    Fermat.lean  Forms.lean  FormClassGroup.lean  Genus.lean
  PartII_ClassFieldTheory/          orders, the bridge, class fields, main theorem
    Orders.lean  Bridge.lean  RingClassField.lean  MainTheorem.lean
  PartIII_ComplexMultiplication/    elliptic functions, modular functions, Weber
    EllipticFunctions.lean  ModularFunctions.lean  WeberFunctions.lean
PrimesXNY2.lean                     root module: imports every chapter
blueprint/src/                      LaTeX blueprint (one chapter per Part)
  content.tex                       the dependency DAG (nodes carry \lean, \uses, \leanok)
CONVENTIONS.md  README.md  ROADMAP.md
.github/workflows/                  CI: build + blueprint + GitHub Pages
```

## Building the Lean project

Requires [`elan`](https://github.com/leanprover/elan) (it will fetch the pinned
toolchain automatically).

```sh
lake exe cache get      # download prebuilt Mathlib oleans (no full rebuild)
lake build              # builds the scaffold; `sorry` warnings are expected
```

## Building the blueprint

Requires Python ≥ 3.10, [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint),
`graphviz` (for the dependency graph), and a LaTeX engine with `xelatex`
(e.g. [TinyTeX](https://yihui.org/tinytex/) or TeX Live).

```sh
pip install leanblueprint
leanblueprint pdf        # blueprint/print/print.pdf   (xelatex via latexmk)
leanblueprint web        # blueprint/web/index.html    (plasTeX; writes blueprint/lean_decls)
leanblueprint checkdecls # checks every \lean{...} name exists in the built Lean
leanblueprint all        # all of the above + `lake build`
leanblueprint serve      # local preview (incl. the dependency graph)
```

The dependency graph and the green/blue status colours are generated from the
`\lean`/`\uses`/`\leanok` annotations in `blueprint/src/content.tex`.

## Continuous integration

`.github/workflows/blueprint.yml` builds the project, compiles the blueprint
(PDF + web), and deploys the blueprint to **GitHub Pages**. To enable it: under
the repository **Settings → Pages**, set **Source** to **GitHub Actions** (and
under **Settings → Actions → General**, allow Actions to create/approve PRs).

> Before first use, replace the placeholder `USERNAME` (GitHub user) in
> `blueprint/src/web.tex` and in the links here. The Pages site will then be served
> at `https://<USERNAME>.github.io/PrimesXNY2/`.

## License

Apache-2.0 (matching Mathlib); see [LICENSE](LICENSE).
