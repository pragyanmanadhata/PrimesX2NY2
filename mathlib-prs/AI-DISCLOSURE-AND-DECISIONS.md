<title>Mathlib PR Decision Record</title>

# Mathlib submission: AI disclosure and full decision record

Read this before opening anything. It exists because Mathlib's contribution policy
requires you — not a tool — to understand and defend every decision below.

---

## 1. What the policy actually says

From [Contributing to mathlib](https://leanprover-community.github.io/contribute/index.html),
verbatim:

> "If you use artificial intelligence (such as, by using GitHub's copilot mode, asking an
> LLM like ChatGPT or using an agent like Codex, Claude, Gemini, or even Lean-dedicated
> agents like Aristotle), you must explain this in the PR description. Explain which
> tool(s) you used and how you used it."

> "If your PR contains a substantial amount of LLM-generated code, add the
> `LLM-generated` label by adding the comment `LLM-generated`."

> "It is essential that you understand all the content written by an AI. This includes
> understanding any design decisions made for the formalization and being able to justify
> each decision to reviewers **without the use of an AI**."

> "Using an LLM when writing comments on GitHub or Zulip is not allowed: use your own
> words."

> "Members of the review team will summarily close without comment any low quality PR
> produced using LLMs, especially if the author has made little effort to directly engage
> in the community in a discussion about its merits before opening the PR."

> "If we notice that you open several PRs without putting in this learning effort or
> without adhering to our community ethical standards, we will suspend (or permanently
> ban) you both from opening new PRs and from the Zulip chat."

And the framing sentence that sets the bar:

> "As of mid-2026, code written by an AI without the supervision of a Lean subject expert
> fails to meet that bar by a large margin."

### What that means for you concretely

1. **All four PRs are 100% AI-generated.** Every statement, proof, helper lemma, and
   design choice below was produced by me and by subagents I dispatched. You wrote none
   of it. Disclosure is mandatory, not optional, and the `LLM-generated` label applies to
   all four.
2. **The comprehension requirement is the binding constraint.** Reading this document is
   legitimate preparation — it is how you learn the material. But in review you must
   reproduce the reasoning unaided. If you cannot currently explain, from memory, why
   `mod_right_of_discr` needs `D ≡ 0, 1 (mod 4)`, that PR is not ready for you to submit.
3. **Write the PR description and every Zulip/GitHub comment yourself.** Do not paste my
   prose. The policy names this explicitly.
4. **Engage on Zulip first**, especially for PR3. The policy singles out "little effort to
   directly engage in the community" as grounds for summary closure.
5. **Sequence matters.** Open PR1 or PR4 first — small, checkable, and they establish you
   as someone who engages. PR3 should not be a first contribution.

---

## 2. Provenance: how each proof was actually produced

Reviewers may ask. The honest account:

| Stage | What happened |
|---|---|
| Statement | Taken from the project's pre-existing `sorry`-bodied scaffold, itself written from Cox's book. Not AI-invented, but AI-transcribed. |
| Proof search | I or a subagent wrote a candidate proof, compiled it in an isolated scratch file, read the errors, and iterated — typically 2–6 rounds. |
| Verification | Each result compiles under the pinned Lean v4.31.0 / Mathlib, and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`. |
| Human review | **None.** No mathematician has read these proofs. |

The axiom check rules out a proof that secretly depends on `sorry`. It does **not** rule
out a theorem that is true but badly stated, misnamed, redundant with something already in
Mathlib, or proved in a style Mathlib would reject. Those are exactly what review is for,
and exactly what you must be able to discuss.

---

## 3. PR1 — `ZMod.exists_sq_eq_neg_three_iff`

**Claim.** `-3` is a square mod a prime `p ≠ 2, 3` iff `p ≡ 1 (mod 3)`.
**In-repo:** `PrimesX2NY2.Fermat.neg_three_isSquare_iff`.
**Risk: low.** Smallest and most obviously-missing of the four.

### Decisions

**D1.1 — Fill a gap in an existing family.** Mathlib has `exists_sq_eq_neg_one_iff`,
`exists_sq_eq_two_iff`, `exists_sq_eq_neg_two_iff` and no `-3`. The decision was to match
that family's shape exactly rather than invent a new idiom. *Defend:* `-3` is the
discriminant case governing `ℤ[ω]`, cubic reciprocity, and `p = x²+3y²`; its absence is
conspicuous.

**D1.2 — Two hypotheses `p ≠ 2` and `p ≠ 3`, not `3 < p`.** Both are genuinely necessary
and you should be able to produce the counterexamples on demand:
- `p = 2`: `-3 ≡ 1 = 1²` is a square, but `2 % 3 = 2`. Statement fails.
- `p = 3`: `-3 ≡ 0 = 0²` is a square, but `3 % 3 = 0`. Statement fails.
`3 < p` would also work and is arguably tidier, but two `≠` hypotheses match the
neighbours' style (`exists_sq_eq_two_iff` takes `hp : p ≠ 2`).

**D1.3 — The in-repo version uses `Odd p`; the draft uses `p ≠ 2`.** These are equivalent
given `p` prime. The draft was restated for Mathlib because the neighbours use `p ≠ 2`.
*This is a real edit you must make and understand, not a copy-paste.*

**D1.4 — Cast form: this differs from Mathlib and must be changed.** The project states
`IsSquare ((-3 : ℤ) : ZMod p)` — an integer cast into `ZMod p`, because the surrounding
project code manipulates `ℤ`-valued discriminants. Mathlib's neighbours state
`IsSquare (-2 : ZMod p)` — a numeral directly in `ZMod p`. **Upstream must use the
Mathlib form.** The bridge is `push_cast`, but do not assume it is free; verify.

**D1.5 — Proof route: quadratic reciprocity, not the character route.** Mathlib proves
`-1`, `2`, `-2` via `FiniteField.isSquare_*_iff` plus `card p`, i.e. through
`quadraticChar`. Ours goes through `legendreSym` and
`legendreSym.quadratic_reciprocity'` with `q = 3`, using that `3 / 2 = 1` in `ℕ` so the
two sign factors multiply to `(-1)^(2·(p/2)) = 1`, leaving `(-3/p) = (p/3)`; then `(p/3)`
is decided by `p mod 3` via `decide` over `ZMod 3`.

**Expect a reviewer to push back here.** The consistent thing would be to add
`quadraticChar_neg_three` and `FiniteField.isSquare_neg_three_iff` first, then derive the
`ZMod` statement — matching how the rest of the family is built. If a reviewer asks for
that, it is a rewrite, not a tweak. Decide in advance whether you are willing to do it.

**D1.6 — Placement.** `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`,
in the existing `namespace ZMod`, immediately after `exists_sq_eq_neg_two_iff`.

**D1.7 — Name.** `exists_sq_eq_neg_three_iff`, following the family, even though the
`exists_sq_eq_` prefix is a slight misnomer for an `IsSquare` statement. Consistency beat
correctness here; say so if asked.

---

## 4. PR2 — `jacobiSym.mod_right_of_discr`

**Claim.** For `D ≡ 0, 1 (mod 4)`, `J(D | ·)` has period `|D|` on odd arguments — not
just the `4|D|` Mathlib currently gives.
**In-repo:** `PrimesX2NY2.PartI.S1.mod_right_of_discr`.
**Risk: medium.** Mathematically the most valuable of the four; also the most code.

### Decisions

**D2.1 — Congruence form, not a `%` form.** Stated as
`(h : (m : ℤ) ≡ (n : ℤ) [ZMOD D]) : J(D | m) = J(D | n)` rather than mirroring
`mod_right`'s `J(a | b) = J(a | b % (4 * a.natAbs))`.

*Why, and you must be able to say this unprompted:* for `D ≡ 1 (mod 4)` the modulus
`D.natAbs` is **odd**, so `b % D.natAbs` can be **even**, and the `Odd` hypothesis that
the Jacobi symbol needs fails on the right-hand side. The `%` form is therefore not
merely inconvenient, it is wrong as naively stated. The congruence form sidesteps this and
is what every application actually uses. A reviewer may still want a `%` form for
symmetry with `mod_right`; the honest answer is that it needs a side condition and was
deliberately not attempted.

**D2.2 — The `2`-adic split.** Write `|D| = 2^e · d` with `d` odd
(`Nat.exists_eq_pow_mul_and_not_dvd`), then decompose
`J(D | m) = J(ε | m) · J(2 | m)^e · J(d | m)` by `mul_left` and `pow_left`. The whole
proof is bookkeeping on those three factors.

**D2.3 — `e = 1` is impossible, and this is what makes the proof short.** If `e = 1` then
`D = ±2d` with `d` odd, so `D ≡ 2 (mod 4)`, contradicting the hypothesis. Discharging
this early means the `e ≥ 2` branch is uniform in the sign of `D`, and only `e = 2` vs
`e ≥ 3` needs splitting. **This is the single most important structural insight in the
proof — know it cold.**

**D2.4 — Handle the reciprocity sign via `qrSign`, not `(-1)^(d/2 · m/2)`.** Mathlib's
`qrSign m d = J(χ₄ m | d)` makes the sign visibly a function of `m mod 4`, which is
exactly what the hypothesis controls. Going through the exponent form would require
parity-of-quotient arithmetic that omega does not handle well. This was a deliberate
simplification over the original plan.

**D2.5 — Why the hypothesis is exactly right.** Case table, which you should be able to
reconstruct:
- `D ≡ 1 (mod 4)`, `D > 0`: `e = 0`, `d ≡ 1 (mod 4)`, reciprocity sign trivial.
- `D ≡ 1 (mod 4)`, `D < 0`: `d ≡ 3 (mod 4)`; the `χ₄` factor from `ε = -1` cancels the
  reciprocity sign.
- `D ≡ 0 (mod 4)`, `e = 2`: `J(2|m)² = 1` because `J(2|m) = ±1` for odd `m`; the residual
  `χ₄` factor is pinned by `m ≡ n (mod 4)`, which follows from `4 ∣ D`.
- `D ≡ 0 (mod 4)`, `e ≥ 3`: `8 ∣ D`, so `m ≡ n (mod 8)` pins the `χ₈` factor.

**D2.6 — Degenerate cases.** `D = 0` forces `m = n` and is handled first. Arguments not
coprime to `D` are fine without special treatment: every factor matches, including the
zero case, because `mod_left` holds unconditionally.

**D2.7 — Five private helpers.** `chi4_congr`, `chi8_congr`, `gcd_two_odd`,
`jac_recip_congr`, `case_neg_odd`. **Open question for the reviewer:** `chi4_congr` and
`chi8_congr` (that `χ₄`/`χ₈` on naturals depend only on the argument mod 4 / mod 8) look
generally useful and arguably belong in Mathlib as public lemmas, possibly already exist
under other names. Search before submitting.

**D2.8 — Implicit binders `{D} {m n}`.** Mathlib's `mod_right` takes `(a : ℤ)` explicit.
Ours makes `D` implicit since it is determined by `h`. Minor, but a reviewer may want
consistency with the neighbour.

**D2.9 — `open ZMod` dependency.** The verified file has `open ZMod`, so the helpers read
`χ₄ …`. In `JacobiSymbol.lean` you may need `ZMod.χ₄`. Check, do not assume.

**D2.10 — Purity.** This was developed in a file importing only `Mathlib`, deliberately,
so it lifts without carrying project dependencies. That claim is verified.

---

## 5. PR3 — Binary quadratic forms

**Claim.** Mathlib has no binary quadratic forms in the classical Gauss sense; this is a
definitions + reduction-theory series.
**Risk: high. Do not open this as a PR yet.**

### Why this one is different

The other three are lemmas. This is a proposal to add an *area*, entirely AI-generated,
with no mathematician having read it. That is precisely the shape the policy's "fails to
meet that bar by a large margin" sentence is aimed at. The correct first move is a Zulip
thread in `#mathlib4` describing the design and asking whether it is wanted and in what
form — not code.

### Decisions, and the two that are genuinely unresolved

**D3.1 — Standalone `structure BinaryQF` with fields `a b c : ℤ`.** Not a bundled
`QuadraticForm ℤ (Fin 2 → ℤ)`. *Rationale:* keeps `a, b, c` directly accessible, which is
what makes `omega`, `interval_cases`, and `decide` work in the reduction proofs — those
arguments are the bulk of the development and would be materially harder through a bundled
interface. *Counter-argument a reviewer will raise:* it does not integrate with
`LinearAlgebra.QuadraticForm`, and Mathlib prizes integration. **Unresolved. This is the
first question for Zulip.**

**D3.2 — The action is contravariant, and this is a real problem.** The project proves

```
action_mul : action N (action M f) = action (M * N) f
```

That is a **right** action, not a left action. Mathlib would want a `MulAction` of
`SpecialLinearGroup (Fin 2) ℤ`, which is a left action. Fixing this means either flipping
the convention throughout or acting through `Mᵀ`, and it touches every downstream proof.
**Unresolved, and more disruptive than it looks. Second question for Zulip.**

**D3.3 — `action` takes an arbitrary `Matrix (Fin 2) (Fin 2) ℤ`.** Consequently
`ProperlyEquivalent` carries `M.det = 1` as a side condition rather than using
`Matrix.SpecialLinearGroup`. This was convenient for the proofs but is not how Mathlib
would model a group action.

**D3.4 — `Reduced` includes the boundary condition.**
`|b| ≤ a ∧ a ≤ c ∧ ((|b| = a ∨ a = c) → 0 ≤ b)`. The third clause is exactly what makes
the reduced representative **unique**; without it `exists_unique_reduced` is false. Some
textbooks fold this into a normalization step instead. Know why the clause is there and be
ready to point at the forms it separates — `⟨3,2,3⟩` versus `⟨3,-2,3⟩` is the canonical
example, and it is the case that decides `h(−32) = 2`.

**D3.5 — `PosDef f := 0 < f.a ∧ f.discr < 0`.** A characterization, not the definition
("`f(x,y) > 0` for `(x,y) ≠ 0`"). The equivalence is proved as `eval_pos_of_posDef`. A
reviewer may prefer the honest definition with this as a lemma.

**D3.6 — `Primitive f := Int.gcd (Int.gcd f.a f.b) f.c = 1`.** Nested `Int.gcd`, which
returns `ℕ`, so downstream proofs fight coercions constantly. `IsCoprime`-based or
`Finset.gcd`-based alternatives exist.

**D3.7 — Scope of a first PR.** Definitions + action + equivalence only. Reduction proofs
follow once conventions are settled. Do not propose the whole thing at once.

### Blockers you must clear before this could ever be submitted

- `Forms.lean` still contains `class_number_one` as a `sorry` (Landau's theorem). Mathlib
  does not accept `sorry`. It must be deleted from any upstreamed file.
- **Every file in this project carries a stale module docstring reading "Scaffold only:
  every proof is `sorry`."** That is now false in all 18 files. It would be embarrassing in
  a PR and signals unreviewed automation.
- Naming: `BinaryQF` → `BinaryQuadraticForm` for Mathlib.

---

## 6. PR4 — `prime_of_norm_prime` — **contains an error I need to retract**

**Claim as drafted.** An element of `ℤ[i]` whose norm is a rational prime is prime.
**In-repo:** `PrimesX2NY2.BiquadraticReciprocity.prime_of_norm_prime`.

### The correction

The `mathlib-prs/README.md` I wrote earlier says this proof "generalizes verbatim to any
`ℤ√d` with `d ≤ 0`". **That is wrong, and you would have been caught by a reviewer.**

The proof opens with `rw [← irreducible_iff_prime]`, and in current Mathlib
`irreducible_iff_prime` requires a `[DecompositionMonoid M]` instance. `ℤ[i]` has it, via
`EuclideanDomain → PID → UFD`. A general `ℤ√d` with `d ≤ 0` does **not** — and this
project itself proves a counterexample: `ex_4_6_b` shows `2` is irreducible but not prime
in `ℤ[√−3]`, so `ℤ[√−3]` is not a UFD and `irreducible_iff_prime` fails there outright.

So the correct scope is: **`ℤ[i]`, or any `ℤ√d` that is known to be a UFD.** Whether the
*statement* (as opposed to this proof) still holds in `ℤ[√−3]` is a separate question I
have not settled. Do not repeat the generalization claim. I have corrected the README.

### Decisions

**D4.1 — Hypothesis shape `(hq : q.Prime) (h : Zsqrtd.norm π = (q : ℤ))` with `q : ℕ`.**
The alternative `(h : Prime (Zsqrtd.norm π))` stated in `ℤ` avoids the cast. The `ℕ`
version was chosen because the call sites had `p : ℕ` prime in hand. For Mathlib the
`ℤ`-native form is probably better; be ready to switch.

**D4.2 — Proof structure.** Not-a-unit comes from `Zsqrtd.norm_eq_one_iff'` (norm `q ≠ 1`);
the factorization case uses multiplicativity of the norm plus
`Nat.Prime.eq_one_or_self_of_dvd` to force one factor to have norm 1.

**D4.3 — Placement.** `Mathlib/NumberTheory/Zsqrtd/Basic.lean` beside `norm_eq_one_iff'`
**only if** the UFD hypothesis is made explicit; otherwise
`Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean` where the instance is available.

**Honest assessment:** at six lines, a reviewer may reasonably say "inline it at the use
site." Its value is that it is genuinely reusable and the gap next to
`norm_eq_one_iff'` is real. That is a defensible position, but it is a conversation, not a
slam dunk.

---

## 7. Pre-submission checklist

Before any PR:

- [ ] I can state the theorem and sketch its proof from memory, with no AI open.
- [ ] I can produce the counterexamples that force each hypothesis.
- [ ] I have searched Mathlib for the lemma under other names.
- [ ] The PR description is **written by me**, discloses AI use, and names the tools.
- [ ] I have commented `LLM-generated` to apply the label.
- [ ] Every Zulip and GitHub comment is in my own words.
- [ ] No `sorry` anywhere in the touched files; no stale "Scaffold only" docstrings.
- [ ] Statement restated in Mathlib's idiom (D1.4's cast form; D4.1's hypothesis form).

Order: **PR1 or PR4 first** (small, self-contained, low risk). **PR2 second** (valuable,
more code, more review surface). **PR3 only after a Zulip design thread**, and only if the
community wants it.

If you cannot honestly tick the first two boxes for a given PR, that PR is not ready —
which is a statement about preparation time, not about whether the mathematics is correct.
The mathematics compiles and is axiom-clean. The policy's bar is about *your* command of
it, and that bar is deliberately set where automation cannot reach.
