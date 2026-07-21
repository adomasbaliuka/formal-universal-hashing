# Project conventions

Formalization of universal hash families in Lean 4 (Mathlib). Everything under
`UniversalHashing/` is a Lean **module** (explicit-export mode).

## Build and test

```
lake build              # library + Tests + Examples (the default targets)
lake build toeplitzBench # the benchmark exe; CI builds this as a separate step
lake test               # runs the #guard suites in Tests/
lake exe toeplitzBench [core|ntt|schoolbook]   # timings, never run in CI
```

`toeplitzBench` is deliberately **not** a default target: the docs job requests the
`:docs` facet of every default target, and Lake provides that facet only for
`lean_lib`, so an executable there fails the docs build.

CI (`lean-action`) runs `lake build` and `lake test`. Every `.lean` file in the repo is
compiled by `lake build` **except** `UniversalHashing/BinConvolution/ConvolutionChallenge.lean`
(see below). Keep it that way: if you add a file, make sure some target reaches it.

## Do not "fix" these

**`ConvolutionChallenge.lean` is `sorry`'d on purpose.** It is the comparator baseline
(`circular_convolution_gf2_correct`) that the AI-written `ConvolutionSolution.lean` is
checked against, and it is deliberately excluded from the root import so its `sorry`
does not warn on every build. Its header says "Do not change!".

**`NextPow2Lemmas.lean`'s header is load-bearing** — `module` + `import all` +
`public import` + `public lemma` are coupled, and the file must keep `import all` to
reach `Nat.nextPowerOfTwo.go`. Do not rewrite it in terms of `2 ^ Nat.clog 2 n`; that
refactor was implemented once and reverted at the owner's request. The full rationale
is in the file's own module docstring.

## Module-system conventions

General semantics are in the Lean docs; what follows is project-specific.

**File shape.** `module` → `public import`s → module docstring → `@[expose] public
section` → body → `end`. The style linter requires the docstring *before* the section.

**`@[expose]` is the main hazard.** A `public def` without `@[expose]` is opaque to
importers: `simp`/`rfl`/`decide` cannot unfold it. The defining file still compiles —
the error appears only in *callers*, which makes it easy to misdiagnose. Every `def`
that downstream proofs unfold needs `@[expose]`. Files currently use a blanket
`@[expose] public section`, preserving pre-module semantics; tightening visibility
per-declaration is possible but should be done one file at a time.

**`public import` vs `import`.** When unsure, use `public import` (it re-exports; plain
`import` does not). Getting it wrong surfaces as "unknown identifier" in callers.

**Executable tests do not belong in `module` files.** Running imported code at
elaboration time (`#guard`, `#eval`) needs `meta`-phase imports, and `meta import X`
grants *only* meta access — regular definitions then fail with "may not access
declaration ... imported as `meta`", forcing every import to be duplicated. Hence the
`#guard` suites live in the non-`module` `Tests/` library.

**A `module` cannot import a non-`module` file** (enforced since Lean v4.32). 

**Prefer a public bridging lemma over spreading `import all`.** Core's
`Nat.isPowerOfTwo` is an unexposed `def` unfolding to `∃ k, n = 2 ^ k`, so inside a
`module` neither `obtain` (destructuring) nor `⟨_, _⟩` (construction) sees through it,
and core ships no `iff`-lemma. Rather than add `import all` everywhere,
`NextPow2Lemmas.lean` — which needs `import all` anyway — exports
`isPowerOfTwo_iff_exists : n.isPowerOfTwo ↔ ∃ k, n = 2 ^ k := Iff.rfl`. Importers use
`.mp`/`.mpr` and need no privileged import. The project has exactly one `import all`.

**Per-file constraints belong in that file's docstring**, not in a separate document.
A note next to the constraint is seen during the edit that would break it; a note in a
side file rots.

## Proof style

Priority order when cleaning up: **errors → warnings → style**.

Style targets, roughly in order: remove `set_option` from source files, replace
non-terminal `simp`/`simp_all` with `simp only [...]`, drop `+decide` flags, prefer
`(by tac : X)` over `show X from by tac`, avoid `grind` where `omega`/`linarith`/`ring`
or a targeted `simp only` works (`grind` is slow and opaque), and avoid `refine'` and
`rotate_left`/`rotate_right`.


## Gotchas worth knowing

**A failing `#synth` does not say why it failed.** The instance may not exist, or it may
exist and simply not be reachable from this file's imports; the error looks the same
either way, so grep Mathlib before defining one locally. Search for the *type*, not just
the class — instances hide in unexpected files. `Fintype (BitVec w)` lives in
`Mathlib.Data.FinEnum` (as `FinEnum (BitVec n)` plus the generic `[FinEnum α] → Fintype
α`), not in `Mathlib.Data.BitVec`, and nothing pulls `FinEnum` in transitively. Adding
the import beats redefining: a duplicate instance is not an error, so nothing warns you,
and the two are propositionally equal but not defeq — once both are in scope,
`Fintype.card X` becomes two atoms that print identically (same failure mode as the
`linarith` gotcha below). Defining one anyway is fine when the import cost is real, but
say so in the docstring.

**Subtype cardinality and `linarith`.** `Fintype.card {i // p i}` can appear twice with
different `Decidable` instances; the terms print identically but are distinct atoms, so
`linarith` fails on what looks like trivial arithmetic. Capture the count from the goal
with `set` so the hypothesis shares the instance.

**`@[csimp]`** requires the tagged theorem to be `public` and stated as `@f = @g` (bare
constants, no `∀`-telescope). The left constant is the one replaced in compiled code.
Used for `toeplitzHashNTT_eq_fast`, which makes compiled calls to `toeplitzHashNTT` run
the fast implementation.
