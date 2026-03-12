# Proof Golfing Guidelines

Proof golfing in this project means, in order of importance and priority when working on it:
- make sure there are no build errors
- make sure there are no warnings (fix the issues. Do not silence linters using `set_option`)
- more proofs more readable, simple and shorter. Split off reusable helper lemmas.
- Try to generalize statements of helper lemmas.

## Principles

### No `set_option maxHeartbeats`
Proofs should fit in the default heartbeat budget (400 000). Strategies:
- **Extract subgoals as separate lemmas** — each gets its own budget.
- **Replace `simp_all +decide [long list]` with targeted rewrites** — broad `simp_all`
  is the most common heartbeat offender; use `simp only [...]`, `push_cast`, and `ring`
  instead.
- **Avoid `norm_cast` loops** — use explicit casts (`Nat.cast_pos.mpr`, `exact_mod_cast`)
  rather than repeated cast-normalization.

### Do not silence linters
Fix the underlying issue instead.
Do not use `set_option` to silence linters
E.g.,
- `refine'` warnings → use `refine`, `exact`, `apply`, or `constructor`.
- `unusedSectionVars` → add `omit [X] in` before the declaration.
- `longLine` → break the line.
- Do not eliminate warnings about unused variables by prefixing an underscore. Remove the variable instead.

### Replace `refine'` using `refine` / `exact`
`refine'` accepts under-specified metavariables; `refine` is stricter but clearer.


### Name helper lemmas well and keep them reusable
Private lemmas that are used only once can stay in the file; 
Those used in multiple files should go in a shared utility module.
Keep naming according to Mathlib conventions.

### Use `push_cast` + `ring` instead of `norm_cast`-heavy proofs
For goals mixing `ℕ` and `ℚ` arithmetic:
```lean
push_cast [Nat.cast_pos.mpr hpos]
ring
```
is typically faster than `norm_cast` + algebraic manipulation.

### Use `omega` for pure natural-number arithmetic
Use `omega` for linear arithmetic over `ℤ`/`ℕ`. 
Especially instead of `linarith` + `norm_cast` when the goal is purely integral.

### Use `positivity` for non-negativity goals
`positivity` handles `0 ≤ f x` goals automatically for products, powers, and sums.

### never change the statements of existing theorems

### remove all instances of `rotate_left`, `rotate_right` and other tactics that purely change order of goals

### Replace non-terminal `simp` and `simp_all` by `simp only` and `simp_all only`
To find lemmas names, use `simp?` and `simp_all?`.
Do not try to guess the required lemma names.

### For any tactics that produce output, consider following that advice.

### Do not put multiple tactics separated by semicolons on the same line unless they close the goal.

### Try to remove `+decide` and `+zetaDelta`

### No unnecessary trailing semicolons

### No sections containing only one definition/theorem
In such cases, include variables directly in the definition/theorem.

### Do not mark things `noncomputable` unless they would otherwise fail

## Workflow

1. **Build first**: make sure the file compiles cleanly before changing anything.
2. **One change at a time**: make a single logical change (e.g., replace one `refine'`,
   extract one lemma), then verify it still compiles.
3. **Check diagnostics**: after each change, look at the IDE diagnostics panel. Zero
   errors, zero warnings is the goal.

## Common Patterns to Eliminate

| Anti-pattern | Replacement |
|---|---|
| `set_option maxHeartbeats N in theorem ...` | Extract expensive subgoals as lemmas |
| `set_option linter.X false in theorem ...` | Fix the underlying issue |
| `refine' ⟨_, ..., _⟩ <;> try infer_instance` | `exact ⟨inferInstance, ..., ?_⟩` |
| `norm_num at * <;> try nlinarith` | Explicit `have` + `linarith` / `nlinarith` |
| `generalize_proofs at *; nlinarith [...]` | Introduce nonzero hyps, then `field_simp [h]; nlinarith` |
| `refine fun x y hxy => ?_` | `intro x y hxy` |

## Automation Opportunities

Try to automate the process.
Use scripts with heuristics.
Make a backup copy before running all scripts.
If any of the scripts introduced errors, revert only the problematic parts to the prior state.
Delete backup once no longer needed.

- **Script: replace `refine'`**
- **Script: find `simp_all +decide`** — grep to find expensive `simp` calls.
- **Linter integration**: `lake build` output should report zero warnings

Be aware of all files in `scripts` folder and `Linters` folder, when they are useful and how to use them.
Linters can be temporarily introduced by adding an import, building to see linter output, then removing the import when no longer needed.

### Useful commands:

```bash
# Find remaining set_option usage:
grep -rn "set_option maxHeartbeats\|set_option linter" UniversalHashing/
```
