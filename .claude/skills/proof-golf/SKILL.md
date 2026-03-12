---
name: proof-golf
description: Perform proof golfing on a Lean file — fix errors, warnings, and style issues
argument-hint: [filename]
---

You are performing "proof golfing" on $ARGUMENTS (default: the current file open in the IDE).

Read ${CLAUDE_SKILL_DIR}/ProofGolf.md for the full guidelines. In summary, the priorities in order are:

1. **No build errors** — the file must compile cleanly.
2. **No warnings** — fix issues; do not silence linters with `set_option`.
3. **Readability and simplicity** — shorter proofs, reusable helper lemmas.

## Workflow

Work on one issue at a time, in this order:

1. Check the current state: grep for `set_option`, `refine'`, `rotate_right`, trailing semicolons, `simp_all +decide`, `simp +decide`.
2. Pick the highest-priority issue (errors first, then warnings, then style).
3. Make the minimal change that fixes it.
4. Verify the file still builds (report what you changed and why).
5. Move to the next issue.

## What to fix (in priority order)

- Remove `set_option maxHeartbeats` — extract expensive subgoals as separate lemmas, or replace `simp_all +decide [long list]` with `simp only [...]; push_cast; ring`.
- Remove `set_option linter.*` — fix the underlying issue instead.
- Replace `refine'` with `refine`, `exact`, `apply`, `intro`, or `constructor`.
- Remove `rotate_right` — restructure so goals appear in the natural order.
- Remove trailing semicolons (`;`) at the end of lines unless the tactic closes the goal.
- Replace non-terminal `simp`/`simp_all` with `simp only`/`simp_all only`. Use `simp?` or `simp_all?` to discover lemma names — do not guess.
- Remove `+decide` and `+zetaDelta` from `simp` calls where possible.
- Replace `refine fun x y hxy => ?_` with `intro x y hxy`.

## Important constraints

- **Never change theorem statements** — only change proofs and add private helper lemmas.
- **Never use `set_option` to silence a warning** — fix the cause.
- Keep changes small enough to verify mentally or by building.
