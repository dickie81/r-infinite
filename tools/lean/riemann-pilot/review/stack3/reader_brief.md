# Reader brief: stack review 3 of the Lean pilot

You are a reader for stack review 3 of the Lean pilot at `/home/user/r-infinite/tools/lean/riemann-pilot`
(Lean 4.35.0-rc3, Mathlib at commit 0f64d30a; a Mathlib source tree is at
`/tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad/mathlib4/Mathlib`).
The stack's own Lean files are `src/*.lean`, `external/dh/*.lean`, `external/pnt/*.lean` and `external/zeta23/*.lean`
(the directories `external/pnt/upstream/` and `external/zeta23/upstream/` are vendored code: search them, do not review them).

The lead verifies every candidate you report by reading the source directly. Your report is a list of suggestions,
not findings. **Read-only:** do not create, edit or delete any file anywhere in the repository, do not run git commands
that change state, and do not run any build. You may run `grep`, `rg`, `sed -n`, `wc` and similar read-only commands.

First read `STRUCTURAL-REVIEW.md` from the line `## 9. Stack review 3` to the end: do not report anything listed there.

Then read every line of your assigned files end to end (use the Read tool with offset/limit chunks for long files) and
report, for each file, the line ranges you covered. In each file look for:

- **(A) Doors and missed connections.**
  - A hypothesis that a theorem elsewhere in the stack already discharges: name the discharging theorem with file:line,
    after grepping for it.
  - A result stated for a special case (one modulus, one character, `ζ` only, real characters only, one constant)
    whose proof works in general, or whose general form exists elsewhere.
  - A result that would plug into a named input, display or socket elsewhere: grep for `def … : Prop` displays and for
    hypotheses of the form `(h… : SomeDisplay …)`.
- **(B) Duplicates.** A lemma that re-proves a lemma elsewhere in the stack or in Mathlib at the pinned commit. Name
  both with file:line, and say whether the statements are identical or one is more general.
- **(C) Dead code.** A declaration with no use anywhere: grep its name across `src/` and `external/`. For a helper, a
  use only in its own `#print axioms` line counts as no use. A headline result that ends in a `#print axioms` line is
  not dead.
- **(D) Patterns.** A proof block of at least 8 lines repeated in two or more places with only renamings, which a
  shared lemma would replace. Give both locations.
- **(E) Efficiencies.** Look for these:
  - `set_option maxHeartbeats` or `maxRecDepth` overrides;
  - heavy `decide`, `native_decide` or `norm_num` on large numerals;
  - over-precise numerics, and generated or near-generated repetition;
  - bare `simp` in proofs that are slow or long.
- **(F) Mismatches.** A docstring or module header that claims more or less than the Lean statement proves. Quote both.

Output format: your final message is the report, in plain text.

1. One coverage line per file: `File: lines 1–N read`.
2. Then numbered candidates. Each candidate gives:
   - the category letter and file:line;
   - the verbatim Lean statement line(s), or the verbatim docstring sentence;
   - the other location(s), with file:line and verbatim text, where relevant;
   - the commands you ran to check (the grep lines and their hits);
   - one sentence stating the candidate.

Report nothing you have not checked by grep or by reading. An empty category is fine. Unpadded: no summaries of what
the files do, no praise, no recommendations beyond the candidate itself.
