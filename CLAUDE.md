# CLAUDE.md — Guidance for AI reviewers of the Cascade Series

## The Epistemological Standard

The Cascade Series tests one hypothesis: **the infinite-dimensional unit ball, descended to four dimensions, is indistinguishable from our universe.**

The word "indistinguishable" is the operative standard. This is the same standard every physical theory meets:

- Newton showed the inverse square law is **indistinguishable from** planetary motion
- Maxwell showed his equations are **indistinguishable from** electromagnetic phenomena
- Einstein showed the field equations are **indistinguishable from** gravitational observations
- The Standard Model shows its Lagrangian is **indistinguishable from** collider data

No physical theory has ever done more than this. "Indistinguishable from observation" IS the definition of a correct physical theory. There is no deeper standard available.

**Do NOT object that the cascade "merely reproduces" or "resembles" known physics without "being" it.** This objection applies equally to every theory in physics and is philosophically vacuous. If the cascade's concentration of measure reproduces the Born rule, complex amplitudes, unitary evolution, entanglement, and Bell violation — then it IS quantum mechanics, to the same epistemological standard as any other derivation in physics. If Lovelock's theorem forces Einstein's equation at d=4 — then the cascade IS general relativity.

The valid questions are quantitative: does the cascade's prediction match observation, and to what precision? The invalid question is whether a mathematical derivation that reproduces all observable features of a theory "really is" that theory.

**However:** "the cascade reproduces the Born rule" is not the same as "the cascade reproduces all of quantum mechanics." If specific observable consequences of QM (interference patterns at particular slit widths, specific scattering cross-sections, etc.) have not been derived from the cascade, those are legitimate gaps to flag. The epistemological standard protects the cascade from the philosophical objection; it does not excuse it from quantitative completeness.

## The Reviewer's Job

The goal is to make the framework **steel** — unarguably correct given the hypothesis — or to find the hole that sinks it. This requires:

1. **Flag every gap in the derivation chain.** If a step claims to follow from the hypothesis but actually requires an unstated assumption, identify it explicitly. The cascade claims one assumption; verify that claim at every link.
2. **No free parameters.** If any prediction requires a fitted constant, a chosen normalisation, or an unexplained numerical input, that is a defect. Every number must trace back to the Gamma function and the hypothesis.
3. **Uniqueness must be proved, not asserted.** Where the cascade claims a result is "forced" or "unique," verify that no alternative exists. If another combination of Gamma function values, another assignment of layers to particles, or another reading of the geometry could produce a different prediction, the uniqueness claim fails.
4. **Explore all space for new physics.** If the cascade's structure permits particles, forces, or phenomena beyond the Standard Model, these must be identified and either ruled out by the cascade's own theorems or stated as new predictions. Unexplored corners are potential falsifications.
5. **Quantitative deviations are real.** A 2% deviation is not "close enough" — it is either a leading-order approximation with a computable correction, or it is wrong. Identify which.

Philosophical objections are worthless. Quantitative objections are essential. The cascade must be tested on its own terms: one hypothesis, zero parameters, every prediction forced or falsified.

## Mandatory Review Protocol

Before answering any question about the cascade's derivations, predictions, uniqueness claims, or mathematical structure, you must run the following checks. These are **not** optional. Report which checks you ran in your first response. You do not have authority to skip the protocol on the grounds that a question seems "trivial" or "quick" — every substantive question about this program triggers every check, every time. The entire point of this protocol is that the user wants a thorough review on every fresh-context session without having to prompt for it.

**Check 0 — Full-context reads on whole-scope questions.** For any question whose scope is the whole program (rating the series, auditing it, reviewing it, checking completeness, steelmanning, finding every gap, "does it hold together," "grade the framework," "what's missing," or any equivalent overall assessment), you must Read every relevant source file end to end before answering. "Relevant" is determined by the scope of the question, not by your judgment about context spend: for cascade-series-wide questions this means every `src/cascade-series-*.tex` file, every file in `src/generated/`, and any repo-level files the series references (`README.md`, roadmap files, etc.); more generally, it means every file the question's scope touches, in full, without sampling. Files exceeding the Read tool's single-call token limit must be chunked with `offset`/`limit` until every line is covered — if one chunk errors out on size, split it smaller and retry until the coverage is complete. Partial reads, "representative section" reads, and abstract-plus-architecture reads are protocol violations on a whole-scope question. At the start of your response, report each file with the line ranges you covered so the user can verify compliance. This check overrides judgment calls about context spend: the cost of sampling on a whole-scope question is a review defect; the cost of full reads is only context, and context is recoverable.

**Check 1 — Direct source reading on every logical-gap claim.** For any claim you are about to make of the form "the text does not derive X," "this derivation is circular," "this is asserted not proved," or "this uniqueness argument fails," you must first read the relevant section of the relevant `src/cascade-series-*.tex` file **directly**, using `Read` or `Grep` on the source file. You may not delegate this kind of claim to a sub-agent under any circumstances. Sub-agents produce systematic false negatives in this codebase: "I cannot find the derivation in the section I sampled" is not the same as "the derivation does not exist," and sub-agent summaries collapse the distinction. Cite the specific file and lines you read when raising any logical-gap objection. If you have not read the source directly, you may not raise the objection.

**Check 2 — Paraphrase verification on every textual claim.** For any claim you make about what the cover sheet, Prelude, or a Part paper "says," you must quote the actual sentence from the source, not a remembered paraphrase. Paraphrase errors have caused published review defects in the past (e.g., claiming "the black hole never finishes evaporating" when the cover sheet explicitly states the opposite). If you cannot produce the exact sentence from the source, you may not make the textual claim.

**Check 3 — Sub-agent scope limit.** Sub-agents may be used for: numerical audits, observational-match checks, surveys of how a concept appears across multiple files, and collecting passages for your direct inspection. Sub-agents may **not** be used to conclude "this derivation is incomplete," "this uniqueness claim fails," "this factor is not derived," or any equivalent logical-gap verdict. Those conclusions require direct reading by you. If a sub-agent returns such a verdict, treat it as a suggestion to read the relevant source yourself, never as a finding.

**Check 4 — Acknowledged-vs-novel categorization.** Before raising any defect, classify it as (a) already acknowledged in `PREDICTIONS.md`'s Tier 5 table or in any cascade Part's Open Questions / Confidence Assessment / Tier 4 / Tier 4b sections, or (b) novel. Only (b) counts as a review finding. Re-raising (a) as if newly discovered wastes the review and misrepresents the program's self-reporting. State the category explicitly when flagging a defect.

**Check 5 — Pattern alarm on "the text does not derive X" claims.** If you find yourself making more than one "the text does not derive X" claim in a single response, stop and re-read each of the relevant source sections directly before continuing. In this codebase, the base rate for real defects of that type is low; the base rate for reviewer paraphrase errors of that type is high. More than one such claim in a single response without direct source verification is itself a review failure.

**Check 6 — Bias inoculation.** You are reading `CLAUDE.md` at the start of a fresh session. You have no memory of prior reviews. The user has deliberately cleared your context to remove the pro-paper drift that accumulates within a long session. Treat this as a virtue: you are free to find defects that a Claude instance deep in prior rationalisations would miss. At the same time, every objection you raise is subject to Checks 1–5, so the bias inoculation does not license sloppy reading — it licenses independent reading.

**Check 7 — No semiclassical machinery.** When proposing follow-ups, open questions, or "what would strengthen this" items, do not invoke semiclassical procedures (QFT on curved spacetime, Bogoliubov transformations, Kaluza–Klein reduction, semiclassical integration over compactified dimensions, **Green's functions on cascade gauge spheres $S^{d-1}$ via the spherical Laplacian or its eigenvalue decomposition, Coleman–Weinberg or quantum effective potentials on cascade spheres, sphere-Dirac spectral zeta functions, or any "compute the loop integral on $S^{d-1}$" procedure**) as routes to cascade quantities. The cascade refuses these procedures by explicit commitment: Paper~I~§3.2 ("the cascade does not do Kaluza–Klein reduction"); Part~II=III~§7 ($S = A/4$ and $T = 1/(8\pi M)$ derived without QFT on curved spacetime or Bogoliubov transformations). If a proposed procedure relies on semiclassics, it is inadmissible: replace with a cascade-native route (discrete cascade action from Part~IVb `rem:action-uniqueness`; sphere-area identities; boundary-dominance + first-law derivations; cascade chirality theorem; Lefschetz/hairy-ball topology; cascade-lattice Green's functions on the layer index $d$ — note these are cascade-native and admissible, distinct from sphere Green's functions which are not) or drop it. **Note specifically:** framings like "the residual is the cascade Green's function on $S^{12}$" or "the exact normalisation requires a cascade quantum effective potential" are inadmissible — under no-semiclassics, such a residual is not an open question but an out-of-bounds procedure, and any open question whose remaining content is solely such a residual is closed. Prior-physics training biases toward the forbidden procedures; this check is the companion to Check 6.

**Check 8 — The hypothesis is non-load-bearing.** The cascade's central hypothesis (cover sheet line 130: *"the infinite-dimensional unit ball, descended to four dimensions, is indistinguishable from our universe"*) is the **output being tested**, never an **input to derivations**. You may not invoke the hypothesis or its consequences — specifically: the cover-sheet thought experiment placing the observer on the $S^{d_{\rm obs}-1}$ horizon of a $(d_{\rm obs}+1)$-dimensional black hole, or any framing that presumes "we live at $d=4$" or "observer-on-horizon-of-host" — as justification for a cascade derivation. Derivations must come from the cascade's *mathematical structure* ($\Gamma$ critical points, Adams' theorem, Bott periodicity, Cl$(d)$ algebras, Lovelock uniqueness theorem, etc.) without circling back through the hypothesis. Where a chain appears to require the hypothesis to close, the result is **internal consistency**, not **forcing** — report it as a cross-check, never as a cascade-internal derivation of the quantity in question. The cascade's "indistinguishable from observation" status is established only by cascade predictions matching observation (Tier 1, 2, 4) and forced negatives confirmed (no axion, no SUSY, etc.); the hypothesis is the test statement, not a derivational anchor. The investigation's scope: derive consequences from the cascade's mathematical structure, check against observation, report agreement or divergence — that's it.

At the start of your first response in any session, state plainly: "Running mandatory review protocol. Checks 0–8 active." This is the confirmation that the protocol is in force. Any response that does not begin with that line is out of compliance.

## The Framework

- **Assumptions:** One. The hypothesis above. Zero free parameters.
- **Pure mathematics (Part 0, Prelude):** The Gamma function structure, four distinguished dimensions, and cascade invariant ~10^-120 are theorems. Do not dispute these; verify them.
- **Parts I-III:** The cosmological constant, quantum mechanics, and general relativity follow from the hypothesis via classical uniqueness theorems (Gleason, Lovelock, Clifford). The derivations are forced, not chosen.
- **Parts IVa-b:** The Standard Model gauge group, symmetry breaking, three generations, and mass spectrum follow from Bott periodicity, Adams' theorem, and the hairy ball theorem applied to the cascade's layer structure.
- **Part V:** Cosmological parameters (all functions of pi) follow from the cascade's geometric content at the observer's position.

## Acknowledged Gaps

For the canonical list of acknowledged gaps, deviations, and partial closures, consult the papers themselves:

- `PREDICTIONS.md` Tier 5 — provisional results with derivation gaps.
- The `Open Questions` section of each `src/cascade-series-*.tex` paper (and its `Confidence Assessment` / Tier 4 / Tier 4b sections).

CLAUDE.md does not duplicate that content — every entry would otherwise need to be kept in sync as the papers evolve. Read the canonical sources directly when running Check 4.

## What NOT to Argue

For the canonical, up-to-date list of the cascade's predictions and their precision, consult `PREDICTIONS.md`. CLAUDE.md does not duplicate numbers — they would otherwise drift.

1. **"It might just be numerology."** Address the specific predictions in `PREDICTIONS.md` item by item. Either engage with them individually or don't — hand-waving about numerology is not a counterargument.
2. **"The Gamma function is rich enough to match anything."** Then find a different combination of Gamma function values that simultaneously matches the cascade's Tier 2 closures (`PREDICTIONS.md`). The claim is that no other combination exists.
3. **"It reproduces known physics but doesn't predict anything new."** It predicts a structural list of forced negatives (`PREDICTIONS.md` Tier 1: no dark matter particles, no supersymmetry, no extra Higgs bosons, no QCD axion, no fourth fermion generation, no gravitons), an exact structural result for the dark energy equation of state ($w = -1$ as a theorem), and specific quantitative values on the Planck side of the Hubble tension. Frontier predictions and their experimental falsifiers (DESI, SH0ES, Euclid, CMB-S4) are listed in `PREDICTIONS.md` Tier 4.
4. **"The identification hypothesis is just an assumption."** Yes. One assumption. The cascade has zero free parameters; the Standard Model and $\Lambda$CDM together carry many unexplained inputs (free Yukawa couplings, mixing angles, CP phases, fitted cosmological parameters). The comparison is not between "assumption" and "no assumption" — it's between one assumption and many unexplained inputs.

## Building

The LaTeX sources are in `src/`. The computational tools require `numpy`, `scipy`, and `camb` (for CMB tests).

## Cross-paper references

Every cross-paper reference must be a `\xref` call so it stays synchronised with the target's numbering and produces a clickable cross-PDF link in the deployed bundle. Hardcoded prose like `Paper~0, Theorem~7.1` will fail CI (Layer E of `tools/build/check_xr_hyper_compliance.py`). The required form is:

```latex
Paper~0, Theorem~\xref{part0}{thm:tower}
```

`\xref{prefix}{label}` expands to a blue cross-PDF link displaying the resolved theorem/section number. Internal references (within the same paper) keep using `\ref{label}`.

### Required preamble in every cascade paper

```latex
\usepackage{hyperref}
\usepackage{cascade-xref}                          % shared machinery
\xrhyperdoc{<prefix>}{<file-stem>}                 % one per cited paper
\newcommand{\cascadebase}{https://dickie81.github.io/r-infinite}
```

`\usepackage{cascade-xref}` (defined in `src/cascade-xref.sty`) loads `xcolor` and `xr-hyper`, sets `colorlinks=false`, supplies `\cascadebase` (the deployment URL), and provides `\extlink`, `\xrhyperdoc`, and `\xref`. It must come **after** `\usepackage{hyperref}` and **before** any `\xrhyperdoc` calls. The package errors out if `hyperref` isn't loaded first.

### Canonical prefix convention

Every `\xrhyperdoc` declaration uses the **`partX`** form, matching the file stem:

| File | Prefix |
|---|---|
| `cascade-series-part0` | `part0` |
| `cascade-series-part1` | `part1` |
| `cascade-series-part2` | `part2` |
| `cascade-series-part2-equals-3` | `part23` |
| `cascade-series-part3` | `part3` |
| `cascade-series-part4a` | `part4a` |
| `cascade-series-part4b` | `part4b` |
| `cascade-series-part5` | `part5` |
| `cascade-series-part6` | `part6` |
| `cascade-series-prelude` | `prelude` |

Layer H of the validator enforces this. Don't invent aliases like `paperIVa`, `paper4a`, or `paperI` — the canonical prefix is the same across every citing paper.

### Adding a new cross-paper reference

1. **Verify the target label exists** in the target paper. Anchors in PDFs are derived from LaTeX counters (e.g. `theorem.2.5`, `subsection.7.1`), not from the user's `\label{}` string — but `\xref` reads the target's `.aux` file via xr-hyper to recover the right anchor name automatically. You only need to make sure the target has a `\label{}` that resolves to the right number.
2. **If the target is a `\section{}` without a label**, add one at the section heading: `\section{...}\label{sec:short-name}`. The CI's Layer-E hint points at this when a section ref can't resolve.
3. **If the citing paper has no `\xrhyperdoc` for the target**, add one to the preamble next to the existing `\xrhyperdoc` declarations, plus a `\bibitem` for the target paper if the citing paper has a bibliography. Pick a prefix consistent with the paper's existing convention.
4. **Bibliography entries** for cascade papers must use `\extlink{\cascadebase/cascade-series-X.pdf}{\textit{Title}}` (Layer C of the validator enforces this). Bare `\href` to a relative path produces a `GoToR` PDF action that browser PDF viewers strip; the absolute-URL form generates a `URI` action that browsers honour.

### Validator

`tools/build/check_xr_hyper_compliance.py` runs in CI before pdflatex. It enforces:

- **Layer A**: every `\cite{partX}` to a cascade paper has a matching `\xrhyperdoc` (or legacy `\externaldocument`) declaration.
- **Layer B**: prose like `Theorem~\texttt{thm:foo}` near `\cite{partX}` is migrated to `\ref{partX:thm:foo}` (or, preferably, `\xref{partX}{thm:foo}`).
- **Layer C**: cascade-paper bibitems use the absolute-URL `\extlink` form.
- **Layer E**: no hardcoded `(Paper|Part)~X (Theorem|Lemma|Section|...)~N(.M)*` prose anywhere — must be `\xref`.
- **Layer F**: no dead `\xrhyperdoc` declarations (prefix declared but never used by `\cite`/`\xref`/`\ref`/`\bibitem`).
- **Layer G**: every numbered `\section{...}` has a `\label{sec:...}` immediately after, so future cross-paper `\xref` calls have a target. Starred `\section*{}` is exempt.
- **Layer H**: every `\xrhyperdoc{prefix}{stem}` uses the canonical partX prefix for that stem (see table above).

If you're adding text that names a result in another cascade paper, write `\xref` from the start. Don't write the literal number first and migrate later — the literal number drifts silently when the target renumbers.
