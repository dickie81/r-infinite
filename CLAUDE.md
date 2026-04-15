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

**Check 4 — Acknowledged-vs-novel categorization.** Before raising any defect, classify it as (a) already acknowledged in CLAUDE.md's "Known Quantitative Issues" section or the series' Tier 5 predictions table, or (b) novel. Only (b) counts as a review finding. Re-raising (a) as if newly discovered wastes the review and misrepresents the program's self-reporting. State the category explicitly when flagging a defect.

**Check 5 — Pattern alarm on "the text does not derive X" claims.** If you find yourself making more than one "the text does not derive X" claim in a single response, stop and re-read each of the relevant source sections directly before continuing. In this codebase, the base rate for real defects of that type is low; the base rate for reviewer paraphrase errors of that type is high. More than one such claim in a single response without direct source verification is itself a review failure.

**Check 6 — Bias inoculation.** You are reading `CLAUDE.md` at the start of a fresh session. You have no memory of prior reviews. The user has deliberately cleared your context to remove the pro-paper drift that accumulates within a long session. Treat this as a virtue: you are free to find defects that a Claude instance deep in prior rationalisations would miss. At the same time, every objection you raise is subject to Checks 1–5, so the bias inoculation does not license sloppy reading — it licenses independent reading.

At the start of your first response in any session, state plainly: "Running mandatory review protocol. Checks 0–6 active." This is the confirmation that the protocol is in force. Any response that does not begin with that line is out of compliance.

## The Framework

- **Assumptions:** One. The hypothesis above. Zero free parameters.
- **Pure mathematics (Part 0, Prelude):** The Gamma function structure, four distinguished dimensions, and cascade invariant ~10^-120 are theorems. Do not dispute these; verify them.
- **Parts I-III:** The cosmological constant, quantum mechanics, and general relativity follow from the hypothesis via classical uniqueness theorems (Gleason, Lovelock, Clifford). The derivations are forced, not chosen.
- **Parts IVa-b:** The Standard Model gauge group, symmetry breaking, three generations, and mass spectrum follow from Bott periodicity, Adams' theorem, and the hairy ball theorem applied to the cascade's layer structure.
- **Part V:** Cosmological parameters (all functions of pi) follow from the cascade's geometric content at the observer's position.

## Known Quantitative Issues

The cascade's predictions are not perfect. The deviations are quantitative, not conceptual:

- **Omega_b = 1/(2*pi^2):** The weakest derivation in the series. The baryon fraction argument ("one unit of content on S^3") needs strengthening.
- **Cosmological constant:** $\rho_\Lambda/M_{\rm Pl,red}^4 = 18\,\Omega_{19}\Omega_{217}/\pi^3 = 6.996 \times 10^{-121}$, from Part 0's bilinear invariant plus two cascade-native sphere-area corrections: host frame $(\Omega_5/\Omega_7)^2 = 9/\pi^2$ at $d_V \to d_0$, and 3D projection $\Omega_2/\Omega_3 = 2/\pi$ at the observer's $S^3$ slice under locked time. The $\pi/2$ projection factor reflects that time is the observer's locked asymptotic infall toward the host 5D-BH pseudo-horizon (Part II §7.1), not a free fourth dimension, so cascade content from above projects over only 3 dimensions; the factor is the elementary latitudinal integral $\int_0^\pi \sin^2\theta\,d\theta = \pi/2$ expressed as the Morse foliation of $S^3$ by 2-spheres. Leading deviation $-2.2\%$, Gram-corrected $-0.07\%$. Descent-dependent population. A complete first-principles derivation of the $2/\pi$ factor from an explicit Kaluza–Klein reduction over the 213 compactified interior dimensions plus the locked-time infall onto $S^3$ is Part I's outstanding open problem.
- **H_0 = 66.78 km/s/Mpc (Option A):** Under Part I's $\rho_\Lambda = (2/\pi) I M_{\rm Pl,red}^4$ with the locked-time 3D projection, cascade $H_0$ sits 0.9% below Planck's 67.4 and is incompatible with SH0ES's 73. The Gram correction brings cascade $H_0$ to ~67.5, essentially on top of Planck. This supersedes the earlier "lapse-corrected Friedmann" derivation that gave $H_0 = 71.05$ and the "between tensions" claim; that chain applied the wrong frame-conversion mechanism ($N(4)^2$ lapse) and has been retracted. The CMB peak positions accordingly shift by ~1% relative to Planck best-fit under Option A (not 2%).
- **CMB full spectrum:** The cascade does not predict n_s or A_s (primordial spectrum parameters).
- **T_CMB = 2.642 K:** Under Option A this is 3.1% below observed 2.7255 K (T_CMB scales as sqrt(H_0) through the Friedmann-derived relation $\rho_r = (\pi^2/30) g_{eff} T^4$; the lower $H_0$ propagates). Descent-dependent through $H_0$; Gram-corrected ~2.1% low; closing the last 2% requires a second-order correction or absorbing $g_{\rm eff}$ into cascade-intrinsic counting.
- **DESI BAO fit:** Under Option A, cascade $r_d \approx 147.75$ Mpc is essentially equal to Planck's 147.60 Mpc, so the cascade and Planck share a ruler. The cascade fits DESI at $\chi^2/n = 2.35$ vs Planck's 1.90 — slightly worse, driven by the two shared outlier bins at $z=0.510$ and $z=0.706$. The cascade no longer has a ruler-mismatch mechanism to explain the apparent $w \neq -1$ signal; it predicts $w = -1$ exactly as a structural theorem and is challenged by DESI to the same degree as $\Lambda$CDM.
- **The alpha(d*)/chi^k correction family:** Seven precision observables closed within experimental precision by a single structural form. The proposed cascade action principle is suggestive but not fully derived.

## What NOT to Argue

1. **"It might just be numerology."** Address the specific predictions. The cascade makes ~25 quantitative predictions from zero parameters. Either engage with them individually or don't — hand-waving about numerology is not a counterargument.
2. **"The Gamma function is rich enough to match anything."** Then find a different combination of Gamma function values that matches the cosmological constant to sub-$0.1\%$ (after the Part 0 Supplement Gram first-order correction), the muon/electron mass ratio to 0.13%, and the strong coupling constant to 0.02 sigma simultaneously. The claim is that no other combination exists.
3. **"It reproduces known physics but doesn't predict anything new."** It predicts: no dark matter particles (confirmed by all null detection experiments), no supersymmetry (confirmed by LHC), no extra Higgs bosons, w = -1 exactly (structural theorem), H_0 = 66.78 km/s/Mpc (Planck-compatible, incompatible with SH0ES), r_d ~ 147.75 Mpc (essentially equal to Planck's 147.60), universe age 13.88 Gyr. Under Option A these predictions are falsifiable by independent $H_0$ measurements landing on the SH0ES side or by DESI / CMB-S4 fixing $r_d$ far from 147.75.
4. **"The identification hypothesis is just an assumption."** Yes. One assumption. The Standard Model has ~25 free parameters. LCDM has 6. The cascade has 0. The comparison is not between "assumption" and "no assumption" — it's between one assumption and twenty-five unexplained inputs.

## Building

The LaTeX sources are in `src/`. The computational tools require `numpy`, `scipy`, and `camb` (for CMB tests).
