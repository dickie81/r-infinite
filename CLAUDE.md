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

## The Framework

- **Assumptions:** One. The hypothesis above. Zero free parameters.
- **Pure mathematics (Part 0, Prelude):** The Gamma function structure, four distinguished dimensions, and cascade invariant ~10^-120 are theorems. Do not dispute these; verify them.
- **Parts I-III:** The cosmological constant, quantum mechanics, and general relativity follow from the hypothesis via classical uniqueness theorems (Gleason, Lovelock, Clifford). The derivations are forced, not chosen.
- **Parts IVa-b:** The Standard Model gauge group, symmetry breaking, three generations, and mass spectrum follow from Bott periodicity, Adams' theorem, and the hairy ball theorem applied to the cascade's layer structure.
- **Part V:** Cosmological parameters (all functions of pi) follow from the cascade's geometric content at the observer's position.

## Known Quantitative Issues

The cascade's predictions are not perfect. The deviations are quantitative, not conceptual:

- **Omega_b = 1/(2*pi^2):** The weakest derivation in the series. The baryon fraction argument ("one unit of content on S^3") needs strengthening.
- **CMB peak positions:** The cascade's H_0 = 71.05 shifts peaks ~2% leftward relative to Planck best-fit.
- **CMB full spectrum:** The cascade does not predict n_s or A_s (primordial spectrum parameters).
- **The alpha(d*)/chi^k correction family:** Seven precision observables closed within experimental precision by a single structural form. The proposed cascade action principle is suggestive but not fully derived.

## What NOT to Argue

1. **"It might just be numerology."** Address the specific predictions. The cascade makes ~25 quantitative predictions from zero parameters. Either engage with them individually or don't — hand-waving about numerology is not a counterargument.
2. **"The Gamma function is rich enough to match anything."** Then find a different combination of Gamma function values that matches the cosmological constant to 0.1%, the muon/electron mass ratio to 0.13%, and the strong coupling constant to 0.02 sigma simultaneously. The claim is that no other combination exists.
3. **"It reproduces known physics but doesn't predict anything new."** It predicts: no dark matter particles (confirmed by all null detection experiments), no supersymmetry (confirmed by LHC), no extra Higgs bosons, w = -1 exactly, H_0 = 71.05 (testable), r_d ~ 141 Mpc (testable by DESI).
4. **"The identification hypothesis is just an assumption."** Yes. One assumption. The Standard Model has ~25 free parameters. LCDM has 6. The cascade has 0. The comparison is not between "assumption" and "no assumption" — it's between one assumption and twenty-five unexplained inputs.

## Building

The LaTeX sources are in `src/`. The computational tools require `numpy`, `scipy`, and `camb` (for CMB tests).
