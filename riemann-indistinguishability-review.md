# External Review of `riemann-indistinguishability.md` — Round 30

**Reviewed artifact:** `riemann-indistinguishability.md` at commit `83aa59f` (branch
`claude/cascade-series-review-1axe9q`, post-Addendum-88 state).
**Reviewer protocol:** CLAUDE.md Checks 0–8 active. This review makes **zero** claims of the
form "the text does not derive X" (Check 5 alarm never triggered); every finding below is a
data-provenance or surface-scope finding, verified by direct reads and by running the code.

## Coverage (Check 0/1 compliance report)

- `riemann-indistinguishability.md`: **lines 1–816, complete** (chunks 1–649, 650–816).
- `riemann-indistinguishability-review-response.md`: lines 1–100 direct (rounds 1–4 tables)
  plus full-file pattern sweeps for Check-4 classification.
- `PREDICTIONS.md`: lines 1–118, complete.
- `cascade-surprisal-audit.md`: overall-accounting section (lines 130–160), addenda 80–88
  headers, and targeted sweeps — used solely to classify findings as acknowledged vs novel.
- `src/cascade-series-part4b.tex`: lines 81–85, 501–505, 1585, 3726–3730, 3918–3960, 4105–4112.
- `src/cascade-series-part4a.tex`: lines 50–62, 157, 188, 234, 280, 300–329.
- `src/cascade-series-part0.tex`: rounding-concession passages (lines 64, 674, 795, 1180–1232).
- **All 27 verifier scripts cited in the paper were executed** (fresh environment,
  numpy/scipy/mpmath): `cascade_formulation_kernel`, `cascade_explicit_formula_bridge`,
  `cascade_zero_side_features`, `cascade_colour_field_bridge`, `cascade_finite_places`,
  `cascade_local_tate`, `cascade_witt_weil`, `cascade_local_family`,
  `cascade_adams_loadbearing`, `cascade_layer_selection`, `cascade_arithmetic_increment`,
  `cascade_second_quantized`, `cascade_arithmetic_period`, `cascade_arithmetic_sign`,
  `cascade_increment_rule`, `cascade_feature_monoid`, `cascade_ds_audit`,
  `cascade_precedence_vacuity`, `cascade_arithmetic_s5`, `cascade_measurement_joint`,
  `cascade_activation_mechanism`, `cascade_joints_derived`, `cascade_arithmetic_d4`,
  `cascade_T4_uniqueness`, `cascade_u2_function`, `cascade_u2_uniqueness`,
  `cascade_u2_first_principles`. **All 27 exit 0.**

## What was verified and held

1. **The verification suite is real and matches the text.** Every script ran clean. The
   in-code gates print computed residuals against stated bounds, and the numbers in the paper
   are the numbers the scripts print: the Theorem-1b worst rearrangement residual is
   1.972×10⁻³¹ (paper: "1.97×10⁻³¹"); the d=12 prime-side residual is 2.05×10⁻⁴¹ within its
   1.56×10⁻⁴⁰ bound (paper verbatim); the window splits Φ(5→13) = 3.226401 − 1.698363 +
   0.011627 = 1.539665 and Φ(13→21) = 4.969202 − 0.904476 + 0.000042 = 4.064768 check by
   hand; Theorem 13b's kill table (44 variants; 187σ, 66σ, 67σ, 4σ; LABEL/RECORD/DATA
   classes; 36 member survivors; six availability survivors; precedence all-six) matches
   `cascade_u2_uniqueness.py` output line for line. The documented failures (the d/s-pairing
   demotion in `cascade_ds_audit`, the feature-monoid failure) print exactly as the paper
   reports them.
2. **Every companion-series quotation checked is verbatim.** part4b:3728 ("the overlap of two
   states, one from each gauge layer"); part4b:83 ("exclusive of the lower endpoint");
   part4b's Tier-2(a) Conditional flag; part4a's `thm:adams` operative sentence (line 329);
   the Cl(1,d−1) spinor-window sentence (part4a:50); the Bott-mirror sentence (part4a:157);
   the d=12-uniqueness sentence (part4a:56–58); "numerical consistency check" (part4a:307)
   and "does not independently derive" (part4a:318); `thm:theta23-closure` does give k=4 with
   −α(7)/χ⁴; `rem:sp36-syntactic` exists; part0's no-uniform-rounding concession is real
   (part0:1180–1232). No paraphrase drift found anywhere — a notable contrast with the
   failure mode earlier rounds document.
3. **The classical mathematics spot-checked independently is correct.** ρ(12)−1 = 3,
   ρ(16)−1 = 8, ρ(14)−1 = 1; Poincaré–Hopf rows (odd d → even sphere → 0 fields); the mod-8
   windows {4,5,6}/{12,13,14}/{20,21,22} with exactly one complete window in (7,19];
   level(ℚ₂) = 4 and level(ℚ_p) = 1 or 2 by p mod 4, giving Witt-image exponents
   2·level ∈ {2,4} at odd p — the Theorem-1g exclusivity chain's classical inputs are right;
   |W(ℚ₂)| = 32, |W(ℚ_p)| = 16 (Lam) are right; quadratic Gauss-sum phases ({1,i} odd
   moduli; ζ₈ at 4-divisible; 0 at 2 mod 4) are Gauss; Landsberg–Schaar's mediating e^{iπ/4}
   is classical; {k : γᵏ = −1} = {4} in μ₈ is immediate; Γ(½)⁴ = π². The
   Steenrod–Whitehead-settles-v₂≤2 claim in the Door-3 Remark is consistent with the
   standard history (the 1951 theorem covers n not divisible by 16), and the paper's own
   citation-confidence caveat already flags the paywall limitation.
4. **The honesty architecture is functioning.** The paper's graded-status discipline
   (theorem / graded identification / convention / instantiation / withdrawn) is applied
   consistently across Theorems 1–13c; the run-record rule preserves failed first runs; the
   abstract's residue count (seven items, one marked deletable-on-uniform-reading) is
   internally consistent with §5–§7. The repo's own surprisal audit — which prices the
   precision closures at ~0 bits and the whole program at ~10 guaranteed bits pending the
   correction family's look-elsewhere burden — is the correct adversarial instrument for the
   "Gamma is rich enough" objection, and §10.3's staking of the framework's standing on the
   pre-registered ledger rather than the retrodictions is the epistemically correct response
   to that audit's verdict.

## Findings

### F1 (novel — moderate): the ℓ_A observed reference 301.6 ± 0.09 is uncited and appears to be a vintage hybrid; the headline "largest strain −1.8σ" is not stable under any consistent choice

The paper's largest-strain figure — abstract ("largest strain ℓ_A at −1.8σ"), §8 table
("vs 301.6 ± 0.09"), §9 framing — divides the cascade's 301.44 by an observed value that
carries **no citation anywhere in the repository**. A full sweep finds `301.6` asserted
bare in `src/cascade-series-part5.tex:493,769` ("Planck's 301.6"), and `±0.09` attached in
`cascade_precedence_vacuity.py:119`, `cascade_null_model_surprisal.py:352–353`,
`cascade_chirality_theorem.py:237`, `cascade_open_closed_mixed.py:136`,
`tools/verifiers/sign_rule_structural.py:100`, with no distance-priors reference in any
`.tex` or `.py` file.

The published compressed-likelihood values are: Planck 2015, ℓ_A = 301.63 ± 0.15; Planck
2018 chains, ℓ_A ≈ 301.53 ± 0.083 (TT,TE,EE+lowE+lensing; ≈301.46 ± 0.089 in some chains).
The repo's 301.6 ± 0.09 pairs a 2015-era central value with a 2018-era error bar. Against
any single published product the strain is **smaller** than the headline: −1.07σ (Planck
2018 +lensing), −1.27σ (Planck 2015), ≈ −0.25σ (301.46 chain). The error's direction is
against the framework — this is the opposite of favorable selection, so no motivated-choice
charge arises — but the paper's most-quoted single number (it appears in the abstract, §8,
PREDICTIONS.md:57, and four scripts) is currently an artifact of an inconsistent reference
pairing. Note the irony: review Finding 5 corrected the ℓ_A *σ-labeling* twice without
either round ever pinning the *observed value's provenance*.

**Recommendation:** pin one published compressed-likelihood product (with citation and
chain identification, since ℓ_A varies by ~0.1 across Planck 2018 chains), recompute the σ,
and propagate through the same repository-wide sweep discipline rounds 3–4 established.
Under every consistent choice the paper's strain profile *improves*; the abstract's
"largest strain" clause may need to hand the title to m_ν3 (−2.9σ, NuFit-conditional).

### F2 (novel — minor): §8's "current world data" claim is inaccurate for the m_H row (PDG 2022 vintage)

The m_H deviation −0.35σ is computed against 125.25 ± 0.17 (verified in
`cascade_geodesic_action.py:57`, `cascade_height_lemma.py:69`, `cascade_null_clone.py:122`,
`cascade_mhmw_case.py:22`, which also pin m_W = 80.377). PDG 2024 gives
m_H = 125.20 ± 0.11, under which the row reads ≈ −0.05σ — the direction is benign (the
agreement improves), but §8 opens with "deviations are against current world data," and for
this row that is not true. **Recommendation:** state a data vintage per row (or one global
vintage date), as the two-metric discipline already does for the metric convention; refresh
m_H/m_W to PDG 2024 in the four scripts.

### F3 (instance-novel of an acknowledged class — minor): two headline surfaces state the determination claim without the chain-scope qualifier that §6 and Theorem 13 carry

§6 states plainly that the exhaustion-verified chain covers ~60 of ~100 discrete entries and
that "rows outside the exhaustion's scope … have not been exhaustion-verified"; Theorem 13
scopes itself the same way. But the abstract still says "given one explicit instantiation
map, the rules leave zero residual freedom," and §8 opens "Every output below is forced by
Theorems 8–13 under Definition 6.1" — both quantify over the full record, including the
rows (m_H, y_t, the c/u stages, the M_Pl→v anchor, 1/α_em, the radiative slot, the
cosmological forms) whose single-valuedness under the rule-set is asserted but not
exhaustion-verified. Round 4's S-class ("abstract's unqualified forcing — swept") shows
this exact surface class was hunted before; these two instances survive in the current
text. **Recommendation:** add the qualifier at both surfaces ("zero residual freedom on the
exhaustion-verified chain; the remaining rows determined by the same rule-set, unverified"),
matching §6's own language.

### F4 (novel — cosmetic): D1 is counted in the abstract's seven-item residue but absent from §10's enumeration

§10.2 lists Lovelock, A2, the unit convention, the precedence, and the feature→layer
convention; §10.1 covers C1. The definition D1 — the abstract's second residue item — has
no §10 entry. Either list D1 in §10 (with its "no tunable content" grading from Theorem 12)
or footnote why the Honest-limits section enumerates six of the seven.

## What this review did not find

- No paraphrase errors (every checked quotation verbatim — the base-rate failure mode of
  prior rounds is absent from the current text).
- No arithmetic errors in any hand-checkable identity or window split.
- No divergence between script output and textual claim in any of the 27 scripts run.
- No unlisted convention beyond the seven-item residue (the round-9/-15/-22/-25/-28 attack
  surfaces — precedence vacuity, d/s pairings, minimality-pairing, quantifier scope,
  self-containment of the layer Remark — all read as the text says they resolved).
- No Check-7 violations: the paper's arithmetic block (Theorems 1b–1g) is explicit-formula
  and Weil-index classical machinery, not semiclassics, and its "no grammar entry is
  derived" scoping is enforced in-code, not just asserted.

## Verdict

The mathematical core and its verification suite survive this pass intact: zero
mathematical findings, zero textual-fidelity findings. All four findings are
reference-data provenance and surface-scope items, of which F1 is the only one touching a
number the abstract quotes — and it moves the paper's worst strain in the paper's *favor*
once repaired, while simultaneously demonstrating that the record table's observational
side has not yet received the same provenance discipline as its arithmetic side. The
conditional structure of Theorem 14 (indistinguishability conditional on a ~100-entry
discrete instantiation map, priced honestly by the repo's own surprisal audit at ~10
guaranteed bits, staked on a frozen falsifier ledger) is stated accurately by the current
text. The paper is what it says it is: one hypothesis, zero continuous parameters, a
seven-item non-arithmetic residue, and a kill schedule — with an observational reference
layer that now needs one round of citation-pinning to match the rigor of everything above
it.
