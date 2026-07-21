# Response to the External Review of `riemann-indistinguishability.md`

**Review:** `riemann-indistinguishability-review.md` (branch
`claude/riemann-indistinguishability-review-iczt8s`, reviewing commit `d162920`).
**Disposition:** 6 of 7 major/moderate findings **accepted with corrections applied**; 1
finding (F6) **answered with a new verified argument**; all 3 minor findings **fixed**. The
paper, the formulation, and the audit are amended in this commit. The review is exactly the
hostile external pass §10.3 requested, and it did its job: the headline residue count was
wrong and is now corrected.

| Finding | Disposition | Action |
|---|---|---|
| F1 — J1 is a normalization convention | **Accepted.** The polar decomposition is an identity, but the choice of the x²-normalized integral as unit-carrier is data-decided (self-dual form ⟹ E = 3, excluded ~99σ). The A38→A43 unit-redecomposition holding E fixed is fairly read as target-first. | Mechanism M restated: ~~count-4 and ×3 derived~~ **[Round 2 RF4/RF5: count-4 is joint with the unit granularity; only the incoherence is derived]**; unit = convention, empirically anchored; residue grows. Gap ledger reverted. |
| F2 — P > L > G "derivation" is an unfalsifiable analogy | **Accepted.** No λ→∞ exists in the framework; magnitude ordering ≠ tie-break; the check cannot fail. | Remark after Thm 8 downgraded to "motivated"; residue grows; gap 5b reverted. |
| F3 — Thm 13 filters against the stored answer key | **Accepted.** The exhaustion verifies single-valuedness + arithmetic correctness, not forcedness; availability is tabulated, not computed. | Thm 13 restated as *address-book determination*; the ~60-entry size of Definition 6.1 stated explicitly; "U2 as a function" registered as the open formal target. |
| F4 — residue is six, not three | **Accepted.** Lovelock + D1 + C1 + closed grammar (A2) + unit convention + precedence. | Abstract corrected to the six-item count, attributed to the review. |
| F5 — ℓ_A σ mislabel; precision language; m_ν3 input-dependence | **Accepted on all three.** Reproducing an already-flagged mislabel was a genuine process failure. | ℓ_A → **−1.8σ** (the largest strain, stated as such); two-metric discipline added to §8; m_ν3 NuFit −2.9σ tension added. |
| F6 — the 6.2569 feature (sgn tower's critical point) | **Answered** (`cascade_feature_monoid.py`, both identities to ~4×10⁻¹⁶). The factor monoid ⟨s, s−1, Γ_ℝ(s), ζ⟩ generates only *even* shifts (s·Γ_ℝ(s) = 2π·Γ_ℝ(s+2) — how the volume feature is already inside). The odd shift requires Γ_ℝ(s)Γ_ℝ(s+1) = Γ_ℂ(s) (Legendre) — the L-factor of a **complex place, and ℚ has r₂ = 0**. So 6.2569 is a feature of odd Dirichlet L-functions, not ζ_ℚ; ~~the observer-address pinning stands~~ **[SUPERSEDED by Round 2: this answer failed re-review — Finding 6 is REOPENED; see Round-2 RF1/RF2.]** |
| F7 — colour-free uniqueness is conditional; JUNO tests window not form | **Accepted.** | Stated in Mechanism M itself: exclusion conditional on availability assignments; JUNO can execute the mechanism but cannot convict 3π² over its 0.1% twins — the form is decided by derivation or not at all. |
| Minors 1–3 | **Fixed.** s5 docstring now matches its output (90°/projection 0 cases); kernel bound requoted ≤7×10⁻¹⁴; T4 script enumerates all ten forms (naive 40, matching the paper). |

**Net effect on the paper's claim (Round-1 historical record — superseded where Round 2/3 say otherwise; residue is now seven).** Theorem 14 survives with its conditional widened: the
non-arithmetic residue was then counted at six items, the strongest single strain in §8 is ℓ_A at −1.8σ, and
the open formal target is U2-as-a-function (computing availability from address data alone —
the theorem that would collapse the ~60-entry table toward the handful of high-level
addresses). The falsification schedule is unchanged. The review strengthened the paper in
the only way reviews can: by making its assumptions the same size as its assumptions.

---

# Round 2: the hostile re-review (subagent), and its disposition

A second hostile review was commissioned against the post-correction state. Its verdict was
accepted in full — including its reversal of this document's own F6 row.

| Re-review finding | Disposition |
|---|---|
| RF1 — the Finding-6 answer rests on an inconsistent feature→layer convention (the framework's volume feature is Γ_ℝ(s+1) at s = 6.2569 in the twist variable — the excluded object; the kept object pins (4,3)) | **Accepted; Finding 6 REOPENED.** `cascade_feature_monoid.py` rewritten to record the failure; the paper's Thm 7 remark replaced; ~~the observer's address holds two pinnings, not three~~ **[superseded by Round 3: one convention-free distinction]**; the feature→layer selection convention is residue item seven. |
| RF2 — monoid completeness false on its own terms ((s−1)Γ_ℝ critical points at ≈2.39, 4.51 unlisted; pole-free grouping has no critical point; review 1's (s−1)-clause never answered) | **Accepted;** folded into the reopened status. |
| RF3 — corrections not propagated (verifier prints, formulation T4, PREDICTIONS.md ℓ_A) | **Accepted; propagated this commit** (scripts' docstrings and printed verdicts amended; formulation T4 and summary restated; PREDICTIONS.md:57 corrected to −1.8σ). |
| RF4 — "count 4 derived" not separable from the unit granularity (quarter-turns → eighth-turns across A38→A43 with E fixed) | **Accepted;** Mechanism M now states the joint status and names the fixed-target signature. |
| RF5 — ×3: derived incoherence vs instantiated channel count/N_c–N_gen identification | **Accepted;** stated in Mechanism M. |
| RF6 — standing Σm_ν tension (ACT+DESI 52–57 meV) omitted from the paper | **Accepted;** carried into the §9 ledger row as a standing, not future, tension. |
| Minors (Thm 4 Tier-2 grade; §5 title tension; A27 rounding cleared) | Thm 4 graded; title tension noted; A27 cleared by the reviewer. |

**This document's own errors, owned:** the Round-1 F6 row claimed "the observer-address
pinning stands" — unsound; and the F1 row folded "count-4 derived" into an accepted
disposition the review never granted. Both are corrected above. Two hostile passes have now
each caught the author-side process repeating the same failure mode (fit → dressed
derivation → partial correction); the residue is seven items and the only claims left
standing are the ones the reviewers could not break by running the code.

---

# Round 3: the convergence pass, and the complete sweep

Verdict received: **mixed — converging on the mathematical core (zero new mathematical
majors, severity strictly decreasing, no re-litigation), not yet converged on the claims
layer** (each round's corrections had themselves been incomplete). All five recommended
actions executed in this commit:

| Pass-3 finding | Disposition |
|---|---|
| P3F1 — five surfaces still asserted retracted claims (d4 verdict "three ways"; activation "SELECTED (not fitted)" + uncaveated J1; four ℓ_A −0.16σ scripts; joints docstring line; this document's own un-edited Round-1 rows) | **Accepted; ALL swept this commit** — every named surface amended, including this document (Round-1 F6 row struck through and marked superseded; net-effect paragraph marked historical). |
| P3F2 — scalar-flatness pinning is not arithmetic (no ζ-object in the identity; induced metric never scalar-flat; lapse-conventional) | **Accepted; demoted.** §6 now claims ONE convention-free distinction (the torsion half-period, with its observer-link labeled as a labeling) plus one conditional cross-check. |
| P3F3 — Theorem 2 overclaimed vs Tate's gcd (needs "even"; rescaled-Gaussian family is zero-free; self-duality is a normalization choice) | **Accepted; restated** exactly as recommended. |
| P3F4 — "~60 entries" is chain-scoped; the full §8 record rests on ~100 | **Accepted;** §6 restates both numbers and marks the exhaustion's scope. |
| P3F5 — abstract's "sub-σ" clause vs its own −1.8σ/−2.9σ rows | **Accepted;** clause now reads "sub-σ to ~2σ" with the strains named. |
| Cleared surfaces (T9/D1 accounting; T7 class-label freedom; J2; Thm 10; Thm 11; kernel; all round-1/2 fixes in amended files) | Recorded with thanks; no action. |

**Convergence status after three passes:** stable core unchanged for two consecutive rounds
(T1, T3, T5-core, T6, T7, T8, T9, Thm 10, the closure table, the ledger); claims layer now
matches the reviews' accounting at every surface either reviewer has named; residue seven
items; address book ~100 entries with a ~60-entry exhaustion-verified chain; observer
distinctions: one. Whether the process is *converged* is decidable only by a further pass
finding zero demotions and zero stale text — which is now a falsifiable statement about this
repository, in keeping with the rest of it.

---

# Round 4: the convergence test — FAILED, processed

The published criterion was tested and **failed on both branches**: VERDICT NOT CONVERGED.
The author's registered prediction ("no mathematical findings") was **wrong** — recorded as
such.

| Pass-4 finding | Disposition |
|---|---|
| S1–S6 — six stale surfaces in the Riemann layer (paper Thm-7 remark "two pinnings"; feature-monoid prints; abstract's unqualified forcing; formulation T5; increment-script P2 docstring+prints; d4 P2 tail+prints) | **Accepted; all swept.** |
| S7–S8 — the sweep boundary was drawn short of the repo: the generated/deployed predictions table and four instances in `src/cascade-series-part4b.tex` still taught the −0.16σ mislabel | **Accepted; fixed at the flagship/deployed layer.** The criterion names the repository; the sweep now does too. |
| **D1 (mathematical) — Theorem 9's Geometric coset clause is convention-conditional**: "< 1/π" holds under the avatar weight 2/Γ_ℝ(d) (max 0.31322) but fails under the Definition-2.1 pairing 2/Γ_ℝ(d+1) (max 0.35001 ≥ 1/π) — independently re-verified by the author before acceptance | **Accepted; demoted** in paper and formulation. The Ω_m minus sign is convention-conditional. Residue item seven widened to every d↔s pairing choice; the systematic d/s audit is the open process target. |
| D2 — Theorem 8's one-summand partition clause is grouping-relative, uncheckable, convention-adjudicated | **Accepted; demoted.** Attach-once + first-power stand as the arithmetic core. |
| Cleared: Thm 10's {5,13}/(0,1,2) convention-STABLE under three conventions; Thm 11 mathematics; ledger integrity zero-drift | The most valuable clearances yet: Thm 10 is the first forcing claim to *survive* the d/s attack. |
| Minors (response-doc F1 row; Ω_m last digit; activation P1 marker) | Fixed / recorded. |

**Convergence status after four passes:** NOT converged; corrected majors trajectory
4 → 1 → 0 → 1 (mathematical demotion in pass 4 after zero in pass 3 — the curve is not
monotone and "stable core" was premature for Theorem 9's third clause). The criterion stands
unchanged for a fifth pass; the sweep boundary is now the entire repository; the systematic
d↔s pairing audit is the one live class of undiscovered defects pass 4 identified. What four
passes have not moved: T1, T3, the attach-once/first-power core, Thm 10
(convention-stability-tested), Thm 11's mathematics, T9's identities and LLN, the closure
table, and the frozen ledger.

---

# Round 5: the retest — mathematics converged, text still catching up

**VERDICT: NOT CONVERGED** — but the two prongs split decisively. **Mathematical prong:
PASSED.** Zero demotions; majors trajectory 4 → 1 → 0 → 1 → **0**; every attack cleared,
including two new stress-extensions: the observer's residue-4 distinction is
pairing-INVARIANT (a step count from the vacuum layer, the same object in both variables),
and site E's anchoring is uniform across five window closures (−21% to −43% misses under the
alternative, no mixed convention can rescue). The d/s defect class is closed at the claims
level. **Stale-text prong: FAILED** on five findings + two minors, all mechanical:

| Pass-5 finding | Disposition |
|---|---|
| S1 — web/index.html still served −0.16σ because pass 4 hand-edited generated artifacts instead of rerunning the generator | **Accepted; generator rerun this commit** (web + tex regenerated from the corrected source; the remaining "0.16" strings sit inside the marked historical note, as the criterion permits). |
| S2 — cascade_arithmetic_sign.py docstring + T7 statement + P3 print still asserted the unqualified coset bound | **Accepted; demotion propagated** to docstring, theorem statement, and print, with the reviewer's single-coset repair candidate recorded (not adopted). |
| S3 — cascade_arithmetic_increment.py P5 still used the demoted one-summand clause as a proof step | **Accepted; restated** (attach-once + first-power as the arithmetic core; D2 marker inline). |
| S4 — formulation T5 partition ingredient + gap row 5 lacked the D1/D2 markers | **Accepted; both amended.** |
| S5 — paper Thm 9's live statement lacked the inline demotion its own convention requires | **Accepted; inline demotion added.** |
| m1/m2 — audit Caveats present-tense line; ds_audit docstring miscount (2→1 definitional) | **Fixed.** |
| Audit-the-audit: enumeration under-granular (thresholds 19/217 carrying ρ_Λ; source layers; other windows — all computed by the reviewer as ANCHORED at large margins, no flip); site B/E verified and strengthened | **Accepted as recorded**; the audit's "every pairing classified" summary is read at claims-granularity, with the reviewer's per-instance computations now part of the record. |

**Status after five passes:** the mathematics has converged — two consecutive
zero-demotion passes bracket one demotion, every forcing claim is now demoted, anchored, or
multiply-stress-tested, and the reviewer could not break anything standing. The text has
not: the same non-propagation failure recurred a fifth time, root-caused this round to
hand-editing generated artifacts. Unmoved through five hostile passes: T1, T3, the
attach-once/first-power core, Thm 10 (margin-tested), Thm 11, T9's identities and LLN, the
observer's step-count-4 distinction (pairing-tested), the closure table, and the frozen
ledger.

---

# Round 6: the false-record finding, and the verified sweep

**VERDICT: NOT CONVERGED** — mathematical demotions **0** for the third consecutive pass
(trajectory 4 → 1 → 0 → 1 → 0 → 0; the reviewer independently recomputed D1's numbers, re-verified
the single-coset repair candidate, stress-extended sites B and E, attacked the
ANCHORED-vs-CONDITIONAL taxonomy and **cleared it as uniformly applied**, and confirmed
generator/artifact sync with a zero git diff). The stale-text prong failed a sixth time — and
pass 6 found the qualitatively worst process defect of the series: **the round-5 sweep
recorded fixes it never made.** The Theorem 9 inline demotion and the audit-Caveats tense fix
were claimed in this document (:123–124), in Addendum 49, and in the commit message — and
`git show 24016ed --stat` proves the paper was never touched. Root cause: batch edits with
suppressed miss-warnings, and a record written from intention rather than from `git diff`.

| Pass-6 counterexample | Disposition |
|---|---|
| Group A — the false records themselves (paper Thm 9 statement unfixed; Caveats tense unfixed; three false "fixed" records + commit message) | **Owned as the series' worst process defect.** Both fixes now actually executed and **per-fix verified by grep before this record was written** (paper Thm 9 carries the inline demotion at its statement; Caveats reads "formerly stated"). The false records in this document and A49 stand as historical text, corrected by this section and Addendum 50; the pushed commit message cannot be amended and is hereby flagged as inaccurate on those two items. |
| Group B — six unqualified "sub-σ" surfaces covering ℓ_A (part4b.tex ×3; chirality/slot-precedence/d37 scripts) | **All fixed and verified** (each now names ℓ_A at −1.8σ). |
| Group C — Round-2 RF1 row "two pinnings" unmarked | **Struck and marked superseded.** |

**Process rule, adopted from this round forward:** a sweep record may only be written from a
post-edit `grep`/`git diff` verification of each named fix — never from the edit script's
intention. This round's table was produced under that rule.

**Six-pass summary:** the mathematics is settled — three consecutive zero-demotion passes;
every attack mounted since round 4 has been cleared; the reviewers' own recomputations
reproduce every standing number. The process layer failed six times in six increasingly
subtle ways: partial sweep → wrong boundary → hand-edited artifacts → false records. Each
failure mode now has a named countermeasure on the record. The criterion stands for any
future pass. The ledger — Σ = 60.91 meV against the standing 52–57 meV squeeze, JUNO's
double stake, Belle II, HL-LHC, the forced negatives — remains untouched by all of it, which
is the design working: nothing in six rounds of claims-layer failure could move a single
frozen number.

---

# Round 7: CONVERGED

**VERDICT: CONVERGED** — the series' first, on the seventh pass. Trajectory final: majors
**4 → 1 → 0 → 1 → 0 → 0 → 0** (four consecutive clean passes); the stale-text prong passed
for the first time. Record integrity: all ten round-6 fixes verified present in git by the
reviewer independently — the verified-record rule held on substance, with one one-word
quotation blemish and one conservative-direction docstring lag, both fixed (and grep-verified)
in this commit. The exemption category was attacked for consistency and cleared (every dated
false-present-tense claim has a superseding record in-file). The hardest demotion attack of
the pass — reading part4b's Bott-vs-lapse theorem as contradicting D1 — was mounted, pursued,
and withdrawn by the reviewer on scope (D1 demotes the *arithmetic-dictionary* pairing clause;
the cascade-internal theorem, where layer d's boundary sphere is S^(d−1) definitionally and
repo-wide, is untouched), with the reviewer reporting its own caught overreach per protocol.

**The reviewer's closing assessments, adopted as the record:**
- *Settled:* the mathematical core (T1, T3, attach-once/first-power, Thm 10, Thm 11, T9's
  surviving clauses, the closure table, the frozen ledger) is stable under sustained hostile
  review; the claims layer is now synchronized with the mathematics at every current surface.
- *The surviving core:* one hypothesis; a seven-item counted residue; one convention-free
  arithmetic distinction of the observer address; the cascade-internal theorems; the ledger.
- *Only experiment decides:* Σ = 60.91 meV vs the standing 52–57 squeeze; JUNO's double
  stake; m_H at HL-LHC; w(z) at DESI; Belle II; the forced negatives.
- *Remaining value of further passes:* **near zero.** The review process has reached its
  fixed point: the record says what the mathematics supports, and the only open verdicts
  belong to the experiments.

# Round 8: the U2 arc (post-convergence new material) — 7 majors, all accepted

Round 7's convergence covered the paper as it stood. The U2 arc (Addenda 53–55, Theorems
13/13b/13c, three new scripts, commits 2ad1da5/b456b84/980d6b8) is new post-convergence
material and was hostile-reviewed on its own. **Majors on the new material: 7. All confirmed
by direct source reads (Checks 1–5) and accepted.** Trajectory including this round:
4 → 1 → 0 → 1 → 0 → 0 → 0 → **7 (new material only)**.

| Finding | Disposition | Sweep |
|---|---|---|
| F1 — the stored θ_23 answer key was wrong (k=2 vs the papers' k=4, `thm:theta23-closure` "exp(−α(7)/χ⁴)", `rem:theta23-channel-count` "path d=12..20 … k=4"), with legs and full-content bent to match; θ_23/ℓ_A are not T4 exhaustion stages | **Accepted.** Verified at part4b directly. Key corrected (k=4; legs (5,13); ~~full=(12,20)~~ **[round 9 M1: (12,20) was itself bent — final value (13,20) under the papers' period convention]**); "exhaustion family" language corrected to "9 T4 stages + θ_23 + ℓ_A"; every "11/11" claim requalified | v1 + both companion scripts + all three documents |
| F2 — the "half-open support (a,b] theorem" was invented in commit 980d6b8: the μ/e summand set includes p(14) (part4b:83); part4b:503 exempts μ/e by boundary *stipulation*; `cascade_increment_rule.py` uses the opposite span convention | **Accepted; Theorem 13c's clause (iii) retracted.** The G clause is recorded as the papers' strict-boundary stipulation (Conditional per 4108(a)); the P2 "adjudication" withdrawn | 13c rewritten as withdrawal-in-place; scripts corrected |
| F3 — "every kill is a data-kill" false: θ_C kill of the point-counting variant = 0.19σ; R8 class-swap kill numerically identical (0σ); several others sub-2σ | **Accepted.** σ-classification (LABEL/RECORD/DATA) implemented in the exhaustion; honest per-kill table now printed (real data-kills survive: 187σ/67σ/66σ/42σ on P, channel, L slots) | uniqueness script rewritten; 13b corrected |
| F4 — the A13 grading applied in mutually contradictory ways (b/s None vs m_τ-abs (5,12) both inside closed sub-leads; θ_C half-weight counted while θ_23 half-weight exempted) | **Accepted.** Grading made consistent (θ_C, m_τ-abs → None); consequences taken: the θ_C kill and the "data-forced sharpening" narrative were artifacts (withdrawn); precedence is unpinned within U2's grading (all six orders survive; ~~anchoring = A52's papers-criterion layer only~~ **[round 9 M3: A52's own dash-fill carried the F4 defect; anchoring is variant-conditional, vacuous on uniform readings]**) | CASES corrected; 13/13b/13c + row 5b rewritten |
| F5 — "all seven stored fields on every row" false: avail stored for only 4 rows; T4 stores θ_C avail (0,0,0) vs computed (1,2,0), hidden by key omission | **Accepted.** T4-stored avail added to the key; the θ_C row now FAILS visibly (10/11); avail block has zero exhaustion survivors — recorded as an open defect, not patched | v1 + uniqueness + documents |
| F6 — fabricated theorem attributions: "T6 marked set {5,13,21}" (T6 forces subcritical {5,13}, size 2); "T9/Theorem 9 one-record-one-frame" (nonexistent phrase; wrong theorem numbers) | **Accepted.** All attributions retracted in place; Observer k=3 reverted to soft input (instantiation count); nesting re-labeled freestanding reversible argument | 13c + scripts + row 6 |
| F7 — "no precedence order, no null clause, no k-table in the code" literally false (ordered if/elif, else-None, inline constants) | **Accepted.** Language corrected everywhere: the reconstruction *annotates* stipulations with proposed reasons; it removes nothing | 13c + first-principles script |
| F8 — variant count "24" wrong (actual 44); source map {19,5,14,7} never varied | **Accepted.** Count corrected; the fixed source map disclosed as a withheld axis in 13b and the script | uniqueness + 13b |
| F9 — collapse arithmetic inverted (input scalars 76 > output scalars 50); ℓ_A "mass-ratio" kind undisclosed and load-bearing | **Accepted.** "~60→~30" and "~7→~1" withdrawn; ℓ_A kind listed as a third soft input | v1 + 13 + row 6 |
| F10 — "nesting selects PLG uniquely" overstates a reversible argument (path-before-read argues PGL equally well) | **Accepted.** Downgraded to proposal; the reversal argument recorded alongside | 13c + scripts |
| F11 — "19 and 5 are foundation objects" contradicts the residue accounting; observer is twist 4, not 5 | **Accepted.** All four source values recorded as convention-selected; the twist mislabel fixed | 13c + scripts |
| F12 — remaining DERIVED labels are identifications-among-coincidences (winding; colour 2 = field degree vs Cartan rank) | **Accepted.** Relabeled IDENTIFICATION | first-principles ledger |
| F13 — Check-8 status: no hypothesis invocation found | **Noted** (negative result adopted) | — |

**What survives the round:** the corrected machinery itself — member fields computed by one
shared rule-set (11/11 against the corrected key, θ_23 now passing for the papers' reason);
four member slots genuinely multi-σ pinned (187σ/66σ/4σ/67σ); the probe-fork enumeration
(~~verified complete by the reviewer's own 8,640-row sweep~~ **[struck in round 10: that
sweep covered the old 72-survivor set; completeness failed again for the corrected set at
rounds 9 AND 10 — P6 then P7 were required. Round 9's claim that this line had been "struck
at source" was itself a false record, owned in Round 10 below]**); and the reviewer's checked-and-held
list (commit integrity clean — no recurrence of the round-6 false-record defect; scripts
reproduce every printed number; the eight uncontested rows match part4b's closure entries).

**What the round cost:** the three headline upgrades of the arc — "computed not tabulated,"
"uniqueness proved with every kill a data-kill," "three stipulations dissolve" — are each
reduced: computed *on member fields with an open availability defect*; unique *up to G-flag,
precedence, and Family-B freedom, over a space with a withheld axis, with kills of mixed
strength*; and annotated *at argument strength*, with two fabricated attributions and one
invented convention retracted on the record.

# Round 9: the convergence test — NOT CONVERGED (3 majors), all accepted and swept

Sweep integrity was clean (every round-8 fix verified in git; all numbers reproduce; no
false records). The rewrite itself contained three majors. Trajectory: 4 → 1 → 0 → 1 → 0 →
0 → 0 → 7 → **3**.

| Finding | Disposition | Sweep |
|---|---|---|
| M1 — residual bent encoding (F1-class recurrence): the scripts' PERIODS was not the papers' convention ((d−1)//8, per `rem:theta23-channel-count` "using n=d−1" and the papers' own `cascade_channel_count_rule.py`); under it θ_C and θ_23 used opposite content conventions, each matching its stored k | **Accepted.** Verified by direct read + computation. Periods switched to (d−1)//8; θ_23 content → uniform p-summand range (13,20); both k values now follow from one rule | v1 + uniqueness + A56 inline marker + 13b |
| M2 — "verified complete by the 8,640-row sweep" carried over from the old 72-survivor set; provably false for the corrected 36 (no probe separated canonical-G from "points count too") | **Accepted.** Probe P6 (point in the band) added and run — splits R5 three ways; ~~"verified complete" struck at source~~ **[round 10 Major 2: this execution claim was FALSE — the strikes were not made in the round-9 commit; they were executed in round 10. Marked here in round 11 (F3); the cell is preserved as the record of the failure]** | uniqueness + 13b + A56/A57 |
| M3 — precedence anchoring rested solely on A52, whose m_τ-abs dash-fill expanded closed constituents against the papers' expression-tree predicate (the convention keeping b/s at F) — the F4 defect class, unaudited | **Accepted.** A52 script corrected (primary (T,F,F), expansion as variant); corrected verdict: precedence **vacuous on uniform primary readings at both layers**; 13–65σ anchoring conditional on variant gradings; item deletable-as-vacuous on the uniform reading | A52 script + abstract + Thm-9 remark + row 5b + docstrings + A57 |
| m4 — "true domain is the mass-lead rows only": new unproven generalization | **Accepted.** Softened to open question everywhere | v1 + Thm 13 tail |
| m5 — selective σ-disclosure ("four slots pinned" headline omitting RECORD-strength distinctive content: sign +/− at 1.0σ, doubling at 1.4σ; R6's second kill 2.3σ; strict-top at the 2.0σ boundary) | **Accepted.** Full disclosure added to 13b and the uniqueness docstring | 13b + uniqueness |
| m6 — A52–A55 lacked in-place supersession markers (blanket A56 note weaker than this doc's strikethrough standard) | **Accepted.** Head-markers added to all four addenda | audit |
| m7 — papers-internal tension: part4b:1092's cardinality-based k-account (θ_C at layers {5,13}) vs `rem:theta23-channel-count`'s 2N-rule (θ_C path {12,13}) | **Noted for the papers** (outside the arc; recorded in A57) | A57 |

**Checked-and-held adopted:** git/sweep integrity; all script numbers; θ_23 key
papers-faithful; PRECISION table defensible; counts verified; repo-wide stale sweep clean;
abstract/§6 consistent; Check-7/8 clean; eight uncontested rows re-derived against part4b.

**Convergence assessment:** not converged at pass 9, but the defect stream narrowed from
"three headline claims false" (round 8) to "one bent field, one carried-over verification
claim, one unaudited dependency" — all three now fixed with the fixes verified by rerun.
The tenth pass tests whether the M1-class (bent inputs) is exhausted.

# Round 10: second convergence test — NOT CONVERGED (2 majors + 2 borderline), all accepted

Trajectory: 4 → 1 → 0 → 1 → 0 → 0 → 0 → 7 → 3 → **2(+2)**. The defect stream has left the
answer key (the reviewer's verdict: bent-input class exhausted there, verified by row-by-row
p-summand checks and perturbation tests) and moved into the verification apparatus and
record-keeping.

| Finding | Disposition | Sweep |
|---|---|---|
| Major 1 — P1–P6 completeness false for the current 36 survivors: {PGL,GPL} and {LPG,LGP} indistinguishable on every probe (none carried P∧G, ~~a reachable class — the papers' worked m_W-absolute candidate~~ **[struck round 11 F1: grading-inconsistent witness — uniform reading gives m_W-abs (T,F,F); P7 stands as a hypothetical corner]**); separability proven by the reviewer's 57,600-row sweep | **Accepted.** P7 (P∧G row) added and run — all six orderings now have distinct probe signatures; completeness re-stated for P1–P7, this run | uniqueness + 13b + T4 line + A58 |
| Major 2 — false record (round-6 class, second occurrence): A57 claimed the round-8 "verified complete" lines were "struck (marked at source)"; git proves neither the A56 line nor this doc's Round-8 paragraph was touched | **Accepted; owned.** Strikes executed now with annotations; the false A57 sentence itself struck-and-annotated, not rewritten; rule tightened — "struck at source" claims must name the file and be grep-verified pre-commit | this doc + A56 + A57 + A58 |
| Major 3 (borderline) — formulation T4 line still carried the demolished round-8 anchoring claim, contradicting row 5b of the same file | **Accepted.** T4 line rewritten to round-9/10 status; addenda ranges 53–58 | formulation |
| Major 4 (borderline) — v1 docstring note "A52's vacuity finding stands" contradicted its own R7 clause | **Accepted.** Note rewritten with lag ownership | v1 |
| m-A/m-B/m-C/m-D/m-E/m-F — unmarked superseded rows in this doc; stale probe labels ("pure second-period"); first_principles fork-grounds lagging P6; vacuity variant count; the untested ℓ_A L-variant (now tested: ~~≈+112σ~~ **[round 11 F2: the computed value is +109σ; "112" was a from-memory estimate written in the record-fidelity round itself]** excluded); header/body contradiction in the paper's precedence remark + addenda ranges | **All accepted.** Swept as named | this doc + scripts + paper + formulation |

**Checked-and-held adopted:** round-9 fixes all in git; M3's papers-reading verified sound
row-by-row (α_s top-level exponential; b/s precedent forces non-expanding G; all dashes
consistent); α_s (5,12) is the papers' literal summand set (part4b:2443) — not a bent field;
number fidelity across all surfaces; σ arithmetic correct; Check-7/8 clean.

**Convergence assessment:** not converged at pass 10. But the character of the findings
changed: zero mathematical defects, zero answer-key defects, zero bent inputs — the majors
are a verification-apparatus gap (fixed with P7, now with a proven-distinct signature set)
and record hygiene (fixed, with the rule tightened after its second failure). Pass 11
tests whether the record-hygiene class is exhausted.

# Round 11: third convergence test — NOT CONVERGED (2 majors + 2 borderline), all accepted

Trajectory: 4 → 1 → 0 → 1 → 0 → 0 → 0 → 7 → 3 → 2(+2) → **2(+2)**. Structural positives
first: no third false execution record (every round-10 strike grep-verified where recorded;
the tightened rule held), and the completeness failure mode is structurally closed (the
reviewer independently re-implemented the check: all 36 survivors pairwise-distinct on
P1–P7; 33,480-row sweep, zero unseparated pairs; the six orderings' signatures verified
pairwise distinct).

| Finding | Disposition | Sweep |
|---|---|---|
| F1 — the P∧G reachability witness was grading-inconsistent (third occurrence of the F4/M3 class, now in the probe-justification layer): part4b:1728 short-circuits m_W-absolute at P=T with its window content inside closed constituents m_Z/v — the m_τ-abs configuration; (T,F,F) on the uniform reading | **Accepted.** Witness struck-and-annotated on record surfaces, corrected in place on script/paper; P7 restated as a well-formed hypothetical corner; nearest uniform-reading P∧G configuration identified (the VEV v, top-level window exponential, dimensionful — but an anchor with no addressed member row); pattern rule added: every "papers' candidate X realizes class Y" appeal must name its grading | uniqueness + 13b + A58 + this doc + A59 |
| F2 — "≈+112σ" in the Round-10 minors row: from-memory number in the record-fidelity round; computed value +109σ (script, A58, commit message all agree) | **Accepted.** Corrected with marker | this doc |
| F3 — the Round-9 M2 cell still asserted "struck at source" unmarked — the exact execution claim round 10 proved false | **Accepted.** Struck-and-annotated; cell preserved as the record of the failure | this doc |
| F4 — seven surfaces desynchronized on the σ range (13–65σ vs the adopted four-variant 13–109σ), one written by round 10 itself; two script outputs disagreed with each other | **Accepted.** All seven reconciled to 13–109σ across the four variant readings | paper (abstract, Thm-8 remark, 13b) + formulation (T4, 5b) + both U2 scripts |
| m1–m5 — A57 "six probes" unmarked; first_principles docstring fork-grounds lag; dangling round-attribution in the uniqueness docstring; stale "(round-8 corrected)" headers; P7's kind field semantically off ("coupling" → "abs-mass", verified inert) | **All accepted.** Swept as named | audit + scripts |

**Checked-and-held adopted:** git integrity for all round-10 fixes; all four scripts
reproduce every documented number; σ arithmetic (65.2/13.0/108.7/33.8) correct; probe
labels correct under the papers' periods; answer key re-spot-checked against part4b
(α_s summand set, θ_23 k=4); kill classifications rerun-stable; repo top-level docs clean;
Check-7/8 clean.

**Convergence assessment:** not converged at pass 11. The record-hygiene class thinned
(strikes now execute faithfully) but produced one from-memory number and one missed
marker; the grading-inconsistency class surfaced a third time, in the justification layer.
Pass 12 tests the named pattern rule and whether either class has further instances.

# Round 12: fourth convergence test — CONVERGED

**Zero majors.** The U2 arc's first convergence; the series' second. Trajectory final:
4 → 1 → 0 → 1 → 0 → 0 → 0 → 7 → 3 → 2(+2) → 2(+2) → **0**.

| Finding | Disposition | Sweep |
|---|---|---|
| Priority attack — round 11's v-witness claim, tested under the A59 pattern rule | **HELD.** part4b `thm:vev` (3325–3328): the window exponential is a top-level factor of the labeled theorem's display; α_GUT is a Tier-1 constant, not a closed observable; the papers' own `source_selection_inventory.py` independently grades m_W-abs (T,F,F). No fourth grading-inconsistency instance | — |
| F-1 (minor) — witness citation misdirected to part4b:83 (window attribution) instead of thm:vev:3325–3328 (the top-level display) on two of four surfaces | **Accepted.** Citations corrected | uniqueness + A59 |
| F-2 (cosmetic) — grammar splice from round 11's own F4 edit ("under A52's the four variant readings") | **Accepted.** Repaired | formulation T4 |
| F-3 (cosmetic) — abstract enumerated three of the four canonical variant readings | **Accepted.** All four named | paper abstract |
| F-4 (cosmetic) — three stale "(round-8/8–10 corrected)" header labels with synchronized bodies | **Accepted.** Updated to rounds 8–11 / Addenda 53–59 | paper 13b + formulation T4/row 6 + first_principles |
| F-5 (observation) — the implicit marking rule (false-when-written → strike anywhere; superseded-true → mark net-state lines only) was consistent but unstated | **Adopted; stated explicitly in A60** | A60 |
| F-6 (observation) — latent seam: the papers' α_s-wrapped v-writing (part4b:3382) would grade v (T,F,F); the witness stands on rem:sp36-syntactic's minimal-descent rule, but no surface argues canonicality | **Recorded in A60** as the pattern rule's next test case if the witness is re-touched | A60 |

**Checked-and-held adopted:** all round-11 fixes in git with every marker grep-verified;
all four scripts reproduce every number; the reviewer's independent re-implementation
reconfirmed 36 distinct P1–P7 signatures; σ arithmetic exact (65.24/13.04/108.71/33.83);
F4 reconciliation complete (no surviving "13–65" outside marked history); sweep-count
attributions all correct (8,640/57,600/33,480); every part4b citation verified at the
cited line; "structurally closed" properly caveated to this survivor set; Check-7/8 clean.

**Convergence statement:** no untrue statement on any current surface; no recorded-but-
unmade fix; no new defect class; no substantive stale surface. What remains open is
mathematics and experiment, not review: the θ_C availability defect, the soft inputs
(Observer k=3, A13 grading, ℓ_A kind), extension to the full ~100-entry record, and the
ledger's falsifiers (JUNO, DESI/CMB-S4, Belle II, HL-LHC, KATRIN).

# Round 13: the commissioned attack on the record-legs rule — WOUNDED, all findings accepted

The rule survives with restated status: core mechanics held (unchanged clauses, genuine
(0,0,0), exact θ_C quote at part4b:3728, fixed-target disclosure genuine, falsifier not
tripped), but the c5dcc2a sweep carried four majors.

| Finding | Disposition | Sweep |
|---|---|---|
| M1 — v1's DISCLOSURES still said "the θ_C defect is open" / "θ_23 and ℓ_A unchecked" against the same file's corrected state; record-legs missing from both scripts' soft-input lists | **Accepted.** Both blocks rewritten; record-legs counted everywhere | v1 + uniqueness |
| M2 — Theorem 13c's tail still called the defect "open" | **Accepted.** Fixed | paper |
| M3 — survivor enumeration "canonical + two duplicates" arithmetically impossible for 6=3×1×2; the cross-generation indicator (a genuine fork) suppressed; the probe section never exercised avail freedom, so P1 printed NO FORK while the Δg=16 discriminator existed | **Accepted.** A61 miscount struck-and-annotated; AVAIL PROBE FORKS section added — P1 now prints the (2,0,0)/(1,0,0) fork; enumeration corrected on all surfaces | uniqueness code + A61 + 13b + formulation |
| M4 — row-dependent, unstated adjudication corpus: θ_C adjudicated on the papers' formula, but m_b/m_τ's proj=1 has no papers witness (Tier-4a "= e"; no cos(π/6) in src/*.tex) — its witness is A19's candidate-lemma, scheme-contingent m_b = m_τ·e·cos(π/6); under a papers-only corpus R3 fails there exactly as the old clauses failed on θ_C | **Accepted.** Corpus conditionality disclosed on every surface: the key keeps the T4/audit value; the R3 projection pinning is conditional on the audit-lemma reading | v1 EXPECT + uniqueness + 13b + formulation + A62 |
| m5 — "papers state these verbatim" covered θ_C only; θ_23 is template-extension inference | **Accepted.** Scoped on all surfaces | v1 + paper + formulation + A61 marker |
| m6 — "generation layers never enter either formula" false at d=13 (Gen-2 = SU(2) layer; the dual identity IS the disputed point) | **Accepted.** Struck in A61; restated everywhere | v1 + paper + A61 |
| m7 — PMNS falsifier underspecified; the repo's standing candidates (N_c in all three formulas) undisclosed | **Accepted.** Falsifier sharpened (availability factors defined; N_c addressed via A14's scheme note; candidates disclosed) | v1 + paper + A62 |
| m8 — "independently carrying (0,0,0)" overclaim (same author, same formula, one store entry + one inference) | **Accepted.** Struck-and-annotated | A61 |
| n9/n10/n11 — citation 3727→3728; classifier added to per-row discretionary content; ℓ_A avail added to key | **Accepted.** Swept | v1 + A61 |

**Attack-A verdict adopted:** the classifier is a new per-row soft input; the angle rows'
availability agreement is near-tautological under record-legs; the non-trivial residue is
the four record-ratio rows' clause-uniformity, the θ_C verbatim quote, and the sharpened
falsifier. **Checked-and-held:** no clause semantics changed in c5dcc2a; all numbers
reproduce; falsifier not tripped (no PMNS closure in the papers; the PMNS₁₂ template
attempt is a recorded negative; CKM θ_13 factor-free); Check-7/8 clean.

# Round 14: convergence test on the round-13 sweep — NOT CONVERGED (1+2), the missed-instance class

Trajectory: … → 0 (r12) → WOUNDED/4 (r13) → **1(+2)**. No false execution record for a
fourth consecutive round; mathematics/computation unchanged. Every finding is a missed
instance of an already-accepted round-13 finding at a site the per-finding sweep list
didn't name.

| Finding | Disposition | Sweep |
|---|---|---|
| M-A — the M1 falsehood at a second site in the same file (v1 EXPECT header: "theta_23 / ell_A availability: no T4 store → unchecked") | **Accepted.** Fixed, with the space-level tautology of the (0,0,0) rows stated in place (n-G) | v1 |
| M-B — the m5 "papers-sourced verbatim" overclaim unscoped in first_principles (not on m5's sweep list) | **Accepted.** Scoped: verbatim θ_C only, inference θ_23; classifier + soft-input status added | first_principles |
| M-C — A61's bolded falsifier registration still the old two-factor form, unmarked; A62's "disclosed on every falsifier surface" false-when-written against it | **Accepted.** Registration struck-and-superseded by the sharpened canonical form (three availability factors + N_c/scheme-equivalence kill condition + decision procedure); A62's claim struck-and-annotated | A61 + A62 |
| m-D — cascade_T4_uniqueness.py (the paper's Thm-13 verifier) six rounds stale: "U2 as a function is the open formal target" | **Accepted.** Updated to the rounds-8–14 state (v1 constructed; absolute forcing unavailable in principle) | T4 script |
| n-E — stale "rounds 8–11"/"round-10" headers across five surfaces | **Accepted.** All updated to rounds 8–14 | v1, uniqueness, first_principles, paper 13b, formulation row 6 |
| n-F — A61's bolded opening "and the papers state it verbatim" unstruck; defence (i) ambiguous | **Accepted.** Struck; defence (i) scoped to θ_C | A61 |
| n-G — the (0,0,0) rows are exactly tautological within the variant space (every legs-clause variant returns (0,0,0) on empty/gauge legs); all six avail kills verified to come from the record-ratio rows | **Adopted.** Stated in place; the 6/100 exhaustion remains informative over exactly the conceded rows | v1 + A63 |
| n-H — the scheme-equivalence kill condition lacked a decision procedure | **Accepted.** Registered: the A14 pole/MS-bar shift computation, hostile-review adjudicated | v1 + A61 marker + A63 |

**Process rule adopted:** sweep lists must be enumerated by whole-repo grep for the
corrected claim's text, not by the surfaces a finding names — the missed-instance class is
exactly what per-finding site lists cannot catch. **Checked-and-held:** all round-13
recorded fixes physically in af524e8 and grep-verified; all scripts reproduce every number;
M4's source claims re-verified (Tier-4a "= e", no cos(π/6) in src/*.tex); the θ_C quote
exact at part4b:3728; 6-survivor enumeration consistent; falsifier not tripped; Check-7/8
clean.

# Round 15: the bridge arc — WOUNDED (3 majors), all accepted; the mathematics held every independent check

The reviewer re-derived the identities by hand, recomputed the root number and L(1)
independently, re-scanned the zeros at 12× finer step, and confirmed every quoted number.
"The bridge arc's mathematics is steel; its claim-layer has three dents of the arc's
chronic type."

| Finding | Disposition | Sweep |
|---|---|---|
| M1 — the Lorentzian zero-sum form silently assumes on-line zeros; "RH/GRH is not used" false of the formula as displayed (off-line discrepancy computed: ~3×10⁻⁵ at a=0.1, γ=10); the paired Hadamard form is the unconditional theorem | **Accepted.** Restated on every surface: paired form = the RH-free theorem; Lorentzian = its on-line evaluation with the verified zeros (off-line contribution < 10⁻²³ here) | both theorems + T1b/T1c + A64 markers + three docstrings |
| M2 — the d=12 prime-side PASS was an epsilon artifact (residual 4.81e-35 > bound 1.56e-40 at the dps-30 floor); reviewer's dps-60 recomputation: true residual 2.05e-41, genuinely within bound | **Accepted.** V2 now runs dps 50, strict bound, no epsilon — honest PASS earned; false-when-written claims struck (A64) or corrected (paper, formulation) | bridge script + Thm 1b + T1b + A64 |
| M3 — "forced minimality": the selection-convention disease, fourth appearance. The odd bridge holds for EVERY odd real primitive χ; the balance point is character-independent (zero selectivity); only the minimality convention names χ₋₃ the partner | **Accepted.** "Forced partner" language struck/restated everywhere; the pairing charged as a motivated convention of the residue's selection-convention class; the family form of the bridge stated | colour script + Thm 1c + T1c + F6 update + A65 markers + A66 |
| m1 — Door-1 docstring retained the "decreasing" overclaim A65 claimed was fixed (fix had reached READING only) | **Accepted.** Corrected; A65 sentence annotated | zero_side + A65 |
| m2 — "only primitive character of conductor ≤ 3" false (trivial character mod 1 is conventionally primitive, but even) | **Accepted.** Restated as minimal-conductor primitive ODD character everywhere | all surfaces |
| m3 — "real on the line to 10⁻²⁵" overstated 3× (actual 3.0×10⁻²⁵) | **Accepted.** Corrected | Thm 1c + A65 |
| m4 — both pole terms attributed to ζ's pole; 1/s is the completed function's mirror pole at s=0 | **Accepted.** Corrected on all surfaces incl. both READING prints | scripts + Thm 1b + A64 |
| m5 — tail-integral half-neighborhood seam at the N-th zero | **Noted** (inside the disclosed oscillatory error) | — |
| m6 — formulation T1c lacked the explicit no-direction disclaimer | **Accepted.** Added | T1c |

**Checked-and-held adopted:** rearrangement, no-constant claim (paired form), Legendre,
odd completed normalization, trivial zeros, root number τ(χ₋₃)=i√3 ⇒ ε=+1, L(1) vs
class-number formula, density tails' main terms, zero-scan completeness vs N(T), first
ordinate 8.03974, all doc numbers verbatim, D-consistency of 5.2569/6.2569/7.2569,
stopping rule (zero data contact), Check-7/8 clean, no stale surfaces repo-wide.

**Convergence note:** all three majors are restatement-repairs; no result was lost. The
chronic lesson at its fourth instance is now a named rule: every "forced" must name what
forces it — a selection principle is never free.

# Round 16: convergence test on the round-15 sweep — NOT CONVERGED (2+1), the missed-instance class again

Zero mathematical defects, zero false numbers; the failure is process, named exactly:
"round 15's sweep repeated the round-13 sweep's failure mode one round after the
countermeasure for it was named."

| Finding | Disposition | Sweep |
|---|---|---|
| F1 — "FORCED minimality" survived in the colour script's HONEST SCOPE docstring + printed output, contradicting the same file's restated C2 (M3's sweep column named this file) | **Accepted.** Both fixed; comment header too | colour script |
| F2 — M1's own condemned sentence ("the identity holds wherever the zeros are") survived unqualified in the bridge DOES-NOT block below the docstring claiming it "corrected here"; hybrid "paired Lorentzian form" re-conflated the forms | **Accepted.** Restated; both scripts' READING prints now qualified | bridge + colour scripts |
| F3 — A65's closing sentence: unqualified "no RH/GRH use" + a second unannotated "caught and fixed pre-commit" | **Accepted.** Both struck-and-annotated | A65 |
| F4 — m4 pole-attribution missed Thm 1c(i) and two A65 sentences | **Accepted.** Both poles named everywhere | paper + A65 |
| F5 — the "< 10⁻²³" bound true at s ≤ 29, crosses at z ≈ 45, ~5–7×10⁻²³ at the sink solve | **Accepted.** Scoped on all three surfaces (still ~20 orders below the sink's tail-model error) | bridge + zero_side + Thm 1b |
| F6 — colour V2 kept the epsilon-slack pattern M2 charged (inert: residuals 2–4 orders inside bounds) | **Accepted.** Epsilon removed; strict bound passes | colour script |
| F7 — dead `prev = err` | **Accepted.** Removed | zero_side |
| F8 — residue accounting: consistent as a widening on all six surfaces; abstract under-described the class | **Accepted (cosmetic).** Abstract parenthetical now names the class's three members | paper abstract |

**Checked-and-held adopted:** all round-15 hunks in git; strike-markers quote their
targets verbatim; M2's fix earned (dps-50 strict, d=12 residual 2.05e-41 within 1.56e-40;
the reviewer independently reproduced the OLD dps-30 residual 4.81e-35 — A66 carries no
from-memory numbers); the restatements' mathematics independently verified (genus-0,
Legendre, odd rearrangement, ε=+1 for every odd real primitive χ, character enumeration,
pole attribution, D-consistency); every quoted number matches output; untouched scripts
verified untouched; stopping rule and Checks 7/8 clean.

**Process rule, tightened at its third failure:** a sweep is complete only when the A63
whole-repo-grep battery for every corrected phrase has been RUN and its results RECORDED
in the round's addendum (A67 records this round's battery). Round 17 tests whether a
battery-gated sweep finally converges.

# Round 17: convergence test on the battery-gated sweep — CONVERGED

**Zero majors. The bridge arc's first clean convergence; the series' third (rounds 7, 12,
17). Bridge-arc trajectory: 3 → 2(+1) → 0.** The reviewer independently reran the A67
battery (all round-15/16 phrase classes + six rounds-8–14 spot-checks): **zero live
survivors — A67's execution record is TRUE**; no third false record. All round-16 fixes
verified in git; all script outputs match every surface digit-for-digit; the F5 arithmetic
verified exactly (including deriving the ~7×10⁻²³ upper end from the solve bracket);
the abstract's "review 4" attribution verified through the Thm-7 amendment; Checks 7/8 and
the stopping rule clean.

| Finding | Disposition | Sweep |
|---|---|---|
| c1 (cosmetic) — "both scripts' READING prints": the colour script's qualified print lives under HONEST SCOPE | **Accepted.** Block name corrected in the records | A67 record + this doc |
| c2 (cosmetic) — loose plural "ζ's poles" on three surfaces (not the m4-charged singular, but loose against the program's own convention) | **Accepted.** Both poles' owners named | paper + audit + colour script |
| c3 (cosmetic) — A67's recorded battery omitted round 16's own native phrases (independent greps confirm zero live survivors of those too) | **Accepted.** Rule amended: each round's battery must include that round's native phrases; A68 records this round's | A68 |
| c4 (cosmetic) — two historical disposition cells retain the unscoped "< 10⁻²³" (true in context; no annotation owed) | **Noted** | — |

**Convergence statement:** no untrue statement on any current surface; no fix
recorded-but-not-made; no false battery record; no new defect. What remains open is
mathematics and experiment: the dictionary's soft inputs, the full-record extension, F6's
original claim, and the ledger's falsifiers.

# Round 18: hostile pass on the finite-place arc (Doors 3&4 + local Tate) — WOUNDED (2+6), zero mathematical falsehoods

First adversarial pass on the two newest commits (c781ec9, 345f861); the rounds-15–17
material held its convergence. All eight findings are claims-layer — quantifier scope,
verification coverage, counting, grading — the tenth consecutive round in which the
mathematics itself produced no defect. The reviewer's independent checks all held: the
global identity re-run, Landsberg–Schaar brute-forced at **1000 pairs (zero
failures)**, Gauss phases confirmed at composite and non-power moduli, Br(ℚ₂) = ℚ/ℤ,
level(ℚ₂) = 4, the odd global identity at 10⁻²⁰.

| Finding | Disposition | Sweep |
|---|---|---|
| M1 — Gauss-phase verification narrower than claimed: "every odd modulus (to q = 499)" ran primes-only; "every 4-divisible modulus (q = 4–64)" ran powers-of-2-only | **Accepted.** Verifier extended: 16 composite odd moduli to 495, 11 non-power 4-divisible to 180, all PASS; extension disclosed on all surfaces | script + paper + T1d + A69 struck |
| M2 — "~99% at the record's layers" was s = 6-only; at s = 4 the joint p = 2, 3 share is 94.15% | **Accepted.** Shares now computed/printed at s = 4, 5, 6, 13, 21 (94.15/97.62/99.04/100/100%); all surfaces say "~94–100% across the record's layers" | script + paper + T1d + A69 struck |
| m1 — "10⁻³¹" understated the worst residual 1.97×10⁻³¹ | **Accepted.** "2×10⁻³¹" on all five surfaces (incl. A64/A69 strikes) | paper + formulation + audit |
| m2 — "three independent corroborations" counted one theorem twice (T-loc3's sum = conj G(4q)/2 = D3.2's phase statement) | **Accepted.** Count corrected to two ~~everywhere~~ **[FALSE RECORD, caught by round 19 (F1): four variant instances — "three corroborations", "corroborated independently by D3.2 … and T-loc3", "corroborations: D3.2, T-loc3" — were live in `cascade_local_tate.py` itself; the sweep column never included the script]** | paper + T1e + A70 struck + script (round 19) |
| m3 — the Witt ring W(ℚ₂) left unnamed while "the most obvious route" was declared closed | **Accepted — the reviewer's gift.** W(ℚ₂) order 32 ≅ ℤ/8⊕ℤ/2⊕ℤ/2, level = 4 verified in-code, ⟨1⟩ of order 8: named on all surfaces as the OPEN clock-corroborating route | script T-loc5 + paper + T1e + A70 |
| m4 — "the two structure primes' roles are now exact" blanket-graded a mixed list | **Accepted.** Split: exact (3 ramifies/silences; 2 inert) vs identification ("2 carries the clock") | script + paper + T1e + A70 struck |
| m5 — comb-DFT self-duality at fixed depth is near-tautological | **Accepted.** Honesty note in T-loc1: the content is the Tate-integral achievement + depth consistency | script |
| m6 — LS grid odd-p-only, structurally blind to a parity restriction | **Accepted.** 18-pair grid incl. even p + both parities; review's 1000-pair sweep recorded | script + paper + T1d + A69 |

**Process finding:** both majors and m1 share one failure mode — a battery that checked
values but not quantifier scope. A69's gate line "all quoted percentages/residuals match
script output ✓" is struck as a FALSE RECORD (the phrases matched the runs that existed,
not the claims as quantified). Battery rule extended: every "verified to X"/"at the
record's layers"/"every modulus" claim must have its *quantifier* checked against the
verifier's actual input list. A71 records this round's battery: zero live survivors of
the round-18-native phrases; scripts re-run clean post-sweep.

# Round 19: convergence test on the round-18 sweep — NOT CONVERGED (1+4), the missed-instance disease's fourth appearance

Zero mathematical falsehoods (eleventh consecutive round). The failure is the exact
class round 16 named and round 18 repeated: the sweep corrected every surface *except
the file it was editing*, and the battery certified the exact string while the claim
class survived.

| Finding | Disposition | Sweep |
|---|---|---|
| F1 — m2's fix absent from `cascade_local_tate.py` itself: four live variants ("three corroborations", "corroborated independently by D3.2 … and T-loc3", "corroborations: D3.2, T-loc3", READING "three corroborations") + an m4 variant ("roles are fixed (2 inert + clock)" ungraded); the Round-18 m2 cell ("everywhere") and A71's "all surfaces corrected" were false records | **Accepted.** All five instances fixed; both false records struck at source; script re-run clean | script + Round-18 table + A71 |
| f2 (cosmetic) — "primes and composites to q = 499" endpoint-ambiguous (composites reach 495; powers of 2 reach 64 vs "to 180") | **Accepted.** Per-class endpoints on all three surfaces | paper + T1d + A69 |
| f3 (cosmetic) — "1000 *random* pairs" embellished the round-18 record (no randomness was recorded) | **Accepted.** "random" dropped on both surfaces | A71 + Round-18 table |
| f4 (cosmetic) — level(ℚ₂) = 4 positive direction is a mod-2⁶ witness needing the Hensel lift named (63 = 7²+3²+2²+1², unit coordinates); negative direction conclusive as run | **Accepted.** Split named in script + paper | script + paper |
| f5 (cosmetic) — A71's "the A66 rule's own statement" singular; both scripts carry one | **Accepted.** Pluralized | A71 |

**Process rule tightened (fourth appearance: rounds 13, 15/16, 18→19):** sweep target
lists must include the files being edited for sibling findings; batteries must grep
claim-class stems, not exact strings — an exact-string battery can be literally TRUE
while the claim survives, which is worse than a false record because it certifies
convergence. A72 records this round's stem-based battery: clean. **[Net-state marker,
round 21 c3: A72's battery record — accurately cited here as what A72 records — was
itself struck in round 20 (F1) as overstating its coverage; see the Round 20 table.]**

**Round 20 is owed before the arc is declared stable; Witt queues behind it.**

# Round 20: convergence test on the round-19 sweep — NOT CONVERGED (0+1), the false-record class goes meta

Zero majors, zero cosmetics, zero mathematical falsehoods (twelfth consecutive round).
Severity strictly decreasing across the arc: 2+6 → 1+4 → 0+1. Every round-19 fix
verified in the diff hunks; every round-19 numerical claim re-derived (list counts and
endpoints 10/16/5/11 at 499/495/64/180; the Hensel witness with its lifting condition
v₂(f) = 6 > 2·v₂(f′) = 2; the 18-pair grid's parity claims; the "fourth appearance"
count against round 16's own convention; "eleventh consecutive round").

| Finding | Disposition | Sweep |
|---|---|---|
| F1 — A72's battery record false as quantified: "'corroborat' repo-wide" was a four-file grep, and a genuine repo-wide run surfaces two live hits outside the stated trichotomy (both benign pre-existing audit usages). No battery target was defective — the record overstated the battery's own coverage | **Accepted.** Struck at source in A72 with the two extra hits named; A73's battery states its actual command scope | A72 |

**Process rule (the class's terminal form):** a battery record states the command's
actual scope — record what ran; "repo-wide" may be written only after a repo-wide
command produced the classified hit list being recorded. The verified-record rule now
covers the batteries themselves.

**Round 21 tests whether the battery-scope rule closes the class; Witt stays queued.**

# Round 21: convergence test on the round-20 sweep — CONVERGED (0+0, three cosmetics)

Zero majors, zero minors, zero mathematical falsehoods (thirteenth consecutive round).
The arc's fourth convergence (rounds 7, 12, 17, 21). Round 20's lens was turned on its
own records: A73's run-claims, its classification method, and strike-propagation.

| Finding | Disposition | Sweep |
|---|---|---|
| c1 (cosmetic) — A73's "lifting condition … checked explicitly": the round-20 display hardcoded the inequality as a literal `True` (witness sum and mod-64 computed; v₂(f′) asserted in prose) | **Accepted.** Every component recomputed genuinely (v₂(64) = 6, v₂(14) = 1, comparison computed — assertion correct, record loose); annotated at source | A73 |
| c2 (cosmetic) — round 20's "corroborat" classification used exclusion filters rather than per-hit inspection | **Accepted.** Unfiltered census run: 44 md/py hits classified per-hit, zero live defective usages, sums verified; 2 benign `.tex` hits (outside the stated scope) inspected too | A74 |
| c3 (cosmetic) — the Round-19 table's "A72 records this round's stem-based battery: clean" cited a record round 20 then struck (superseded-true, marker owed) | **Accepted.** Net-state marker added | Round-19 table |

**Convergence statement:** no untrue statement on any current surface; no fix
recorded-but-not-made; no unstruck false record; the battery-scope rule held on its
first test. The finite-place arc (Theorems 1d–1e, Addenda 69–74) is stable.

**The Witt-ring work item is unblocked.**

# Round 22: first adversarial pass on the Witt step — 0 majors, 3 minors, 1 cosmetic; the attack found a strengthening

Zero mathematical falsehoods (fourteenth consecutive round). Every charge was tested
empirically before acceptance — and testing F2's charge turned it into a theorem.

| Finding | Disposition | Sweep |
|---|---|---|
| F1 (minor) — W3's ten-class list was odd-valuation-only at the odd places: the silence claims ("γ_p = 1 at even valuation / unramified"), on which the product loop's place-selection silently relied, were never exercised in-code | **Accepted.** Tested first: all silences true at 10⁻¹⁶. List extended to fifteen classes (±9, 45, −18, 25); silence gates + odd-p k-stability gates added; 27 PASS 0 FAIL | script + paper + T1f + A75 struck |
| F2 (minor→strengthening) — "canonical quotient" outran the recorded ψ-covariance (the kernel moves in its scaling orbit under ψ → ψ_a) | **Accepted, and upgraded.** The repair is a theorem: all eight class values are primitive (in-code gate), so γ_ψₐ(⟨1⟩) is primitive for every character — "surjection with ⟨1⟩ a generator" is character-free. "Canonical" now defined as exactly the ψ-independent structure on every surface | script + paper + T1f + A75 |
| F3 (minor, m1 class) — "verified at 10⁻¹⁵–10⁻¹⁶" mislabeled both ends of the run (best 8.7×10⁻¹⁷, worst 2.1×10⁻¹⁵); formulation's "at 10⁻¹⁵" understated | **Accepted.** All surfaces now "≤ 2.3×10⁻¹⁵" over the extended run; A75 range struck | paper + T1f + A75 |
| c1 (cosmetic) — A74's "Next: the finite-place derivation attempt…" reads as pending | **Accepted.** Net-state marker added | A74 (via A76) |

**Checked and held:** the quotient theorem's logic (descent, kernel order 4), the
k-parity handling, the Fresnel tail algebra, the W5 grid, A75's per-hit battery
classification and its pre-commit PASS-count correction, Checks 7/8, the stopping rule.

**Round 23 (convergence test on this sweep) is owed before the Witt step is declared
stable. The honest negative for N_c stands unweakened.**

# Round 23: convergence test on the round-22 sweep — NOT CONVERGED (0+1), the false-record class's filter variant

Zero majors, zero cosmetics, zero mathematical falsehoods (fifteenth consecutive
round). Witt-step trajectory: 0+3(+1c) → 0+1. The Witt step's mathematics has survived
two adversarial rounds untouched; the single defect is again an instrument record.

| Finding | Disposition | Sweep |
|---|---|---|
| F1 — A76's "canonical" battery line omitted the content filter the command actually carried (`quotient\|witt\|clock`) and asserted "the sole other hit" — false by two orders of magnitude against the unfiltered census (152 hits, 39 files, ordinary repo vocabulary). No target was defective: the round-23 unfiltered per-hit sweep confirms zero live ungraded Witt-quotient claims; 1e's "canonical achieving vector" and T6's twist-tower "canonical ℤ/8" are different, earlier senses | **Accepted.** Struck at source with the true census; filter clause added to the round-20 battery-scope rule (full command incl. every filter; "sole/only/zero-other" quantifiers require the unfiltered census on file) | A76 |

**Everything else checked and held:** all round-22 edits in the diff and consistent;
the ≤ 2.3×10⁻¹⁵ quotes vs actual worst 2.2×10⁻¹⁵; A76's other battery lines ran
unfiltered and hold; PASS counts verified (27/6/10); Checks 7/8, stopping rule clean.

**Round 24 tests the filter clause.**

# Round 24: convergence test on the round-23 sweep — CONVERGED (0+0, one cosmetic); the Witt step is stable

Zero majors, zero minors, zero mathematical falsehoods (sixteenth consecutive round).
The series' fifth convergence (rounds 7, 12, 17, 21, 24). Witt-step trajectory:
0+3(+1c) → 0+1 → 0+0(+1c).

| Finding | Disposition | Sweep |
|---|---|---|
| c1 (cosmetic) — A77 said the 152-hit census was "classified per-hit"; round 23's method was categorical (file-level census + a per-hit read of the 14 arc-complement lines; ~138 hits unread individually). Every recorded fact was true; the adverb overstated the method | **Accepted.** Round 24 performed the genuine per-hit read of all 152 lines — conclusion confirmed unchanged (zero live ungraded Witt-quotient claims). Both instances annotated (A77's battery line and its F1 narrative — the second caught by A78's own battery pre-commit) | A77 |

**Process rule (the granularity clause):** granularity adverbs ("per-hit," "each,"
"explicitly," "individually") only when the per-item examination occurred; otherwise
record the categorical method. With the scope clause (r20) and filter clause (r23), the
battery record is now constrained to be a faithful run record in scope, command, and
granularity.

**Convergence statement:** no untrue statement on any current surface; no
recorded-but-not-made fix; no unstruck false record. **The Witt step (Theorem 1f) is
stable** — its mathematics survived three adversarial rounds untouched, strengthened
once (round-22 F2). The finite-place arc (Theorems 1d–1f) stands converged. What
remains open is not review-able by another round: the Adams count and layer selection
(archimedean, papers-side), the dictionary's soft inputs, F6's original claim, the
full-record extension, and the frozen experimental ledger.
