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
| M2 — "verified complete by the 8,640-row sweep" carried over from the old 72-survivor set; provably false for the corrected 36 (no probe separated canonical-G from "points count too") | **Accepted.** Probe P6 (point in the band) added and run — splits R5 three ways; "verified complete" struck at source | uniqueness + 13b + A56/A57 |
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
| Major 1 — P1–P6 completeness false for the current 36 survivors: {PGL,GPL} and {LPG,LGP} indistinguishable on every probe (none carried P∧G, a reachable class — the papers' worked m_W-absolute candidate); separability proven by the reviewer's 57,600-row sweep | **Accepted.** P7 (P∧G row) added and run — all six orderings now have distinct probe signatures; completeness re-stated for P1–P7, this run | uniqueness + 13b + T4 line + A58 |
| Major 2 — false record (round-6 class, second occurrence): A57 claimed the round-8 "verified complete" lines were "struck (marked at source)"; git proves neither the A56 line nor this doc's Round-8 paragraph was touched | **Accepted; owned.** Strikes executed now with annotations; the false A57 sentence itself struck-and-annotated, not rewritten; rule tightened — "struck at source" claims must name the file and be grep-verified pre-commit | this doc + A56 + A57 + A58 |
| Major 3 (borderline) — formulation T4 line still carried the demolished round-8 anchoring claim, contradicting row 5b of the same file | **Accepted.** T4 line rewritten to round-9/10 status; addenda ranges 53–58 | formulation |
| Major 4 (borderline) — v1 docstring note "A52's vacuity finding stands" contradicted its own R7 clause | **Accepted.** Note rewritten with lag ownership | v1 |
| m-A/m-B/m-C/m-D/m-E/m-F — unmarked superseded rows in this doc; stale probe labels ("pure second-period"); first_principles fork-grounds lagging P6; vacuity variant count; the untested ℓ_A L-variant (now tested: ≈+112σ excluded); header/body contradiction in the paper's precedence remark + addenda ranges | **All accepted.** Swept as named | this doc + scripts + paper + formulation |

**Checked-and-held adopted:** round-9 fixes all in git; M3's papers-reading verified sound
row-by-row (α_s top-level exponential; b/s precedent forces non-expanding G; all dashes
consistent); α_s (5,12) is the papers' literal summand set (part4b:2443) — not a bent field;
number fidelity across all surfaces; σ arithmetic correct; Check-7/8 clean.

**Convergence assessment:** not converged at pass 10. But the character of the findings
changed: zero mathematical defects, zero answer-key defects, zero bent inputs — the majors
are a verification-apparatus gap (fixed with P7, now with a proven-distinct signature set)
and record hygiene (fixed, with the rule tightened after its second failure). Pass 11
tests whether the record-hygiene class is exhausted.
