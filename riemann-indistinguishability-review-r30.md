# External review of `riemann-indistinguishability.md` — the data-currency pass

**Reviewed:** `riemann-indistinguishability.md` at commit `83aa59f` (branch
`claude/cascade-series-review-1axe9q`, "Addendum 88"), read end to end (lines 1–816).
**Review date:** 2026-07-21. **Protocol:** CLAUDE.md Checks 0–8, all active.

**Coverage report (Check 0).** Full read: `riemann-indistinguishability.md` 1–816.
Targeted direct reads (Check 1/Check 2 verifications, cited in place below):
`riemann-indistinguishability-review-response.md` 1–80 plus the full round index
(rounds 1–29) and topic sweeps; `cascade-surprisal-audit.md` A61–62, A83–88 regions plus
repo-wide topic greps; `src/cascade-series-part4b.tex` 3725–3730; `PREDICTIONS.md`
Tier-5 region. Verifier scripts executed from the reviewed commit's tree: 17 scripts
(listed in §V below), all passing, zero FAIL lines.

**Disposition summary.** The mathematics held every check I ran, including independent
re-derivation outside the repo's own code. The novel findings are **observational, not
mathematical**: the paper's §8/§9 record is computed against a data snapshot that has
since been superseded at two points — one of which (JUNO) is a §9 *judge that has now
begun ruling*, with its first central value placing the framework's prediction outside
its own declared kill window. Plus one presentational finding (a new instance of the
already-accepted P3F5 class).

---

## I. What was verified and held (the steel)

1. **Independent re-derivation of the tower's features and windows** (mpmath, dps 30,
   no repo code): critical point s = 7.256946…, threshold s = 20.730775…
   (p = ln Γ(½)), sink s = 218.6267… (p = Γ(½)), sgn-tower crossing s = 6.256946…,
   volume maximum d = 5.256946…, and the Theorem-1b window totals
   Φ(5→13) = 1.53966514… and Φ(13→21) = 4.06476812… — all match the paper's quoted
   values exactly, under the (a, b] window convention the sums confirm.
2. **The verifier battery runs clean.** From the reviewed commit's tree:
   `cascade_formulation_kernel`, `cascade_arithmetic_increment`, `_period`, `_sign`,
   `_s5`, `cascade_explicit_formula_bridge`, `cascade_finite_places`,
   `cascade_colour_field_bridge`, `cascade_local_tate`, `cascade_witt_weil`,
   `cascade_local_family`, `cascade_zero_side_features`, `cascade_adams_loadbearing`,
   `cascade_layer_selection`, `cascade_T4_uniqueness`, `cascade_measurement_joint`,
   `cascade_activation_mechanism`, `cascade_precedence_vacuity`, `cascade_ds_audit` —
   all pass; zero FAIL/ERROR lines. Notably, the scripts' *printed verdicts carry the
   same demotions and hedges as the paper text* — the print-drift disease of rounds
   4–6 did not recur at any surface I sampled.
3. **Classical inputs spot-checked by hand:** the Radon–Hurwitz table (ρ at
   d = 8, 12, 13, 14, 16 and the window column); |W(ℚ₂)| = 32 ≅ ℤ/8 ⊕ (ℤ/2)² with
   level 4 and |W(ℚ_p)| = 16 with exponent 2·level (Lam); the Gauss-phase
   classification ({1, i} at odd moduli, ζ₈ at 4-divisible); L(1, χ₋₃) = π/(3√3) and
   the first ordinate 8.0397; Legendre Γ_ℝ(s)Γ_ℝ(s+1) = Γ_ℂ(s). All correct as
   stated.
4. **Check-2 verification of the load-bearing quote:** part4b:3727 does read *"A
   mixing-matrix element measures the overlap of two states, one from each gauge
   layer"* — the record-legs rule's θ_C warrant is quoted faithfully.
5. **The RH-scope discipline of Theorem 1b/1c** (paired Hadamard form unconditional;
   Lorentzian form an on-line specialization with the off-line contribution bounded
   below 10⁻²³ at the evaluated layers) is correctly stated.

No logical-gap claims are raised in this review (Checks 1, 5: none survived direct
reading — every candidate I chased was already carried, with citation, in the paper's
own hedges).

---

## II. Finding 1 (MAJOR, observational; Check 4: category (b), novel — no mention
anywhere in the repo). **The ledger's first judge has ruled, and the row does not
know it.**

The §9 ledger row

> | Δm²₂₁ | 7.572×10⁻⁵ eV² | JUNO (~0.3%) | outside ~0.6% window kills Mechanism M |

treats JUNO as a future judge. JUNO published its first reactor-oscillation
measurement in November 2025 (arXiv:2511.14593, 59.1 days of data):

**Δm²₂₁ = (7.50 ± 0.12) × 10⁻⁵ eV²** — already 1.6× more precise than all previous
experiments combined, i.e. more precise than the PDG value the §8 row's "+0.24σ" is
computed against.

Consequences, computed:

- Against JUNO alone, the framework's 7.572×10⁻⁵ sits at **+0.60σ** — alive on the
  σ-metric. The §8 row should read +0.60σ (JUNO 2025), not +0.24σ (pre-JUNO PDG).
- On the central value, 7.572/7.50 = **+0.96%**. The declared kill window is ±0.6%:
  around JUNO's central value that window is (7.455–7.545)×10⁻⁵, and **7.572 is
  outside it**. The row survives today only because JUNO's current error (1.6%) is
  still wide. If the central value holds as JUNO approaches its design ~0.3%, the
  deviation lands at ≈ 3.2σ and the row dies — killing Mechanism M and with it the
  E = 3π² composite.
- This is exactly the situation the Σm_ν row already handles with its "standing
  tension, not future" clause (the ACT+DESI 52–57 meV squeeze, audit A29). The
  Δm²₂₁ row needs the same clause: *the judge has begun ruling, and the first ruling
  points at the kill window.*
- Cross-sector remark: the three neutrino-sector strains now on record — m_ν3 at
  −2.9σ (NuFit 6.0, acknowledged), Σm_ν against the 52–57 meV squeeze
  (acknowledged), and Δm²₂₁ vs JUNO (this finding) — all have the framework's
  central value **high** relative to the data's drift. Under the paper's own
  standard ("quantitative deviations are real"), a correlated one-sided strain
  across one sector is the falsification front, and §9 is where it should be
  visible.

**Required action:** update the §8 row's reference measurement, add the standing-
tension clause to the §9 row, and record the kill-window arithmetic. No derivation
changes; the stopping rule (§10.4) is untouched — this is ledger maintenance, which
the ledger's own function requires.

---

## III. Finding 2 (MODERATE, data currency; category (b), novel — no instance of
1776.93 anywhere in the repo). **The τ rows are computed against a superseded world
average, and one script mislabels its vintage.**

The current world average is **m_τ = 1776.93 ± 0.09 MeV** (PDG 2024, incorporating
Belle II's 1777.09 ± 0.14 MeV, the most precise single measurement). Every anchor in
the repo uses the previous average 1776.86 ± 0.12 — and `cascade_leptons.py:77`
labels that value "PDG 2024", which it is not.

Consequences, computed:

- **m_τ absolute:** 1776.82 MeV moves from the quoted −0.31σ to
  (1776.82 − 1776.93)/0.09 = **−1.22σ**. Still within tolerance, but no longer
  sub-σ: on current data this is the record's second-largest experimental-error
  strain after m_ν3, and the abstract's strain list ("largest strain ℓ_A at −1.8σ")
  silently gains a −1.2σ member.
- **m_τ/m_μ:** 16.8173 moves from +0.24σ to ≈ **−0.45σ** (observed ratio
  16.81768 ± 0.00085). Sign flip; still sub-σ.
- **The §9 fork sharpens against the paper:** the m_τ row's Belle II fork
  adjudication is no longer neutral — the current data (Belle II high, world average
  pulled up to 1776.93) trends *away* from 1776.82. Worth stating in the row.
- Counter-instance, for fairness: the same staleness runs the other way at m_H —
  against the current 125.20 ± 0.11 GeV the quoted −0.35σ (vs the older
  125.25 ± 0.17) improves to −0.09σ. The vintage problem is directionally neutral;
  the defect is that §8 is a **mixed-vintage snapshot presented as "current world
  data"** with no cut date.

**Required action:** re-anchor the τ rows (and the `cascade_leptons.py` label),
re-run the affected verifiers, and stamp §8 with an explicit data-vintage date so
"every current measurement" is a checkable claim rather than a drifting one.

---

## IV. Finding 3 (MINOR, presentational; a new instance of the accepted P3F5 class —
abstract clause vs its own record). **The abstract's definite-article output list
overstates the §8 record.**

The abstract asserts the outputs include "the mixing angles" and "the cosmological
parameters." The §8 table — which the paper itself declares is "the content of the
word 'indistinguishable'" — contains **exactly two** mixing angles (θ_C, θ₂₃) and
**exactly four** cosmological rows (ρ_Λ, w, Ω_m, ℓ_A). The PMNS angles θ₁₂, θ₁₃ and
δ_CP are not outputs — the paper's own sharpened falsifier (Theorem 13 tail) holds
the standing PMNS candidates *unpromoted*, and PREDICTIONS.md Tier 5 concedes the
mixing-derivation gap; H₀, n_s, τ, σ₈ appear nowhere in this self-contained
document. Since the document forbids itself the companion series' results, its
abstract cannot borrow the series' wider record. Fix: replace the definite articles
with the counts ("two mixing angles", "four cosmological parameters"), matching the
precision discipline the abstract already applies to the fermion masses ("all nine
charged-fermion and three neutrino masses" — which I checked: nine charged rows
present; the three neutrino masses are jointly determined by the m_ν3, Δm²_sol, and
Σm_ν outputs, so that clause is sound).

---

## V. Observations, category (a) — acknowledged elsewhere; noted, not findings

1. **The seven-item residue headline vs the per-row soft-input list.** The abstract
   counts seven non-arithmetic items; the per-row soft inputs (Observer k = 3, the
   A13 content grading, the ℓ_A kind, the record-legs classifier, the 13b withheld
   axis) are carried under C1/Definition 6.1 rather than the headline count. This
   accounting is disclosed (§6 states ~100 entries; §7 states the soft-input list;
   audit line 2747 carries it as open), so it is category (a) — but a reader who
   stops at the abstract will undercount the conditionality. A one-clause pointer in
   the abstract ("plus the per-row soft inputs disclosed in §7, all discrete") would
   close the surface.
2. **Self-containment residue:** three part4b: line citations remain in §7 (630,
   708, 711) as warrants for soft inputs. Consistent with the A84 correspondence
   standard since they are instantiation-side, not theorem imports; noted for
   completeness.

---

## VI. Verdict

At every point I could test, the mathematics is what the paper says it is — including
the parts the paper says are conventions, which is the harder half of that sentence.
The verification suite passes, the internal numbers reproduce independently to stated
precision, the quoted sources are quoted faithfully, and 29 rounds of hostile review
have left the text's hedging in genuine sync with its code. What has drifted is the
**world**: the record is a pre-JUNO, pre-PDG24 snapshot, and the framework's own §9
machinery — the only bias-immune instrument it claims — is exactly where that drift
must be recorded. The sharpest sentence this review can write is the one the paper's
design demands: **JUNO's first central value places Δm²₂₁ = 7.572×10⁻⁵ outside the
framework's own ±0.6% kill window, at a precision not yet sufficient to convict.**
The framework said it is defined by its executioners. The first one has taken the
stand.

*Data sources for §II–III: JUNO collaboration, "First measurement of reactor
neutrino oscillations at JUNO," arXiv:2511.14593 (Δm²₂₁ = (7.50 ± 0.12)×10⁻⁵ eV²,
59.1 days); PDG 2024 world average m_τ = 1776.93 ± 0.09 MeV; Belle II
m_τ = 1777.09 ± 0.14 MeV (arXiv:2305.19116).*
