# Cascade Surprisal Audit — an adversarial null model for the numerical closures

**Tool:** `tools/research/cascade_null_model_surprisal.py`
**Question answered:** For each class of numerical agreement the cascade claims, how many bits of
surprisal survive once you account for (i) the size of the expression space the cascade's own
grammar makes available, and (ii) the number of places a match was looked for?

Surprisal is measured in bits: a claimed match carries `bits = −log₂ P`, where `P` is the
probability that a null model — random targets, or random assignment of shifts — would produce an
agreement at least as good. 0 bits means "expected by chance"; 10 bits means "one-in-a-thousand
under the null."

This audit is deliberately adversarial. It is scoped to the *numerical* closures (the
Gamma-function matches); it says nothing about the structural results (Lovelock, Gleason, Bott,
Adams, hairy-ball), which are theorems and are not probabilistic claims.

---

## Method

**Expression grammar.** The pool is built from the cascade's own primitives — the atoms are small
integers and their square roots, π, √π, e, and the cascade functions R(d), N(d) = √π·R(d),
α(d) = R(d)²/4, Ω(d), p(d), and exp(Φ(a..b)) evaluated at the cascade's distinguished dimensions.
Complexity C counts atom slots; each slot may carry an exponent in {−2, −1, 1, 2}. The C≤2 pool
holds 31,355 unique values; the C≤3 pool holds 2,253,647.

**Calibration.** 2,000 pseudo-targets drawn log-uniform in [0.5, 250] establish the false-positive
baseline: how close does the *nearest* pool expression get to a number that means nothing?

**Look-elsewhere.** Where the cascade selected a formula from a family (correction terms, span
choices, prefactors), the null enumerates the family and asks how likely *some* member was to land.

---

## Results

### 1. The multiplicative grammar is saturated at the percent level — and at C≤3, at the 0.01% level

Calibration on random targets:

| Pool | median nearest-match dev | matched within 0.1% | matched within 0.01% |
|---|---|---|---|
| C≤2 (31k exprs) | 0.017% | 98.3% | 34.5% |
| C≤3 (2.25M exprs) | 0.0002% | 100% | 100% |

**Consequence:** any single closure of the form "cascade expression ≈ observable to ~1%" carries
**zero bits** against this grammar. That covers, as-scored:

| Target | claimed dev | bits (C≤2) | bits (C≤3) |
|---|---|---|---|
| Ω_Λ = (π−1)/π | 0.44% | 0.0 | 0.0 |
| Ω_m = 1/π | 1.05% | 0.0 | 0.0 |
| m_H/m_W = π/2 | 0.80% | 0.0 | 0.0 |
| m_K/m_π = 5/√2 | 0.045% | 0.1 | 0.0 |
| m_η′/m_η = 7/4 | 0.103% | 0.0 | 0.0 |
| f_π/m_π = 2/3 | 1.06% | 0.0 | 0.0 |
| m_π/Λ = 2/3 | 0.31% | 0.0 | 0.0 |
| m_μ/m_e lead | 0.13% | 0.1 | 0.0 |
| 1/α_em | 0.0057% | 2.8 | 0.0 |

For every target the pool contains dozens of unrelated expressions closer than the cascade's chosen
one (e.g. for Ω_Λ: `p(12)⁻²·p(14)²/√5` at 0.0000%). The cascade's *choices* are simpler than the
pool's best matches, and a complexity-weighted prior would give the simple closed forms some credit
back — but the burden of quantifying that prior is on the papers, and nothing in them does.

**The fine-structure constant gets no protection from its precision.** The published formula
1/α = 1/α(13) + π/α(14) + 6π is a *three-term sum*. In the additive grammar, 26,667 complexity-≤2
values yield **5,330 distinct two-term sums** within the published 0.0057% of 137.035999. The
three-term pool is strictly denser. Bits: **~0**. The 0.006% precision, which reads as the
strongest single number in `PREDICTIONS.md`, is fully consumed by the additive grammar's density.

### 2. The α(d*)/χᵏ correction family is the only numerically loaded structure — worth ~14 bits at face value, decaying with scan size

The corrections are drawn from a 16-member grid α(d*)/χᵏ (d* ∈ {12,13,14}, k = 0..4, plus χ⁻¹α
forms) spanning [0.0016, 0.045]. Per-observable surprisal of the *specific designated member*
landing within measurement error:

| Observable | needed shift | member | \|diff\|/σ | bits |
|---|---|---|---|---|
| m_τ/m_μ | 0.01721 | α(14)/2 = 0.01723 | 0.24 | 3.4 |
| m_τ (absolute) | 0.01283 | α(13)/2 = 0.01282 | 0.27 | 3.4 |
| sin²θ_W | 0.01125 | α(12)/2 = 0.01132 | 0.40 | 2.1 |
| ℓ_A | 0.01335 | α(13)/2 | 1.78 | 1.3 |
| α_s, Ω_m, θ_C, b/s, θ_23 | — | (loose σ) | ≤0.04σ but P(any)≈1 | 0.0 |

Naive product: 10.3 bits. The **reuse pairs** — the same grid member closing two unrelated
observables ({α_s, m_τ/m_μ} both by α(14)/2; {m_τ, ℓ_A} both by α(13)/2) — add 10.9 bits.
**As-presented total: 21.1 bits (~1 in 2 million).**

But that total assumes the 9 published observables were the only places the family was tried.
Monte-Carlo look-elsewhere (null: needed shifts log-uniform over the family's span, T observables
scanned, scoring identical to the real scoring including same-member credits):

| T (observables scanned) | null S (50/95/99.9%) | P(S ≥ 21.1) | surviving bits |
|---|---|---|---|
| 9 (publication bias–free) | 2.4 / 9.5 / 17.6 | 5.0×10⁻⁵ | **14.3** |
| 20 | 11.8 / 23.6 / 35.9 | 0.09 | 3.5 |
| 40 | 35.6 / 54.0 / 71.9 | 0.93 | 0.1 |

**Reading:** if the correction family was genuinely tested against only these 9 observables, the
pattern is a 1-in-20,000 coincidence — real evidence of structure. If ~40 observables were ever
scanned for a match against the grid (across the program's development), the pattern is exactly
what chance produces. The papers do not report how many observables were tried and discarded, so T
is not knowable from the published record. **This is the audit's central actionable finding: the
correction family's evidential weight rests entirely on an unreported quantity — the size of the
search.** A pre-registered extension (predict the correction for a *new* observable before
comparing) would settle it.

### 3. m_μ/m_e leading formula: ~3 bits

The variant space (contiguous Φ-spans of length 7–9 anchored in d = 5..14, × 10 natural
topological prefactors = 300 variants) contains **zero** other members within the claimed 0.13%,
and the nearest sibling (`exp(Φ(14..21))·2√π`, 0.132%) is essentially the same formula.
P(some variant lands) ≈ 0.13 → **2.9 bits**. Modest but genuine: the formula is not surrounded by
equally good siblings.

### 4. The 120-decade hierarchy: ~7–8 bits

Solving p(d) = c₁, p(d) = c₂ for (c₁, c₂) = (ln K, K) and computing the decade count from the
Ω-suppression: outputs across 3,452 candidate constants K span 11 to 9,001 decades, and only
0.09% land within ±0.5 decade of the observed 120.15. The cascade's K = √π gives 120.155 vs
120.146 observed. If K were a free draw: **10.2 bits**; subtracting ~2 bits for the documented
freedom in choosing the critical-point construction (p = c₁ vs p = c₂ vs argmax V vs argmax Ω)
leaves **~7–8 bits**. This is the single most robust numerical surprise in the program: the
hierarchy's *order of magnitude* is genuinely hard to hit by accident, and √π is arguably the
grammar's most distinguished constant.

---

## Overall accounting

| Claim class | bits surviving |
|---|---|
| All percent-level single closures (Ω_Λ, Ω_m, m_H/m_W, hadronic ratios, …) | **0** |
| 1/α_em to 0.0057% (three-term additive form) | **~0** |
| m_μ/m_e leading formula | **~3** |
| 120-decade hierarchy from √π critical points | **~7–8** |
| α(d*)/χᵏ correction family | **14.3 if T=9; ~0 if T≳40 — hinges on unreported search size** |

Total surviving surprisal: **~10 bits guaranteed** (hierarchy + m_μ/m_e), plus **0–14 bits**
contingent on the correction family's true look-elsewhere burden. The program's headline precision
claims (1/α_em at 0.006%, the percent-level cosmological and hadronic closures) contribute
essentially nothing, because the cascade's own expression grammar is dense enough to hit any
target that well.

## What would change this verdict

1. **Pre-registration of the correction family.** Publish, in advance, the α(d*)/χᵏ correction for
   an observable not yet compared (e.g. a mass ratio outside the current nine). A hit at ≤0.5σ
   would push the family to ~20+ bits regardless of historical T.
2. **A complexity prior.** The saturation argument treats all pool expressions as equal. A
   principled prior favouring low complexity (the cascade's choices *are* systematically simple)
   could restore a few bits to the single closures — but it must be stated and computed, not
   assumed.
3. **Disclosure of the search history.** Any record of observables tested against the correction
   grid and discarded would fix T and settle the family's evidential weight in either direction.

## Caveats

- The grammar is one choice; a different atom set changes densities. The atoms used are exactly
  the primitives the papers themselves use, which is the fairest available choice.
- Measurement σs are taken at the values used in `PREDICTIONS.md`; where the papers' σ accounting
  is disputed (e.g. the ℓ_A entry, where 301.44 vs 301.6±0.09 is −1.8σ, not the −0.16σ the table
  states — the absolute difference appears to have been mislabeled as a σ count), the audit uses
  the recomputed σ.
- Monte-Carlo results use 40,000 replicates; quoted tail probabilities below ~10⁻⁴ carry
  correspondingly large relative error.
