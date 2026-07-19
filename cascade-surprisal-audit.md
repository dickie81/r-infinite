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

## Addendum: the adelic compensator test

**Tool:** `tools/research/cascade_adelic_compensator.py`

**Motivation.** The cascade's primitives are exactly the archimedean local factor of the Riemann
zeta function: Ω(d) = 2/Γ_ℝ(d+1) and p(d) = (log Γ_ℝ)′(d+1), with Γ_ℝ(s) = π^(−s/2)Γ(s/2)
(verified to machine precision, Part A). In Tate's adelic picture the missing partners are the
finite-place factors ζ_p(s) = (1−p^(−s))⁻¹ with ∏_p ζ_p(s) = ζ(s), and the Freund–Witten adelic
product formula (A_∞ · ∏_p A_p = 1 for the Veneziano amplitude) supplies a physics precedent for
"the archimedean quantity is completed by a zeta compensator." The testable conjecture: the
empirical corrections to cascade leading-order quantities are δ ln X = ±ln ζ(d+1) at X's layer d.

**Result: the conjecture fails as a general mechanism.**

- **Strict layer-deterministic scorecard (Part C):** of seven observables with layer assignments,
  one hit (m_τ/m_μ via ln ζ(6), 0.30σ — but only after dropping the μ-layer factor; the canonical
  ratio ln[ζ(6)/ζ(14)] misses at 1.2σ), two loose "nears" with huge σ, and four misses including
  two catastrophic ones: m_τ absolute at 65σ and sin²θ_W at 64σ. The ζ-ladder has only one rung
  (ζ(6) ↔ 1.72%) in the 1–2% band where the corrections cluster; the α(d*)/χᵏ grid has several.
- **Head-to-head grid comparison (Part D):** scored with the identical P(any)/bits machinery over
  a common span, the ζ-grid carries **0.0 bits** total (its dense tail of tiny members makes
  small-shift matches free) against **14.7 bits** for the papers' α-grid. The correction family is
  *better* explained by the cascade's own structure than by the adelic one.
- **Exact-residual test (Part E):** the 1/α_em lead-formula residual is +5.672×10⁻⁵, known to
  ~10⁻¹⁰. The best adelic candidate, ln ζ(14) = +6.125×10⁻⁵, is off by 8% of the residual — a
  definitive miss at the available precision. Adelic corrections to ρ_Λ are ~10⁻⁶ relative,
  four orders below observational error: untestable, trivially consistent.

**The survivor.** ln ζ(6) = ln(π⁶/945) = 0.0171943 and the papers' α(14)/2 = 0.0172312 are two
structurally unrelated constants that *bracket* the measured m_τ/m_μ correction
(0.0172152 ± 0.0000678) at −0.30σ and +0.24σ respectively. The current PDG m_τ error (±0.12 MeV)
cannot discriminate between them. The two candidates differ by 3.7×10⁻⁵ (0.54σ); an m_τ
measurement at **±0.02 MeV** (a ~5× improvement, within reach of Belle II) would separate them at
3σ — a rare case where a numerological dispute has a scheduled experimental adjudication.

**Bottom line:** the "other half of ξ" reading is aesthetically compelling and structurally exact
at the level of identities, but as a *quantitative* completion mechanism it is refuted everywhere
it can be tested, with one measurement-limited exception. In audit terms it contributes 0 bits.

## Addendum 2: the cascade lattice operator vs the Riemann spectrum

**Tool:** `tools/research/cascade_lattice_spectrum.py`

**Pre-registered question.** The cascade's one admissible native operator — the stiffness matrix
of Part 0's elastic action S = Σ(2α(d))⁻¹(Δφ)² on the layer chain — was tested for (a) a
Riemann-shaped counting function (θ(T)/π, the phase of the cascade's own Γ_ℝ on the critical
line) and (b) GUE level statistics (the Montgomery–Odlyzko signature of the zeta zeros). Stated
prior, recorded before computation: no on both — a deterministic 1-D Jacobi chain should be
spectrally rigid.

**Result: the prior held; the cascade-native route to a Hilbert–Pólya realization is closed.**

- **Level statistics (decisive):** the operator's mean adjacent-gap ratio is 0.993 (d=4..217),
  drifting to 0.999 as the chain lengthens — a rigid crystal. Calibrated same-size controls run
  through the identical pipeline: Poisson 0.406, GOE 0.517, GUE 0.615, actual Riemann zeros
  0.615. The operator is ~40σ of spacing-variance away from GUE; no boundary condition or chain
  length changes this. 1-D deterministic chains are generically picket-fence; GUE requires
  complex/chaotic structure the layer chain does not have.
- **Staircase:** the λ-staircase prefers an E ln E fit (R² 0.996 vs 0.882 linear), but well below
  the Riemann-zero control's 0.99996, and the extra parameter accounts for much of the
  preference. Suggestive of nothing.
- **Direct overlap:** the best affine map of the first 30 eigenfrequencies onto the first 30
  zeros misses by 0.80 of a mean zero gap per level — no level-by-level correspondence. (A naive
  bootstrap makes the overlap look "1.5% rare"; that reflects only the crudeness of the
  comparison family and is explicitly disclaimed in the tool output.)

**Interpretation.** If the finite places ever enter the cascade (the ζ(6) scenario of Addendum 1),
the spectral object realizing them cannot be the layer-chain operator — it would have to be
something non-1-D and complex-Hermitian that the current papers do not construct. In audit
currency: 0 bits, door cleanly closed, with the controls demonstrating the pipeline would have
detected a real GUE signature had one been present.

## Addendum 3: can Part II's complex structure J rescue the spectral rigidity?

**Tool:** `tools/research/cascade_J_operator.py`

Addendum 2 closed the layer-chain operator (crystal, not GUE). The one complex object the
cascade owns is Part II's forced-precession complex structure J (`thm:complex`: two quarter-turns
give J² = −Id; evolution L(d) = i·N(d), cumulative propagator phase i^(D−d)). Three tests, priors
stated first:

1. **J-twisting the layer chain is exactly gauge-trivial.** Replacing real hopping −w_d with
   −i·w_d leaves the spectrum identical to machine precision (max eigenvalue difference 0.0) —
   bond phases on a path graph carry no flux. J alone *cannot* alter the chain's crystal
   spectrum; this is a theorem, checked numerically.
2. **The pairing-offset ambiguity yields no quaternionic structure.** The two admissible axis
   pairings ((12)(34)… vs (23)(45)…) give J₁, J₂ that neither commute nor anticommute; their
   product J₂J₁ is a signed two-step shift along the axis chain — a translation operator, a
   curiosity worth noting (a discrete momentum), but not an un-gaugeable flux source.
3. **Even genuine flux fails.** The minimal object where J can act spectrally — a two-leg ladder
   with elastic legs w_d = 1/(2α(d)) and lapse rungs N(d) carrying the propagator's cumulative
   phase i^d, giving verified flux π/2 per plaquette — has ⟨r̃⟩ = 0.07: a near-degenerate doublet
   crystal, *further* from GUE (0.60) than the bare chain, because the rung coupling N(d) ~
   √(2π/d) decays while leg stiffness grows, decoupling the legs; and deterministic quasi-1-D
   systems are regular regardless.

**Conclusion.** The J route is closed. GUE statistics require genuinely chaotic dynamics —
many coupled degrees of freedom with un-gaugeable phases at all scales — and the cascade's
defining virtue (everything exactly solvable through the Γ function) is precisely what forbids
this. The structural picture is consistent with Addenda 1–2: in ξ = Γ_ℝ·ζ, the archimedean half
is smooth and integrable, the prime half is where the spectral chaos lives, and the cascade owns
only the first. 0 bits; door closed with pre-registered priors.

## Caveats

- The grammar is one choice; a different atom set changes densities. The atoms used are exactly
  the primitives the papers themselves use, which is the fairest available choice.
- Measurement σs are taken at the values used in `PREDICTIONS.md`; where the papers' σ accounting
  is disputed (e.g. the ℓ_A entry, where 301.44 vs 301.6±0.09 is −1.8σ, not the −0.16σ the table
  states — the absolute difference appears to have been mislabeled as a σ count), the audit uses
  the recomputed σ.
- Monte-Carlo results use 40,000 replicates; quoted tail probabilities below ~10⁻⁴ carry
  correspondingly large relative error.
