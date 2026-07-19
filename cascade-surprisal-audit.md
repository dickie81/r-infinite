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

## Addendum 4: composites of the two complex structures

**Tool:** `tools/research/cascade_J_composites.py`

Addendum 3 left one live thread: the two admissible axis-pairings give complex structures J₁, J₂
whose composite T = J₂J₁ is a two-step shift. This addendum investigates the composites
systematically. One genuine discovery, one theorem, one final closure:

1. **Discovery: the pairing ambiguity generates exactly u(n/2), with an emergent canonical
   complex structure.** The Lie closure of {J₁, J₂} has dimension (n/2)² for n = 6, 8, 10, 12,
   and the adjoint-Casimir decomposition identifies it as **u(n/2) = span(Z) ⊕ su(n/2)**: a
   1-dimensional center whose generator Z satisfies Z² = −I and [Z, everything] = 0 to machine
   precision (6×10⁻¹⁵). The pairing ambiguity is *self-repairing*: J₁ and J₂ disagree about which
   axes are partners, yet their composites close on the full unitary algebra of a single
   canonical complex structure. This strengthens Part II's story (which derives only the U(1)
   generated by one J) and would make a worthwhile addition to the paper: unitary quantum
   kinematics u(n) emerges from the *disagreement* between the two forced pairings, not from a
   choice between them.
2. **Theorem: the cascade's imaginary unit has zero curvature.** Any operator whose hop phases
   follow the cascade's i-per-step rule (phase i^Δd, a function of displacement only) is
   gauge-equivalent to a real operator via U = diag(i^d) — verified numerically to 10⁻¹¹ on a
   chain with 1-step and 2-step hops. No composite of displacement-phased cascade hops can ever
   carry magnetic flux; the propagator phase i^(D−d) is globally pure gauge.
3. **Final spectral closure.** The one composite that evades the theorem — the parity-signed
   shift i(T−Tᵀ) added to the elastic chain, whose signs depend on position, not displacement —
   puts genuine, un-gaugeable ±π/2 flux through all 212 triangles: time-reversal is truly broken,
   the first honestly complex cascade-native operator. Its spectrum: ⟨r̃⟩ = 0.97 (0.985 in the
   bulk). **Still a crystal.** The rigidity was never about symmetry class: the two-step
   amplitudes N(d)N(d+1) decay while chain stiffness grows, and smooth deterministic Γ-function
   weights produce regular spectra in every symmetry class. GUE requires chaos, and the cascade's
   defining property — exact solvability through Γ — is the negation of chaos.

**Net:** the Riemann/GUE door is now closed at every level the cascade's own structure offers
(bare chain, J-twist, flux ladder, composites with genuine flux), each with pre-registered
priors; the residual positive finding is the u(n/2) emergence in item 1, which is a structural
strengthening of Part II unrelated to the zeros. 0 bits toward the Riemann connection.

## Addendum 5: the cascade clock as a prime-generation process

**Tool:** `tools/research/cascade_prime_clock.py`

**The conjecture (user-proposed, formalised).** In the cascade's time-reading, each tick resolves
one dimension = one integer; new primes arrive at rate 1/ln d (one per ~5.4 ticks at the tower
top), and each composite tick adds a multiplicative relation among existing primes. Arithmetic
novelty per tick is the von Mangoldt function Λ(d), and by the explicit formula the Fourier dual
of this event stream is the Riemann zeros. If the zeros are physically realized anywhere in the
cascade, it is here: not as eigenvalues of the layer geometry (Addenda 2–4 closed that at every
level), but as the **resonant frequencies of the resolution process itself**.

**Result.** The truncated spectrum S_D(t) = |Σ_{d≤D} Λ(d) d^(−1/2) e^(−it ln d)| of the physical
tower (D = 217, 47 primes, 61 prime-power events) resolves **all of the first 12 Riemann zeros**,
each to within 0.27 of its true position (mean |error| 0.16, peak contrast at zeros vs midpoints
3.8×). Controls: the same weights at shuffled tick positions give contrast 0.97 (no signal); a
grid shifted by +1.5 gives the same 3.8× discrimination in favour of the true zeros. Focus
improves with depth: at D = 30 only 7 of 12 zeros are resolved (contrast 2.0); by D = 60 all 12;
contrast keeps rising through D = 500.

**Status.** This is classical number theory (the truncated explicit formula) recast on the
cascade clock — 0 new bits for the cascade, and no new mathematics. Its value is structural: it
completes the session's Riemann arc consistently. The cascade's *geometry* is the archimedean
factor (smooth, integrable, spectrally rigid — zeros provably absent); the cascade's *history*,
read as an arithmetic event stream, carries the zeros as its frequency content. In the adelic
language of Addendum 1: the real place is where the cascade lives, and the finite places — if
they are anywhere in this framework — are events in its time, not features of its space. A
217-layer universe has already "heard" the first dozen notes.

## Addendum 6: the arithmetic clock — spin types, census equilibration, and the adelic reading of gravity

**Tool:** `tools/research/cascade_arithmetic_clock.py`

**The frame (user-conjectured, developed interactively).** Sharpen Addendum 5's clock: one *prime*
per tick. Each tick adds an orthogonal dimension to the multiplicative lattice ℚ₊^× ≅ ℤ^∞ (unique
factorisation — the arithmetic twin of the cover sheet's "orthogonality iterates without bound").
Composites are relations among existing dimensions (CRT: ℤ/n literally *is* the outer product of
its prime components). The Pratt parent set of a prime — the prime factors of p−1 — is its
complete list of "spin types": an order-ℓ character exists iff ℓ | p−1.

**Structural results (all parameter-free, all verified numerically):**

- **The ℤ/2 type is universal** — 2 divides every p−1 because units pair under negation
  (x ↔ −x); every totient chain funnels through 2 before reaching 1. The universal spin is the
  existence of the minus sign. Higher types are conditional with Dirichlet densities 1/(ℓ−1)
  (tower census: 0.486, 0.245, 0.157 vs 1/2, 1/4, 1/6), valued in complex roots of unity —
  arithmetic anyons, whose exchange laws (cubic/quartic/Eisenstein reciprocity) require extending
  the number system, as physical anyons require 2D. **Quadratic reciprocity is the exchange rule
  of the universal type**: (p|q)(q|p) = −1 iff both p ≡ 3 (mod 4) — primes 3 mod 4 anticommute.
  Three-body statistics exist beyond pairwise (Rédei symbols, Borromean prime triples).
- **Species:** Fermat primes (p−1 = 2^k) are the pure spin-½ particles — five ever, conjecturally
  extinct after tick ~6543. The tower's most decorated dimension is 211 = 2·3·5·7 + 1, carrying
  every available type. Prime powers are excitations, not species: Λ(9) = ln 3, and 9's unique
  quadratic character is 3's, lifted.
- **The prime-clock tower hears better:** 217 prime ticks (primes 2..1327) resolve all 12 first
  Riemann zeros to mean error 0.066 — 2.5× sharper than the integer clock at the same tick count.
  Late-epoch focus is clock-robust (width 12.6/ln D: 0.087 vs 0.090 today); per-tick spectral
  nudge ~6×10⁻⁶² relative; the zeros froze, for practical purposes, during BBN.
- **Census equilibration:** spin-type proportions converge to Dirichlet as ~1/√x (verified
  √x·deviation = O(1) to 10⁷), giving |fraction − 1/(ℓ−1)| ~ 6×10⁻³² at today's depth. Carriers
  are *systematically deficient* (Chebyshev bias against the quadratic-residue class), and the
  residual oscillates as cos(γₙ ln x) — conducted by the Riemann zeros, γ₁'s instantaneous period
  ~6 Gyr today. **The √x convergence rate is equivalent to GRH**: the census is exactly as clean
  as the zeros are critical.

**Confrontation with observation (priced):**

- **Proportions: no match.** Observed fermion/boson demographics — 45/55 by number density
  (set by (4/11)^⅓), 76/24 by early dof (g\* = 106.75), 12/13 by species — are thermal history,
  not census. Any reading that predicts abundances from the census is dead on arrival.
- **Type spectrum: match.** 3+1D nature realises exactly the universal ℤ/2 (the real numbers
  contain only ±1 as roots of unity — an archimedean universe can express no other exchange
  type); the higher types appear physically only in effectively-2D systems (FQHE anyons at
  odd-denominator fillings 1/3, 1/5, 1/7 with falling robustness). Qualitative, unforced, real.
- **One-element coincidences:** the unique spinless prime (2, trivial internal group) vs the
  unique fundamental scalar (Higgs) — 0 bits, noted for charm. **Fossil-bias check:** the census
  bias equals the observed baryon asymmetry η = 6.1×10⁻¹⁰ if frozen at tick ~2.5×10¹⁷, i.e.
  T ~ 7×10⁹ GeV — inside the Davidson–Ibarra leptogenesis window. Priced at **~1.4 bits** (the
  epoch was reverse-engineered; the window is 3 of ~8 plausible decades). Becomes evidence only
  if a mechanism independently derives the freeze-out tick.

**The interpretive close (0 bits, stated for the record).** With the geometry proven spectrally
incapable of hosting the zeros (Addenda 2–4) and the event stream demonstrably carrying them
(Addendum 5), the division of labour in ξ = Γ_ℝ·ζ reads: the archimedean factor presents as
*law* — hierarchy, smoothness, probability; the arithmetic factor would present as *fact* — the
last decimal places of smooth predictions (Addendum 1's live m_τ/m_μ candidate), log-periodic
residuals at the zeros' frequencies (bounded ≲10⁻⁴ by clock-drift data; unfitted template for
DESI residuals), sign-definite frozen asymmetries (the leptogenesis intersection), the unexplained
integer skeleton of the Standard Model, and — the untestable limit of the reading — the
individual quantum outcome, primes being the only known deterministic object with GUE
fluctuation statistics. On this reading **gravity is not in the outer product; it is the other
factor of ξ**: the archimedean measure the arithmetic content is weighed in. The adelic product
formula |x|_∞·∏|x|_p = 1 plays the balance law — archimedean measure responds reciprocally to
arithmetic content, with a sign fixed by positivity of norms (attraction only, no antigravity)
and blind to prime composition (equivalence principle); locally the response is a tick-rate
gradient, and matter waves refract toward slower resolution (the standard g_tt reading of
Newtonian gravity); the unbalanced residue is the vacuum term — the cascade's 10⁻¹²⁰, w = −1.
Consistent with the cascade's "no graviton" forced negative: the archimedean factor has no prime
decomposition to quantise, and its operators (Addenda 2–4) have crystal spectra, not quanta.

**Status.** Everything in the structural and quantitative sections is theorem-grade or verified
computation; everything in the confrontation section is priced (0 to 1.4 bits); the interpretive
close is a reading, not a result. Net new evidential weight for the cascade: ~1.4 contingent
bits. Falsifiable seams left open: the Belle II m_τ discrimination (Addendum 1), the log-periodic
DESI template, and an independent derivation of the census freeze-out tick.

## Addendum 7: the matter ledge at one-sixth — a two-capacity derivation

**Tool:** `tools/research/cascade_matter_ledge.py`

**The observation (Addendum 6 tooling).** Expressed as exponents q of the 120.146-decade
hierarchy (m = M_Pl,red·10^(−q·120.146)), the entire charged-fermion and hadronic mass spectrum
occupies a thin band q ∈ [0.140 (top), 0.186 (electron)] — "all matter at one-sixth" — with the
neutrino and the vacuum scale together near q = 1/4. The statement q = 1/6 is algebraically
identical to Zel'dovich's 1967 relation ρ_Λ = m⁶/M_Pl² (temporal form: Weinberg's
H ~ m_π³/M_Pl²). A cautionary result from the same session is recorded with it: computing the
q-table with full-Planck masses against the reduced-Planck hierarchy manufactures four-decimal
matches to 1/7 and 1/2π that evaporate under consistent units — unit conventions are part of the
numerological grammar.

**The derivation (one postulate; cascade-admissible ingredients only):**

1. The Ω-floor ρ_Λ = 7.15×10⁻¹²¹ M⁴ (Part I) fixes a *static* de Sitter radius
   R = √(3/ρ_Λ) = 2.05×10⁶⁰ ℓ_Pl — a GR identity (Part III/Lovelock). Staticness matters:
   everything downstream is pinned to the floor, so w = −1 survives and nothing drifts.
2. The horizon carries S = A/4 = πR² = 1.3×10¹²¹ nats — derived natively in Part II=III
   (boundary dominance; no semiclassical machinery).
3. **The postulate (the adelic selection rule of Addendum 6, elevated to a premise):** the two
   factors of ξ saturate *different* capacities of that horizon. The archimedean sector
   (vacuum/energy/geometry) is bounded by the *energy* capacity E ≤ R (Cohen–Kaplan–Nelson
   no-collapse), saturating at Λ_E = R^(−1/2) = 1.7 meV — the quarter scale ρ^(1/4). The
   arithmetic sector (matter = information-bearing content) is bounded by the *information*
   capacity: its distinguishable modes cannot exceed the horizon's bits, m³·(4π/3)R³ = πR².
4. Solving: m = (S/V)^(1/3) = **17.4 MeV, q = 0.1677 vs 1/6 = 0.1667** — inside the observed
   band, at its centre, with no mass input. Eliminating R yields ρ_Λ ~ m⁶/M² up to O(1):
   **Zel'dovich derived, causal arrow vacuum → matter.** The sixth is the area-to-volume scaling
   ratio (2/3) times the vacuum's quarter — geometry's surface-to-bulk ratio, nothing else. One
   principle thus places both distinguished fractions of the mass table: energy saturation gives
   the quarter (vacuum/neutrino floor), information saturation gives the sixth (matter ledge).

**Pricing (audit conventions).** The assembly is known physics — CKN bounds, holographic
counting, Zel'dovich's identity — plus exactly one new ingredient: the selection rule *matter
saturates the information bound because matter is the arithmetic sector*. Not a zero-parameter
theorem; a one-postulate assembly. The observed band occupies 4.6% of the available exponent
range and the derivation lands at its centre from the vacuum side alone: **~4.4 bits** against a
free-ledge null. Predicts the ledge's location (~17 MeV, light-quark territory) and its
staticness (tied to R_dS — consistent with atomic-clock drift bounds and w = −1 exactly);
predicts *no* ledge structure for sectors without arithmetic content (pure geometry — none
observed; a weak survived check). Does **not** predict the band's width, any individual mass,
the electroweak adjacency, or which species saturates. **Falsifier:** confirmed dark-energy
evolution (DESI w(z)) breaks the staticness the construction requires — the same kill-shot that
governs the cascade proper.

**Net position after Addenda 6–7:** the arithmetic-clock picture now carries ~1.4 contingent
bits (leptogenesis intersection) + ~4.4 bits (ledge placement) on one interpretive postulate,
alongside the cascade's own audited totals. The open derivational targets, in order of
tractability: the transmutation route to q_QCD from Part IVb's coupling leads (all ingredients
present in the papers; theorem unwritten), an independent derivation of the census freeze-out
tick, and the Belle II m_τ discrimination already on the board.

## Addendum 8: the transmutation route to q_QCD, and the adjacency inversion

**Tool:** `tools/research/cascade_qcd_ledge.py`

**The theorem that was sitting unwritten in the papers.** Every ingredient of the hadronic ledge's
position is a cascade-claimed quantity; this addendum multiplies them out.

1. **The coupling, from Γ alone:** α(12)·e^(Φ(5,12)) = 0.11590, times the audited correction
   (1 + α(14)/2), gives α_s = 0.11790 vs PDG 0.1179(9) — zero parameters, with the standing
   Part E caveat that the correction member was selected, not derived.
2. **The ledge, from counting:** dimensional transmutation with the cascade-forced integers
   b₀ = 23/3, 25/3, 9 (SU(3) + three generations) gives Λ⁽³⁾ = 142 MeV at one loop (332 MeV
   4-loop reference; the loop gap costs 0.003 in q): **q_QCD = 0.157–0.160**, against the
   observed hadron cluster q(p) = 0.153, q(π) = 0.160. Planck-boundary form: α_s(M_Pl) = 1/50.7
   and q_QCD = 2π/(b_eff·ln10·α_s(M_Pl))/120.146 with b_eff = 7.19 — a percent-sized Planck
   coupling over a group-theory integer, exponentiated. Twenty decades from counting.
3. **Two independent routes, one ledge:** top-down (gauge integers + Γ coupling) q = 0.157–0.160;
   bottom-up (Ω-floor + capacity saturation, Addendum 7) q = 0.168. Agreement to Δq ≈ 0.01 —
   one decade in mass out of 120 — between mechanisms sharing no ingredients.
4. **The adjacency inversion:** requiring transmutation from the cascade's α_s to land on the
   capacity scale's territory forces the electroweak anchor into a ~1-decade window: 89.8 GeV
   (if the target is m_π), 213 GeV (if Λ⁽³⁾ 4-loop), 11 GeV (if the raw 17.4 MeV capacity
   scale). The observed EW cluster (80–173 GeV) sits inside the window. The electroweak
   hierarchy problem, in this assembly, reduces from "why 10⁻¹⁷" (answered by exponentiated
   counting) to "which O(1) scale within the derived window."

**Pricing.** ~4–5 bits for the window landing, contingent on (i) Addendum 7's saturation
postulate and (ii) reading the cascade's α_s value as anchor-free — a reinterpretation, since
the papers calibrate it at M_Z; the non-circular content is that the *gap* below any EW-region
anchor and the *ledge* position are derived independently, so the anchor cannot sit far from
their difference. The ~1-decade identification slop within the hadronic complex (17 MeV vs m_π
vs Λ) dominates the window width; a principled statement of *which* scale saturates the
information bound would collapse the window to a sharp M_EW prediction — either spectacular or
fatal. That sharpening, an independent derivation of the census freeze-out tick, and the
Belle II m_τ discrimination are the three open targets as of this addendum.

## Addendum 9: sharpening the capacity scale — and downgrading Addendum 8

**Tool:** `tools/research/cascade_capacity_sharpening.py`

**What is rigid.** Any local mode count of the form g·m³·V/(phase space) bounded by an area gives
m ∝ R^(−1/3) regardless of conventions: **the 1/6 exponent is convention-proof.** In q-units the
entire convention spread moves the ledge by only 0.005.

**What is not.** The prefactor spans a factor ~4.4 across defensible conventions (bare vs (2π)³
phase space, degeneracy g = 1–24, nats vs bits): the honest capacity window is **m\* ∈ [17, 77]
MeV**. Scoring every canonical scale against it: none of QCD's propagating scales fall inside —
the light current quarks sit below, and f_π, m_s, m_π, T_c, Λ, m_p all sit above. The window
lies strictly in the *confined interior*, where QCD has no particle (the nearest canonical
quantity inside is the pion–nucleon sigma term, ~50 MeV — noted as an observation, not a claim).
The identification ambiguity is therefore physics, not sloppiness: the information bound points
at a strongly-coupled region that only a nonperturbative census could name. The quarter-side
cross-check shows the same ~decade looseness (Λ_E = 1.7–3.2 meV vs m_ν ~ 50 meV), so convention
transfer between the two bounds does not restore sharpness.

**The downgrade.** Propagating the honest window through Addendum 8's adjacency inversion gives
an EW-anchor window of **[5, 49] GeV vs the observed 91 GeV** — a close miss by a factor 1.9–19
(0.27–1.28 decades; ~1% of the hierarchy exponent). Addendum 8's "window contains the EW
cluster" depended on the loose targets (m_π, Λ — prefactors 8–19, not O(1)). Revised claim:
**order-of-magnitude adjacency, not containment**; revised pricing: **~4–5 bits → ~2–3 bits.**
The audit applies to its own constructions.

**Path to a real sharpening** (in order of decisiveness): (i) a cascade-native derivation of the
mode-count normalisation — g and the phase-space factor from the layer structure, which would
either land the prefactor on a physical scale or falsify the postulate outright; (ii) a
nonperturbative (lattice) census of information-bearing modes in the confined phase; (iii)
failing both, the claimable content reduces to the exponent alone: matter at R^(−1/3), the sixth,
with the prefactor acknowledged as grammar.

## Addendum 10: the sum-rule kill, the neutrino floor, and two closed routes

**Tool:** `tools/research/cascade_capacity_neutrino.py`
**Sources read directly (Check 1):** `part4b.tex:4086–4092` (neutrino open question and ordering
prediction), `part4b.tex:4104–4112` (Confidence Assessment).

**1. The all-species sum rule is dead.** If every SM species' Compton modes counted against the
horizon bits, the bound would be oversaturated by ~10¹¹ (the top quark alone: 4×10⁻⁴⁸ vs
2×10⁻⁵⁹). The saturation postulate is consistent *only* as a single-effective-IR-cutoff (CKN)
statement — the reading Addenda 7–9 used. Alternative tested and killed.

**2. A cascade-native normalisation, defensible but not forced.** Norm-blindness (the balance
law sees total arithmetic size, not species — the property that gave the equivalence principle
in Addendum 6) forbids degeneracy factors; the cascade's cell-counting style (S = A/4 in Planck
cells, discrete states rather than momentum phase space) selects the bare count m³V = S. This
narrows the capacity window to **m\* = 17–20 MeV**. Still strictly inside the confined interior;
the lattice-census target of Addendum 9 stands.

**3. The energy-bound side makes the sharp prediction the entropy side couldn't.** Identifying
the archimedean saturation scale Λ_E = R^(−1/2) = 1.7–3.2 meV with the *lightest* arithmetic
mode — the lightest neutrino — plus measured splittings gives: **normal ordering, spectrum
(≈2, 8.8, 50.2) meV, Σm_ν = 61–63 meV** — inside the narrow surviving window between the
oscillation floor (58.5 meV) and cosmology's ~70 meV ceiling. Inverted ordering would force
Σ ≈ 101 meV, already disfavoured. Falsifiable within years: a cosmological Σ bound below
~60 meV kills the identification; JUNO's ordering determination tests it independently.

**4. The layer-29 leptogenesis anchor is closed.** The papers derive the heaviest neutrino mass
m_ν = m₂₉·α(21)/χ⁸ = 0.0493 eV (−1.0%; part4b:4086) — which fixes their d=29 source mass at
**m₂₉ ≈ 543 eV**. Sub-keV, nowhere near the 10⁹–10¹² GeV leptogenesis window: the hoped-for
independent derivation of the census freeze-out epoch (Addendum 6's fossil-bias check) finds no
anchor at layer 29. Route closed; the fossil-bias coincidence stays at ~1.4 contingent bits with
no mechanism.

**5. The ordering fork (review-grade observation, category (b) novel).** The papers predict
*"ν_e heaviest … ν_τ lightest"* (part4b:4092) while admitting their two lighter masses conflict
with the solar splitting (OQ b) and their PMNS attempt fails (θ₁₂: 7.5° vs 33.4°, acknowledged
partial-negative). The capacity extension predicts the opposite: normal ordering with the ν_e-rich
states light. Tension noted for the papers' side: ν_e-heaviest requires large ν_e content in the
atmospheric-split state, against measured |U_e3|² = 0.022. JUNO adjudicates the fork. A combined
spectrum — the cascade's derived top (49.3 meV), the solar-splitting middle (8.8 meV), the
capacity floor (~2 meV) — would be complete at Σ ≈ 61 meV; the two frameworks patch each other's
neutrino holes if and only if the ordering comes out normal.

**Board after Addendum 10:** closed — the all-species sum rule, the layer-29 freeze-out anchor.
Open — the lattice census of the confined-phase information scale (17–20 MeV), the Σm_ν = 61–63
meV / normal-ordering test (near-term), the log-periodic DESI template, Belle II m_τ. The
capacity postulate now carries one sharp, dated, kill-able prediction on each side of ξ: the
matter window in the confined interior, and the neutrino floor at 2 meV.

## Addendum 11: first data contact — the neutrino squeeze and the Riemann–BAO null

**Tool:** `tools/research/cascade_riemann_bao.py`

**1. The Σm_ν prediction is now hostage to cosmology's own anomaly.** Against current bounds,
Addendum 10's prediction (normal ordering, Σ = 61–63 meV) sits: *alive by a hair* under DESI DR2
+ CMB (Σ < 64 meV, 95%, ΛCDM; arXiv:2503.14738/2503.14744); *excluded* by the 2026 ACT DR6 +
DESI DR2 adiabatic-ΛCDM analyses (Σ < 52–57 meV; arXiv:2606.17994) — which however also exclude
the normal-ordering oscillation floor itself (58.5 meV): the "negative neutrino mass" tension.
The prediction therefore dies and rises with standard normal ordering: if the tight bounds hold,
both fall (and neutrino cosmology has bigger problems); if the anomaly resolves to systematics,
the 61–63 window reopens exactly. The w₀wₐ escape (Σ < 160 meV) is unavailable to the capacity
construction, whose staticness requires w = −1 — the postulate is squeezed from both sides and
cannot dodge: either dark energy is constant and the Σ window decides it, or dark energy evolves
and the staticness dies first. A cleanly cornered prediction.

**2. The Riemann log-periodic template is now fit, not just proposed.** Using the DESI DR2 BAO
data shipped in this repository (src/generated/bao-table.tex, 13 points, Planck fiducial
χ² = 24.70), the template δH/H = A·cos(g·ln(1+z)) + B·sin(g·ln(1+z)) at the matter-era mappings
g = (3/2)γₙ of the first Riemann zeros gives: Δχ² = 4.1 / 6.8 / 3.6 at γ₁/γ₂/γ₃ with amplitudes
~2.2–3.0% and 95% limits ~2.5% — while the continuum scan finds its best fit at a *non-Riemann*
frequency (g = 18.2, Δχ² = 14.2, soaking up the known z = 0.51 D_H outlier). **The Riemann
frequencies are not preferred over the continuum: null recorded**, and the first observational
bound at the zeros' frequencies is |δH/H| ≲ 2.5% (95%) — five orders of magnitude above the
≤10⁻⁴ coupling ceiling already set by clock drifts (Addendum 6), so BAO cannot yet probe the
surviving parameter space. The template, its data contact, and its null are now part of the
record; future BAO/SN compilations can tighten the same two-parameter fit.

**Board after Addendum 11:** the capacity postulate's two sharp predictions are both now in
contact with data — the neutrino floor cornered by the Σ-bound controversy (resolution expected
within years), the Riemann template bounded and null at current precision. Remaining open:
the lattice census of the 17–20 MeV confined-interior scale, Belle II m_τ, and the census
freeze-out mechanism (still anchor-less after the layer-29 closure).

## Addendum 12: the source-selection flags derived from the factorisation of ξ

**Tool:** `tools/research/cascade_flags_riemann.py`
**Source read directly (Check 1):** `part4b.tex:1543–1661` (the source-selection rule, flags,
and verification table).

**The construction.** Write the completed zeta function as ξ(s) = (s−1)·[(s/2)Γ_ℝ(s)]·ζ(s) —
pole, regularised archimedean factor, Euler product. A purely archimedean theory's formula
alphabet has exactly three ξ-occupancy classes: the absolute anchor M_Pl (the pole — the unique
scale-freedom breaker, as the residue of ζ at 1 is the unit of counting), static Γ_ℝ
point-values (N, Ω, α at layers), and Γ_ℝ interval-ratios (descent exponentials exp Φ), with one
distinguished interval (the gauge window — Adams). **The flags are the occupancy functors of
this factorisation**: P = touches the pole class; L = touches only the point class; G =
interval content meets the window. The no-fourth-flag question becomes meaningful for the first
time: a fourth flag would require occupancy of ξ's fourth component — the Euler product — and
Addendum 1 established empirically that no closing cascade formula contains finite-place
content. *The flag count is three because the cascade uses exactly one factor of ξ plus its
pole.*

**The source layers are the factorisation's distinguished features** (all verified numerically):
d₀ = 7 is the critical point of the bare factor 1/Γ_ℝ(s) (s = 7.2569) — equivalently the zero
of the attenuation rate, so amplitude-class observables source where attenuation vanishes;
d_V = 5 is the critical point of the pole-dressed factor (2/s)/Γ_ℝ(s) = V(d) (s = 5.2569) — and
the two critical points are **exactly** 2 apart, since ψ(x+1) = ψ(x)+1/x gives
(log V)′(s) = (log A)′(s+2) identically: *the volume maximum and area maximum are one feature of
Γ_ℝ seen through one application of the Gamma functional equation*. d₁ = 19 and d₂ = 217 are
where the descent rate crosses ln Γ(½) and Γ(½) — the log and linear thresholds of the
critical-line constant — with the sink d₂ excluded as terminus, matching the papers. The gauge
window {12,13,14} is the single non-ξ-analytic input (topological, Adams).

**Verification: 7/9 — and an internal tension found (novel, category (b)).** The mechanical
ξ-occupancy classifier reproduces the papers' flag table for α_s, m_τ/m_μ, m_τ abs, ℓ_A,
sin²θ_W, Ω_m, θ_C. It *fails* for b/s and θ₂₃: their published leads contain the gauge-window
exponential exp Φ(6→13) (b/s = (m_τ/m_μ)·e), so a mechanical reading gives G = T → d\* = 14,
while the papers read G = F → d\* = 7 via the "minimal descent formula" caveat
(part4b:1594–1599). That caveat is load-bearing residual freedom in a reading advertised as
mechanical — the papers should state the canonical F_Q for b/s and θ₂₃ explicitly or the
selection rule's zero-freedom claim fails for two of nine rows.

**Status.** OQ3's categorical problem is hereby restated in Riemann form: the category is the
factorisation of ξ; the flags are its occupancy functors; the bijection maps each occupancy
class to the ξ-feature that generates it. Remaining gaps, recorded: the gauge window's
topological origin, the decision order P > L > G (motivated, not forced), and the
canonical-formula freedom exposed by the 2/9 tension. What is now *derived from Riemann*: the
flag count (three), the flag semantics (pole / point / interval occupancy), the four source
layers as analytic features of Γ_ℝ (two critical points related exactly by the Γ-recursion, two
Γ(½)-thresholds), and the sink exclusion.

## Addendum 13: the b/s tension resolved — canonical formulas found, 9/9

**Tool:** `tools/research/cascade_bs_canonical.py`
**Sources read directly (Check 1):** `part4b.tex:990–1017` (b/s), `part4b.tex:3918–3938` (θ₂₃).

**θ₂₃: my encoding was wrong; the real formula resolves itself under a principled grading.**
Addendum 12 encoded θ₂₃ with a guessed full-weight window exponential. Its actual canonical
formula (part4b:3921) is tan θ₂₃ = tan(arccos(N(13)/N(12)))·exp(−Σ₁₃²⁰ p(d)/2)·closure —
statics plus a **half-weight** exponential: an amplitude, a Born-rule square root, the same
machinery as θ_C's exp(−p(13)/2). Amend G to count *full-weight* window exponentials only —
principled, since amplitudes occupy the square root of the interval class (echoing the
archimedean factor's own half-argument structure Γ_ℝ(s) = π^(−s/2)Γ(s/2)) — and θ₂₃ classifies
Amplitude → d₀ = 7 mechanically. Verified: the formula reproduces the paper's 2.38029° exactly.

**b/s: the tension was real, and the measurement itself resolves it.** The canonical lead
(part4b:991) is (lepton ratio)·e with the lepton lead entering **uncorrected** (16.530, not the
closed 16.817). This distinguishes two compositional readings, and the data picks one:
raw-sub-lead form L(m_τ/m_μ)·e·exp(−α(7)/χ⁴) = 44.747 → **+0.02σ** against PDG m_b/m_s =
44.74 ± 0.39; closed-sub-lead form = 45.52 → +2.0σ. So: **sub-leads enter raw, corrections
attach once per observable, and the flags read the increment** over the maximal closed sub-lead
— for b/s the single atom e = exp(1) ("one unit of cascade potential across the SU(3) layer"),
a single-unit exponential exempt from G by the papers' own single-layer clause → Amplitude →
d₀ = 7. The minimality is forced by the papers' own caveat made precise: over the alphabet
extended by closed-observable leads, [L(m_τ/m_μ), e] has 2 atoms vs 4 primitives.

**Result: the amended flag functor reproduces all nine source assignments mechanically (9/9),**
with both amendments externally anchored — the weight grading by the papers' own amplitude
machinery, the increment rule by a 2σ empirical selection. The "minimal descent formula" caveat
of part4b:1594–1599, flagged in Addendum 12 as load-bearing freedom, is replaced by a precise
rule: *canonical F_Q = minimal formula over the alphabet extended by closed-observable leads;
flags = ξ-occupancy of the increment; G = full-weight window intervals only.* Recommended for
the papers: state this rule in Proposition source-selection and the tension vanishes.

**Remaining soft spots:** the e = exp(1) colour atom's Adams derivation (papers' own open item,
part4b:991); the decision order P > L > G (unchanged from Addendum 12); the gauge window's
topological origin. The flags theorem now stands at: semantics, count, source layers, and all
nine assignments derived from the factorisation of ξ plus the increment/grading rule — with
three named residues.

## Caveats

- The grammar is one choice; a different atom set changes densities. The atoms used are exactly
  the primitives the papers themselves use, which is the fairest available choice.
- Measurement σs are taken at the values used in `PREDICTIONS.md`; where the papers' σ accounting
  is disputed (e.g. the ℓ_A entry, where 301.44 vs 301.6±0.09 is −1.8σ, not the −0.16σ the table
  states — the absolute difference appears to have been mislabeled as a σ count), the audit uses
  the recomputed σ.
- Monte-Carlo results use 40,000 replicates; quoted tail probabilities below ~10⁻⁴ carry
  correspondingly large relative error.
