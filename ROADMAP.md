# Cascade Series — Roadmap

This file tracks open structural questions and the concrete next steps to close them. Each entry has: status, what's known, what's missing, and the most tractable path forward.

The single source of truth for predictions is [`PREDICTIONS.md`](PREDICTIONS.md). The single source of truth for review protocol and standing issues is [`CLAUDE.md`](CLAUDE.md). This roadmap is the working document for advancing the framework.

## Open structural questions

### 1. Channel-count rule for Amplitude observables — structural closure (3/3 of identification done; rigour gap (a) closed by inverting the framing; only completeness proof remains)

**Status:** Empirical fit grounded in stable homotopy theory and KO-theoretic Bott periodicity. Activation mechanism derived from cascade scalar action's sector-symmetry. Term-by-term (w_1, w_2) identification supplied for all three closed Amplitude observables (θ_C, b/s, θ_23). The "θ_23 P_2 rigour gap" framing is corrected by the exploration verifier: P_2 is actually one of the two most directly anchored cases. Only residual (b) (formal completeness) remains.

**Verifiers:**
- [`tools/research/cascade_channel_count_rule.py`](tools/research/cascade_channel_count_rule.py) — empirical verification + activation argument + term-by-term identification for all three observables.
- [`tools/research/cascade_channel_count_p2_rigour.py`](tools/research/cascade_channel_count_p2_rigour.py) — exploration of the θ_23 P_2 rigour gap; finds the original framing inverted.

**What's known and now derived:**

- Empirical rule: `k = 2 · #{Bott periods spanned by descent path}` for Amplitude observables. Verified 3/3 on the closed observables θ_C (k=2), b/s (k=4), θ_23 (k=4) under the Part IVb `n = d-1` indexing convention.
- **Per-period chi² multiplicity (DERIVED).** Adams' J-homomorphism `im J: π_n(O) → π^s_n` has exactly two free Z_2 direct factors per Bott period of 8, at residues n ≡ 0, 1 (mod 8), corresponding to the Stiefel–Whitney classes w_1 ∈ KO^1 (orientation) and w_2 ∈ KO^2 (spin) of the cascade tangent bundle. These generator layers sit at d = 8n + 1 (w_1) and d = 8n + 2 (w_2) — distinct from the Dirac residue d mod 8 = 5.
- **Cascade scalar action is sector-symmetric (DERIVED).** S[φ] = Σ(2α(d))⁻¹(Δφ)² is invariant under (w_1, w_2) flips: φ(d) = ln Ω_d carries no bundle data; α(d) = R(d)²/4 is a Γ-ratio with no spin structure; the slicing measure (1-x²)^{d/2} is even in x; and SO(d) volume is identical under both spin lifts on a sphere. Each of the χ²ᴺ patterns therefore carries equal Boltzmann weight.
- **Per-case anchoring tabulated (NEW finding from `cascade_channel_count_p2_rigour.py`).** Of the five period-by-period selections, two are DIRECT (generator layers in path) and three are INHERITED (generator layers outside path; selection extends from period's Dirac layer):

    | observable | period | path | (w_1, w_2) gens | Dirac in period | anchoring |
    |---|---|---|---|---|---|
    | θ_C | P_1 | d=12..13 | d=9, d=10 | d=13 | INHERITED |
    | b/s | P_0 | d=6..13 | d=1, d=2 | d=5 | INHERITED |
    | b/s | P_1 | d=6..13 | d=9, d=10 | d=13 | **DIRECT** |
    | θ_23 | P_1 | d=12..20 | d=9, d=10 | d=13 | INHERITED |
    | θ_23 | P_2 | d=12..20 | d=17, d=18 | d=21 (outside path) | **DIRECT** |

- **Global (w_1, w_2) = (+, +) convention (DERIVED + LABELLING).** Both DIRECT and INHERITED cases reduce to the same two cascade-internal forcings:
  - **w_1 = + universally derived** by the slicing recurrence's preferred direction (high-d → low-d as descent from B^∞).
  - **w_2 = + universally a labelling convention** parallel to the Standard Model's "matter is left-handed under SU(2)_L" — zero observational input per Part IVb `rem:cpt-balance-basins` (basins are CPT-conjugate, either is "matter" under suitable relabelling).
- **Per-period anchoring is bookkeeping.** Both DIRECT and INHERITED cases evaluate the cascade observable at the global (+, +) pattern, picking up factor 1/χ² per spanned period.

**Why the original framing was wrong:**

The earlier ROADMAP framing called θ_23 P_2 "structurally weaker (no Dirac layer crossed)." This was based on the assumption that Dirac-anchoring is more rigorous than non-Dirac-anchoring. But the (w_1, w_2) generators are NOT at Dirac layers (residue 5 mod 8); they sit at residues 0, 1 mod 8. In θ_23 P_2's path d=17..20, both generators (d=17, d=18) are directly in the path; in θ_C P_1's path d=12..13, neither generator (d=9, d=10) is in the path. Under the corrected analysis, θ_23 P_2 is one of the two MOST directly anchored cases, alongside b/s P_1.

**What remains open:**

- (b) **Formal completeness proof.** That no higher-order tangent-bundle structure (e.g., p_1 ∈ KO^4 = Z) activates additional Z_2 selectors at the integer-d Bott lattice points. Conjecture: KO^4 = Z is a free abelian factor at residue n ≡ 3 (mod 8), not a Z_2 chirality filter, and contributes to source strength (roadmap #3) rather than to channel count. Closing this requires explicit enumeration of im J's Z_2 generators across the Bott periods touched by cascade descent paths and verification that no other structure activates.

**Most tractable path forward:**

(b) is the longer-pole item; closing it requires an explicit cascade-internal calculation excluding higher KO classes from the channel count.

**Implications if (b) closes:**

Promotes the channel-count rule to a theorem, joining the chirality theorem χ^(m-k) (Part IVb thm:chirality-factorisation) and the source-selection bijection (Part IVb prop:source-selection) as the three structural rules governing the entire α(d*)/χ^k correction family.

### 2. Source-selection rule — categorical derivation pending

**Status:** Bijection 4 types ↔ 4 non-sink distinguished layers verified 9/9. The three syntactic flags (P, L, G) are mechanical queries on cascade formulas. Categorical derivation of the flags from a formal category of cascade observables is open.

See Part IVb Proposition `prop:source-selection` and the open question `oq:source-selection-category`.

### 3. Source strength — unit normalisation derivation pending

**Status:** Each observable's leading deviation matches `±α(d*)/χ^k` with unit source strength (no fitted prefactor). Why magnitude exactly 1 — i.e., why the source coefficient is exactly α(d*) at distinguished layers — has not been derived from cascade primitives. Conjectured to follow from the Wronskian normalisation of the cascade Green's function on the layer lattice.

### 4. Sign rule — Morse-index conjecture

**Status:** Each closure has a definite ± sign matching the descent-vs-geometric population of its leading deviation. Conjectured: sign = (−1)^(Morse index of Q on the cascade configuration space). Not proved.

The closed-form Green's function on the cascade lattice (now available — see ROADMAP entry on Bott decomposition) makes this computation tractable: 8 existing observables give 8 sign constraints on the Morse index.

### 5. Lighter neutrino masses, solar Δm², PMNS — different mechanism needed

**Status:** Heaviest neutrino mass closes at −0.4% via the m_29 chain. Lighter masses in the diagonal cascade form give m_2 ≈ 3×10⁻⁴ eV, undershooting the observed solar splitting √Δm²_sol = 8.6×10⁻³ eV by factor ~800. Cabibbo-template extended to PMNS_12 gives 7.5° vs observed 33.4° — wrong by factor 4.5.

**Genuine open structural piece:** a cascade-internal derivation of neutrino-sector mixing yielding (a) large θ_12, θ_23, (b) small θ_13, (c) magnitude Δm²_sol. The CKM and PMNS sectors require structurally different mechanisms.

See Part IVb open question on PMNS and `tools/research/cascade_pmns_solar_splitting.py` for the partial-negative tests on existing cascade ingredients (Gram, geometric-mean, χ-factor).

### 6. Up-type quark masses — Weyl chirality factor at SU(3) layer

**Status:** Tier 4 in PREDICTIONS.md. The relation (t/b)/(c/s) ≈ N_c = 3 is empirically suggestive but the Weyl chirality coupling at d=12 (SU(3) algebra layer) has not been computed.

**Most tractable path:** compute the Weyl chirality factor on S^11 explicitly. Closing this would derive 3 quark masses at once.

### 7. CP-violation — structurally outside cascade scope

**Status:** The cascade is structurally CPT-symmetric in audited primitives. CKM δ_CP and PMNS δ_CP enter as external observational input, parity with SM treatment. Same epistemic status as the SM's Q_e = −1 convention.

θ_13 closes conditional on the standard SM treatment of CP-violation: cascade structurally derives |V_ub| = |V_us|·|V_cb|; observed deviation matches the Wolfenstein factor √(ρ²+η²) to 3% (Part IVb Remark `rem:theta13-cp`).

### 8. Cosmology primordial spectrum — Tier 5

**Status:** n_s, A_s not derived. The cascade has a native perturbation source (per-layer Gram deficit, Part 0 §12), but quantitative match to the observed primordial spectrum is fuzzy at current precision. r is qualitatively suppressed; magnitude open. See Part VI.

### 9. Ω_b derivation — needs strengthening

**Status:** Tier 5 in PREDICTIONS.md. The "one unit of content on S³" argument for Ω_b = 1/(2π²) needs structural strengthening. Interpretive, not a missing derivation chain.

## Closed in this development cycle

### θ_23 (CKM mixing angle 2↔3)

**Closure:** +0.005σ from PDG via cascade Cabibbo template extended through the gauge window and across the cascade phase-transition threshold d_1=19, with source-selection shift −α(7)/χ⁴.

**Formula:**
```
tan θ_23 = tan(arccos(N(13)/N(12))) · exp(−Σ_{d=13}^{20} p(d)/2) · exp(−α(7)/χ⁴)
         = 2.380°
```

**Source assignment:** Amplitude type → d_0 = 7 by Proposition `prop:source-selection` (9/9 verified).

**Channel count k = 4:** descent path d=12..20 spans Bott periods {P_1, P_2}; rule `k = 2 · #periods` gives k=4.

**Documented in:** Part IVb Theorem `thm:theta23-closure`, PREDICTIONS.md Tier 3, this roadmap.

## Working principles

- **Tier discipline.** Every result carries its tier. Tier 5 (provisional) is explicitly not sufficient for the cascade to claim a prediction.
- **No semiclassical machinery.** Per CLAUDE.md Check 7: no QFT on curved spacetime, no Bogoliubov, no Kaluza–Klein, no semiclassical sphere Green's functions or quantum effective potentials. Cascade-native procedures only.
- **Falsifiability.** Every roadmap entry that proposes a closure mechanism must specify what would falsify it.
- **Acknowledged-vs-novel categorisation.** Defects already acknowledged in CLAUDE.md or PREDICTIONS.md Tier 5 are not new findings. Only novel structural gaps count.
