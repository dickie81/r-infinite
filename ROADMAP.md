# Cascade Series — Roadmap

This file tracks open structural questions and the concrete next steps to close them. Each entry has: status, what's known, what's missing, and the most tractable path forward.

The single source of truth for predictions is [`PREDICTIONS.md`](PREDICTIONS.md). The single source of truth for review protocol and standing issues is [`CLAUDE.md`](CLAUDE.md). This roadmap is the working document for advancing the framework.

## Open structural questions

### 1. Channel-count rule for Amplitude observables — partial structural closure

**Status:** Empirical fit grounded in stable homotopy theory and KO-theoretic Bott periodicity. Activation mechanism articulated. Formal sector-projection identification remains open.

**What's known:**

- Empirical rule: `k = 2 · #{Bott periods spanned by descent path}` for Amplitude observables. Verified 3/3 on the closed observables θ_C (k=2), b/s (k=4), θ_23 (k=4).
- Structural source: Adams' J-homomorphism `im J: π_n(O) → π^s_n` has exactly two free Z_2 direct factors per Bott period of 8, at residues n ≡ 0, 1 (mod 8). The cyclic groups at residues 3, 7 (Z_24, Z_240, …) are not direct Z_2 factors and don't contribute clean binary chirality filters.
- Identification: the two Z_2 generators per period correspond to the Stiefel–Whitney classes w_1 ∈ KO^1 (orientation) and w_2 ∈ KO^2 (spin) of the cascade tangent bundle. Cascade chirality basin selection (from Poincaré–Hopf χ(S^{2n}) = 2) is the orientation Z_2.
- Activation mechanism: cascade scalar action S[φ] = Σ(2α(d))⁻¹(Δφ)² is sector-symmetric (the scalar field carries no tangent-bundle data), so each (w_1, w_2) pattern over N Bott periods carries equal weight in the path-integral measure. An Amplitude observable selecting one specific pattern picks up sector-selectivity factor 1/χ^{2N}.

**What's missing:**

The formal proof that each Amplitude cascade formula is a 1-of-χ^{2N} sector projection. Specifically:
- (a) Cabibbo formula `tan(arccos(N(13)/N(12)))·exp(-p(13)/2)` encodes a specific (w_1, w_2) choice in P_1.
- (b) b/s formula `(m_τ/m_μ)·e` encodes specific (w_1, w_2) choices in both P_0 and P_1.
- (c) Extended Cabibbo descent for θ_23 encodes specific (w_1, w_2) choices in P_1 and P_2.

For each, the proof requires writing out the cascade formula's topological content explicitly: boundary conditions of the slicing kernel f_d(x) = (1-x²)^{d/2}, chirality basin selected at the gauge-window edge, spin structure inherited.

**Most tractable path forward:**

Identify each cascade Amplitude formula's topological coupling term-by-term. The empirical match at χ^{2N} tells us the projection structure is real; the work is identifying which specific (w_1, w_2) pattern each formula selects. Estimated effort: weeks of focused research, not a single computation.

**Implications if closed:**

Promotes the channel-count rule from "Tier 3 (numerical)" to a theorem, closing all three Amplitude observables (θ_C, b/s, θ_23) at the same forcing level as the four Gauge/Absolute/Observer-type closures.

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
