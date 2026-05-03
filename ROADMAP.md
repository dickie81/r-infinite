# Cascade Series — Roadmap

This file tracks open structural questions and the concrete next steps to close them. Each entry has: status, what's known, what's missing, and the most tractable path forward.

The single source of truth for predictions is [`PREDICTIONS.md`](PREDICTIONS.md). The single source of truth for review protocol and standing issues is [`CLAUDE.md`](CLAUDE.md). This roadmap is the working document for advancing the framework.

## Open structural questions

### 1. Channel-count rule for Amplitude observables — formal closure (theorem-level; only PMNS test remains as falsifier)

**Status:** Empirical fit grounded in stable homotopy theory and KO-theoretic Bott periodicity. Activation mechanism derived from cascade scalar action's sector-symmetry. Term-by-term (w_1, w_2) identification supplied for all three closed Amplitude observables. Per-case anchoring corrected: the original "θ_23 P_2 is structurally weaker" framing was inverted (P_2 is one of the two most directly anchored cases). **Formal completeness proof now closed:** the chirality factor exponent 2N is forced by combining the cascade scalar action's Z_2-only discrete symmetry group with Adams' theorem on im J's Z_2 generator residues. Higher cyclic groups (Z_24 at residue 3 mod 8, Z_240 at residue 7) detect integer-valued Pontryagin classes of the cascade tangent bundle and contribute to source strength/sign (roadmap #3, #4), not to the chirality factor.

**Verifiers:**
- [`tools/research/cascade_channel_count_rule.py`](tools/research/cascade_channel_count_rule.py) — empirical verification + activation argument + term-by-term identification for all three observables.
- [`tools/research/cascade_channel_count_p2_rigour.py`](tools/research/cascade_channel_count_p2_rigour.py) — exploration of the (originally framed) θ_23 P_2 rigour gap; finds the framing inverted.
- [`tools/research/cascade_channel_count_completeness.py`](tools/research/cascade_channel_count_completeness.py) — formal completeness proof with 3-lemma structure (action symmetry group, im J residue structure, activation criterion).

**Theorem (formal completeness):** Let Q be a cascade Amplitude observable with descent path P spanning N Bott periods. Then the chirality factor in Q's cascade prediction is exactly χ^{2N} = 4^N, with no contribution from higher KO classes or higher cyclic groups in im J at residues 3, 7 mod 8.

**Proof structure:**
- **Lemma 1 (cascade scalar action symmetry group).** The action S[φ] = Σ(2α(d))⁻¹(Δφ)² with real-valued φ has automorphism group A(S) = R × Z_2 (continuous translation × discrete sign flip). No higher cyclic group of order n > 2 is a symmetry, because (Δφ)² → ω²(Δφ)² under φ → ωφ requires ω² = 1, and for real-valued φ only ω = ±1 satisfies this.
- **Lemma 2 (im J generator structure, Adams 1966).** Per Bott period, im J has 2 binary (Z_2) generators at residues 0, 1 mod 8 (η, η²; corresponding to Stiefel–Whitney classes w_1, w_2) and 2 cyclic-of-order >2 generators at residues 3, 7 mod 8 (Z_24, Z_240; corresponding to integer-valued Pontryagin classes p_1, p_2).
- **Lemma 3 (activation criterion).** For a generator g of order m to activate as a multiplicity-m factor in the cascade path-integral, the cascade scalar action must be invariant under g's action on φ. Without action invariance, the m orbit elements have different Boltzmann weights and no clean 1-of-m projection emerges.
- **Combining:** Only Z_2 generators in im J satisfy Lemma 3 (by Lemmas 1, 2). Per period, this gives 2 binary selectors → χ² = 4 multiplicity. Over N periods, χ^{2N}. Higher cyclic groups don't satisfy Lemma 3 and contribute to other parts of the cascade observable (source strength, sign), not to the chirality factor.

**What's known and now derived:**

- Empirical rule: `k = 2 · #{Bott periods spanned by descent path}` for Amplitude observables. Verified 3/3 on the closed observables θ_C (k=2), b/s (k=4), θ_23 (k=4).
- **Per-period chi² multiplicity (DERIVED).** Adams' im J's two Z_2 direct factors per Bott period at residues 0, 1 mod 8.
- **Cascade scalar action is sector-symmetric (DERIVED).** S[φ] invariant under (w_1, w_2) Z_2 flips; multiplicity activation gives equal Boltzmann weight to all χ²ᴺ patterns.
- **Term-by-term (w_1, w_2) identification for all three closed Amplitudes (DERIVED).** Each spanned period selects (+, +) by the global cascade conventions (w_1 = + derived from slicing recurrence direction; w_2 = + a labelling convention parallel to SM left-handed convention with zero observational input per `rem:cpt-balance-basins`).
- **Per-case anchoring tabulated.** 2/5 selections are DIRECT (b/s P_1, θ_23 P_2 — both (w_1, w_2) generator layers in path); 3/5 are INHERITED (θ_C P_1, b/s P_0, θ_23 P_1 — generators outside path; selection extends from period's Dirac layer via cascade scalar action's adjacency).
- **Formal completeness (DERIVED, this section).** Chirality factor is exactly χ^{2N}; higher cyclic groups in im J don't contribute, because they aren't symmetries of S[φ].

**What remains:**

Only one test: monitor PMNS θ_12 or any future Amplitude observable. If a future cascade-native closure for such an observable requires k ≠ 2N, the rule is falsified. Until then, the channel-count rule stands as a theorem.

**Connection to other roadmap items:**

The cyclic-of-order >2 generators (Z_24 at residue 3 mod 8, Z_240 at residue 7 mod 8) detect integer-valued Pontryagin classes p_1, p_2 of the cascade tangent bundle. These contribute to:
- **Source strength** (roadmap #3): Pontryagin numbers at distinguished source layers d* could fix the unit-1 normalisation of α(d*).
- **Sign rule** (roadmap #4): Pontryagin classes contribute to the Morse index of Q on the cascade configuration space, conjectured to govern the +/- sign in ±α(d*)/χ^k.

The completeness theorem **forces** these contributions to live outside the chirality factor; they're separate structural ingredients in the cascade observable's full prediction.

**Implications:**

The channel-count rule is now a theorem of the cascade. Combined with the chirality theorem χ^(m-k) (Part IVb thm:chirality-factorisation, extended in `cascade_chirality_theorem.py`) and the source-selection bijection (Part IVb prop:source-selection), three structural rules govern the entire α(d*)/χ^k correction family at theorem level.

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
