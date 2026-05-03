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

**Empirical coverage (after the 3-period investigation):**

The rule is confirmed at k=2 (1 observation: θ_C) and k=4 (2 observations: b/s, θ_23). It is **untested at k=6** (3-period Amplitudes): no current SM observable maps cleanly to that slot. The investigation in [`tools/research/cascade_3period_amplitudes.py`](tools/research/cascade_3period_amplitudes.py) tested six plausible 3-period descent paths against four candidate observables (|V_ub|, |V_td|, PMNS θ_13, PMNS θ_12). Best match was |V_ub| at path d=12..28 with ratio 0.72 (cascade prediction 0.158° vs observed 0.219°) — outside the cascade's standing precision. Three structural reasons the slot is empty:

- (i) CKM cross-generation observables (V_ub, V_td) close via the standard multiplicative CKM closure |V_ub| = |V_us|·|V_cb| in a CPT-symmetric setting; the deviation matches the Wolfenstein CP factor as external observational input (Part IVb `rem:theta13-cp`). No direct cascade Amplitude with 3-period descent.
- (ii) PMNS sector tested partial-negative on existing cascade ingredients (Roadmap #5); 3-period predictions also miss observed PMNS θ_13 by factor ~7–8.
- (iii) Cross-3-generation mass ratios (m_τ/m_e) are derived as products of 1-period ratios (k=1+1=2 single-period contributions), not as a direct 3-period Amplitude with k=6.

**Most likely future tests:** PMNS sector extension (Roadmap #5), up-type quark masses (Roadmap #6), or any newly-derived cascade Amplitude with 3-period descent. The empty slot at k=6 is not evidence against the rule — it's evidence that the cascade's natural Amplitude structure (gauge-window starting angle, descent terminating at d_1+1 or at a generation layer) doesn't naturally generate 3-period descents in the SM sector.

**Connection to other roadmap items:**

The cyclic-of-order >2 generators (Z_24 at residue 3 mod 8, Z_240 at residue 7 mod 8) detect integer-valued Pontryagin classes p_1, p_2 of the cascade tangent bundle. These contribute to:
- **Source strength** (roadmap #3): Pontryagin numbers at distinguished source layers d* could fix the unit-1 normalisation of α(d*).
- **Sign rule** (roadmap #4): Pontryagin classes contribute to the Morse index of Q on the cascade configuration space, conjectured to govern the +/- sign in ±α(d*)/χ^k.

The completeness theorem **forces** these contributions to live outside the chirality factor; they're separate structural ingredients in the cascade observable's full prediction.

**Implications:**

The channel-count rule is now a theorem of the cascade. Combined with the chirality theorem χ^(m-k) (Part IVb thm:chirality-factorisation, extended in `cascade_chirality_theorem.py`) and the source-selection bijection (Part IVb prop:source-selection), three structural rules govern the entire α(d*)/χ^k correction family at theorem level.

**Soft spots (caveats on the proof's rigour level):**

The completeness proof is at the same rigour level as other Part IVb Tier 2 structural arguments — not a fully formalised mathematical theorem in the measure-theoretic sense. Four explicit caveats:

- **(SS1) Cascade path-integral not formally defined.** Lemma 3's activation criterion treats path-integral multiplicities as arising from action-symmetry orbits — the standard physics heuristic. Tightening would require formal definition of `∫ exp(-S[φ]) Dφ` as a measure-theoretic object on the cascade configuration space. The cascade scalar action (Part IVb Remark 4.6) is a discrete-elastic-action proposal, not yet a formal path-integral theory.
- **(SS2) Lemma 1 not exhaustive over arbitrary group actions.** Multiplicative actions `φ → ωφ` and layer permutations are excluded; exotic non-multiplicative actions (twist actions, non-linear field redefinitions) are excluded by structural argument rather than full classification of the cascade scalar action's automorphism group.
- **(SS3) Magnitude vs labelling distinction.** The theorem forces the chirality-factor MAGNITUDE to be exactly χ^{2N}. It does NOT determine which specific (w_1, w_2) pattern the observable evaluates at. The global (+, +) convention is a labelling parallel to the SM's "matter is left-handed under SU(2)_L" convention (Part IVb `rem:cpt-balance-basins`, zero observational input). Empirical k = 2N tests the magnitude only.
- **(SS4) Connection to items #3, #4 is structural, not derived.** The completeness theorem says higher cyclic groups (Z_24, Z_240) at residues 3, 7 mod 8 contribute to source strength and sign rather than to the chirality factor. *How* they contribute — whether Pontryagin numbers fix the source's unit normalisation or the +/- sign via Morse index — remains open as roadmap items #3 and #4.

These soft spots don't undermine the theorem's content; they delimit the rigour level. Tier 2 promotion is consistent with this rigour level (matches the Tier 2 entries for α_s, m_τ/m_μ, sin²θ_W, Ω_m, etc., all of which rely on the same-level structural arguments).

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

### 6. Up-type quark masses — substantial progress (full quark hierarchy in 4 cascade quantities + 1 anchor)

**Status:** Going deeper than the original (t/b)/(c/s) = N_c hint, the FULL six-quark mass hierarchy now follows from FOUR cascade-natural structural quantities plus one absolute anchor. Two NEW structural relations identified, both within cascade standing precision. The Weyl chirality factor at d=12 — the proposed structural mechanism — has not been computed; closing it would promote five quark masses to Tier 2.

**Verifiers:**
- [`tools/research/cascade_uptype_quarks.py`](tools/research/cascade_uptype_quarks.py) — initial up-type investigation (m_top, m_c, m_u).
- [`tools/research/cascade_quark_hierarchy_full.py`](tools/research/cascade_quark_hierarchy_full.py) — full six-quark hierarchy with two new relations.

**The four cascade structural quantities:**

1. **b/s = -α(7)/χ⁴ = 44.7436** (cascade Tier 2 closure, theorem-level via channel-count rule).
2. **s/d = Ω_3 = 2π² ≈ 19.74** (NEW, -1.30% match). Down-quark Gen 2 → Gen 1 step IS the observer's spatial S^3 area.
3. **(t/b)/(c/s) = N_c = 3** (Roadmap #6 hint, -1.26% match). Up-down asymmetry at Gen 3 → Gen 2 step.
4. **(c/s)/(u/d) = N_c · π² ≈ 29.61** (NEW, -0.71% match). Up-down asymmetry at Gen 2 → Gen 1 step.

Plus one anchor: m_b empirical (or m_top = v_cas/√2 via cascade v + SM y_top = 1).

**Combined: c/u = N_c · π² · Ω_3 = 6π⁴ ≈ 584.45** (-0.60% match).

**All six quark masses match to standing precision (0.0% – 1.4%):**

| observable | cascade | observed | dev | route |
|---|---|---|---|---|
| m_top | 170.27 GeV | 172.69 GeV | -1.40% | v_cas/√2 (SM y_top=1) |
| m_c | 1.2685 GeV | 1.27 GeV | -0.12% | m_top/(N_c·b/s) |
| m_u | 2.170 MeV | 2.16 MeV | +0.48% | m_c/(6π⁴) |
| m_b | 4.18 GeV | 4.18 GeV | (input) | empirical |
| m_s | 93.42 MeV | 93.4 MeV | +0.02% | m_b/(b/s) |
| m_d | 4.733 MeV | 4.67 MeV | +1.34% | m_s/Ω_3 |

**What's structurally going on:**

The up-down asymmetry GROWS by π² between consecutive generation steps:
- Gen 3 → Gen 2: asymmetry factor N_c.
- Gen 2 → Gen 1: asymmetry factor N_c · π².

The π² = Ω_3/2 = HALF the observer's spatial S^3 area. Cascade-internal: as the cascade descent approaches the observer (Gen 1 = d=21, deepest fermion layer), the observer's spatial slice Ω_3 becomes progressively more relevant. Equivalent forms: π² = 4·Ω_5/Ω_2 (cascade ratio at volume maximum and observer equator); π² = 4·N(2)² (cascade lapse at d=2). The cleanest structural reading is π² = Ω_3/2.

**What would promote these to Tier 2 (theorem level):**

1. **Cascade-internal derivation of (t/b)/(c/s) = N_c.** Promotes m_c to Tier 2. Roadmap #6's original target — Weyl chirality factor at d=12 (Spin(12) = Spin(4)^⊗3 decomposition).
2. **Cascade-internal derivation of s/d = Ω_3.** Promotes m_d to Tier 2. Likely involves cascade descent through the observer's S^3 slice.
3. **Cascade-internal derivation of (c/s)/(u/d) = N_c·π².** Promotes m_u to Tier 2 (combined with 1+2). The π² growth between asymmetry steps is the new structural target.
4. **Cascade-internal derivation of y_top = 1.** Promotes m_top to Tier 2.

All four point to the SU(3) layer at d=12 and the observer's spatial S^3 (Ω_3) as the cascade-internal sources. Roadmap #6's "compute the Weyl chirality factor on S^11 explicitly" is the proposed unified mechanism — closing it should derive all four relations simultaneously.

**Most tractable path forward:** the s/d = Ω_3 finding gives a concrete structural toehold. The down-quark Gen 2 → Gen 1 step matches the observer's S^3 area to -1.3%. If this is derived cascade-internally (e.g., from descent through the observer's spatial slice between d=13 Gen 2 layer and d=21 Gen 1 layer), the rest of the structural pattern (π² growth in up-down asymmetry, etc.) likely follows by the same mechanism applied at the SU(3) layer.

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
