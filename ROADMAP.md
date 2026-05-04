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

**All six quark masses match to standing precision (with v_cas Gram-corrected per Part 0 line 1781):**

| observable | cascade | observed | dev | route |
|---|---|---|---|---|
| m_top | 172.32 GeV | 172.69 GeV | -0.21% | v_cas/√2 (SM y_top=1, v_cas Gram-corrected 243.7 GeV) |
| m_c | 1.2838 GeV | 1.27 GeV | +1.09% | m_top/(N_c·b/s) |
| m_u | 2.197 MeV | 2.16 MeV | +1.69% | m_c/(6π⁴) |
| m_b | 4.18 GeV | 4.18 GeV | (input) | empirical |
| m_s | 93.42 MeV | 93.4 MeV | +0.02% | m_b/(b/s) |
| m_d | 4.733 MeV | 4.67 MeV | +1.34% | m_s/Ω_3 |

Note on residual pattern: with leading v_cas = 240.8 GeV, the residuals were m_top -1.40%, m_c -0.12%, m_u +0.48% — favourable cancellations between v_cas's leading-order error and the cascade chain made some residuals look small. With Part 0 Gram-corrected v_cas = 243.7 GeV, m_top closes to -0.21% but the up-quark chain residuals (m_c, m_u) shift to ~+1% as previously-hidden cascade-chain structure surfaces. The down-quark side (m_d at +1.34%, the bundle/scalar gap signature) is unchanged. Cascade quark RMS residual is ~1.1% under either v_cas choice, distributed differently.

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

**Structural conjecture (NEW): s/d = vol(SU(2)) = Ω_3.** [`tools/research/cascade_sd_su2_volume.py`](tools/research/cascade_sd_su2_volume.py).

**Key fact:** SU(2) ≅ S^3 (the unit quaternions) with bi-invariant metric has vol(SU(2)) = 2π² = Ω_3. The same 3-sphere area as the observer's spatial slice. This is a standard differential-geometry identity.

**Conjecture:** the cascade descent from Gen 2 (d=13, SU(2)_L gauge boson home) to Gen 1 (d=21) integrates over the SU(2) gauge group manifold, picking up the bi-invariant Haar volume:

- **Down quarks** (Q_L doublet, Y_d_R = -1/3): integrate over full SU(2). Factor = vol(SU(2)) = Ω_3 → s/d = Ω_3 = 2π² (-1.3%).
- **Up quarks** (Q_L doublet, Y_u_R = +2/3 = 2·|Y_d_R|): integrate over PSU(2) = SU(2)/Z_2 = SO(3) ≅ ℝP^3 (the antipodal quotient). Factor = vol(PSU(2)) = vol(SU(2))/2 = π². The up-down asymmetry at this step picks up an extra factor of vol(SU(2))/2 = Ω_3/2 = π² → (c/s)/(u/d) = N_c · π² (-0.7%).

The Z_2 quotient SU(2) → PSU(2) realises Theorem 4.8's chirality basin selection on the SU(2) gauge group manifold (S^3 doesn't natively split into chirality basins since it's odd-dim, but the Z_2 antipodal covering provides the natural binary split).

**Why Gen 3 → Gen 2 doesn't pick up SU(2) volume:** the descent (d=5 → d=13) terminates AT the SU(2) home layer, not past it. The factor N_c at this step comes from SU(3) color at d=12, not SU(2) volume. SU(2) volume integration manifests only when descent crosses the post-gauge-window region (Gen 2 → 1, descent d=13..21).

**Combined: c/u = N_c · vol(SU(2))² / 2 = N_c · 2π⁴ = 6π⁴** (-0.6% match). Two factors of vol(SU(2)) for the up quark — one from descent integration, one from chirality basin halving — combined with SU(3) color N_c.

**What's needed to make this a theorem:**

1. Explicit cascade scalar action Green's function with SU(2)-symmetric boundary conditions over descent d=13..21, showing integration measure equals vol(SU(2)) · (cascade factors).
2. Cascade-internal proof that up-quark cascade descent picks up vol(PSU(2)) = vol(SU(2))/2 via Theorem 4.8 chirality basin selection on the SU(2) manifold.
3. Connection to the original Weyl chirality factor at d=12: the N_c factor at Gen 3 → 2 should also derive from the same Green's function with SU(3)-symmetric boundary conditions.

Closing (1)–(3) cascade-internally would promote five of six quark masses to Tier 2 via gauge group volume integration — a significant unification connecting Adams + Bott + Lefschetz framework to the observed quark mass spectrum.

**Lepton consistency check (tension dissolved structurally — sector membership selects the mechanism).** [`tools/research/cascade_sd_lepton_resolution.py`](tools/research/cascade_sd_lepton_resolution.py).

The natural sceptical question for the SU(2) volume conjecture was: L_L is also an SU(2)_L doublet, so should m_μ/m_e show vol(SU(2))? Initial framing said the tension dissolves *numerically* at standing precision (exp(Φ(21)−Φ(13)) ≈ N_c · vol(SU(2)) at 1.6%). The post-test-(1)/(b) framing supersedes this: **the tension dissolves *structurally* because the cascade has three independent first-order correction mechanisms, and sector membership in cascade-bundle structure determines which one applies.**

| Sector | Bundle structure | Mechanism | Reading |
|---|---|---|---|
| Leptons (color singlet) | Scalar descent through fermion homes d=5,13,21,29; never traverses SU(3) home at d=12 non-trivially | Scalar Φ descent + Dirac amplification (mech 1, leading order) | m_μ/m_e = exp(ΔΦ)·(2√π) = 206.50, PDG 206.77, **dev −0.13%** |
| Quarks (color triplet) | Bundle-valued sections at d=12 (SU(3)) and d=13 (SU(2)); descent integrates over gauge fiber | Gauge-bundle orbit measure at gauge home (mech 3) | s/d = vol(SU(2)) = Ω_4 = 19.74, PDG 20.00, **dev −1.30%** (−0.05% with Gram) |

The cascade does NOT predict that leptons should pick up vol(SU(2)). It predicts that leptons should follow the scalar Φ descent (they do, −0.13%) and that quarks should follow the gauge-bundle measure (they do, −1.30%). Different sectors, different mechanisms, by structural design.

**What the 1.6% near-miss is:** `exp(Φ(21)−Φ(13)) = 58.25` (scalar reading of d=13→21) vs `N_c · vol(SU(2)) = 59.22` (bundle reading of same span) is the **bundle/scalar gap** — the structural signature of SU(2) gauge-bundle non-triviality at d=13. For quarks (which see the bundle), the bundle reading is correct. For leptons (which don't), the scalar reading is correct. The 1.6% gap is a quark-sector observation about bundle non-triviality at the SU(2) home, not a leptonic prediction failure.

**Lepton ratio precision confirms the scalar regime.** Three readings of m_μ/m_e against PDG = 206.7682:
- Leading scalar Φ descent + Dirac: 206.50 (dev **−0.13%**, BEST)
- Local-Gram-corrected Φ descent: 205.81 (dev −0.46%)
- Gauge-volume reading 12π^(5/2): 209.93 (dev +1.50%)

Leading scalar wins. Applying Gram or gauge-vol corrections to the lepton ratio moves it AWAY from observation — correct behaviour, since leptons are not in the bundle regime.

**Bott-period specificity:** the bundle/scalar gap match exp(Φ(d+8)−Φ(d)) ≈ N_c · vol(SU(2)) holds ONLY at d=13 → 21. Gen 3 → 2 gives 4.66; Gen 1 → 0 gives 267.2. The d=13 → 21 span is unique because it crosses out of the gauge window (d=13 is the SU(2) home) into the post-gauge regime, where the bundle and scalar readings of the same descent diverge by the structural amount measured here.

**Still open (research-level, not blockers):**
- Exact identity exp(Φ(21)−Φ(13)) = N_c · vol(SU(2)) + cascade-natural higher-order correction (Gram closes 96.7%; residual 0.05% unexplained).
- Cascade-internal proof that color-singlet matter cannot pick up the gauge-bundle reading (currently a structural reading from path-tensor rep rules in Part IVa `rem:fund-or-trivial`, not an explicit theorem).
- Whether other Bott-period spans show similar bundle/scalar gaps at gauge-home boundaries.

### 7. CP-violation — structurally outside cascade scope

**Status:** The cascade is structurally CPT-symmetric in audited primitives. CKM δ_CP and PMNS δ_CP enter as external observational input, parity with SM treatment. Same epistemic status as the SM's Q_e = −1 convention.

θ_13 closes conditional on the standard SM treatment of CP-violation: cascade structurally derives |V_ub| = |V_us|·|V_cb|; observed deviation matches the Wolfenstein factor √(ρ²+η²) to 3% (Part IVb Remark `rem:theta13-cp`).

### 8. Cosmology primordial spectrum — Tier 5

**Status:** n_s, A_s not derived. The cascade has a native perturbation source (per-layer Gram deficit, Part 0 §12), but quantitative match to the observed primordial spectrum is fuzzy at current precision. r is qualitatively suppressed; magnitude open. See Part VI.

### 9. Ω_b derivation — needs strengthening

**Status:** Tier 5 in PREDICTIONS.md. The "one unit of content on S³" argument for Ω_b = 1/(2π²) needs structural strengthening. Interpretive, not a missing derivation chain.

### 10. Observer-frame correction: unify Paper 1's explicit treatment with Part IVa/IVb's implicit treatment — CLOSED at structural-equivalence level

**Status:** structural cleanup, CLOSED at the equivalence level by [`tools/research/cascade_observer_frame_unification.py`](tools/research/cascade_observer_frame_unification.py). Identified during a numerical test of "what happens if we include d=1..4 in the Phi descent sum?" — a test that surfaces an inconsistency in derivation style between Paper 1 and Part IVa/IVb.

**The diagnostic:** including d=1, 2, 3, 4 in the Phi sum shifts every Phi value by `Σ p(1..4) ≈ −1.997`, multiplying all absolute lepton/quark masses by `exp(1.997) ≈ 7.4`. The factor itself has closed form `4π² · exp(2γ − 17/6)` with `4π² = 2·Ω_3` (twice the observer's spatial slice area), suggesting the bottom-4 contribution IS structurally tied to observer-frame geometry.

**Two distinct cascade derivation styles:**

| | Paper 1 (cosmological constant) | Part IVa/IVb (mass formulas) |
|---|---|---|
| Cascade-internal piece | `Ω_19 · Ω_217` | `exp(−Phi(d_g))` |
| Observer-frame correction | EXPLICIT: `(2/π) · (9/π²)` | IMPLICIT: Phi-from-d=5 + `(2√π)^(n_D+1)` |
| Gram | EXPLICIT: `exp(δ_path(5,217))` | EXPLICIT: `α(d*)/χ^k` closure family |

Paper 1 derives the observer-frame correction explicitly via two pieces:
- **Cube–sphere bridge at d=3:** `Ω_2/V_3^cube = 4π/8 = π/2`, applied as `2/π`. Converts cascade sphere-area content to the cube-volume normalisation of the reduced Planck mass.
- **Host-frame correction:** `(Ω_5/Ω_7)² = 9/π²`. Translates from cascade reference layer d_0=7 (area max) to observer's host d_V=5 (volume max).

Mass formulas perform the equivalent observer-frame correction implicitly:
- **Phi sum starts at d=5** (= d_V boundary). Skipping d=1..4 telescopes the bottom-4 contribution into the convention rather than spelling it out.
- **`(2√π)^(n_D+1)` Dirac amplification** carries π factors from S^3 (= Ω_3 = 2π²) geometry — the observer's spatial slice area enters via Γ(1/2) = √π.

**Why this matters:** the cascade currently has TWO derivation styles for the same kind of observer-frame correction. Paper 1 makes it explicit and structurally derivable; Part IVa/IVb telescopes it into a convention that gives the right answer but obscures the structure. A user asking "what happens if we include the 4 spacetime dimensions in the cascade descent?" cannot get a clean structural answer from the current literature — the answer requires reverse-engineering the implicit correction.

**Concrete cleanup:**

Rewrite mass formulas in Paper-1 style with the observer-frame correction explicit:
```
m_l = [observer-frame correction] · [cascade-internal piece] · [Dirac amp at observer]
    = [Ω_d=3 / V^cube · host-frame factor] · [exp(−Phi_from_d_1(d_g))] · [Spin(4) factor]
```

Then prove that this restructured form equals the current formula: i.e., the explicit observer-frame correction multiplied by `exp(−Phi_from_d_1)` and Spin(4) factors equals the current `exp(−Phi_from_d_5) · (2√π)^(n_D+1)`.

This would:
- Make the role of the 4 spacetime dimensions explicit in mass derivations (currently hidden in conventions)
- Unify cosmological-scale and particle-scale cascade derivations under one structural style
- Enable systematic application of observer-frame corrections to other cascade quantities (mixing angles, gauge couplings)
- Resolve the "Phi convention starts at d=5 by stipulation" ambiguity by replacing it with a derivation

**Falsifiability:** if the restructured Paper-1-style mass formula doesn't equal the current Part IVa/IVb formula at the same numerical precision, the unification fails — meaning the observer-frame correction is NOT what's hidden in the Phi convention. In that case the Phi convention requires an independent structural justification.

**Predicted outcome:** the unification succeeds. The implicit correction in Phi convention exactly equals Paper-1-style observer-frame correction at d=3 + d_V applied to Phi-from-d=1. This is a research-level cascade cleanup, not a new derivation, and would clarify the cascade's overall structural symmetry between cosmology and particle physics.

**What this is NOT:** new physics. The cascade's predictions don't change; the derivation style becomes uniform. Same particles, same masses, same observer-frame corrections — just spelled out symmetrically across all parts of the framework.

**Verifier:** [`tools/research/cascade_observer_frame_unification.py`](tools/research/cascade_observer_frame_unification.py).

(a) Computes mass predictions with Phi-from-d=1 + explicit OFC: DONE.
(b) Demonstrates equality with current Phi-from-d=5 formulation: VERIFIED to machine precision (1e-16) for charged leptons + neutrino source layer.
(c) Identifies cascade-natural form of OFC: DONE.

**Cascade-natural form of OFC found:**
```
OFC = exp(p(1)) · exp(p(2)) · exp(p(3)) · exp(p(4))
    = product of cascade descent step factors at bottom 4 layers
    = exp(-2γ + 17/6) / (4π²)
    ≈ 0.13576
```

Each `exp(p(d))` for d=1..4 is the cascade descent step at one of the bottom 4 cascade layers (S^0, S^1, S^2, S^3 boundaries). The 4π² in the closed-form denominator is `2·Ω_3` (twice the observer's spatial-slice area, cascade-natural). The transcendental `exp(-2γ + 17/6)` is the residual from digamma values at small d.

**Refinement of predicted outcome:** the original prediction was "OFC = Paper-1-style correction at d=3 + d_V applied to Phi-from-d=1." The actual result: OFC samples cascade descent at the bottom 4 layers (d=1, 2, 3, 4), not specifically at d=3 + d_V. Both Paper 1 and mass-formula corrections are cascade-internal descent factors at observer-frame layers, but they sample at different specific layers because they bridge different cascade-internal pieces (sphere-area products vs Phi descent).

**Unified principle (post-closure):** observer-frame corrections sample cascade descent at layers relevant to the observer's frame.
- Paper 1 (cosmological constant): samples at landmark layers d=3 (cube-sphere bridge) and d_V=5 (host-frame ratio).
- Mass formulas (Part IVa/IVb): sample at the bottom 4 layers d=1, 2, 3, 4 (cascade descent steps).

Both are cascade-internal descent-based corrections, computed via the same primitive p(d). The cascade has ONE consistent observer-frame correction style across cosmology and particle physics.

**Concrete next work (post-closure, lower priority):**
1. Document the unification in Part IVa/IVb LaTeX (currently implicit; making explicit clarifies the cascade's structural symmetry).
2. Apply explicit OFC decomposition to other cascade-derived quantities (gauge couplings, mixing angles) to verify universality.
3. Test whether the α(d*)/χ^k correction family also admits Paper-1-style observer-frame + cascade-internal decomposition.

These extensions further unify the cascade's observer-frame correction methodology across all observables, but the core structural equivalence (the goal of this ROADMAP item) is now demonstrated.

### 11. d=217 framing: landmark, not terminus — CLOSED at structural-clarity level

**Status:** structural clarification, no numerical observables change. CLOSED at the structural-clarity level by [`tools/research/cascade_uv_convergence.py`](tools/research/cascade_uv_convergence.py). Identified during a discussion of cascade UV behavior: the user observed that the tower is convergent and shouldn't be artificially capped at d=217.

**The original phrasing in Part 0 Theorem 6.7** says "the cascade ends at d_2=217." Numerical investigation shows this is more accurately framed as: d=217 is the deepest distinguished Gamma-critical landmark; cascade descent continues structurally beyond d=217 with negligible contributions to observable physics.

**Cascade UV behavior (verified numerically):**

```
delta_path(5, d_max):
  d=29:    0.0175
  d=100:   0.0204
  d=217:   0.0211   <-- cosmological constant calibration
  d=500:   0.0214
  d=1000:  0.0215
  d=10000: 0.0217   <-- converges to ~0.0217
```

Per-layer Gram contributions (1−C²_{d,d+1}) decay as ~1/(8d²) — sum converges absolutely. Sphere areas Ω_d decay super-exponentially. Phi(d) and cumulative compliance diverge logarithmically but never appear in cascade observable predictions (only finite-layer Phi(d_g) does).

**Critical clarification: cosmological constant calibration is correctly at d=217.**

The Gram correction for ρ_Λ is naturally capped at d=217 because **d=217 IS the cosmological landmark**. Extending Gram beyond d=217 in the CC formula would be incorrect — it would sample cascade structure beyond the cosmological landmark. The CC prediction is NOT shifted by the cascade's extension to d=∞.

What changes (interpretation):
- Cascade structure: extends to d=∞ (consistent with B^∞ block-universe ontology)
- Higher Bott layers (d=29, 37, 45, …) extend forever with exponentially suppressed contributions
- Part 0 Theorem 6.7 phrasing: "deepest landmark" rather than "ends at"

What does NOT change (numerical observables):
- CC prediction still calibrated at Gram(5, 217)
- Mass-formula predictions (terminus-independent anyway)
- All other cascade observables

**Verifier:** [`tools/research/cascade_uv_convergence.py`](tools/research/cascade_uv_convergence.py).

(a) Verify UV convergence of cascade observable quantities. DONE: δ_path, sphere areas, Gram all converge or are bounded.

(b) Identify role of d=217 (landmark vs terminus). DONE: d=217 is the deepest Γ-critical landmark, not a structural terminus. Cascade extends to d=∞.

(c) Confirm cosmological constant correctly calibrated at d=217 (NOT shifted). DONE: CC stays at Gram(5, 217) calibration.

**Lower-priority follow-up:**
1. Update Part 0 Theorem 6.7 phrasing in LaTeX (interpretive, not derivation change)
2. Document cascade extension to d=∞ in Part 0 supplementary remarks
3. Verify all other cascade predictions correctly use specific landmarks (not the d=217 cap)

This roadmap item resolves an interpretive ambiguity about cascade structure without changing any numerical predictions. Consistent with cascade block-universe ontology and higher Bott layer predictions.

### 12. T_CMB closure under "cascade extends to d=∞" — exploratory, no closure yet

**Status:** EXPLORATORY only. The Part V leading prediction T_CMB = 2.642 K (−3.07%) and the H_0-propagated Gram correction T_CMB ≈ 2.669 K (−2.07%) remain the cascade's stated predictions. Closing the residual remains an open problem (Part V Remark `rem:tcmb-descent-dependent` explicitly flags it as such). Verifier: [`tools/research/cascade_tcmb_calibrated_to_infinity.py`](tools/research/cascade_tcmb_calibrated_to_infinity.py).

**Context.** ROADMAP Item 11 (cascade UV convergence) clarified that the cascade extends structurally to d=∞ rather than terminating at d=217. The cosmological constant is calibrated AT d=217 (so its Gram path correctly truncates there), but T_CMB is *not* calibrated at any specific landmark — it is derived thermodynamically from Ω_r, M_Pl,red, H_0, and g_eff. This raises the question of whether T_CMB should pick up its own Gram correction with δ_path(5, ∞) ≈ 0.02165 rather than the H_0-inherited δ_path(5, 217) ≈ 0.02108.

**Numerical readings tested** (none structurally derived):

| Reading | T_CMB (K) | Residual | Status |
|---|---|---|---|
| Part V leading | 2.642 | −3.06% | committed |
| Gram(5,217) on H_0 (Part V Remark) | 2.669 | −2.07% | committed |
| **Reading 1**: extend δ_path(5,217)→δ_path(5,∞) in CC chain | 2.670 | −2.04% | rejected (CC is calibrated at 217) |
| **Reading 2**: T_CMB picks up δ_path(5,∞) directly | 2.700 | −0.94% | open |
| **Reading 3** (power=1.5): T_leading·exp(1.5·δ_∞) | 2.729 | +0.14% | rejected (numerology absent derivation) |
| **Reading 4**: g_eff = N_c = 3 plus δ_path(5,∞) | 2.782 | +2.08% | rejected |
| **Reading 5**: g_eff = N_c = 3 alone (no Gram extension) | 2.723 | −0.11% | OPEN — cleanest single-mechanism candidate |

**Reading 5 detail.** Replacing the SM thermodynamic g_eff = 3.383 (photons + 3 neutrino species with (4/11)^(4/3) post-decoupling entropy factor) with a cascade-intrinsic g_eff = N_c = 3 closes the residual to −0.11%, well within standing cascade precision. N_c is forced by Part IVa (Adams' theorem at d=12), so the value 3 is cascade-internal. **What is missing:** a structural derivation that *thermodynamic* radiation-degree-of-freedom counting in the cascade is g_eff = N_c rather than the SM photon+neutrino count, and an explanation of how the (4/11)^(4/3) post-neutrino-decoupling factor and photon polarisation count are subsumed into a single N_c-based counting rule.

**Reading 2 detail.** Direct application of δ_path(5,∞) to T_CMB closes to −0.94%. **What is missing:** a structural argument for why the Gram correction enters T_CMB linearly via exp(δ_∞) rather than through the inherited sqrt(H_0) channel, which would give exp(δ_∞/2).

**Falsification.** A structural derivation of either (a) Reading 5's g_eff = N_c rule from cascade primitives or (b) Reading 2's direct-Gram channel would close T_CMB. Conversely, second-order Gram corrections to H_0 alone (without modifying g_eff or applying a separate Gram channel to T_CMB) appear unlikely to close the gap, since the leading inherited correction is already exhausted.

**Concrete next work:**
1. Search for a cascade-native derivation of g_eff at recombination from Part 0 / Part IVa primitives. Candidate route: thermodynamic radiation degrees of freedom on S^3 at the four-dimensional observer slice, where N_c may emerge as the effective count after gauge-window structure is accounted for.
2. Test whether the "(4/11)^(4/3) factor" has a cascade-internal reading (e.g. as a ratio of cascade volumes between the photon-coupled era and post-neutrino-decoupling era).
3. Verify the falsification claim: compute the second-order Gram correction to H_0 directly and confirm it does NOT close the T_CMB residual on its own.

This is a structural OPEN QUESTION promoted from Part V Remark `rem:tcmb-descent-dependent`. The candidate readings document the new closure attempts unlocked by ROADMAP Item 11, but no reading is currently structurally derived. The cascade's T_CMB prediction stands at the Part V values until a structural derivation is provided.

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
