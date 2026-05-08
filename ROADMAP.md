# Cascade Series — Roadmap

This file tracks open structural questions and the concrete next steps to close them. Each entry has: status, what's known, what's missing, and the most tractable path forward.

The single source of truth for predictions is [`PREDICTIONS.md`](PREDICTIONS.md). The single source of truth for review protocol and standing issues is [`CLAUDE.md`](CLAUDE.md). This roadmap is the working document for advancing the framework.

## Open structural questions

### 1. Source-selection rule — categorical derivation pending

**Status:** Bijection 4 types ↔ 4 non-sink distinguished layers verified 9/9. The three syntactic flags (P, L, G) are mechanical queries on cascade formulas. Categorical derivation of the flags from a formal category of cascade observables is open.

See Part IVb Proposition `prop:source-selection` and the open question `oq:source-selection-category`.

### 2. Lighter neutrino masses, solar Δm², PMNS — different mechanism needed

**Status:** Heaviest neutrino mass closes at −0.4% via the m_29 chain. Lighter masses in the diagonal cascade form give m_2 ≈ 3×10⁻⁴ eV, undershooting the observed solar splitting √Δm²_sol = 8.6×10⁻³ eV by factor ~800. Cabibbo-template extended to PMNS_12 gives 7.5° vs observed 33.4° — wrong by factor 4.5.

**Genuine open structural piece:** a cascade-internal derivation of neutrino-sector mixing yielding (a) large θ_12, θ_23, (b) small θ_13, (c) magnitude Δm²_sol. The CKM and PMNS sectors require structurally different mechanisms.

See Part IVb open question on PMNS and `tools/research/cascade_pmns_solar_splitting.py` for the partial-negative tests on existing cascade ingredients (Gram, geometric-mean, χ-factor).

**Exploratory tools (tested, not yet adopted into closures):** the following research verifiers document research directions in the Item 5 sector that are not yet promoted to predictions but represent tested approaches:
- [`tools/research/cascade_higher_bott_tower.py`](tools/research/cascade_higher_bott_tower.py) — higher Bott layers (d=29, 37, 45, ...) and their potential roles as cascade-native source masses.
- [`tools/research/cascade_neutrino_mass_d37_proposal.py`](tools/research/cascade_neutrino_mass_d37_proposal.py) — proposes m_2 = m_37 · α(5)/χ; matches PDG +0.66% but structural derivation pending.
- [`tools/research/cascade_neutrino_d37_structural_dig.py`](tools/research/cascade_neutrino_d37_structural_dig.py) — follow-up structural exploration of the d=37 source layer hypothesis.
- [`tools/research/cascade_neutrino_flavor_change_compat.py`](tools/research/cascade_neutrino_flavor_change_compat.py) — compatibility check between cascade neutrino spectrum proposals and observed neutrino oscillations.
- [`tools/research/cascade_pmns_mixing_angle_proposal.py`](tools/research/cascade_pmns_mixing_angle_proposal.py) — candidate cascade-native PMNS angles: sin²θ_12 = (1−α(5))/N_c, sin²θ_23 = 4/7, sin²θ_13 = N_c·α_em.
- [`tools/research/cascade_pmns_structural_derivation_attempt.py`](tools/research/cascade_pmns_structural_derivation_attempt.py) — structural derivation attempts for the candidate PMNS formulas.

These are exploratory tools without integration into the cascade's published derivation chain. They represent the cascade research program's current state on Item 5: candidate formulas that match observation numerically but lack the structural derivation that would promote them to closure (parallel to where the channel-count rule sat before its Tier 1 completeness proof).

### 3. Up-type quark masses — substantial progress (full quark hierarchy in 4 cascade quantities + 1 anchor)

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

### 4. Cosmology primordial spectrum — Tier 5

**Status:** n_s, A_s not derived. The cascade has a native perturbation source (per-layer Gram deficit, Part 0 §12), but quantitative match to the observed primordial spectrum is fuzzy at current precision. r is qualitatively suppressed; magnitude open. See Part VI.

### 5. Ω_b derivation — needs strengthening

**Status:** Tier 5 in PREDICTIONS.md. The "one unit of content on S³" argument for Ω_b = 1/(2π²) needs structural strengthening. Interpretive, not a missing derivation chain.

### 6. T_CMB closure under "cascade extends to d=∞" — exploratory, Reading 8 stands as candidate

**Status:** EXPLORATORY only. The Part V leading prediction T_CMB = 2.642 K (−3.07%) and the H_0-propagated Gram correction T_CMB ≈ 2.669 K (−2.07%) remain the cascade's stated predictions. Closing the residual remains an open problem (Part V Remark `rem:tcmb-descent-dependent` explicitly flags it as such). Verifier: [`tools/research/cascade_tcmb_calibrated_to_infinity.py`](tools/research/cascade_tcmb_calibrated_to_infinity.py).

**REVISED (2026-05-04 evening):** The earlier retraction of Readings 6–8 (made on the basis of Part VI's "Phase D = SM Boltzmann" reading) is **walked back**. Per Part VI's own Tier classification (line 1316–1383):

> "**No result of Part VI is Tier 1 or Tier 2.** The paper's function is to provide a speculative but concrete cascade-native cosmic history..."

Specifically:
- N=217 Big Bang (`thm:reheating`): **Tier 5** — "Mechanism proposed; thermalisation-to-w=1/3 step assumed"
- Phase table (Phases A–D): **Tier 5**
- Particle structural timeline ("freeze out in thermal order"): **Tier 5**

Per CLAUDE.md: Tier 5 results are explicitly *not* sufficient to compel cascade predictions. **Retracting Reading 8 on Tier 5 evidence is unsound** — the Part VI single-tick Big Bang and Phase D = SM Boltzmann framework are themselves speculative, not derived. The basin symmetry from Part IVb `thm:chirality-factorisation` is **Tier 1** (Poincaré-Hopf, theorem-level) and is structurally always present, including pre-Big-Bang.

**What actually compels belief:**
- Basin symmetry χ(S⁴)=2 (Tier 1, Part IVb)
- `prop:g_eff` at T_RH = 106.75 as a cascade-native layer sum (Tier 3)
- Part V T_CMB derivation using SM g_eff = 3.383 as input (acknowledged as the open problem)

**What is speculative:**
- The single-tick Big Bang interpretation (Tier 5)
- The "Phase D = standard Boltzmann dynamics with cascade-derived masses" reading (Tier 5)
- The "no basin effect on local thermal physics" assumption (not stated as a theorem anywhere; emergent from Part VI's Tier 5 phase structure)

**Implications for Reading 8:**
- Reading 8's f⁴ = N_c/χ⁴ = 3/16 closure to +0.02% **stands as a candidate**.
- The cascade has NOT derived post-Big-Bang thermodynamics cascade-natively. Part VI imports SM Boltzmann into the cascade framework as a Tier 5 speculative reading.
- **Reading 8 is an alternative cascade-native thermodynamic reading**, also speculative but built on Tier 1 ingredients (basin symmetry, sector-dim ratio, channel-count rule).
- Both readings are Tier 5; neither compels belief; the cascade has work to do to derive post-Big-Bang thermodynamics structurally.

**The genuine question is:** which speculative reading of post-Big-Bang thermodynamics is cascade-correct?
- Part VI's reading (SM Boltzmann embedded): T_CMB residual stays at −3.07%
- Reading 8's reading (cascade-native f⁴ = N_c/χ⁴): T_CMB closes to +0.02%
- A third reading not yet articulated

The structural ingredients of Reading 8 are cascade-native (Tier 1 basin symmetry + sector-dim ratio + channel-count rule). The structural ingredients of Part VI's reading import SM thermodynamics. Neither is decisively better at the current Tier-classification level.

**The earlier "RETRACTED" framing in this section was over-confident.** I treated Part VI's Tier 5 framing as load-bearing when Part VI itself flags it as speculative. Returning to honest exploration:

**Static B^∞ reading as third structural commitment.** [`tools/research/cascade_static_binfty_thermal.py`](tools/research/cascade_static_binfty_thermal.py) explores whether the cascade's deepest ontology (B^∞ static, all dimensions exist eternally) combined with basin symmetry operating throughout cosmic history yields a coherent BBN+T_CMB picture.

**Under static B^∞:**
- All cascade layers exist eternally, including d=217. No "Big Bang creation event."
- Pre-217 matter exists in **structural occupancy** (cascade Hilbert space populated, basin symmetry operative); post-217 matter has **observable thermal occupancy** at d=4.
- The N=217 transition is **observational accessibility change**, not creation.
- Basin symmetry χ(S⁴)=2 (Tier 1) operates at all epochs, including BBN.

**What changes at "N=217":** structural matter content becomes thermally accessible to the d=4 observer. Pre-217 matter has a "different character" (not in thermal bath); post-217 it's thermally observable. The cascade's static ontology is preserved.

**BBN implications under static B^∞ + local basin filter:**

| Reading | g_eff(BBN) | dev vs SM 10.75 | Status |
|---|---|---|---|
| **X1**: basin filter local, no Reading 8 (e⁻ + 3 ν_L only) | 6.38 | **−41%** | INCONSISTENT with BBN |
| **X2**: basin filter local + Reading 8 (N_c/χ⁴ on all fermions) | 2.82 | **−74%** | RULED OUT |
| **X3**: epoch-dependent activation at T ~ m_e | 10.75 | 0% | passes BBN, allows R8 at recomb (needs Tier 5 mechanism) |
| **X4**: cascade non-Boltzmann thermal physics | undetermined | n/a | speculative, no derivation |

**What this finding shows:**
- **Static B^∞ alone does NOT determine cascade thermodynamics.** B^∞ is the ontology; thermal physics is a separate structural derivation.
- **Uniform local basin filter fails BBN** (X1, X2 ruled out).
- **The B^∞ ontology + Reading 8 closure requires either** epoch-dependent activation (X3, Tier 5) or non-Boltzmann cascade-native thermal physics (X4, speculative).
- **Part VI's reading (a)** corresponds to "basin filter only operates globally, local thermal physics is SM Boltzmann" — Tier 5, gives T_CMB residual −3.07%.

**The three competing Tier 5 readings of cascade thermodynamics:**
1. **Part VI reading**: cascade Phase D = SM Boltzmann with cascade masses. T_CMB residual stays at −3.07%. Imports SM thermodynamics into cascade framework.
2. **Reading 8 + X3 epoch-dependent**: basin filter activates at T ~ m_e, gives Reading 8 closure at recombination, matches SM at BBN. Requires Tier 5 mechanism for the activation.
3. **Static B^∞ + X4 non-Boltzmann thermal**: cascade has its own thermal physics not yet articulated. Speculative.

**Genuine open structural question:** what is cascade-native post-Big-Bang thermodynamics?

The cascade has Tier 1 ingredients (B^∞ static, basin symmetry, sector-dim mechanism) but has *not* derived thermal physics rigorously beyond:
- Part V's import of SM g_eff = 3.383 at recombination (acknowledged as the open problem)
- Part VI's `prop:g_eff` = 106.75 at T_RH (Tier 3, cascade-native layer sum)

Closing T_CMB requires deriving cascade-native thermal physics structurally — which is the genuine work, not resolvable by ontological arguments alone. The user's insight (matter pre-217 with different character; static B^∞ as base ontology) sharpens the question but does not yet answer it.

**Updated Reading 8 status:** Tier 5 candidate, requires either X3 (epoch-dependent) or X4 (non-Boltzmann) cascade thermal physics. Part VI's competing Tier 5 reading also requires structural derivation it has not yet provided. The question is genuinely undetermined at current cascade tier discipline.

**Context.** Earlier work on cascade UV convergence (now closed) clarified that the cascade extends structurally to d=∞ rather than terminating at d=217. The cosmological constant is calibrated AT d=217 (so its Gram path correctly truncates there), but T_CMB is *not* calibrated at any specific landmark — it is derived thermodynamically from Ω_r, M_Pl,red, H_0, and g_eff. This raises the question of whether T_CMB should pick up its own Gram correction with δ_path(5, ∞) ≈ 0.02165 rather than the H_0-inherited δ_path(5, 217) ≈ 0.02108.

**Numerical readings tested** (none structurally derived):

| Reading | T_CMB (K) | Residual | Status |
|---|---|---|---|
| Part V leading | 2.642 | −3.06% | committed |
| Gram(5,217) on H_0 (Part V Remark) | 2.669 | −2.07% | committed |
| **Reading 1**: extend δ_path(5,217)→δ_path(5,∞) in CC chain | 2.670 | −2.04% | rejected (CC is calibrated at 217) |
| **Reading 2**: T_CMB picks up δ_path(5,∞) directly | 2.700 | −0.94% | open (needs structural channel) |
| **Reading 3** (power=1.5): T_leading·exp(1.5·δ_∞) | 2.729 | +0.14% | rejected (numerology absent derivation) |
| **Reading 4**: g_eff = N_c = 3 plus δ_path(5,∞) | 2.782 | +2.08% | rejected |
| **Reading 5**: g_eff = N_c = 3 alone (no Gram extension) | 2.723 | −0.11% | DEMOTED — most likely numerical coincidence (see basin re-examination below) |
| **Reading 6**: cascade no-annihilation, neutrinos full 2 d.o.f. | 2.178 | −20.09% | structural cascade reading; rules itself out |
| **Reading 7**: cascade no-annihilation + basin halving (1 d.o.f./species) | 2.438 | −10.54% | structural cascade reading; rules itself out |
| **Reading 8**: cascade no-annihilation + (T_ν/T_γ)⁴ = N_c/χ⁴ = 3/16 | 2.726 | +0.02% | **leading candidate** — cascade-native structural form |

**Basin / no-annihilation re-examination.** The cascade has CPT-conjugate basins at $d=4$ (Part IVb `thm:chirality-factorisation`); e⁺e⁻ never annihilate in our basin (antimatter is in the antipodal basin, causally disconnected). The SM $(4/11)^{4/3}$ post-annihilation entropy factor in $g_\text{eff} = 2 + (7/8)\cdot 2\cdot N_\text{eff}\cdot (4/11)^{4/3} = 3.383$ is therefore structurally an **SM artifact**, not a cascade quantity. Under cascade-native logic photons and neutrinos stay at the same temperature throughout, giving $g_\text{eff} = 2 + (7/8)\cdot d_\nu \cdot N_\text{eff}$ with $d_\nu \in \{1, 2\}$ — i.e. $g_\text{eff} \approx 4.6$ to $7.3$ (Readings 6–7), pushing T_CMB to $2.18$–$2.44$ K (residual $-10\%$ to $-20\%$, **much worse**).

Cascade neutrino masses ($m_3 = 0.049$ eV, $m_2 \sim 10^{-4}$ eV, $m_1 \sim 10^{-6}$ eV) are all relativistic at recombination ($T_\gamma = 0.26$ eV); the non-relativistic-transition lever is unavailable. Source mass $m_{29} = 543$ eV is non-relativistic but is the cascade source, not the propagated physical mass.

**Reading 5 status: DEMOTED.** Reading 5's near-closure ($g_\text{eff} = N_c = 3$, residual $-0.11\%$) is *most likely a numerical coincidence*. The cascade-native answer for $g_\text{eff}$ under "no annihilation" is $\sim 7$, not $3$. The required $g_\text{eff}$ for exact T_CMB closure is $2.987$, very close to $N_c = 3$, but no cascade-native derivation gives $g_\text{eff} \approx 3$ — only Reading 5's *ad hoc* substitution does.

**Reading 8 — leading candidate.** A different cascade-native form closes T_CMB with structurally-grounded ingredients. Under cascade-native counting (no annihilation, photons + neutrinos at distinct temperatures) with $N_\text{eff} = 3$:
$$
g_\text{eff}^\text{cascade} = 2 + \tfrac{7}{8} \cdot 2 \cdot N_\text{eff} \cdot \left(\tfrac{T_\nu}{T_\gamma}\right)^4
$$
where $(T_\nu / T_\gamma)^4 = N_c / \chi^4 = 3/16 = 0.1875$. Both factors are cascade primitives:
- $N_c = 3$: colour count, forced by Adams' theorem at $d=12$ (Part IVa).
- $\chi = 2$: Euler characteristic of $S^4$ (the cascade observer's basin host).
- $\chi^4 = 16$: chirality filter applied with $k=4$ — Part IVb's channel-count rule gives $k = 2 \cdot \text{(Bott periods spanned)}$, so $k=4$ corresponds to 2 Bott periods spanned.

This gives $g_\text{eff} = 2.984$ and $T_\text{CMB} = 2.726$ K, residual **+0.023%** — within standing cascade precision and *better* than Reading 5.

**Structural derivation attempt:** [`tools/research/cascade_f4_derivation_attempt.py`](tools/research/cascade_f4_derivation_attempt.py) lays out the plausibility argument with cascade-native ingredients (now including the sector-dimension-ratio mechanism from Part IVb `thm:sector-fundamental-y`) and identifies three concrete logical gaps:

- **GAP 1**: Sector-dim-ratio extension to radiation thermodynamics is novel. Part IVb `thm:sector-fundamental-y` derives N_c via $\dim V_{12}(Q_L) / \dim V_{12}(H) = N_c$ for the **Y-spectrum**. Reading 8 requires extending this same mechanism to **radiation density**: cascade radiation samples the full path-tensor $V_{12} \otimes V_{13} \otimes V_{14}$ (not just relativistic-species subspace), with bosons traversing gauge layers transparently while fermions pick up sector-dim factors at each crossed gauge layer. Plausible from Part IVa `rem:fermion-gauge-coupling-proposal` but not derived for thermodynamics.

- **GAP 2**: χ⁴ power = k=4 channel count for neutrino descent. Neutrino at d=21 → observer d=4 crosses 2 Bott boundaries (P_3/P_2 at d=20-21, P_2/P_1 at d=12-13), giving k=4 by the Part IVb channel-count rule. Photon at d=14 → d=4 crosses 1 boundary, giving k=2. The connection $(T_\nu/T_\gamma)^k = \chi^{-k}$ from Born-rule squaring on cascade descent amplitudes is plausible but not formally derived.

- **GAP 3**: No cascade-native bridge from Ω_r to T_CMB at recombination. Part V uses SM g_eff = 3.383 as input; Part VI `prop:g_eff` derives g_eff cascade-natively at T_RH = 106.75 by summing over distinguished layers. The analogous derivation at recombination is missing — this is the priority closure work, with (I9) below providing the template.

**Cascade-native ingredients (all sourced):** χ(S⁴) = 2 (Part IVb `thm:chirality-factorisation`); 4 spatial dims forced (Lovelock, Part III); χ⁴ from k=4 channel count (Part IVb correction-family rule); N_c = 3 (Part IVa `thm:adams`); left-handed neutrinos (Part IVa+IVb); no e⁺e⁻ annihilation in our basin (CLAUDE.md sign-anchor); cascade-native g_eff(T_RH) = 106.75 = SM exactly (Part VI `prop:g_eff`); **sector-dimension-ratio mechanism for N_c factors at d=12 — derived for Y-spectrum in Part IVb `thm:sector-fundamental-y`** (extending to radiation thermodynamics is the new structural commitment).

**Important update — the path to closure is now concrete.** Earlier framings of the T_CMB closure as "needs new structural mechanism" overstated the gap. The N_c factor has a *derived* cascade mechanism (sector dimension ratio); what remains is *extending* it from hypercharge ratios to radiation thermodynamic counting. This is structural extension within existing cascade machinery, not a new theorem.

**Layer-sum analysis identifies the key structural commitment.** [`tools/research/cascade_g_eff_recomb_layer_sum.py`](tools/research/cascade_g_eff_recomb_layer_sum.py) extends Part VI `prop:g_eff` (which sums over distinguished layers at T_RH) to recombination temperature. Two candidate rules give substantially different predictions:

| Rule | g_eff at recomb | T_CMB | dev |
|---|---|---|---|
| **Rule A: per-generation descent** (each ν gets own descent factor) | 5.39 | 2.35 K | **−13.72%** (ruled out) |
| **Rule B: unified sector** (all ν get d=21 descent factor) | 2.98 | 2.73 K | **+0.023%** (Reading 8) |

Reading 8 = Rule B. **The cascade must commit to the unified sector rule for Reading 8 to close.** The structural justification: the cascade path-tensor $V_{12} \otimes V_{13} \otimes V_{14}$ (Part IVa `rem:path-tensor`) couples all 3 neutrino generations within the same Hilbert-space sector; cascade radiation samples this unified sector with descent factor set by maximal extension at d=21.

**Falsifiability test for Rule A vs Rule B:** Rule A predicts cosmic neutrino background dominated by ν_τ (weighted to d=5 home); Rule B predicts equal weighting across generations. CnB measurement (e.g. PTOLEMY) could distinguish. More immediately, Reading 8 (Rule B) agrees with observed T_CMB at +0.023%; Rule A disagrees at −14%. This is current evidence for Rule B.

**Concrete remaining structural work:**
1. Derive the unified sector rule from cascade path-tensor primitives.
2. Justify "maximal extension d=21" over alternatives (e.g. why not d=29 source layer?).
3. Derive boson transparency at gauge layers from cascade fermion-gauge coupling structure.
4. ~~Cross-check against BBN epoch~~ **DONE** — see BBN finding below.

**BBN cross-check finding ([`tools/research/cascade_bbn_cross_check.py`](tools/research/cascade_bbn_cross_check.py)) — Reading 8 needs an epoch-dependent rule.** Applying the unified sector rule UNIFORMLY at all epochs FAILS BBN dramatically:

| Case | g_eff(BBN) | dev vs SM 10.75 | Status |
|---|---|---|---|
| **Case 1**: uniform R8 on ν, no e⁺ at BBN | 4.73 | −56% | RULED OUT |
| **Case 2**: uniform R8 on all fermions | 3.64 | −66% | RULED OUT |
| **Case 3**: cascade = SM at all epochs | 10.75 | 0% | ok (but fails T_CMB) |
| **Case 4**: epoch-dependent transition at T = m_e | 10.75 | 0% | passes both, needs GAP 4 |

**The structural commitment for Reading 8 to survive:** an epoch-dependent rule with transition at T ~ m_e. At T > m_e thermal pair production keeps e⁺ in our basin → cascade thermodynamics matches SM exactly → BBN passes. At T = m_e pair production drops below threshold; e⁺ cannot be replenished, and by cascade no-annihilation cannot disappear via annihilation, so they MIGRATE to the antipodal basin via cascade basin-asymmetry mechanism. Below T = m_e only e⁻ remains in our basin → cascade unified sector rule activates → Reading 8 closes T_CMB.

**GAP 4 (new structural commitment):** Derive the e⁺ migration mechanism at T = m_e cascade-natively. This is mechanically distinct from SM e⁺e⁻ annihilation (which the cascade explicitly excludes via basin separation) but coincides numerically in temperature.

**Updated falsifiability framework:**
- **Reading 8 (Case 4) survives** if GAP 4 + GAPs 1-3 close. Predicts T_CMB to +0.02%.
- **Reading 8 fails BBN** under uniform application (Cases 1, 2). Cannot be rescued by simple modifications.
- **Cascade falls back to SM-like (Case 3)** if GAP 4 cannot be closed. T_CMB residual remains at −3.07% (Part V leading) or −2.07% (Gram-corrected). T_CMB closure remains an open problem.

This is a sharper structural test than before: **Reading 8 is a viable closure ONLY if the cascade has a derivable transition mechanism at T = m_e**. The existence of this transition is now itself a falsifiable cascade prediction — distinct from SM annihilation in mechanism but coincident in temperature.

**Priority next work:** Gap 3 is the root cause — derive a cascade-native bridge formula from Ω_r (geometric, derived in Part V Theorem on Ω_r) to T_CMB that propagates through the gauge window {d=12, 13, 14} with explicit multiplicity factors at each layer crossing. Part VI `prop:g_eff` already does this at T_RH (sums over distinguished layers). The cascade just needs the analogous derivation at recombination temperature, where most layers have decoupled and only photon (d=14) + neutrino (d=21, 13, 5) layers contribute. If that derivation independently yields photon × N_c and neutrino × 1/χ⁴ weightings, Reading 8 closes structurally.

**Cross-check still required:** the cascade-native (T_ν/T_γ)⁴ = N_c/χ⁴ should be consistent with BBN (light-element abundances), recombination acoustic-peak positions, and N_eff measurements (which currently use SM (4/11)^(4/3) implicitly).

**Precision sensitivity caveat.** The match $f^4 = 3/16$ to target $0.188$ is at $\sim 0.27\%$ — robust to T_leading rounding. Higher-precision forms like $N_c \cdot R(12)^2 / \chi^{12}$ give apparent $0.014\%$ matches but are sensitive to $T_\text{leading} = 2.642$ K rounding to 4 sig figs (verifier sensitivity check). The honest claim is: **$f^4 \approx N_c/\chi^4$ at standing precision**, not exact algebraic identity.

**Falsification.** A structural derivation of either (a) Reading 8's $f^4 = N_c/\chi^4$ ratio from cascade primitives or (b) a cascade-native $\Omega_r \to T_\text{CMB}$ bridge would close T_CMB. Reading 5 ($g_\text{eff} = N_c$) and Reading 2 (direct Gram) cannot be promoted absent such a derivation, because cascade-native "no annihilation" logic actively contradicts Reading 5's $g_\text{eff} \approx 3$ requirement (cascade-native gives $g_\text{eff} \approx 7$ unless an additional $T_\nu / T_\gamma$ suppression is invoked, which is exactly Reading 8).

**Concrete next work:**
1. **Search for the structural origin of $f^4 = N_c/\chi^4$.** Test the "2 Bott periods spanned" interpretation: is there a cascade descent path from photon ($d=14$) through both heavy neutrino generation homes ($d=13, 21$) that picks up exactly $\chi^4$ in the temperature-ratio computation?
2. **Search for a cascade-native bridge from $\Omega_r$ to $T_\text{CMB}$** that bypasses SM $g_\text{eff}$. Candidate: dimensional construction $T \sim (\Omega_r \cdot M_\text{Pl}^2 \cdot H_0^2)^{1/4} \cdot (\text{cascade Gamma-function factor})$.
3. **Cross-check Reading 8 against BBN.** The (4/11)^{4/3} factor enters BBN via the same $g_\text{eff}$ at the relevant epoch. If the cascade replaces this with $N_c/\chi^4$, BBN should show consistent shifts in light-element abundances. Check current BBN constraints.

This is a structural OPEN QUESTION promoted from Part V Remark `rem:tcmb-descent-dependent`. The exploratory readings document the closure attempts unlocked by the (now-closed) cascade UV convergence work, but the basin/no-annihilation re-examination reveals that cascade-native logic actually makes T_CMB *harder* to close, not easier. The cascade's T_CMB prediction stands at the Part V values until a structural derivation lands.

### 7. Higher-loop QED anomalous magnetic moment — frontier

The cascade's coverage of the gyromagnetic ratio currently reaches 1-loop:

- **Tree-level** g = 2: derived cascade-natively as g = χ(S^{d_f − 1}) = 2 (Part IVb `cor:g-equals-two`, Part II=III `thm:cascade-dirac-descent`). All factors cascade-internal, no fitted parameter.
- **1-loop** (g − 2)/2 = α_em/(2π): all three factors cascade-identifiable (Part IVb `rem:two-pi-prefactor-identification`, Part IVb `rem:chirality-special-cases`). α_em from Tier 2 closure; chirality factor χ⁰ = 1 from `thm:chirality-selection-rule`; prefactor 1/(2π) = 1/(N(0)·Γ(1/2)²) by `cor:2sqrtpi-primitive`.

**What's open:** higher-loop QED coefficients beyond Schwinger.

- **2-loop** (Sommerfield–Petermann): a_e^{(2)} = −0.328478… · α²/π². The structural prefactor α²/π² extends the cascade-primitive identification (1/π² = 1/Γ(1/2)⁴, two factors of the per-leg primitive squared). The transcendental numerical coefficient −0.328478… = 197/144 + π²/12 − π²·ln 2/2 + 3·ζ(3)/4 + … is the contribution of specific Feynman diagrams not currently cascade-derived.
- **5-loop a_e**: precision ~10⁻¹³, currently the most precisely measured anomalous magnetic moment in physics. The cascade matches the structural-prefactor form via Cor:2sqrtpi-primitive at every order, but the QED-specific numerical coefficients at each loop are not cascade-internal.
- **a_μ frontier**: ~5σ tension between Brookhaven/Fermilab measurements (a_μ^exp ~ 2.51 × 10⁻⁹) and lattice-QCD hadronic-vacuum-polarization predictions. Hadronic contributions involve QCD beyond pure QED. The cascade currently does not predict either side of this tension.

**Path to cascade-native coverage:**

1. **Cascade-native expansion of the QED transcendentals.** Specifically: are 197/144, π²/12, ζ(3)/4 expressible as cascade-primitive ratios? This would be analogous to the 1/(2π) = 1/(N(0)·Γ(1/2)²) identification but for higher-loop coefficients. Worth a systematic algebraic audit.

2. **Cascade-extension of the chirality-selection-rule to higher slots.** Per Part IVb `oq:chirality-selection-extensions`: cascade observables exercising m ≥ 2 closed loops or higher k. The g − 2 at 2-loop corresponds to m = 2, k = 1 → χ^(m−k) = χ¹ = 2. Whether the cascade per-loop primitive structure at m = 2 produces the Sommerfield–Petermann coefficient cascade-natively is the structural question.

3. **Hadronic cascade contribution.** The a_μ frontier involves QCD effects at hadronic energies. The cascade's QCD structure (Part IVa: SU(3) at d_0 = 7 / d_g = 12) would need to combine with the 1-loop chirality-selection-rule structure to produce the hadronic anomalous moment. Whether the cascade naturally gives the correct sign/magnitude relative to the experimental discrepancy is open.

**Falsification.** If a cascade-native 2-loop derivation produces a numerical coefficient inconsistent with Sommerfield–Petermann's −0.328478… (at the precision the experimental measurements probe), the cascade's higher-loop extension fails. Conversely, a cascade-native a_μ prediction landing on either side of the experimental/lattice tension at >1σ would resolve the frontier in cascade favour.

**Status.** Tier 4 frontier item, tracked in Part IVb `oq:higher-loop-qed-coefficients`. The 1-loop cascade-primitive identification (this session) is the entry point; higher-loop coverage is the natural extension. Closely related to ROADMAP items closing on the chirality-selection-rule's higher slots.

## Working principles

- **Tier discipline.** Every result carries its tier. Tier 5 (provisional) is explicitly not sufficient for the cascade to claim a prediction.
- **No semiclassical machinery.** Per CLAUDE.md Check 7: no QFT on curved spacetime, no Bogoliubov, no Kaluza–Klein, no semiclassical sphere Green's functions or quantum effective potentials. Cascade-native procedures only.
- **Falsifiability.** Every roadmap entry that proposes a closure mechanism must specify what would falsify it.
- **Acknowledged-vs-novel categorisation.** Defects already acknowledged in CLAUDE.md or PREDICTIONS.md Tier 5 are not new findings. Only novel structural gaps count.
