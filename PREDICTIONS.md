# Cascade Series — Predictions

Full tiered predictions table. This file is the single source of truth for the series' predictions; `tools/build/generate_predictions.py` parses the `## Predictions` section below to generate the LaTeX table (`src/generated/predictions-table.tex`) embedded in the cover sheet, and the HTML table on [the project website](https://dickie81.github.io/r-infinite/).

A compact headline subset is shown in the [main README](README.md).

## Predictions

One hypothesis. Zero free parameters. Every prediction below is a test of the hypothesis.

### Tier 1 — Exact: Forced by Uniqueness Theorems

Mathematical uniqueness proofs leave no alternative. These are not approximations.

| Prediction | Value | Status | Source |
|---|---|---|---|
| Spacetime dimension | d = 4 | Confirmed | Lovelock ∩ Clifford (III) |
| Metric signature | (−,+,+,+) | Confirmed | Propagator + Clifford (III) |
| Gauge group | SU(3) × SU(2) × U(1) | Confirmed | Adams + Bott (IVa) |
| Symmetry breaking | SU(2) broken; SU(3), U(1) exact | Confirmed | Hairy ball theorem (IVa) |
| Fermion generations | Exactly 3 | Confirmed | Bott periodicity + d₁=19 (IVa) |
| Free Yukawa couplings | Zero — every fermion mass equals the per-layer gauge-coupling amplitude m(d) = R(d)/2; layer position from Bott + Adams (IVa) | Confirmed (charged-lepton sector <1.2%; m_τ/m_μ +0.24σ; m_τ abs −0.31σ; θ_C +0.03σ; b/s 0.014%) | Chirality halving + Berezin partition (IVb): m(d) = R(d)/χ from Poincaré-Hopf on even-sphere Dirac layers; no Yukawa parameter ever introduced |
| Dark energy EoS | w = −1 exactly | Confirmed | Fixed geometric constant (III) |
| Strong CP phase | θ_QCD = 0 | Confirmed | π₃(S¹¹) = 0 (IVa) |
| No supersymmetry | — | Confirmed (LHC) | No pairing mechanism (IVa) |
| No dark matter particles | — | Confirmed (null results) | Geometry provides content (V) |
| No extra Higgs bosons | — | Confirmed (LHC) | One hairy ball zero (IVa) |
| No axion | — | Confirmed (null results) | θ_QCD = 0 topologically (IVa) |
| No gravitons | — | Not yet testable | Metric is state property, not quantised field (II=III, III) |

### Tier 2 — Derived: Closed-Form, Zero Free Parameters

Numerical predictions from cascade geometry. Formulas are exact; deviations reflect leading-order truncation.

| Observable | Formula | Predicted | Observed | Dev. |
|---|---|---|---|---|
| ρ_Λ / M⁴_Pl,red | 18 · Ω(19) · Ω(217) / π³ · exp(δΦ) | 0.7145 × 10⁻¹²⁰ | 0.7150 × 10⁻¹²⁰ ± 0.013 | −0.07% (≈ −0.04σ) |
| Ω_Λ | (π−1)/π | 0.6817 | 0.685 ± 0.007 | −0.5% (≈ −0.47σ) |
| Ω_m | 1/π | 0.3183 | 0.315 ± 0.007 | +1.1% |
| Ω_r | 1/(4π⁷) | 8.28 × 10⁻⁵ | 8.27 × 10⁻⁵ | +0.1% |
| T_CMB | from Ω_r, H₀ | 2.642 K | 2.7255 K | −3.1% (descent-dependent) |
| H₀ | from ρ_Λ, Ω_Λ | 66.78 km/s/Mpc (Gram-corrected ≈ 67.5) | 67.4 ± 0.5 | −0.9% leading; ≈Planck after Gram |
| t₀ | ΛCDM integral | 13.88 Gyr | 13.80 ± 0.02 | +0.6% |
| m_H / m_W | π/2 | 1.5708 | 1.559 | +0.8% |
| m_μ / m_e | exp(ΔΦ) · 2√π | 206.50 | 206.77 | +0.13% |
| m_e | geometric-topological | 0.514 MeV | 0.511 MeV | +0.6% |
| m_μ | geometric-topological | 106.2 MeV | 105.66 MeV | +0.5% |
| α_s(M_Z) leading | α(12) · exp(ΔΦ) | 0.1159 | 0.1179 ± 0.0009 | −1.7% |
| sin²θ_W leading | Radon-Hurwitz ratio | 0.2286 | 0.23121 | −1.1% |
| θ_C leading | arctan(tan(arccos(N(13)/N(12))) · exp(−p(13)/2)) | 13.26° | 13.04 ± 0.05° | +1.7% |
| θ_C (Cabibbo) closed | −α(7)/χ² (channel-count rule, k=2) | 13.04° | 13.04 ± 0.05° | +0.03σ |
| θ_23 (CKM) closed | −α(7)/χ⁴ (channel-count rule, k=4) | 2.380° | 2.38 ± 0.06° | +0.005σ |
| b/s closed | −α(7)/χ⁴ (channel-count rule, k=4) | 44.7436 | 44.75 | 0.014% |
| α_s(M_Z) closed | +α(14)/χ (correction family, k=1) | 0.11792 | 0.1179 ± 0.0009 | +0.02σ |
| m_τ / m_μ closed | +α(14)/χ (correction family, k=1) | 16.8173 | 16.8170 ± 0.0011 | +0.24σ |
| m_τ absolute closed | +α(19)/χ (correction family, k=1) | 1776.82 MeV | 1776.86 ± 0.12 | −0.31σ |
| ℓ_A closed | +α(19)/χ (correction family, k=1) | 301.44 | 301.6 ± 0.09 | −1.8σ (vs 301.6±0.09; earlier −0.16 was the absolute difference mislabeled as σ) |
| sin²θ_W closed | +α(5)/χ³ (correction family, k=3) | 0.23123 | 0.23121 ± 0.00004 | +0.40σ |
| Ω_m closed | −α(5)/χ³ (correction family, k=3) | 0.31473 | 0.315 ± 0.007 | −0.04σ |
| 1/α_em | 1/α(13) + π/α(14) + 6π (chirality theorem, three Dirac layers) | 137.028 | 137.036 | 0.006% |
| m_ν (heaviest) | m_29 · α(21)/χ⁸ (cascade neutrino chain) | 0.0493 eV | √Δm²_atm = 0.0495 eV (PDG 2024) | −0.4% (≈ −0.7σ vs PDG; −2.9σ vs NuFit 6.0) |
| m_K / m_π | d_V/√N(0) = 5/√2 (cascade pseudoscalar octet, Part IVb rem:cascade-beta0) | 3.5355 | 3.5371 | −0.05% |
| m_K (charged) | Λ_PDG · 5√2/3 = Λ · d_V·√N(0)/N_c | 495.0 MeV | 493.68 MeV | +0.27% |
| m_η' / m_η | d_0/(N_c+1) = 7/4 (η-η' double-Adams; Part IVb thm:axial-anomaly-mass) | 1.7500 | 1.7482 | +0.10% |
| m_η' | Λ_PDG · √(N_c · d_0) = Λ · √21 (double-Adams: ρ(12)−1 × ρ(8)−1) | 962.3 MeV | 957.78 MeV | +0.48% |
| m_η | Λ_PDG · (N_c+1)·√(N_c/d_0) = Λ · 4√(3/7) | 549.9 MeV | 547.86 MeV | +0.37% |
| m_π / Λ_PDG | N(0)/N_c = 2/3 (cascade chiral physics; rem:cascade-beta0) | 0.6667 | 0.6646 | +0.31% |
| f_π / m_π | N(0)/N_c = 2/3 (chiral, scheme-invariant) | 0.6667 | 0.6597 | +1.06% |

The "closed" entries above use the α(d\*)/χ^k correction family with all three structural rules now at theorem level (with the source-selection rule at Tier 2 empirical 9/9 + structural uniqueness per pairing):
- **Channel count k = 2N** is a cascade theorem (Part IVb `rem:theta23-channel-count`; chirality factor exponent 2N forced by combining the cascade scalar action's Z₂-only discrete symmetry with Adams' theorem on im J's Z₂ generator residues; ROADMAP Item 1).
- **Sign rule** sign(δΦ) = +1 for descent, −1 for geometric/amplitude is a cascade theorem (Part IVb `thm:sign-rule`; three-case proof: Cauchy-Schwarz on Gram positivity for descent, Bott-vs-lapse theorem for Ω_m, Born-rule overlap chirality decomposition for amplitude observables; ROADMAP Item 4).
- **Source strength** α(d\*) at unit coefficient is structurally forced (Part IVb `rem:marginal-greens` + `rem:action-uniqueness`; marginal Green's function identity gives source response = α(d\*) exactly at every layer; ROADMAP Item 3).
- **Source selection** d\*(Q) bijection is empirical 9/9 + structural uniqueness per pairing (Part IVb `prop:source-selection`; categorical derivation of the syntactic flags is open; ROADMAP Item 2).

Soft spots: cascade path-integral not formally defined; the χ^{2N} magnitude is forced but the (+,+) labelling is convention parallel to the SM's left-handed convention with zero observational input; categorical derivation of source-selection flags pending. See ROADMAP.md items 1–4 for explicit caveats.

**On the m_ν (heaviest) σ value.** The cascade prediction 0.0493 eV is compared against √Δm²_atm = 0.0495 eV from PDG 2024 (Δm²_32 = 2.453(34) × 10⁻³ eV², giving m_3 = 0.04953 ± 0.00034 eV). The cascade-vs-PDG residual is **−0.7σ**. Using the higher central value from NuFit 6.0 (Δm²_3l = 2.507(27) × 10⁻³ eV², without SK atmospheric input), the residual is **−2.9σ**. This is a real input-dependence: cascade m_ν heaviest is sub-σ vs PDG but borderline vs NuFit. The Tier 2 classification reflects PDG (the more conservative experimental aggregation); future global fits resolving the Δm²_atm central value firmly above 2.50 × 10⁻³ eV² would push m_ν heaviest to Tier 4 (frontier under active tension) rather than Tier 2 (closed within precision).

**Convention: % vs σ in Tier 2.** Tier 2 entries fall into two categories with different precision metrics:
- **Corrected closures** (correction-family α(d\*)/χ^k entries plus m_ν heaviest): quoted in σ vs the relevant experimental measurement. These are claimed at experimental precision; σ is the appropriate metric. The exception is b/s, where the experimental ratio has scheme/scale ambiguity that makes σ ill-defined; Part IVb groups it with sub-σ closures and quotes 0.014% directly.
- **Leading predictions** (entries without explicit "closed" label, e.g., m_e, m_μ, m_μ/m_e, m_H/m_W, T_CMB, Ω_r): quoted in %. The cascade's standing claim for these is "~1% leading-order systematic," not experimental-precision σ. For high-precision experimental observables (e.g., m_e measured to 10⁻¹⁰ relative precision), the cascade's % deviation translates to many σ — but this reflects the cascade's leading-order systematic floor, not a tension with the framework. The framework-level claim is the % deviation is within standing precision; tighter closure requires the same kind of correction-family extension that closed the σ-quoted entries.

This is the cascade's tier discipline: "Tier 2" = closed within standing precision (% for leading, σ for corrected closures), not "closed at the strictest experimental σ." The distinction is structurally meaningful: corrected closures use the now-theorem-level α(d\*)/χ^k correction family; leading predictions await analogous closure via additional structural pieces (cf. Open Question on m_μ/m_e residual in Part IVb).

**On the QCD-frontier entries (m_K, m_η, m_η', m_π/Λ, f_π/m_π).** These are sub-percent / ~1% closures from the cascade-primitive grammar developed in Part IVb `rem:cascade-beta0`. Same primitive set $\{N_c, N(0), 2\pi, d_V, d_0\}$ generates QCD's β_0 1-loop coefficient, the cascade-native Λ_QCD descent scale, the chiral relations (m_π, f_π), and the η-η' anomaly sector. The η' anomaly mass receives a topological derivation in Part IVb `thm:axial-anomaly-mass` (Tier 4b status, parallel to `thm:strong-cp`): $m_{\eta'}^2 = \Lambda^2 (\rho(12)-1)(\rho(8)-1)$ identifies the U(1)_A anomaly mass as a double-Adams product, with both factors fixed by Adams' theorem on cascade parallelizable spheres ($S^{11}$ at the gauge layer, $S^7$ at the octonion layer). The same Adams apparatus that anchors SU(3) at $d_g=12$ in `thm:strong-cp` and gives θ_QCD = 0 from $\pi_3(S^{11}) = 0$ now also sets the magnitude of the U(1)_A anomaly mass scale.

### Tier 3 — _Vacated_: correction-family closures all promoted to Tier 2

The seven correction-family closures previously listed in Tier 3 have been promoted to Tier 2 above following the closure of ROADMAP Items 3 (source strength) and 4 (sign rule) at theorem level. The α(d\*)/χ^k correction family's three-of-four structural rules (channel count, sign, source strength) are all theorem-level cascade results; the fourth (source selection) is at the same rigour level the channel-count rule had before its formal completeness proof. No observable currently sits in Tier 3.

### Tier 4 — Frontier: Under Active Experimental Test

Specific predictions testable by current or near-future experiments (DESI, Euclid, CMB-S4, SH0ES, lattice QCD, PDG meson masses).

| Observable | Predicted | Current data | Status |
|---|---|---|---|
| H₀ | 66.78 km/s/Mpc (Gram-corrected ≈ 67.5) | Planck: 67.4 · SH0ES: 73.0 | Planck-side of Hubble tension; incompatible with SH0ES |
| r_d (sound horizon) | ≈147.75 Mpc | Planck: 147.60 Mpc | Essentially equal to Planck; cascade and ΛCDM share a ruler |
| DESI DR2 BAO fit | χ²/n = 2.35 (cascade) vs 1.90 (Planck) | Two shared outliers at z=0.510, z=0.706 | Cascade fits slightly worse than Planck; both face same anomalies |
| DESI w ≠ −1 signal | w = −1 exactly (structural theorem) | DESI DR2: w ≈ −0.76 | Challenges cascade and ΛCDM equally; no ruler-based explanation |
| β_0 (QCD 1-loop) | (N_c²+N_c−1) − N(0)·n_f/N_c (cascade-primitive identity; rem:cascade-beta0) | β_0 = 7 at n_f=6 (QCD definition) | Exact match across n_f windows; cascade form is structural identification of QCD's 1-loop coefficient |
| β_1 (QCD 2-loop) | exact match with two cascade-primitive forms | QCD MS-bar value at any n_f | Exact match; cascade-internal disambiguation between the two forms is the open structural piece |
| Λ_QCD cascade-native | M_Z · exp(−2π) ≈ 170 MeV; with cascade↔MS-bar scheme factor √(N_c/N(0)) → 208.6 MeV | PDG MS-bar (n_f=5): 210 ± 14 MeV | Within PDG band (−0.7%); cascade-internal derivation of √(N_c/N(0)) scheme factor is the Tier 2 promotion target |
| χ_top^(1/4) (QCD topological susceptibility) | Witten-Veneziano with cascade-primitive m_η, m_η', m_K, f_π | 181 MeV (cascade inputs) · 179 MeV (PDG inputs) | Lattice average ≈ 178 MeV; cascade reproduces lattice within +1.7% (cascade) / +0.7% (PDG) |
| Vector mesons (ρ, ω, K*, φ) | Best cascade-primitive fits 1–3% from PDG; structural form ambiguous across the nonet | PDG values | Diagnostic: cascade grammar reaches PS Goldstone octet, stops at J=1; missing machinery is cascade-native hyperfine splitting (open structural direction) |

### Tier 5 — Provisional: Derivation Incomplete

Results where the argument has acknowledged gaps or needs strengthening.

| Observable | Issue |
|---|---|
| Ω_b = 1/(2π²) | "One unit of content on S³" argument needs strengthening |
| n_s, A_s | Primordial spectrum not yet derived |
| Lighter neutrino masses, solar Δm², PMNS | Single-source diagonal form gives m_2 ≈ 3×10⁻⁴ eV and m_3 ≈ 3×10⁻⁶ eV, too small for the observed solar splitting; cascade analogue of inter-generation mixing not yet derived |

(The "correction-family source-selection bijection" entry previously listed in Tier 5 has been removed: per Part IVb `prop:source-selection`, the 4-to-4 type-to-layer assignment is empirical 9/9 with structural uniqueness per pairing — the same rigour as the channel-count rule before its formal completeness proof. The categorical derivation of the syntactic flags from a formal cascade observable category remains open as ROADMAP Item 2, but does not affect any numerical prediction's tier classification: the bijection itself is established structurally.)
