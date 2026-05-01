# Cascade Series — Predictions

Full tiered predictions table. This file is the single source of truth for the series' predictions; `tools/generators/generate_predictions.py` parses the `## Predictions` section below to generate the LaTeX table (`src/generated/predictions-table.tex`) embedded in the cover sheet, and the HTML table on [the project website](https://dickie81.github.io/r-infinite/).

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
| Dark energy EoS | w = −1 exactly | Confirmed | Fixed geometric constant (III) |
| Strong CP phase | θ_QCD = 0 | Confirmed | π₃(S¹¹) = Z₂ (IVa) |
| No supersymmetry | — | Confirmed (LHC) | No pairing mechanism (IVa) |
| No dark matter particles | — | Confirmed (null results) | Geometry provides content (V) |
| No extra Higgs bosons | — | Confirmed (LHC) | One hairy ball zero (IVa) |
| No axion | — | Confirmed (null results) | θ_QCD = 0 topologically (IVa) |
| No gravitons | — | Not yet testable | Metric is state property, not quantised field (II=III, III) |

### Tier 2 — Derived: Closed-Form, Zero Free Parameters

Numerical predictions from cascade geometry. Formulas are exact; deviations reflect leading-order truncation.

| Observable | Formula | Predicted | Observed | Dev. |
|---|---|---|---|---|
| ρ_Λ / M⁴_Pl,red | 18 · Ω(19) · Ω(217) / π³ | 0.6996 × 10⁻¹²⁰ | 0.7150 × 10⁻¹²⁰ | −2.2% |
| Ω_Λ | (π−1)/π | 0.6817 | 0.685 ± 0.007 | −0.5% |
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

### Tier 3 — Precision: Correction-Family Closures

Eight Standard Model observables close within experimental precision via δΦ = ±α(d*)/χ^k shifts sourced at Part 0's distinguished dimensions. Three shift-observable pairs reuse the same correction across independent quantities. A ninth observable (heaviest neutrino mass) closes via the related cascade-internal form m_29 · α(d_g)/χ^k, where m_29 is the cascade charged-lepton formula at the fourth Bott layer d=29 and χ^k is the chirality filter for the cascade distance to the generation layer.

| Observable | Shift source | Predicted | Observed | Residual |
|---|---|---|---|---|
| α_s(M_Z) | α(14)/χ | 0.11792 | 0.1179 ± 0.0009 | +0.02σ |
| m_τ / m_μ | α(14)/χ | 16.8173 | 16.8170 ± 0.0011 | +0.24σ |
| m_τ absolute | α(19)/χ | 1776.82 MeV | 1776.86 ± 0.12 | −0.31σ |
| ℓ_A | α(19)/χ | 301.44 | 301.6 ± 0.09 | −0.16σ |
| sin²θ_W | α(5)/χ³ | 0.23123 | 0.23121 ± 0.00004 | +0.40σ |
| Ω_m | −α(5)/χ³ | 0.31474 | 0.315 ± 0.007 | −0.04σ |
| θ_C (Cabibbo) | −α(7)/χ² | 13.04° | 13.04 ± 0.05° | +0.03σ |
| b/s | −α(7)/χ⁴ | 44.7436 | 44.75 | 0.014% |
| m_ν (heaviest) | m_29 · α(21)/χ⁸ | 0.0493 eV | √Δm²_atm = 0.0495 eV | −0.4% |

### Tier 4 — Frontier: Under Active Experimental Test

Specific predictions testable by current or near-future experiments (DESI, Euclid, CMB-S4, SH0ES).

| Observable | Predicted | Current data | Status |
|---|---|---|---|
| H₀ | 66.78 km/s/Mpc (Gram-corrected ≈ 67.5) | Planck: 67.4 · SH0ES: 73.0 | Planck-side of Hubble tension; incompatible with SH0ES |
| r_d (sound horizon) | ≈147.75 Mpc | Planck: 147.60 Mpc | Essentially equal to Planck; cascade and ΛCDM share a ruler |
| DESI DR2 BAO fit | χ²/n = 2.35 (cascade) vs 1.90 (Planck) | Two shared outliers at z=0.510, z=0.706 | Cascade fits slightly worse than Planck; both face same anomalies |
| DESI w ≠ −1 signal | w = −1 exactly (structural theorem) | DESI DR2: w ≈ −0.76 | Challenges cascade and ΛCDM equally; no ruler-based explanation |

### Tier 5 — Provisional: Derivation Incomplete

Results where the argument has acknowledged gaps or needs strengthening.

| Observable | Issue |
|---|---|
| Ω_b = 1/(2π²) | "One unit of content on S³" argument needs strengthening |
| n_s, A_s | Primordial spectrum not yet derived |
| Correction selection rule | Observable-to-source assignment not fully derived from first principles |
| Lighter neutrino masses, solar Δm², PMNS | Single-source diagonal form gives m_2 ≈ 3×10⁻⁴ eV and m_3 ≈ 3×10⁻⁶ eV, too small for the observed solar splitting; cascade analogue of inter-generation mixing not yet derived |
