# The Cascade Series

**[Read the papers online](https://dickie81.github.io/r-infinite/)**

The cascade series tests one hypothesis: the infinite-dimensional unit ball, descended to four dimensions, is indistinguishable from our universe. From a single axiom (orthogonality) and with zero free parameters, the series derives the cosmological constant, quantum mechanics, general relativity with d=4 and Lorentzian signature, the Standard Model gauge group and its symmetry breaking, three fermion generations, precision mass and coupling predictions, and the background cosmological parameters including a Hubble constant between the two competing measurements.

<!-- BEGIN PREDICTIONS -->
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
| Cosmological constant | 1.099 × 10⁻¹²⁰ | 0.1% match | Cascade invariant (I) |
| Dark energy EoS | w = −1 exactly | Confirmed | Fixed geometric constant (III) |
| Strong CP phase | θ_QCD = 0 | Confirmed | π₃(S¹¹) = Z₂ (IVa) |
| No supersymmetry | — | Confirmed (LHC) | No pairing mechanism (IVa) |
| No dark matter particles | — | Confirmed (null results) | Geometry provides content (V) |
| No extra Higgs bosons | — | Confirmed (LHC) | One hairy ball zero (IVa) |

### Tier 2 — Derived: Closed-Form, Zero Free Parameters

Numerical predictions from cascade geometry. Formulas are exact; deviations reflect leading-order truncation.

| Observable | Formula | Predicted | Observed | Dev. |
|---|---|---|---|---|
| Ω_Λ | (π−1)/π | 0.6817 | 0.685 ± 0.007 | −0.5% |
| Ω_m | 1/π | 0.3183 | 0.315 ± 0.007 | +1.1% |
| Ω_r | 1/(4π⁷) | 8.28 × 10⁻⁵ | 8.27 × 10⁻⁵ | +0.1% |
| T_CMB | from Ω_r | 2.730 K | 2.7255 K | +0.16% |
| m_H / m_W | π/2 | 1.5708 | 1.559 | +0.8% |
| m_μ / m_e | exp(ΔΦ) · 2√π | 206.50 | 206.77 | +0.13% |
| m_e | geometric-topological | 0.514 MeV | 0.511 MeV | +0.6% |
| m_μ | geometric-topological | 106.2 MeV | 105.66 MeV | +0.5% |
| α_s(M_Z) leading | α(12) · exp(ΔΦ) | 0.1159 | 0.1179 ± 0.0009 | −1.7% |
| sin²θ_W leading | Radon-Hurwitz ratio | 0.2286 | 0.23121 | −1.1% |

### Tier 3 — Precision: Correction-Family Closures

Seven observables close within experimental error via δΦ = α(d*)/χ^k shifts sourced at Part 0's distinguished dimensions. Three shift-observable pairs reuse the same correction across independent quantities.

| Observable | Shift source | Predicted | Observed | Residual |
|---|---|---|---|---|
| α_s(M_Z) | α(14)/χ | 0.11792 | 0.1179 ± 0.0009 | +0.02σ |
| m_τ / m_μ | α(14)/χ | 16.8173 | 16.8170 ± 0.0011 | +0.24σ |
| m_τ absolute | α(19)/χ | 1776.82 MeV | 1776.86 ± 0.12 | −0.31σ |
| sin²θ_W | α(5)/χ³ | 0.23123 | 0.23121 ± 0.00004 | +0.40σ |
| Ω_m | −α(5)/χ³ | 0.31474 | 0.315 ± 0.007 | −0.04σ |
| θ_C (Cabibbo) | −α(7)/χ² | 13.04° | 13.04 ± 0.05° | +0.03σ |

### Tier 4 — Frontier: Under Active Experimental Test

Specific predictions testable by current or near-future experiments (DESI, Euclid, CMB-S4, SH0ES).

| Observable | Predicted | Current data | Status |
|---|---|---|---|
| H₀ | 71.05 km/s/Mpc | Planck: 67.4 · SH0ES: 73.0 | Between tensions; resolves with cascade r_d |
| r_d (sound horizon) | ≈141 Mpc | Planck: 147.6 Mpc | DESI BAO: cascade fits better (χ²/n = 1.70 vs 1.90) |
| DESI w ≠ −1 signal | w = −1; apparent deviation is ruler mismatch | DESI DR2: w ≈ −0.76 | Cascade explains signal without dynamical dark energy |

### Tier 5 — Provisional: Derivation Incomplete

Results where the argument has acknowledged gaps or needs strengthening.

| Observable | Issue |
|---|---|
| Ω_b = 1/(2π²) | “One unit of content on S³” argument needs strengthening |
| n_s, A_s | Primordial spectrum not yet derived |
| Correction selection rule | Observable-to-source assignment not fully derived from first principles |

<!-- END PREDICTIONS -->

## Papers

| File | Title |
|------|-------|
| [`cascade-series-cover-sheet.tex`](src/cascade-series-cover-sheet.tex) | Cover Sheet — The Thought Experiment, Hypothesis, and Series Overview |
| [`cascade-series-prelude.tex`](src/cascade-series-prelude.tex) | Prelude — Why Nothing Has Structure |
| [`cascade-series-part0.tex`](src/cascade-series-part0.tex) | Part 0 — Scale Variance from Orthogonality: How the Unit Ball Generates 10^120 Orders of Magnitude |
| [`cascade-series-part0.0.tex`](src/cascade-series-part0.0.tex) | Part 0 Supplement — Inter-Layer Coupling and the Independent-Step Correction |
| [`cascade-series-part1.tex`](src/cascade-series-part1.tex) | Part I — The Cosmological Constant from the Observer's Frame |
| [`cascade-series-part2.tex`](src/cascade-series-part2.tex) | Part II — Quantum Mechanics from the Cascade: Effective Theory of a 4-Dimensional Observer in the Sphere-Area Geometry |
| [`cascade-series-part3.tex`](src/cascade-series-part3.tex) | Part III — General Relativity, Four Dimensions, and Lorentzian Signature from the Cascade |
| [`cascade-series-part2-equals-3.tex`](src/cascade-series-part2-equals-3.tex) | Part II = III — Quantum Gravity without Quantising Gravity: Why the Quantum and Gravitational Projections of the Cascade Are the Same Theorem |
| [`cascade-series-part4a.tex`](src/cascade-series-part4a.tex) | Part IVa — The Standard Model from the Cascade: Gauge Group, Symmetry Breaking, and Three Generations from Bott Periodicity and Hairy Ball Zeros |
| [`cascade-series-part4b.tex`](src/cascade-series-part4b.tex) | Part IVb — The Standard Model from the Cascade: Masses, Couplings, and Precision Predictions from the Geometric-Topological Factorization |
| [`cascade-series-part5.tex`](src/cascade-series-part5.tex) | Part V — Cosmology from the Cascade: ΛCDM Parameters, the Hubble Constant, and the DESI BAO Observations |

## Building PDFs

A GitHub Actions workflow automatically compiles all `.tex` files into PDFs on every push. PDFs are available as build artifacts.

To build locally, run:

```bash
cd src
latexmk -pdf cascade-series-cover-sheet.tex
```

Or compile all files at once:

```bash
cd src
latexmk -pdf *.tex
```

## License

This work is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Citation

See [CITATION.cff](CITATION.cff) for citation information.
