# The Cascade Series

[![DOI](https://zenodo.org/badge/1166833443.svg)](https://doi.org/10.5281/zenodo.19520075)

> **The infinite-dimensional unit ball, descended to four dimensions, is indistinguishable from our universe.**

One hypothesis. Zero free parameters. No choices.

The series derives — from this alone — the cosmological constant, quantum mechanics, general relativity at d=4 with Lorentzian signature, the Standard Model gauge group and its symmetry breaking, three fermion generations, particle masses and couplings, and the cosmological parameters including a Planck-compatible Hubble constant (incompatible with SH0ES).

**[Read the papers](https://dickie81.github.io/r-infinite/)**

## Headline results

**Structural (forced by uniqueness theorems):**

- Spacetime dimension **d = 4** with Lorentzian signature (−,+,+,+)
- Gauge group **SU(3) × SU(2) × U(1)** with SU(2) broken
- Exactly **three fermion generations**
- Dark energy equation of state **w = −1 exactly**
- Strong CP phase **θ_QCD = 0**
- **No** supersymmetric partners · **No** dark matter particles · **No** extra Higgs bosons · **No** axion · **No** gravitons

**Precision numerics (closed within experimental error, zero fitted parameters):**

| Observable | Predicted | Observed | Match |
|---|---|---|---|
| ρ_Λ / M⁴_Pl,red (Gram-corrected) | 7.14 × 10⁻¹²¹ | 7.15 × 10⁻¹²¹ | −0.07% |
| α_s(M_Z) | 0.11792 | 0.1179 ± 0.0009 | +0.02σ |
| m_τ / m_μ | 16.8173 | 16.8170 ± 0.0011 | +0.24σ |
| sin²θ_W | 0.23123 | 0.23121 ± 0.00004 | +0.40σ |
| m_μ / m_e | 206.50 | 206.77 | +0.13% |
| H₀ | 66.78 km/s/Mpc | Planck: 67.4 ± 0.5 | Planck-compatible |
| Universe age | 13.88 Gyr | 13.80 ± 0.02 | +0.6% |

**See [PREDICTIONS.md](PREDICTIONS.md) for the full tiered table** (structural results, all precision derivations, frontier experimental predictions, and provisional items with known gaps).

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
| [`cascade-series-part6.tex`](src/cascade-series-part6.tex) | Part VI — Tower Growth, Inflation, and the Pre-Big-Bang from the Cascade (speculative extension; Tier 5) |

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

## Computational tools

Every numerical claim in the series is backed by a script in [`tools/`](tools/). The scripts are organised by role (generators, verifiers, closures, model checks) and share a single source of truth for cascade primitives in [`tools/cascade_constants.py`](tools/cascade_constants.py).

See [`tools/README.md`](tools/README.md) for the full index — which script backs which LaTeX citation, how to run each one, and which results it reproduces.

## License

This work is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Citation

See [CITATION.cff](CITATION.cff) for citation information.
