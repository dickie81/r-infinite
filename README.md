# The Cascade Series

**[Read the papers online](https://dickie81.github.io/r-infinite/)**

The cascade series tests one hypothesis: the infinite-dimensional unit ball, descended to four dimensions, is indistinguishable from our universe. From a single axiom (orthogonality) and with zero free parameters, the series derives the cosmological constant, quantum mechanics, general relativity with d=4 and Lorentzian signature, the Standard Model gauge group and its symmetry breaking, three fermion generations, precision mass and coupling predictions, and the background cosmological parameters including a Hubble constant between the two competing measurements.

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
