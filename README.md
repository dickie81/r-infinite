# The Cascade Series

The cascade series tests one hypothesis: the infinite-dimensional unit ball, descended to four dimensions, is indistinguishable from our universe. From a single axiom (orthogonality) and with zero free parameters, the series derives the cosmological constant, quantum mechanics, general relativity with d=4 and Lorentzian signature, the Standard Model gauge group and its symmetry breaking, three fermion generations, precision mass and coupling predictions, and the background cosmological parameters including a Hubble constant between the two competing measurements.

## Papers

| File | Title |
|------|-------|
| `cascade series cover sheet.tex` | Cover sheet and overview |
| `cascade series part0.0.tex` | Part 0.0 |
| `cascade series part0.tex` | Part 0 — Scale Variance from Orthogonality |
| `cascade series part1.tex` | Part I — Scale Variance from Orthogonality |
| `cascade series part2.tex` | Part II — Quantum Mechanics from the Cascade |
| `cascade series part3.tex` | Part III — General Relativity from the Cascade |
| `cascade series part4a.tex` | Part IVa — The Standard Model (Gauge Group, Symmetry Breaking, Three Generations) |
| `cascade series part4b.tex` | Part IVb — The Standard Model (Masses, Couplings, Precision Predictions) |
| `cascade series part5.tex` | Part V — Cosmology from the Cascade |

## Building PDFs

A GitHub Actions workflow automatically compiles all `.tex` files into PDFs on every push. PDFs are available as build artifacts.

To build locally, run:

```bash
latexmk -pdf "cascade series cover sheet.tex"
```

Or compile all files at once:

```bash
latexmk -pdf *.tex
```

## License

This work is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Citation

See [CITATION.cff](CITATION.cff) for citation information.
