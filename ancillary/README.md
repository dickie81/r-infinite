# Ancillary Materials — Infinite Nested Black-Hole Tower Cosmology

**Status:** v0.1 stubs (February 2026) | Full release v0.2 with Zenodo DOI (March 2026)

### Contents
- `GL_shooting.py` — SciPy-based shooting solver for the master radial ODE (generalized Gregory–Laflamme + regulator δV_λ). Reproduces the D=5 benchmark and permits exploration of the D→4 limit.
- `contents.md` — complete manifest and release checklist.
- (forthcoming) `junction_montecarlo.ipynb` — 8D Gaussian + WKB overlap sampler for Table 1.
- (forthcoming) `SO8_branching.nb` — Mathematica notebook with explicit generator matrices and junction-filter projections.

### Quick execution (Python stub)
```bash
cd ancillary
python GL_shooting.py --D 5.0 --lambda_reg -0.083333