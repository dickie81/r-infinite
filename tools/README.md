# Cascade Series Computational Tools

This directory contains every script cited in the cascade series LaTeX sources, plus the shared primitives module and an archive of deprecated scripts. Scripts are grouped by role; each script is cited from a specific section of a specific paper (cross-references given below).

## Shared primitives: `cascade_constants.py`

Every numerical script reads its Part 0 quantities from `tools/cascade_constants.py` — the single source of truth for the cascade's Gamma-function primitives, layer constants, and cosmological parameters. Exports:

- **Layer function** — `R(d) = Γ((d+1)/2) / Γ((d+2)/2)`; `alpha(d) = R(d)² / 4`; `Omega(d) = 2 π^((d+1)/2) / Γ((d+1)/2)`; `V_ball(d)`; `N_lapse(d) = Γ((d+1)/2) · Γ((d+2)/2)`; observer exponent `p(d)`.
- **Distinguished layers** — `D_V = 5`, `D_0 = 7`, `D_GW = 14`, `D_1 = 19`, `D_2 = 217`.
- **Cosmological parameters** — `H0 = 66.78` km/s/Mpc, `Omega_m = 1/π`, `Omega_b = 1/(2π²)`, `Omega_r = 1/(4π⁷)`, `Omega_Lambda = (π−1)/π`, `N_eff = 3.044`, `c_km_s = 299792.458`, `M_PL_RED_GEV = 2.435e18`.
- **High-precision namespace** — `mp` provides the same functions via `mpmath` for arbitrary-precision computations (`mp.R`, `mp.alpha`, `mp.Omega`, `mp.N_lapse`, `mp.p`, `mp.pi`).

No free parameters are introduced anywhere in this tree — every number traces back to `cascade_constants.py` and ultimately to the cascade hypothesis.

## Running the scripts

All scripts are invoked from the repository root:

```bash
python3 tools/<subfolder>/<script>.py
```

Python 3.11+ is required. Dependencies are listed in `tools/requirements.txt` (`numpy`, `scipy`, `matplotlib`, `mpmath`, `sympy`). Install with:

```bash
pip install -r tools/requirements.txt
```

CI uses Python 3.12; scripts are also tested locally under pyenv 3.11.9 (`PYENV_VERSION=3.11.9 python tools/...`).

## Directory layout

```
tools/
├── cascade_constants.py    Shared primitives (above)
├── requirements.txt        Dependency list
├── generators/             Emit artefacts consumed by the LaTeX build
├── verifiers/              Verify structural / uniqueness claims in the series
├── closures/               Derive specific numerical closures cited in the series
├── model_checks/           Numerical model checks and cross-checks
└── archive/                Deprecated scripts kept for reference
```

---

## `generators/` — build-time artefact emitters

Scripts in this folder run as part of the LaTeX build (see `.github/workflows/build-latex.yml`) and write files under `src/generated/` that are `\input`-ed by the papers.

| Script | Output | Cited in |
|---|---|---|
| `generate_predictions.py` | `src/generated/predictions-table.tex` | cover sheet (parsed from `PREDICTIONS.md`) |
| `generate_bao_table.py` | `src/generated/bao-table.tex`, `src/generated/bao-values.tex` | Part V §BAO |
| `cascade_g_eff.py` | `src/generated/cascade_g_eff.json` | Part VI §radiation bath |
| `tower_growth_simulator.py` | `src/generated/tower_growth/summary.txt`, `src/generated/tower_growth/trace.json` | Part VI §tower growth (Issue #65) |

These four scripts must be runnable by CI. Any change here should be validated by a byte-identical diff against the committed `src/generated/` contents (modulo any intentional numerical change).

---

## `verifiers/` — structural and uniqueness claim verification

Scripts in this folder verify claims that the series frames as theorems or as mechanically-checkable facts. They are cited inline from the proofs they support.

| Script | Verifies | Cited in |
|---|---|---|
| `verify_continuous_boundary.py` | Cascade invariant ~10⁻¹²⁰ is the unique argmax of the continuous boundary action on the distinguished layers | Part 0 §continuous boundary |
| `verify_selection_rule.py` | Three-flag decision procedure that assigns `d*` to each of the seven precision observables (Definition of observable-type) | Part IVb §source selection, Prop `prop:source-selection` |
| `cascade_greens_function.py` | Eigenstructure of the cascade action's discrete Laplacian — the Green's function response is maximised at the assigned `d*` for each observable, to machine precision | Part IVb §Green's function identity, §source selection |
| `action_uniqueness.py` | Uniqueness of the cascade action principle: first-order Euler–Lagrange forces the quadratic nearest-neighbour form with compliance `alpha(d) = N(d)² / Ω₂` | Part IVb Remark 4.8 |

---

## `closures/` — numerical closures cited in the series

Scripts here derive specific numerical closures quoted in the papers from the cascade primitives alone.

| Script | Derives | Cited in |
|---|---|---|
| `cascade_v_closure.py` | Electroweak VEV `v` via the marginal Green's function identity on `S⁴` | Part IVb Remark 4.9 |
| `cascade_unified_descent.py` | All backward-descent steps of the cascade agree with the forward construction (consistency check) | Part I §unified descent |
| `btz_cross_check.py` | BTZ boundary-action cross-check — confirms the Part II=III entropy/temperature identities reduce correctly in the (2+1)D limit without parameter fitting | Part II=III §BTZ cross-check |
| `derive_alpha_s_closure.py` | Strong coupling `α_s` closure via the `α(d*)/χ^k` structural form | Part IVb §α_s closure (supporting computation) |
| `derive_2sqrtpi_no_dirac.py` | Verifies the `2√π` factor appearing in the boundary Green's-function identity is forced without invoking a Dirac structure | Part IVb §supporting computation |

---

## `model_checks/` — numerical cross-checks and model probes

Scripts here perform numerical checks that are not themselves proofs in the series but are cited as sanity checks, falsification tests, or "verified numerically" claims.

| Script | Checks | Cited in |
|---|---|---|
| `cascade_decoherence.py` | Decoherence coefficient from the cascade's spectral trace | Part II §decoherence |
| `cascade_decoherence_vs_tower_height.py` | Decoherence is insensitive to tower height — no approximation needed for the quoted value | Part VI §decoherence robustness |
| `fermion_dirac_spectral_zeta.py` | Tests the naive "fermion lapse = regularised Dirac spectral zeta on `S^{2n}`" conjecture at Dirac layers 5, 13, 21, 29. **Naive formulation falsified** — see `future-paper-fermion-cascade-dirac.md` for status. | Part IVc §Dirac (status note) |

---

## `archive/` — deprecated / superseded scripts

Scripts in `archive/` are retained for traceability but are **not** cited in the current series. They represent earlier computation paths that have been superseded. Do not cite these from new work.

| Script | Superseded by | Notes |
|---|---|---|
| `cascade_geometric_rd.py` | `generators/generate_bao_table.py` | Early geometric `r_d` computation |
| `cascade_geometric_rd_verify.py` | `generators/generate_bao_table.py` | Early verification pass for `r_d` |
| `desi_bao_recompute.py` | `generators/generate_bao_table.py` | Early DESI BAO recomputation |
| `desi_bao_sensitivity.py` | — | DESI sensitivity study (one-off) |
| `cascade_weinberg.py` | `verifiers/verify_selection_rule.py` + `closures/` | Early Weinberg-angle closure route |
| `compute_all_corrections.py` | Individual `closures/` scripts | Monolithic correction computer, split into per-observable scripts |
| `derive_kQ.py` | — | Early `k_Q` derivation |
| `derive_kQ_v2.py` | — | Second iteration of `k_Q` derivation |
| `purge_perturbation.py` | — | One-off perturbation-analysis utility |

---

## Contributing

1. **Single source of truth.** New scripts must import cascade primitives from `cascade_constants.py`. Do not redefine `R(d)`, `alpha(d)`, `Omega(d)`, or any Part 0 quantity locally.
2. **Folder choice.** If a script emits a file that LaTeX reads → `generators/`. If it verifies a claim framed as a theorem or uniqueness result → `verifiers/`. If it derives a specific closure cited in the series → `closures/`. If it is a numerical cross-check or probe → `model_checks/`.
3. **Citation.** Any script cited from the `.tex` sources must be referenced by its full path `\texttt{tools/<subfolder>/<script>.py}` (with LaTeX-escaped underscores `\_`).
4. **Archive, don't delete.** Scripts superseded by newer work move to `archive/` via `git mv`, not `rm`.
