# The slack-law constant: potential-theory (Landau–Widom) analysis — Addendum 440

Research instruments, cited by no paper surface, keyed by nothing.

- `lw_variational.py` — the reduction (docstring) and the simplest admissible probe: f(X) = 2[max_in φ − sup_out φ] with φ(x) = ∫₀^X ln|1 − x²/y²| ln y dy.
- `lw_lp.py` — LP over the probe's zero-deviation density (cell-integrated kernel); `refined` mode.
- `lw_continuum.py` — the δ → ∞ problem with the in-band constraint made exact; the converged value f_∞ = 12.56 at X* = 2.00.
- `lw_semidiscrete.py` — the same LP at a physical δ with the zeta zeros discrete.
- `probe_test.py` — builds the explicit real-zero probe prescribed by an LP solution and computes its exact Rayleigh quotient (the test that showed the finite-δ model's O(log) slack).
- `probe_profile.py` — pointwise envelope check of a constructed probe against the reduction.
- `lp_*.json` — the LP solutions used in Addendum 440 (X = 2, continuum; the simple probe; the semi-discrete δ = 2.3 optimum).

Run from this directory (the zero list is read from `../checkpoints/zeta_zeros_2000.json`).
