# The slack-law constant: potential-theory (Landau–Widom) analysis — Addenda 440–442

Research instruments, cited by no paper surface, keyed by nothing.

- `lw_variational.py` — the reduction (docstring) and the simplest admissible probe: f(X) = 2[max_in φ − sup_out φ] with φ(x) = ∫₀^X ln|1 − x²/y²| ln y dy.
- `lw_lp.py` — LP over the probe's zero-deviation density (cell-integrated kernel); `refined` mode.
- `lw_continuum.py` — the δ → ∞ problem with the in-band constraint made exact; the converged value f_∞ = 12.56 at X* = 2.00.
- `lw_semidiscrete.py` — the same LP at a physical δ with the zeta zeros discrete.
- `probe_test.py` — builds the explicit real-zero probe prescribed by an LP solution and computes its exact Rayleigh quotient (the test that showed the finite-δ model's O(log) slack).
- `probe_profile.py` — pointwise envelope check of a constructed probe against the reduction.
- `balayage_check.py` — Addendum 441: the equilibrium problem solved in closed form by balayage onto the doubly slit plane; checks B = −(π/2)(1 + ln 2), the positivity of the balayage density on the exterior (admissible for X ≤ 2.05), the constancy of the potential there (−2π at X = 2), the interior bound, and f(X) = 2πX(1 + ln 2 − ln X), maximal at X = 2 with f_∞ = 4π.
- `discrete_balayage.py` — Addendum 442: the finite-δ balayage formula ln λ₁ ≈ min_T 2 s_δ(T), s_δ(T) = 2 Σ_{γ<T} ln[(1 + √(1 − γ²/T²)) T/γ] − aT, against the exact zero-side values (offset 5–8 nats through δ = 3.5).
- `lp_*.json` — the LP solutions used in Addendum 440 (X = 2, continuum; the simple probe; the semi-discrete δ = 2.3 optimum).

Run from this directory (the zero list is read from `../checkpoints/zeta_zeros_2000.json`).
