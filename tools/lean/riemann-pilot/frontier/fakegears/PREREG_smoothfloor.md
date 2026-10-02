# Pre-registration: gear sets with a perfectly smooth floor (round 179)

Written and committed before `ksmoothfloor.py` is run.

## Question (the owner's)

Round 178 left one case untested: gear sets other than the real primes whose integers are
perfectly regular. Does a smooth floor force the drift down to `√x`?

## Construction: "floor first"

Choose the target floor `T(x)` first, then find gears that realise it. Walk `n = 1, 2, …, X`:
- `a(n)` is the number of ways to write `n` as a product of gears already chosen (all `< n`);
- place `g(n) = max(0, round(T(n) − N(n−1) − a(n)))` new gears at `n`, where `N(n−1)` is the running integer count.

The floor error then stays within ½ unless `a(n)` alone overshoots the target.

**Sanity property.** With `T(x) = x` this rule selects exactly the primes. This is checked in the run (S1).

## Systems (to `X = 10⁷`)

| id | target floor `T(x)` |
|---|---|
| S1 | `x` (control, must reproduce the primes) |
| Sa | `1 + A(x−1)` for `A = π/4, 0.9, 1.1, √2, 2, e` |
| W25 | `x + 0.5·x^{1/4}·cos(5 log x)` for `x ≥ 10³` (a planted floor tone below ½) |
| W40 | same with `x^{0.4}` |

## Measurements

As round 178:
- **Floor** `F = N − T`.
- **Drift** `D = ψ_P(x) − x`, where `ψ_P` counts gears and their powers with weight `log`. The Beurling prime number theorem gives `ψ_P ~ x` whatever `A` is.
- **Exponents** from dyadic block maxima, `j = 14…22`.
- **For W25/W40:** the amplitude of the planted tone `x^{θ}cos(5 log x)` in `D`, fitted on `[10⁵, 10⁷]`.

## Hypothesis H (owner's): smooth floor ⇒ drift at most random-walk size

> For every system with measured `θ_F ≤ 0.25`, `θ_D ∈ [0.40, 0.65]`.

(The band is wider than round 178's; that round showed ±0.15 slope noise.)

- **H is falsified** by any such system with `θ_D > 0.65`.
- A system with `θ_D < 0.40` and a smooth floor would contradict Hilberdink's theorem
  (`max(θ_N, θ_ψ) ≥ ½`, recalled, not re-read), so it would point to a code error or a finite-range artefact.

## Predictions (mine)

- **S1:** gears = primes exactly, `θ_F = 0`, `θ_D ≈ 0.48` (as R1).
- **Sa:** the floor stays smooth (`θ_F ≤ 0.25`) for `A ≤ 1.1`. For `A ≥ √2` the greedy may be forced to overshoot (`a(n)` already exceeds the target), which roughens the floor; I record `θ_F` whatever it is. Where the floor is smooth, I predict H holds.
- **W25, W40:** the drift carries the planted tone amplified by roughly `log x` (the inverse of round 178's leakage), so its amplitude ratio is `≈ log x / 0.75`. This is weakly held.

**Bearing on RH:** none possible. These are finite-range numerics on toy systems.
