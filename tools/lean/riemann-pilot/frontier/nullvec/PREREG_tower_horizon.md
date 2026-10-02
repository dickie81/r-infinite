# Pre-registration 2: the tower up to the dimension horizon (round 87)

Committed before computing any kernel value at these layers or at this window. It extends `PREREG_tower_layers.md` (round 86). That test passed but could not discriminate the multiplier's shape from the Gaussian null at `d ≤ 60`.

## Setting

- Window `δ = 3.5`: `T₀ = 2πe^δ = 208.07`, dimension horizon `2T₀ = 416.1`.
- Direct kernel `K_a(i(d+½),0)/K_a(0,0)` for `d = 0, 25, 50, …, 500`.
- Two bases: `K = 15e^δ + 40 = 539` (top frequency `ω_K ≈ 968`) and `K = 25e^δ + 40 = 868` (`ω_K ≈ 1558`), both at `300 + 24e^δ` bits.

## Predictions

The quantities, with `z = d+½` and `η = z/(2T₀)`:
- `P1 = ln[ξ(d+1)/ξ(½)] + T₀[√(1+η²) − 1 − η·arsinh η]`, the closed-form multiplier (round 77);
- `N = ln[ξ(d+1)/ξ(½)] − τz²`, `τ = e^{−δ}/(16π)`, the Gaussian (round 70).

The registered criteria:
- **Validity.** The two bases agree to `≤ 1e-3` relative for every `d ≤ 500`. If not, the test is void at the layers where they disagree.
- **(A) P1 holds to the horizon and beyond.** `|meas/P1 − 1| ≤ 3e-3` for every `d ≤ 500`, i.e. `1.2 × 2T₀`.
- **(B) The Gaussian null fails.** `|meas/N − 1| > 3e-3` for every `d` with `300 ≤ d ≤ 500`.
- **(C) The residual is the known correction.** `meas − P1 = −c·z²`, with `c` within ±30% of `0.0058·e^{−2δ} = 5.3e-6`.

Expected separations, computed before the data: `N/P1 − 1 = 5.3e-3, 1.1e-2, 1.8e-2` at `d = 300, 400, 500`. The `τ` correction's relative size is `1.2e-3, 1.5e-3, 1.8e-3`.

The scoring script is `ztower_score2.py`.
