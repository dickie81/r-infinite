# Pre-registration 13: the window's reading height (round 99)

Committed before any window-relative chain is computed.

**Construction.** At each window `x`, the edge is `E = 4πx = 2T₀`. For each index `k` (below 1000), use the true zero `γ_k` if `r_k = γ_k/E` lies in the band, and the smooth quantile otherwise:
- **keep-B:** the true zero is used for `r_k ∈ B`, quantiles elsewhere;
- **drop-B:** the quantile is used for `r_k ∈ B`, true zeros elsewhere.

There are ten equal bands `B_j = [0.2j, 0.2j + 0.2)`, `j = 1, …, 10`, covering `r ∈ [0.2, 2.2)`. The kernel is round 95's fast kernel (`kzeroside3.py`, with the same tail), on the grid `x ∈ [3, 12]`, 226 windows, giving 20 chains. For each chain we report the correlation with the true-zero residual and the 9.42 "present" test (round 97).

**Sensitivity.** The loss is `ℓ_j = 1 − corr(drop-B_j)`. The reading height is its centre of mass,

`r̄ = Σ ℓ_j r_j / Σ ℓ_j`, with `r_j` the band centres.

**Hypothesis RH (the p = 2 derivation of the line).** The main line is `p = 2`'s term `sin(t ln 2)` read at height `r̄·4πx`. That requires `r̄·4π ln 2 = 9.42`, i.e. `r̄ = 1.082`. RH passes if:
- **(i)** `r̄ ∈ [1.03, 1.13]`;
- **(ii)** the band `[1.0, 1.2)` has the largest loss `ℓ_j` of the ten.

**Alternatives.**
- The window reads at its nominal edge: `r̄ ≈ 1`, with `[0.8, 1.0)` largest.
- It reads broadly or deeper inside the window: `r̄ < 0.9`.

In either case, the p = 2 derivation at a single reading height fails.

**Expectation.** Unknown. Round 98 constrains only the absolute heights: the carriers lie between 100 and 200, with the edge up to 151. That is compatible with `r̄` anywhere in about 0.7–1.3.
