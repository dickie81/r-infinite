# Pre-registration 3: the wiggles from the discrete zeros (round 88)

Committed before evaluating the model below on any grid.

**The model.** `riemann-indistinguishability.md` Theorem 1bm(v) gives the finite-δ formula from the same balayage with the zeros left discrete:

`F(δ) = min_T [ 4·Σ_{γ<T} ln((1 + √(1 − γ²/T²))·T/γ) − 2aT ]`,  `a = δ/2`,

which approximates `ln λ₁(δ)` up to an `O(δ)` offset. It has no free parameter. The zeros are the first 6700 from `tools/research/checkpoints/zeta_zeros_6700.json`. This is the zero side of the explicit formula that the paper (Theorem 1b) identifies with the cascade tower.

**Prediction P3.** The fine structure of the window chain's `ln K_a(0,0)` (rounds 82–85) is the discreteness structure of `−F(δ)`.

**Protocol.** Evaluate `−F` on the measured `δ` grid (`hamiltonian_grid_to3.jsonl` ∪ `hamiltonian_grid_x20_55.jsonl`, `x = e^δ ∈ [1.65, 54.6]`). Remove the same smooth fit (`e^δ, δ, 1, e^{−δ}`) from both. Compare them in `x`:
- **(i)** the model's dominant spectral line lies within ±0.2 of the measured `9.42` (≈ 3π);
- **(ii)** the correlation between the model and measured residuals is `≥ 0.5`.

P3 passes only if (i) and (ii) both hold.

**Null.** The same formula with the zeros replaced by the smooth Riemann–von Mangoldt density, i.e. the continuum `F`. Its residual must carry `< 10%` of the discrete model's residual variance. This confirms that any structure in the model comes from discreteness.

**Expectation, stated before computing.** Rounds 82–84 found the wiggles not log-periodic and not tied to zero crossings. The model's zero-crossing events at `T ≈ 2T₀ = 4πx` have local frequency `≈ 4π ln(2x)` in `x`, which drifts. So P3 is expected to fail. A failure would show that the paper's own discreteness mechanism is not the origin of the wiggles.
