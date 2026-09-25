# Pre-registration 5: digging the Bott (round 90)

Committed before any of the new data exist.

**Hypothesis B.** The dominant wiggle line (9.38 on `[1.65, 54.6]`, 9.28 on `[20, 37]`) is Bott periodicity: a pattern of period 8 in the integer cascade layers `D`, seen through some linear depth map `D ≈ s·x + c`. The slope `s` is **not** assumed; round 89 excluded the derived slope `4π`. With `s` left free, B makes two predictions that do not depend on `s`. They also do not depend on which 8-periodic pattern is meant (fermion layers `D ≡ 5 mod 8`, the KO sequence, the Clifford types):
- **B1: harmonics.** A pattern on integer layers is not a pure sinusoid, so there are lines at `k·ω₁` for integer `k`, with `ω₁` the fundamental.
- **B2: the lattice line.** Features sitting on integer layers give a line at `8ω₁ = 2πs`, the layer spacing itself. For any pattern with nonzero mean (every one listed), this line is present. It is the Bott-specific signature: the line at *eight times* the fundamental is what "period 8 in integer layers" means.

Both predictions can be killed by smearing. If each layer's feature is spread over ≳ 1 layer in `x`, both B1 (k ≥ 3) and B2 are suppressed. A failure therefore means "Bott is not visible as a lattice pattern at this resolution", not "Bott is refuted".

**New data (blind).** Previously the data on `[20, 54.6]` had step 0.12 (Nyquist 26), so no line above 26 was ever observed for `x ≥ 20`. The new windows are `x_j = x₀ + 0.03j`, with `x₀ = e^{2.9957323}`, `j ≢ 0 (mod 4)`, `x ≤ 37.04`: 426 windows with the same basis (`K = 15x + 40`, `300 + 24x` bits). Merged with the existing points, this gives a uniform step of 0.03 (Nyquist 104.7) on `[20, 37.04]`, where the basis is uniform and there is no junction. The output file is `hamiltonian_grid_x20_37_fine.jsonl`.

**Protocol** (`kbott.py`):
- Residual: `ln K00` minus a least-squares fit in `(e^δ, δ, 1, e^{−δ})` on this segment.
- Spectrum: uniform resample to 8192 points, cubic detrend, Hann window.
- Resolution: `res = 2π/L`.
- `ω₁` is the highest peak in `[8, 11]`.
- Line test: a line at `ω` passes if the maximum power within `±res` exceeds the 95th percentile of the bins in `[ω − 4, ω + 4]`, with `±1` excluded.

| Test | Target | Passes if | Blind? |
|---|---|---|---|
| B1 | `3ω₁` and `4ω₁` | either line passes | yes |
| B2 | `8ω₁` | that line passes | yes |

The following are reported for description only and are not scored:
- the lines at `2ω₁`, `5ω₁`, `6ω₁` and `7ω₁` (`2ω₁ ≈ 18.6` lies below 26 and was seen before as weak/absent, so it is not blind);
- the strongest line in `[50, 100]` and its ratio to `ω₁`.

**Verdict rule.**
- B2 passes: the evidence is for a period-8 lattice on integer layers, with slope `s = 8ω₁/2π` measured, not fitted. This is the strongest outcome available.
- Only B1 passes: the line is a non-sinusoidal periodic signal. That is consistent with a lattice pattern but not specific to Bott.
- Both fail: the line is effectively sinusoidal at this resolution, and Bott is not visible.

**Expectation, stated before computing.** Unknown. The earlier `(26, 62)` scan on `[1.65, 20]` (seen in round 89) showed no obvious line at `3 × 9.6 ≈ 28.8`, which leans toward B1 failing. That scan covered only small `x`, where layer features would be most smeared.
