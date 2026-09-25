# Pre-registration 4: topological depths in the wiggles (round 89)

Committed before computing any statistic below.

**Depth map (derived, not fitted).** The closed-form multiplier `ln M(z) = T₀[w·arcsin w + √(1−w²) − 1]`, `w = z/(2T₀)`, has its branch point at `z = 2T₀ = 4πx`. Round 87 confirmed that the chain carries the tower at `z = i(d+½)` up to this horizon. Tower index `d` carries `Ω(d) = |S^d| = 2/Γ_ℝ(d+1)`, so it is cascade layer `D = d+1`, whose sphere is `S^{D−1}` in Part IVa's convention. The horizon therefore reaches layer `D` at

`x_D = (D − ½)/(4π)`.

**Hypothesis T.** A topological feature of cascade layer `D` shows in the wiggles of `ln K_a(0,0)` (smooth fit and junction step removed, exactly as in `kspectrum2.py`) when the horizon passes `x_D`. A feature recurring with period `P` in `D` then gives a spectral line at `ω = 2π·4π/P = 8π²/P` in `x`. The slope `4π` is fixed by the multiplier; no other slope is tried.

**Accessible depths.** The data cover `x ∈ [1.65, 54.6]`, i.e. `D ∈ [21.2, 686.6]`. So `d_V = 5`, `d₀ = 7`, `d₁ = 19` and the Adams/Hopf dimensions are below range and untestable here. `d₂ = 217` is at `x = 17.23`.

**Tests.** A line passes if the maximum spectral power within `±` one resolution bin `2π/L` of the target exceeds the 95th percentile of the bin powers in the flanking band given, with `±1` around the target excluded. The spectra use the `kspectrum2.py` method (uniform x-resample with 8192 points, cubic detrend, Hann window).

| Test | Topology | Period in `D` | Target | Range | Flank band | Blind? |
|---|---|---|---|---|---|---|
| H2 | hairy ball / Lefschetz: `S^{D−1}` even iff `D` odd | 2 | `4π² = 39.48` | `x ∈ [1.65, 20]` (fine grid only; Nyquist ≥ 62) | `[30, 50]` | yes: no spectrum above ω = 26 was examined before |
| H3 | Bott / Clifford, fermion layers `D ≡ 5 mod 8` | 8 | `π² = 9.87` | `[1.65, 54.6]` | `[5, 15]` | **no**: the known dominant line is 9.38 ± 0.02, so H3 is expected to fail |
| H4 | Bott half-period (real ↔ quaternionic) | 4 | `2π² = 19.74` | `[1.65, 54.6]` | `[15, 25]` | **no**: 19.74 was absent from earlier top-8 lists |
| H1 | the threshold `d₂ = 217` (one-shot) | — | `x = 17.23` | `[3, 19]` | — | yes |

**H1** uses the residual `r(x)`. At each grid point `x_c ∈ [3, 19]`, fit straight lines to `r` on `[x_c − 1, x_c]` and `[x_c, x_c + 1]`. Two statistics are formed:
- `J(x_c)`: the jump between the two fits at `x_c`;
- `R(x_c)`: the rms of `r` on `[x_c − ½, x_c + ½]`.

H1 passes if `max J` or `max R` over `|x_c − 17.23| ≤ 0.1` ranks in the top 2.5% of all `x_c` (Bonferroni over the two statistics).

**Verdict rule.** Hypothesis T is supported only if a blind test passes (H1 or H2). A pass on H3 or H4 alone is not claimed, since those are not blind. Multiplicity is four tests, so one blind pass at 5% is suggestive only.

**Expectation, stated before computing.** H3 fails, because 9.38 ≠ 9.87 and the discrepancy of 0.49 is four resolution bins. H4 probably fails. H1 and H2 are genuinely unknown.

**Recorded caveat.** A period-8 comb read with slope 12 instead of 4π would give `2π·12/8 = 3π` exactly, the measured line. The slope 12 is not derived; the multiplier fixes 4π. Adopting 12 would be a fitted parameter, so it is excluded here.
