# Pre-registration 12: which heights carry the line family? (round 98)

Committed before any band-swapped set is computed.

**Sets.** Take the true zeros and the smooth quantiles below 1000 (649 each, matched by index; round 95).
- **L_H:** true zeros for `γ < H`, quantiles above.
- **U_H:** quantiles below `H`, true zeros above.

`H ∈ {30, 50, 100, 200, 500}`. The kernel, grid and detection are those of round 97 (the fast kernel, `x ∈ [3, 12]`, 226 windows, and the interpolated-peak "present" test for 9.42, 4.97 and 16.75). Also reported: the correlation with the true-zero residual, and the rms ratio.

**Scale.** On this grid the window's edge `2T₀ = 4πx` runs from 38 (x = 3) to 151 (x = 12).

**Hypothesis LOW** (round 97: the low zeros, coherently displaced).
- Under L_50 the 9.42 line is present, and the correlation is `≥ 0.7`.
- Under U_50 the 9.42 line is absent.

**Hypothesis EDGE** (the window reads the zeros near its moving edge).
- L_100 lacks the 9.42 line and L_200 has it, i.e. the zeros up to the maximal edge (≈ 151) are needed.
- U_H keeps the line for `H ≤ 30`.

At most one of LOW and EDGE can pass. If neither passes, the carrier is distributed over heights; report the correlation-versus-H curve.

**Expectation.** LOW is the round-97 lead. EDGE is the natural reading of the window. My guess is EDGE, because the window's sensitivity peaks at its edge (rounds 80–87).
