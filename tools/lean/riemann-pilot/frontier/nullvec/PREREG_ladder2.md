# Pre-registration 15: does the staircase continue? (round 101)

Committed before any band above `r = 2.5` is computed.

**Construction.** This is round 100's method (keep-bands, `kzeroside3.py`), with ten bands of width 0.1 covering `r ∈ [2.5, 3.5)`. The top band reaches `γ ≤ 3.5·4π·12 = 528 < 1000`. `ω` is the strongest interpolated peak in `[4, 45]`, and the second peak is recorded.

**Predictions** (from round 100's rungs 9.3, 16.7, 23.4 and the emerging ≈ 30.0):
- **P4.** The fourth rung, `ω ∈ [29.0, 31.0]`, is the dominant peak in a contiguous run of `≥ 2` bands.
- **P5.** A fifth rung, `ω ∈ [35.5, 38.5]`, appears as the dominant or second peak in `≥ 2` bands. The band where it first appears lies above the start of the P4 run.
- **Order.** Assign each band's dominant `ω` to its nearest rung (23.4, 30.0 or the fifth-rung window). Moving up in `r`, the assigned rung never decreases.

The staircase continues if P4, P5 and Order all hold.

**Recorded caveats.**
- The plateau widths so far are 0.4, 0.4 and ≥ 0.7. Where the third-to-fourth step falls is not predicted.
- If the third rung (23.4) persists across all ten bands, P4 fails, even though the ladder might resume higher up.
