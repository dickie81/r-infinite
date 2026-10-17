# Pre-registration 16: is the ladder real, and whose is it? (round 102)

Committed before any computation below.

Before we derive the irregular plateau boundaries, three controls decide what the ladder *is*. At the six plateau centres, the true-zero ladder (rounds 100–101) gives:

| band `r` | [1.1, 1.2) | [1.5, 1.6) | [2.1, 2.2) | [2.6, 2.7) | [3.0, 3.1) | [3.4, 3.5) |
|---|---|---|---|---|---|---|
| tone | 9.29 | 16.75 | 23.56 | 30.14 | 36.69 | 42.97 |

**S (sub-range stability; no new chains).** Re-analyse all 26 existing band chains (rounds 100–101) separately on `x ∈ [3, 7.5]` and `[7.5, 12]` (resolution 1.40). S passes if, in `≥ 80%` of the bands, both halves' dominant `ω` in `[4, 45]` lie within `±1.40` of the full-range `ω`. If S fails, the ladder is an artefact of the finite analysis range.

**C (construction control).** Rerun the keep-band construction at the six centres with the true zeros replaced by round 97's *white-jittered* quantiles (N1, seed 1), which carry no arithmetic. There are 6 chains.
- **ARTEFACT** holds if `≥ 4` of the 6 bands give a tone within `±0.6` of the true ladder's tone for that band. The ladder would then come from the band construction and the window, not from the arithmetic.
- **ARITH** holds if `≤ 1` of 6 do.

**D (another arithmetic).** Run the same six bands with round 95's `P = 7` zero set, which is arithmetic but differs from the true zeros (correlation 0.90). There are 6 chains. **UNIVERSAL-RUNGS** holds if `≥ 4` of 6 give the true ladder's tone (±0.6).

Detection is the round-100 method: the strongest interpolated peak in `[4, 45]`, fast kernel, `x ∈ [3, 12]`, 226 windows.

**Expectation.** S should pass, because the rungs were stable to 0.3 within plateaus. C is the real question. D is likely to pass if C gives ARITH.
