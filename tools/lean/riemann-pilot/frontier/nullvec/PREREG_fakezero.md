# Pre-registration 14: are the octonion (8D) and quaternion (4D) mirror averages blind to an off-line zero? (round 174)

Committed before any value below is computed.

**The question (the owner's).** The octonions keep appearing (Hurwitz dimension 8, `E₈ = 240·2^{−s}ζ(s)ζ(s−3)`, the real-rooted 8D superposition of round 94). Do they constrain where ζ's zeros are?

**The test: a planted violation.**
- **Fake function:** `Ξ̃(z) = Ξ(z)·(z² − w²)(z² − w̄²) / ((z² − γ₁²)(z² − γ₂²))`, with `w = (γ₁ + γ₂)/2 + iη` and `γ₁ = 14.1347…`, `γ₂ = 21.0220…`.
- `Ξ̃` is even, real on ℝ, entire, and of the same order as `Ξ`. It equals Riemann's `Ξ` except that two real zeros are replaced by an off-line quadruple `±w, ±w̄` at distance `η` from the line: a planted RH violation.
- **Mirror averages:** `G_b(t) = Ξ̃(t + ib) + Ξ̃(t − ib)` for `b = ¼` (the "3D" gap), `½` (4D, quaternionic) and `3/2` (8D, octonionic).
- **Tilts:** `η ∈ {0.3, 0.45}`, and `η = 0` as the control (true `Ξ`).

**Measurement.**
- Zeros of `G_b` in `|z| < 30` by the argument principle, against its real zeros (sign changes) on `(−30, 30)`.
- "Real-rooted" means the two counts agree.
- Evaluation uses mpmath at 40 digits, with ξ on `Re s < ½` via `ξ(s) = ξ(1 − s)`.

**Predictions** (de Bruijn: `G_b` is real-rooted whenever `b ≥` the largest `|Im|` of `Ξ̃`'s zeros, which is `η` here):
- **F1 (octonionic blindness).** `b = 3/2`: real-rooted for `η = 0, 0.3, 0.45`. It cannot see the planted violation.
- **F2 (quaternionic blindness).** `b = ½`: real-rooted for `η = 0, 0.3, 0.45`.
- **F3 (detection only below the tilt).** `b = ¼`: real-rooted for `η = 0`. For `η = 0.3` and `0.45` (`b < η`), non-real zeros are allowed but not guaranteed. Report as found.

**What this can mean.**
- **If F1 and F2 hold:** the 8D and 4D structures give the same verdict (real-rooted) with and without an RH violation, so they carry no information about whether RH holds. Their real-rootedness comes from de Bruijn's theorem and the width of the critical strip, not from the zeros' positions.
- **If F1 or F2 fails:** that would contradict de Bruijn's theorem, and would first be checked as a numerical error.
