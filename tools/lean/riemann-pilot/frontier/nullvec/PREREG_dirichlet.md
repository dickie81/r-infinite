# Pre-registration 23: character-twisted arithmetic through the ζ lens (round 110)

Committed before any twisted zero set or chain is computed.

**Scope, stated honestly.** The round-109 formula describes the ζ chain's lens (its Γ base and kernel `K̃`) acting on an arithmetic input. A true Dirichlet `L`-function has a different Γ factor and conductor, hence a different lens and its own `K̃`; testing it would first need that kernel. This test keeps the ζ lens and replaces the arithmetic input by a Dirichlet-twisted one:

`S_χ(t) = −(1/π) Σ_{p ≤ 101} Im log(1 − χ(p)p^{−1/2−it})`.

The zero set is built as in rounds 95–96: `θ/π + 1 + S_χ = k − ½`, taking all crossings with `t ≥ 10`. It is then run through the fast chain: `kzeroside2.py`, `x ∈ [3, 12]`, 226 windows.

**What the formula says.**
- `ω_p` depends only on `p`, through the stationarity `K̃′(r*) = ln(2r*/p)`.
- `χ(p)` multiplies the prime's wave. A sign flips its phase by π, and `χ(p) = 0` removes it; neither moves its frequency.
- Only `p = 2` (9.64) and `p = 3` (16.73) have reading heights in the lens's range.

**The two characters:**
- **`χ₋₄`**: `χ(2) = 0`, `χ(3) = −1`, `χ(5) = +1`, `χ(7) = −1`, …
- **`χ₋₃`**: `χ(3) = 0`, `χ(2) = −1`, `χ(5) = −1`, `χ(7) = +1`, …

**Predictions.** Tones are the strongest interpolated peaks in `[1.5, 40]`, taken from the residual after the 4-term smooth fit.
- **(D1) `χ₋₄`:** no peak within ±0.3 of 9.47 among the top 3, and the strongest peak within ±0.3 of 16.75.
- **(D2) `χ₋₃`:** the strongest peak within ±0.3 of 9.47, and no peak within ±0.3 of 16.75 among the top 3.

The formula passes only if D1 and D2 both hold.

**Recorded prior knowledge.** Rounds 96 and 103 already showed that only-2 chains carry a ≈ 9.4 line and only-3 chains a 16.75 line, with `χ = +1`. What is new here:
- the sign flips `χ(p) = −1` on the lines' own primes: 3 under `χ₋₄`, 2 under `χ₋₃`;
- the full twisted background of the other primes, with mixed signs;
- the claim that the frequencies are unmoved by those signs.

A failure would mean the per-prime frequency law does not survive sign changes and a mixed background.
