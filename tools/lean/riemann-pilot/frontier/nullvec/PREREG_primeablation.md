# Pre-registration 10: one prime at a time, and one prime removed (round 96)

Committed before any of these zero sets or chains is computed.

**Construction.** This is the same as round 95 (`θ/π + 1 + S_Q = k − ½`, `kzeroside2.py`, `x ∈ [3, 12]`, step 0.04, 226 windows), with `S_Q` summed over a *set* `Q` of primes (all powers of each):
- **only-p:** `Q = {p}`;
- **minus-p:** `Q` = the primes `≤ 101` without `p`;

for `p ∈ {2, 3, 5, 7, 11, 13}`. The baseline is round 95's `P = 101` (correlation 0.945 with the true-zero wiggles). The drop is `D(p) = 0.945 − corr(minus-p)`.

**Weights, for reference.**
- In the zero displacement, prime `p` enters as `p^{−1/2} sin(t ln p)/π`, with amplitude `1/√p`, largest for 2.
- In the Weil form it enters with weight `ln p/√p`: 0.490, 0.634, 0.720, **0.736**, 0.723 and 0.711 for 2, 3, 5, 7, 11 and 13, maximal at `p = 7` because the continuous maximum is at `e² ≈ 7.39`.

**Hypothesis D7 (the owner's: 7 is special).**
- `D(7)` is the largest of the six drops.
- It also exceeds both `D(5)` and `D(11)` by a factor `≥ 1.5`, i.e. clearly more than the Weil weights predict, since those three weights lie within 2%.

D7 passes only if both hold.

**Hypothesis F (frequency ∝ ln p, towards a derivation).** Only-p's strongest line in `[2, 40]` lies within `±1` resolution bin (0.70) of `ω₂·ln p/ln 2`, with `ω₂` only-2's strongest line. The predictions are, for `ω₂ ≈ 9.77`: 15.5, 22.7, 27.4, 33.8 and 36.2 for `p` = 3, 5, 7, 11 and 13. F passes if this holds for at least 4 of the 5 primes `p ≥ 3`.

**Also reported** (descriptive): each variant's correlation, rms ratio, top lines, and the 9.075 line test.

**Expectation, stated before computing.**
- D7: expected to fail. I expect the largest drop at `p = 2`, since 2 alone makes the line.
- F: genuinely unknown. The window may read each prime's oscillation at the same reading height, which would give F, or not.
