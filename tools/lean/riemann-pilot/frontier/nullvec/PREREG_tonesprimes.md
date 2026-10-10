# Pre-registration 17: which primes fix the tone set? (round 103)

Committed before any chain below is computed.

The tone set is 9.29, 16.75, 23.56, 30.14, 36.69 and 42.97, at band centres `r` = 1.1, 1.5, 2.1, 2.6, 3.0 and 3.4 (round 102). The full primes and `P = 7` reproduce it to `≤ 0.05`.

**Sets** (round 95 construction, crossings with `t ≥ 10`):
- `Q = {2}`;
- `Q = {3}`;
- `Q = {2, 3}`;
- `Q = {2, 3, 5}`.

A set one zero short near `t = 1000` is completed by the quantile (`kzeroside3.py`; this changes nothing within the bands used, which reach `γ ≤ 3.5·4π·12 = 528`).

The run uses the six bands of round 102 (keep-B), with the `P = 7` reference already computed, giving 24 chains. A band **hits** if its strongest interpolated peak in `[4, 45]` lies within `±0.3` of the true tone for that band.

**Predictions.**
- **T23.** `Q = {2, 3}` hits `≥ 5` of 6.
- **T2.** `Q = {2}` alone hits `≤ 3` of 6. Two was the main-line driver (round 96), but only-2 misplaced the line by one bin.
- **T3.** `Q = {3}` alone hits `≤ 3` of 6.

**Minimal set.** The smallest set, in the order `{2}`, `{3}`, `{2, 3}`, `{2, 3, 5}`, `{2, 3, 5, 7}`, that hits 6 of 6 is reported as the carrier of the tone set.

**Expectation.** Rounds 95–96 suggest that 2 sets the main line and 3 the 16.75 line, so the pair may generate the family. If `{2, 3}` suffices, the target formula involves only `ln 2` and `ln 3`.
