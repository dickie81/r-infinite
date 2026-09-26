# Pre-registration 25: a second L-function (χ₋₃, blind) and a widened kernel fit (round 112)

Committed before anything about `L(s, χ₋₃)` is computed.

**Widened fit (method, fixed now).** The round-111 chirp fit covered `[r_e, 2.2λ]`. The widened fit covers `[r_e, 4.0λ]` with two changes:
- **(i) Equal weighting of the oscillation.** Round 111 fitted the raw oscillation, where the fading far region barely counted. Here the oscillation is divided by its envelope before fitting, with `|env|` floored at 10% of its median.
- **(ii) A cubic chirp,** `κ = ln x + c₀ + c₁s′ + c₂s′² + c₃s′³`, with `s′ = r/λ − 1.4`.

Everything else follows round 111 and its amendment 1: the edge `r_e`, `λ = mean(r_e)/0.8613`, the window-phase rate `β′`, and the formula `ω_p = 4π stat_r[r(1 + ln(p/2qr)) + K̃(r)]`, with `r*` searched in `[r_e, 4.0λ]`. A prime whose `r*` lies beyond `3.0λ` is marked *far* and reported separately.

**A. `L(s, χ₋₃)`, blind.**
- **Character and Γ factor.** Conductor `q = 3`; `χ₋₃` is odd, with `χ(3) = 0`, `χ(p) = +1` for `p ≡ 1 (mod 3)` and `−1` for `p ≡ 2 (mod 3)`. The Γ factor matches `χ₋₄`'s: `θ_χ = (t/2)ln(3/π) + Im log Γ(¾ + it/2)`.
- **Steps**, as in round 111:
  1. zeros to 1000;
  2. quantile base;
  3. kernel dumps with `LCOND = 3`;
  4. widened fit;
  5. **predictions committed as an amendment before the chain or any per-prime response is computed**;
  6. the chain, the base chain and the first-order per-prime responses.
- **Criteria:**
  - **L1:** at least 2/3 of the predicted in-range (non-far) primes have a first-order strongest tone within `±0.5` of the prediction. This needs at least 2 such primes.
  - **L2:** the chain's two strongest lines each lie within `±0.5` of some predicted `ω_p`.
  - The formula passes on `χ₋₃` if L1 and L2 both hold.

**B. `χ₋₄` with the widened fit: not blind.** `χ₋₄`'s chain and first-order responses were computed in round 111, with lines 4.23, 1.61, 7.55, 10.77 and per-prime tones `p = 5` → 7.59, `p = 7` → 2.70, `p = 11` → 5.76. So the widened `χ₋₄` predictions are a **consistency check only**, reported but not counted as evidence:
- whether 4.14 survives the widened fit;
- whether `p = 5` now gets a prediction near 7.59.

## Amendment 1 (committed after part B's widened fit on `χ₋₄`, before the `χ₋₃` kernel dumps or anything later)

**Part B result: the widened method is unstable.** It uses the envelope-normalised fit, a cubic chirp and the range `[r_e, 4λ]`. Applied to `χ₋₄` (`kLwide.py`, `Lwide_predictions.json`):
- **Poor fit:** it captures only 65% of the normalised oscillation, and the chirp coefficients scatter widely (sd 0.14, 0.31, 0.52, 0.20).
- **Inconsistent window-phase rate:** `β′` comes out at −0.56, −8.27 and −1.74 on the three segments. The phase `φ₀` is poorly determined once the fading far region is up-weighted.
- **Consequence:** `ω₃` becomes 1.33, with a `β′` range of −3.4 to 4.3, and `p = 5` gets 4.6 (range −0.1 to 7.6). The narrow fit's 4.14 is not preserved, and 7.59 is not predicted with any usable precision. **The consistency check fails. The widened method does not reproduce a known result.**

**Amended plan for `χ₋₃`.** Both predictions are committed before the chain:
- **A1 (as registered):** the widened method. Primary.
- **A2 (added):** round 111's narrow method, `[r_e, 2.2λ]`, quadratic chirp, unnormalised: the method that predicted `χ₋₄`'s 4.14.

Each is scored with the registered L1/L2 criteria, and they are reported separately. An A2 pass would not rescue the widened method. It would only mean that the narrow method transfers to a second `L`-function.

## Amendment 2: the `χ₋₃` predictions (committed after the `χ₋₃` kernel fits, before the `χ₋₃` chain, base chain or any per-prime response)

**`χ₋₃` lens.** 823 zeros to 1000, starting 8.0397, 11.2492, 15.7046, 18.2620 (the known values), with no missed zeros. `r_e = 0.278 ± 0.018`, and `λ = 0.323 ≈ 1/3.1`.

**A1, widened method (primary as registered).**
- Normalised variance captured: 0.59.
- `β′` segments: −0.58, −4.95, −13.76.
- Predictions: `p = 2` gives `ω = −2.45`, i.e. a line at 2.45, with a `β′` range of −9.8 to 3.4, i.e. anywhere in 0–9.8. `p = 5` is *far*: 4.62, range −2.7 to 10.5.

**A1 is uninformative.** Its ranges cover almost the entire low-frequency band, so it cannot fail. It is recorded as *no usable prediction*, and its L1/L2 are not scored. This is the same instability found in part B.

**A2, narrow method (round 111's).**
- Variance captured 0.95; `β′` segments −0.71, −0.79, −0.85, which is stable.
- **Only `p = 2` (`χ = −1`) is read in range: `r* = 0.409`, `ω₂ = 3.22` (range 3.15–3.29).**
- L1 is not meaningful with one prime.

It is scored as round 111 was:
- **single-prime check:** `Δ₁^{(2)}` with the `χ₋₃` kernel has its strongest peak within ±0.5 of 3.22;
- **chain check:** the `χ₋₃` chain's strongest line lies within ±0.5 of 3.22.

Also reported: whether the ζ `p = 3` line (16.75) is absent from the chain's top 3, since `χ(3) = 0`.
