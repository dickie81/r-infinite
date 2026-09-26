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
