# Pre-registration: the cascade tower seen through the Weil window chain (round 86)

Committed before any computation of the quantities below. The owner's intuition is: "the Gamma and the arithmetic are the same object … the wiggles are arithmetic/topology".

The derivation uses theorems only (Check 8: the cascade hypothesis is not used):
- **The tower.** `riemann-indistinguishability.md` Theorem 1: the tower is `Γ_ℝ` at `s = d+1`, and `Ω(d) = 2/Γ_ℝ(d+1) = |S^d|`.
- **The explicit-formula bridge.** Theorem 1b: the tower potential is one side of the explicit formula, evaluated at `z = d+½`.
- **The functional equation.** `Ξ(i(d+½)) = ξ(−d) = ξ(d+1) = ½(d+1)d·Γ_ℝ(d+1)·ζ(d+1)`, checked to 20 digits at `d = 1, 2, 5, 10`.
- **The multiplier.** Round 77: the chain's kernel satisfies `K_a(z,0)/K_a(0,0) ≈ (Ξ(z)/Ξ(0))·exp{T₀[w arcsin w + √(1−w²) − 1]}`, with `w = z/(2T₀)`.

## Prediction P1 (the layer law)

At support `δ = 2a`, with `T₀ = 2πe^δ`, for layers `d = 0, 1, …`, with `η_d = (d+½)/(2T₀)`:

  `ln[K_a(i(d+½),0)/K_a(0,0)] = ln[ξ(d+1)/ξ(½)] + T₀[√(1+η_d²) − 1 − η_d·arsinh η_d]  (1 + O(e^{−δ}))`

Consequences:
- Layers `d ≪ 2T₀` are reproduced as `Γ_ℝ(d+1)ζ(d+1)`, up to the multiplier.
- The suppression becomes `O(1)` nats at `d ≈ 2√T₀`.
- It dominates beyond a dimension horizon `d* ≈ 2T₀ = 4πe^δ`.

## Test protocol

- **Windows.** A fresh window `δ = 4.3`, not computed before, plus `δ = 2` and `3` for the `e^{−δ}` trend.
- **Measurement.** The direct kernel at `z = i(d+½)` for `d = 0…60` (`zdirect.py` with an extended list), at `K = 15e^δ + 40`.
- **Score.** The ratio of measured to predicted log-ratio, per layer. P1 passes if `|ratio − 1| ≤ 3e^{−δ}` for all `d ≤ 2T₀`, and fails otherwise.
- **Null.** The same comparison with the multiplier replaced by the Gaussian `e^{τz²}` (round 70). The null must fail beyond `d ≈ √T₀`.

## Not pre-registered

- **No wiggle-frequency prediction.** No ball-topology prediction for the wiggle frequencies (`3π`, `5π/3`, `16π/3`, …; rounds 84–85) is registered. No derivation from theorems exists, and a list chosen now would be numerology.
- **The primes-off control** (round 86), recorded here: with the primes removed, the chain collapses. `ln K_a(0,0) = 0.18` at `δ = 1.5`, against `≈ 29` with primes, and the 2×2 kernel matrix is indefinite. So the trend `4πe^δ` is not "the Gamma part" alone: it is the Γ–prime balance.
