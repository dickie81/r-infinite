# Pre-registration 24: the tone formula on a real Dirichlet L-function, L(s, χ₋₄) (round 111)

Committed before anything about `L(s, χ₋₄)` is computed. The numerical predictions are added in a second commit, after the `L` lens's kernel is fitted but **before** the `L` chain or any per-prime response is computed.

**Object.** `χ₋₄` is odd and primitive, with conductor `q = 4`: `χ(2) = 0`, `χ(p) = +1` for `p ≡ 1 (mod 4)`, `−1` for `p ≡ 3 (mod 4)`. The completed function is `Λ(s) = (q/π)^{(s+1)/2} Γ((s+1)/2) L(s, χ₋₄)`. It has the Hardy-type function `Z(t) = e^{iθ_χ(t)} L(½ + it, χ₋₄)`, which is real, with `θ_χ(t) = (t/2)ln(q/π) + Im log Γ(¾ + it/2)` and zero density `≈ ln(qt/2π)/2π`.

**Steps.**
1. **Zeros** of `Z` up to `t = 1000`, from sign changes refined by root-finding. Check against the Riemann–von Mangoldt count.
2. **The `L` lens.**
   - Quantile base: `θ_χ(γ̃_k)/π + c = k − ½`, with `c` set by the mean of `N(t) − θ_χ(t)/π` over the computed zeros.
   - Smooth tail above 1000 with density `ln(qt/2π)/2π`.
   - Kernel dumps on `x ∈ [3, 12]` (226 windows): round 106's `klinkernel.py` with the `L` base and tail.
   - Chirp fit: round 108's `kchirp.py` procedure, giving `K̃_χ(r)`, `β′`, `r_e`.
3. **The formula for this lens, derived before computing.** The node alias is `e^{2iθ_χ}`, with `2θ_χ′ = ln(qγ/2π) = ln x + ln(2qr)`. The `m = −1` branch cancels `ln x`, as for ζ. Stationarity gives `K̃_χ′(r*) = ln(2qr*/p)`, and

   **`ω_p = 4π · stat_r [ r(1 + ln(p/2qr)) + K̃_χ(r) ]`**, with amplitude `∝ χ(p)p^{−1/2}`.

   For ζ (`q = 1`) this reduces to round 109. The conductor moves every prime's reading height by a factor of `q`:
   - without a chirp, `r* = p/2q`;
   - with `q = 4`, the oscillating region `r ≈ 1–2.2` is read by the primes near **`p ≈ 8–17`**, not by 2 and 3.
4. **Numerical predictions**, to be filled in by the amendment commit: `ω_p` for every prime `p ≤ 101` that has a stationary point inside the fitted range.
5. **The `L` chain.** Zero-side kernel on the true `L` zeros, and on the `L` base. Also the first-order per-prime responses `Δ₁^{(p)}` with the `L` kernel.

**Criteria** (the tolerances are fixed now):
- **L1.** Every prime with a predicted tone in range gets its own first-order response, whose strongest peak lies within ±0.5 of the prediction.
  - This needs at least 2 such primes to be meaningful.
  - L1 passes if at least 2/3 of them hit.
- **L2.** The full `L` chain's residual has its two strongest lines each within ±0.5 of some predicted `ω_p` (among the primes in range).
- **L3.** There is no line within ±0.5 of 9.47, the ζ chain's `p = 2` tone, in the `L` chain's top 3. The prime 2 is absent, and 3 is predicted to be read outside the oscillating region.

The formula passes on this `L`-function only if L1 and L3 hold. L2 is reported.

## Amendment 1 (committed after the `L` kernel dumps, before any chirp fit, prediction, `L` chain or per-prime response)

**What the kernel shows.** The `L` lens's edge is not at ζ's position. `F′²/s` drops below 1 already at `r = γ/4πx ≈ 0.1–0.2`, against ζ's `r_e ≈ 0.86`. The kernel's non-negligible oscillating region therefore sits at small `r`. Round 108's procedure hard-codes ζ's region: reference height 1.4 and upper limit 2.2. Applied unchanged, it would fit mostly noise.

**Amended procedure** (it uses kernel information only):
- **Edge.** `r_e^L(x)` is the largest node ratio at which `F′²/s > 1`. Windows where the first node is already below 1 are excluded from the mean.
- **Scale.** `λ = mean(r_e^L)/0.8613`, where 0.8613 is ζ's `r_e`.
- **Chirp model.** It is the round-108 model in the scaled height `s = r/λ`: reference `1.4λ`, fit range `[r_e, 2.2λ]`, and the same parameterisation `κ = ln x + c₀ + c₁(s − 1.4) + c₂(s − 1.4)²`.
- **Window-phase rate.** `β′ = φ₀′ − 4π·1.4λ(ln x + 1)`.
- **Formula.** Unchanged: `ω_p = 4π stat_r[r(1 + ln(p/2qr)) + K̃(r)]`, with `r*` searched in `[r_e, 2.2λ]`.

**Consequence for the registered expectation.** The pre-registration assumed the oscillating region stays at `r ≈ 1–2.2` and so expected `p ≈ 8–17`. Scaling the region by `λ` (about `1/q`) moves the readable primes back to small `p` (`r* ≈ p·e^{κ_c}/2q`). That expectation was wrong in advance. The criteria are unchanged.
- **L1** is scored only if at least 2 primes have in-range stationary points. Otherwise it is reported as *not meaningful*, and only L3, plus the single-prime check, stand.
