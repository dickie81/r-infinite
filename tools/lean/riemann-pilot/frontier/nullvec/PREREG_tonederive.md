# Pre-registration 20: the tones from the first-order kernel (round 106)

Committed before any kernel profile beyond round 104's three samples, or any per-prime response, is computed.

**Derivation.**
- **First order.** To first order (round 104), `Δ₁(x) = Σ_k w_x(γ̃_k) δ_k`, with `w_x = −2F_kF′_k/s` from the Γ chain.
- **Displacements by prime.** Linearising `N(γ) = θ/π + 1 + S` gives `δ_k ≈ −S(γ̃_k)/ρ(γ̃_k)`, where `ρ = θ′/π = ln(γ/2π)/2π`. Split `S` by prime: `S = Σ_p S_p`, `S_p(γ) = −(1/π) Im log(1 − p^{−1/2−iγ})` (all powers of `p`).
- **Per-prime response.** So `Δ₁ = Σ_p Δ₁^{(p)}`, with `Δ₁^{(p)}(x) = −Σ_k w_x(γ̃_k) S_p(γ̃_k)/ρ(γ̃_k)`.
- **Poisson summation over the nodes.** The `m = 0` term is `−∫ W_x(γ) S_p(γ) dγ`. The kernel profile `W_x(γ) = U(γ/4πx)` has a sharp step at a height `r_e`. That step contributes an oscillation `∝ sin(4πx r_e ln p + const)`. The prime's tone in `x` is therefore

  **`ω_p = 4π r_e ln p`** (fundamental; `p^k` powers give `k·ω_p`).

  The `m ≠ 0` aliasing terms have stationary points at the fixed heights `γ = 2πp^{1/|m|}` and give no fixed tone.

**Defining `r_e` independently of the tones.** `r_e(x)` is the node-height ratio `γ/4πx` at which `F′_k²/s` crosses 1, by log-linear interpolation between nodes. Round 104 shows it collapses by many orders of magnitude across the edge. Take `r̄_e` as its mean over the grid.

**Computation.**
- Grid: `x ∈ [3, 12]`, 226 windows.
- Dump `w_x` and `F′²/s` at all 649 nodes (`klinkernel.py`, same kernel as round 104).
- Compute `Δ₁^{(p)}` for `p = 2, 3, 5, 7`, and check `Σ_{p ≤ 101} Δ₁^{(p)}` against round 104's `Δ₁` (the linearisation of `δ`).

**Predictions, all four fixed before computing.**
- **(E1)** `r_e(x)` is constant across the grid: its standard deviation is `< 0.05`.
- **(E2)** Each `Δ₁^{(p)}`'s strongest line lies within `±0.5` of `4π r̄_e ln p`, for at least 3 of the 4 primes.
- **(E3)** `2π/ln 2`: the true chain's main line equals `4π r̄_e ln 2` within `±0.5`, i.e. `r̄_e ∈ [1.02, 1.14]` if the main line is 9.42.
- **(E4)** The full family 9.42, 16.75, 23.5, … is not claimed. Any member that is not `k·ω_p` for small `p, k` is reported as underived.

**Recorded prior.** Round 96's F test (single-prime chains; lines against `ln p` scaling with `ω₂`) failed. That test used full nonlinear chains and a fitted `ω₂`; this one uses the linear kernel and an independently defined `r_e`. If E2 fails here too, the `ln p` reading is dead at first order.
