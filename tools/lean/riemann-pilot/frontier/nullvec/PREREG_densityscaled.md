# Pre-registration 13: sphere-weighted superposition with physically rescaled grids (round 172, the owner's "B")

Committed before any value below is computed.

**The object.** Rescale each dimension's grid so its point density equals the layer surface-area ratio:
- `ρ_d = S_{d−1}/S_{d−2} = √π Γ((d−1)/2)/Γ(d/2)`, for `d ≥ 2` (`ρ₁` is undefined since `S_{−1} = 0`);
- scale `λ_d = ρ_d^{−1/d}`.

A scaled lattice has zeta `λ^{−2s}Z_L(s)`. On the d-slice's centre coordinate `s = d/4 + iz` this is `ρ_d^{1/2}e^{ic_d z}` with `c_d = 2 log(ρ_d)/d`. So

  `G_B(z) = Σ_{d≥2} S_{d−1} ρ_d^{1/2} e^{ic_d z}[Ξ(z + ib_d) + Ξ(z − ib_d)]`, with `b_d = (d − 2)/4`,
  `= ∫_ℝ K(v)e^{izv}dv`, with `K(v) = 2Σ_d S_{d−1}ρ_d^{1/2}Φ(|v − c_d|)cosh(b_d(v − c_d))`.

`K` is real but not even, so `G_B` is not real on ℝ. Its zeros are symmetric under `z ↦ −z̄`, not under conjugation.

**What any outcome can mean.**
- Rescaling never moves an individual lattice's zeros (`λ^{−2s} ≠ 0`). It breaks each slice's self-duality about its centre line.
- **Bearing on RH: none, whatever the result.**

**Method.**
- `G_B` from `K` on Gauss–Legendre nodes on `[−4, 4]` (800 nodes, 50 digits, `d ≤ 200`), validated against the direct ξ-sum at `z = 3, 17.5 + 2i` to `1e-20`.
- **Total zeros in `|z| < 40`:** argument principle.
- **Location:** local minima of `|G_B|` on a grid over `[−40, 40] × [−12, 12]`, refined by Newton. The count must match the argument-principle total, or the zeros outside the grid are reported as unlocated.

**Predictions.**
- **B1.** No real zeros: every located zero has `|Im z| > 1e-6`.
- **B2.** Zeros come in pairs `z, −z̄`.
- **B3.** The number of zeros in `|z| < 40` is between 10 and 20 (round 171's unscaled sum had 14).
- **B4 (contrast).** The real-rootedness of round 171 is lost. At least half of the located zeros have `|Im z| > 0.1`.

**Verdict rule.**
- Report B1–B4 as found.
- **If B1 fails** (a genuinely real zero): record it as unexpected and check it at higher precision.
