# Pre-registration 22: the chirped heterodyne (round 108)

Committed before any chirped model is fitted.

**Model M3.** The kernel's oscillation beyond the edge is modelled as one *chirped* wave: `E(r)·cos(Ψ(γ))`, with `Ψ(γ) = φ₀ + ∫^γ κ(γ′)dγ′` and a local wavenumber `κ(γ) = ln x + c₀ + c₁(r − 1.4) + c₂(r − 1.4)²`, where `r = γ/4πx`.
- Per window, `(c₀, c₁, c₂, φ₀)` and an overall amplitude are fitted to the kernel's oscillatory part `w − S(w)` on `r ∈ [r_e, 2.2]`, by nonlinear least squares started on the `ln x` branch (`c₀ = 0.33`, `c₁ = c₂ = 0`).
- `E(r)` is round 107's smoothed envelope.
- `M3 = S(w)` + that wave.
- Five shape numbers per window, none from the primes.

**Hypothesis CHIRP.** With M3, the first-order per-prime responses give strongest tones within `±0.3` of 9.47 (`p = 2`) **and** 16.75 (`p = 3`).

**Also reported:**
- the fitted `κ(r)` profile averaged over windows (the chirp law to derive);
- the oscillatory variance captured;
- whether the `p = 3` line is still missing, which would locate the defect outside the single-wave picture.

**Guard against overfitting.** The quadratic chirp has 3 wavenumber parameters over a band of about 20–60 nodes per window. It cannot reproduce the node-by-node sign pattern except through the physics of a smooth chirp. As a control, M3 is also applied with its fitted parameters shuffled across windows. If the shuffled model gives the same tones, the fits carry no window-specific information.
