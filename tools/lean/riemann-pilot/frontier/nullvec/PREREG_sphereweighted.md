# Pre-registration 12: all ball dimensions, weighted by sphere area (round 171)

Committed before any value of G below is computed.

**The object (the owner's choice: "B with sphere areas").**
  `G(z) = Σ_{d≥1} S_{d−1}[Ξ(z + ib_d) + Ξ(z − ib_d)]`
with `b_d = (d − 2)/4` (the mirror gap of the d-ball, rounds 168–169) and `S_{d−1} = 2π^{d/2}/Γ(d/2)`.

**Equivalent form (derived before computing):**
  `G(z) = 2∫_ℝ Φ(u)W(u)e^{izu}du`, with
  `W(u) = Σ_d S_{d−1}cosh(b_d u) = e^{−u/2}f(√π e^{u/4}) + e^{u/2}f(√π e^{−u/4})` and
  `f(x) = Σ_{d≥1} x^d/Γ(d/2) = x/√π + x²e^{x²}(1 + erf x)`.
Here `Φ` is Riemann's kernel, so `Ξ(z) = ∫Φ(u)e^{izu}du`.

**What any outcome can and cannot mean.**
- **RH does not imply G real-rooted, and G real-rooted does not imply RH.** A positive sum of real-rooted functions need not be real-rooted. The `d ≥ 4` terms are individually real-rooted unconditionally (de Bruijn); the `d = 2` term is `2S₁Ξ`; the `d = 1, 3` terms have gap ¼.
- `W` has infinite order, so the Pólya–de Bruijn multiplier theorems do not apply.
- **Bearing on RH is none, whatever the result.** The test characterises the object the owner proposed.

**Method.**
- **Real zeros:** sign changes of `G` on `[0, R]`, with `R = 40`, grid `0.01` plus refinement.
- **All zeros in `|z| < R`:** argument principle on the circle `|z| = R`, with `G` evaluated from the integral form at 50 digits.
- `G` is even and real on ℝ, so real-rootedness in the disc means `N_disc = 2·N_real(0, R)`, counting a zero at 0 if present.
- **Validation:**
  - `W` from the closed form matches `Σ_{d≤200}` to `1e-30` at `u = 0, 0.5, 1, 2`;
  - `G(t)` from the integral matches the direct `Σ_{d≤200}` form (ξ at shifted points) at `t = 3, 17.5`, to `1e-20`.

**Predictions.**
- **Q1.** `G` is real-rooted in `|z| < 40`. Expectation: yes, because the heavy large-`d` terms (each unconditionally real-rooted) dominate.
- **Q2.** `G`'s real zeros are not ζ's zeros: none within 0.05 of `γ₁…γ₆`, beyond coincidence.
- **Q3.** Zero density: `N_real(0, R)` differs from ζ's `N(R) = 6` at `R = 40`.

**Verdict rule.** Report Q1–Q3 as found.
- **If Q1 fails:** the sphere-weighted superposition loses real-rootedness. Record the non-real zeros.
- **If Q1 holds:** record that the weighting keeps it real-rooted in the tested disc. No RH consequence (see above).
