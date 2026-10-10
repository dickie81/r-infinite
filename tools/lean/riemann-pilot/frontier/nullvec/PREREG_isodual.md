# Pre-registration 10: consistent discretisation of the ball's d-dimensional slices, d = 2–8 (round 168)

Committed before any zero of the functions below is computed.

**The owner's intuition.** The arithmetic is the imperfection that appears when the (infinite-dimensional) unit ball is discretised. The test runs on its d-dimensional slices, d = 2, …, 8.

**Operational form (extends round 92).**
- **The slice.** By Poincaré–Borel, the ball's d-dimensional slice is the Gaussian `e^{−π|t|²x}` on ℝ^d. The Gaussian is Fourier self-dual.
- **The admissible discretisations.** A discretisation preserves that self-duality under Poisson summation iff the lattice `L` is **isodual**: `L* = R·L` for a rotation `R`, normalised to covolume 1. Then `θ_L(1/x) = x^{d/2}θ_L(x)`, and the completed Epstein zeta
  `Λ_L(s) = π^{−s}Γ(s)Σ'_{v∈L}|v|^{−2s} = ∫₁^∞(θ_L − 1)(x^s + x^{d/2−s})dx/x − 1/s − 1/(d/2 − s)`
  satisfies `Λ_L(s) = Λ_L(d/2 − s)`, with centre line `Re s = d/4`.
- **Excluded.** Non-isodual lattices (`A₃`, `D₅`, `E₆`, `E₇`) have no self-functional equation, so there is no centre line to test.
- **Consistency test.** As in round 92: every zero of `Ξ_L = s(s − d/2)Λ_L` with `0 < Im s < 40` lies on `Re s = d/4`, i.e. `N_line(40) = N(40)`.

**The fixed list** (building blocks at covolume 1: `ℤ`; `A₂`, norms `(2/√3)(a²+ab+b²)`; `D₄`, norms `|v|²/√2`; `E₈`):

| d | lattices |
|---|---|
| 2 | ℤ², A₂ |
| 3 | ℤ³, ℤ⊕A₂ |
| 4 | ℤ⁴, D₄, A₂² |
| 5 | ℤ⁵, ℤ⊕D₄, ℤ⊕A₂² |
| 6 | ℤ⁶, A₂³, A₂⊕D₄ |
| 7 | ℤ⁷, ℤ⊕A₂³, ℤ⊕A₂⊕D₄ |
| 8 | ℤ⁸, E₈, D₄², A₂⁴ |

`ℤ^d` and `E₈` repeat rounds 92–93 as controls.

**Predictions (from modular forms, stated before computing).**
- **P1.** `A₂` passes. `Λ_{A₂} ∝ ζ(s)L(s, χ₋₃)`, both factors unshifted (weight 1); this assumes GRH up to height 40, known numerically.
- **P2.** Every lattice with `d ≥ 3` fails.
  - `θ_L` is a modular form of weight `k = d/2 ≥ 3/2` with nonzero Eisenstein part.
  - Where it is pure Eisenstein, the zeta is a product of ζ/L factors at `s` and `s − k + 1`, whose zeros sit at `d/4 ± (d − 2)/4`.
  - Otherwise it is a sum without an Euler product, which gives Davenport–Heilbronn-type off-line zeros.
- **P3 (displacement).** For `D₄`, `A₂²` and `E₈` (pure Eisenstein), the off-line zeros lie at `Re s = ½` and `d/2 − ½`, at ordinates of zeros of ζ or `L(χ₋₃)`. The displacement `(d − 2)/4` vanishes only at `d = 2`.

**Verdict rule.**
- **If only d = 2 lattices pass:** among self-dual discretisations, only the 2-dimensional slice (and the 1-dimensional one, round 92) discretises consistently. The obstruction in `d ≥ 3` is the modular weight, which is fixed by the dimension, and not the choice of lattice.
- **If some `d ≥ 3` lattice passes:** it is recorded as a new consistent layer, and P2 is refuted.
- **Validation (must hold, or the run is void):**
  - isoduality `|θ_L(1/x)/(x^{d/2}θ_L(x)) − 1| < 1e-25` at `x = 1.7`;
  - `A₂` and `E₈` match their closed forms to `1e-25`.
