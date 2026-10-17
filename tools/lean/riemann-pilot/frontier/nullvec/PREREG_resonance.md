# Pre-registration 6: is the 3π line geometric or arithmetic? (round 91)

Committed before the grids below are computed. Only four single-point probes have been computed so far; they are listed in the next section.

**Background, computed before registering.**
- **The prime side cannot be ablated.** At `x = 12` (`kchain_variant.py`), `ln K00 = 122.5` with the full prime side. Scaling every `Λ(n)` by 0.9 gives `ln K00 = 1.9`; scaling by 1.1 makes the form indefinite. Dropping `n ≤ 5` gives `0.09`; dropping `n = 11` alone gives `100.4`. The chain's `e^{4πx}` growth exists only at exact prime weight 1, so prime-side ablations destroy the object instead of dissecting it.
- **The zero side is exact.** By Weil's explicit formula, `Q(g) = Σ_ρ |ĝ(γ)|²` for even `g` if the zeros lie on the line (the sum runs over ±γ). So `K_a(0,0) = sup ĝ(0)²/Σ_γ |ĝ(γ)|²`. `kzeroside.py` computes this in the same cosine basis from the first 6700 zeros (`γ ≤ 6997`). It reproduces the prime-side chain up to a near-constant offset: `ln K00 = 39.561` against `38.894` at `x = 5.003`, and `74.948` against `74.284` at `x = 8.004`. The offsets `0.667` and `0.664` are close to `ln 2` less the truncation.
- **Zero-side ablation is safe.** Any point set gives a positive form, so the zeros can be replaced.

**Route R, the "one remaining route".** The line is a *geometric* resonance: an interference between the window scale `a` and the *mean* zero spacing near the edge, where the local spacing is `2π/ln(γ/2π)`. R predicts that the line survives when the zeros are replaced by their fluctuation-free quantiles `γ̃_k`, defined by `θ(γ̃_k) = (k − 3/2)π` (the smooth Riemann–von Mangoldt count, with the same number of points).

**The alternative, A (arithmetic).** The line is carried by the *fluctuations* of the true zeros about their mean positions, so it disappears for the quantiles.

**Protocol.**
- Grid: `x ∈ [3, 12]`, step `0.02`, 451 points, basis `K = 15x + 40`.
- Two point sets: `true` (Z0) and `smooth` (Z1).
- Residual: least-squares fit in `(e^δ, δ, 1, e^{−δ})`.
- Spectrum and line test: as in rounds 89–90, with flank band `[5, 15]` and resolution `2π/9 = 0.70`.

**Criteria.**
- **(V) Validation.** The Z0 residual correlates with the measured residual (`hamiltonian_grid_to3.jsonl` interpolated to the same `x`, same fit) at `≥ 0.9`. If V fails, the test is void.
- **(R)** Z1's highest peak in `[8, 11]` lies within `±0.70` of Z0's and passes the line test. R passes if this holds, and the route is then open, with Z1 as its explicit model.
- **(A)** Z1 has no line passing the test within `±0.70` of Z0's peak. A holds if this is so, and route R is then closed: the line is arithmetic, carried by the zero fluctuations.

The Z1/Z0 residual rms ratio is also reported.

**Expectation.** Genuinely unknown. Round 88's continuum balayage (no discreteness) gave no wiggles. But Z1 keeps the discreteness and removes only the fluctuations, which is exactly the case round 88 did not test.
