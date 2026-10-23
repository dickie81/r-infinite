# Pre-registration 11: the spacetime-signature grid ℤ^{3,1} (round 170)

Committed before any count below is computed.

**The owner's idea.** "4D one way": replace the Euclidean 4D grid (round 169: `ζ(s)ζ(s−1)`) by a grid of spacetime signature. The question is whether its imperfection carries a different arithmetic, in particular an unshifted ζ.

**Operational form.**
- **The lattice.** `ℤ^{3,1}` with `Q(x, y, z, t) = x² + y² + z² − t²`. It is odd unimodular and indefinite, so its genus has one class (Eichler).
- **Shells.** Each shell `Q = n` holds infinitely many points. The count is taken in an expanding window:
  `N_n(T) = #{v : Q(v) = n, |t| ≤ T} = Σ_{|t|≤T} r₃(n + t²)`, and for `n < 0` only `t² ≥ |n|` contributes.
- **Density.** Divide by the real volume of the window: `δ(n) = lim_T N_n(T) / (2π Σ_{|t|≤T} √(n + t²))`. This uses `r₃(m) ≈ 2π√m` on average.
- **The Siegel theorem as a check.** For class number one, `δ(n) = Π_p α_p(n)` (Siegel). So `δ` is the lattice's own grid-on-hyperboloid density, measured, not assumed.
- **Numerics.** `T = 1400`, `|n| ≤ 400`, with `r₃` computed exactly to `2·10⁶`.

**Predictions** (local densities of a quaternary form with discriminant `−1`, whose quadratic character is `χ₋₄`):
- **L1 (Euler product).** For odd `m, n` with `gcd(m, n) = 1`, `δ(mn)δ(1) = δ(m)δ(n)` within the numerical error, estimated from the spread between `T = 1000` and `T = 1400`.
- **L2 (closed form).** For odd `n > 0`, `δ(n)/δ(1) = Σ_{d|n} χ₋₄(d)/d`. The same holds for odd `n < 0`, with `δ(−1)` in place of `δ(1)`.
- **L3 (reading).** It follows that `Σ_{n odd} n·δ(n) n^{−s} ∝ ζ(s−1)·L(s, χ₋₄)` restricted to odd `n`. The unshifted factor is `L(χ₋₄)`, not ζ. ζ appears only shifted, at `Re s = 3/2`.
  - Contrast with the Euclidean 4D case, `ζ(s)ζ(s−1)`, where the unshifted factor is ζ itself.
  - The displacement from the centre `Re s = 1` stays `±½`.

**Verdict rule.**
- **If L1 and L2 hold:** the Lorentzian 4D grid's imperfection is `L(χ₋₄)` together with a shifted ζ. The signature change swaps the unshifted ζ for `L(χ₋₄)` and does not remove the ½ displacement.
- **If L2 fails but L1 holds:** record the measured multiplicative function and identify it.
- **If L1 fails:** there is no Euler product, and the Lorentzian grid behaves like the Euclidean 3D one.
