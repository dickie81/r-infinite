# Pre-registration 7: does discretising the ball force a consistent arithmetic? (round 92)

Committed before any zero of the functions below is computed.

**The claim under test** (the owner's): *the arithmetic is forced by discretising the (infinite) unit ball.*

**Operational form.** Take the Gaussian `e^{−π|t|²x}`. Its integral over ℝ^d is the continuum, which gives the ball volumes `π^{d/2}/Γ(d/2+1)` and Γ. Its sum over the integer lattice ℤ^d gives `θ(x)^d`, with `θ(x) = Σ_{n∈ℤ} e^{−πn²x}`. The Mellin transform is the completed Epstein zeta of the discretised d-ball:

`Λ_d(s) = π^{−s}Γ(s) Σ'_{m∈ℤ^d} |m|^{−2s} = ∫₁^∞ (θ^d − 1)(x^s + x^{d/2−s}) dx/x − 1/s − 1/(d/2 − s)`.

It satisfies `Λ_d(s) = Λ_d(d/2 − s)`. For `d = 1` this is Riemann's own formula, `Λ_1(s) = π^{−s}Γ(s)ζ(2s)`, whose trend-minus-lattice split is exactly the round-91 split.

**The window chain of the discretised d-ball exists only if every nontrivial zero of `Ξ_d(s) = s(s − d/2)Λ_d(s)` lies on `Re s = d/4`.** The reason: the zero-side form `Σ_ρ |ĝ(γ_ρ)|²` of round 91 is positive for all probes if and only if every `γ_ρ` is real.

**Hypothesis H.** Discretising the d-ball by ℤ^d yields a consistent arithmetic, i.e. a chain, at every layer `d`.

**Prediction under H.** `N_line(T) = N(T)` for `d = 1, …, 8`, where:
- `N_line` counts the sign changes of the real function `Ξ_d(d/4 + it)` on `0 < t ≤ T`;
- `N` is the total number of zeros with `0 < Im s < T`, from the argument principle on the half contour `σ₁ → σ₁ + iT → d/4 + iT`, with `σ₁ = d/2 + 2`. Real zeros are handled separately (reported with the counts).

The height is `T = 40`, and a dimension passes if the two counts agree.

**Already known, stated before computing.** `Λ_4 ∝ (1 − 4^{1−s})ζ(s)ζ(s−1)` and `Λ_8 ∝ (1 − 2^{1−s} + 2^{4−2s})ζ(s)ζ(s−3)` (Jacobi). Their ζ-zeros lie at `Re s = ½, 3/2` (d = 4) and `½, 7/2` (d = 8), away from the centres 1 and 2. So H is **already false at d = 4 and d = 8 by theorem**. The computation must reproduce this, which serves as the method's validation, together with agreement against the closed forms at sample points.

**Genuinely open here** (to me): `d = 3, 5, 6, 7`. `Λ_6` is a *sum* of two products (`16ζ(s−2)L(s,χ₋₄) − 4ζ(s)L(s−2,χ₋₄)`). The odd dimensions have no Euler product. Expectation: they fail (Davenport–Heilbronn-type off-line zeros for Epstein zetas without an Euler product). `d = 1` and `d = 2` should pass (`ζ(2s)` and `ζ(s)L(s,χ₋₄)`), up to `T` and assuming GRH.

**Verdict rule.**
- If only `d ∈ {1, 2}` pass: H fails. The literal ℤ^d discretisation of the ball gives a consistent arithmetic only in the lowest dimensions. The chain's arithmetic is then the 1-D lattice's, which *is* forced among 1-D lattices through the origin, because `λℤ` gives `λ^{−2s}Λ_1`, with the same zeros.
- If some `d ≥ 3` other than 4 and 8 also passes: that `d` is recorded as a new consistent layer.
