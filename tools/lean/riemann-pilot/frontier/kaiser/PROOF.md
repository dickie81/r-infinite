# The 4X upper bound for Weil's ground energy, with an elementary trial function

**Theorem.** There are constants `K, p, a₀` such that for every `a ≥ a₀`

  `λ₁(a) ≤ K · e^{p a} · exp(−4π e^{2a})`.

This is the upper half of Connes' heuristic `λ₁ ≈ 1 − χ₂` ([arXiv:2602.04022], §6.4), whose exponent is
`−4πe^{2a} + 9a`. Round 159's `lam_dexp` proves the exponent `−2πe^{2a} + 16a`, half the rate.

No prolate spheroidal function is used. Connes' trial `E(h_λ)` (prolates `h_{0,λ}, h_{4,λ}`) is replaced by
Connes' map `E` applied to a Kaiser-type function whose Fourier side is elementary. It has the same
concentration exponent `e^{−c}`, `c = 2πλ²`, which is prolate-optimal.

## Notation

- `λ = e^a`, `X = πλ²`, `c = 2πλ² = 2X`.
- `η = 1/λ`, `μ = λ − 4η`, `β = 2πμ`. The total exponential type is `β + 8πη = 2πλ`.
- Fourier transform: `𝓕f(ξ) = ∫ f(x) e^{−2πixξ} dx` (Mathlib's convention). For even `f`, `𝓕⁻¹f = 𝓕f`.
- Connes' map: `E(f)(x) = x^{1/2} Σ_{n≥1} f(nx)` for `x > 0`.
- The pilot's window transform: `ĝ(z) = ∫_{−a}^{a} g(u) e^{izu} du`. Weil's form over the zeros is
  `Q(g) = Σ_ρ ĝ(t_ρ)²` with `t_ρ = (ρ − ½)/i` (`weilExplicit_zeta`, round 156).

## Step 1: the Kaiser kernels

For `j ∈ {0, 1}` put `C_j(β; v) = Σ_{k≥0} (−β²v)^k/(2k+j)!`. These are entire in `v`, as locally
uniform limits of polynomials with majorant `Σ (β²R)^k/(2k)!`.

- For `v ≥ 0`: `C₀ = cos(β√v)` and `C₁ = sin(β√v)/(β√v)`. Both have `|·| ≤ 1`.
- For `v ≤ 0`: `C₀ = cosh(β√(−v))`.
- If `s² = v` then `C₀(β; v) = cos(βs)`, so `|C₀| ≤ e^{β|Im s|}`.
- **Lemma (square-root imaginary part).** If `s² = z² − λ²` and `z = x + iy`, then `(Im s)² ≤ y² + λ²`.
  - Proof. Write `s = p + iq`. Then `pq = xy` and `p² − q² = x² − y² − λ²`.
  - If `q² > y² + λ²`, then `p² > x²`, so `p²q² > x²y² = (pq)²`, a contradiction.
- **Derivative bound.** For `v ≥ 0`, `|∂_v C₀(β; v)| = |β sin(β√v)/(2√v)| ≤ β²/2`.

Define `K(z) = C₀(β; z² − λ²)` and `S(z) = C₁(πη; z²)^8 = (sin(πηz)/(πηz))^8`. Then:

- `|K(x + iy)| ≤ e^{β(|y| + λ)}` everywhere, and `|K(x)| ≤ 1` for real `|x| ≥ λ`.
- For real `|x| < λ`, `K(x) = cosh(β√(λ² − x²)) ∈ [½e^{β√(λ²−x²)}, ½e^{β√(λ²−x²)} + ½]`.
- `|S(x + iy)| ≤ e^{8πη|y|} · min(1, 2/(πη|z|))^8`.
- For real `x`: `0 ≤ S(x) ≤ 1`, `S(x) ≤ (πηx)^{−8}`, and `S(x) ≥ (1 − (πηx)²/6)^8`.

## Step 2: the Fourier-side function `H`

Let `H₀ = K·S` and `m_k = ∫_ℝ ω^k H₀(ω) dω` (`k = 2, 4`). Define

  `α = m₄/m₂`,  `H(z) = z²(z² − α) H₀(z)`.

- **Growth.** `|H(x + iy)| ≤ A(λ) e^{2πλ|y|}/(1 + x²)`, since the total type is `β + 8πη = 2πλ`.
- **Normalisation.** `H(0) = 0` and `∫ H = m₄ − α m₂ = 0`.
- **Real-line bounds for `x ≥ λ`.**
  - `|H(x)| ≤ 2λ⁸π^{−8}/x⁴`.
  - `|H′(x)| ≤ P(λ)/x³`, with `P` polynomial, from `|K′(x)| ≤ β²x` and `|S′| ≤ 16πη(πηx)^{−8}`.

**Lemma (moment ratio).** For `λ ≥ λ₀`, `m₂ > 0` and `α ≤ 4/5`.
- **Setup.** Put `σ² = λ/β`. On `|ω| ≤ λ`, `√(λ² − ω²) ≤ λ − ω²/(2λ)`. On `|ω| ≤ 1`, `√(λ² − ω²) ≥ λ − ω²/(2λ) − ω⁴/(2λ³)`.
- **Upper bound.** `m₄ ≤ ½e^{βλ}·3σ⁴√(2π)σ + R(λ)`.
- **Lower bound.** `m₂ ≥ ½e^{βλ}e^{−β/(2λ³)}(1 − π²η²/6)^8 ∫_{|ω|≤1} ω² e^{−ω²/(2σ²)} − R(λ)`.
- Here `R(λ)` collects the `|ω| ≥ λ` parts and the `+½` of `cosh`, and is polynomial in `λ`.
- **Conclusion.** `σ² → 1/(2π)`, and the truncated Gaussian moment is `≥ 0.9·σ³√(2π)`. So `α ≤ 3σ²/0.9·(1 + o(1)) ≈ 0.53`.

## Step 3: Paley–Wiener by contour shift

Let `h = 𝓕⁻¹H`, i.e. `h(ξ) = ∫ H(ω) e^{2πiξω} dω`, which is continuous and even.

**Claim.** `h(ξ) = 0` for `|ξ| ≥ λ`.
- Take `ξ > λ`. `strip_shift` (round 156) moves the line to `Im ω = T`. The integrand is
  `≤ A e^{2πλT}e^{−2πξT}/(1 + r²)`.
- So `|h(ξ)| ≤ A′ e^{−2π(ξ−λ)T} → 0` as `T → ∞`.
- For `ξ = λ`, use continuity. Negative `ξ` follow by evenness.

Since `h` has compact support, is continuous and integrable, and `H` is continuous and integrable,
Fourier inversion gives `𝓕h = H`.

## Step 4: Poisson summation and the even trial `G`

**Poisson.** Apply `Real.tsum_eq_tsum_fourier_of_rpow_decay` to `y ↦ h(xy)`, which has decay exponent `b = 4`:
- `Σ_{n∈ℤ} h(nx) = x^{−1} Σ_{k∈ℤ} H(k/x)`;
- with `h(0) = ∫H = 0` and `H(0) = 0`, this gives `E(h)(x) = E(H)(1/x)`.

Put `f = h + H` and `G(u) = E(f)(e^u)`. Then

  `G(u) = E(H)(e^u) + E(H)(e^{−u})`,

which is even in `u`.
- For `u > a` every argument satisfies `ne^u > λ`. So `h` drops out, and `G(u) = e^{u/2} Σ_n H(n e^u)`.
- Hence `|G(u)| ≤ 4λ⁸ e^{−7u/2}` and `|G′(u)| ≤ P′(λ) e^{−3u/2}` for `u ≥ a`.

## Step 5: the full transform of `G` vanishes at every zero

Put `F = E(f)`. Then `F(x) = O(x^{−3/2})` as `x → ∞`, and `F(x) = F(1/x) = O(x^{3/2})` as `x → 0`.

- **Analyticity of the left side.** By `mellin_differentiableAt_of_isBigO_rpow`, `𝓜F(s)` is analytic on
  `|Re s| < 3/2`, and `∫_ℝ G(u) e^{itu} du = 𝓜F(it)`.
- **The interchange.** For `1 < Re w < 3/2`, Fubini gives `𝓜F(w − ½) = ζ(w)·𝓜f(w)`, where `f = O(1)` at 0 and
  `O(x^{−2})` at ∞, so `𝓜f` is analytic on `0 < Re w < 2`.
- **Identity theorem.** Both sides are analytic on the connected open set `{0 < Re w < 3/2} ∖ {1}`, so they agree there.
- **At a nontrivial zero `ρ`.** `𝓜F(ρ − ½) = ζ(ρ)𝓜f(ρ) = 0`, and `ρ − ½ = i t_ρ`.

So `∫_ℝ G(u) e^{i t_ρ u} du = 0` for every nontrivial zero.

## Step 6: the zero side

Let `g = G·1_{[−a,a]}`.
- **It is a probe.** It is even, bounded and supported in `[−a, a]`.
- **`ĝ²` is a strip test.** `G` is `C¹` on `[−a, a]`, so one integration by parts gives `|ĝ(z)| ≤ B/|z|` on `|Im z| ≤ 1`.
- **The explicit formula** (`weilExplicit_zeta`) gives `Q(g) = Σ_ρ ĝ(t_ρ)²`.
- **The tail.** `ĝ(t_ρ) = −∫_{|u|>a} G e^{it_ρu} = −2∫_a^∞ G(u) cos(t_ρ u) du`.
  - Integrating by parts once, with `|Im t_ρ| < ½`:
    `|ĝ(t_ρ)| ≤ 2 min(1, 1/|t_ρ|)(|G(a)|e^{a/2} + ∫_a^∞ (|G| + |G′|)e^{u/2}) ≤ P″(λ) min(1, 1/|t_ρ|)`.
  - So `|ĝ(t_ρ)|² ≤ 5P″(λ)²/|t_ρ² + 4|`.
- **Summing.** With `Σ_ρ 1/|t_ρ² + 4| < ∞` (round 157), `Q(g) ≤ K₁ P″(λ)²`.

## Step 7: the bulk

Take `|u| ≤ δ = 1/10`.
- **Nonnegative terms.** Every argument `y = n e^{±u}` with `y ≤ λ` has `y² ≥ e^{−1/5} > 4/5 ≥ α`. So `H(y) ≥ 0` there,
  because `K = cosh > 0` and `S = sinc^8 ≥ 0`.
- **Arguments above `λ`.** They contribute at most a polynomial `P‴(λ)` in absolute value.
- **The main term** (`n = 1`), using `√(λ² − y²) ≥ λ − y²/λ` and `β/λ ≤ 2π`:
  `e^{u/2}H(e^u) ≥ e^{−δ/2}e^{−2δ}(e^{−2δ} − 4/5)·½ e^{βλ − 2π e^{2δ}}·½ ≥ c₂ e^{βλ}`.
- **Conclusion.** For large `λ`, `G(u) ≥ (c₂/2)e^{βλ}` on `|u| ≤ δ`, so `‖g‖² ≥ 2δ(c₂/2)² e^{2βλ}`.

Here `βλ = 2π(λ − 4/λ)λ = c − 8π`.

## Step 8: assembly

Take `g/‖g‖` as the trial in `lam_le`:

  `λ₁(a) ≤ Q(g)/‖g‖² ≤ K₁P″(λ)² / (2δ(c₂/2)²e^{2c−16π}) = K e^{pa} e^{−2c}`,

with `2c = 4πe^{2a}`. ∎

## Numerics (`kaiser2.py`, zeros on the line, 300 zeros)

| a | α | −ln(Q/‖g‖²) | 4X | 4X − (−ln RQ) | `lam_dexp`: 2X − 16a | Connes/jets: −ln λ₁ |
|---|---|---|---|---|---|---|
| 0.8 | 0.417 | 19.5 | 62.2 | 42.7 | 18.3 | 38.5 |
| 1.1 | 0.445 | 66.4 | 113.4 | 47.0 | 39.1 | 86.6 |
| 1.5 | 0.463 | 201.8 | 252.4 | 50.6 | 102.2 | 223.3 |

- The loss `4X − (−ln RQ) ≈ 16π + O(a)` is the `e^{−16π}` of Step 7 plus the polynomial `P″`.
- The rate is `4X`.
