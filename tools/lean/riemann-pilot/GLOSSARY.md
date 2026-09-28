# Plain-language glossary for the Riemann pilot

One short entry per symbol or idea, in the order they tend to come up. "Picture" gives the
geometric intuition; "precisely" gives what the notation actually says.

## The main objects

- **ζ(s), the zeta function.** Adds up `1/n^s` over all whole numbers `n`.
  - Picture: a single function that encodes every prime at once.
  - Precisely: `ζ(s) = 1 + 2^{−s} + 3^{−s} + …`, extended to the whole complex plane.
- **s = σ + it.** The input to ζ is a point in a 2D plane. `σ` is the real part (left–right) and `t` the imaginary part (height).
- **Zeros, ρ.** The points where ζ equals 0. The interesting ones lie in the strip `0 < σ < 1`.
- **Critical line, `σ = ½`.** The vertical line down the middle of that strip.
- **RH (Riemann Hypothesis).** Every interesting zero sits exactly on the critical line.
- **Euler product.** ζ is also a product over primes, `Π_p 1/(1 − p^{−s})`. This is the "multiplicative" half: where the primes live.
- **Functional equation.** A mirror symmetry, `ξ(s) = ξ(1 − s)`. Picture: reflecting the plane across the critical line maps the zeros to each other. It forces zeros to come in mirror pairs; it does not force them onto the line.
- **ξ, Ξ (xi).** ζ with its "Gamma factor" attached, which makes the mirror symmetry exact. `Ξ(t)` is `ξ` read along the critical line, so RH says: every zero of `Ξ` is a real number.
- **Γ factor / archimedean factor, `π^{−s/2}Γ(s/2)`.** The geometric half of ξ.
  - Picture: a Gaussian averaged over all scales.
  - Equivalently: 2 divided by the sphere area, continued to dimension `s` (round 142).
- **Φ (Riemann's kernel).** The function whose Fourier transform is `Ξ`. It is built from theta functions.

## Grids, balls, and the symmetry

- **θ (theta function).** A Gaussian summed over a grid, e.g. `Σ e^{−πn²x}`.
- **Poisson summation.** Summing a function over a grid equals summing its Fourier transform over the dual grid.
  - Picture: the fine↔coarse exchange (denser grid with lighter points = sparser grid with heavier points).
  - This is where the functional equation comes from.
- **Mellin transform.** Averaging over all scales with a weight `x^s`. It turns a grid sum into a zeta function.
- **Lattice / grid, `ℤ^d`.** The points with whole-number coordinates in `d` dimensions.
- **Isodual lattice.** A grid that looks the same after the fine↔coarse exchange (its own dual, up to rotation).
- **`r_d(n)`.** The number of grid points on the sphere of radius `√n` in `d` dimensions. For example `r₄(n) = 8 × (divisors of n not divisible by 4)` (Jacobi).
- **Epstein zeta.** The zeta function of a general grid: add `1/|v|^{2s}` over its points. For `ℤ⁴` it is ζ(s)·ζ(s−1), i.e. ζ and its mirror.
- **Mirror gap, `(d − 2)/4`.** In a d-dimensional ball, ζ's zeros appear as mirror pairs this far either side of the centre line. The gap is exactly this size only if RH holds (rounds 168–170 correction).
- **Modular weight, `d/2`.** The "dimension tag" of a grid's theta function. It fixes the mirror gap.
- **Hurwitz dimensions, 1, 2, 4, 8.** The only dimensions where sums of squares multiply (reals, complex numbers, quaternions, octonions). They are why those grids have Euler products.
- **Sphere area, `S_{d−1} = 2π^{d/2}/Γ(d/2)`.** The surface area of the unit ball's boundary in `d` dimensions. It peaks near `d ≈ 7.26`.

## The pilot's machinery

- **Weil's form, Q.** A way of scoring a test function `g` living on a window `[−a, a]`: archimedean part minus prime part, plus a pole term. RH ⟺ `Q(g) ≥ 0` for every window and every `g`.
- **Window `a`, support `δ = 2a`.** How wide a patch of the log-scale line the test function may use. A wider window sees higher zeros (the horizon is about `2πe·e^{2a}`).
- **λ₁, λ₂.** The lowest and second-lowest scores of Weil's form on a given window (eigenvalues).
  - `λ₁ ≥ 0` for every window ⟺ RH.
  - `λ₂ > λ₁` is "simplicity", Connes–Consani–Moscovici's open step.
- **Explicit formula.** The exact identity linking the prime side of Weil's form to a sum over the zeros.
- **Prolate functions (Slepian).** The functions that live as fully as possible inside both a position window and a frequency window. The pilot's lowest Weil states track them (round 162).
- **Adèles / Tate's thesis.** Treat the real numbers and every prime ("p-adic unit ball `ℤ_p`") together. ζ's symmetry is the product of the local symmetries at every place.

## Guardrails that keep coming up

- **Davenport–Heilbronn.** A function with ζ's mirror symmetry but no Euler product. It has zeros off the line, so the symmetry alone is not enough.
- **Beurling systems.** Fake prime systems with an Euler product but the wrong symmetry. They can have zeros off the line, so the Euler product alone is not enough.
- **de Bruijn's theorem.** Averaging a function with its copy shifted by at least its zero-strip width makes all zeros real. That is why the 4D and higher mirror averages are automatically clean.
- **Conditional vs unconditional.** "Unconditional" means proved without assuming RH. The owner rejects RH-conditional results.
