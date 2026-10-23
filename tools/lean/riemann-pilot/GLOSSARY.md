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

## Primes as rotating circles

- **Bohr torus.** Each prime `p` is a circle turning at speed `log p` as the height `t` increases. ζ at height `t` is read off from where all the circles are at once: a point on an infinite-dimensional torus. The speeds share no common rhythm, so the circles never all line up exactly, but they come arbitrarily close to any alignment (Kronecker–Weyl).
- **Why it fails on the critical line.** Each circle wobbles by about `p^{−σ}`. The total `Σ p^{−2σ}` is finite for `σ > ½` but becomes `Σ 1/p`, which diverges, at `σ = ½`. There are slightly too many wobbles, each slightly too big.
- **Selberg's central limit theorem.** On the critical line, `log|ζ|` behaves like a bell curve whose width grows like `√(½ log log t)`.
- **Function-field (meshing) case.** Zeta functions of curves over a finite field `F_q`. Every "prime" turns at a whole-number multiple of `log q`, so the gears mesh, ζ repeats periodically in `t`, and there are finitely many zeros per period. RH is proved there (Weil 1948, Deligne 1974).
- **Almost periodic.** Built from many rotations whose speeds share no common rhythm. It never repeats exactly but comes back arbitrarily close. This is ζ's behaviour along a vertical line (Bohr).
- **Tone law, `ω = 2π(n − 1/n)/q`** (rounds 109–118). The "grinding" wiggles in the pilot's window chain are beat tones, one family per small prime `n`: `3π ≈ 9.42` for 2 and `16π/3` for 3. `q` is 1 for ζ and the conductor for an L-function. The law was derived without fitted constants, passed blind tests on new L-functions, and needs no RH input (round 118). It describes the shape of the wiggles, not where the zeros are.
