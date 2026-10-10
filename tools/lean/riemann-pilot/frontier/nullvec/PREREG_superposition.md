# Pre-registration 8: the octonion superposition (round 94)

Committed before the superposed zero set is computed.

**The owner's idea.** The on-line arithmetic is a *superposition* of the octonion ball's two displaced copies of Riemann's function (round 93: `E₈` gives `ζ(s)ζ(s−3)`, i.e. ζ's zeros at `2 ∓ 3/2`).

**The superposition, made exact.** In `z` (`s = ½ + iz`), the two copies are `Ξ(z ± 3i/2)`. Their symmetric superposition is

`G(t) = Ξ(t + 3i/2) + Ξ(t − 3i/2) = ξ(−1 + it) + ξ(2 + it) = 2·Re ξ(2 + it)`,

which is real for real `t`.

**Theorem** (de Bruijn 1950, the `cos(bD)` shift). If `F` is real entire of order `< 2` with all zeros in `|Im z| ≤ Δ`, then `F(z+ib) + F(z−ib)` has only real zeros when `b ≥ Δ`. For `Ξ`, unconditionally `Δ ≤ ½`, so with `b = 3/2` **every zero of the octonionic superposition lies on the critical line, with no hypothesis**. Its zeros are the solutions of `arg ξ(2 + it) ≡ π/2 (mod π)`. They are *not* Riemann's zeros. Their fluctuation about the smooth count comes from `arg ζ(2 + it)`, i.e. prime weights `Λ(n)/(n² ln n)` instead of the critical line's `Λ(n)/(√n ln n)`.

**Hypothesis S.** The chain's arithmetic is this superposition. Prediction under S: the window chain built on `G`'s first 6700 zeros (`kzeroside.py`, same grid as round 91: `x ∈ [3, 12]`, step 0.02, `K = 15x + 40`) reproduces the measured wiggles as the true zeros did:
- residual correlation with the measured residual `≥ 0.9`;
- the 9.075 line passes the round-91 line test.

S passes only if both hold.

**Expectation, stated before computing: S fails.** `arg ζ(2+it)` is bounded by about 0.6 and dominated by `n = 2, 3`. So `G`'s zeros should be close to the fluctuation-free quantiles, which gave *no* wiggles in round 91, plus a weak ripple at frequencies `ln n`. Predicted: wiggle rms well below the true zeros' 0.074, and no 9.075 line.

**Also reported:** the zero count of `G` against ζ's (the same smooth law), and the mean |displacement| of `G`'s zeros from ζ's smooth quantiles against that of the true zeros.
