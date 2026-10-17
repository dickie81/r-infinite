# Pre-registration 9: which primes set the wiggle lines? (round 95)

Committed before any prime-truncated zero set or its chain is computed.

**Construction.** The zero counting function is `N(t) = θ(t)/π + 1 + S(t)`, with `S(t) = (1/π) arg ζ(½ + it)`. Replace `S` by its truncated Euler product,

`S_P(t) = −(1/π) Σ_{p ≤ P} Im log(1 − p^{−½−it})`,

and define the prime-`P` zero set as the solutions of `θ(t)/π + 1 + S_P(t) = k − ½`, taking all crossings. `P = 0` gives round 91's smooth quantiles, which carry no wiggles.

**Faster kernel** (`kzeroside2.py`). Zeros below `H = 1000` enter individually. Above `H`, they enter through the smooth density, with `sin²(ta)` replaced by its mean. Against the round-91 kernel this changes `ln K00` by `0.009` (x = 5) and `0.0004` (x = 12), and runs about 5× faster. The grid is `x ∈ [3, 12]`, step `0.04` (226 windows, Nyquist 78).

**(V) Validation.** `kzeroside2` on the true zeros must reproduce the round-91 true-zero residual at correlation `≥ 0.99` on the common points. If V fails, the test is void.

**Variants.** `P ∈ {2, 3, 5, 7, 13, 31, 101, 1009}`. For each variant, report:
- the correlation of its residual with the true-zero residual;
- the rms ratio;
- the line test (round 91's, flank `[5, 15]`) at the true-zero peak `ω₀` (±res);
- its own dominant line in `[8, 11]`.

**Hypothesis LP.** The line positions are set by the lowest primes. It predicts:
- **(i)** the line test at `ω₀` passes already at `P = 3`, and at every larger `P`;
- **(ii)** the correlation with the true-zero residual at `P = 3` is `≥ 0.5`.

LP passes if both (i) and (ii) hold.

**The alternative, C (collective).** The line needs many primes, i.e. the line test first passes only at `P ≥ 31`, or never.

**Expectation, stated before computing.** Round 94 found that the superposition, whose arithmetic is dominated by `p = 2, 3` with weights `1/n²`, carries a strong line one bin from `ω₀` and correlates at 0.54. On the critical line the weights are `1/√n`, so the low primes are relatively stronger still. I lean towards LP (i) passing. On (ii) I have no strong expectation.
