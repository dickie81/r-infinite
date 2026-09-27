# What would "in practice" take? (round 166, literature survey)

Question: round 165 found the mixed (two-sided) shift terms are where the kernel equation lives,
and that they bear on RH "in principle yes, in practice no". What does the literature say it
would take to control them, or to get around them?

Quotes marked **[verified]** were read from the paper's text (arXiv source or PDF, extracted to
the session scratchpad). Items marked **[agent]** come from a literature survey and were not
re-read here. Items marked **[unverified]** are my reading of the state of the art, and I have
not found a source that states them.

## 1. Controlling the mixed terms directly: closed by the literature

The mixed terms `A A*` are shifts by `log(m/n)`. Their size is controlled by prime-pair
correlations `Σ Λ(n)Λ(n+h)`.

- **Every asymptotic for these correlations assumes RH.** This covers Montgomery's pair
  correlation, Goldston–Montgomery (pair correlation ⟺ variance of primes in short intervals)
  and Goldston–Gonek–Montgomery. **[agent]**
- **Unconditional results are much weaker.**
  - Sieve upper bounds, `≤ (2 + o(1))𝔖(h)X` for the correlation at a fixed shift. **[agent]**
  - Matomäki–Radziwiłł–Tao (arXiv:1707.01315) get Hardy–Littlewood for `Σ Λ(n)Λ(n+h)` on
    average over `h ≤ H`, with log-power savings, for `H ≥ X^{8/33+ε}`. **[agent]**
  - No single-`h` asymptotic is known.
- **The conjectured error is too large by itself.** Even the conjectured error is
  `X^{1/2+o(1)}`, a power saving. Round 165 needs relative precision `e^{−4πe^{2a}}`
  (10²⁹–10¹¹⁵ at the supports tested).

**Conclusion.** No conjecture, let alone theorem, about prime correlations reaches this
precision. A route that bounds the mixed terms by estimating prime correlations cannot close,
even if all the standard conjectures are assumed.

## 2. Guardrails: what a proof must use

Both one-sided inputs are known to be insufficient.

- **An Euler product with regular integers is not enough.**
  - Diamond–Montgomery–Vorhauer (2006) built Beurling systems with `N(x) = Ax + O(x^θ)` whose
    zeta has zeros near `σ = 1`. **[agent]**
  - Broucke (arXiv:2409.10051), Theorem 6.3, pushes this to `θ = 1/2`. **[verified]**
    > "Let θ ∈ [1/2, 1). Then there exists a Beurling number system (P, N) for which
    > N_P(x) = Ax + O(x^θ(1 + I_{θ=1/2} log x)) … N(ζ_P; (1+θ)/2, T) ∼ ((1−θ)T/2π) log((1−θ)T/2π)."

    So an Euler product plus integers regular to `√x·log x` still allows a positive
    proportion of zeros off the line. Whether regularity `θ < 1/2` forces RH for Beurling
    systems appears to be open. **[unverified]**
- **A functional equation without an Euler product is not enough.**
  - Davenport–Heilbronn is the classical example.
  - Bucur et al. (2016) exhibit negative Li-type coefficients for it. **[agent]**
  - Round 165 certified the first Weil-form failure: `λ₁^{DH}(1.725) < 0`, ball arithmetic.

A proof has to use how the archimedean/functional-equation term and the Euler (prime) term
interact. The Weil form `Q = arch + pole − primes` is exactly that interaction, and round 165's
Selberg test shows the one-sided algebra of the prime term adds nothing on the window.

## 3. The live programme: Connes–Consani–Moscovici

CCM restate the obstacle as a problem in operator theory rather than prime counting.

- **The missing steps.** Zeta Spectral Triples, arXiv:2511.22755, §8, "The missing steps".
  **[verified]**
  > (i) prove that the smallest eigenvalue of `QW_λ` is simple with an even eigenvector
  > `ξ_λ`; (ii) show that `k_λ = E(h_λ)` (the prolate `h₀`/`h₄` combination) approximates
  > `ξ_λ` sufficiently well.

  In §7 they write: "Justifying rigorously this step is the main remaining obstacle to our
  approach to RH." They list "three indications supporting the feasibility". One of them is
  that simple-and-even holds for every `λ` for the prolate operator.
- **Connes, arXiv:2602.04022.** **[verified]**
  - The approach "may encounter serious obstacles".
  - Yoshida's positivity gives no reason for positivity "when primes are involved".
  - It restates the simple-even requirement.
- **Connes–van Suijlekom, arXiv:2511.23257.** If the lowest eigenvalue is simple and isolated
  with an even eigenfunction `ξ`, then `ξ̂` has only real zeros. **[agent, abstract]**
- **Proven ranges.**
  - Positivity: Yoshida (1992) and Connes–Consani (2021), only for the prime-free window
    `[2^{−1/2}, 2^{1/2}]`.
  - Continuity: Suzuki (arXiv:2606.09096) proves `λ_a` continuous, and simple, even and
    positive for small `a`. **[agent]**
  - Certified finite range: Zhu (arXiv:2608.24827, unrefereed; compared in round 38).
  - Bombieri (2000): with finitely many off-line zeros, the number of negative eigenvalues is
    half their count. **[agent]**

### The pilot has already formalised the same reduction (Check 4: acknowledged, internal)

| Pilot theorem | Statement |
|---|---|
| `rh_of_eventually_simple` (`SwapRealize.lean:412`) | ground states eventually simple + `HypConv` ⟹ RH |
| `rh_of_dim_le_two` (`ZeroCount.lean:306`) | ground-state space eventually of dimension ≤ 2 + `HypConv` ⟹ RH |
| `rh_of_parity_gap` (`ParityGap.lean`) | eventual parity gap + `HypConv` ⟹ RH, no simplicity needed |
| `rh_of_no_crossing` (`ParityCont.lean`) | no parity crossing past `a = 1/4` + `HypConv` ⟹ RH |

These match CCM's step (i) (simple-even) and Connes–van Suijlekom (simple ⟹ real zeros). The
pilot's `HypConv` plays the part of CCM's step (ii): the normalised ground-state transforms
converge to `Ξ`.

Certified coverage in the pilot:
- `groundState_unique_036`: `δ = 2a ≤ 0.72`, Lean-checked.
- `Round47Certs`: `δ ≤ 2.07`, not checked by Lean.

## 4. The precision barrier: why "in practice" means a structural argument

- **Step (i) is a spectral-gap statement.**
  - The gap `μ₂ − μ₁` equals `|μ₁|` to 88 digits at `δ = 3` (README, the `μ₂(Q₀)` gap-bound section).
  - `λ₂` falls doubly exponentially: `e^{−203}` at `a = 1.5`.
  - Certified numerics therefore extend it one finite cell at a time, at rapidly rising cost,
    and never to all `a`.
- **Step (ii) needs a gap lower bound too.** By Davis–Kahan, an eigenvector approximation
  bound needs `‖(Q − λ₁)k‖ ≪ λ₂ − λ₁`.
  - The pilot's Kaiser trial has Rayleigh residual `≈ e^{−201.7}` at `a = 1.5`, which is
    *above* `λ₂ ≈ e^{−203}`.
  - So the best explicit trial vector in hand is useless for (ii), and the doubly
    exponential size of `λ₂` means any explicit trial must be exponentially sharper.
- **Both steps therefore need a lower bound on `λ₂` for all large `a`.** This is a positivity
  statement of the same strength as the original problem, restricted to the complement of one
  vector.
  - The literature has no such bound.
  - CCM's evidence for it is the prolate analogy, where the operator commutes with a
    differential operator. In round 158 the pilot found an obstruction to an approximate
    commuting operator for Weil's form.

## Summary answer

"In practice" would require one of the following.

- **(A) Prime-pair correlations to precision `e^{−4πe^{2a}}`.** This is excluded: even the
  conjectured error is `X^{1/2}`, and everything better than log-power savings is conditional
  on RH.
- **(B) A structural lower bound on the second eigenvalue `λ₂(a)` of the Weil form, for all
  large `a`.** This is CCM's open step (i) with its companion (ii), and the pilot's
  `rh_of_eventually_simple` / `rh_of_parity_gap` hypothesis.
  - No method in the literature gives it.
  - Numerics can only certify finite ranges.
  - It must use how the functional-equation and prime terms interact, since each alone is
    provably insufficient (Broucke Thm 6.3; Davenport–Heilbronn, round 165).

**Check 4.**
- **Acknowledged.** Every literature item above; the pilot's reductions (README module table; rounds
  146–151); the gap-precision barrier (the README section ending
  "No lower bound on `μ₂(Q₀)` at the needed scale exists").
- **New here.**
  - The explicit comparison of the Kaiser residual with `λ₂`, showing the trial is useless for
    Davis–Kahan.
  - The observation that round 165's DH certificate and Broucke Thm 6.3 together bracket the
    one-sided inputs.

**Bearing on RH:** none new. The survey locates the obstacle and shows the prime-correlation
route is closed. The remaining route, (B), is an open problem that the literature and the
pilot both reduce RH to, and nothing here makes progress on it.
