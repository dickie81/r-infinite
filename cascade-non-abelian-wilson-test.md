# Test: is the non-Abelian Wilson lift cascade-forced?

This document tests the second of the two natural extensions identified
at the close of `cascade-wilson-line-derivation2.md`: lifting the
cascade's Abelian Wilson line interpretation to a full non-Abelian
Wilson line on cascade gauge paths, which would close the
non-perturbative gauge dynamics gap.

## Result

**The non-Abelian Wilson lift is NOT cascade-forced. It is not even
cascade-constructible without importing additional structure not
present in the cascade.**

This is a clean negative result. The cascade's structure is genuinely
insufficient to support a full non-Abelian gauge theory, and no
candidate cascade-internal scheme supplies the missing components.

This confirms reading (B) of the trichotomy for non-perturbative
content: the cascade is genuinely partial in this regime.

## What a non-Abelian Wilson line requires

For a connection $A$ valued in a Lie algebra $\mathfrak{g}$ of dimension
$\dim\mathfrak{g} = n$, the Wilson line
$$W_\gamma = \mathcal{P}\exp\left(\int_\gamma A^a T_a\right)$$
requires $n$ independent component functions $A^a(d)$ along the path,
one per Lie algebra generator $T_a$.

For the SM gauge groups:
- $\mathfrak{su}(3)$: $\dim = 8$ (eight Gell-Mann matrices)
- $\mathfrak{su}(2)$: $\dim = 3$ (three Pauli matrices)
- $\mathfrak{u}(1)$: $\dim = 1$

## What the cascade provides

The cascade's available structure at each layer:
- **$J$ (cascade complex structure)**: 1 generator (the $U(1)$ from
  Theorem `complex` of Part II), available at every layer.
- **Adams vector fields at gauge layers**: $\rho(d) - 1$ additional
  generators at $d \in \{12, 13, 14\}$.
- **Cascade slicing potential $p(d)$**: a single scalar function of
  layer index.

## The component-count comparison

| Layer | Group | $\dim\mathfrak{g}$ | Cascade-provided generators | Gap | Sufficient? |
|---|---|---:|---:|---:|---:|
| $d=14$ | $U(1)$ | 1 | 1 ($J$) | 0 | **YES** |
| $d=13$ | $SU(2)$ | 3 | 2 ($J$ + 1 Adams) | 1 | **NO** |
| $d=12$ | $SU(3)$ | 8 | 4 ($J$ + 3 Adams) | 4 | **NO** |

So the cascade can support an Abelian $U(1)$ Wilson line at $d=14$
(giving the hypercharge running) but NOT a true non-Abelian Wilson
line at $d=12$ (SU(3)) or $d=13$ (SU(2)).

## What the cascade is missing

For $SU(2)$ at $d=13$: the cascade has 2 of 3 generators. The third
($\sigma_y$ in Pauli notation) has no cascade-internal source.

For $SU(3)$ at $d=12$: the cascade has 4 of 8 generators (Cartan +
some root vectors). The 4 off-diagonal Gell-Mann matrices
$\lambda_4, \lambda_5, \lambda_6, \lambda_7$ have no cascade-internal
source.

## Candidate cascade-internal schemes (all fail)

I tested five natural cascade-internal proposals to supply the missing
generators:

1. **Replicate $p(d)$ across components**: $A^a(d) = p(d)$ for all $a$.
   Fails — gives 1 scalar replicated $n$ times; Wilson line collapses
   to scalar $\exp(n p(d))$, equivalent to Abelian.

2. **Differentiate $p(d)$**: $A^a(d) = \frac{d^a}{dd^a} p(d)$.
   Fails — higher derivatives of smooth $p(d)$ are linearly dependent;
   doesn't produce $n$ independent components.

3. **Sphere-area ratios**: $A^a(d) = \Omega_{d+a}/\Omega_d$.
   Fails — these are cross-layer ratios mixing scales, not gauge
   directions; they're not Lie-algebra-valued.

4. **Adams + neighbouring-layer perturbations**: extend Adams vector
   fields by perturbing across cascade layers.
   Fails — cascade's slicing recurrence is multiplicative scalar; it
   doesn't carry tangent vector information between layers.

5. **Import from SM gauge fields**: use SM gauge field values directly.
   Fails by construction — would import the answer.

None of the natural cascade-internal schemes produces the missing
Lie-algebra-valued component functions cascade-natively. This is a
clean negative result.

## Why this matters

**Non-perturbative gauge dynamics is genuinely outside cascade scope.**
The phenomena that depend on the full non-Abelian gauge structure are
not derivable cascade-internally as currently formulated:

- Gluon self-coupling (depends on $f^{abc}$ structure constants).
- Asymptotic freedom in its complete RG form (depends on full
  $\beta$-function with non-Abelian contributions).
- Confinement (non-perturbative, depends on full SU(3) dynamics).
- Instantons (require $\pi_3(SU(N))$ structure of the full gauge
  group).
- $\theta$-vacuum (Part IVb's Tier 4b claim that
  $\theta_{\rm QCD} = 0$ from $\pi_3(S^{11}) = \mathbb{Z}_2$ is
  *exactly* the kind of claim that would need the cascade's
  non-Abelian structure to be cascade-internal — and per this test,
  it is not).

The cascade gives:
- Gauge GROUPS via Adams + Hurwitz (forced).
- Gauge running via Abelian Wilson lines (under Reading G; cascade-
  consistent if not strictly forced).
- Matter representations via path tensor product (cascade-forced
  composition rule, with reps imported from SM).

The cascade does NOT give:
- Full non-Abelian gauge field theory.
- Non-perturbative dynamics.

## Three options for the program

Given austerity (Prelude 2.2), there are three honest responses:

**(i)** Identify additional cascade-internal structure that supplies
the missing Lie-algebra components. **No candidate identified.** Five
natural schemes have been tested and all fail.

**(ii)** Import the missing components from outside the cascade.
**Violates austerity** — would be a free input not derivable from the
hypothesis.

**(iii)** Accept that non-perturbative content is outside the
cascade's current scope. **The honest conclusion under austerity.**

The cascade's claims should be qualified to perturbative SM physics,
with non-perturbative content explicitly out of scope. This is
consistent with what the predictions table actually delivers
(running couplings, mass ratios, gauge group, generations,
cosmological parameters) — none of which is non-perturbative.

The Tier 4b $\theta_{\rm QCD} = 0$ claim in Part IVb (which depends on
the cascade's topology being SU(3)-equivalent) should remain at Tier 4b
or be downgraded, since the cascade's structure does not fully realise
SU(3) without external input.

## Implication for the trichotomy

This test cleanly separates the cascade's reading-(A) and reading-(B)
content:

| Content | Cascade-internal? | Reading |
|---|---|---|
| Abelian Wilson lines (running couplings) | YES | (A) |
| Path tensor product (composite matter) | YES | (A) |
| Born rule (dim ≥ 3) under Reading G | YES | (A) |
| Generation structure | YES | (A) |
| Gauge group identification | YES | (A) |
| **Non-Abelian Wilson lines** | **NO** | **(B)** |
| **Non-perturbative gauge dynamics** | **NO** | **(B)** |

The session's accumulated evidence now distinguishes the two readings
with a sharp criterion: anything requiring the full non-Abelian
algebra structure is outside cascade scope.

The framework is **real for perturbative SM physics, partial for
non-perturbative gauge theory**. This is the honest verdict.

## What this means concretely

- The cascade's "indistinguishable from our universe" claim is
  qualified to perturbative observables.
- The seven precision closures via $\alpha(d^*)/\chi^k$ remain Tier 3
  — they're perturbative.
- The running couplings, mass ratios, and gauge-anchored predictions
  remain at their current tiers — also perturbative.
- $\theta_{\rm QCD} = 0$ at Tier 4b in Part IVb should arguably be
  flagged as a *non-perturbative* claim that the cascade's structure
  cannot yet support cascade-internally.
- Confinement, instanton effects, and QCD vacuum structure are
  explicitly outside scope.

This is a meaningful but honest scope statement. The cascade's
*positive* content (perturbative SM physics from one hypothesis) is
substantial. Its *limit* (non-perturbative content not delivered)
is now sharply identified.

## Conclusion

Non-Abelian Wilson lift: **not forced, not constructible cascade-
internally as currently formulated**. The cascade's bare structure
cannot supply the Lie-algebra-valued component functions required
for a true non-Abelian gauge theory.

This is the cleanest negative result the session has produced. It
identifies exactly where the cascade ends and where additional
structure would be needed for a complete derivation of SM physics.
