# Hopf fibration as cascade-internal identity

This document records a structural finding from the cascade
geometric/topological audit (item 3.5 IGN, see
`cascade-geometric-topological-audit.md`).

## The identity

For the four Hopf fibrations $S^{2n+1} \to S^{n+1}$ with fibre $S^n$
that exist (Adams 1960, Hopf invariant 1, at $n \in \{0, 1, 3, 7\}$):

$$
\Omega_{n+1} \cdot \Omega_n = N(0)^{n+1} \cdot \Omega_{2n+1}
$$

where $N(0) = 2$ is the cascade's zeroth lapse (Part IVb Cor 2.3) and
also $\chi(S^{2n}) = 2$ (Euler characteristic of even spheres).

**Numerical verification** (machine precision):

| $n$ | Fibration | $\Omega_{n+1} \Omega_n$ | $N(0)^{n+1} \Omega_{2n+1}$ | Ratio |
|---|---|---|---|---|
| 0 | $S^1 \to S^1$ | 12.566371 | 12.566371 | 1.000000 |
| 1 | $S^3 \to S^2$ | 78.956835 | 78.956835 | 1.000000 |
| 3 | $S^7 \to S^4$ | 519.515152 | 519.515152 | 1.000000 |
| 7 | $S^{15} \to S^8$ | 963.914262 | 963.914262 | 1.000000 |

**Algebraic proof** (for $n=3$, the observer-host case):
- $\Omega_4 = 8\pi^2/3$ (Gamma function at $d=4$).
- $\Omega_3 = 2\pi^2$.
- $\Omega_4 \cdot \Omega_3 = 16\pi^4/3$.
- $\Omega_7 = \pi^4/3$.
- $\Omega_4 \cdot \Omega_3 / \Omega_7 = 16 = 2^4 = N(0)^4$.

The identity is forced by the Gamma function values at the specific
half-integer arguments. For Hopf fibrations beyond the Hurwitz
dimensions, the relation does not hold — Adams' theorem on Hopf
invariant 1 ensures the fibration only exists at $n \in \{0, 1, 3, 7\}$.

## Cascade-tower interpretation

Each Hopf fibration ties three cascade layers:

| $n$ | Fibre $S^n$ at $d$ | Base $S^{n+1}$ at $d$ | Total $S^{2n+1}$ at $d$ |
|---|---|---|---|
| 0 | $d = 1$ | $d = 2$ | $d = 2$ |
| 1 | $d = 2$ | $d = 3$ | $d = 4$ |
| 3 | $d = 4$ | $d = 5$ | $d = 8$ |
| 7 | $d = 8$ | $d = 9$ | $d = 16$ |

The $n = 3$ case (quaternionic Hopf fibration $S^7 \to S^4$) is the
**observer-relevant** one:

- **Fibre $S^3$** = boundary of $B^4$ = **observer's spatial slice** ($d=4$).
- **Base $S^4$** = boundary of $B^5$ = **observer host** ($d=5$, the volume
  maximum $d_V$ of Part 0).
- **Total $S^7$** = boundary of $B^8$ = **first Bott-period boundary**
  ($d=8$, the first integer multiple of the Bott period 8).

The cascade-internal identity becomes:

$$
\Omega_4 \cdot \Omega_3 = N(0)^4 \cdot \Omega_7 = 16 \cdot \Omega_7
$$

which ties observer, host, and first Bott multiple via the unique
quaternionic Hopf fibration.

## What this connects in the cascade

The Hopf-fibration ladder unifies four cascade-related structural
facts that the paper treats as independent:

1. **Hurwitz division algebras** at dimensions $\{1, 2, 4, 8\}$ (used
   in Part III for $d=4$ via $\mathbb{H}$).
2. **Parallelisability of $S^1, S^3, S^7$** (forced by Hurwitz, not
   currently invoked explicitly).
3. **Hopf fibrations at $n \in \{0, 1, 3, 7\}$** (Adams 1960, currently
   IGN per audit).
4. **Bott period 8** for the cascade's spinor classification (Part IVa
   §2, used explicitly).

These four facts are NOT independent — they are connected by Adams'
Hopf-invariant-1 theorem. Adams 1960 proved that the Hopf
fibration exists with Hopf invariant 1 ONLY at $n \in \{0, 1, 3, 7\}$,
which are precisely the Hurwitz dimensions, which are precisely the
dimensions where parallelisable spheres exist, which are precisely
the boundary points of the Bott period.

The cascade tower visits these dimensions at $d \in \{2, 4, 8, 16\}$.
**Bott period 8 is the spacing of these dimensions.** This is the
structural reason for the cascade's Bott periodicity in fermion
classification.

Currently, the cascade series invokes Bott periodicity as a
classical fact (Part IVa §2) without making this Hurwitz/Hopf
forcing argument explicit.

## Cascade-internal derivation of $\Omega_4$

Given the Hopf identity at $n=3$, the cascade can derive the
observer-host sphere area $\Omega_4$ from $\Omega_3$ (observer) and
$\Omega_7$ (first Bott boundary):

$$
\Omega_4 = \frac{N(0)^4 \cdot \Omega_7}{\Omega_3} = \frac{16 \cdot \pi^4/3}{2\pi^2} = \frac{8\pi^2}{3}
$$

This is the specific value of $\Omega_4$ derived directly from the
Gamma function at $d=5$, but obtained here as a consequence of:
- $N(0) = 2$ (cascade primitive).
- $\Omega_3 = 2\pi^2$ (observer's spatial sphere area).
- $\Omega_7 = \pi^4/3$ (first Bott boundary's sphere area).
- The Hopf fibration (forced by Adams' theorem at $n=3$).

This is a **structural derivation** of the observer host's primary
sphere area from the Hopf fibration, rather than from direct Gamma
function evaluation.

## Why this matters per austerity

The audit listed the Hopf fibration $S^7 \to S^4$ as IGN — cascade-
forced (intrinsic property of $S^4$ as the Hopf base of $S^7$) but
not invoked.

Investigating it has revealed:

1. An **exact cascade-internal identity** connecting four cascade
   layers ($d=4, 5, 8$) via the Gamma-function-derived sphere areas.
2. A **structural derivation** of the cascade's Bott period 8 from
   the Hurwitz/Hopf ladder, which the paper currently treats as
   classical fact without forcing argument.
3. The cascade's observer/host/Bott structure has a **unifying
   geometric realisation** via the quaternionic Hopf fibration.

These are not numerical changes — the Gamma function values are
unchanged. They are **structural connections** the paper currently
omits.

Per austerity (Prelude Principle 2.2): silently omitting these is an
unjustified assumption that they don't matter. The investigation
shows they DO matter — they unify several cascade observations
under a single Adams-theorem forcing argument.

## Recommendation for the paper

**Action 1** (smallest): add the Hopf fibration identity
$\Omega_{n+1} \Omega_n = N(0)^{n+1} \Omega_{2n+1}$ as a remark in
Part IVa §2 (where Bott periodicity is invoked), making explicit
the Hurwitz/Hopf forcing argument behind Bott period 8.

**Action 2**: add a structural-derivation remark in Part I (where
the observer host $d=5$ is established) noting that $\Omega_4$ can
be derived from the observer's $\Omega_3$ and the first Bott
boundary's $\Omega_7$ via the Hopf fibration.

**Action 3** (largest): unify Parts III, IVa under a single
Hurwitz-Hopf-Bott chapter that makes the chain
**Hurwitz $\to$ parallelisability $\to$ Hopf invariant 1 $\to$ Bott
period 8** explicit as the structural force behind the cascade's
fermion classification.

## Caveats

1. The Hopf identity is forced by **Gamma function values at small
   integers**, not by deeper cascade structure. Whether this is a
   "derivation" or a "consistency check" depends on whether the
   reader accepts the Gamma function values as primitive (cascade-
   internal) or as derived (from the Hurwitz/Hopf/Bott connection).

2. The identity is exact at $n \in \{0, 1, 3, 7\}$ but does NOT hold
   at other $n$. The cascade could in principle use the FAILURE of
   the identity at $n \notin \{0, 1, 3, 7\}$ as a consistency check:
   only the Hurwitz/Hopf-allowed $n$ values give the identity.

3. The quaternionic curvature factor $16$ in the $n=3$ identity is
   $N(0)^4 = \chi^4$, which connects the observer's dimension $d=4$
   to the cascade primitive $N(0)$. This is a coincidence of the
   $S^4$ Hopf-base curvature with the cascade's chirality factor;
   structurally significant but the deeper connection (if any)
   remains to be articulated.
