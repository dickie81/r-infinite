# Investigation: Bott-shift transport for missing non-Abelian generators

This document tests the Bott-shift transport mechanism flagged at the
close of `cascade-non-abelian-wilson-test.md` as the most concrete
candidate for supplying the cascade's missing Lie-algebra components
at gauge layers.

**Specific test**: does quaternionic structure at $d=4$ (Hurwitz) get
transported via Bott shift to give the missing third generator of
$SU(2)$ at $d=13$?

## Result

**Negative — and the investigation reveals a stronger negative result:
the cascade's existing gauge group identifications themselves
overclaim relative to what the cascade strictly forces.**

Three layers of negative finding:

### Layer 1: Bott arithmetic doesn't cleanly map

Hurwitz dimensions: $\{1, 2, 4, 8\}$. Bott period: 8. Bott images of
$d=4$ (quaternion layer): $d \in \{4, 12, 20, 28, \ldots\}$.

Cascade gauge layer assignments:
- $d=12$: cascade claims $SU(3)$ — coincides with Bott image of $d=4$,
  but $SU(3)$ is related to *octonions*, not *quaternions*.
- $d=13$: cascade claims $SU(2)$ — **NOT a Bott image of any Hurwitz
  dimension**.
- $d=14$: cascade claims $U(1)$ — also not a Bott image.

If Bott-shift transported Hurwitz structure cleanly:
- $d=12$ would carry quaternionic structure → $SU(2)$ ($Sp(1)$, dim 3).
- $d=13$ would have no inherited Hurwitz structure.

But cascade puts $SU(3)$ (dim 8) at $d=12$. Mismatch in both group
identity (quaternionic vs octonionic) and dimension (3 vs 8).

The arithmetic doesn't work for the proposed transport mechanism.

### Layer 2: Bott periodicity is K-theoretic, not Lie-algebra-supplying

Bott periodicity statement: $KO^{n+8}(X) \simeq KO^n(X)$. This is
cohomological — it says K-theory groups repeat every 8 dimensions.
It predicts $\rho(d)$ values via Adams' analysis.

It does **not** predict:
- Lie-algebra-valued connection components $A^a(d)$.
- Additional generators beyond $\rho(d) - 1$.
- Non-Abelian structure constants.

So even if (1) worked arithmetically, the mechanism is structurally
wrong. Bott periodicity supplies the *count* of vector fields (already
used by Adams), not additional Lie-algebra components.

### Layer 3: cascade's gauge identifications overclaim

A more careful generator count at gauge layers reveals:

**At $d=13$ (SU(2) layer):**
- $J$ (cascade complex structure): 1 generator.
- 1 Adams vector field on $S^{12}$: 1 generator.
- **Total: at most 2 generators**, and their Lie-bracket structure is
  cascade-undetermined.
- $SU(2)$ requires 3 generators with specific Pauli structure constants.
- Missing: 1 generator + the Lie-bracket specification.

**At $d=12$ (SU(3) layer):**
- $J$: 1 generator.
- 3 Adams vector fields on $S^{11}$: 3 generators.
- **Total: at most 4 generators.**
- If the 3 Adams vector fields form $\mathfrak{su}(2)$ (e.g., from
  quaternionic structure on $\mathbb{H}^3$), then with $J$ the cascade
  algebra at $d=12$ is $\mathfrak{u}(2)$ (dim 4).
- $SU(3)$ requires 8 generators with $\mathfrak{su}(3)$ structure.
- Missing: 4 generators + the Gell-Mann structure constants.

The cascade's natural Lie algebra at $d=12$ is **at most $\mathfrak{u}(2)$
(4-dim)**, not $\mathfrak{su}(3)$ (8-dim).

## Implications for Part IVa's gauge group derivation

The cascade derives:
- **Number of vector fields** at each layer: $\rho(d) - 1$ from Adams.
- **Broken/unbroken status**: hairy ball at even-dim spheres
  ($S^{12}$ at $d=13$ has zero, $S^{11}$ and $S^{13}$ don't).
- **Bott periodicity** of layer structure.

The cascade does **not** strictly derive:
- Specific identification of the structures with $SU(3) \times SU(2) \times U(1)$.
- The full Lie algebra dimension at each layer (8 for $SU(3)$, 3 for
  $SU(2)$, 1 for $U(1)$).
- The structure constants (Gell-Mann, Pauli).

The identification with the SM gauge group is **SM-consistent fitting**,
not strict cascade derivation. The cascade gives compatible content but
the specific group choice uses the SM as guide.

## Tier implications

This is the strongest evidence the session has produced for a tier
revision. The current Tier 1 entry "Gauge group $SU(3) \times SU(2) \times U(1)$"
in the predictions table should arguably be split:

**Tier 1 (cascade-forced):**
- Three gauge layers at $d \in \{12, 13, 14\}$ from Adams + Bott.
- Multiplicities $\rho(d) - 1 = 3, 1, 0$.
- Broken/unbroken pattern from hairy ball obstruction.

**Tier 2-3 (SM-consistent identification, not strictly forced):**
- Specific identification of gauge layers as $SU(3), SU(2), U(1)$.
- Lie algebra structure (8-dim, 3-dim, 1-dim) and structure constants.
- Off-diagonal generators of $SU(3)$ at $d=12$ (5 generators not
  cascade-internal).
- Third generator of $SU(2)$ at $d=13$ (1 generator not cascade-internal).

## Comparison with existing Tier 4b ($\theta_{\rm QCD} = 0$)

Part IVb already flags $\theta_{\rm QCD} = 0$ at Tier 4b, noting that
"the claim that the cascade's topological sectors are classified by
$\pi_3(S^{11})$ rather than $\pi_3(SU(3))$ requires showing how the
vector-field realisation of $SU(3)$ on $S^{11}$ modifies the
topological sector classification."

This Tier 4b acknowledgment **is exactly the gap this investigation
identifies**: the cascade gives vector-field realization on $S^{11}$
(rho(12)-1 = 3 vector fields), not the full $SU(3)$ structure. The
"how do these relate to $\pi_3(SU(3))$" question is the same as "how
do these relate to full $SU(3)$" — and the answer per this
investigation is: **they don't, cascade-internally**.

So the Tier 4b gap on $\theta_{\rm QCD} = 0$ is structural, not just
proof-incomplete. It cannot be closed cascade-internally without
additional structure that the cascade does not currently supply.

## What this means for the framework

This investigation pushes the trichotomy verdict toward (B) for
non-perturbative content even more sharply than the non-Abelian
Wilson test:

| Cascade content | Status |
|---|---|
| Gauge layer placement (Adams) | DERIVED |
| Vector field counts $\rho(d) - 1$ | DERIVED |
| Broken/unbroken pattern | DERIVED |
| Gauge group identification ($SU(3)$, $SU(2)$, $U(1)$) | **SM-consistent fit, not strictly forced** |
| Full non-Abelian Lie algebra structure | NOT DERIVED |
| Structure constants | NOT DERIVED |
| Non-perturbative gauge dynamics | NOT DERIVED |

The cascade derives **layer placement and rough multiplicity**, not
**specific group structure**. The full SM gauge group is matched, not
forced.

## Honest verdict

Bott-shift transport: **does not work**.
- Arithmetic mismatch.
- Wrong mechanism (K-theoretic, not Lie-algebra-component-supplying).
- Cascade's existing gauge identifications already overclaim relative
  to what's strictly derived.

This is the cleanest "the cascade can't do this cascade-natively"
result the session has produced. It identifies a real boundary of the
framework's scope: **the cascade derives the topology of gauge layers,
not the algebra of gauge groups**.

For the framework to claim the SM gauge group is *forced*, an
additional cascade-internal mechanism would be needed that supplies
the missing Lie-algebra structure. None has been identified, and the
candidates I've tested (Bott-shift transport, higher-rank tensor
fields, cross-layer correlations, generation-gauge interactions,
matter-content sources) all fail.

## What this might mean for the program

Two honest options:

**(I) Acknowledge the boundary and qualify Tier 1 claims.** Update
the predictions table to distinguish "cascade derives $X$ vector
field counts at $Y$ gauge layers" (Tier 1) from "we identify these as
$SU(3) \times SU(2) \times U(1)$ matching SM observation" (Tier 2-3).

**(II) Find a genuinely new cascade-internal mechanism.** The session
hasn't identified one. The space of natural candidates seems to be
exhausted. If such a mechanism exists, it would need to be quite
unexpected — perhaps through some structure the cascade has but
hasn't been recognised as supplying gauge generators.

Option (I) is the austerity-compliant move: acknowledge what's
strictly forced and what's SM-imported. Option (II) is open
mathematical investigation, with no concrete leads identified by the
session.

This is the cleanest place the investigation can land. The cascade
has well-characterised positive content (perturbative SM physics
under Option 2 / Reading G plus tensor-product composition) and
well-characterised negative content (non-perturbative gauge dynamics
beyond the framework's reach, AND specific group identification
beyond what the cascade strictly derives).
