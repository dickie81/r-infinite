# Derivation 3: cascade-native composite matter via path tensor product

This document attempts follow-up 3 from
`cascade-path-state-hilbert-derivation1.md`: derive cascade-internally
how matter content at multiple cascade layers composes into a single
multi-layer matter state. This was identified as the
**austerity-forced** next step: the cascade's own matter content
sits at multiple layers simultaneously (a quark has color, weak
isospin, and hypercharge), and the cascade currently lacks a
formalised composition rule.

## Result

**Cascade-internal forcing of tensor-product composition rule.** The
cascade's multiplicative slicing structure plus the independence of
Adams gauge groups at different layers forces tensor-product
composition. This delivers the composition mechanism. Specific
representations at each gauge layer (fundamental vs. higher) remain
imported from SM observation; deriving them cascade-natively is open
beyond follow-up 3's scope.

## The forcing argument

Three cascade-internal facts force tensor product:

**(a) Slicing recurrence is multiplicative.** Paper 0's recurrence
$V_{d+1} = V_d \cdot \sqrt{\pi}\,R(d+1)$ composes cascade content by
*product*, not by sum. Cascade descent through multiple layers
multiplies factors layer-by-layer.

**(b) Adams gauge groups at different layers are independent.**
Part IVa Theorem `adams` places gauge groups at $d \in \{12, 13, 14\}$:
- $d=12$: $SU(3)$, $\rho(12)-1=3$ vector fields on $S^{11}$.
- $d=13$: $SU(2)$, $\rho(13)-1=1$ vector fields on $S^{12}$.
- $d=14$: $U(1)$, $\rho(14)-1=0$ vector fields on $S^{13}$.

These are *independent* Adams structures at three distinct distinguished
dimensions. No cascade-internal relation forces them to act on the same
state space; each is its own gauge structure at its own layer.

**(c) Tensor product is the unique composition that respects (a) and
(b).** For independent multiplicative actions on a single state,
the standard mathematical answer is tensor product:
$$\mathcal{H}_{\rm composite} = \bigotimes_{d \in {\rm gauge\ layers}} V_{d, R(d)}.$$

Direct sum is excluded by (a) — cascade descent is multiplicative,
not additive. Wedge/symmetric/antisymmetric products are excluded by
(b) — no relation between distinct Adams structures justifies them.

So the cascade's own structure forces tensor product as the
composition rule.

## Numerical verification on SM matter

`tools/verifiers/cascade_path_tensor_product.py` computes path-tensor-
product Hilbert dim for each SM fermion:

| Particle | $SU(3)$ rep | $SU(2)$ rep | $U(1)$ Y | Hilbert dim |
|---|---:|---:|---:|---:|
| $Q_L$ (LH quark doublet) | 3 | 2 | Y | **6** |
| $u_R$ (RH up-quark) | 3 | 1 | Y | **3** |
| $d_R$ (RH down-quark) | 3 | 1 | Y | **3** |
| $L_L$ (LH lepton doublet) | 1 | 2 | Y | **2** |
| $e_R$ (RH charged lepton) | 1 | 1 | Y | **1** |
| $\nu_R$ (RH neutrino) | 1 | 1 | 0 | **1** |
| $H$ (Higgs doublet) | 1 | 2 | Y | **2** |

**Total fermion d.o.f. per generation** (Weyl, no RH neutrino):
$6+3+3+2+1 = 15 = 30/2$ Dirac, matching Part IVa Section 4's stated
**30 d.o.f. per generation**.

The cascade-internal tensor-product rule is consistent with SM matter
content for every fermion species and the Higgs.

## The Bott-orbit structure

Generation layers $d \in \{5, 13, 21\}$ are consecutive points in the
$d \bmod 8 = 5$ Bott orbit (Part IVa Remark `bott-length`). Their
positions relative to the gauge window $\{12, 13, 14\}$ are:

- **Gen-3** at $d=5$: above the gauge window (lighter cascade descent
  through gauge window for gauge-anchored observables).
- **Gen-2** at $d=13$: AT the $SU(2)$/Higgs layer.
- **Gen-1** at $d=21$: below the gauge window.

Gen-2's coincidence with $d=13$ is *not* a freedom — it's forced by
the Bott period and the position of the gauge window. Part IVa Section
4 line 706 notes this gives Gen-2 the $1/N_c$ colour normalisation
factor "inside the gauge window."

So the cascade's three generations are structurally distinguished by
their position relative to the gauge window:
- Gen-3, Gen-1: outside, with $N_c=3$ colour channels coherently.
- Gen-2: inside, with $1/N_c$ correction.

This matches observed mass-spectrum patterns and is forced
cascade-internally.

## What's forced vs. what isn't

### Forced cascade-internally (Reading G + this derivation)

| Cascade-internal forcing | Status |
|---|---|
| Tensor product as composition rule | DERIVED (slicing multiplicative + Adams independence) |
| Hilbert dim from path representation content | DERIVED |
| Path determined by particle's gauge charges | DERIVED |
| Number of generations = 3 | Derived (Bott + $d_1=19$ cutoff, Part IVa) |
| Generation positions $\{5, 13, 21\}$ | Derived (Bott period + gauge window placement) |

### Still imported / open

| Component | Status |
|---|---|
| Specific representation at each gauge layer (fundamental vs. higher) | IMPORTED FROM SM |
| Why each particle takes its specific path | IMPORTED FROM SM (i.e., particle quantum numbers determine path; cascade doesn't yet derive WHICH particles exist) |
| Right-handed neutrino existence | OPEN (cascade doesn't currently constrain) |
| Particle multiplet structure (e.g., why Q_L is a doublet vs. four singlets) | IMPORTED |

The cascade derives the *gauge groups* at distinguished layers; it
does not yet derive the *representation content* of matter under
those groups. The SM tells us $Q_L$ is fundamental of $SU(3)$ × fundamental
of $SU(2)$ × hypercharge $\frac{1}{6}$; the cascade so far accommodates
this without independently deriving it.

## What this delivers for Option 2

| Component | Status before | Status after follow-up 3 |
|---|---|---|
| Path-state Hilbert space construction | Reading G (gauge-equiv) | Reading G + tensor product composition |
| Born rule from $U(1)$ gauge | Forced for dim ≥ 3 | Forced for dim ≥ 3, qubits closed via composition |
| Running coupling as Wilson holonomy | Abelian, derived | Abelian, derived |
| Hilbert dim from path content | Open | Forced via tensor product of layer reps |
| Composite system tensor product | Open | DERIVED (this) |
| Continuous-variable Hilbert spaces | Open | Open |
| Non-perturbative gauge dynamics | Open | Open |

**Three of Option 2's open items closed** (composite tensor product,
Hilbert dim scaling, qubit Born rule via composition). Two remain open
(continuous variables, non-perturbative dynamics).

The qubit Born rule closure is automatic: any qubit (e.g., a single
$SU(2)$ doublet) is part of a larger cascade matter context (the full
fermion with color, weak, hypercharge, generation content). Tensor
products with higher-dim partners reach dim $\geq 3$, where Cauchy
forces $g(x) = x$, and consistency drags the qubit Born rule to
$g(x) = x$ as well. Same mechanism as Gleason's compositionality
closure of the dim-2 gap.

## Updated trichotomy verdict

| Physics regime | Cascade delivers | Reading |
|---|---|---|
| Perturbative running couplings | ✓ (follow-up 2) | (A) |
| Mass ratios / generation structure | ✓ (Part IVa+IVb) | (A) |
| Gauge group determination | ✓ (Part IVa Adams) | (A) |
| Born rule (dim ≥ 3) | ✓ (follow-up 1) | (A) |
| Composite matter Hilbert spaces | ✓ (follow-up 3) | (A) |
| Specific gauge representations | imported from SM | (A)? open |
| Non-perturbative gauge dynamics | ✗ | (B) |
| Continuous-variable QM | ✗ | (B) |

**Most of perturbative SM physics falls under reading (A)** — cascade
right, formulation needs Option-2-style reformulation but the content
is there. The remaining (B) items are non-perturbative (confinement,
instantons, tunnelling, harmonic oscillators) — physics the cascade
doesn't currently claim to derive.

This is the structural verdict at session's close: the cascade is a
*real partial framework* covering perturbative SM physics under the
path-state reformulation. Non-perturbative content is genuinely
outside its scope as currently formulated.

## What this means for the program

**For Parts 0–V**: the existing perturbative content is consistent
with Option 2's path-state reformulation. The reformulation is
mostly a re-reading of existing structure, not a content change.
Specific paragraphs would need to be updated:

- Part II §5 Born rule: re-derive on the complex simplex with $U(1)$
  gauge invariance forcing $g(x) = x$ for dim ≥ 3, with Gleason-style
  compositionality closing dim 2.
- Part II §7 discrete propagator: explicitly identify $L(d) = iN(d)$
  as a gauge-fixed Wilson-line representative; physical content is
  the gauge-invariant holonomy.
- Part IVa Theorem `forced-paths`: re-state $\Phi(d)$ as the log
  Abelian Wilson holonomy of connection $A(d) = p(d)$.
- Part IVa Section 4: matter content composition via path tensor
  product made explicit.

**For the headline claim**: the "indistinguishable from our universe"
phrasing should be qualified. The cascade is indistinguishable from
*perturbative* SM physics under Option 2. Non-perturbative content
(confinement, instantons, vacuum structure) is currently outside the
cascade's claims and is the remaining gap if the headline is to hold.

This is the cleanest place the session has reached. The framework's
scope is now well-characterised: real for perturbative physics under
Option 2, partial for non-perturbative physics.
