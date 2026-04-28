# Cascade Geometric / Topological Audit

Per Prelude Principle 2.2 (austerity): every fact forced by cascade
structure must be either USED, ACKNOWLEDGED OPEN, or explicitly
justified as irrelevant. Silent omission is an unjustified
assumption that the fact "doesn't matter".

## What counts as cascade-forced

The cascade's primitive at each layer is $B^d$ (unit $d$-ball, round
metric inherited from Euclidean $\mathbb{R}^d$) with boundary
$S^{d-1}$. **A fact is cascade-FORCED if it is an intrinsic property
of $S^{d-1}$ as a round unit sphere** — i.e., it holds whenever the
cascade exists, with no additional choice required.

Facts requiring additional structure beyond round-$S^{d-1}$ at each
layer are NOT cascade-forced. These include:
- Multiple spheres in the same $\mathbb{R}^d$ (sphere packing,
  lattices) — the cascade has ONE sphere per layer.
- Non-round metrics (Berger spheres, deformations) — round is forced
  by the unit-ball construction.
- Lie group actions beyond $SO(d)$ acting on $S^{d-1}$ — choosing
  e.g. $G_2$ requires extra structure.
- External theoretical contexts (string-theory critical dimensions,
  Leech lattice / moonshine) — these live outside the cascade's
  primitive set.

These NON-FORCED items are inventoried in Appendix A for completeness
but require no austerity treatment.

## Status legend

- **USED** — invoked in the paper (citation given).
- **ACK** — acknowledged open in the paper.
- **IGN** — cascade-forced, not invoked, no justification on record
  (austerity-flag).
- **TESTED-NEG** — investigated, ruled out (notebook documents).
- **INVESTIGATED-PARTIAL** — examined cascade-internally; supplies
  some content but not full closure of the question that motivated
  investigation.
- **INVESTIGATED-USED** — examined and now incorporated into paper.
- **INVESTIGATED-NOT-NEEDED** — examined; turned out a different
  cascade structure was the productive route.

---

## Section 1: Topological invariants of $S^{d-1}$

| # | Item | Status | Where / Why |
|---|---|---|---|
| 1.1 | $\chi(S^{2n}) = 2$ (even) | USED | Thm 4.14, Rem 4.6, $2\sqrt{\pi}$ identity |
| 1.2 | $\chi(S^{2n+1}) = 0$ (odd) | USED implicitly | No chirality at gauge layers $d=12, 14$ |
| 1.3 | Hairy ball (Poincaré-Hopf on $S^{2n}$) | USED | Part IVa §3, Thm 4.14 |
| 1.4 | Adams' theorem (Radon-Hurwitz $\rho(d)$) | USED | Part IVa Thm 2.4 |
| 1.5 | Bott periodicity (Clifford mod 8) | USED | Part IVa §2 |
| 1.6 | Lefschetz fixed-point | USED | Part IVa Thm 3.2 |
| 1.7 | Brouwer fixed-point | USED implicitly | Subsumed by Lefschetz |
| 1.8 | Borsuk-Ulam (antipodal-map invariant) | **IGN** | Could constrain antipodal cascade structure |
| 1.9 | Generalised Stokes' theorem $B^d \to S^{d-1}$ | USED implicitly | Slicing recurrence |
| 1.10 | Cobordism $S^d = \partial B^{d+1}$ | USED | Cascade tower itself |

---

## Section 2: Measure / metric on $S^{d-1}$

| # | Item | Status | Where / Why |
|---|---|---|---|
| 2.1 | Sphere area $\Omega_d$ (Gamma) | USED | Part 0 §1 |
| 2.2 | Ball volume $V_d$ | USED | Part 0 §3 |
| 2.3 | Boundary dominance $\Omega_{d-1}/V_d = d$ | USED | Part 0 Thm 3.1 |
| 2.4 | Slicing recurrence | USED | Part 0 §3 |
| 2.5 | Concentration of measure (Lévy) | USED | Part II §3 |
| 2.6 | Spherical cap volume | USED | Part II Thm 5.1 |
| 2.7 | Heat kernel asymptotics | **IGN** (structural) | Cascade scalar action lives on the integer tower, not tower $\times$ sphere; sphere-Laplacian operates on a degree of freedom the action does not include (`tools/research/audit_section2_sphere_laplacian.py`) |
| 2.8 | Laplacian eigenvalues $\ell(\ell+d-2)$ | **IGN** (structural) | Same as 2.7: spectral gap $d{-}1$ has right scaling but no cascade match; cascade chose 1D tower fields, not spatial fields per layer |
| 2.9 | Dirac eigenvalues $\pm(k+n)$ | TESTED-NEG | Notebook alt. (A): scaling pathology |
| 2.10 | Spectral zeta $\zeta_D(s)$ | TESTED-NEG | Notebook alt. (A) |
| 2.11 | Spherical harmonics | USED implicitly | Part II concentration |

---

## Section 3: Hurwitz / Hopf / parallelisability

These are properties of $S^{d-1}$ at specific dimensions, forced by
the unit-ball construction.

| # | Item | Status | Where / Why |
|---|---|---|---|
| 3.1 | Hurwitz: $\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O}$ are only normed division algebras | USED | Part III, Part IVa $d=4$ |
| 3.2 | Hopf invariant 1 (Adams 1960): only $d \in \{1,2,4,8\}$ | **IGN** | The forcing argument behind 3.1 not made explicit |
| 3.3 | Parallelisability of $S^1, S^3, S^7$ only | **IGN** | $S^3$ is observer's spatial slice |
| 3.4 | Hopf fibration $S^3 \to S^2$ | **INVESTIGATED-USED** | Closes Born rule gap (Bloch sphere $\mathbb{R}P^3 \to \mathbb{C}P^1$) under Reading G; Part II Remark `reading-G-born` |
| 3.5 | Hopf fibration $S^7 \to S^4$ | **TESTED-NEG** | Tested as cascade-internal arithmetic identity ($\Omega_{n+1}\Omega_n = N(0)^{n+1}\Omega_{2n+1}$); collapses to Legendre duplication, holds at every $n$, no Hopf content |
| 3.6 | Hopf fibration $S^{15} \to S^8$ | **IGN** | $d=9$ or $d=16$? No obvious cascade role |

---

## Section 4: Characteristic classes of $TS^{d-1}$

| # | Item | Status | Where / Why |
|---|---|---|---|
| 4.1 | Euler class $e(TM)$ | USED implicitly | $= \chi$ |
| 4.2 | First Chern class $c_1$ on 2-cycles | ACK | Part IVb Rem 4.9 ($v$ closure residual) |
| 4.3 | Higher Chern classes $c_i$ | **IGN** | Vanishing pattern not invoked |
| 4.4 | Pontryagin classes $p_i$ | **IGN** | Vanish on spheres in low dim — vanishing IS information |
| 4.5 | Stiefel-Whitney classes $w_i$ | **IGN** | Vanishing pattern not invoked |
| 4.6 | $\hat{A}$-genus | USED | Notebook Rem `no-dirac-route`: $\hat{A}(S^{2n})=0$ |
| 4.7 | Atiyah-Singer index theorem | USED implicitly | Via $\hat{A}$ |
| 4.8 | K-theory of spheres | USED implicitly | Bott periodicity equivalent |

---

## Section 5: Smooth structures on cascade $S^{d-1}$

| # | Item | Status | Where / Why |
|---|---|---|---|
| 5.1 | $S^7$ has 28 smooth structures (Milnor) | **IGN** | Cascade silently uses standard |
| 5.2 | $S^{11}$ has 992 smooth structures | **IGN** | Same |
| 5.3 | $S^{12}, S^{20}, S^{28}$ smooth structures | **IGN** | Spinor bundles depend on smooth structure |
| 5.4 | $S^4$ smooth Poincaré conjecture (open) | **IGN** | Observer-relevant, not flagged |
| 5.5 | Smooth-structure-dependence of Dirac operator | **IGN** | Sphere-Dirac route used standard structure |

---

## Section 6: Homotopy groups of $S^{d-1}$

| # | Item | Status | Where / Why |
|---|---|---|---|
| 6.1 | $\pi_3(S^{11}) = \mathbb{Z}_2$ | USED | Part IVb $\theta_{\rm QCD} = 0$ |
| 6.2 | $\pi_4(S^3) = \mathbb{Z}_2$ | **IGN** | Hopf-fibration descendant |
| 6.3 | $\pi_n(S^k)$ table | **IGN** | Cascade picks $\pi_3(S^{11})$; others silent |
| 6.4 | Stable homotopy $\pi^s_n$ | **IGN** | Generic structure not invoked |
| 6.5 | EHP sequence | **IGN** | Not invoked |
| 6.6 | Steenrod squares $Sq^i$ | **IGN** | Not invoked |
| 6.7 | Cohomology ring $H^*(S^{d-1})$ | USED implicitly | Trivial ring $\mathbb{Z}[x]/(x^2)$ |

---

## Section 7: Riemannian structure of round $S^{d-1}$

| # | Item | Status | Where / Why |
|---|---|---|---|
| 7.1 | Constant sectional curvature $K=1$ | USED implicitly | Standard round metric |
| 7.2 | Ricci tensor $\text{Ric} = (d-2)g$ | USED implicitly | Part III §14 |
| 7.3 | Scalar curvature $R = (d-1)(d-2)$ | USED implicitly via 7.2 | $R_{\rm scal} = \mathrm{tr}(\mathrm{Ric}) = (d-1)(d-2)$ is just the trace of the Ricci tensor (entry 7.2, USED).  No new content beyond 7.2 |
| 7.4 | Lichnerowicz formula $\slashed{D}^2 = \nabla^*\nabla + R/4$ | **IGN** (structural exclusion) | Sphere-Dirac route forbidden by 4.6 ($\hat A(S^{2n})=0$, Notebook Rem `no-dirac-route` in Part IVb) |
| 7.5 | Conformal Killing spinors | **IGN** (structural exclusion) | Same as 7.4: requires sphere-Dirac, excluded by 4.6 |
| 7.6 | Riemannian sectional/Ricci/scalar relations | USED | Lovelock at $d=4$ (Part III) |

---

## Section 8: Dynamics on $S^{d-1}$

| # | Item | Status | Where / Why |
|---|---|---|---|
| 8.1 | Morse function on $S^{2n}$ (height) | USED | Thm 4.14 |
| 8.2 | Morse-Bott structures | USED implicitly | Same |
| 8.3 | $SO(d)$ Killing fields on $S^{d-1}$ | **INVESTIGATED-PARTIAL** | Cascade has $\mathfrak{so}(d)$ via $SO(d)$-invariance; bracket computation at $d=12$ shows the 3 Adams nowhere-zero vector fields close as $\mathfrak{su}(2)$ from quaternionic structure on $H^3$. For $\mathfrak{su}(N)$ with $N\geq 3$ at gauge layers, full closure requires extra structure (item 10.11 was the productive route) |
| 8.4 | Equivariant index theorem (Bott localisation) | **INVESTIGATED-NOT-NEEDED** | Item 10.11 ($G_2/SU(3)$ at $d=7$) was the productive path for the SU(3) algebra; equivariant localisation didn't end up needed |
| 8.5 | Mathai-Quillen Thom form | TESTED-NEG | Notebook Route 4: scaling pathology |

---

## Section 9: Foliation / fibration structure

| # | Item | Status | Where / Why |
|---|---|---|---|
| 9.1 | Morse foliation of $S^3$ by $S^2$ | USED | Part I §3.2 ($\Omega_2/\Omega_3 = 2/\pi$) |
| 9.2 | Morse foliation of $S^4$ by $S^3$ | USED | Part IVb Rem 4.9 ($v$ closure) |
| 9.3 | Generic Morse foliation of $S^{2n}$ by $S^{2n-1}$ | **IGN** | Used at $d=3, 4$ only |
| 9.4 | Hopf fibration as foliation | **IGN** | See 3.5 |
| 9.5 | Cobordism cascade | USED | Cascade tower |

---

## Section 10: Specific dimensional coincidences

Cascade-distinguished or cascade-touching dimensions and their forced
structure.

| # | Item | Status | Where / Why |
|---|---|---|---|
| 10.1 | $d_V = 5$ (volume max) | USED | Part 0 |
| 10.2 | $d_0 = 7$ (area max) | USED | Part 0 |
| 10.3 | $d_1 = 19$ (first threshold) | USED | Part 0 |
| 10.4 | $d_2 = 217 = 7 \cdot 31$ (second threshold) | USED, partial | $7 \cdot 31$ structure not exploited |
| 10.5 | $217 - 19 = 198$ layer count | USED | Part I §6 |
| 10.6 | $d=4$ observer | EMPIRICAL | Part III declared empirical |
| 10.7 | $d = 4 = \dim_\mathbb{R}\mathbb{H}$ | USED | Part III |
| 10.8 | $d = 8$ first Bott multiple | USED | Part IVa |
| 10.9 | $d = 12$ Adams unique $\rho-1=3$ | USED | Part IVa Thm 2.4 |
| 10.10 | $d = 14 = \dim G_2$ | **IGN** | Coincidence at U(1) layer? |
| 10.11 | $d = 7$ = $S^6$ admits $G_2$ structure | **USED** | Reading (III): SU(3) algebra at $d=7$ via $G_2/SU(3)$ on $S^6$. Part IVa Remark `reading-III`. Verifier `cascade_d7_su3_bs_closure.py`. Closes $b/s$ to 0.014\% via $-\alpha(7)/\chi^4$ (Part IVb Tier 3, proposed) |

---

## Section 11: Number-theoretic structure of cascade primitives

| # | Item | Status | Where / Why |
|---|---|---|---|
| 11.1 | $\Gamma(n+1/2) = (2n)!\sqrt{\pi}/(4^n n!)$ | USED implicitly | Half-integer evaluations |
| 11.2 | $\Gamma$ recursion | USED | Slicing |
| 11.3 | Beta function identities | USED | Slicing integral |
| 11.4 | Euler reflection $\Gamma(z)\Gamma(1-z) = \pi/\sin(\pi z)$ | **IGN** | Not invoked |
| 11.5 | Gauss multiplication theorem | USED ($n=2$) | Part 0 Lemma `lem:R-duplication`: $R(2d-1)R(2d) = 1/d$ |
| 11.6 | Wallis product | **IGN** | Implicit in $R(d) \sim \sqrt{2/d}$ asymptotics |
| 11.7 | Stirling's formula | USED | Asymptotics |
| 11.8 | Continued fractions of $\Gamma$ ratios | **IGN** | Not invoked |
| 11.9 | Zeta values at integer / half-integer | **IGN** | Not invoked |

---

## Section 12: Cascade dynamics (already invoked)

| # | Item | Status | Where / Why |
|---|---|---|---|
| 12.1 | Slicing axis as time | USED | Part II §7.1 |
| 12.2 | Forced precession $\alpha = \pi/2$ | USED | Part II Thm 6.1 |
| 12.3 | Wick rotation $x \leftrightarrow it$ | USED, ACK | Part III Rem `wick-rotation-cascade` |
| 12.4 | Lorentzian signature $(-,+,+,+)$ | USED | Part III Thm 10.2 |
| 12.5 | $J^2 = -\text{Id}$ from two-step composition | USED | Part II Thm 6.2 |
| 12.6 | Periodicity-4 in propagator phase | USED | Part II Cor 6.5 |

---

## Summary of austerity-flagged items (post-investigation)

**Items resolved by investigation:**
- 3.4 — Hopf fibration $S^3 \to S^2$: USED via Reading G (Born rule
  Bloch sphere closure).
- 3.5 — Hopf fibration $S^7 \to S^4$: TESTED-NEG (Legendre duplication
  identity, no Hopf content).
- 8.3 — $SO(d)$ Killing fields: INVESTIGATED-PARTIAL (closes
  $\mathfrak{su}(2)$ at $d=12$ via Adams quaternionic brackets; full
  $\mathfrak{su}(N)$ via different route below).
- 8.4 — Equivariant index theorem: INVESTIGATED-NOT-NEEDED.
- 10.11 — $S^6 = G_2/SU(3)$: **USED** (Reading III, supplies SU(3)
  algebra at $d=7$; closes $b/s$ to 0.014\% as new Tier 3).

**Remaining IGN items (still cascade-forced, not yet invoked):**

*Higher cascade-relevance:*
- 3.2, 3.3 — Hopf invariant 1 / parallelisability forcing argument
  (no fresh investigation; ladder Hurwitz $\to$ parallel $\to$
  Hopf-1 $\to$ Bott-8 still implicit).
- 4.2 — first Chern class on Morse 2-cycles (ACK in Part IVb).
- 5.1–5.5 — smooth structures on cascade-relevant spheres.
- 10.10 — $\dim G_2 = 14$ at U(1) layer (coincidence not investigated;
  worth checking now that 10.11 is USED).

*Medium relevance:*
- 1.8 — Borsuk-Ulam.
- 7.4 — Lichnerowicz formula.
- 9.3 — generic Morse foliation across all even spheres.

*Lower relevance, should still be checked:*
- 4.3, 4.4, 4.5 — higher Chern, Pontryagin, Stiefel-Whitney classes.
- 6.2–6.6 — generic homotopy groups beyond $\pi_3(S^{11})$.
- 7.3, 7.5 — scalar curvature, conformal Killing spinors.
- 11.4, 11.5, 11.6, 11.8, 11.9 — Gamma identities not invoked.

---

## Appendix A: items NOT cascade-forced (require external structure)

These appear in higher-dimensional mathematics but are NOT properties
of cascade $S^{d-1}$ as the cascade has it. Listed for explicitness so
the audit is unambiguous. None require austerity treatment.

**Sphere packing / lattices in $\mathbb{R}^d$** — about MULTIPLE spheres
in same Euclidean space; the cascade has ONE sphere per layer.
- Kissing numbers (12, 24, 240, 196560 in dim 3, 4, 8, 24).
- $E_8$ lattice / Viazovska 2016 optimal packing.
- Leech lattice in $\mathbb{R}^{24}$.
- 24-cell regular polytope.

**Non-$SO(d)$ Lie group actions on $S^{d-1}$** — require choosing the
group; cascade only has $SO(d)$ acting on $S^{d-1}$ as inherited from
the embedding $S^{d-1} \subset \mathbb{R}^d$.
- $SU(n)$ acting on $S^{2n-1}$ (requires complex structure choice
  beyond what the cascade provides at generic $d$).
- $Sp(n)$ acting on $S^{4n-1}$.
- $G_2$ on $S^6$ — UNLESS forced by some cascade structure at $d=7$;
  this is item 10.11 above (cascade-forced via $d_0$, IGN).
- $F_4, E_6, E_7, E_8$ — no cascade-forcing argument.

**Non-round metric structures** — cascade uses round $S^{d-1}$ from
unit ball.
- Berger spheres / squashed metrics.
- Reeb / contact structures (require additional 1-form choice).

**Stiefel manifolds, Grassmannians, flag varieties** — different
manifolds, not cascade primitives.

**Bounded symmetric domains (Hua/Wyler route)** — tested negatively in
notebook; not cascade-forced.

**Critical dimensions from external theories:**
- $d = 10$ superstring critical.
- $d = 11$ M-theory critical.
- $d = 26$ bosonic string critical.
- $d = 248 = \dim E_8$.

Cascade has no role for these. The cascade's distinguished dimensions
$\{5, 7, 19, 217\}$ come from Gamma function critical points, not from
string consistency or exceptional Lie algebra dimensions.

---

## What austerity requires for each IGN item

For each item in Sections 1–12 marked **IGN**:

1. **Investigate** if relevance is plausible. The most concrete is 3.5
   (Hopf fibration $S^7 \to S^4$ at observer host).
2. **Show subsumption** by something already used (e.g., 4.8 K-theory
   is implicit in Bott periodicity).
3. **Justify irrelevance** via specific cascade structure (e.g., a
   direct argument that scalar curvature on $S^{d-1}$ doesn't enter
   any cascade observable derivation).

Currently the paper does NONE of these for any IGN item. They are
silently omitted, which austerity flags as an unjustified assumption
that the fact "doesn't matter".

---

## Methodology validation

The audit's central thesis (per Prelude Principle 2.2: investigate
every cascade-forced fact, don't silently omit) was empirically
validated by item 10.11. An apparent crisis ("cascade can't supply
SU(3) at $d=12$ — bracket computation gives only $\mathfrak{su}(2)$")
resolved by re-engaging with 10.11, which had been dismissed as IGN.
The result: SU(3) algebra is cascade-internal at $d=7$ via $G_2/SU(3)$,
and a Tier 4 observable ($b/s$) closes to Tier 3 precision via
$-\alpha(7)/\chi^4$.

Working method confirmed: when an apparent gap appears, re-examine
IGN items before concluding the cascade fails. The audit's IGN list
is a checklist of unrealised cascade content, not a list of
irrelevant facts.

## Recommendation

**Action 1**: ~~Investigate Hopf fibration $S^7 \to S^4$ at observer
host (item 3.5).~~ **DONE — TESTED-NEG (Legendre duplication, no Hopf
content). The actually-productive direction was item 10.11 ($G_2$ on
$S^6$ at $d=7$).**

**Action 2**: For each remaining IGN item in Sections 1–12, write a
one-line justification (subsumption / dismissal) or a TODO. Priority
order is now:
- 10.10 ($\dim G_2 = 14$ at U(1) layer) — fresh look warranted
  given 10.11 is now USED.
- 3.2, 3.3 (Hopf-1 / parallelisability forcing) — make the
  Hurwitz $\to$ parallel $\to$ Hopf-1 $\to$ Bott-8 chain explicit
  in Part IVa as the structural reason for Bott periodicity.
- 4.2 (first Chern on Morse 2-cycles) — already ACK in Part IVb;
  the open question is the formal proof that the 4D tangent-field
  obstruction equals a first Chern class.

**Action 3**: Promote this audit to a Part IVa appendix once 10.11
and the related Reading (III) are formally written up in Part IVa.

---

## Caveats

This audit is not exhaustive — there are likely cascade-forced facts I
haven't enumerated. Each new item should be added under its
appropriate status with a citation or a TODO.

The boundary between "cascade-forced" and "requires external
structure" is itself a structural question. The audit's Appendix A
items are listed as not-cascade-forced under the current cascade
primitive set ($B^d$, $S^{d-1}$, round metric); future cascade
extensions could change this boundary.
