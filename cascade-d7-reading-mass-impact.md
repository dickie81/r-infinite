# Particle mass impact under the d=7 G_2/SU(3) reading

This document investigates the impact on cascade particle mass
predictions of accepting the audit-revealed reading where SU(3) algebra
source is at d=7 (via G_2 / octonions) rather than d=12 (Adams).

## Bottom line

**Numerical mass predictions: UNCHANGED.**
**Structural meaning: STRENGTHENED in most cases; one Tier 4b claim
weakened.**
**One open opportunity: Tier 4 quark mass patterns potentially closeable
via $\alpha(7)/\chi^k$ corrections.**

## What reading (III) says

| Gauge group | Algebra source | Running anchor |
|---|---|---|
| SU(3) | $d=7$ ($G_2$ on $S^6$) | $d=12$ (Adams) |
| SU(2) | $d=4$ ($S^3$ = unit quaternions) | $d=13$ (Adams + Lefschetz) |
| U(1) | cascade J / $S^1$ | $d=14$ (Adams) |

Each gauge group has TWO cascade-internal anchors: one for algebra
structure (Hurwitz layer) and one for running (Adams layer).

## Why mass predictions are unchanged

Cascade descent paths in Part IVa Theorem `forced-paths` use the cascade
slicing potential $p(d)$, summed over layers in the path:
$$\Phi(d_b) - \Phi(d_a) = \sum_{d=d_a+1}^{d_b} p(d).$$

The $p(d)$ values are cascade primitives (from digamma function),
independent of which gauge structure "lives" at each layer. Reading (III)
doesn't change $p(d)$ or the descent paths, so:

**All Tier 1-4 predictions are numerically unchanged.**

## Path-through-d=7 consistency check

The cascade's existing descent paths for SU(3)-relevant observables ALL
pass through d=7 implicitly:

| Observable | Path | d=7 in path? | SU(3) relevant? | Consistent? |
|---|---|---|---|---|
| $\alpha_s(M_Z)$ | $d=5..12$ | YES | YES | ✓ |
| $m_\tau/m_\mu$ | $d=6..13$ | YES | YES (via Higgs) | ✓ |
| $m_\mu/m_e$ | $d=14..21$ | no | no (leptonic) | ✓ |
| EW VEV | $d=5..12$ | YES | YES | ✓ |
| $\sin^2\theta_W$ | $d=5..14$ | YES | YES | ✓ |
| $\theta_C$ Cabibbo | $\alpha(7)/\chi^2$ | YES (source) | YES | ✓ |

**Every observable that involves SU(3) has a descent path that includes
d=7. Every observable that doesn't (m_μ/m_e) has a path that doesn't.**
This is structural consistency, automatic from the cascade's existing
formulas.

## Strengthening: cascade-internal gauge group

**Tier 1 "Gauge group $SU(3) \times SU(2) \times U(1)$" becomes fully
cascade-internal under reading (III):**

- $SU(3)$ at $d=7$ from $G_2 = \mathrm{Aut}(\mathbb{O})$ acting transitively on
  $S^6$, with $SU(3)$ as stabilizer of unit imaginary octonion.
  Cascade-internal because octonions are forced by Hurwitz at $d=8$.
- $SU(2)$ at $d=4$ from $S^3 = \mathrm{unit\ quaternions}$. Cascade-internal
  because quaternions are forced by Hurwitz at $d=4$ and $S^3$ is the
  observer's spatial slice.
- $U(1)$ from cascade complex structure $J$ (Part II Thm `complex`).

**The SM gauge group is now cascade-forced via the Hurwitz division
algebras at $\{2, 4, 8\}$ (with $G_2$ as the octonion automorphism
group).**

This strengthens the headline claim: previously, "Gauge group SU(3) ×
SU(2) × U(1)" relied on Adams + SM-consistent identification (Tier 1 but
with hidden SM input per the bracket computation finding). Now, with the
Hurwitz algebra-source identification, it's cascade-internal.

## Strengthening: $\alpha(d^*)/\chi^k$ source layers gain meaning

The seven precision closures in Tier 3 use four source layers $d^* \in \{5, 7, 14, 19\}$. Under reading (III), each has structural meaning:

| Source $d^*$ | Cascade role | Observables sourced |
|---|---|---|
| 5 | observer host $d_V$, where SU(2) $S^3$ slice lives | $\sin^2\theta_W$, $\Omega_m$ |
| 7 | SU(3) algebra source ($G_2$ on $S^6$, area max $d_0$) | $\theta_C$ (Cabibbo) |
| 14 | U(1) running anchor | $\alpha_s$, $m_\tau/m_\mu$ |
| 19 | first phase transition $d_1$ | $m_\tau$ abs, $\ell_A$ |

The $\alpha(7)/\chi^2$ correction for $\theta_C$ is now cascade-natural:
$\theta_C$ is a quark-mixing angle, quarks have SU(3) color, and SU(3)
algebra source is at $d=7$. The correction sources at the SU(3) layer.

This is a structural confirmation of an existing Tier 3 derivation.

## Weakening: $\theta_{\rm QCD} = 0$ claim's gap deepens

**This is the one negative impact.**

Currently (Tier 4b in Part IVb): the claim $\theta_{\rm QCD} = 0$ exactly is
derived from $\pi_3(S^{11}) = \mathbb{Z}_2$, with the topological sectors of
the cascade's gauge structure at $d=12$ being classified by this homotopy
group.

Under reading (III): $SU(3)$ algebra is at $d=7$, not $d=12$. The
relevant topological sector classification is $\pi_3(SU(3)) = \mathbb{Z}$
(infinite, not $\mathbb{Z}_2$). The cascade's argument
"$\theta_{\rm QCD} = 0$ from $S^{11}$ topology" becomes a more clearly
unjustified identification of $S^{11}$ topology with $SU(3)$ topology.

The Tier 4b acknowledged gap was: "the claim that the cascade's
topological sectors are classified by $\pi_3(S^{11})$ rather than
$\pi_3(SU(3))$ requires showing how the vector-field realisation of
SU(3) on $S^{11}$ modifies the topological sector classification."

Under reading (III), this gap deepens: the cascade's SU(3) is NOT
realised on $S^{11}$ (only u(2) is, per the bracket computation). The
realisation is at $S^6$ via $G_2$. The cascade's $\theta_{\rm QCD}$ argument
needs to use the d=7 / G_2 topology, not the d=12 / S^{11} topology.

**This is a real downgrade.** The Tier 4b claim should arguably be
moved to Tier 5 ("provisional, derivation incomplete") or flagged with
"requires reformulation under reading (III)."

## Open opportunity: Tier 4 quark mass patterns

The current Tier 4 entries in Part IVb (line 1948):
- $m_b/m_\tau = e$ (1.05% deviation).
- $b/s = (\text{lepton ratio}) \times e$.
- $(t/b)/(c/s) = N_c = 3$.

These are "observed patterns needing derivation" at Tier 4. Under
reading (III), $\alpha(7)/\chi^k$ corrections (sourced at SU(3) algebra
layer) are a candidate for closing some of these:
- $\alpha(7) = R(7)^2 / 4 = 8/(105\pi)$ (closed form).
- $\alpha(7)/\chi^k$ for various $k$ gives different correction
  magnitudes.

If quark mass ratios close via $\alpha(7)/\chi^k$ for some specific
$k$, they'd move from Tier 4 to Tier 3 alongside $\theta_C$. This is
**open investigation enabled by reading (III)**.

## Summary of tier impacts

| Prediction | Current tier | Under reading (III) | Direction |
|---|---|---|---|
| Gauge group $SU(3)\times SU(2)\times U(1)$ | Tier 1 | Tier 1 (strengthened) | ↑ |
| Tier 2-3 mass / coupling predictions | various | unchanged numerically | ↔ |
| $\theta_C$ Cabibbo | Tier 3 | Tier 3 (structurally clarified) | ↔ |
| $\theta_{\rm QCD} = 0$ | Tier 4b | Tier 5 / reformulation needed | ↓ |
| $m_b/m_\tau$, $b/s$, $(t/b)/(c/s)$ | Tier 4 | Tier 3 candidates via $\alpha(7)/\chi^k$ | ↑ (open) |
| Other Tier 4 frontier | Tier 4 | unchanged | ↔ |

**Net: one downgrade ($\theta_{\rm QCD}$), several strengthenings, one
open upgrade opportunity (quark masses).**

## Mass formula audit

Going through Part IVb's mass formulas explicitly:

**$m_\mu/m_e$** (Tier 2, 0.13% deviation): path $d=14..21$. Lepton ratio,
no SU(3) involvement. Reading (III) consistent (path doesn't include
d=7). **Unchanged.**

**$m_\tau/m_\mu$** (Tier 3 via $\alpha(14)/\chi$, 0.24σ): path $d=6..13$,
includes d=7. Tau and muon are leptons, no direct SU(3). The d=7 in
the path passes through SU(3) algebra source but is not directly
relevant. **Unchanged.**

**$m_\tau$ absolute** (Tier 3 via $\alpha(19)/\chi$, 0.31σ): path
$d=5..13$ + $\alpha(19)/\chi$ source at $d_1$. Reading (III)
consistent. **Unchanged.**

**$m_b/m_\tau \approx e$** (Tier 4, 1.05% deviation): involves $b$
quark (SU(3) triplet) vs $\tau$ lepton (singlet). Under reading (III),
$b$'s SU(3) charge sources at d=7. The $b$ vs $\tau$ ratio might pick
up an $\alpha(7)/\chi^k$ correction. **OPEN UPGRADE candidate.**

**$\alpha_s(M_Z)$** (Tier 3 via $\alpha(14)/\chi$, 0.02σ): running of
strong coupling. Path $d=5..12$ implicitly includes d=7 (SU(3) source).
**Unchanged.**

**EW VEV $v$** (Tier 3 partial closure): involves SU(2) Higgs
mechanism. Under reading (III), SU(2) at $d=4$ (host $S^3$). The
existing Part IVb Rem 4.9 uses Morse foliation of $S^4$ by $S^3$ —
consistent with SU(2) source at observer's $S^3$. **Unchanged.**

**Higgs mass $m_H = 125.82$ GeV** (Tier 3): inherits from EW VEV.
**Unchanged.**

## Why reading (III) doesn't change numerical predictions

The cascade's mass formulas are based on cascade DESCENT POTENTIAL
$\Phi(d) = \sum p(d')$. The $p(d)$ values are cascade primitives
(digamma), and they're the same regardless of which gauge structure
"lives" at any given layer.

Reading (III) is a **structural reinterpretation**: it says cascade has
two anchor points per gauge group (algebra source + running anchor)
rather than one. Both anchors are at cascade-distinguished layers, and
the descent paths happen to span them naturally.

The cascade's predictive content is in the $p(d)$ values and the
descent paths. Reading (III) preserves both. It changes the
INTERPRETATION of which layer "is" SU(3) (algebra source d=7 vs running
anchor d=12), but doesn't change which descent paths are forced or
which $p(d)$ values they sum.

## Verifier

`tools/verifiers/cascade_mass_impact_d7_reading.py` confirms numerically:
- All cascade descent paths pass through d=7 iff SU(3) is relevant.
- All Tier 1-3 predictions are numerically unchanged.
- $\alpha(7)/\chi^k$ correction magnitudes are computed for k = 1, 2, 3.

## Next steps

The most concrete forward step: investigate whether Tier 4 quark mass
patterns close under $\alpha(7)/\chi^k$ corrections for some specific
$k$. If they do, this would:
- Promote Tier 4 to Tier 3 for those observables.
- Confirm reading (III) (d=7 as SU(3) algebra source) by demonstrating
  predictive use of the d=7 layer for SU(3)-relevant observables beyond
  $\theta_C$.
- Strengthen the cascade's overall predictive coverage.

This is concrete, computational, and bounded — a clean test of whether
reading (III) is just a reinterpretation or actually enables new
predictions.
