#!/usr/bin/env python3
"""
Open-closed mixed cascade observables: the chirality selection-rule
integer m - k as a unifying classification.

CONTEXT
=======
Two cascade chirality structures have been identified:

  OPEN LINE  (Part IVb thm:chirality-factorisation, EXISTING):
    Observable Q with k independent definite-chirality propagator
    modes has Green's function G_Q = G / chi^k.  Each open-line
    mode contributes 1/chi (chirality SELECTION on the open observable).

  CLOSED LOOP  (CONJECTURED, see cascade_alpha_em_screening.py):
    Observable Q with m closed loops has topological invariant
    contribution chi^m * Gamma(1/2)^(legs in loops).  Each closed
    loop contributes chi (chirality MULTIPLICITY: loop traces
    both basins).

For MIXED observables with both k open-line modes AND m closed loops,
the natural extension is a CHIRALITY SELECTION RULE governed by the
signed integer m - k:

  chirality factor = chi^(m - k)

  m - k > 0: closed-dominated (more loops than open modes).
  m - k = 0: balanced (open and closed cancel; chirality factor 1).
  m - k < 0: open-dominated (more open modes than loops).

This script:
  1. Articulates the chirality selection rule chi^(m - k).
  2. Tabulates the cascade's existing precision predictions by m - k.
  3. Identifies gaps in the spectrum (e.g., balanced m-k = 0 is missing).
  4. Notes a STRUCTURAL ASYMMETRY: open-line primitive is alpha(d*)
     (layer-DEPENDENT, source coupling); closed-loop primitive is
     Gamma(1/2)^n (layer-INDEPENDENT, topological obstruction).
     These are different kinds of primitives, not a clean dual.
  5. Discusses what the m-k organization unlocks and what it doesn't.

WHAT THIS SCRIPT DELIVERS
=========================
Identifies chi^(m-k) as a chirality selection rule that classifies
all cascade precision predictions on a single integer axis, spanning
m - k = -4 (b/s) to +1 (1/alpha_em screening) in current observables.

Highlights the m - k = 0 balanced case as currently UNFILLED: no
existing cascade observable has both 1 open-line mode and 1 closed
loop with chirality cancellation.  Candidates include fermion-mass
self-energy corrections and (g-2)-style vertex corrections.

WHAT THIS SCRIPT DOES NOT DO
============================
  - Promote the m-k classification to a cascade theorem.  It is a
    descriptive organizing principle for the existing observables,
    with predictive content for new observables in unfilled m-k slots.
  - Unify the layer-dependent open-line and layer-independent closed-
    loop primitive structures.  The asymmetry is real and reflects
    that open-line cascade modes carry SOURCE structure (alpha at
    a source layer) while closed-loop modes carry TOPOLOGICAL
    structure (Gamma(1/2) per leg, layer-independent).
"""

from __future__ import annotations

import math
import sys
from typing import NamedTuple


# ---------------------------------------------------------------------------
# Cascade primitives
# ---------------------------------------------------------------------------

def Gamma_half() -> float:
    return math.sqrt(math.pi)


def chi() -> float:
    return 2.0


def alpha_cascade(d: int) -> float:
    R = math.exp(math.lgamma((d+1)/2) - math.lgamma((d+2)/2))
    return R**2 / 4


# ---------------------------------------------------------------------------
# Cascade observable classification by m - k
# ---------------------------------------------------------------------------

class CascadeObservable(NamedTuple):
    name: str
    primitive_form: str
    k_open: int      # number of open-line definite-chirality modes
    m_closed: int    # number of closed loops
    chi_exponent: int  # m - k (signed)
    cascade_value: str
    observed_match: str
    family: str


def cascade_observables() -> list[CascadeObservable]:
    """All cascade observables in the alpha(d*)/chi^k family + 1/alpha_em screening."""
    obs = []
    # Open-line family (Part IVb Remark 4.6)
    obs.append(CascadeObservable(
        name="alpha_s(M_Z)",
        primitive_form="+alpha(14)/chi^1",
        k_open=1, m_closed=0, chi_exponent=-1,
        cascade_value="0.117917",
        observed_match="+0.02 sigma",
        family="open-line (k=1)",
    ))
    obs.append(CascadeObservable(
        name="m_tau / m_mu",
        primitive_form="+alpha(14)/chi^1",
        k_open=1, m_closed=0, chi_exponent=-1,
        cascade_value="16.81731",
        observed_match="+0.24 sigma",
        family="open-line (k=1)",
    ))
    obs.append(CascadeObservable(
        name="m_tau (absolute)",
        primitive_form="+alpha(19)/chi^1",
        k_open=1, m_closed=0, chi_exponent=-1,
        cascade_value="1776.82 MeV",
        observed_match="-0.31 sigma",
        family="open-line (k=1)",
    ))
    obs.append(CascadeObservable(
        name="ell_A",
        primitive_form="+alpha(19)/chi^1",
        k_open=1, m_closed=0, chi_exponent=-1,
        cascade_value="301.44",
        observed_match="-0.16 sigma",
        family="open-line (k=1)",
    ))
    obs.append(CascadeObservable(
        name="theta_C (Cabibbo)",
        primitive_form="-alpha(7)/chi^2",
        k_open=2, m_closed=0, chi_exponent=-2,
        cascade_value="13.04 deg",
        observed_match="+0.03 sigma",
        family="open-line (k=2)",
    ))
    obs.append(CascadeObservable(
        name="sin^2 theta_W",
        primitive_form="+alpha(5)/chi^3",
        k_open=3, m_closed=0, chi_exponent=-3,
        cascade_value="0.231226",
        observed_match="+0.40 sigma",
        family="open-line (k=3)",
    ))
    obs.append(CascadeObservable(
        name="Omega_m (Bott)",
        primitive_form="-alpha(5)/chi^3",
        k_open=3, m_closed=0, chi_exponent=-3,
        cascade_value="0.31474",
        observed_match="-0.04 sigma",
        family="open-line (k=3)",
    ))
    obs.append(CascadeObservable(
        name="b/s",
        primitive_form="-alpha(7)/chi^4",
        k_open=4, m_closed=0, chi_exponent=-4,
        cascade_value="44.7436",
        observed_match="0.014 %",
        family="open-line (k=4)",
    ))
    # Closed-loop family (1/alpha_em screening)
    obs.append(CascadeObservable(
        name="1/alpha_em (screening)",
        primitive_form="+chi^1 * Gamma(1/2)^2 (per layer) x 3 gen",
        k_open=0, m_closed=1, chi_exponent=+1,
        cascade_value="137.030",
        observed_match="-0.005 %",
        family="closed-loop (n=2)",
    ))
    return obs


# ---------------------------------------------------------------------------
# Step 1: chirality selection rule
# ---------------------------------------------------------------------------

def report_selection_rule():
    print("=" * 78)
    print("STEP 1: chirality selection rule chi^(m - k)")
    print("=" * 78)
    print()
    print("OPEN-LINE THEOREM (Part IVb thm:chirality-factorisation, EXISTING):")
    print("  Observable with k independent definite-chirality propagator modes")
    print("  has Green's function G_Q = G / chi^k.  Each open-line mode")
    print("  contributes 1/chi (chirality SELECTION).")
    print()
    print("CLOSED-LOOP DUAL (CONJECTURED, cascade_alpha_em_screening.py):")
    print("  Observable with m closed loops has topological invariant")
    print("  proportional to chi^m * Gamma(1/2)^(legs in loops).  Each closed")
    print("  loop contributes chi (chirality MULTIPLICITY).")
    print()
    print("MIXED CHIRALITY SELECTION RULE:")
    print("  Observable with k open-line modes AND m closed loops has")
    print("  chirality factor:")
    print()
    print("      chi^(m - k)")
    print()
    print("  Three regimes by sign of (m - k):")
    print()
    print(f"    m - k > 0:  closed-dominated  (more loops than open modes)")
    print(f"                chirality factor > 1, MULTIPLICITY dominates.")
    print()
    print(f"    m - k = 0:  balanced  (open and closed cancel)")
    print(f"                chirality factor = 1, no chi-enhancement.")
    print()
    print(f"    m - k < 0:  open-dominated  (more open modes than loops)")
    print(f"                chirality factor < 1, SELECTION dominates.")
    print()


# ---------------------------------------------------------------------------
# Step 2: tabulate existing cascade observables by m - k
# ---------------------------------------------------------------------------

def report_observables_by_chi():
    print("=" * 78)
    print("STEP 2: cascade observables tabulated by m - k")
    print("=" * 78)
    print()
    print("All currently-closed cascade precision predictions:")
    print()
    obs = cascade_observables()
    # Sort by m - k ascending
    obs_sorted = sorted(obs, key=lambda x: x.chi_exponent)
    print(f"  {'observable':<22s}  {'m-k':>4s}  {'k_open':>6s}  {'m_closed':>8s}  {'family':<22s}  {'match':<14s}")
    print("  " + "-" * 92)
    for o in obs_sorted:
        print(f"  {o.name:<22s}  {o.chi_exponent:>+4d}  {o.k_open:>6d}  {o.m_closed:>8d}  {o.family:<22s}  {o.observed_match:<14s}")
    print()
    print("CHIRALITY SPECTRUM (by m - k):")
    print()
    counts = {}
    for o in obs_sorted:
        counts[o.chi_exponent] = counts.get(o.chi_exponent, 0) + 1
    print(f"  {'m - k':>5s}  {'count':>5s}  {'examples':<40s}")
    print("  " + "-" * 55)
    for mk in sorted(counts.keys()):
        examples = ", ".join(o.name for o in obs_sorted if o.chi_exponent == mk)
        print(f"  {mk:>+5d}  {counts[mk]:>5d}  {examples:<40s}")
    print()
    print("Spectrum spans m - k = -4 to +1 in current observables.")
    print("Missing: m - k = 0 (balanced).")
    print("Missing: m - k > +1 (multi-closed-loop, e.g., n=4 4-leg observables).")
    print()


# ---------------------------------------------------------------------------
# Step 3: structural asymmetry between open-line and closed-loop
# ---------------------------------------------------------------------------

def report_structural_asymmetry():
    print("=" * 78)
    print("STEP 3: STRUCTURAL ASYMMETRY between open-line and closed-loop")
    print("        (the m - k pattern is a chirality selection rule, NOT a")
    print("         full duality of cascade primitives)")
    print("=" * 78)
    print()
    print("My earlier 'nice pattern' framing implied open and closed are clean")
    print("duals.  This is true ONLY for the chirality factor chi^(m-k); the")
    print("PER-LEG primitive structure differs between open and closed:")
    print()
    print("  OPEN-LINE primitive (in alpha(d*)/chi^k family):")
    print("    Source: alpha(d*) at distinguished source layer d*.")
    print("    LAYER-DEPENDENT: alpha(5) ~ 0.091, alpha(7) ~ 0.066,")
    print("                    alpha(14) ~ 0.034, alpha(19) ~ 0.026.")
    print("    Reflects the cascade gauge-coupling structure at the SOURCE layer.")
    print()
    print("  CLOSED-LOOP primitive (in chi * Gamma(1/2)^n family):")
    print("    Per-leg: Gamma(1/2) = sqrt(pi).")
    print("    LAYER-INDEPENDENT: same primitive at every Dirac layer.")
    print("    Reflects the cascade Jacobian (TOPOLOGICAL obstruction).")
    print()
    print("These are different kinds of cascade primitives, not a clean dual:")
    print()
    print(f"  {'role':<20s}  {'open-line':<25s}  {'closed-loop':<25s}")
    print("  " + "-" * 72)
    print(f"  {'chirality':<20s}  {'1/chi per mode (select)':<25s}  {'chi per loop (multiply)':<25s}")
    print(f"  {'per-leg primitive':<20s}  {'alpha(d*) (source)':<25s}  {'Gamma(1/2) (Jacobian)':<25s}")
    print(f"  {'layer dependence':<20s}  {'YES (d-dependent)':<25s}  {'NO (universal)':<25s}")
    print(f"  {'cascade interpretation':<20s}  {'source coupling':<25s}  {'topological obstruction':<25s}")
    print()
    print("CONSEQUENCE FOR MIXED OBSERVABLES:")
    print("A mixed observable would carry BOTH structures:")
    print("  - alpha(d*) per open-line mode (layer-dependent source factor)")
    print("  - Gamma(1/2)^(legs in loops) per closed loop (layer-independent topology)")
    print("  - chi^(m - k) chirality factor")
    print()
    print("  I_Q^cascade = alpha(d*)^? . Gamma(1/2)^(closed legs) . chi^(m-k)")
    print()
    print("The exponent on alpha(d*) for mixed observables is NOT immediately")
    print("clear from the existing examples (which have either pure m=0 or")
    print("pure k=0).  A mixed observable test would resolve whether alpha(d*)")
    print("enters per open mode (suggesting product alpha(d_1*)*alpha(d_2*)*...)")
    print("or via some other structure.")
    print()


# ---------------------------------------------------------------------------
# Step 4: candidate balanced (m - k = 0) observables
# ---------------------------------------------------------------------------

def report_balanced_candidates():
    print("=" * 78)
    print("STEP 4: candidate cascade observables with m - k = 0 (BALANCED)")
    print("=" * 78)
    print()
    print("The chirality factor chi^0 = 1 means open and closed contributions")
    print("cancel chirality-wise.  Candidate cascade observables in this class:")
    print()
    print("  (A) Fermion mass self-energy correction (k=1, m=1):")
    print("      External fermion line (1 definite-chirality mode, k=1)")
    print("      with internal fermion-loop correction (1 closed loop, m=1).")
    print("      Topology: like the QED 1-loop fermion self-energy diagram")
    print("      with internal photon exchange.  In cascade, the internal")
    print("      photon doesn't propagate (per-layer locality on fermion;")
    print("      photon is at gauge layer); structure may be different.")
    print("      Cascade-prediction status: not currently in the cascade.")
    print("      Observable: subleading correction to mass formula.")
    print()
    print("  (B) Vertex correction (g-2) (k=1, m=1):")
    print("      External fermion lines (k=1 since same particle in/out)")
    print("      with internal triangle loop (m=1, n=3 internal legs).")
    print("      Cascade per-Dirac-layer: chi^0 * Gamma(1/2)^3 = pi^(3/2) ~ 5.57.")
    print("      Multiplied by external coupling (gauge alpha) and dimensional")
    print("      kinematic factors.  Could test against (g-2) of charged leptons.")
    print()
    print("  (C) Box diagram for 2->2 fermion scattering (k=2, m=1):")
    print("      Wait: this has m - k = 1 - 2 = -1, NOT balanced.")
    print("      A balanced 2->2 scattering would need k=2 + m=2: two pairs")
    print("      of external fermions + two internal fermion loops.  This is")
    print("      a 2-loop diagram, structurally complex.")
    print()
    print("  (D) Mass-loop correction (1-loop wave function renormalisation, k=1, m=1):")
    print("      External fermion (k=1) + internal closed loop on the propagator")
    print("      (m=1).  Cascade prediction: subleading mass correction with")
    print("      no chirality enhancement, magnitude pi^(3/2)/normalisation.")
    print()
    print("MOST TRACTABLE CANDIDATE: (B) or (D) -- 1-loop self-energy or vertex")
    print("corrections to fermion masses or anomalous moments.  These are")
    print("k=1, m=1 (m - k = 0, balanced) with the cascade primitive contributing")
    print("a sub-leading correction.")
    print()
    print("Could the m_mu/m_e residual at +0.13% (Part IVb oq:mu-e-residual,")
    print("currently a 'novel unresolved discrepancy') be a balanced m - k = 0")
    print("self-energy correction?  Numerical scale check:")
    print()
    target_residual = 0.0013  # 0.13% in m_mu/m_e
    cascade_balanced_n3 = math.pi**(3/2)  # Gamma(1/2)^3
    cascade_balanced_n2 = math.pi  # Gamma(1/2)^2
    print(f"  m_mu/m_e residual:           {target_residual:.4f}")
    print(f"  Balanced n=2 primitive (pi):       {cascade_balanced_n2:.4f}")
    print(f"  Balanced n=3 primitive (pi^(3/2)): {cascade_balanced_n3:.4f}")
    print(f"  Ratio (target/n=3):                {target_residual/cascade_balanced_n3:.6f}")
    print()
    print("The bare cascade primitives are MUCH LARGER than the observed")
    print("residual (factor 4000+ off).  So the m_mu/m_e residual cannot be")
    print("a bare m - k = 0 cascade primitive contribution -- it would need a")
    print("normalisation factor in the observable's formula.  In QFT, sub-")
    print("leading corrections enter as alpha/(4*pi) ~ 6e-4, which would")
    print("multiply the cascade primitive: pi^(3/2) * (alpha/(4*pi)) ~ 0.0035")
    print("-- not quite right but closer.  Whether the cascade has a natural")
    print("normalisation factor that brings the m - k = 0 primitive into the")
    print("sub-percent range for fermion mass corrections is open.")
    print()


# ---------------------------------------------------------------------------
# Step 5: what the m-k organization unlocks
# ---------------------------------------------------------------------------

def report_implications():
    print("=" * 78)
    print("STEP 5: what the m - k organization unlocks (and what it doesn't)")
    print("=" * 78)
    print()
    print("UNLOCKS:")
    print()
    print("  1. UNIFIED CHIRALITY CLASSIFICATION.  All cascade precision")
    print("     predictions sit on a single integer axis m - k spanning")
    print("     -4 to +1.  Both open-line and closed-loop families are")
    print("     special cases (m=0 and k=0, respectively).")
    print()
    print("  2. STRUCTURAL PREDICTION FOR NEW OBSERVABLES.  Mixed observables")
    print("     with specific m - k values inherit the chirality factor from")
    print("     the rule, narrowing the cascade prediction space.  Balanced")
    print("     m - k = 0 case is the most natural next research target.")
    print()
    print("  3. SHARP CONSTRAINT ON LAYER DEPENDENCE.  The data forces the")
    print("     closed-loop primitive to be LAYER-INDEPENDENT (Gamma(1/2)),")
    print("     while the open-line primitive is LAYER-DEPENDENT (alpha(d*)).")
    print("     For mixed observables, both structures appear simultaneously;")
    print("     the chirality factor chi^(m-k) is the only piece common to")
    print("     both.")
    print()
    print("  4. NEGATIVE PREDICTIONS.  The cascade has a predicted SPECTRUM")
    print("     of m-k slots; observables that don't fit any slot are anomalous")
    print("     and signal genuinely new structure.  Currently every closed")
    print("     observable has m=1 (single closed loop); m >= 2 observables")
    print("     would require multi-loop topologies.")
    print()
    print("DOES NOT UNLOCK:")
    print()
    print("  1. UNIFIED PER-LEG PRIMITIVE.  The open-line alpha(d*) and")
    print("     closed-loop Gamma(1/2) are DIFFERENT KINDS of cascade")
    print("     primitives (source vs. topological).  The m - k rule is a")
    print("     selection rule for the chirality structure, not a unification")
    print("     of all primitives under one umbrella.")
    print()
    print("  2. NORMALISATION.  The m - k rule fixes the chirality factor")
    print("     chi^(m-k); it does NOT fix the absolute magnitude of mixed-")
    print("     observable contributions.  The per-leg structure (alpha(d*) vs.")
    print("     Gamma(1/2)^n) and the kinematic normalisation enter on top.")
    print()
    print("  3. THEOREM STATUS.  The m - k rule is currently a descriptive")
    print("     organizing principle, not a derived cascade theorem.  Promoting")
    print("     it to theorem status requires proving that the open-line and")
    print("     closed-loop chirality factors COMPOSE multiplicatively (i.e.,")
    print("     no cross-terms that violate chi^(m-k)).  This is plausible")
    print("     given the chirality basins are orthogonal (S^+ and S^- have")
    print("     zero overlap), but not yet shown.")
    print()


def main() -> int:
    print("=" * 78)
    print("CASCADE OPEN-CLOSED MIXED OBSERVABLES")
    print("Chirality selection rule chi^(m-k) and what it organizes")
    print("=" * 78)
    print()
    report_selection_rule()
    report_observables_by_chi()
    report_structural_asymmetry()
    report_balanced_candidates()
    report_implications()
    return 0


if __name__ == "__main__":
    sys.exit(main())
