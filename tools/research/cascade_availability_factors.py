#!/usr/bin/env python3
"""THE AVAILABILITY FACTORS' ARITHMETIC HOMES (Theorem 1m): mass
layer 3 attacked at the factor level.  Category (a): exact
Gamma/lattice identities plus reproductions of committed-instrument
records; no data (the papers' own stated values are cited as
record), no closures, no RH/GRH, no semiclassics (Check 7); the
hypothesis is nowhere an input (Check 8 -- see GRADING).

CONTEXT.  The U2 availability triple (obstruction, colour,
projection) is computed by clauses R1-R3 from leg data
(cascade_u2_function.py, 11/11 vs the corrected key), but the
clauses are STIPULATIONS, the first-principles groundings are
graded arguments/identifications only, and the 13b exhaustion's
availability block has SIX survivors -- R1: canonical (|dg|/8) +
periods-spanned-minus-1 + the cross-generation indicator; R2:
canonical alone; R3: canonical + matter-kinds-minus-1 = 3*1*2 --
with the indicator a GENUINE fork discriminated only by the
off-domain probe P1 (legs 5 & 21), graded 'asserted, and the
data cannot distinguish' (cascade_u2_first_principles.py).  This
file attacks the FACTOR level: each availability factor is an
already-derived, already-gated object of the framework, and the
identifications carry consequences for the fork.

THE THREE IDENTIFICATIONS (the new registrations):
  obstruction unit  2*sqrt(pi) = chi * Gamma(1/2), chi = 2 =
    |mu(R)| -- EXACTLY T2's graded-crossing normalisation
    (1/(chi*Gamma(1/2)) per graded crossing, the arithmetic side)
    and EXACTLY part4b's per-Dirac-layer topological toll (the
    geometric side: 'The topological obstruction factor is
    2 sqrt(pi) = 2 Gamma(1/2) per Dirac layer: 2 from chirality
    (chi(S^2n) = 2) and sqrt(pi) = Gamma(1/2) from the ...
    quarter-turn constant', part4b:48; per-layer attachment
    'Each obstruction attenuates the projection by 2 sqrt(pi),
    giving (2 sqrt(pi))^(-n_D)', part4b:92; the d-independent
    propagator ratio Z_f/Z_s = (R/2)/(sqrt(pi) R) = 1/(2 sqrt(pi)),
    part4b:99/155).
  projection factor cos(pi/6) = sqrt(3)/2 = covol(Z[omega]) --
    the colour ring's covolume, ALREADY identified at Door 4
    (the paper: 'covolume sqrt(3)/2 = sqrt(|d_K|)/2'; in the
    source the adjacent 'whose inverse' clause attaches to the
    DIFFERENT ideal frak-d, whose inverse is the trace-dual
    30-degree lattice of Theorem 11 -- round-67 F5 corrected an
    excerpt that shifted that antecedent to the covolume); NEW
    here: the census minimality -- covol = sqrt(|d|)/2 is minimal
    over ALL 3043 fundamental imaginary quadratic discs at
    d = -3 (the 1j census reused), so the projection factor is
    the minimal covolume among such maximal orders --
    equivalently the densest, since every imaginary-quadratic
    maximal order has shortest vector exactly 1, making packing
    density proportional to 1/covol (premise stated per
    round-67 F6).
  colour factor e^(r/2), r = 2 -- GRADING UNCHANGED: the 2 is a
    choice among coincident 2s ([Q(zeta_3):Q] = 2 = su(3) Cartan
    rank; 13c), with the 1j-census anchor that the mu_6 field is
    degree-2 qua imaginary quadratic; e^(2/2) = e is the papers'
    own Tier-4a statement 'm_b/m_tau = e' (record, not data).

THE FORK CONSEQUENCE (V2).  R1's count |dg|/8 equals the number
of Dirac layers (d = 5 mod 8) in the half-open interval between
the legs -- gated on every generation-coset pair.  On P1's cell
(legs 5 & 21) the count is 2 and the indicator is 1; the
periods-minus-1 variant equals the count on every coset pair
(extensional duplicate, gated).  GIVEN the obstruction-factor
identification, part4b's per-layer attachment forces the COUNT
at P1 -- each Dirac layer crossed costs exactly one factor, so a
two-layer crossing costs (2 sqrt(pi))^2, and the indicator
variant contradicts the per-layer attenuation it would have to
reproduce.  The 13b block's one genuine fork is thereby
DISCRIMINATED ARITHMETICALLY -- conditional on the
identification, not on realizing the off-domain probe; the
surviving variants are then extensionally equal to the canonical
clauses on every reachable input (per the 13b record's own
census, reproduced in the docstring above).  The
first-principles P1 position upgrades from 'asserted, and the
data cannot distinguish' to 'entailed given the factor
identification' -- the 1j/1k/1l grammar, applied to layer 3.

GRADING (honest, per Check 8).  What this file does NOT do: the
clause TRIGGERS (legs, the record-legs classifier, the A13
grading, the ell_A kind, Observer k=3) are soft inputs,
UNTOUCHED; the angle rows stay near-tautological per round 13;
R2's coincident-2s identification stays at 13c's strength; the
identifications themselves are C1-conditional exactly where
their sources are (T2's normalisations; part4b's topological
channel; T11's colour field).  What changes: the three
availability FACTORS are registered as already-derived objects
(none is a new constant), and the availability block's
uniqueness upgrades -- conditional on the identifications -- to
canonical-up-to-extensional-equivalence.  Layer 3's residual gap
after 1m: the trigger data and the identifications'
conditionality.  No number changes; no closure.
"""

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cascade_torsion_selection import fundamental_discs

PI = math.pi
CHI = 2                       # Euler characteristic chi(S^2n) = |mu(R)|
GEN_COSET = (5, 13, 21)       # generation layers, d = 5 mod 8


def dirac_layers(a, b):
    """Dirac layers (d = 5 mod 8) in the half-open interval (a, b]."""
    lo, hi = min(a, b), max(a, b)
    return [d for d in range(lo + 1, hi + 1) if d % 8 == 5]


def main():
    print("=" * 74)
    print("THE AVAILABILITY FACTORS' ARITHMETIC HOMES (Theorem 1m)")
    print("=" * 74)

    # ---- V1: the obstruction unit is T2's graded-crossing normalisation
    print()
    print("V1 the obstruction unit 2*sqrt(pi) = chi * Gamma(1/2):")
    unit = CHI * math.gamma(0.5)
    ok1 = abs(unit - 2 * math.sqrt(PI)) < 1e-15
    # part4b's propagator ratio (R/2)/(sqrt(pi) R) = 1/(2 sqrt(pi)) is
    # algebraically d-independent: R cancels identically, so the conjunct
    # below is an EXHIBIT re-testing the unit identity (round-67 F3 --
    # the earlier comment's "failable via the Gamma route" was wrong;
    # V1's failable content is the chi*Gamma(1/2) = 2 sqrt(pi) identity):
    R = lambda d: math.exp(math.lgamma((d + 1) / 2) - math.lgamma((d + 2) / 2))
    ok1 &= all(abs((R(d) / 2) / (math.sqrt(PI) * R(d)) - 1 / unit) < 1e-15
               for d in (5, 13, 21, 100))
    print(f"   chi*Gamma(1/2) = {unit:.15f} = 2 sqrt(pi); T2's unit is its")
    print(f"   reciprocal (same object -- exhibit); part4b's propagator")
    print(f"   ratio (R/2)/(sqrt(pi) R) = 1/(2 sqrt(pi)) at d = 5,13,21,100")
    print(f"   (d-independence is algebraic -- declared)   "
          f"{'PASS' if ok1 else 'FAIL'}")

    # ---- V2: R1 = Dirac-layer count; the P1 fork cell; the duplicate
    print()
    print("V2 the obstruction rank counts Dirac layers; the P1 fork:")
    pairs = [(5, 13), (13, 21), (5, 21)]
    counts = {p: len(dirac_layers(*p)) for p in pairs}
    r1 = {p: abs(p[1] - p[0]) // 8 for p in pairs}
    spans = {p: len({(d - 1) // 8 for d in range(p[0], p[1] + 1)}) - 1
             for p in pairs}
    indicator = {p: int(p[0] != p[1]) for p in pairs}
    ok2 = all(counts[p] == r1[p] == spans[p] for p in pairs)
    ok2 &= counts[(5, 21)] == 2 and indicator[(5, 21)] == 1
    print(f"   coset pairs: count = R1 = periods-minus-1 = "
          f"{[counts[p] for p in pairs]} on {pairs}")
    print(f"   (periods-minus-1 is an extensional duplicate on the coset);")
    print(f"   P1 cell (5,21): count 2 vs indicator 1 -- given the factor")
    print(f"   identification, part4b's per-layer attachment forces 2: the")
    print(f"   13b block's genuine fork is discriminated arithmetically   "
          f"{'PASS' if ok2 else 'FAIL'}")

    # ---- V3: the projection factor is the colour ring's covolume
    print()
    print("V3 the projection factor cos(pi/6) = covol(Z[omega]):")
    om_im = math.sin(2 * PI / 3)          # Im(omega), basis (1, omega)
    disc = -3                             # disc(x^2 + x + 1)
    ok3 = abs(om_im - math.sqrt(3) / 2) < 1e-15
    ok3 &= abs(math.sqrt(abs(disc)) / 2 - math.sqrt(3) / 2) < 1e-15
    ok3 &= abs(math.cos(PI / 6) - math.sqrt(3) / 2) < 1e-15
    print(f"   |Im omega| = sqrt(|disc|)/2 = cos(pi/6) = "
          f"{math.cos(PI/6):.15f}")
    print(f"   (three routes; Door 4's object -- the 30-degree trace-")
    print(f"   duality lattice, already gated in colour_field_bridge)   "
          f"{'PASS' if ok3 else 'FAIL'}")

    # ---- V4: census minimality (the 1j census reused)
    print()
    print("V4 covol = sqrt(|d|)/2 minimal over all fundamental discs:")
    fund = fundamental_discs(10000)
    covols = {d: math.sqrt(-d) / 2 for d in fund}
    dmin = min(covols, key=covols.get)
    ok4 = len(fund) == 3043 and dmin == -3
    ok4 &= abs(covols[-3] - math.cos(PI / 6)) < 1e-15
    ok4 &= all(covols[d] > covols[-3] for d in fund if d != -3)
    print(f"   {len(fund)} discs; min covol = {covols[-3]:.6f} uniquely at")
    print(f"   d = {dmin} (classical closure: |d| >= 3 for every imaginary")
    print(f"   quadratic fundamental disc, so the scan bound is total) --")
    print(f"   the projection factor is the minimal covolume among such")
    print(f"   rings (= the densest: shortest vector exactly 1, density")
    print(f"   proportional to 1/covol -- premise per round-67 F6)   "
          f"{'PASS' if ok4 else 'FAIL'}")

    # ---- V5: the colour slot (grading unchanged; exhibits declared)
    print()
    print("V5 the colour slot: coincident 2s, grading unchanged (13c):")
    # x^2 + x + 1 irreducible over Q (negative discriminant, no real
    # root): degree [Q(zeta_3):Q] = 2; su(3) Cartan rank 2 is a cited
    # constant (exhibit).  e^(2/2) = e vs the papers' Tier-4a record.
    ok5 = (1 * 1 - 4 * 1 * 1) == disc and disc < 0
    ok5 &= abs(math.exp(2 / 2) - math.e) < 1e-15
    print(f"   disc(x^2+x+1) = {disc} < 0 (irreducible quadratic: degree 2,")
    print(f"   the 1j-census anchor -- the mu_6 field is degree-2 qua")
    print(f"   imaginary quadratic); e^(r/2) at r = 2 is e, the papers'")
    print(f"   Tier-4a 'm_b/m_tau = e' (record, not data); identification")
    print(f"   among coincident 2s unchanged   {'PASS' if ok5 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  None of the three availability factors is a new constant:")
    print("  the obstruction unit is T2's graded-crossing normalisation")
    print("  and part4b's per-Dirac-layer toll (one object, chi*Gamma(1/2)");
    print("  = 2 sqrt(pi)); the projection factor is the colour ring's")
    print("  covolume (Door 4's object), minimal over all 3043 fundamental")
    print("  imaginary-quadratic discs at d = -3; the colour factor's rank")
    print("  stays a coincident-2s identification (13c).  GIVEN the")
    print("  obstruction identification, the per-layer attachment forces")
    print("  the count reading at P1's cell -- the availability block's")
    print("  one genuine fork is discriminated arithmetically, and the")
    print("  block is canonical up to extensional equivalence, conditional")
    print("  on the identification.  The clause triggers and soft inputs")
    print("  are untouched; no number changes; no closure.")


if __name__ == "__main__":
    main()
