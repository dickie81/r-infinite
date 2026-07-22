#!/usr/bin/env python3
"""THE LATTICE SELECTION (Theorem 1k): the feature->layer map
re-read on the integer lattice -- member one of the
selection-convention class RE-MOTIVATED given the site-E pairing.
Category (a): classical Gamma-function facts, machine-gated; no
data, no closures, no RH/GRH, no semiclassics (Check 7); the
hypothesis is nowhere an input (Check 8 -- see GRADING for
exactly where the anchored pairing enters).

CONTEXT.  Review 2 (the Finding-6 defeat) charged the
feature->integer-layer selection as a convention -- the first
member of the selection-convention residue class: no uniform
ROUNDING rule produces {5, 7, 19, 217} from the feature set
(floor-in-s for the critical pair, floor-in-d for the
thresholds), and part0 concedes 'No rounding convention selects
a canonical integer uniformly across the three boundaries'
(part0.tex, the sentence before its variational theorem).  The
charge is true in the rounding frame.  This file gates the
LATTICE frame, in which no continuum position is rounded at all
-- the frame part0's own regime partition and variational
theorem already occupy (both in part0 since 2026-05, predating
the riemann paper): every distinguished layer is an extremal
member of an integer set defined by the feature inequalities
themselves.

THE LATTICE FACTS (K1-K4).  Under the canonical window-potential
pairing p(d) := P(d+1) (the d<->s audit's site E, the
data-anchored convention), p is strictly increasing on the
lattice, and the threshold bands
  B1 = {d : 0 < p(d) < ln Gamma(1/2)}          = {7, ..., 19}
  B2 = {d : ln Gamma(1/2) < p(d) < Gamma(1/2)} = {20, ..., 217}
are exact integer intervals.  No lattice point lies within
8.5e-4 of a threshold, so all four half-open interval
conventions produce the same integer sets -- the boundary
convention is immaterial.  V(d) has the strict discrete argmax
5.  Hence
  {argmax_Z V, min B1, max B1, max B2} = {5, 7, 19, 217}
with min B2 = max B1 + 1 (tiling: the band structure carries
exactly four independent integers), and ZERO rounding anywhere.

THE CONCORDANCE (K5-K6).  The paper's Theorem-7 s-space features
are the same objects: the critical pair 5.2569/7.2569 is ONE
equation psi(x) = ln pi read at two argument offsets (the
V-argmax at d = 5.2569, factor Gamma_R(d+2); the p-zero at
d = 6.2569, s = 7.2569) -- gated as the same root; the
s-thresholds 20.73, 218.63 are the d-crossings + 1.  Part0's
variational labels (the sup of the invariant's bilinear form
over the eight boundary labelings, unique at (7,19,217)) agree
gate-by-gate: at the two upper boundaries identically, because
d(log Omega_d)/dd = -p(d) (part0's own identity: 'the first
derivative of the log-area, which is -p(d)') makes Omega
decreasing exactly where p > 0, so the variational extremum IS
the band-sign fact; at the first boundary the two principles are
distinct and agree numerically (Omega_7 < Omega_6, margin
~1.9%).

GRADING (honest, per Check 8; the round-57 adjudication grammar
applied in advance).  GIVEN the site-E pairing -- an anchored
convention that PERSISTS in the residue; under the alternative
pairing p(d) = P(d) the whole structure shifts coherently to
{5, 8, 20, 218} (gated, K4) -- the feature->layer assignment is
lattice-entailed with zero further freedom.  Member one of the
selection-convention class is RE-MOTIVATED, not deleted: its
content is absorbed into the pairing member (the assignment was
never an independent choice; it is the pairing choice, seen
once), exactly as the third member was re-motivated by Theorem
1j.  Three members and the seven-item residue count stand.
Finding 6 (feature-list completeness) stays REOPENED: this file
reads the LISTED features on the lattice; it does not prove the
list complete.  No number changes; no closure.
"""

import math

from scipy.optimize import brentq
from scipy.special import digamma, gammaln

PI = math.pi
LNPI = math.log(PI)
C1 = 0.5 * LNPI                 # ln Gamma(1/2)
C2 = math.sqrt(PI)              # Gamma(1/2)


def P(s):
    return 0.5 * digamma(s / 2.0) - 0.5 * LNPI


def p(d):
    return P(d + 1)


def V(d):
    return math.exp(d / 2 * LNPI - gammaln(d / 2 + 1))


def Om(d):
    return 2 * math.exp((d + 1) / 2 * LNPI - gammaln((d + 1) / 2))


def bands(pot, lo_strict, hi_strict):
    """Integer bands of pot vs thresholds under a chosen convention."""
    lt = (lambda a, b: a < b) if hi_strict else (lambda a, b: a <= b)
    gt = (lambda a, b: a > b) if lo_strict else (lambda a, b: a >= b)
    b1 = [d for d in range(1, 400) if gt(pot(d), 0) and lt(pot(d), C1)]
    b2 = [d for d in range(1, 400) if gt(pot(d), C1) and lt(pot(d), C2)]
    return b1, b2


def main():
    print("=" * 74)
    print("THE LATTICE SELECTION (Theorem 1k)")
    print("=" * 74)

    # ---- K1: the bands, exact and boundary-convention-free
    print()
    print("K1 threshold bands on the lattice (canonical pairing p = P(d+1)):")
    B1, B2 = bands(p, True, True)
    same = all(bands(p, ls, hs) == (B1, B2)
               for ls in (True, False) for hs in (True, False))
    margin = min(min(abs(p(d) - t) for t in (0.0, C1, C2))
                 for d in range(1, 400))
    ok1 = (B1 == list(range(7, 20)) and B2 == list(range(20, 218))
           and same and margin > 5e-4)
    print(f"   B1 = {{7..19}} ({len(B1)} layers), B2 = {{20..217}}"
          f" ({len(B2)} layers); all four interval conventions agree;")
    print(f"   min lattice-to-threshold distance = {margin:.2e} > 5e-4   "
          f"{'PASS' if ok1 else 'FAIL'}")

    # ---- K2: the discrete argmax of V, with unimodality
    print()
    print("K2 V(d) strict discrete argmax (ratio method):")
    r = lambda d: V(d + 1) / V(d)
    ok2 = V(4) < V(5) > V(6)
    ok2 &= max(range(101), key=V) == 5
    ok2 &= all(r(d + 1) < r(d) for d in range(0, 200))   # ratio strictly dec
    ok2 &= r(4) > 1 > r(5)   # => V rises to 5, falls forever after (tail
    #                          by the gated decreasing ratio; R dec., classical)
    print(f"   V(4,5,6) = {V(4):.4f}, {V(5):.4f}, {V(6):.4f}; argmax = 5;"
          f" ratio r(4) = {r(4):.4f} > 1 > r(5) = {r(5):.4f},")
    print(f"   r strictly decreasing on [0,200]   {'PASS' if ok2 else 'FAIL'}")

    # ---- K3: lattice monotonicity (bands are intervals)
    print()
    print("K3 p strictly increasing on the lattice (bands = intervals):")
    ok3 = all(p(d + 1) > p(d) for d in range(1, 400))
    ok3 &= p(400) > C2            # beyond the scan: monotone, above C2
    ok3 &= B1 == list(range(min(B1), max(B1) + 1))
    ok3 &= B2 == list(range(min(B2), max(B2) + 1))
    print(f"   p(d+1) > p(d) on [1,400]; p(400) = {p(400):.4f} > Gamma(1/2);"
          f" both bands contiguous   {'PASS' if ok3 else 'FAIL'}")
    print("   (tail: p' = psi'((d+1)/2)/4 > 0 everywhere -- trigamma,")
    print("   classical; the [1,400] gate covers every band claim)")

    # ---- K4: the four layers, the tiling, and the pairing conditionality
    print()
    print("K4 the selection, and its site-E conditionality:")
    sel = sorted({5, min(B1), max(B1), max(B2)})
    A1, A2 = bands(P, True, True)                 # alternative pairing P(d)
    alt = sorted({5, min(A1), max(A1), max(A2)})
    ok4 = (sel == [5, 7, 19, 217] and min(B2) == max(B1) + 1
           and alt == [5, 8, 20, 218])
    print(f"   {{argmax V, min B1, max B1, max B2}} = {sel};"
          f" min B2 = max B1 + 1 (tiling);")
    print(f"   alternative pairing p = P(d) gives {alt} -- the entailment"
          f" is conditional")
    print(f"   on the site-E anchored pairing, which persists   "
          f"{'PASS' if ok4 else 'FAIL'}")

    # ---- K5: the s/d concordance; the critical pair is one equation
    print()
    print("K5 concordance with the paper's Theorem-7 s-space features:")
    x0 = brentq(lambda x: P(x), 3.0, 12.0)          # psi(x/2) = ln pi
    dv = brentq(lambda d: P(d + 2), 3.0, 12.0)      # V-argmax equation
    d0s = brentq(lambda d: p(d), 3.0, 12.0)
    d1s = brentq(lambda d: p(d) - C1, 12.0, 30.0)
    d2s = brentq(lambda d: p(d) - C2, 100.0, 400.0)
    ok5 = abs(dv - (x0 - 2)) < 1e-9                 # same root, offset 2
    ok5 &= abs(d0s - (x0 - 1)) < 1e-9               # p-zero = same root, s=x0
    ok5 &= abs(dv - 5.2569) < 5e-4 and abs(d0s - 6.2569) < 5e-4
    ok5 &= abs((d1s + 1) - 20.7308) < 5e-4 and abs((d2s + 1) - 218.6267) < 5e-4
    print(f"   psi(x/2) = ln pi root x = {x0:.4f}: V-argmax d = {dv:.4f}"
          f" = x-2; p-zero d = {d0s:.4f} = x-1;")
    print(f"   s-thresholds {d1s+1:.4f}, {d2s+1:.4f} = d-crossings + 1"
          f"   {'PASS' if ok5 else 'FAIL'}")
    print("   (the 'critical pair 2 apart' is ONE equation at two argument")
    print("   offsets: the mixed-rounding appearance was the s = d+1 frame")
    print("   line crossing one lattice rule)")

    # ---- K6: concordance with part0's variational labels
    print()
    print("K6 part0's variational selection reproduced, and explained:")
    ok6 = Om(7) < Om(6) and Om(19) > Om(20) and Om(217) > Om(218)
    # the identity d log Om / dd = -p(d) is definitional algebra
    # (log Om = ln 2 + (d+1)/2 ln pi - ln Gamma((d+1)/2); differentiate)
    # -- an exhibit, declared; the FAILABLE content is the three sign
    # comparisons above and the band-sign equivalence below:
    ok6 &= p(19) > 0 and p(20) > 0 and p(217) > 0 and p(218) > 0
    #        ^ Omega strictly decreasing at both upper boundaries, so the
    #          variational pick = the band pick IDENTICALLY there
    print(f"   min(Om6,Om7) = Om7 ({Om(7):.4f} < {Om(6):.4f}, margin"
          f" {Om(6)/Om(7)-1:+.1%}); max(Om19,Om20) = Om19;")
    print(f"   max(Om217,Om218) = Om217; p > 0 at 19,20,217,218 (Omega")
    print(f"   decreasing there: variational = band, identically; identity")
    print(f"   d log Om/dd = -p is definitional -- declared exhibit)   "
          f"{'PASS' if ok6 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  No continuum crossing is rounded anywhere: the four")
    print("  distinguished layers are the discrete argmax of V and the")
    print("  three independent band extrema of the lattice sequence p(d),")
    print("  boundary-convention-free (no lattice point near a threshold).")
    print("  Part0's variational labels and regime partition say the same")
    print("  thing in the invariant's frame.  GIVEN the site-E pairing")
    print("  (anchored, persists in the residue; the alternative shifts")
    print("  the set to {5,8,20,218}), the assignment is lattice-entailed")
    print("  with zero further freedom.  Member one re-motivated -- the")
    print("  assignment is the pairing choice, seen once.  Three members;")
    print("  seven-item residue count unchanged; Finding 6 stays open.")


if __name__ == "__main__":
    main()
