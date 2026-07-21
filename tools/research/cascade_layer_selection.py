#!/usr/bin/env python3
"""
THE LAYER QUESTION (Addendum 87): what selects d = 12 -- the
complement of Door 3.  Category (a): a source-reading result
(Check 1, quotes below) plus machine-gated arithmetic; no data, no
closures, no number changes; every attribution graded.

THE QUESTION.  Door 3 (A83/A85) decomposed what the COUNT
rho(12)-1 = 3 load-bears on.  The honest negative's other half is
the LAYER: what selects d = 12?  If the selection introduced a new
unlisted assumption, the N_c dependency map would grow; if it
decomposes into already-named components, the map completes.

THE SOURCES, READ DIRECTLY (Check 1; quotes verbatim, Check 2).
Part IVa:
  - line 50:  "The Clifford algebra Cl(1,d-1) has complex minimal
    spinors when d mod 8 in {4,5,6}."  (The papers' Clifford
    input; classical spinor-type bookkeeping.  Its PERIOD is 8 --
    the Clifford/Bott Z/8.)
  - lines 157-158:  "The second window {12,13,14} is the Bott
    mirror of the spacetime window {4,5,6}.  It reproduces the
    same Weyl-Dirac-Weyl pattern exactly, shifted by one Bott
    period."
  - lines 56-57:  "d = 12 is the unique dimension in [5, d_1 = 19]
    where rho(d)-1 = 3, so the gauge window is forced, not
    chosen."  (The range bound d_1 = 19 is Part 0's threshold --
    pure Gamma structure -- with d_0 = 7; Part 0 Thm 6.7 via the
    generator-count remark.)
  - thm:generators:  the equality 12 = d_1 - d_0 = 8 + 3 + 1 is,
    in the papers' OWN grading, "a numerical consistency check ...
    not a structural identity forced by either derivation alone";
    likewise rank 4 = observer d: "The cascade does not
    independently derive that the gauge window's total Lie-algebra
    rank must equal the observer's spacetime dimension."

THE DECOMPOSITION (gated below).  The selection of d = 12 is the
composite of FOUR already-named components:
  (1) the mod-8 complex-spinor classification (classical Clifford;
      period = the SAME Z/8 as Radon-Hurwitz/Bott/BW(R), whose
      two-place Witt-Weil arithmetic home is Theorems 1f-1g);
  (2) the spacetime anchor d = 4 (the observer window {4,5,6}) --
      the papers' Lovelock-cap-Clifford selection, ALREADY residue
      item 1 + the hypothesis C1 in this paper's seven-item count;
  (3) Part 0's Gamma thresholds d_0 = 7, d_1 = 19 -- pure Gamma
      structure, i.e. the territory this paper's Theorem 1/1b
      grounds (the tower as the log-geometry of xi's real factor);
  (4) the within-window factor assignment by the vector-field
      count -- Door 3's decomposed content (Clifford construction
      + classical mod-2 upper bounds).
STRUCTURE: the gauge window is 12 = 4 + 8 -- the observer anchor
plus one Clifford period -- with the window's position
OVER-DETERMINED: the mirror (+8 from spacetime) and the
rho-uniqueness scan (the only rho-1 = 3 in [5, d_1]) select the
same d = 12 independently, and the threshold d_1 = 19 excludes the
third window ({20,21,22} lies wholly beyond it).

THE FINDING (the map completes).  The layer selection introduces
NO new unlisted dependency: every component is either (a) in the
paper's declared seven-item residue (Lovelock, the hypothesis),
(b) the classical Z/8 the arithmetic chain grounded (1f-1g), (c)
Part 0's Gamma structure (Theorem 1/1b territory), or (d) Door 3's
decomposed count.  After both doors, the full N_c dependency reads:
  N_c = [Clifford construction + classical mod-2 upper bounds]
        at [observer anchor + one Clifford Z/8 period, confirmed
        by rho-uniqueness within Gamma-thresholds].
The papers' own coincidence-grading (12 = 12; rank 4 = d) is
respected and machine-checked as arithmetic while confirmed
NON-load-bearing in the chain above (the papers themselves say
so; Check 4: their self-report, not a novel finding).

WHAT THIS DOES NOT DO: derive the layer from finite places (the
mirror's 8 has an arithmetic HOME (1f-1g), which is not a
finite-place DERIVATION of the selection -- the anchor d = 4 and
the thresholds are archimedean/geometric inputs); change any
number; alter the residue count.  No data, no closures, no RH/GRH,
no semiclassics.
"""


def rho(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    a, b = divmod(v, 4)
    return 8 * a + 2 ** b


def main():
    print("=" * 74)
    print("THE LAYER QUESTION: what selects d = 12")
    print("=" * 74)

    d0, d1 = 7, 19          # Part 0's thresholds (Gamma structure; cited)
    obs_window = [4, 5, 6]  # the papers' spacetime window (anchor d = 4)

    # G1: the mod-8 complex-window arithmetic
    win = [d for d in range(4, 23) if d % 8 in (4, 5, 6)]
    g1 = (win == [4, 5, 6, 12, 13, 14, 20, 21, 22]
          and [d + 8 for d in obs_window] == [12, 13, 14]
          and [d + 16 for d in obs_window] == [20, 21, 22])
    print()
    print(f"G1 complex windows in [4,22] = {win}")
    print(f"   second = first + 8; third = first + 16   "
          f"{'PASS' if g1 else 'FAIL'}   (the mirror IS the mod-8"
          " period: one Clifford/Bott Z/8 shift)")

    # G2: threshold exclusion -- exactly one complete window in (d0, d1]
    windows = [[4, 5, 6], [12, 13, 14], [20, 21, 22]]
    inside = [w for w in windows if all(d0 < d <= d1 for d in w)]
    g2 = inside == [[12, 13, 14]]
    print(f"G2 complete windows inside (d_0, d_1] = ({d0}, {d1}]:"
          f" {inside}   {'PASS' if g2 else 'FAIL'}")
    print("   ({20,21,22} lies wholly beyond d_1 = 19; the spacetime")
    print("   window sits at/below d_0 = 7)")

    # G3: over-determination -- the rho-uniqueness scan agrees
    rho3 = [d for d in range(5, d1 + 1) if rho(d) - 1 == 3]
    g3 = rho3 == [12] and 12 in windows[1]
    print(f"G3 {{d in [5,{d1}] : rho(d)-1 = 3}} = {rho3}; 12 in the"
          f" mirror window   {'PASS' if g3 else 'FAIL'}")
    print("   => two independent selectors (mirror shift; rho-unique-")
    print("      ness) pick the SAME layer: d = 12 is over-determined")

    # G4: the three 8s are one 8 (arithmetic side)
    g4 = all(rho(2 ** (v + 4) * m) - rho(2 ** v * m) == 8
             for v in range(4) for m in (1, 3, 5))
    print(f"G4 Radon-Hurwitz period = 8 = the window period   "
          f"{'PASS' if g4 else 'FAIL'}   (both are the Clifford/Bott")
    print("   Z/8 = BW(R), cited classical -- the object whose two-place")
    print("   Witt-Weil home is Theorems 1f-1g)")

    # G5: the papers' self-graded coincidences, checked as arithmetic
    g5 = (d1 - d0 == 8 + 3 + 1) and (2 + 1 + 1 == 4)
    print(f"G5 coincidence arithmetic: d_1 - d_0 = {d1-d0} = 8+3+1;"
          f" rank 2+1+1 = 4   {'PASS' if g5 else 'FAIL'}")
    print("   (held apart per the papers' OWN grading: 'a numerical")
    print("   consistency check ... not a structural identity'; neither")
    print("   is load-bearing in the selection chain above)")

    print()
    print("=" * 74)
    print("READING (source-reading result + gated arithmetic)")
    print("=" * 74)
    print("  The layer selection introduces NO new unlisted dependency:")
    print("  d = 12 = (observer anchor 4) + (one Clifford Z/8 period),")
    print("  over-determined by rho-uniqueness within Part 0's Gamma")
    print("  thresholds.  Every component is already named: the anchor's")
    print("  residue (Lovelock + hypothesis, items in the seven-item")
    print("  count), the classical Z/8 (arithmetically homed, 1f-1g),")
    print("  the Gamma thresholds (Theorem 1/1b territory), and Door 3's")
    print("  decomposed count.  The N_c dependency map is COMPLETE.")
    print("  Not a finite-place derivation of the selection; no number")
    print("  changes; no data, no closures.")


if __name__ == "__main__":
    main()
