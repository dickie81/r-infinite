#!/usr/bin/env python3
"""
THE LAYER QUESTION (Addendum 87; corrected by round 30, Addendum
89): what selects d = 12 -- the complement of Door 3.  Category
(a): a source-reading result plus machine-gated arithmetic; no
data, no closures, no number changes; every attribution graded.

ROUND-30 CORRECTION, STATED FIRST (M1 + M2 of the subagent review,
verified directly by the lead).  The first version of this file
claimed d = 12 was "over-determined: the mirror and the
rho-uniqueness scan select the same layer INDEPENDENTLY", and
attributed the scan's bounds to the thresholds d_0 = 7, d_1 = 19.
Both claims were false:
  (M1) rho(d)-1 = 3  <=>  v_2(d) = 2  <=>  d = 4 mod 8 -- i.e.
       {rho-1 = 3} IS the set of window-START dimensions.  The
       "two selectors" are ONE mod-8 condition; the agreement
       carries no confirmatory content beyond Bott periodicity
       itself.  The companion paper says so four lines above its
       uniqueness theorem (part4a.tex:353-356: "at d = 4, S^3 has
       rho(4)-1 = 3 independent vector fields ... The same
       topological invariant governs both the spacetime structure
       and the gauge structure, applied at the two Bott mirrors").
       rho(4)-1 = 3: the anchor has a rho-twin, now disclosed and
       gated below.
  (M2) the uniqueness scan's range is [5, d_1 = 19]
       (part4a.tex:359: "Among all dimensions 5 <= d <= d_1=19")
       -- LOWER BOUND 5, not d_0 = 7.  The bound is load-bearing:
       over [4, 19] the rho-condition picks {4, 12} and uniqueness
       fails; d = 4 is excluded because the ANCHOR assigns it to
       spacetime, and the tower's layers begin at the first
       distinguished layer d_V = 5.  d_0 = 7 bounds a DIFFERENT
       statement (window-completeness in the inter-threshold band,
       G2 below), which the first version conflated with the scan.

THE SOURCES, READ DIRECTLY (Check 1; quotes verbatim, Check 2;
ranges re-read and re-recorded for this round, including the
uniqueness theorem's body at part4a.tex:358-397 and the rho(4)
caveat at 353-356 -- the round-30 F6 gap).  Part IVa:
  - lines 50-51:  "The Clifford algebra Cl(1,d-1) has complex
    minimal spinors when d mod 8 in {4,5,6}."  (Classical
    spinor-type bookkeeping, cited not verified here; its PERIOD
    is 8 -- the Clifford/Bott Z/8.)
  - lines 157-158:  "The second window {12,13,14} is the Bott
    mirror of the spacetime window {4,5,6}.  It reproduces the
    same Weyl-Dirac-Weyl pattern exactly, shifted by one Bott
    period."
  - lines 56-58 (abstract form; theorem body at 358-360):
    "Furthermore, d = 12 is the unique dimension in [5, d_1 = 19]
    where rho(d)-1 = 3, so the gauge window is forced, not
    chosen."
  - thm:generators (grading sentence at 307-310; remark begins
    293) and the rank remark (~318): the
    papers' OWN grading of 12 = d_1 - d_0 = 8+3+1 ("a numerical
    consistency check ... not a structural identity forced by
    either derivation alone") and rank 4 = observer d ("The
    cascade does not independently derive" it).

THE CORRECTED DECOMPOSITION (gated below).  The selection of
d = 12 is the composite of:
  (1) ONE mod-8 condition: complex-window starts = {d = 4 mod 8}
      = {rho(d)-1 = 3} (the equivalence is gated, G3) -- the
      classical Clifford/Bott Z/8, whose two-place Witt-Weil
      arithmetic home is Theorems 1f-1g;
  (2) the spacetime ANCHOR d = 4 -- Lovelock-cap-Clifford + the
      hypothesis, residue items in the paper's seven-item count --
      doing DOUBLE duty: it assigns the window {4,5,6} to
      spacetime AND thereby excludes the rho-twin d = 4 from
      gauge candidacy;
  (3) the scan range [5, 19]: 5 = d_V, the tower start and first
      distinguished layer; 19 = d_1, the phase-threshold layer --
      both members of the paper's distinguished set {5,7,19,217},
      each identification carrying the feature->integer-layer
      selection convention (a LISTED residue member) (net-state,
      Theorem 1k as corrected round 60: entailed given the site-E
      pairing plus part0's variational-sup labeling; member
      re-motivated, count unchanged);
  (4) the within-window factor assignment -- Door 3's decomposed
      count (Clifford construction + classical mod-2 bounds).
d_0 = 7 enters only the separate window-completeness fact (G2).

THE FINDING (corrected form -- weaker than the first version, and
honest).  The layer selection introduces no new UNLISTED
dependency: every component above is a listed residue member, the
classical Z/8 (arithmetically homed), or Door 3's content.  What
the first version added beyond this -- "over-determination by
independent selectors" -- is RETRACTED: there is one selector
(the Z/8 window structure), one anchor, and one range whose ends
are listed layers.  The papers' own coincidence-grading (12 = 12;
rank 4 = d) is respected and checked as arithmetic display
(constants -- explicitly NOT counted as gates).

WHAT THIS DOES NOT DO: derive the layer from finite places;
change any number; alter the residue count.  No data, no
closures, no RH/GRH, no semiclassics.
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
    print("THE LAYER QUESTION (round-30 corrected): what selects d = 12")
    print("=" * 74)

    d0, d1 = 7, 19          # Part 0 thresholds (cited); d0's only GATE
                            # role is G2 (also shown in the AD display)
    dV = 5                  # tower start / first distinguished layer

    # G1: the mod-8 complex-window arithmetic
    win = [d for d in range(4, 23) if d % 8 in (4, 5, 6)]
    g1 = (win == [4, 5, 6, 12, 13, 14, 20, 21, 22]
          and win[3:6] == [d + 8 for d in win[:3]]        # computed, can fail
          and win[6:9] == [d + 16 for d in win[:3]])      # (round-31 F4)
    print()
    print(f"G1 complex windows in [4,22] = {win}")
    print(f"   second = first + 8; third = first + 16   "
          f"{'PASS' if g1 else 'FAIL'}")

    # G2: window-completeness in the inter-threshold band (d0, d1]
    windows = [win[0:3], win[3:6], win[6:9]]   # computed (round-32 F4)
    inside = [w for w in windows if all(d0 < d <= d1 for d in w)]
    g2 = inside == [[12, 13, 14]]
    print(f"G2 complete windows inside the inter-threshold band"
          f" ({d0}, {d1}]: {inside}   {'PASS' if g2 else 'FAIL'}")
    print("   (d_0's ONLY role here -- it does NOT bound the")
    print("   uniqueness scan; round-30 M2)")

    # G3 (round-30 reworked): ONE condition, and the anchor's twin
    g3a = all((rho(d) - 1 == 3) == (d % 8 == 4)
              for d in range(1, 10001))
    s54 = [d for d in range(dV, d1 + 1) if rho(d) - 1 == 3]
    s44 = [d for d in range(4, d1 + 1) if rho(d) - 1 == 3]
    g3 = g3a and s54 == [12] and s44 == [4, 12]
    print(f"G3 {{rho(d)-1 = 3}} == {{d = 4 mod 8}} on [1, 10000]:"
          f" {g3a}")
    print(f"   scan [{dV},{d1}] -> {s54};  scan [4,{d1}] -> {s44}   "
          f"{'PASS' if g3 else 'FAIL'}")
    print("   => ONE mod-8 condition (the window-start condition");
    print("      itself); rho(4)-1 = 3 is the anchor's twin, excluded")
    print("      by the anchor assignment + the tower start d_V = 5")
    print("      -- NOT by an independent selector (round-30 M1)")

    # G4 (relabeled): two facts, identification cited
    g4 = all(rho(2 ** (v + 4) * m) - rho(2 ** v * m) == 8
             for v in range(4) for m in (1, 3, 5))
    print(f"G4 rho's v_2-recurrence: rho(16n) = rho(n) + 8   "
          f"{'PASS' if g4 else 'FAIL'}")
    print("   (a DIFFERENT structure from the d -> d+8 window shift")
    print("   of G1; the identification of the two 8s as one classical")
    print("   Clifford/Bott Z/8 = BW(R) is CITED, not gated --")
    print("   round-30 m-grade relabel)")

    # arithmetic display (NOT a gate -- constants, cannot fail)
    print(f"AD coincidence arithmetic (display only, not a gate:")
    print(f"   constants -- round-30 m-grade): d_1 - d_0 = {d1 - d0}"
          f" = 8+3+1; rank 2+1+1 = 4")
    print("   (held apart per the papers' own grading: 'a numerical")
    print("   consistency check ... not a structural identity')")

    print()
    print("=" * 74)
    print("READING (source-reading result + gated arithmetic;")
    print("round-30 corrected)")
    print("=" * 74)
    print("  ONE selector: the Clifford/Bott Z/8 window structure")
    print("  ({rho-1 = 3} IS the window-start set -- gated).  The")
    print("  anchor (Lovelock + hypothesis, listed residue) assigns")
    print("  d = 4 to spacetime and thereby excludes the rho-twin;")
    print("  the scan range's ends are the listed distinguished")
    print("  layers d_V = 5 and d_1 = 19 (feature->layer convention,")
    print("  a listed residue member; net-state, Theorem 1k as")
    print("  corrected round 60: entailed given the site-E pairing")
    print("  plus part0's variational-sup labeling).  The layer")
    print("  selection still")
    print("  introduces no new UNLISTED dependency -- but the")
    print("  'over-determined by independent selectors' claim of the")
    print("  first version is RETRACTED (round-30 M1).  Not a")
    print("  finite-place derivation; no number changes; no data,")
    print("  no closures.")


if __name__ == "__main__":
    main()
