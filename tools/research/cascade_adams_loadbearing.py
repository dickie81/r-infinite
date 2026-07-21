#!/usr/bin/env python3
"""
DOOR 3 (Addendum 83): the Adams dependency, decomposed -- what the
N_c chain actually load-bears on.  Category (a): a source-reading
result (Check 1, direct quotes below) plus machine-gated
classification arithmetic; no data, no closures; no number changes
anywhere; every attribution graded, with the one
citation-confidence caveat stated in D3.3.

THE QUESTION (the post-convergence survey's Door 3).  Theorem
1f(iii) registered the honest negative "N_c = 3 is Adams' theorem
(archimedean K-theory)".  Adams' theorem has two halves of very
different depth: the LOWER bound (rho(n)-1 fields EXIST -- the
Hurwitz-Radon-Eckmann Clifford construction, elementary algebra)
and the UPPER bound (no more exist -- hard; K-theory in general).
Which half does the cascade's N_c chain actually load-bear on, at
which dimensions?

THE SOURCES, READ DIRECTLY (Check 1).  Part IVa, "N_c = 3 from
Adams' theorem":
  - thm:adams (part4a.tex:328): "The maximum number of linearly
    independent nowhere-zero tangent vector fields on S^{n-1} is
    rho(n)-1" -- applied at d = 12 (max 3 = N_c), d = 13 (max 0:
    broken), d = 14 (max 1 = dim U(1)).
  - thm:adams-unique (part4a.tex:359): "Among all dimensions
    5 <= d <= d_1 = 19, the dimension d = 12 is the unique
    dimension for which rho(d)-1 = 3", by the rho table over
    [5,19].
  - The papers cite Adams throughout ("Steenrod" appears nowhere
    in src/*.tex; Poincare-Hopf is already papers-native at
    part4a.tex:1276 for the breaking pattern).

THE DECOMPOSITION (D3.2, machine-gated below).  For each claim in
the chain, the load-bearing direction and the weakest classical
theorem sufficing:
  d = 13 ("max 0"):  UPPER bound only; S^12 is EVEN-dimensional,
      so this is the hairy ball / Poincare-Hopf theorem
      (chi(S^2n) = 2 != 0) -- elementary, 1885/1926.
  d = 12 ("max = 3" -> N_c):  LOWER (>= 3: Clifford construction,
      Hurwitz 1898 / Radon 1922 / Eckmann 1942) + UPPER (<= 3).
  d = 14 ("max = 1" -> dim U(1)):  LOWER (>= 1: odd sphere,
      elementary) + UPPER (<= 1).
  Uniqueness scan over [5,19] ("rho(d)-1 != 3 for d != 12"):
      d with rho-1 > 3 (d = 8, 16):  LOWER bound alone suffices
          (construction gives > 3 fields; no upper bound needed --
          in particular d = 16, the window's ONLY 16 | d case,
          needs NO upper bound);
      d odd (rho-1 = 0):  UPPER bound 0 = Poincare-Hopf
          (even sphere), elementary;
      d = 2 mod 4 (rho-1 = 1):  UPPER bound "max <= 2" needed
          (to exclude 3); sits at v_2(d) = 1.
THE KEY STRUCTURAL FACTS, GATED IN-CODE:
  (i)  no load-bearing UPPER bound occurs at d = 0 mod 16;
  (ii) every load-bearing upper bound sits at v_2(d) in {0, 1, 2}
       -- v_2 = 0 needing only Poincare-Hopf, v_2 in {1, 2}
       needing the classical pre-Adams upper bounds.

D3.3 (THE ATTRIBUTION, WITH ITS CONFIDENCE STATED).  The upper
bounds at v_2(d) in {1, 2} (n not divisible by 16 -- indeed n with
v_2 <= 2, the very first cases of the classical method) were
settled a decade before Adams by Steenrod-Whitehead (PNAS 1951,
via Steenrod squares on stunted projective spaces; refinements
James 1957, Toda), with Adams (Annals 1962, K-theory + Adams
operations) needed for the general theorem -- in particular the
16 | n cases the cascade never load-bears on.  CITATION
CONFIDENCE: the exact scope of the Steenrod-Whitehead theorem is
quoted here from the standard history (Adams' own introduction and
the survey literature; the 1951 PNAS original was paywalled in
this session).  The conclusion is robust across readings of that
scope: every cascade-needed upper bound sits at v_2 <= 2, the
lightest cases of the 1951 method, and none sits at 16 | n.

WHAT THIS DOES AND DOES NOT DO.
  DOES: decompose the honest negative of 1f(iii).  "The count is
    Adams (K-theory)" refines to: the count's CONSTRUCTION half is
    Clifford algebra -- the same Cl/Bott/BW(R) = Z/8 object whose
    arithmetic home Theorems 1f-1g established -- and its
    UPPER-BOUND half is classical mod-2 topology (Poincare-Hopf +
    the 1951-class bounds), with K-theory proper load-bearing
    NOWHERE in the cascade window.  The genuinely archimedean
    residue for N_c narrows to: the mod-2 cohomology upper bound
    at v_2(d) in {1,2}, plus the layer-12 selection (papers-side).
  DOES NOT: derive N_c from the finite places (1f(iii)'s negative
    stands verbatim); change any number, any layer assignment, or
    any papers-side theorem (part IVa's Adams citation is correct
    and sufficient -- citing the strongest standard theorem is
    normal practice; this file reduces the DEPENDENCY, not the
    correctness).  A part-IVa remark carrying this decomposition
    is optional papers-side follow-up, not commissioned here.
No data, no closures, no RH/GRH, no semiclassics.
"""


def rho(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    a, b = divmod(v, 4)
    return 8 * a + 2 ** b


def v2(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def main():
    print("=" * 74)
    print("DOOR 3: the Adams dependency, decomposed")
    print("=" * 74)

    print()
    print("Load-bearing directions across the gauge window and the")
    print("uniqueness scan [5, 19] (claim: rho(d)-1 = 3 iff d = 12):")
    print()
    print("   d   rho-1  claim        needs lower?  needs upper?  upper via")
    rows = []
    for d in range(5, 20):
        r = rho(d) - 1
        if d == 12:
            claim, lo, up = "= 3 (N_c)", True, True
        elif r > 3:
            claim, lo, up = "!= 3 (>3)", True, False
        elif r == 0:
            claim, lo, up = "!= 3 (=0)", False, True
        else:
            claim, lo, up = "!= 3 (<3)", False, True
        via = ("-" if not up else
               "Poincare-Hopf (even sphere)" if d % 2 == 1 else
               "classical (v_2 <= 2)")
        rows.append((d, r, lo, up, via))
        print(f"  {d:>3}   {r:>3}   {claim:<11}  {str(lo):<12}"
              f"  {str(up):<12}  {via}")

    # gate (i): no load-bearing upper bound at 16 | d
    g1 = all(d % 16 != 0 for d, r, lo, up, via in rows if up)
    print()
    print(f"  gate (i): no load-bearing upper bound at d = 0 mod 16"
          f" (d = 16 needs lower only: rho-1 = {rho(16)-1} > 3)   "
          f"{'PASS' if g1 else 'FAIL'}")
    # gate (ii): every load-bearing upper bound at v_2 in {0,1,2}
    g2 = all(v2(d) in (0, 1, 2) for d, r, lo, up, via in rows if up)
    print(f"  gate (ii): every load-bearing upper bound sits at v_2(d)"
          f" in {{0, 1, 2}}   {'PASS' if g2 else 'FAIL'}")
    # gate (iii): the d = 13, 14 gauge rows
    g3 = (rho(13) - 1 == 0) and (13 % 2 == 1)   # even sphere S^12: P-H
    g4 = (rho(14) - 1 == 1) and v2(14) == 1     # upper at v_2 = 1
    print(f"  gate (iii): d = 13 'max 0' is the even-sphere"
          f" Poincare-Hopf case   {'PASS' if g3 else 'FAIL'}")
    print(f"  gate (iv): d = 14 'max 1' upper bound sits at v_2 = 1"
          f"   {'PASS' if g4 else 'FAIL'}")
    # gate (v): the N_c row itself
    g5 = rho(12) - 1 == 3 and v2(12) == 2
    print(f"  gate (v): d = 12 'max 3' -- lower = Clifford construction,"
          f" upper at v_2 = 2   {'PASS' if g5 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (source-reading result + gated arithmetic)")
    print("=" * 74)
    print("  The cascade's N_c chain load-bears on: the Hurwitz-Radon-")
    print("  Eckmann CONSTRUCTION (Clifford algebra -- the same Cl/Bott/")
    print("  BW(R) = Z/8 object of Theorems 1f-1g), Poincare-Hopf at the")
    print("  odd-d rows and d = 13, and pre-Adams classical upper bounds")
    print("  at v_2(d) in {1, 2} (Steenrod-Whitehead 1951 class; see the")
    print("  citation-confidence note in D3.3).  K-theory proper is")
    print("  load-bearing NOWHERE in the cascade window: the only")
    print("  16 | d dimension (d = 16) needs no upper bound at all.")
    print("  1f(iii)'s honest negative stands verbatim; its 'Adams")
    print("  (K-theory)' attribution refines to 'Clifford construction +")
    print("  classical mod-2 topology'.  No number changes; no grammar")
    print("  entry derived; no data, no closures.")


if __name__ == "__main__":
    main()
