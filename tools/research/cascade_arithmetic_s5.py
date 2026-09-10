#!/usr/bin/env python3
"""
S5 DERIVED: THE ROOT-FRAME PROJECTION IS TRACE DUALITY IN Z[omega].

S5 (named joint of A25): 'the measurement frame lies along roots, so
weight states overlap at cos(pi/6)'.  Claim: both halves are
arithmetic.

P1 (The roots ARE the units).  The unit group of Z[omega] (omega =
   e^(2 pi i/3), the ring of integers of Q(zeta_3)) is mu_6 =
   {+-1, +-omega, +-omega^2} -- and these six points ARE the root
   system A_2 of su(3), exactly (verified coordinate-by-coordinate).
   'Along roots' = 'along units of the colour character ring'.

P2 (The measurement frame is the dual lattice).  A functional on a
   lattice lives in its trace-dual -- that is the definition of
   duality, not physics.  The trace-dual of Z[omega] is the inverse
   different d^(-1) = (1/sqrt(-3)) Z[omega] (disc(Q(zeta_3)) = -3).
   Multiplication by 1/sqrt(-3) scales by 1/sqrt(3) and rotates by
   -90 = +30 mod 60 (the order-6 unit rotations): THE DUAL LATTICE
   IS THE LATTICE ROTATED BY EXACTLY 30 DEGREES.  Verified: minimal
   vectors, duality pairings Tr in Z, and the su(3) fundamental
   weight w_1 = e^(i pi/6)/sqrt(3) is EXACTLY a minimal vector of
   d^(-1).

P3 (The projection value).  Pairing a lattice minimal vector (root/
   unit) with the nearest dual minimal vector (weight) projects at
   cos(30 deg) = sqrt(3)/2 = cos(pi/6).  The sec(pi/6) of the
   inverse frame change is the same statement read dual-to-lattice.

P4 (Uniqueness).  Among imaginary quadratic integer rings the
   nontrivial projection angle is unique to disc = -3: computed
   minimal lattice-vs-dual angles collapse to the trivial cases
   (Z[i]: 0 deg, projection 1, no factor; Z[sqrt(-2)] and
   Z[(1+sqrt(-7))/2]: 90 deg, projection 0, degenerate);
   only Z[omega] -- the unique ring with six units -- gives 30 deg.
   The factor cos(pi/6) exists because and only because the colour
   character field is Q(zeta_3).

BOUNDARY (P5): arithmetic does not supply the colour multiplicity 3
(2-adic/instantiation, as at T5) nor which physical legs carry a
pairing (occupancy).  The FRAME (dual lattice) and the VALUE
(cos(pi/6)) are mathematics: theorem T8.
"""

import cmath
import itertools
import math

PI = math.pi
W = cmath.exp(2j * PI / 3)                     # omega


def lattice_points(b1, b2, n=6):
    return [a * b1 + b * b2 for a in range(-n, n + 1)
            for b in range(-n, n + 1) if (a, b) != (0, 0)]


def minimal_vectors(pts, tol=1e-9):
    m = min(abs(p) for p in pts)
    return [p for p in pts if abs(abs(p) - m) < tol]


def min_angle(l1, l2):
    best = 180.0
    for v in minimal_vectors(l1):
        for w_ in minimal_vectors(l2):
            c = (v.real * w_.real + v.imag * w_.imag) / (abs(v) * abs(w_))
            ang = math.degrees(math.acos(max(-1, min(1, c))))
            best = min(best, ang)
    return best


def P1():
    print("=" * 74)
    print("P1: the su(3) roots are the units of Z[omega]")
    print("=" * 74)
    units = [u for u in lattice_points(1, W)
             if abs(abs(u) - 1) < 1e-12]
    roots = [1 + 0j, -1 + 0j, complex(0.5, math.sqrt(3) / 2),
             complex(-0.5, -math.sqrt(3) / 2),
             complex(-0.5, math.sqrt(3) / 2),
             complex(0.5, -math.sqrt(3) / 2)]
    print(f"  |mu(Z[omega])| = {len(units)} (norm-1 elements)")
    match = all(min(abs(u - r) for r in roots) < 1e-12 for u in units)
    print(f"  units == A_2 root system of su(3), point-by-point: {match}")
    print("  => 'along roots' = 'along the units of the colour ring'.")


def P2():
    print()
    print("=" * 74)
    print("P2: the dual lattice is Z[omega] rotated by exactly 30 deg")
    print("=" * 74)
    gen = 1 / cmath.sqrt(-3)                   # inverse-different generator
    dual = lattice_points(gen * 1, gen * W)
    lat = lattice_points(1, W)
    print(f"  1/sqrt(-3): modulus {abs(gen):.6f} = 1/sqrt(3)"
          f" = {1/math.sqrt(3):.6f};  arg {math.degrees(cmath.phase(gen)):.1f}"
          f" deg = +30 mod 60 (unit rotations)")
    ang = min_angle(lat, dual)
    print(f"  minimal lattice-vs-dual angle: {ang:.6f} deg")
    w1 = complex(0.5, 1 / (2 * math.sqrt(3)))  # su(3) fundamental weight
    tgt = cmath.exp(1j * PI / 6) / math.sqrt(3)
    ind = min(abs(w1 - p) for p in dual)
    print(f"  su(3) weight w_1 = {w1:.6f};  e^(i pi/6)/sqrt(3) = {tgt:.6f}"
          f"   |diff| = {abs(w1-tgt):.1e}")
    print(f"  w_1 in d^(-1) (nearest dual point: {ind:.1e});"
          f" |w_1| = {abs(w1):.6f} = 1/sqrt(3): minimal")
    units = [u for u in lat if abs(abs(u) - 1) < 1e-12]
    trs = sorted(round((w1 * u.conjugate()).real * 2, 9) for u in units)
    print(f"  duality pairings Tr(w_1 u-bar) = 2Re(...): {trs}  (integers)")


def P3():
    print()
    print("=" * 74)
    print("P3: the projection value")
    print("=" * 74)
    w1 = cmath.exp(1j * PI / 6) / math.sqrt(3)
    c = (w1.real * 1 + w1.imag * 0) / abs(w1)
    print(f"  cos(angle(w_1, nearest root)) = {c:.9f}"
          f" = sqrt(3)/2 = {math.sqrt(3)/2:.9f} = cos(pi/6)")
    print("  => one pairing per crossing projects at cos(pi/6);")
    print("     the inverse frame change carries sec(pi/6).")


def P4():
    print()
    print("=" * 74)
    print("P4: uniqueness among imaginary quadratic rings")
    print("=" * 74)
    rings = [
        ("Z[omega]   (disc -3)", 1, W, 1 / cmath.sqrt(-3)),
        ("Z[i]       (disc -4)", 1, 1j, 1 / (2j)),
        ("Z[sqrt-2]  (disc -8)", 1, cmath.sqrt(-2), 1 / (2 * cmath.sqrt(-2))),
        ("Z[(1+sqrt-7)/2] (disc -7)", 1, (1 + cmath.sqrt(-7)) / 2,
         1 / cmath.sqrt(-7)),
    ]
    for name, b1, b2, g in rings:
        lat = lattice_points(b1, b2)
        dual = lattice_points(g * b1, g * b2)
        ang = min_angle(lat, dual)
        proj = math.cos(math.radians(ang))
        print(f"  {name:<28} min angle = {ang:>7.3f} deg"
              f"   projection = {proj:.6f}")
    print("  => the nontrivial projection (30 deg) is UNIQUE to disc = -3,")
    print("     the only imaginary quadratic ring with six units.  The")
    print("     factor cos(pi/6) exists iff the colour field is Q(zeta_3).")


if __name__ == "__main__":
    P1()
    P2()
    P3()
    P4()
    print()
    print("=" * 74)
    print("P5: boundary -- colour multiplicity 3 (2-adic) and which legs")
    print("carry a pairing (occupancy) are instantiation data.  The frame")
    print("(trace-dual lattice) and the value (cos(pi/6)) are theorem T8.")
    print("=" * 74)
