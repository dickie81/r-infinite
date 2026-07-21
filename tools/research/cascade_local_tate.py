#!/usr/bin/env python3
"""
THE LOCAL TATE STEP (Addendum 70): 2-adic and 3-adic Tate theory at
the identity layer -- the self-dual achievers at every place, the
dyadic squareness modulus, the compensation, the colour field's
local geography, and one checked negative.  Category (a): exact
identities and classical theorems, machine-verified; no data, no
closures; every identification graded; nothing claimed forced.

T-loc1 (SELF-DUAL ACHIEVERS AT EVERY PLACE -- the per-place T2).
Tate's local theory: at each place v the local zeta integral of the
self-dual vector achieves the local factor.
  - v = infinity: the Gaussian e^(-pi x^2) is self-dual and achieves
    Gamma_R(s) (this is T2 / Theorem 2, already proved).
  - v = p finite: the unit-ball indicator 1_{Z_p} is self-dual
    (Fourier transform = itself, unramified psi, self-dual measure)
    and achieves E_p(s) = (1 - p^(-s))^(-1):
        Z_p(1_{Z_p}, s) = sum_{k>=0} p^(-ks) = E_p(s).
  Verified below: the geometric identity numerically; self-duality
  by exact finite Fourier (the indicator of Z_p sampled on the
  lattice p^(-k)Z/p^k Z is a comb whose DFT is itself -- checked by
  FFT for p = 2, 3 at two depths).  COROLLARY (assembly): the
  program's Gaussian is the archimedean component of THE standard
  adelic self-dual vector Phi = e^(-pi x^2) x prod_p 1_{Z_p}, whose
  global Tate integral is Gamma_R(s) zeta(s).  A1's "dynamics = the
  achieving vector" is a per-place statement; the tower's dynamics
  is the archimedean member of an adelic family (extends T1d).

T-loc2 (THE DYADIC SQUARENESS MODULUS -- the clock's second dyadic
anchor; classical, verified by enumeration + Hensel lifting).
  - A 2-adic unit u is a square in Z_2 iff u = 1 mod 8.  (Squares
    of odd numbers mod 8 = {1}; conversely u = 1 mod 8 lifts by
    Hensel -- verified to 2^20 for a sample.)
  - Square-class counts: |R^x/(R^x)^2| = 2 = chi;
    |Q_2^x/(Q_2^x)^2| = 8; |Q_p^x/(Q_p^x)^2| = 4 (p odd).
    The real place has 2 square classes (= chi = |mu(R)|, A2's
    torsion constant); THE DYADIC PLACE HAS 8; odd places have 4.
  GRADING: exact classical theorems, plus the IDENTIFICATION that
  this mod-8 -- the dyadic squareness modulus -- is the finite-place
  home of the program's mod-8 clock; corroborated independently by
  D3.2 (dyadic-exclusive zeta_8 Gauss phases) and D3.3/T-loc3 (the
  compensation).  Identification, not derivation.

T-loc3 (THE COMPENSATION IS DYADIC-EXCLUSIVE).  The p = 1 case of
Landsberg-Schaar gives exactly
    sum_{n mod 2q} e^(-pi i n^2/(2q)) = sqrt(2q) * zeta_8^(-1):
the conjugate dyadic Gauss sum carries the INVERSE clock -- the
finite-place compensation of gamma_inf = zeta_8 (T6) in the product
formula, localized at 2.  Odd places are silent for the unit form:
G(p^2)/p = 1 exactly (verified).  Together with T-loc2: the mod-8
clock is a real <-> dyadic duality, with all other places neutral.

T-loc4 (THE COLOUR FIELD'S LOCAL GEOGRAPHY + the odd global
potential identity).
  - p = 3 RAMIFIES in Q(zeta_3): chi_{-3}(3) = 0, the local factor
    E_3^chi = 1 -- the conductor (= the different, C4) silences the
    3-factor of the colour L-function.
  - p = 2 is INERT: chi_{-3}(2) = -1, E_2^chi = (1 + 2^(-s))^(-1).
  - The odd tower's global potential identity (the sgn/colour
    analogue of D3.1), exact:
        p_sgn(s) + sum_p p_p^chi(s) = Lambda'/Lambda(s, chi) -
        (1/2) ln 3,
    with p_p^chi = (log E_p^chi)' and the conductor term standing
    where the even tower had its poles.  Verified numerically.
  The two structure primes' roles, now exact: p = 2 carries the
  clock and is inert in colour; p = 3 carries the colour
  ramification (the different) and is silent in its own L-factor.

T-loc5 (A CHECKED NEGATIVE, recorded).  The naive transplant of the
clock's real-place home to p = 2 -- "BW(Q_2) = Z/8" -- is FALSE:
Br(Q_2) = Q/Z by local class field theory, so the graded Brauer
group of Q_2 is infinite.  The dyadic home of the mod-8 clock is
the square-class / Gauss-phase structure (T-loc2/3), NOT the graded
Brauer group.  (Classical; recorded as a negative so no future pass
re-attempts the transplant.)

WHAT THIS DOES AND DOES NOT DO (honest scope, stated first):
  DOES: give every place its achieving vector (per-place T2); anchor
    the clock's modulus at the dyadic squareness criterion (graded
    identification, three corroborations); verify the compensation
    and the odd global identity; fix the colour primes' local roles;
    record the BW(Q_2) negative.
  DOES NOT: derive N_c = 3 or any other A2 grammar entry from the
    finite places (the Radon-Hurwitz v_2 form remains a labeling;
    deriving it from Q_2 Clifford/Tate structure is the remaining
    open step and the BW negative closes its most obvious route);
    touch data; close anything; use RH/GRH.
"""

import cmath
import math

import numpy as np
from mpmath import mp, mpf, mpc, zeta, gamma as mpgamma, diff, log, pi as mppi

mp.dps = 25


def chi3(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)


def L_chi(s):
    if isinstance(s, mpc):
        return mpc(3) ** (-s) * (zeta(s, mpf(1) / 3) - zeta(s, mpf(2) / 3))
    return mpf(3) ** (-s) * (zeta(s, mpf(1) / 3) - zeta(s, mpf(2) / 3))


def Lambda_chi(s):
    return (mpf(3) / mppi) ** ((s + 1) / 2) * mpgamma((s + 1) / 2) * L_chi(s)


def p_sgn(s):
    return -log(mppi) / 2 + mp.digamma((mpf(s) + 1) / 2) / 2


def main():
    print("=" * 74)
    print("THE LOCAL TATE STEP: finite-place theory at the identity layer")
    print("=" * 74)

    # ---- T-loc1: achievers
    print()
    print("T-loc1 self-dual achievers at every place:")
    ok = True
    for p in (2, 3):
        for s in (2.0, 6.0):
            partial = sum(p ** (-k * s) for k in range(200))
            ok &= abs(partial - 1 / (1 - p ** (-s))) < 1e-15
    print(f"  Z_p(1_Zp, s) = (1 - p^-s)^-1 for p = 2, 3"
          f"   {'PASS' if ok else 'FAIL'}   (geometric identity)")
    sd = True
    for p, k in ((2, 3), (2, 5), (3, 2), (3, 3)):
        N = p ** (2 * k)
        v = np.zeros(N)
        v[::p ** k] = 1.0                     # 1_{Z_p} on p^-k Z / p^k Z
        vhat = np.fft.fft(v) / math.sqrt(N)
        sd &= np.allclose(np.abs(vhat), v / 1.0, atol=1e-9) and \
            np.allclose(vhat.real[::p ** k], 1.0, atol=1e-9)
    print(f"  1_Zp self-dual (comb DFT = itself; p = 2, 3, two depths)"
          f"   {'PASS' if sd else 'FAIL'}")
    print("  => the program's Gaussian is the archimedean component of")
    print("     the standard adelic self-dual vector; A1's 'dynamics =")
    print("     the achieving vector' is a per-place statement.")

    # ---- T-loc2: dyadic squareness modulus
    print()
    print("T-loc2 the dyadic squareness modulus:")
    sq8 = {(n * n) % 8 for n in range(1, 16, 2)}
    print(f"  squares of odd integers mod 8 = {sq8}"
          f"   {'PASS' if sq8 == {1} else 'FAIL'}")
    hensel = True
    for u in (9, 17, 25, 33, 41, 57, 73, 89, 105, 1 + 8 * 1234567):
        # lift x^2 = u mod 2^k from k=3 to k=20
        x = 1
        for k in range(3, 21):
            if (x * x - u) % (2 ** (k + 1)) != 0:
                x2 = x + 2 ** (k - 1)
                if (x2 * x2 - u) % (2 ** (k + 1)) == 0:
                    x = x2
                else:
                    hensel = False
        hensel &= (x * x - u) % (2 ** 20) == 0
    non = all(all((x * x - u) % 16 != 0 for x in range(16))
              for u in (3, 5, 7, 11, 13, 15))
    print(f"  u = 1 mod 8  => square in Z_2 (Hensel to 2^20, sample)"
          f"   {'PASS' if hensel else 'FAIL'}")
    print(f"  u = 3,5,7 mod 8 => NOT square (mod 16 obstruction)"
          f"   {'PASS' if non else 'FAIL'}")
    # square-class counts
    odd_classes = {(n * n) % 16 for n in range(1, 16, 2)}   # -> {1,9}
    q2 = 2 * 4    # valuation parity x units-mod-squares {1,3,5,7 mod 8}
    okp = True
    for p in (3, 5, 7):
        residues = {(n * n) % p for n in range(1, p)}
        okp &= len(residues) == (p - 1) // 2
    print(f"  square classes: |R^x/sq| = 2 (= chi);  |Q_2^x/sq| = {q2}"
          f" (units mod sq = 4 via mod-8);  |Q_p^x/sq| = 4 (p odd,"
          f" QR count verified)   {'PASS' if okp and odd_classes == {1, 9} else 'FAIL'}")
    print("  => the clock's modulus 8 IS the dyadic squareness modulus")
    print("     (graded identification; corroborations: D3.2, T-loc3).")

    # ---- T-loc3: the compensation
    print()
    print("T-loc3 the compensation (p = 1 Landsberg-Schaar case):")
    zeta8inv = cmath.exp(-1j * cmath.pi / 4)
    comp = True
    for q in range(1, 9):
        ssum = sum(cmath.exp(-1j * cmath.pi * n * n / (2 * q))
                   for n in range(2 * q))
        comp &= abs(ssum - math.sqrt(2 * q) * zeta8inv) < 1e-9
    print(f"  sum_{{n mod 2q}} e^(-pi i n^2/(2q)) = sqrt(2q) zeta_8^-1,"
          f" q = 1..8   {'PASS' if comp else 'FAIL'}")
    silent = True
    for p in (3, 5, 7, 11):
        g = sum(cmath.exp(2j * cmath.pi * n * n / (p * p))
                for n in range(p * p))
        silent &= abs(g - p) < 1e-8
    print(f"  odd places silent: G(p^2) = p exactly (phase 1), p ="
          f" 3,5,7,11   {'PASS' if silent else 'FAIL'}")
    print("  => gamma_inf x (dyadic conjugate phase) = 1: the product-")
    print("     formula compensation of T6's clock is DYADIC-EXCLUSIVE.")

    # ---- T-loc4: colour geography + odd global identity
    print()
    print("T-loc4 colour local geography + odd global potential identity:")
    print(f"  chi_-3(3) = {chi3(3)} (RAMIFIED: E_3 = 1 -- the conductor/")
    print(f"  different silences its own 3-factor);  chi_-3(2) ="
          f" {chi3(2)} (INERT: E_2 = (1+2^-s)^-1)")
    okg = True
    for s in (2, 6):
        s = mpf(s)
        lhs = p_sgn(s) + diff(lambda u: log(L_chi(u)), s)
        rhs = diff(lambda u: log(Lambda_chi(u)), s) - log(3) / 2
        okg &= abs(float(lhs - rhs)) < 1e-20
    print(f"  p_sgn + sum_p p_p^chi = Lambda'/Lambda - (1/2)ln3"
          f" (s = 2, 6)   {'PASS' if okg else 'FAIL'}")
    print("  => both towers now carry global potential identities; the")
    print("     odd tower's 'pole slot' is the conductor = the different.")

    # ---- T-loc5: the checked negative
    print()
    print("T-loc5 checked negative (recorded, classical):")
    print("  BW(Q_2) is NOT Z/8: Br(Q_2) = Q/Z (local class field")
    print("  theory), so the graded Brauer group of Q_2 is infinite.")
    print("  The dyadic home of the mod-8 clock is the square-class /")
    print("  Gauss-phase structure, not the graded Brauer group.  This")
    print("  closes the most obvious route to a finite-place derivation")
    print("  of the Radon-Hurwitz grammar entry; that derivation stays")
    print("  OPEN and un-attempted here.")

    print()
    print("=" * 74)
    print("READING (exact + graded; honest scope in docstring)")
    print("=" * 74)
    print("  Every place has its achieving vector; the clock's modulus")
    print("  is the dyadic squareness modulus (identification, three")
    print("  corroborations); the compensation is dyadic-exclusive; the")
    print("  colour primes' roles are fixed (2 inert + clock; 3 ramified")
    print("  = different); the odd tower has its global identity.  NO")
    print("  grammar entry is derived; N_c's v_2 form stays a labeling.")


if __name__ == "__main__":
    main()
