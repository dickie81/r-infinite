#!/usr/bin/env python3
"""
Deriving the exp(1) colour atom (the e in b/s = (m_tau/m_mu) e).

Papers' status (part4b:991): 'one unit of cascade potential accumulated
across the SU(3) layer'; Adams derivation open.  This tool: (A) fixes
the measured target; (B) reports a scheme inconsistency between the
papers' two e-claims; (C) prices the candidate derivations; (D) tests
the strongest candidate's consistency web across all colour ratios.

The proposed derivation (Cartan equipartition):
    The cascade descent is a sequence of measurements (Born rule via
    Gleason, Part II).  A coloured state crossing the gluon layer
    d_g = 12 has its colour measured; measurable colour charges = the
    commuting set = the Cartan subalgebra of SU(3), of rank 2 (rank
    forced by the Adams-forced SU(3)).  Each measured Gaussian mode of
    the cascade action S = sum (2 alpha)^-1 (Delta phi)^2 contributes
    exactly 1/2 to the exponent (equipartition -- the papers' own
    Berezin/Gaussian machinery).  Colour factor:
        exp(rank(SU(3)) x 1/2) = exp(1),   exactly.
    Colour singlets (leptons, neutrinos) measure nothing: factor 1.
"""

import math

from scipy.special import digamma

SQRTPI = math.sqrt(math.pi)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def Phi(a, b):
    return sum(p(d) for d in range(a, b + 1))


MB_MS, MB_POLE, MS_Q, MTAU, MMU = 4.183, 4.78, 0.0935, 1.77686, 0.1056584
MT, MC = 172.57, 1.27


def part_A():
    print("=" * 74)
    print("PART A: the measured target")
    print("=" * 74)
    lead = math.exp(Phi(6, 13)) * 2 * SQRTPI
    expo = math.log((MB_MS / MS_Q) / lead)
    sig = math.hypot(0.007 / 4.183, 0.8 / 93.5)
    print(f"  measured exponent ln[(b/s)/(tau/mu lead)] = {expo:.5f}"
          f" +/- {sig:.5f}")
    print(f"  papers' package: 1 - alpha(7)/chi^4 = {1-alpha(7)/16:.5f}"
          f"   ({(1-alpha(7)/16-expo)/sig:+.2f} sigma)")
    print(f"  bare exp(1):  1.00000   ({(1-expo)/sig:+.2f} sigma)")


def part_B():
    print()
    print("=" * 74)
    print("PART B: scheme inconsistency in the papers' two e-claims (novel)")
    print("=" * 74)
    print(f"  m_b/m_tau (MS-bar m_b = 4.183): {MB_MS/MTAU:.4f}"
          f"   vs e = {math.e:.4f}  ({(MB_MS/MTAU/math.e-1)*100:+.1f}%)")
    print(f"  m_b/m_tau (pole  m_b = 4.78):  {MB_POLE/MTAU:.4f}"
          f"   vs e   ({(MB_POLE/MTAU/math.e-1)*100:+.1f}%)")
    print("  => the papers' 'm_b/m_tau = e (1.05%)' (Tier 4a) requires the")
    print("     POLE mass, while 'b/s = (tau/mu) e (0.4%)' uses MS-bar.")
    lead = math.exp(Phi(6, 13)) * 2 * SQRTPI
    print(f"  in the POLE scheme the b/s colour factor becomes"
          f" {(MB_POLE/MS_Q)/lead:.3f} ~ N_c ({((MB_POLE/MS_Q)/lead/3-1)*100:+.1f}%)")
    print("  => 'e vs N_c' for the colour atom is a SCHEME question (they")
    print("     differ by ~10%, the known pole/MS-bar b-quark shift); any")
    print("     derivation must also derive the scheme, via the papers' own")
    print("     sqrt(N_c/N(0)) scheme-factor machinery.")


def part_C():
    print()
    print("=" * 74)
    print("PART C: candidate derivations, priced")
    print("=" * 74)
    print("  1. Cartan equipartition: exp(rank SU(3) x 1/2) = exp(1) EXACT.")
    print("     rank 2 forced by Adams' SU(3); 1/2 forced by Gaussian")
    print("     equipartition of the cascade action (their own Berezin")
    print("     machinery); 'measured charges = commuting set' from the")
    print("     cascade's Born-rule descent.  Zero numerical freedom.")
    print(f"  2. literal 'window potential': Phi(12,14) = {Phi(12,14):.4f}")
    print("     != 1 -- the papers' own phrasing fails numerically at 9%.")
    print(f"  3. colour multiplicity ln N_c = {math.log(3):.4f} minus an")
    print("     unforced correction (grammar; rejected by audit rules).")
    print(f"  4. full-adjoint equipartition exp(8 x 1/2) = e^4: excluded")
    print("     (factor ~55).  The rank (measurable charges), not the")
    print("     dimension, is what a Born-rule descent can excite.")


def part_D():
    print()
    print("=" * 74)
    print("PART D: consistency web of the Cartan-equipartition rule")
    print("=" * 74)
    lead = math.exp(Phi(6, 13)) * 2 * SQRTPI
    bs = (MB_MS / MS_Q)
    print(f"  b/s = lead x e:        {lead*math.e:.3f} vs {bs:.3f}"
          f"  ({(lead*math.e/bs-1)*100:+.2f}% -> their alpha(7) closure)")
    print(f"  mu/e, tau/mu (singlets): no factor -- consistent (no e appears")
    print(f"    in any lepton ratio in the papers)")
    tc = MT / MC
    print(f"  t/c vs N_c x (b/s):    {tc:.2f} vs {3*bs:.2f}"
          f"  ({(3*bs/tc-1)*100:+.2f}%)")
    print(f"    [equivalent to the papers' Tier-4 (t/b)/(c/s) = N_c; the")
    print(f"     rule 'coloured ratio -> e; up-type -> extra N_c (Weyl")
    print(f"     chirality at d=12, their open item)' reproduces both]")
    print(f"  m_b/m_tau: MS-bar {MB_MS/MTAU:.3f} -- the crossing rule")
    print(f"    predicts NO factor for a same-layer ratio, so m_b/m_tau = e")
    print(f"    (pole) remains UNEXPLAINED by this route; its Tier-4 status")
    print(f"    and scheme dependence (Part B) mean the two e-claims are")
    print(f"    probably not the same phenomenon.")
    print()
    print("  STATUS: proposed lemma, not proof.  Exact, zero-freedom, and")
    print("  consistent with every colour-singlet and cross-generation")
    print("  datum; the open step is formalising 'a gluon-layer crossing")
    print("  measures exactly the Cartan, at 1/2 per mode' inside the")
    print("  papers' Gleason/Berezin machinery (one lemma).  It also")
    print("  predicts: any future coloured cross-generation ratio carries")
    print("  exactly one factor e per gauge-window crossing -- falsifiable")
    print("  in the up-type spectrum once derived.")


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
    part_D()
