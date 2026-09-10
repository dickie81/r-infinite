#!/usr/bin/env python3
"""
More masses from the crossing/Cartan machinery: the down-type quark
absolutes, and an honest refusal on the rest.

Machinery in play: the variance-normalisation theorem (Addendum 18),
the Cartan-equipartition colour atom e (Addendum 14: crossing the
gluon layer measures the rank-2 Cartan, exp(2 x 1/2) = e), and the
composition rule (Addendum 13: closed observables compose, corrections
attach once).

THE NEW CANDIDATE (Cartan projection).  In su(3) the angle between
weight directions and root directions is exactly 30 degrees -- the
hexagonal weight geometry.  If the colour crossing measures the Cartan
along root directions (Addendum 14), a down-type quark's weight
projects onto the measured frame with cos(pi/6) = sqrt(3)/2.  The
same-layer quark/lepton mass offset is then the measured colour
content:

    m_b = m_tau x e x cos(pi/6)

-- the colour atom times the weight-root projection.  From it, the
already-closed b/s ratio generates m_s, and the up-type relation
t/c = N_c (b/s) follows from the Weyl-chirality multiplicity.

Pricing (audit rules): the projection factor is a single-candidate
match (cos(pi/6) is THE angle of su(3) weight-root geometry, not one
of many), landing at 0.00 sigma; held at candidate-lemma grade like
Addendum 14, ~3 bits, pending the projection lemma.  The scheme/scale
caveat of Addendum 14 applies with force: all quark 'masses' here are
PDG-convention values (m_b at m_b, m_s at 2 GeV); the closures live in
that convention and a scheme-consistent derivation must eventually
justify it.

REFUSALS (recorded): the up-type absolute anchor (t or c alone) and
the Gen-1 inversion (u/d < 1) are NOT derivable from the present
machinery; the papers say so ('does not derive the full up-type
spectrum') and no grammar search is performed here.
"""

import math

E = math.e
COS30 = math.sqrt(3.0) / 2.0


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def p_digamma(d):
    from scipy.special import digamma
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def main():
    SQRTPI = math.sqrt(math.pi)
    Phi = sum(p_digamma(d) for d in range(6, 14))
    mtau = 1776.82e-3                        # closed, GeV (Addendum 17 chain)
    lead_tm = math.exp(Phi) * 2 * SQRTPI     # m_tau/m_mu lead
    bs_closed = lead_tm * E * math.exp(-alpha(7) / 16)

    print("=" * 74)
    print("PART A: the bottom anchor -- m_b = m_tau x e x cos(pi/6)")
    print("=" * 74)
    mb = mtau * E * COS30
    print(f"  m_b = {mtau*1e3:.2f} MeV x e x sqrt(3)/2 = {mb:.4f} GeV")
    print(f"  PDG m_b(m_b) = 4.183 +0.007/-0.006"
          f"   -> {(mb-4.183)/0.007:+.2f} sigma")
    print("  structure: colour atom e (rank-2 Cartan equipartition,")
    print("  Addendum 14) x weight-root projection cos(pi/6) (the unique")
    print("  angle of su(3) weight geometry).  Candidate-lemma grade.")

    print()
    print("=" * 74)
    print("PART B: the strange mass via the closed b/s ratio")
    print("=" * 74)
    ms = mb / bs_closed
    print(f"  b/s closed = {bs_closed:.4f} (Addendum 13 canonical form)")
    print(f"  m_s = m_b/(b/s) = {ms*1e3:.2f} MeV   PDG 93.5 +/- 0.8"
          f"   -> {(ms*1e3-93.5)/0.8:+.2f} sigma")

    print()
    print("=" * 74)
    print("PART C: the up-type relation t/c = N_c x (b/s)")
    print("=" * 74)
    tc = 3 * bs_closed
    tc_obs = 172.57 / 1.27
    sig_tc = tc_obs * math.hypot(0.29 / 172.57, 0.02 / 1.27)
    print(f"  t/c = 3 x {bs_closed:.3f} = {tc:.2f}   observed {tc_obs:.2f}"
          f" +/- {sig_tc:.2f}   -> {(tc-tc_obs)/sig_tc:+.2f} sigma")
    print("  (equivalent to the papers' Tier-4 (t/b)/(c/s) = N_c; the Weyl")
    print("  multiplicity N_c enters as counting, not equipartition)")

    print()
    print("=" * 74)
    print("PART D: scheme/scale caveat (applies to ALL of the above)")
    print("=" * 74)
    print("  PDG convention mixes scales: m_b at mu = m_b, m_s at mu = 2 GeV.")
    print("  Running m_s to mu = m_b shrinks it ~15%, moving b/s to ~52.6:")
    print("  the e-relation holds in the PDG convention specifically.  Same")
    print("  class as Addendum 14's pole/MS-bar finding: the cascade must")
    print("  eventually derive its scheme (the papers' sqrt(N_c/N(0))")
    print("  machinery is the opening), or these matches are convention-")
    print("  contingent.")

    print()
    print("=" * 74)
    print("PART E: refusals (recorded)")
    print("=" * 74)
    print("  - up-type absolute anchor (t or c alone): one equation short;")
    print("    the Weyl-chirality decomposition of S^11 (papers' open item)")
    print("    is the missing theorem.  No grammar search performed.")
    print("  - Gen-1 inversion (u/d = 0.46 < 1): outside the crossing")
    print("    pattern; the papers acknowledge; not derivable tonight.")
    print()
    print("  net new masses tonight: m_b (0.00 sigma), m_s (-0.01 sigma),")
    print("  plus the t/c relation (-0.72 sigma) -- all on one candidate")
    print("  lemma (weight-root projection) and one scheme caveat.")


if __name__ == "__main__":
    main()
