#!/usr/bin/env python3
"""
The transmutation route to q_QCD: deriving the hadronic ledge position
from the cascade's own coupling content.

Addendum 7 derived the matter-ledge location bottom-up (vacuum floor ->
capacity saturation -> q = 1/6).  This tool derives it top-down, through
the one mechanism by which known physics generates a hierarchy: QCD
dimensional transmutation, with every input a cascade-claimed quantity:

  - alpha_s at the electroweak anchor: the Part IVb lead
    alpha(12) * exp(Phi(5,12)), corrected by (1 + alpha(14)/2)
    [the correction the surprisal audit's Part E scrutinised];
  - b0 = 11 - (2/3) n_f from the cascade's forced SU(3) and forced
    three generations (integer counting only);
  - flavour thresholds at the charm/bottom/top masses (cascade
    Phi-ladder leads; PDG values used numerically);
  - the 120.146-decade hierarchy from the Omega-floor (Part I).

Output: Lambda_QCD and the ledge exponent q = decades(Lambda)/120.146,
the Planck-boundary "counting form" q ~ 2pi/(b0_eff ln10 alpha_s(M_Pl))
/ 120.146, the comparison with Addendum 7's capacity route, and the
inversion that turns electroweak adjacency into a consistency window.

Caveats carried explicitly: 1-loop running underestimates Lambda by
~x2.3 vs the 4-loop MS-bar reference (0.37 decades -> 0.003 in q); the
cascade's alpha_s value was calibrated at M_Z by the papers, so the
anchor-free reading used in the inversion is a reinterpretation; the
capacity scale's identification within the hadronic complex (17 MeV vs
m_pi vs Lambda) carries ~1 decade of slop, which dominates the
inversion window.
"""

import math

from scipy.special import digamma

MRED = 2.435e18          # reduced Planck mass, GeV
H_DEC = 120.146          # hierarchy decades (Omega-floor, reduced units)
MZ, MT, MB, MC = 91.188, 172.57, 4.18, 1.27
LAM3_4LOOP = 0.332       # 4-loop MS-bar Lambda^(3), GeV (reference)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def q_of(m_gev):
    return math.log10(MRED / m_gev) / H_DEC


def b0(nf):
    return 11.0 - 2.0 * nf / 3.0


def run_1loop(alpha_lo, mu_lo, mu_hi, nf):
    """1-loop evolve alpha_s from mu_lo up to mu_hi at fixed nf."""
    inv = 1.0 / alpha_lo + (b0(nf) / (2 * math.pi)) * math.log(mu_hi / mu_lo)
    return 1.0 / inv


def lam_1loop(alpha_mu, mu, nf):
    return mu * math.exp(-2 * math.pi / (b0(nf) * alpha_mu))


def main():
    print("=" * 74)
    print("PART 1: the cascade's alpha_s at the electroweak anchor")
    print("=" * 74)
    Phi = sum(p(d) for d in range(5, 13))
    a_lead = alpha(12) * math.exp(Phi)
    a_s = a_lead * (1 + alpha(14) / 2)
    print(f"  lead alpha(12) e^Phi(5,12) = {a_lead:.5f}")
    print(f"  x (1 + alpha(14)/2)        = {a_s:.5f}   (PDG: 0.1179(9))")
    print("  [zero parameters; the correction factor is the audited")
    print("   alpha(14)/2 member -- Part E scrutiny applies]")

    print()
    print("=" * 74)
    print("PART 2: downward transmutation with cascade counting integers")
    print("=" * 74)
    a5b = 1.0 / (1.0 / a_s + (b0(5) / (2 * math.pi)) * math.log(MB / MZ))
    l4 = lam_1loop(1.0 / (1.0 / a5b), MB, 4)
    a4c = 1.0 / (1.0 / a5b + (b0(4) / (2 * math.pi)) * math.log(MC / MB))
    l3 = lam_1loop(a4c, MC, 3)
    print(f"  b0 integers (SU(3) forced, 3 generations forced):"
          f" 23/3, 25/3, 9")
    print(f"  Lambda^(3) 1-loop = {l3*1e3:.0f} MeV"
          f"   (4-loop MS-bar reference: {LAM3_4LOOP*1e3:.0f} MeV)")
    print(f"  q(Lambda) = {q_of(l3):.4f} (1-loop) /"
          f" {q_of(LAM3_4LOOP):.4f} (4-loop ref)")
    print(f"  q(m_p = 0.938) = {q_of(0.93827):.4f},"
          f" q(m_pi) = {q_of(0.13957):.4f}")

    print()
    print("=" * 74)
    print("PART 3: the Planck-boundary counting form")
    print("=" * 74)
    a6t = run_1loop(a_s, MZ, MT, 5)          # crude: nf=5 to top
    aPl = run_1loop(a6t, MT, MRED, 6)
    print(f"  alpha_s(M_Pl,red) = 1/{1.0/aPl:.1f}")
    dec = math.log10(MRED / l3)
    b_eff = (2 * math.pi / math.log(10)) * (1.0 / aPl) / dec
    print(f"  decades M_Pl -> Lambda = {dec:.2f}"
          f"  =>  q_QCD = [2pi/(b_eff ln10 alpha_s(M_Pl))]/120.146"
          f" with b_eff = {b_eff:.2f}")
    print("  the ledge position is a percent-sized Planck coupling divided")
    print("  by a group-theory integer, exponentiated: counting sets q.")

    print()
    print("=" * 74)
    print("PART 4: two independent routes, and the adjacency inversion")
    print("=" * 74)
    print(f"  top-down (transmutation): q = {q_of(LAM3_4LOOP):.4f}"
          f" .. {q_of(l3):.4f}")
    print(f"  bottom-up (capacity, Addendum 7): q = 0.1677")
    print(f"  observed hadron cluster: q(p) = {q_of(0.93827):.4f},"
          f" q(pi) = {q_of(0.13957):.4f}")
    print("  agreement of the two routes: Delta q ~ 0.008-0.011"
          " (~1 decade in mass)")
    # inversion: anchor scale required so that transmutation lands on the
    # capacity scale; Lambda scales linearly with the anchor at fixed
    # alpha_s(anchor)
    for name, target in [("capacity scale 17.4 MeV", 0.0174),
                         ("m_pi", 0.13957), ("Lambda(3) 4-loop", LAM3_4LOOP)]:
        anchor = MZ * target / l3
        print(f"  EW anchor if transmutation must land on {name:<24}"
              f" ~ {anchor:7.1f} GeV")
    print("  => the electroweak anchor is forced into a ~1-decade window")
    print("     (~10-200 GeV) out of 120 available decades; the observed")
    print("     EW cluster (80-173 GeV) sits inside it.  Priced ~4-5 bits,")
    print("     contingent on Addendum 7's postulate and on reading the")
    print("     cascade alpha_s value as anchor-free (a reinterpretation:")
    print("     the papers calibrate it at M_Z).")


if __name__ == "__main__":
    main()
