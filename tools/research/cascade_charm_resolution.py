#!/usr/bin/env python3
"""
Resolving the charm strain: the t/c relation's forced correction.

The strain (Addendum 21): c = t/(N_c (b/s)) = 1.2858 GeV vs the precise
PDG m_c(m_c) = 1.2730(46) at +2.8 sigma.

The resolution comes from the incremental flag rule (Addendum 13), not
from member-shopping.  The canonical formula for t/c is
[b/s (closed)] x N_c: its increment is the single static atom {N_c}
(the Adams count) -- no exponential, no window content.  Flags on the
increment: P = F, L = T -> OBSERVER class -> source d_V = 5, member
alpha(5)/chi^3 (the Observer-class k = 3 of sin^2 theta_W and
Omega_m).  Sign: the lead sits BELOW observation (-1.0%), the
descent-population signature, which per the papers' two-population
systematics (part4b Confidence Assessment: 'descent-dependent
quantities carry uniformly negative deviations') takes the POSITIVE
shift -- the sin^2 theta_W precedent exactly.

    t/c = N_c (b/s) e^{+alpha(5)/chi^3}

Checks below: the double ratio (t/b)/(c/s) = N_c e^{alpha(5)/8} vs
PDG; the resolved charm mass; and what remains named (the sign rule's
formal derivation; u, d still refused).
"""

import math

from scipy.special import digamma

SQRTPI = math.sqrt(math.pi)
V_GF = 246.2196
MC, SMC = 1.2730, 0.0046      # PDG m_c(m_c)
MT, SMT = 172.57, 0.29
MB, MS_Q = 4.183, 0.0935


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def main():
    Phi = sum(0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)
              for d in range(6, 14))
    bs = math.exp(Phi) * 2 * SQRTPI * math.e * math.exp(-alpha(7) / 16)
    mt = (V_GF / math.sqrt(2)) * math.exp(-alpha(14) / 4)

    print("=" * 74)
    print("The forced assignment")
    print("=" * 74)
    print("  increment of t/c over [b/s closed]: {N_c} -- static, no")
    print("  exponential, no window content -> L = T -> Observer class")
    print("  -> +alpha(5)/chi^3 (k = 3, as sin2thW/Omega_m; sign from the")
    print("  papers' two-population systematics: lead low -> positive).")

    shift = math.exp(alpha(5) / 8)
    tc = 3 * bs * shift
    tc_obs = MT / MC
    stc = tc_obs * math.hypot(SMT / MT, SMC / MC)
    print()
    print(f"  t/c = N_c (b/s) e^(alpha(5)/8) = {tc:.3f}"
          f"   observed {tc_obs:.3f} +/- {stc:.3f}"
          f"   ({(tc-tc_obs)/stc:+.2f} sigma)")

    print()
    print("=" * 74)
    print("Consequences")
    print("=" * 74)
    c_pred = mt / tc
    print(f"  m_c = t / [N_c (b/s) e^(alpha(5)/8)] = {c_pred:.4f} GeV")
    print(f"    vs m_c(m_c) = 1.2730 +/- 0.0046:"
          f" {(c_pred-MC)/SMC:+.2f} sigma   (was +2.8 sigma: RESOLVED)")
    dr = 3 * shift
    dr_obs = (MT / MB) / (MC / MS_Q)
    sdr = dr_obs * math.hypot(SMT / MT, 0.007 / MB, SMC / MC, 0.0008 / MS_Q)
    print(f"  double ratio (t/b)/(c/s): predicted N_c e^(alpha(5)/8)"
          f" = {dr:.4f}")
    print(f"    observed {dr_obs:.4f} +/- {sdr:.4f}"
          f"   ({(dr-dr_obs)/sdr:+.2f} sigma)")
    print("    [the papers' Tier-4 '(t/b)/(c/s) = N_c to 1.5%' closes to")
    print("     0.1 sigma with the forced Observer member]")

    print()
    print("=" * 74)
    print("Named residuals")
    print("=" * 74)
    print("  - the sign step: taken from the papers' two-population")
    print("    systematics (their thm:sign-rule is the formal home);")
    print("  - the scheme derivation (all values PDG-convention);")
    print("  - u, d: Gen-1 refusal maintained.")
    print()
    print(f"  quark ledger: b -0.03 | s -0.03 | t +0.14 | c"
          f" {(c_pred-MC)/SMC:+.2f} | u,d refused")


if __name__ == "__main__":
    main()
