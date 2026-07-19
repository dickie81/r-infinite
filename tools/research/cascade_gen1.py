#!/usr/bin/env python3
"""
Gen-1 derived: the u/d inversion as a theorem of the threshold ladder.

The structure (papers' own distinction): Gen-1 (layer 21) is the only
generation ABOVE the d_1 = 19 phase transition; the Gen2 -> Gen1
descent crosses the threshold.  Two candidate lemmas complete the
ladder there:

  (i) UP-TYPE threshold selection: the crossing engages the full turn
      -- four quarter-turn legs, Gamma(1/2)^4 = pi^2 -- on top of the
      N_c copy selection:  (c/u)/(s/d) = N_c pi^2 = 29.609.
      Observed: 29.62 +/- 1.0  ->  +0.02 sigma.
  (ii) DOWN-TYPE threshold factor: (mu/e)/(s/d) = 2 pi sqrt(e) --
      the closed-cycle unit 2 pi = N(0) Gamma(1/2)^2 (the papers'
      structural unit) times HALF the Cartan atom (one of the two
      colour charges frozen at the phase transition).  Its grammar
      twin e^2 sqrt(2) (equally close on s/d alone) is DISCRIMINATED
      by FLAG's precision ratio m_s/m_ud = 27.42(12): the 2 pi sqrt(e)
      form survives at -0.6 sigma, the twin dies at -2.5 sigma --
      data selection, the b/s precedent.

CONSEQUENCE (no further freedom): the famous Gen-1 inversion is
derived --

    u/d = (c/s) / (N_c pi^2) = 0.459   (lattice 0.462(20): -0.1 sigma)

u is lighter than d BECAUSE the Gen-2 up/down split (c/s = 13.6) is
smaller than the threshold selection factor (29.6).  The absolutes
follow from the derived s and the closed mu/e chain.
"""

import math

from scipy.special import digamma

SQRTPI = math.sqrt(math.pi)
V_GF = 246.2196


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def main():
    # the session chain (Addenda 17-22)
    Phi613 = sum(p(d) for d in range(6, 14))
    bs = math.exp(Phi613) * 2 * SQRTPI * math.e * math.exp(-alpha(7) / 16)
    mtau = 1776.82e-3
    mb = mtau * math.e * math.sqrt(3) / 2
    ms = mb / bs
    mt = (V_GF / math.sqrt(2)) * math.exp(-alpha(14) / 4)
    mc = mt / (3 * bs * math.exp(alpha(5) / 8))
    mue = 206.7710                                   # closed m_mu/m_e

    print("=" * 74)
    print("PART A: the up-type threshold factor N_c pi^2")
    print("=" * 74)
    dr_pred = 3 * math.pi ** 2
    dr_obs = (1273.0 / 2.16) / (93.5 / 4.70)
    sdr = dr_obs * math.hypot(0.0046 / 1.273, 0.07 / 2.16, 0.0008 / 0.0935,
                              0.05 / 4.70)
    print(f"  (c/u)/(s/d) predicted N_c Gamma(1/2)^4 = {dr_pred:.3f}")
    print(f"  observed {dr_obs:.2f} +/- {sdr:.2f}"
          f"   ({(dr_pred-dr_obs)/sdr:+.2f} sigma)")

    print()
    print("=" * 74)
    print("PART B: the inversion derived (no new unknowns)")
    print("=" * 74)
    ud = (mc / ms) / dr_pred
    print(f"  u/d = (c/s)/(N_c pi^2) = {mc/ms:.4f}/{dr_pred:.4f} = {ud:.4f}")
    print(f"  lattice m_u/m_d = 0.462 +/- 0.020"
          f"   ({(ud-0.462)/0.020:+.2f} sigma)")
    print("  u < d BECAUSE c/s (13.6) < N_c pi^2 (29.6): the inversion is")
    print("  the threshold selection factor exceeding the Gen-2 split.")

    print()
    print("=" * 74)
    print("PART C: the down-type threshold factor, data-discriminated")
    print("=" * 74)
    candA = 2 * math.pi * math.sqrt(math.e)          # 2pi sqrt(e)
    candB = math.e ** 2 * math.sqrt(2)               # grammar twin
    for lab, F in [("2 pi sqrt(e)  [closed-cycle unit x half-Cartan]", candA),
                   ("e^2 sqrt(2)   [grammar twin]", candB)]:
        sd = mue / F
        d_ = ms * 1e3 / sd
        u_ = d_ * ud
        mud = (u_ + d_) / 2
        s_over = ms * 1e3 / mud
        print(f"  F = {lab}")
        print(f"    s/d = {sd:.3f}; d = {d_:.3f} MeV"
              f" ({(d_-4.70)/0.05:+.2f}s vs 4.70(5));"
              f" u = {u_:.3f} ({(u_-2.16)/0.07:+.2f}s vs 2.16(7))")
        print(f"    m_s/m_ud = {s_over:.2f} vs FLAG 27.42(12):"
              f" {(s_over-27.42)/0.12:+.2f} sigma"
              f"   {'SURVIVES' if abs(s_over-27.42)/0.12 < 1.5 else '** DEAD **'}")
    print("  => FLAG's precision ratio selects 2 pi sqrt(e); the twin dies.")

    print()
    print("=" * 74)
    print("PART D: the complete quark spectrum (session chain)")
    print("=" * 74)
    sdA = mue / candA
    d_mev = ms * 1e3 / sdA
    u_mev = d_mev * ud
    rows = [("t", mt, 172.57, 0.29), ("b", mb, 4.183, 0.007),
            ("c", mc, 1.2730, 0.0046), ("s", ms, 0.0935, 0.0008),
            ("d", d_mev / 1e3, 0.00470, 0.00005),
            ("u", u_mev / 1e3, 0.00216, 0.00007)]
    for name, pred, obs, sig in rows:
        print(f"  {name:>2}: {pred*1e3:>10.3f} MeV   obs {obs*1e3:>10.3f}"
              f" +/- {sig*1e3:.3f}   ({(pred-obs)/sig:+.2f} sigma)")
    print()
    print("  all six quarks from: m_tau (closed), the bare unit + v (top),")
    print("  and six structural factors -- e, cos(pi/6), N_c, alpha-members,")
    print("  pi^2, 2 pi sqrt(e) -- each assigned by rule or discriminated by")
    print("  data.  Named residual lemmas: threshold-full-turn (pi^2),")
    print("  half-Cartan-at-threshold (sqrt(e)), doublet assignment, signs,")
    print("  scheme.")


if __name__ == "__main__":
    main()
