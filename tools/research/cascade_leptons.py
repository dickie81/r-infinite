#!/usr/bin/env python3
"""
The lepton sector from the existing machinery -- no new atoms, no new
rules.  Sources (read directly): part4b thm:lepton-ratios (l.498),
thm:alpha-s-closure (l.2462), rem:slot-precedence-mu-e (l.1854),
thm:mtau-abs-closure (l.2995), thm:complete-mass (l.610), thm:vev
(l.3325), Tier-2 summary (l.4108).

PART A: the papers' three lepton closures recomputed in the session's
  epsilon-factor dictionary -- every factor a named local constant:
    tau/mu = e^(Phi(6,13) + a(14)/chi) * chi Gamma(1/2)
    mu/e   = e^(Phi(14,21)) * chi Gamma(1/2)
             * (1 + a_em/period + a_em * a(21))     [radiative slot]
    tau    = (alpha_s v / sqrt(2)) e^(-Phi(5) + a(19)/chi) / (chi Gamma(1/2))^2
  with alpha_s, v, a_em themselves dictionary objects and v anchored
  at the reduced Planck mass.

PART B: chain composition -- absolute m_mu, m_e ride the closed m_tau
  and the closed ratios; the direct-formula 0.5% systematic cancels.

PART C: the cross-sector identity the dictionary predicts: the quark
  and lepton chains over the SAME window differ by exactly the colour
  atom and a member swap:  (b/s)/(tau/mu) = e * e^(-a(7)/chi^4 - a(14)/chi).

PART D: null-clone pricing of the three lepton stages (extends A27):
  credited = the freedom the source-selection rules leave (the four
  distinguished source layers); skeptical = windows x prefactors x
  members all free.

Check-4 category: the three closures are the papers' own Tier-2
results (acknowledged, not novel); novel here is the dictionary form,
the Planck-anchored nine-fermion chain, the cross-sector identity,
and the pricing.
"""

import itertools
import math

import numpy as np
from scipy.special import digamma

LN2 = math.log(2.0)
SQRTPI = math.sqrt(math.pi)
M_PL_RED = 2.435e18                      # GeV


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def N(d):
    return SQRTPI * R(d)


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def Phi(a, b):
    return sum(p(d) for d in range(a, b + 1))


# ---- dictionary-derived inputs (no empirical numbers) ----
A_GUT = N(12) ** 2 / (4 * math.pi)                    # 1/25.02
ALPHA_S = A_GUT * math.exp(Phi(5, 12))                # leading 0.1159
V_CASCADE = M_PL_RED * A_GUT * math.exp(Phi(5, 12)) \
    * math.exp(-math.pi / alpha(5))                   # ~240.8 GeV
A_EM = 1 / (1 / alpha(13) + math.pi / alpha(14) + 6 * math.pi)  # 1/137.028

# ---- observations ----
TAU_MU_OBS, TAU_MU_ERR = 16.81703, 0.00114
MU_E_OBS = 206.7682830
MTAU_OBS, MTAU_ERR = 1776.86, 0.12                    # MeV, PDG 2024
MMU_OBS = 105.6583755
ME_OBS = 0.51099895


def part_A():
    print("=" * 74)
    print("PART A: the three closures in dictionary form (Planck-anchored)")
    print("=" * 74)
    print(f"  dictionary inputs: 1/a_GUT = {1/A_GUT:.2f},"
          f" alpha_s = {ALPHA_S:.5f},")
    print(f"  v_cascade = {V_CASCADE:.1f} GeV (from M_Pl,red),"
          f" 1/a_em = {1/A_EM:.3f}")
    print()
    tau_mu = math.exp(Phi(6, 13) + alpha(14) / 2) * 2 * SQRTPI
    print(f"  tau/mu = e^(Phi(6,13)+a(14)/chi) chi G(1/2) = {tau_mu:.5f}")
    print(f"           obs {TAU_MU_OBS}({TAU_MU_ERR})"
          f"   ({(tau_mu-TAU_MU_OBS)/TAU_MU_ERR:+.2f} sigma)")
    mu_e_lead = math.exp(Phi(14, 21)) * 2 * SQRTPI
    mu_e = mu_e_lead * (1 + A_EM / (2 * math.pi) + A_EM * alpha(21))
    print(f"  mu/e   = e^(Phi(14,21)) chi G(1/2) x radiative slot"
          f" = {mu_e:.4f}")
    print(f"           obs {MU_E_OBS}   ({(mu_e/MU_E_OBS-1)*100:+.4f}% ="
          f" the cascade a_em systematic)")
    mtau = (ALPHA_S * V_CASCADE / math.sqrt(2)) \
        * math.exp(-p(5) + alpha(19) / 2) / (2 * SQRTPI) ** 2 * 1e3  # MeV
    print(f"  m_tau  = (alpha_s v/sqrt2) e^(-Phi(5)+a(19)/chi)"
          f" / (chi G(1/2))^2")
    print(f"         = {mtau:.2f} MeV   obs {MTAU_OBS}({MTAU_ERR})"
          f"   ({(mtau-MTAU_OBS)/MTAU_ERR:+.2f} sigma)")
    return tau_mu, mu_e, mtau


def part_B(tau_mu, mu_e, mtau):
    print()
    print("=" * 74)
    print("PART B: chain composition -- all three absolutes from M_Pl")
    print("=" * 74)
    mmu = mtau / tau_mu
    me = mmu / mu_e
    for name, pred, obs in [("m_tau", mtau, MTAU_OBS),
                            ("m_mu ", mmu, MMU_OBS),
                            ("m_e  ", me, ME_OBS)]:
        print(f"  {name} = {pred:.6f} MeV   obs {obs}"
              f"   ({(pred/obs-1)*1e6:+.0f} ppm)")
    print("  the papers' direct-formula residuals (0.47%, 0.60%) cancel in")
    print("  the chain: composition through closed ratios leaves ~40-60 ppm,")
    print("  the papers' own Tier-2(i) 'chain-subtracted inherited shift'")
    print("  band -- the cascade's standing leading-order systematic.")


def part_C():
    print()
    print("=" * 74)
    print("PART C: the cross-sector identity (quark = lepton x colour)")
    print("=" * 74)
    lhs = (math.exp(Phi(6, 13)) * 2 * SQRTPI * math.e
           * math.exp(-alpha(7) / 16)) \
        / (math.exp(Phi(6, 13) + alpha(14) / 2) * 2 * SQRTPI)
    rhs = math.e * math.exp(-alpha(7) / 16 - alpha(14) / 2)
    print(f"  (b/s)/(tau/mu) = {lhs:.6f} = e exp(-a(7)/chi^4 - a(14)/chi)"
          f" = {rhs:.6f}")
    print("  identical by construction -- the CONTENT: both sectors descend")
    print("  the SAME window Phi(6,13) with the SAME obstruction chi G(1/2);")
    print("  the entire quark/lepton difference is the colour atom e (two")
    print("  measured Cartan modes) and a member swap a(14)/chi -> a(7)/chi^4")
    print("  (U(1) source -> area-maximum source).  Observed check:")
    obs = (4.183 / 0.0935) / TAU_MU_OBS
    print(f"  observed (b/s)/(tau/mu) = {obs:.4f} vs {rhs:.4f}"
          f"   ({(rhs/obs-1)*100:+.3f}%)")


def p_match(logvals, logT, dev, W=LN2):
    lo, hi = logT - W, logT + W
    a = np.clip(logvals - dev, lo, hi)
    b = np.clip(logvals + dev, lo, hi)
    keep = b > a
    a, b = a[keep], b[keep]
    if len(a) == 0:
        return 0.0
    order = np.argsort(a)
    a, b = a[order], b[order]
    total, ca, cb = 0.0, a[0], b[0]
    for x, y in zip(a[1:], b[1:]):
        if x > cb:
            total += cb - ca
            ca, cb = x, y
        else:
            cb = max(cb, y)
    total += cb - ca
    return total / (2 * W)


def part_D(tau_mu, mu_e, mtau):
    print()
    print("=" * 74)
    print("PART D: null-clone pricing of the lepton stages (extends A27)")
    print("=" * 74)
    P0 = [2.0, math.sqrt(2), SQRTPI, 2 * SQRTPI, math.pi, math.pi ** 2,
          2 * math.pi, math.e, math.sqrt(math.e), math.cos(math.pi / 6),
          1 / math.cos(math.pi / 6), 3.0, math.pi ** 0.25]
    LAYERS = (5, 7, 12, 13, 14, 19, 21)
    corr = np.array([0.0] + [s * alpha(d) / 2 ** k for d in LAYERS
                             for k in range(5) for s in (1, -1)])
    prod2 = set()
    for r_ in range(0, 3):
        for combo in itertools.combinations_with_replacement(P0, r_):
            base = [math.log(x) for x in combo]
            for signs in itertools.product((1, -1), repeat=r_):
                prod2.add(round(sum(s * l for s, l in zip(signs, base)), 9))
    prod2 = np.array(sorted(prod2))
    windows = np.array([Phi(a_, b_) for a_ in range(5, 9)
                        for b_ in range(12, 24)])
    skep = np.unique(np.round(
        np.add.outer(np.add.outer(windows, prod2), corr).ravel(), 9))

    # credited freedom: the four family source shifts the rules choose among
    fam = [alpha(14) / 2, alpha(19) / 2, alpha(5) / 8, alpha(7) / 4]

    stages = []
    base_tm = Phi(6, 13) + math.log(2 * SQRTPI)
    stages.append(("tau/mu", TAU_MU_OBS, tau_mu,
                   base_tm + np.array(fam), skep))
    base_me = Phi(14, 21) + math.log(2 * SQRTPI)
    rad = [0.0, A_EM / (2 * math.pi),
           A_EM / (2 * math.pi) + A_EM * alpha(21), A_EM * alpha(21)]
    stages.append(("mu/e", MU_E_OBS, mu_e, base_me + np.array(rad), skep))
    base_ta = math.log(ALPHA_S * V_CASCADE / math.sqrt(2) / (4 * math.pi)
                       * 1e3) - p(5)
    stages.append(("tau abs (MeV)", MTAU_OBS, mtau,
                   base_ta + np.array(fam), skep))

    print(f"  {'stage':<15}{'dev':>9}{'N_cr':>6}{'p_cr':>10}{'bits':>7}"
          f"{'N_sk':>9}{'p_sk':>10}{'bits':>7}")
    tc = ts = 0.0
    for name, obs, pred, cred, sk in stages:
        dev = abs(math.log(pred / obs))
        pc = p_match(cred, math.log(obs), dev)
        ps = p_match(sk, math.log(obs), dev)
        bc = -math.log2(pc) if pc > 0 else float("inf")
        bs_ = -math.log2(ps) if ps > 0 else float("inf")
        tc += bc
        ts += bs_
        print(f"  {name:<15}{dev:>9.1e}{len(cred):>6}{pc:>10.2e}{bc:>7.1f}"
              f"{len(sk):>9}{ps:>10.2e}{bs_:>7.1f}")
    print(f"  {'TOTAL added':<15}{'':>9}{'':>6}{'':>10}{tc:>7.1f}"
          f"{'':>9}{'':>10}{ts:>7.1f}")
    print()
    print("  combined with A27:  credited 61 + these; skeptical 19 + these.")
    print("  The lepton stages carry the chain's smallest deviations (~1e-5)")
    print("  so they dominate the credited column; under full skepticism the")
    print("  window x member space saturates them, same as b/s.")


if __name__ == "__main__":
    tm, me_, mt = part_A()
    part_B(tm, me_, mt)
    part_C()
    part_D(tm, me_, mt)
