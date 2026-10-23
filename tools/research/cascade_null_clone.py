#!/usr/bin/env python3
"""
THE NULL-CLONE TEST -- the de-biaser the audit named and never ran.

QUESTION.  If the observed masses had been different (a 'clone'
universe, each stage target perturbed within a factor-2 log window),
how often would the session's machinery have produced an equally good
'derivation'?  The mass arc's worth is  -log2 P(clone matched as well
as reality),  measured, not estimated.

DESIGN.  The session's chain factorises into 7 stages, each stage a
dimensionless ratio matched by one structural factor:

  H  : m_H/m_W        = sqrt(2)/(pi^(1/4) N(13))     [height lemma]
  t  : y_t            = exp(-alpha(14)/4)            [Yukawa filter]
  b  : m_b/m_tau      = e cos(pi/6)                  [Cartan+Eisenstein]
  bs : m_b/m_s        = e^Phi(6,13) 2sqrt(pi) e e^(-a7/16) [flags+incr.]
  c  : m_t/(m_c b/s)  = N_c exp(alpha(5)/8)          [Observer+incr.]
  d  : (mu/e)/(s/d)   = 2 pi sqrt(e)                 [threshold, data-disc.]
  u  : (c/u)/(s/d)    = N_c pi^2                     [threshold full turn]

Because the knobs partition by stage, the joint clone-match probability
factorises exactly:  P = prod_i p_i,  with p_i computed EXACTLY (interval
union, no MC noise) as the log-measure of clone targets within the
achieved deviation dev_i of ANY variant value, over the factor-2 window.

TWO FREEDOM LEVELS -- the disputed quantity is which one I actually had:

  CREDITED:  the assignment rules (flags theorem, increment rule,
     Yukawa filter, Cartan/Eisenstein, refusal discipline) are taken as
     forced; the variant set per stage is only the freedom the rules
     leave (typically 2-11 values).
  SKEPTICAL: every discrete choice the rules 'fixed' is counted as free
     (window endpoints, prefactor atoms, correction member, layer,
     denominator k, sign) -- the rules treated as post-hoc dressing.

LEVEL-1 CONTROL (mining freedom): the full <=4-atom signed grammar with
one optional correction member -- the space the original surprisal audit
showed to be saturated.  Expect p ~ 1 per stage: raw matches are free.
The mass arc's honest worth lies between SKEPTICAL and CREDITED; the
gap IS the epistemic status of the assignment rules.
"""

import itertools
import math

import numpy as np
from scipy.special import digamma

LN2 = math.log(2.0)
SQRTPI = math.sqrt(math.pi)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def N(d):
    return SQRTPI * R(d)


def Phi(a, b):
    return sum(0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)
               for d in range(a, b + 1))


# ---- the dictionary atom pool (the session's grammar) ----
P0 = [2.0, math.sqrt(2), SQRTPI, 2 * SQRTPI, math.pi, math.pi ** 2,
      2 * math.pi, math.e, math.sqrt(math.e), math.cos(math.pi / 6),
      1 / math.cos(math.pi / 6), 3.0, math.pi ** 0.25]
LAYERS = (5, 7, 12, 13, 14, 19, 21)
CORR = [0.0] + [s * alpha(d) / 2 ** k
                for d in LAYERS for k in range(5) for s in (1, -1)]   # logs


def signed_product_logs(atoms, rmax):
    out = {0.0}
    for r in range(1, rmax + 1):
        for combo in itertools.combinations_with_replacement(atoms, r):
            base = [math.log(a) for a in combo]
            for signs in itertools.product((1, -1), repeat=r):
                out.add(round(sum(s * l for s, l in zip(signs, base)), 9))
    return np.array(sorted(out))


def p_match(logvals, logT, dev, W=LN2):
    """Exact log-measure of clone targets in [logT-W, logT+W] lying
    within dev of some variant value (interval union)."""
    lo, hi = logT - W, logT + W
    a = np.clip(logvals - dev, lo, hi)
    b = np.clip(logvals + dev, lo, hi)
    keep = b > a
    a, b = a[keep], b[keep]
    if len(a) == 0:
        return 0.0
    order = np.argsort(a)
    a, b = a[order], b[order]
    total, cur_a, cur_b = 0.0, a[0], b[0]
    for x, y in zip(a[1:], b[1:]):
        if x > cur_b:
            total += cur_b - cur_a
            cur_a, cur_b = x, y
        else:
            cur_b = max(cur_b, y)
    total += cur_b - cur_a
    return total / (2 * W)


def build_stages():
    prod1 = signed_product_logs(P0, 1)
    prod2 = signed_product_logs(P0, 2)
    prod3 = signed_product_logs(P0, 3)
    corr = np.array(CORR)

    stages = []

    # H
    obs = 125.25 / 80.377
    pred = math.sqrt(2) / (math.pi ** 0.25 * N(13))
    cred = np.log([math.sqrt(2) / (math.pi ** 0.25 * N(d))
                   for d in (12, 13, 14)])
    skep = np.unique(np.round(np.concatenate(
        [prod2 - math.log(N(d)) for d in LAYERS] + [prod2]), 9))
    stages.append(("H  m_H/m_W", obs, pred, cred, skep))

    # t
    obs = 172.57 * math.sqrt(2) / 246.2196
    pred = math.exp(-alpha(14) / 4)
    cred = np.array([-alpha(14) / 2 ** k for k in range(5)])
    skep = corr.copy()
    stages.append(("t  y_t", obs, pred, cred, skep))

    # b
    obs = 4.183 / 1.77682
    pred = math.e * math.cos(math.pi / 6)
    cred = np.log([math.e, math.e * math.cos(math.pi / 6),
                   math.e / math.cos(math.pi / 6)])
    skep = prod2
    stages.append(("b  m_b/m_tau", obs, pred, cred, skep))

    # bs
    obs = 4.183 / 0.0935
    base = Phi(6, 13) + math.log(2 * SQRTPI * math.e)
    pred = math.exp(base - alpha(7) / 16)
    cred = base + np.array([0.0] + [s * alpha(7) / 2 ** k
                                    for k in range(5) for s in (1, -1)])
    windows = [Phi(a, b) for a in range(5, 9) for b in range(12, 16)]
    skep = np.unique(np.round(
        (np.add.outer(np.add.outer(np.array(windows), prod2), corr)
         ).ravel(), 9))
    stages.append(("bs m_b/m_s", obs, pred, cred, skep))

    # c
    obs = 172.57 / (1.273 * (4.183 / 0.0935))
    pred = 3 * math.exp(alpha(5) / 8)
    cred = math.log(3) + np.array([alpha(5) / 2 ** k for k in range(5)])
    skep = np.unique(np.round(
        (np.add.outer(np.add.outer(
            np.log([1.0, 3.0, 9.0]), corr), prod1)).ravel(), 9))
    stages.append(("c  t/(c*bs)", obs, pred, cred, skep))

    # d
    obs = 206.771 / (93.5 / 4.70)
    pred = 2 * math.pi * math.sqrt(math.e)
    cred = np.log([2 * math.pi * math.sqrt(math.e),
                   math.e ** 2 * math.sqrt(2)])
    skep = prod3
    stages.append(("d  (mu/e)/(s/d)", obs, pred, cred, skep))

    # u
    obs = (1273.0 / 2.16) / (93.5 / 4.70)
    pred = 3 * math.pi ** 2
    cred = np.log([3 * math.pi ** 2, 2 * math.pi * math.e * math.sqrt(3),
                   math.pi ** 3])
    skep = prod3
    stages.append(("u  (c/u)/(s/d)", obs, pred, cred, skep))

    return stages


def run(stages, W, label):
    print(f"  clone window: target x 2^(+-{W/LN2:.2f})   [{label}]")
    print(f"  {'stage':<18}{'dev':>9}{'N_cr':>7}{'p_cr':>10}{'bits':>7}"
          f"{'N_sk':>9}{'p_sk':>10}{'bits':>7}")
    tot_c = tot_s = 0.0
    for name, obs, pred, cred, skep in stages:
        dev = abs(math.log(pred / obs))
        pc = p_match(cred, math.log(obs), dev, W)
        ps = p_match(skep, math.log(obs), dev, W)
        bc = -math.log2(pc) if pc > 0 else float("inf")
        bs_ = -math.log2(ps) if ps > 0 else float("inf")
        tot_c += bc
        tot_s += bs_
        print(f"  {name:<18}{dev:>9.1e}{len(cred):>7}{pc:>10.2e}{bc:>7.1f}"
              f"{len(skep):>9}{ps:>10.2e}{bs_:>7.1f}")
    print(f"  {'TOTAL':<18}{'':>9}{'':>7}{'':>10}{tot_c:>7.1f}"
          f"{'':>9}{'':>10}{tot_s:>7.1f}")
    return tot_c, tot_s


def level1(stages):
    print("=" * 74)
    print("LEVEL-1 CONTROL: full mining freedom (<=4 signed atoms x corr)")
    print("=" * 74)
    prod4 = signed_product_logs(P0, 4)
    full = np.unique(np.round(
        np.add.outer(prod4, np.array(CORR)).ravel(), 9))
    print(f"  grammar size: {len(full)} distinct log-values")
    for name, obs, pred, cred, skep in stages:
        dev = abs(math.log(pred / obs))
        logT = math.log(obs)
        cnt = int(np.searchsorted(full, logT + dev)
                  - np.searchsorted(full, logT - dev))
        p = p_match(full, logT, dev)
        print(f"  {name:<18} forms within achieved dev: {cnt:>6}"
              f"   p(clone matched) = {p:.3f}")
    print("  => saturation: at mining freedom EVERY clone is matched as")
    print("     well as reality.  Raw per-number matches are worth 0 bits --")
    print("     the original audit's grammar-saturation finding, reproduced.")


def main():
    stages = build_stages()
    level1(stages)
    print()
    print("=" * 74)
    print("LEVEL-2: the exercised-freedom bracket (exact, interval-union)")
    print("=" * 74)
    tc, ts = run(stages, LN2, "primary")
    print()
    print("  sensitivity: narrower clone window (x1.3):")
    tc2, ts2 = run(stages, math.log(1.3), "narrow")
    print()
    print("=" * 74)
    print("VERDICT")
    print("=" * 74)
    print(f"  The arc's measured worth brackets:")
    print(f"    CREDITED  (rules forced):    {tc:.0f} bits "
          f"(narrow window {tc2:.0f})")
    print(f"    SKEPTICAL (rules post-hoc):  {ts:.0f} bits "
          f"(narrow window {ts2:.0f})")
    print("  minus a target-selection penalty (which 7 observables got")
    print("  formulas; stage definitions): ~10 bits, judgment-priced.")
    print("  Every x10 inflation of a stage's variant count costs 3.3 bits.")
    print("  The gap between the brackets is EXACTLY the epistemic status")
    print("  of the assignment rules (flags, increment, filter, Cartan/")
    print("  Eisenstein, refusal): derived-then-applied vs mined-then-")
    print("  dressed.  The registered ledger (Addendum 26) is what moves")
    print("  numbers from the skeptical column to the credited one.")


if __name__ == "__main__":
    main()
