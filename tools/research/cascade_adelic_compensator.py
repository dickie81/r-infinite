#!/usr/bin/env python3
"""
Adelic (finite-place) compensator test for the cascade.

Motivation
----------
The cascade's fundamental measure is the archimedean local factor of the
Riemann zeta function:

    Omega(d) = 2 / Gamma_R(d+1),   Gamma_R(s) = pi^(-s/2) Gamma(s/2)
    p(d)     = (log Gamma_R)'(d+1)

(Tate: Gamma_R is the local zeta integral at the real place; the factor at a
finite place p is zeta_p(s) = (1 - p^-s)^(-1), and prod_p zeta_p(s) = zeta(s).)

The Freund-Witten adelic product formula (Phys. Lett. B199 (1987) 191) shows
the archimedean Veneziano amplitude equals the reciprocal of the product of
its p-adic analogues: A_inf * prod_p A_p = 1.  This script tests the analogous
conjecture for the cascade: that the empirical corrections to cascade
leading-order quantities are finite-place compensators

    delta(ln X) = eps * ln zeta(d+1),   eps in {+1, -1},

with d the cascade layer carrying X (layer assignments from the papers /
src/generated/cascade_g_eff.json), zeta the Riemann zeta function.

Parts
-----
  A. Identity verification: Omega(d) = 2/Gamma_R(d+1), p(d) = (ln Gamma_R)'.
  B. The compensator menu: ln zeta(s) for s = 3..24, with closed forms at
     even s and leading-prime dominance.
  C. Strict Freund-Witten scorecard: deterministic layer-based compensators
     vs the signed needed shifts of the nine correction-family observables
     (same leads/sigmas as cascade_null_model_surprisal.py Part E).
  D. Head-to-head: the zeta-grid {|ln zeta(s)|, s=3..24} vs the papers'
     alpha(d*)/chi^k grid, scored with the identical P(any)/bits machinery.
  E. Exact-residual tests: 1/alpha_em (lead formula residual known to ~1e-10)
     and rho_Lambda (adelic correction size vs observational error).

Verdict conventions match the surprisal audit: a "hit" must land within the
observational sigma of the needed shift; freedom actually exercised (the sign
eps, dropping a layer's factor) is charged in bits.
"""

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import R, alpha, Omega, p  # noqa: E402

try:
    from scipy.special import zeta as _zeta
    def zeta(s):
        return float(_zeta(s))
except ImportError:  # plain-python fallback, fine for s >= 3
    def zeta(s, terms=200000):
        return sum(n ** -float(s) for n in range(1, terms))

PI = math.pi
SQRTPI = math.sqrt(PI)
E = math.e
CHI = 2.0


def Nl(d):
    """Papers' lapse N(d) = sqrt(pi) * R(d)."""
    return SQRTPI * R(d)


def Phi(a, b):
    return sum(p(d) for d in range(a, b + 1))


def Gamma_R(s):
    return PI ** (-s / 2.0) * math.gamma(s / 2.0)


def lnz(s):
    return math.log(zeta(s))


# ---------------------------------------------------------------------------
# Part A: identities
# ---------------------------------------------------------------------------

def part_A():
    print("=" * 78)
    print("PART A: the cascade IS the archimedean place (exact identities)")
    print("=" * 78)
    worst_o = worst_p = 0.0
    for d in (2, 3, 4, 5, 7, 11, 12, 13, 14, 19, 21):
        o1, o2 = Omega(d), 2.0 / Gamma_R(d + 1)
        h = 1e-6
        dp = (math.log(Gamma_R(d + 1 + h)) - math.log(Gamma_R(d + 1 - h))) / (2 * h)
        worst_o = max(worst_o, abs(o1 / o2 - 1))
        worst_p = max(worst_p, abs(p(d) - dp))
    print(f"  Omega(d) = 2/Gamma_R(d+1):    max rel. deviation {worst_o:.1e}")
    print(f"  p(d) = (ln Gamma_R)'(d+1):    max abs. deviation {worst_p:.1e}")
    print("  => every cascade primitive is the local zeta factor at the real")
    print("     place (Tate); the finite-place partners are zeta_p(s) = ")
    print("     (1-p^-s)^-1 with prod_p zeta_p(s) = zeta(s).")


# ---------------------------------------------------------------------------
# Part B: the compensator menu
# ---------------------------------------------------------------------------

EVEN_CLOSED = {6: "pi^6/945", 8: "pi^8/9450", 14: "2 pi^14/18243225",
               22: "zeta(22) = rational * pi^22"}


def part_B():
    print()
    print("=" * 78)
    print("PART B: finite-place compensators ln zeta(s), s = d+1 at cascade layers")
    print("=" * 78)
    print(f"{'s':>4} {'layer d':>8} {'zeta(s)-1':>12} {'ln zeta(s)':>12}"
          f" {'2^-s share':>11}  closed form / layer content")
    layers = {6: "d=5 Gen3 (tau,b,nu_tau)", 13: "d=12 SU(3)",
              14: "d=13 SU(2)+Higgs+Gen2", 15: "d=14 U(1)",
              20: "d=19 threshold", 22: "d=21 Gen1 (e,d,u)"}
    for s in range(3, 25):
        z = zeta(s)
        share = 2.0 ** -s / (z - 1)
        tag = layers.get(s, "")
        cf = EVEN_CLOSED.get(s, "")
        note = " ".join(x for x in (cf, tag) if x)
        print(f"{s:>4} {('d=%d' % (s-1)) if s-1 in (5,7,12,13,14,19,21) else '':>8}"
              f" {z-1:>12.3e} {lnz(s):>12.3e} {share:>11.1%}  {note}")
    print("  note: fermion layers (5, 13, 21) sit at EVEN s => compensators are")
    print("  rational multiples of pi^s (classical Euler values); gauge layers")
    print("  (12, 14) sit at ODD s => compensators are the odd zeta values")
    print("  zeta(13), zeta(15) (Apery-class transcendentals).")


# ---------------------------------------------------------------------------
# Part C: strict Freund-Witten scorecard
# ---------------------------------------------------------------------------

def needed_shifts():
    """Signed needed shifts ln(observed/lead), same leads as the surprisal
    audit Part E.  Layer content per papers / cascade_g_eff.json."""
    a_s_lead = alpha(12) * math.exp(Phi(5, 12))
    mtmu_lead = math.exp(Phi(6, 13)) * 2 * SQRTPI
    s2w_lead = R(14) ** 2 / (PI * R(13) ** 2 + R(14) ** 2)
    thC_lead = math.degrees(math.atan(
        math.tan(math.acos(Nl(13) / Nl(12))) * math.exp(-p(13) / 2)))
    bs_lead = mtmu_lead * E
    mmue_lead = math.exp(Phi(13, 21)) * 2 * SQRTPI
    # (name, signed needed shift, sigma, layers involved (s = d+1))
    return [
        ("alpha_s",    math.log(0.1179 / a_s_lead),  0.0009 / 0.1179,  [13]),
        ("m_tau/m_mu", math.log(16.81703 / mtmu_lead), 0.00114 / 16.81703,
         [6, 14]),
        ("m_tau abs",  math.log(1776.86 / 1754.20),  0.12 / 1776.86,   [6]),
        ("sin2thW",    math.log(0.23121 / s2w_lead), 0.00004 / 0.23121,
         [14, 15]),
        ("theta_C",    math.log(13.04 / thC_lead),   0.05 / 13.04,     [14, 22]),
        ("m_mu/m_e",   math.log(206.76828 / mmue_lead), 206.77 * 3e-8 / 206.77,
         [14, 22]),
        ("b/s",        math.log(44.75 / bs_lead),    0.005,            [6, 14]),
    ]


def variants(ss):
    """All eps-assignments over the involved layers, incl. dropping factors.
    Returns list of (label, value, freedom_bits)."""
    out = []
    if len(ss) == 1:
        s = ss[0]
        for eps in (1, -1):
            out.append((f"{'+' if eps>0 else '-'}ln z({s})", eps * lnz(s), 1.0))
    else:
        s1, s2 = ss
        for e1 in (1, -1):
            for e2 in (1, -1, 0):
                if e2 == 0:
                    lab = f"{'+' if e1>0 else '-'}ln z({s1}) [drop z({s2})]"
                    fb = 2.0
                else:
                    lab = (f"{'+' if e1>0 else '-'}ln z({s1})"
                           f"{'+' if e2>0 else '-'}ln z({s2})")
                    fb = 2.0
                out.append((lab, e1 * lnz(s1) + (e2 * lnz(s2) if e2 else 0.0),
                            fb))
    return out


def part_C():
    print()
    print("=" * 78)
    print("PART C: strict Freund-Witten scorecard (layer-deterministic)")
    print("=" * 78)
    print("  conjecture: delta ln X = sum over X's layers of eps ln zeta(d+1)")
    print("  a hit requires |compensator - needed| < 1 sigma; the sign eps and")
    print("  any dropped factor are charged as freedom bits.")
    print()
    print(f"{'observable':<12}{'needed':>10}{'sigma':>9}  best variant"
          f"{'':<18}{'value':>10}{'|diff|/sig':>11}{'freedom':>8}")
    for name, need, sig, ss in needed_shifts():
        best = min(variants(ss), key=lambda v: abs(v[1] - need))
        lab, val, fb = best
        ns = abs(val - need) / sig
        verdict = "HIT" if ns < 1 else ("near" if ns < 3 else "miss")
        print(f"{name:<12}{need:>10.5f}{sig:>9.5f}  {lab:<28}{val:>10.5f}"
              f"{ns:>11.2f}{fb:>7.1f}b  {verdict}")
    print()
    print("  m_tau/m_mu detail (tau@d=5, mu@d=13):")
    need = math.log(16.81703 / (math.exp(Phi(6, 13)) * 2 * SQRTPI))
    sig = 0.00114 / 16.81703
    for lab, val in [("ln z(6)          (drop mu factor)", lnz(6)),
                     ("ln z(6) - ln z(14)  (ratio, canonical)",
                      lnz(6) - lnz(14)),
                     ("ln z(6) + ln z(14)", lnz(6) + lnz(14)),
                     ("papers' alpha(14)/2", alpha(14) / 2)]:
        print(f"    {lab:<40} {val:.6f}   needed {need:.6f}"
              f"   |diff|/sig = {abs(val-need)/sig:.2f}")


# ---------------------------------------------------------------------------
# Part D: zeta-grid vs alpha-grid head-to-head
# ---------------------------------------------------------------------------

def p_any(sig, grid, L):
    return min(1.0, sum(2 * sig / (g * L) for g in grid))


def part_D():
    print()
    print("=" * 78)
    print("PART D: head-to-head  |ln zeta(s)| grid  vs  alpha(d*)/chi^k grid")
    print("=" * 78)
    zgrid = sorted(lnz(s) for s in range(3, 25))
    agrid = sorted(alpha(d) / CHI ** k for d in (5, 7, 14, 19)
                   for k in (1, 2, 3, 4))
    span_lo = min(min(zgrid), min(agrid)) / 1.5
    span_hi = max(max(zgrid), max(agrid)) * 1.5
    L = math.log(span_hi / span_lo)
    rows = needed_shifts()
    print(f"  common null span [{span_lo:.5f}, {span_hi:.5f}] ln-width {L:.2f}")
    print(f"  zeta grid: 22 members in [{zgrid[0]:.5f}, {zgrid[-1]:.5f}]")
    print(f"  alpha grid: 16 members in [{agrid[0]:.5f}, {agrid[-1]:.5f}]")
    print()
    print(f"{'observable':<12}{'|needed|':>10}"
          f"{'zeta best':>11}{'z|d|/sig':>9}{'z bits':>7}"
          f"{'alpha best':>12}{'a|d|/sig':>9}{'a bits':>7}")
    zt = at = 0.0
    for name, need, sig, _ in rows:
        an = abs(need)
        zb = min(zgrid, key=lambda g: abs(g - an))
        ab = min(agrid, key=lambda g: abs(g - an))
        zs, as_ = abs(zb - an) / sig, abs(ab - an) / sig
        pz = p_any(sig, zgrid, L) if zs < 1 else 1.0
        pa = p_any(sig, agrid, L) if as_ < 1 else 1.0
        bz = -math.log2(pz) if pz < 1 else 0.0
        ba = -math.log2(pa) if pa < 1 else 0.0
        zt += bz
        at += ba
        print(f"{name:<12}{an:>10.5f}{zb:>11.5f}{zs:>9.2f}{bz:>7.2f}"
              f"{ab:>12.5f}{as_:>9.2f}{ba:>7.2f}")
    print(f"  total bits (hits only):    zeta grid {zt:.1f}"
          f"    alpha grid {at:.1f}")


# ---------------------------------------------------------------------------
# Part E: exact residuals
# ---------------------------------------------------------------------------

def part_E():
    print()
    print("=" * 78)
    print("PART E: exact-residual tests")
    print("=" * 78)
    lead = 1 / alpha(13) + PI / alpha(14) + 6 * PI
    obs = 137.035999084
    need = math.log(obs / lead)
    print(f"  1/alpha_em: lead {lead:.6f}, observed {obs:.6f}")
    print(f"    needed relative residual: {need:+.4e}  (known to ~1e-10)")
    for lab, val in [("+ln zeta(14)  [mu layer d=13]", lnz(14)),
                     ("+ln zeta(15)  [U(1) layer d=14]", lnz(15)),
                     ("+ln zeta(14)+ln zeta(15)", lnz(14) + lnz(15)),
                     ("+ln zeta(14)-ln zeta(15)", lnz(14) - lnz(15))]:
        print(f"    {lab:<32} {val:+.4e}"
              f"   off by {(val-need)/need:+7.1%} of the residual")
    print("    verdict: MISS at infinite precision (closest candidate off by")
    print("    ~8% of the residual; measurement error is 4 orders smaller).")
    print()
    z20, lnz218 = zeta(20), math.log1p(2.0 ** -218)  # zeta(218)-1 ~ 2^-218
    print(f"  rho_Lambda: invariant uses Gamma_R(20), Gamma_R(218);")
    print(f"    adelic compensators ln zeta(20) = {math.log(z20):.2e},"
          f" ln zeta(218) = {lnz218:.2e}")
    print(f"    combined ~ 1e-6 relative; observational error is 1.9e-2.")
    print("    verdict: UNTESTABLE (prediction: no visible adelic shift in")
    print("    Lambda -- consistent by 4 orders of magnitude of slack).")


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    print()
    print("done.")
