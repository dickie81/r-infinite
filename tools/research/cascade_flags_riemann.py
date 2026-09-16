#!/usr/bin/env python3
"""
The source-selection flags derived from the factorisation of xi.

Part IVb's source-selection rule (part4b:1543-1661) classifies each
observable by three syntactic flags (P, L, G) and assigns the correction
source layer d* in {5, 7, 14, 19}.  Open Question 3 asks for a formal
derivation of the flags.  This tool constructs and verifies the Riemann
form of that derivation:

    xi(s) = (s-1) * [(s/2) Gamma_R(s)] * zeta(s)
             pole    regularised          Euler
                     archimedean          product

A purely archimedean theory (the cascade: Addendum 1 showed its closing
formulas contain no finite-place content) has an alphabet with exactly
three xi-occupancy classes:
    1. the absolute anchor M_Pl,red        <-> the pole factor
       (the unique scale-freedom breaker; residue of zeta at 1 = the
        unit of counting; M_Pl = the unit of measure),
    2. static Gamma_R point-values (N, Omega, alpha at layers),
    3. Gamma_R interval-ratios (descent exponentials exp Phi(a->b)),
       with one distinguished interval: the gauge window {12,13,14}
       (Adams' theorem -- the single topological, non-xi-analytic input).

The flags are the occupancy functors:  P = touches class 1;
L = touches ONLY class 2;  G = class-3 content meets the window.
No fourth flag exists because the fourth xi-component (the Euler
product) has no occupancy in any closing cascade formula -- exactly
Addendum 1's empirical result.  The four source layers are the four
distinguished features of the archimedean factor:

    d_0 = 7  : critical point of the BARE factor 1/Gamma_R(s)
               (equivalently the unique zero of the attenuation rate:
                amplitude-class observables source where attenuation
                vanishes),
    d_V = 5  : critical point of the POLE-DRESSED factor
               (2/s)/Gamma_R(s) = V(d) (the measure maximum: where the
                observer sits; static observables source at the point
                feature),
    d_1 = 19 : descent rate p(d) crosses ln Gamma(1/2) -- the log
               threshold of the critical-line constant (gateway of the
               19->217 hierarchy span that manufactures the absolute
               scale; pole-class observables source here),
    d_2 = 217: p(d) crosses Gamma(1/2) itself -- the sink (terminus,
               excluded as source, matching the papers),
    d_gw = 14: gauge-window boundary (Adams; the topological import).

Parts: A verifies the exact identities; B locates the four features;
C re-derives the nine flag rows mechanically from xi-occupancy;
D records the residual gaps found (including one internal tension in
the papers' own flag reading for b/s and theta_23).
"""

import math

from scipy.special import digamma

SQRTPI = math.sqrt(math.pi)


def Gamma_R(s):
    return math.pi ** (-s / 2.0) * math.gamma(s / 2.0)


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def part_A():
    print("=" * 74)
    print("PART A: the alphabet's xi-identities (exact)")
    print("=" * 74)
    worst_v = worst_a = 0.0
    for d in range(2, 30):
        V = math.pi ** (d / 2.0) / math.gamma(d / 2.0 + 1)
        A = 2 * math.pi ** (d / 2.0) / math.gamma(d / 2.0)
        worst_v = max(worst_v, abs(V * Gamma_R(d) * d / 2.0 - 1))
        worst_a = max(worst_a, abs(A * Gamma_R(d) / 2.0 - 1))
    print(f"  V(d) = (2/s)/Gamma_R(s):  max rel dev {worst_v:.1e}")
    print(f"  A(d) = 2/Gamma_R(s):      max rel dev {worst_a:.1e}")
    print("  descent exponentials exp Phi(a->b) = interval content of")
    print("  (log Gamma_R)' summed over layers: class-3 objects by")
    print("  construction (p(d) = (log Gamma_R)'(d+1), verified Add.2).")


def bisect(f, lo, hi):
    for _ in range(200):
        mid = (lo + hi) / 2.0
        if f(lo) * f(mid) <= 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2.0


def part_B():
    print()
    print("=" * 74)
    print("PART B: the four source layers as features of the factorisation")
    print("=" * 74)
    # critical point of bare 1/Gamma_R(s): d/ds log Gamma_R = 0
    dlog = lambda s: -0.5 * math.log(math.pi) + 0.5 * digamma(s / 2.0)
    s0 = bisect(dlog, 2, 20)
    # critical point of pole-dressed (2/s)/Gamma_R(s)
    dlogV = lambda s: dlog(s) + 1.0 / s
    sV = bisect(dlogV, 2, 20)
    d1 = bisect(lambda d: p(d) - math.log(SQRTPI), 5, 40)
    d2 = bisect(lambda d: p(d) - SQRTPI, 50, 400)
    print(f"  bare archimedean critical point:    s = {s0:.4f}  -> d_0  = 7")
    print(f"  pole-dressed critical point:        s = {sV:.4f}  -> d_V  = 5")
    print(f"  p(d) = ln Gamma(1/2):               d = {d1:.4f}  -> d_1  = 19")
    print(f"  p(d) = Gamma(1/2):                  d = {d2:.4f}  -> d_2  = 217"
          f" (sink, excluded)")
    print(f"  gauge window {{12,13,14}}: Adams' theorem -- the one input the")
    print(f"  factorisation of xi does not supply (topological import).")
    print(f"  note: the two critical points differ by {s0-sV:.4f} (~2: the")
    print(f"  pole dressing shifts the stationary dimension by two layers).")


# ---- Part C: mechanical re-derivation of the nine flag rows ------------
# ingredient encoding: ('MPL',), ('static', layer), ('exp', a, b) for
# multi-layer descent exponentials, ('exp1', layer) for single-layer
# attenuation.  Canonical formulas per the papers' leads.
FORMULAS = {
    "alpha_s":    [("static", 12), ("exp", 5, 12)],
    "m_tau/m_mu": [("exp", 6, 13), ("static", 14)],   # 2 sqrt(pi) = d=14 obstruction
    "m_tau abs":  [("MPL",), ("exp", 5, 19)],
    "ell_A":      [("MPL",), ("static", 4)],
    "sin2thW":    [("static", 13), ("static", 14)],
    "Omega_m":    [("static", 5)],
    "theta_C":    [("static", 12), ("static", 13), ("exp1", 13)],
    "b/s":        [("exp", 6, 13), ("static", 14), ("static", 7)],
    "theta_23":   [("exp", 6, 13), ("static", 7)],
}
PAPER = {"alpha_s": 14, "m_tau/m_mu": 14, "m_tau abs": 19, "ell_A": 19,
         "sin2thW": 5, "Omega_m": 5, "theta_C": 7, "b/s": 7, "theta_23": 7}
WINDOW = {12, 13, 14}


def classify(ing):
    P = any(t[0] == "MPL" for t in ing)
    has_exp = any(t[0] in ("exp", "exp1") for t in ing)
    L = not has_exp
    G = any(t[0] == "exp" and set(range(t[1], t[2] + 1)) & WINDOW
            for t in ing)
    if P:
        return (P, L, G), 19
    if L:
        return (P, L, G), 5
    if G:
        return (P, L, G), 14
    return (P, L, G), 7


def part_C():
    print()
    print("=" * 74)
    print("PART C: nine flag rows from xi-occupancy")
    print("=" * 74)
    print(f"  {'observable':<12}{'(P,L,G)':>12}{'xi-derived d*':>14}"
          f"{'paper d*':>10}")
    agree = 0
    for name, ing in FORMULAS.items():
        flags, dstar = classify(ing)
        ok = dstar == PAPER[name]
        agree += ok
        f = "".join("T" if x else "F" for x in flags)
        print(f"  {name:<12}{f:>12}{dstar:>14}{PAPER[name]:>10}"
              f"   {'ok' if ok else '** TENSION **'}")
    print(f"  agreement: {agree}/9")


def part_D():
    print()
    print("=" * 74)
    print("PART D: residual gaps (recorded honestly)")
    print("=" * 74)
    print("  1. b/s and theta_23: their published leads CONTAIN the gauge-")
    print("     window exponential exp Phi(6->13) (b/s = (m_tau/m_mu) e),")
    print("     so the mechanical xi-occupancy reading gives G = T ->")
    print("     d* = 14, while the papers read G = F and assign d* = 7,")
    print("     invoking the 'minimal descent formula' caveat.  The caveat")
    print("     is load-bearing residual freedom in a reading advertised as")
    print("     mechanical: an internal tension for the papers to resolve")
    print("     (state the canonical F_Q for b/s, theta_23 explicitly).")
    print("  2. The gauge window itself is Adams/topological, not")
    print("     xi-analytic: one imported input.")
    print("  3. The decision order P > L > G is motivated (most-global")
    print("     ingredient wins) but not forced by the factorisation.")
    print("  4. No-fourth-flag: forced RELATIVE to xi's factorisation --")
    print("     the fourth component (Euler product) has no occupancy in")
    print("     any closing formula, which is Addendum 1's empirical kill")
    print("     restated as the reason the flag count is three.")


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
    part_D()
