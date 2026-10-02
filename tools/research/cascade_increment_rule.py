#!/usr/bin/env python3
"""
THE INCREMENT RULE DERIVED FROM THE FACTORISATION OF xi.

Rule (as used, Addenda 13-29 and papers' phase family): a closing
observable's cascade expression carries AT MOST ONE member of the
correction family exp(+-alpha(d*)/chi^(k-m)), at FIRST power, sourced
at the unique analytic feature of its xi-occupancy class; point-class
(local-constant) content carries none ("sub-leads raw").

DERIVATION, five steps (grades marked; numerics below):

S1 (Partition -- xi-native exclusivity) [structural].
   log xi = log(s(s-1)/2) + log Gamma_R + log zeta is a PARTITION of
   one analytic object.  A12 derived the flags P/L/G as the occupancy
   functors of this partition; an observable's correction is its
   class's share of d log xi.  Drawing members from two summands for
   one observable double-counts d log xi -- the xi-form of the papers'
   slot-precedence exclusivity (prop:slot-precedence: 'adding both
   would double-count the same underlying loop contribution').
   => at most one source class per observable.

S2 (Residue-increment correspondence) [rigorous in the second-
   quantised theory, A25/T2].  The correction sourced at layer d* is
   the marginal-Green increment G(d*) - G(d*+1) = alpha(d*), exact;
   the chirality grading distributes it over sectors as chi^(m-k)
   (papers' chirality selection rule, thm at part4b:1291-1314, whose
   proof composes open-line filters chi^-k and closed-loop traces
   chi^m with zero cross-terms).

S3 (Simplicity lemma) [RIGOROUS -- trigamma positivity].
   Every analytic feature of xi's archimedean summands has order one:
     - the pole of zeta at s=1 is simple (classical);
     - the poles of Gamma_R are simple (Gamma's poles are);
     - (log A)'(s) = -P(s) with P(s) = (log Gamma_R)'(s): since
       P'(s) = psi'(s/2)/4 > 0 (trigamma positivity), (log A)' is
       strictly decreasing => the area feature s_0 = 7.2569 is the
       UNIQUE critical point and is NONDEGENERATE; the exact
       recursion (log V)'(s) = (log A)'(s+2) (psi(x+1) = psi(x)+1/x)
       transports uniqueness+nondegeneracy to the volume feature
       s_V = 5.2569;
     - P(s) strictly increasing => the threshold crossings
       P = ln Gamma(1/2) (d_1 = 19) and P = Gamma(1/2) (d_2 = 217)
       are TRANSVERSAL (first derivative nonzero) and unique.
   A feature of order one contributes its increment to the FIRST
   power; a squared member would require a double feature, which the
   factorisation does not possess.

S4 (Monotonicity) [definitional].  The descent lattice is totally
   ordered; a descent path crosses each layer at most once.  Combined
   with S2's telescoping (site variances = accumulated bond
   compliances), a feature's increment enters an observable's window
   at most once -- verified below by single-site perturbation of the
   sink-pinned chain: the shift is linear (first power), equal to the
   increment, present iff the window spans the site, and independent
   of window length.

S5 (Conclusion).  One class (S1) x one feature per class in scope
   (A12's assignment) x first order (S3) x at most one crossing (S4)
   = at most one member, first power.  L-class content occupies no
   interval, crosses no feature => raw.                        QED*

*Tier-2, the same grade as the flags derivation: inherited joints are
the P > L > G precedence (motivated, not forced -- A12), the gauge
window's topological origin (Adams), and the papers' chirality-rule
proof.  The rule is thereby moved from AXIOM (A3, gap #1 of the
formulation) to DERIVED-AT-TIER-2, conditional on those joints.
"""

import math

import numpy as np
from scipy.optimize import brentq
from scipy.special import polygamma, digamma

LNPI = math.log(math.pi)
SQRTPI = math.sqrt(math.pi)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def P(s):                            # (log Gamma_R)'(s)
    return 0.5 * digamma(s / 2.0) - 0.5 * LNPI


def Pp(s):                           # P'(s) = psi'(s/2)/4 > 0
    return 0.25 * polygamma(1, s / 2.0)


def part_S3():
    print("=" * 74)
    print("S3: simplicity of the four features (trigamma positivity)")
    print("=" * 74)
    # area feature: (log A)'(s) = -P(s) = 0
    s0 = brentq(P, 2.1, 20.0)
    print(f"  area feature:   (log A)' = 0 at s_0 = {s0:.4f}"
          f"   (log A)'' = {-Pp(s0):+.5f}  (nonzero, unique: P' > 0)")
    # volume feature: (log V)'(s) = -1/s - ... = (log A)'(s+2), exact
    f = lambda s: -1.0 / s - P(s)
    sV = brentq(f, 2.1, 20.0)
    fpp = 1.0 / sV ** 2 - Pp(sV)
    print(f"  volume feature: (log V)' = 0 at s_V = {sV:.4f}"
          f"   (log V)'' = {fpp:+.5f}  (nonzero)")
    print(f"  exact recursion check: s_0 - s_V = {s0-sV:.10f}  (= 2 by"
          f" psi(x+1) = psi(x) + 1/x)")
    # thresholds: P crosses ln G(1/2) and G(1/2), transversally
    for name, lvl, lo, hi, dstar in [
            ("d_1", math.log(SQRTPI), 10, 40, 19),
            ("d_2", SQRTPI, 100, 400, 217)]:
        sc = brentq(lambda s: P(s) - lvl, lo, hi)
        print(f"  threshold {name}:  P(s) = {lvl:.4f} at s = {sc:.3f}"
              f" (layer {dstar} = last below)   P'(s) = {Pp(sc):.2e} > 0:"
              f" transversal")
    print("  => all features order ONE: members enter at first power.")


def part_S4():
    print()
    print("=" * 74)
    print("S4: single-site perturbation of the sink-pinned chain")
    print("=" * 74)
    d_lo, d_hi, dstar, eps = 4, 30, 7, 1e-6
    ds = list(range(d_lo, d_hi + 1))
    n = len(ds)

    def greens(perturb):
        L = np.zeros((n, n))
        for i in range(n - 1):
            a = alpha(ds[i]) * (1 + (eps if perturb and ds[i] == dstar
                                     else 0.0))
            w = 1.0 / a
            L[i, i] += w
            L[i + 1, i + 1] += w
            L[i, i + 1] -= w
            L[i + 1, i] -= w
        L[-1, -1] += 1e9
        return np.linalg.inv(L)

    G0, G1 = greens(False), greens(True)
    print(f"  perturb alpha({dstar}) -> alpha({dstar})(1+eps), eps = {eps}")
    print(f"  {'window [a,b]':<16}{'spans d*?':>10}{'shift/eps':>14}"
          f"{'alpha(d*)':>12}")
    for a, b in [(4, 10), (4, 20), (4, 30), (6, 9), (5, 8), (8, 20),
                 (10, 30), (4, 7)]:
        ia, ib = ds.index(a), ds.index(b)
        shift = ((G1[ia, ia] - G1[ib, ib]) - (G0[ia, ia] - G0[ib, ib])) / eps
        spans = a <= dstar < b
        print(f"  [{a:>2},{b:>3}]{'':<8}{str(spans):>10}{shift:>14.6f}"
              f"{alpha(dstar) if spans else 0.0:>12.6f}")
    print("  => shift = alpha(d*) x 1_(window spans d*), linear in eps,")
    print("     INDEPENDENT of window length: attach once, first power,")
    print("     only in scope.  (Telescoping: G(a)-G(b) = sum of bond")
    print("     compliances; a single site contributes a single term.)")


def part_S5():
    print()
    print("=" * 74)
    print("S5: the one-member audit across the papers' closed family")
    print("=" * 74)
    rows = [
        ("b/s", "-alpha(7)/chi^4", -alpha(7) / 16),
        ("sin^2 theta_W", "+alpha(5)/chi^3", alpha(5) / 8),
        ("Omega_m", "-alpha(5)/chi^3", -alpha(5) / 8),
        ("theta_C", "-alpha(7)/chi^2", -alpha(7) / 4),
        ("alpha_s", "+alpha(14)/chi", alpha(14) / 2),
        ("m_tau/m_mu", "+alpha(14)/chi", alpha(14) / 2),
        ("m_tau abs", "+alpha(19)/chi", alpha(19) / 2),
        ("ell_A", "+alpha(19)/chi", alpha(19) / 2),
        ("m_mu/m_e", "NONE (L-class: radiative slot m-k=0)", 0.0),
    ]
    for name, member, val in rows:
        print(f"  {name:<15} {member:<38} {val:+.6f}" if val else
              f"  {name:<15} {member}")
    print("  => every closed observable: exactly one member or none, first")
    print("     power, one source layer -- no squared member, no stacked")
    print("     sources, anywhere in the family.  The reuse pairs share")
    print("     one feature across two observables (permitted: S1 is a")
    print("     per-observable exclusion), never two features on one.")


if __name__ == "__main__":
    part_S3()
    part_S4()
    part_S5()
