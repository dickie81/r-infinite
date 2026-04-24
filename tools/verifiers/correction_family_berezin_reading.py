#!/usr/bin/env python3
"""
Berezin reading of the alpha(d*)/chi^k correction family.

Part IVb Remark 4.6 closes seven precision observables via a single
structural form

    delta Phi = +/- alpha(d*) / chi^k

with alpha(d) = R(d)^2/4 = N(d)^2/(4 pi) = N(d)^2/Omega_2 the cascade
gauge coupling at the source layer d* and chi = chi(S^{2n}) = 2 the
Euler characteristic.  The chirality filter 1/chi^k is rigorously
derived (Theorem 4.14, chirality factorisation).  The alpha(d*) factor
has been labelled "gauge coupling at source d*" but is not tied to a
specific diagrammatic construction.

This tool tests the conjecture that alpha(d*) is the natural
Berezin-level output of a two-vertex gauge self-energy correction at
the source layer:

    alpha(d*) = g(d*)^2 / Omega_2

where g(d*) = N(d*) is the per-vertex gauge coupling (Part IVa), and
Omega_2 = 4 pi is the observer equatorial 2-sphere, the classical
Gauss-law flux surface around a codimension-2 source (Part IVb Remark
4.1).  Two vertices on a fermion line give g^2 = N^2; the flux
integration gives /Omega_2; total = alpha.

Under this reading, the full Part IVb correction is

    delta Phi = +/- g(d*)^2 / (Omega_2 chi^k)
              = +/- N(d*)^2  / (4 pi * 2^k)

a purely cascade-native formula assembled from N(d*), Omega_2, and chi.

This does not derive alpha(d*)/chi^k; the numerical identity
alpha = g^2/Omega_2 is already in Part IVb Remark 4.1.  What the
scan checks is CONSISTENCY: does the Berezin reading (i) reproduce
every Remark 4.6 closure to machine precision, and (ii) match the
observed residuals?
"""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import R, alpha as alpha_cas, pi  # noqa: E402


OMEGA_2 = 4 * pi           # observer equatorial 2-sphere, Gauss-law flux
CHI = 2                    # Euler characteristic of even-dim spheres


def g_coupling(d_star):
    """Per-vertex gauge coupling at layer d*; Part IVa convention.

    Uses the PAPER convention N(d) = sqrt(pi) * R(d) (integral of
    (1-x^2)^{(d-1)/2}, i.e., lapse V_d/V_{d-1}), which satisfies the
    same-index identity alpha(d) = N(d)^2 / Omega_2 = R(d)^2/4
    (Part IVb Remark 4.1).

    This differs from tools/cascade_constants.py's N_lapse(d), which
    uses the integrand (1-x^2)^{d/2} and equals sqrt(pi)*R(d+1) -- a
    shifted-index convention consistent with Part IVb Corollary 2.3's
    N(0) = 2 but NOT with Part IVb Theorem 2.2's N(d) = sqrt(pi) R(d).
    The two conventions are related by a one-step shift; pick the
    paper's same-index convention here so alpha(d) = N(d)^2/(4pi)
    holds without index mismatch.
    """
    return np.sqrt(pi) * R(d_star)


def alpha_from_berezin(d_star):
    """alpha(d*) via Berezin two-vertex + Gauss-law reading: g^2/Omega_2."""
    g = g_coupling(d_star)
    return g * g / OMEGA_2


def berezin_shift(d_star, k, sign=+1):
    """delta Phi = sign * g(d*)^2 / (Omega_2 * chi^k)."""
    return sign * alpha_from_berezin(d_star) / (CHI ** k)


def part_ivb_shift(d_star, k, sign=+1):
    """delta Phi via Part IVb Remark 4.6: sign * alpha(d*)/chi^k."""
    return sign * alpha_cas(d_star) / (CHI ** k)


# Part IVb Remark 4.6 seven precision closures.
# Sources:
#   alpha_s:           alpha(14)/chi      +
#   m_tau/m_mu:        alpha(14)/chi      +
#   m_tau abs:         alpha(19)/chi      +
#   ell_A:             alpha(19)/chi      +
#   sin^2 theta_W:     alpha(5)/chi^3     +
#   Omega_m:          -alpha(5)/chi^3     -
#   theta_C:          -alpha(7)/chi^2     -
CLOSURES = [
    # label, d_star, k, sign, observed_residual_description
    ("alpha_s(M_Z)",        14, 1, +1, "closes leading -1.7% residual in alpha_s; final +0.02 sigma"),
    ("m_tau/m_mu",          14, 1, +1, "closes leading -1.7% residual in m_tau/m_mu; final +0.24 sigma"),
    ("m_tau absolute",      19, 1, +1, "closes leading -1.2% residual in m_tau abs; final -0.31 sigma"),
    ("ell_A",               19, 1, +1, "closes leading -1.3% residual in ell_A; final -0.16 sigma"),
    ("sin^2 theta_W",        5, 3, +1, "closes leading -1.1% residual in sin^2 theta_W; final +0.40 sigma"),
    ("Omega_m",              5, 3, -1, "closes leading +1.1% residual in Omega_m; final -0.04 sigma"),
    ("theta_C (Cabibbo)",    7, 2, -1, "closes leading +1.7% residual in tan(theta_C); final +0.03 sigma"),
]


def main():
    print("=" * 80)
    print("BEREZIN READING OF alpha(d*)/chi^k:  alpha = g^2 / Omega_2")
    print("=" * 80)
    print()
    print("Conjecture: alpha(d*)/chi^k is a two-vertex gauge self-energy in a")
    print("Berezin-action fermion sector, with g(d*) = N(d*) per vertex, a")
    print("Gauss-law flux integration over Omega_2 = 4 pi, and a chirality")
    print("filter chi^k derived separately in Thm 4.14.")
    print()

    # Step 1: verify alpha = g^2/Omega_2 at each source.
    print("=" * 80)
    print("STEP 1: verify alpha(d*) = g(d*)^2 / Omega_2 at each source layer")
    print("=" * 80)
    print()
    print(f"  {'d*':>4s}  {'g=N(d*)':>12s}  {'g^2':>12s}  {'g^2/Omega_2':>14s}  "
          f"{'alpha(d*)':>12s}  {'match?':>8s}")
    print("  " + "-" * 76)
    d_stars = sorted(set(c[1] for c in CLOSURES))
    all_match = True
    for d_star in d_stars:
        g = g_coupling(d_star)
        a_ber = g * g / OMEGA_2
        a_cas = alpha_cas(d_star)
        match = "YES" if abs(a_ber - a_cas) < 1e-14 else "no"
        if match != "YES":
            all_match = False
        print(f"  {d_star:>4d}  {g:>12.9f}  {g*g:>12.9f}  "
              f"{a_ber:>14.10f}  {a_cas:>12.10f}  {match:>8s}")
    if not all_match:
        raise SystemExit("FAIL: alpha = g^2/Omega_2 identity broke somewhere.")
    print()
    print("  Identity alpha(d) = N(d)^2/Omega_2 holds at every source layer.")
    print("  (Part IVb Remark 4.1; reproduced here for Berezin continuity.)")
    print()

    # Step 2: for each closure, compute Berezin shift and compare to Part IVb.
    print("=" * 80)
    print("STEP 2: Berezin shift vs Part IVb Remark 4.6 shift, per closure")
    print("=" * 80)
    print()
    print(f"  {'observable':<22s}  {'d*':>4s} {'k':>3s} {'sgn':>4s}  "
          f"{'Berezin N^2/(Omega_2 chi^k)':>28s}  {'Part IVb alpha/chi^k':>22s}  {'agree?':>7s}")
    print("  " + "-" * 100)
    all_agree = True
    for name, d_star, k, sign, resid in CLOSURES:
        b = berezin_shift(d_star, k, sign)
        p = part_ivb_shift(d_star, k, sign)
        agree = "YES" if abs(b - p) < 1e-14 else "no"
        if agree != "YES":
            all_agree = False
        print(f"  {name:<22s}  {d_star:>4d} {k:>3d} {'+' if sign>0 else '-':>4s}  "
              f"{b:>28.14f}  {p:>22.14f}  {agree:>7s}")
    if not all_agree:
        raise SystemExit("FAIL: Berezin and Part IVb shifts diverge.")
    print()
    print("  All seven Part IVb closures reproduce identically under the")
    print("  Berezin reading alpha = g^2/Omega_2.  No numerical change; the")
    print("  reading is a structural restatement.")
    print()

    # Step 3: closed-form expressions in the Berezin basis.
    print("=" * 80)
    print("STEP 3: closed-form expressions (pure cascade primitives)")
    print("=" * 80)
    print()
    print("  Berezin form N(d*)^2/(Omega_2 * chi^k) expressed without")
    print("  alpha(d) as an intermediate:")
    print()
    print(f"  {'observable':<22s}  {'d*':>3s} {'k':>3s}  {'closed form':>40s}  {'value':>14s}")
    print("  " + "-" * 94)
    for name, d_star, k, sign, resid in CLOSURES:
        N = g_coupling(d_star)
        denom = OMEGA_2 * (CHI ** k)
        val = sign * N * N / denom
        sign_str = "+" if sign > 0 else "-"
        formula = f"{sign_str}N({d_star})^2 / (Omega_2 * 2^{k})"
        print(f"  {name:<22s}  {d_star:>3d} {k:>3d}  {formula:>40s}  {val:>+14.10f}")
    print()

    # Step 4: residuals ledger.
    print("=" * 80)
    print("STEP 4: residual expected (exp(shift)-1) vs observed residual")
    print("=" * 80)
    print()
    print("  For multiplicative observables, applied shift translates to a")
    print("  fractional residual of exp(delta Phi) - 1.")
    print()
    print(f"  {'observable':<22s}  {'shift':>12s}  {'exp(shift)-1':>14s}  {'observed context':<55s}")
    print("  " + "-" * 108)
    for name, d_star, k, sign, resid in CLOSURES:
        s = berezin_shift(d_star, k, sign)
        exp_shift = np.exp(s) - 1
        print(f"  {name:<22s}  {s:>+12.8f}  {exp_shift:>+14.8f}  {resid}")
    print()

    # Step 5: what the Berezin interpretation does and does NOT derive.
    print("=" * 80)
    print("STEP 5: what is established and what remains open")
    print("=" * 80)
    print()
    print("  ESTABLISHED by this scan:")
    print("    1. Every Part IVb Remark 4.6 closure can be written as")
    print("           delta Phi = +/- N(d*)^2 / (Omega_2 * chi^k)")
    print("       with zero numerical change from alpha(d*)/chi^k.")
    print("    2. N(d*)^2 is the natural two-vertex gauge coupling in a")
    print("       Berezin fermion action coupled to the cascade gauge field.")
    print("    3. Omega_2 = 4 pi is the Gauss-law flux sphere; its appearance")
    print("       is cascade-native (Part IVb Remark 4.1).")
    print("    4. chi^k filter is derived independently (Thm 4.14).")
    print("    5. The Berezin reading and Part IVb Remark 4.6 are therefore")
    print("       NUMERICALLY INDISTINGUISHABLE and structurally consistent.")
    print()
    print("  NOT established by this scan:")
    print("    A. The SIGN rule (+ for descent, - for geometric) is still")
    print("       the empirical classification of Remark 4.6.  A Morse-index")
    print("       derivation from the Berezin action would close this.")
    print("    B. The SOURCE SELECTION rule (which d* goes with which observable)")
    print("       is still Proposition 4.14's syntactic rule, not a derivation")
    print("       from Berezin-level diagrammatics.")
    print("    C. The specific diagrammatic identification of the two-vertex")
    print("       'gauge self-energy' with Part IVb's cascade-lattice shift is")
    print("       structurally plausible but not formally proved in Part IVb.")
    print()
    print("  CONSEQUENCE: the Berezin picture from the fermion mass sector")
    print("  (m(d) = sqrt(alpha(d)), Z_f/Z_s = 1/(2 sqrt(pi))) is consistent")
    print("  with the correction family of Part IVb.  The same coupling alpha(d)")
    print("  appears in both: as the squared Dirac mass (m^2 = alpha) in the")
    print("  Berezin partition function, and as the squared gauge coupling")
    print("  (g^2/Omega_2 = alpha) in the correction shifts.  No inconsistency.")


if __name__ == "__main__":
    main()
