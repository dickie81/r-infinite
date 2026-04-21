#!/usr/bin/env python3
"""
Closure of alpha_s(M_Z), m_tau/m_mu, and m_tau absolute via cascade
potential shifts alpha(d*)/chi sourced at distinguished cascade layers.

Two independent identities, both of the form alpha(d*)/chi with chi=2:

  1. delta_Phi_U(1) = alpha(14)/chi = R(14)^2/8 = 429^2 pi/2^25
                    = 0.017231...
     acts on the cascade potential for observables whose path lies
     strictly below d=14. Closes:
       - alpha_s(M_Z) = alpha(12)*exp(Phi(12) + delta_Phi_U(1))
                      = 0.117917   (obs 0.1179 +/- 0.0009, +0.019 sigma)
       - m_tau/m_mu   = exp((Phi(13)-Phi(5)) + delta_Phi_U(1)) * 2sqrt(pi)
                      = 16.81731   (obs 16.81703 +/- 0.00114, +0.243 sigma)

  2. delta_Phi_phase = alpha(19)/chi = R(19)^2/8
                     = 0.012816...
     sourced at the phase-transition layer d_1 = 19 (Paper I threshold).
     Closes:
       - m_tau absolute = m_tau_lead * exp(delta_Phi_phase)
                        = 1776.82 MeV  (obs 1776.86 +/- 0.12, -0.31 sigma)

Both shifts use the same Euler characteristic chi(S^{2n}) = 2 that
appears in the 2*sqrt(pi) fermion obstruction identity
(Part IVb Corollary 2.2).  Both source layers (d=14 and d_1=19) are
distinguished dimensions from Paper I's four-dimension tower.

This is a cascade-structural FAMILY of alpha(d*)/chi shifts indexed by
Paper I's distinguished layers, each acting on a distinct class of
observables.  A first-principles derivation of the observable-class
selection rule (which d* for which class) is still open.

Generalisation tests against the chain propagation hypothesis (that a
single shift propagates through alpha_s -> v -> m_g) show it DOES NOT
work: v, m_mu, m_e, and other absolute scales do not close at
experimental precision under any integer power of delta_Phi_U(1).  The
correct structural picture is not propagation but a DIFFERENT shift
sourced at a different distinguished layer.
"""

import math
import os
import sys

# Shared cascade primitives.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import R, alpha as alpha_cascade, p, pi  # noqa: E402


def Phi(d, d_low=5):
    """Cumulative cascade potential Phi(d) = sum_{d'=d_low}^{d} p(d')."""
    return sum(p(dd) for dd in range(d_low, d+1))


def main():
    print("=" * 74)
    print("CASCADE SHIFT FAMILY: alpha(d*)/chi")
    print("=" * 74)

    # === The two shifts ===
    dPU1 = alpha_cascade(14)/2  # U(1) gauge layer
    dPphase = alpha_cascade(19)/2  # phase-transition layer

    print(f"\ndelta_Phi_U(1)   = alpha(14)/chi = R(14)^2/8 = {dPU1:.12f}")
    print(f"                  = 429^2 pi / 2^25 (closed form)")
    print(f"delta_Phi_phase = alpha(19)/chi = R(19)^2/8 = {dPphase:.12f}")
    print(f"                  (sourced at d_1 = 19, Paper I threshold)")

    # === alpha_s closure ===
    print("\n" + "=" * 74)
    print("(1) alpha_s(M_Z): closed by delta_Phi_U(1)")
    print("=" * 74)
    a12 = alpha_cascade(12)
    Phi12 = Phi(12)
    als_full = a12 * math.exp(Phi12 + dPU1)
    als_obs, als_err = 0.1179, 0.0009
    print(f"  alpha_s = alpha(12) * exp(Phi(12) + delta_Phi_U(1))")
    print(f"          = {als_full:.10f}")
    print(f"  obs     = {als_obs} +/- {als_err} (PDG 2024)")
    print(f"  residual = {als_full - als_obs:+.3e}  ({(als_full-als_obs)/als_err:+.4f} sigma)")

    # === m_tau/m_mu closure ===
    print("\n" + "=" * 74)
    print("(2) m_tau/m_mu: closed by the SAME delta_Phi_U(1)")
    print("=" * 74)
    dPhi = Phi(13) - Phi(5)
    mtmu_full = math.exp(dPhi + dPU1) * 2*math.sqrt(pi)
    mtmu_obs = 1776.86/105.6583755
    mtmu_err = mtmu_obs * (0.12/1776.86)
    print(f"  m_tau/m_mu = exp((Phi(13)-Phi(5)) + delta_Phi_U(1)) * 2sqrt(pi)")
    print(f"             = {mtmu_full:.8f}")
    print(f"  obs        = {mtmu_obs:.8f} +/- {mtmu_err:.6f}")
    print(f"  residual   = {mtmu_full - mtmu_obs:+.3e}  ({(mtmu_full-mtmu_obs)/mtmu_err:+.4f} sigma)")

    # === m_tau absolute closure via delta_Phi_phase ===
    print("\n" + "=" * 74)
    print("(3) m_tau absolute: closed by delta_Phi_phase = alpha(19)/chi")
    print("=" * 74)
    v_lead = 2.435e18 * (a12*math.exp(Phi12)) * math.exp(-pi/alpha_cascade(5))  # GeV
    two_sq_pi = 2*math.sqrt(pi)
    mtau_lead = (a12*math.exp(Phi12)) * v_lead/math.sqrt(2) * math.exp(-Phi(5)) * two_sq_pi**(-2) * 1000
    mtau_full = mtau_lead * math.exp(dPphase)
    mtau_obs, mtau_err = 1776.86, 0.12
    print(f"  m_tau leading  = {mtau_lead:.4f} MeV")
    print(f"  m_tau new      = m_tau_lead * exp(delta_Phi_phase)")
    print(f"                 = {mtau_full:.4f} MeV")
    print(f"  obs            = {mtau_obs} +/- {mtau_err} MeV (PDG 2024)")
    print(f"  residual       = {mtau_full - mtau_obs:+.4f} MeV  ({(mtau_full-mtau_obs)/mtau_err:+.4f} sigma)")

    # === Summary table ===
    print("\n" + "=" * 74)
    print("SUMMARY")
    print("=" * 74)
    print(f"""
  shift              source layer  value        acts on
  -----------------  ------------  -----------  ---------------------------
  delta_Phi_U(1)     d = 14        0.017231     alpha_s, m_tau/m_mu
  delta_Phi_phase    d_1 = 19      0.012816     m_tau absolute

  observable          predicted      observed       residual
  ------------------  -------------  -------------  --------
  alpha_s(M_Z)        0.117917       0.1179         +0.019 sigma
  m_tau/m_mu          16.81731       16.81703       +0.243 sigma
  m_tau (MeV)         {mtau_full:.2f}        {mtau_obs}        {(mtau_full-mtau_obs)/mtau_err:+.2f} sigma

All three within experimental precision.  All three use the same
structural form alpha(d*)/chi with chi = 2 (Euler characteristic of
even-dim sphere, identical to factor in 2*sqrt(pi) obstruction).
No loops, no renormalisation group, no fitting coefficients.
""")

    # === Audit: does chain propagation work? ===
    print("=" * 74)
    print("Audit: chain propagation of delta_Phi_U(1) does NOT close the chain")
    print("=" * 74)
    v_with_u1 = v_lead * math.exp(dPU1)
    print(f"  v_leading = {v_lead:.4f} GeV")
    print(f"  v with 1x delta_Phi_U(1) via alpha_s = {v_with_u1:.4f} GeV")
    print(f"  v observed = 246.22 GeV  (residual: {v_with_u1 - 246.22:+.4f} GeV, not closed)")
    print()
    for k in [0, 1, 2]:
        mtau_k = mtau_lead * math.exp(k * dPU1)
        sig = (mtau_k - 1776.86)/0.12
        print(f"  m_tau with {k}x delta_Phi_U(1) = {mtau_k:.4f} MeV  ({sig:+.1f} sigma)")
    print("  None of the integer multiples closes m_tau absolute.")
    print("  The resolution: m_tau absolute receives delta_Phi_phase (different layer).")


if __name__ == "__main__":
    main()
