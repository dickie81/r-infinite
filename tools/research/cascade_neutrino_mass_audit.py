#!/usr/bin/env python3
"""
Audit the cascade neutrino-mass derivation.

CLAIM (Part IVb OQ "Neutrino masses", Part IVa thm:generations):
  m_nu(Gen 1) = m_29 * alpha(21) / chi^8 = 0.0493 eV
  with m_29 ≈ 543 eV claimed as "the fourth Bott fermion mass at d=29".

QUESTION: Is m_29 ≈ 543 eV derivable from cascade primitives, or is it
fitted to match the observed atmospheric neutrino mass?

This script:
1. Computes cascade primitives at d=29 (Phi(29), alpha(21), chi=2).
2. Computes the charged-lepton mass formula extrapolated to d=29
   (which gives m_4 = 543 eV; Part IVb's prose now carries this value
   -- the "0.5 eV" units defect this audit originally found at the
   then-line-936 has since been FIXED in Part IVb, and this script's
   stale defect report was corrected in review round 124, F7).
3. Tests various cascade-internal candidate m_29 values and checks
   which (if any) gives 543 eV.
4. Reports honestly whether m_29 = 543 eV is cascade-internal or fitted.

Round-124 hardening (F1/F7): this script previously returned 0
unconditionally -- `sys.exit(main())` with `return 0` -- so citing
it as "gated" was false (the round-120 F3 defect class, third
instance).  main() now computes verdicts (m_e reproduced at d=21;
m_29 = 543 eV; the heaviest m_nu at 0.0493 eV vs part4b's quoted
value; the -0.4% deviation vs 0.0495) and exit-gates on them.
"""

from __future__ import annotations

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + "/..")

from cascade_constants import alpha, R, p, pi


def Phi(d: int) -> float:
    """Cascade potential as cumulative sum from observer host d=5:
      Phi(d) = sum_{k=5..d} p(k).

    Source values (Part IVb line 65):
      Phi(5)  = -0.111
      Phi(13) = +1.429
      Phi(21) = +5.494
      Phi(29) = +11.082
    """
    return sum(p(k) for k in range(5, d + 1))


def report_cascade_primitives():
    print("=" * 78)
    print("CASCADE PRIMITIVES AT NEUTRINO-MASS LAYERS")
    print("=" * 78)
    print()
    for d in (5, 13, 21, 29):
        a = alpha(d)
        ph = Phi(d)
        print(f"  d = {d:>3d}:   alpha(d) = {a:.6f}    "
              f"Phi(d) = {ph:+.4f}    exp(-Phi(d)) = {math.exp(-ph):.4e}")
    print()


def charged_lepton_formula(d: int, n_D: int, alpha_s: float, v_GeV: float) -> float:
    """m_g = (alpha_s * v / sqrt(2)) * exp(-Phi(d_g)) * (2 sqrt(pi))^(-(n_D+1))

    Returns mass in GeV (Part IVb Theorem complete-mass).
    """
    prefactor = alpha_s * v_GeV / math.sqrt(2)
    geo = math.exp(-Phi(d))
    topo = (2.0 * math.sqrt(pi)) ** (-(n_D + 1))
    return prefactor * geo * topo


def report_charged_lepton_check():
    print("=" * 78)
    print("STEP 1: Verify charged-lepton formula at d=21 (e), then extrapolate")
    print("        to d=29 (m_4)")
    print("=" * 78)
    print()
    alpha_s = 0.1159   # Part IVb leading
    v_GeV   = 240.8    # Part IVb leading
    print(f"  Using leading cascade values: alpha_s = {alpha_s}, v = {v_GeV} GeV")
    print()
    for label, d, n_D, obs_eV in [
        ("e   ",  21, 3, 0.511e6),
        ("m_4 ", 29, 4, None),
    ]:
        m_GeV = charged_lepton_formula(d, n_D, alpha_s, v_GeV)
        m_eV = m_GeV * 1e9
        print(f"  {label}  d={d:>3d}, n_D={n_D}: "
              f"m = {m_GeV:.4e} GeV = {m_eV:.4e} eV", end="")
        if obs_eV is not None:
            dev = (m_eV - obs_eV) / obs_eV * 100
            print(f"   (obs {obs_eV:.3e} eV; dev {dev:+.2f}%)")
        else:
            print()
    print()
    print("  -> Charged-lepton formula at d=29 gives m_4 = 543 eV, the")
    print("     value Part IVb's prose now carries (the old '0.5 eV' units")
    print("     defect was fixed papers-side; round-124 F7 corrected this")
    print("     script's stale report of it).")
    print()


def test_neutrino_formula_with_candidate_m29s():
    print("=" * 78)
    print("STEP 2: Test m_nu(Gen 1) = m_29 * alpha(21) / chi^8 with various")
    print("        candidate m_29 values from cascade primitives")
    print("=" * 78)
    print()
    alpha_s = 0.1159
    v_GeV   = 240.8
    chi8    = 2 ** 8
    a21     = alpha(21)
    print(f"  alpha(21) = {a21:.6f}")
    print(f"  chi^8 = {chi8}")
    print(f"  factor alpha(21)/chi^8 = {a21/chi8:.4e}")
    print()
    print("  Target: m_nu(Gen 1) = 0.0493 eV (Part IVb OQ claim, matches")
    print("          sqrt(Delta m^2_atm) = 0.0495 eV to -1%)")
    print()
    print("  Candidate cascade-internal values for m_29:")
    print()

    target_mnu_eV = 0.0493
    required_m29_eV = target_mnu_eV * chi8 / a21
    print(f"  REQUIRED m_29 to match 0.0493 eV: {required_m29_eV:.2f} eV")
    print()

    candidates = []

    # (a) Charged-lepton formula with full topological wall (n_D+1=5)
    m_a = charged_lepton_formula(29, 4, alpha_s, v_GeV) * 1e9
    candidates.append(("(α_s v / √2) exp(-Φ(29)) (2√π)^(-5)", m_a, "(charged-lepton formula at d=29)"))

    # (b) Without topological wall
    m_b = (alpha_s * v_GeV / math.sqrt(2)) * math.exp(-Phi(29)) * 1e9
    candidates.append(("(α_s v / √2) exp(-Φ(29))", m_b, "(no topological wall)"))

    # (c) With √π factor only (one half-obstruction)
    m_c = (alpha_s * v_GeV / math.sqrt(2)) * math.exp(-Phi(29)) * math.sqrt(pi) * 1e9
    candidates.append(("(α_s v / √2) exp(-Φ(29)) √π", m_c, "(charged-lepton minus 1/(2√π)^5 plus √π)"))

    # (d) v alone times exp(-Phi(29))
    m_d = v_GeV * math.exp(-Phi(29)) * 1e9
    candidates.append(("v exp(-Φ(29))", m_d, "(no α_s, no walls)"))

    # (e) M_Pl × exp(-Φ(29))
    M_Pl_GeV = 2.435e18
    m_e = M_Pl_GeV * math.exp(-Phi(29)) * 1e9
    candidates.append(("M_Pl exp(-Φ(29))", m_e, "(naive seesaw mass scale)"))

    # (f) v / (some power of cascade primitives)
    m_f = v_GeV / chi8 * 1e9
    candidates.append(("v / χ^8", m_f, "(naive Bott chirality scaling)"))

    # (g) (α_s v) without √2 or wall
    m_g = alpha_s * v_GeV * math.exp(-Phi(29)) * 1e9
    candidates.append(("α_s v exp(-Φ(29))", m_g, "(no √2, no wall)"))

    print(f"  {'candidate formula':>50s}  {'m_29 (eV)':>14s}  {'ratio to 543':>14s}")
    for label, m_eV, comment in candidates:
        ratio = m_eV / 543.0
        print(f"  {label:>50s}  {m_eV:>14.3e}  {ratio:>14.4e}  {comment}")
    print()


def verify_full_formula():
    print("=" * 78)
    print("STEP 3: Verify the full neutrino formula with cascade-derived m_29")
    print("=" * 78)
    print()
    alpha_s = 0.1159
    v_GeV   = 240.8
    chi     = 2

    m29_eV = charged_lepton_formula(29, 4, alpha_s, v_GeV) * 1e9
    print(f"  m_29 (cascade-derived from charged-lepton formula at d=29):")
    print(f"    = (α_s v / √2) exp(-Φ(29)) (2√π)^(-5)")
    print(f"    = {m29_eV:.3f} eV")
    print()
    print(f"  Three-neutrino mass spectrum from m_nu = m_29 × alpha(d_g)/chi^(29-d_g):")
    print()
    print(f"  {'gen':>5s}  {'d_g':>5s}  {'cascade dist':>14s}  "
          f"{'alpha(d_g)':>12s}  {'chi^k':>10s}  {'m_nu (eV)':>14s}")
    for gen, d_g in [(1, 21), (2, 13), (3, 5)]:
        k = 29 - d_g
        m_nu = m29_eV * alpha(d_g) / (chi ** k)
        print(f"  {gen:>5d}  {d_g:>5d}  {k:>14d}  "
              f"{alpha(d_g):>12.6f}  {chi**k:>10d}  {m_nu:>14.4e}")
    print()
    print("  Observed (PDG 2024):")
    print(f"    sqrt(Delta m^2_atm) = 0.0495 eV   (heaviest neutrino mass scale)")
    print(f"    sqrt(Delta m^2_sol) = 0.0086 eV")
    print()
    print(f"  Cascade m_nu(Gen 1) = {m29_eV * alpha(21) / chi**8:.4f} eV  "
          f"vs 0.0495 eV: dev {(m29_eV * alpha(21) / chi**8 - 0.0495) / 0.0495 * 100:+.2f}%")
    print()


def report_status():
    print("=" * 78)
    print("STEP 4: Status assessment")
    print("=" * 78)
    print()
    print("FINDINGS (after correcting the audit's initial Phi convention):")
    print()
    print("  1. m_29 ≈ 543 eV IS cascade-derived: it equals the charged-")
    print("     lepton mass formula extrapolated to d=29 with n_D+1 = 5:")
    print("       m_29 = (α_s v / √2) exp(-Φ(29)) (2√π)^(-5) = 543 eV.")
    print("     All ingredients are Part IVb cascade primitives (α_s, v,")
    print("     Φ via digamma, (2√π) topological obstruction).")
    print()
    print("  2. [RESOLVED -- net-state, round 124 F7] This audit originally")
    print("     found a units defect ('m_4 ≈ 0.5 eV' for 543 eV) in Part")
    print("     IVb's then-line-936.  Part IVb has since been fixed (the")
    print("     prose now carries 543 eV throughout; grep for '0.5 eV'")
    print("     returns zero) and this script's stale live-defect report")
    print("     was corrected in review round 124.")
    print()
    print("  3. The full neutrino formula m_nu(Gen g) = m_29 × alpha(d_g)/")
    print("     chi^(29-d_g) IS cascade-internal at the heaviest-mass level:")
    print("     all ingredients (m_29 above, alpha(d_g), chi=2) are cascade")
    print("     primitives.  Match to sqrt(Delta m^2_atm) is -1%.")
    print()
    print("  4. The STRUCTURAL form of the neutrino formula remains an open")
    print("     question: WHY is m_nu = m_29 × alpha(d_g)/chi^(29-d_g)? The")
    print("     factor alpha(d_g) (cascade gauge coupling at generation")
    print("     layer) plus chirality filter chi^(29-d_g) (Bott periodicity)")
    print("     is structurally suggestive of a cascade-native seesaw, but")
    print("     no derivation is given in Part IVa or IVb.")
    print()
    print("  5. The lighter two neutrinos (m_29 × alpha(13)/chi^16 ~ 3e-4 eV")
    print("     and m_29 × alpha(5)/chi^24 ~ 3e-6 eV) are much smaller than")
    print("     required for observed solar splitting sqrt(Delta m^2_sol) =")
    print("     0.0086 eV.  The OQ acknowledges this gap and attributes it")
    print("     to inter-generation mixing not yet derived (cascade")
    print("     analogue of PMNS).")
    print()
    print("STATUS:")
    print("  Heaviest neutrino mass: cascade-internally derived to -1% on")
    print("    sqrt(Delta m^2_atm).  Closure is real, modulo the open")
    print("    structural question about the formula's derivation.")
    print()
    print("  Lighter neutrino masses + solar splitting + PMNS: open;")
    print("    cascade analogue of mixing-matrix derivation needed.")
    print()
    print("  Text defect (the old 'm_4 ≈ 0.5 eV'): RESOLVED papers-side;")
    print("    this script's report of it is retained as history only")
    print("    (net-state, round 124 F7).")
    print()


def main():
    print("=" * 78)
    print("CASCADE NEUTRINO MASS AUDIT")
    print("=" * 78)
    print()
    report_cascade_primitives()
    report_charged_lepton_check()
    test_neutrino_formula_with_candidate_m29s()
    verify_full_formula()
    report_status()

    # round-124 F1 hardening: verdicts computed and exit-gated (the
    # script previously returned 0 unconditionally, so subprocess
    # callers certified runnability only -- the round-120 F3 class).
    alpha_s, v_GeV, chi = 0.1159, 240.8, 2
    m_e_eV = charged_lepton_formula(21, 3, alpha_s, v_GeV) * 1e9
    m29_eV = charged_lepton_formula(29, 4, alpha_s, v_GeV) * 1e9
    m_nu = m29_eV * alpha(21) / chi**8
    dev = (m_nu - 0.0495) / 0.0495 * 100
    verdicts = [
        ("m_e reproduced at d=21 within 1%",
         abs(m_e_eV - 0.511e6) / 0.511e6 < 0.01),
        ("m_29 = 543 eV (part4b's committed value) within 1 eV",
         abs(m29_eV - 543.0) < 1.0),
        ("heaviest m_nu rounds to part4b's quoted 0.0493 eV",
         abs(m_nu - 0.0493) < 5e-5),
        ("deviation vs sqrt(Dm2_atm) = 0.0495 eV within -1% .. 0%",
         -1.0 < dev < 0.0),
    ]
    n_fail = 0
    for name, ok in verdicts:
        print(f"  VERDICT {name}: {'PASS' if ok else 'FAIL'}")
        n_fail += 0 if ok else 1
    print()
    print(f"RESULT: {len(verdicts) - n_fail} pass / {n_fail} fail "
          "(4 verdicts -- exit gating added round 124 F1)")
    return 0 if n_fail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
