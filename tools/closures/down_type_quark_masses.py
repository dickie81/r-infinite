#!/usr/bin/env python3
"""
Derivation: down-type quark masses from cascade primitives.

Status: Tier 4 for m_b (1% precision); Tier 5 (qualitative pattern only)
for m_s and m_d due to scale-dependence of GJ ratios under QCD running.

Cascade structural inputs
-------------------------
1. Lepton absolute masses (cascade Tier 1/2 closures, Part 4b):
     m_tau = 1776.82 MeV  (Tier 1, alpha(19)/chi closure)
     m_mu  =  105.66 MeV  (Tier 2, chain-subtracted shift)
     m_e   =    0.511 MeV (Tier 2, same chain)

2. Cascade Tier 4 down-type / lepton ratio at pole-mass scale:
     m_b / m_tau ≈ e            (Part 4b Tier 4, line 2020; 1.05% deviation)

3. Cascade Tier 4 Georgi-Jarlskog STRUCTURAL pattern (not quantitative):
     m_b / m_tau ≈ N_c          (Gen 3, outside gauge window)
     m_s / m_mu  ≈ 1 / N_c      (Gen 2, inside gauge window)
     m_d / m_e   ≈ N_c          (Gen 1, outside gauge window)
   The "≈" is the cascade Theorem at line 696 (Part 4b). At Tier 4
   precision the structural N_c / 1/N_c factors are approximate; the
   refined version for m_b is m_b/m_tau = e ≈ 2.72 vs N_c = 3.

4. Color factor N_c = 3 (cascade Tier 1, Adams' theorem at d=12).

Result
------
m_b is derivable at Tier 4 precision via the e factor:
     m_b ≈ e * m_tau = 2.7183 * 1776.82 = 4830 MeV
which matches m_b^pole ≈ 4780 MeV (PDG b-quark pole mass) to ~1%.

m_s, m_d are NOT cleanly derivable at Tier 4 numerical precision because
the GJ ratios 1/N_c and N_c hold at the GUT scale (where standard SUSY-
GUT also predicts ~1/3 and ~3) but the cascade has no precision factor
analogous to the m_b/m_tau = e refinement. PDG m_s and m_d are at low-
energy hadronic scales where QCD running has shifted the values
significantly from GUT.

So the honest cascade-internal status is:
  m_b: TIER 4 absolute closure available (1% precision via e factor)
  m_s: TIER 5 qualitative pattern (m_s ~ m_mu / 3 at GUT scale, qualitative)
  m_d: TIER 5 qualitative pattern (m_d ~ 3 m_e at GUT scale, qualitative)
"""

from __future__ import annotations

import math
import sys


# ============================================================
# Cascade-internal inputs
# ============================================================

# Lepton masses (cascade Tier 1/2 closures, low-energy MS-bar)
m_tau = 1776.82  # MeV (Tier 1)
m_mu  =  105.66  # MeV (Tier 2)
m_e   =    0.511 # MeV (Tier 2)

# Color factor (cascade Tier 1, Adams' theorem at d=12)
N_c = 3

# Cascade Tier 4 ratio (Part 4b line 2020)
m_b_over_m_tau_cascade = math.e  # ≈ 2.7183, deviation 1.05%

# Cascade Tier 4 GJ structural pattern (Part 4b Theorem at line 696)
# Approximate N_c factors -- refined version for m_b is e ≈ 2.72


# ============================================================
# Derivations
# ============================================================

# m_b: at Tier 4 precision via m_b/m_tau = e
m_b_predicted_e = math.e * m_tau

# m_b: at GJ scale (qualitative, N_c factor)
m_b_predicted_N_c = N_c * m_tau

# m_s, m_d: at GJ scale (qualitative)
m_s_predicted = m_mu / N_c
m_d_predicted = N_c * m_e


# ============================================================
# PDG comparison values (PDG 2024)
# ============================================================
m_b_pdg_at_mb_msbar = 4180.0   # MeV at scale Q = m_b (MS-bar)
m_b_pdg_pole       = 4780.0    # MeV pole-mass approximation
m_s_pdg_2GeV       =   93.5    # MeV at Q = 2 GeV (MS-bar)
m_d_pdg_2GeV       =    4.67   # MeV at Q = 2 GeV (MS-bar)


# ============================================================
# Output
# ============================================================

def main() -> int:
    print("=" * 78)
    print("DOWN-TYPE QUARK MASSES: cascade-internal derivation, Tier 4 precision")
    print("=" * 78)
    print()
    print("Cascade inputs:")
    print(f"  m_tau = {m_tau:>9.3f} MeV  (Tier 1)")
    print(f"  m_mu  = {m_mu:>9.3f} MeV  (Tier 2)")
    print(f"  m_e   = {m_e:>9.3f} MeV  (Tier 2)")
    print(f"  N_c   = {N_c}             (Tier 1)")
    print()
    print("=" * 78)
    print("BOTTOM QUARK -- Tier 4 precision via m_b/m_tau = e (Part 4b line 2020)")
    print("=" * 78)
    print()
    print(f"  m_b  =  e * m_tau  =  {math.e:.6f} * {m_tau:.2f} MeV")
    print(f"       =  {m_b_predicted_e:.2f} MeV")
    print()
    print("Comparison to PDG b-quark mass:")
    rel_pole = (m_b_predicted_e / m_b_pdg_pole - 1) * 100
    rel_msbar = (m_b_predicted_e / m_b_pdg_at_mb_msbar - 1) * 100
    print(f"  cascade            : {m_b_predicted_e:>7.0f} MeV")
    print(f"  PDG m_b^pole       : {m_b_pdg_pole:>7.0f} MeV   "
          f"(cascade/PDG: {rel_pole:>+5.1f}%)")
    print(f"  PDG m_b^MS-bar(m_b): {m_b_pdg_at_mb_msbar:>7.0f} MeV   "
          f"(cascade/PDG: {rel_msbar:>+5.1f}%)")
    print()
    print(f"Tier 4 verdict: m_b matches m_b^pole to 1.05% (within Tier 4 spec).")
    print()
    print("Comparison to GJ N_c factor:")
    print(f"  m_b via N_c factor : {m_b_predicted_N_c:>7.0f} MeV "
          f"(off pole by {100*(m_b_predicted_N_c/m_b_pdg_pole-1):+.1f}%)")
    print(f"  m_b via e factor   : {m_b_predicted_e:>7.0f} MeV "
          f"(refined to 1.05%)")
    print(f"  Ratio N_c / e = {N_c/math.e:.4f} -- the e is the 'precise' Tier 4 form")
    print(f"  of the qualitative N_c at the b-quark pole-mass scale.")
    print()
    print("=" * 78)
    print("STRANGE QUARK -- Tier 5 qualitative pattern only")
    print("=" * 78)
    print()
    print(f"  Cascade prediction (GJ scale): m_s = m_mu / N_c = "
          f"{m_s_predicted:.2f} MeV")
    print(f"  PDG m_s(2 GeV) MS-bar         : {m_s_pdg_2GeV:.2f} MeV")
    print(f"  cascade/PDG: {100*(m_s_predicted/m_s_pdg_2GeV - 1):>+.1f}%")
    print()
    print("This 62% deviation reflects QCD running between GUT-level GJ")
    print("scale and the 2 GeV reference. The cascade has the QUALITATIVE")
    print("pattern (m_s ~ m_mu/N_c at high scale) but no Tier 4 precision")
    print("factor analogous to the m_b/m_tau = e refinement.")
    print()
    print("Status: Tier 5 (qualitative pattern verified).")
    print("Promotion path: derive a precision factor for m_s/m_mu at the")
    print("appropriate cascade scale (analogous to e for m_b).")
    print()
    print("=" * 78)
    print("DOWN QUARK -- Tier 5 qualitative pattern only")
    print("=" * 78)
    print()
    print(f"  Cascade prediction (GJ scale): m_d = N_c * m_e = "
          f"{m_d_predicted:.4f} MeV")
    print(f"  PDG m_d(2 GeV) MS-bar         : {m_d_pdg_2GeV:.2f} MeV")
    print(f"  cascade/PDG: {100*(m_d_predicted/m_d_pdg_2GeV - 1):>+.1f}%")
    print()
    print("Same status as m_s: Tier 5 qualitative pattern only.")
    print()
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print()
    print(f"  m_b: TIER 4 ABSOLUTE CLOSURE  ({m_b_predicted_e:>7.0f} MeV via e * m_tau)")
    print(f"       1.05% deviation vs PDG m_b^pole = {m_b_pdg_pole} MeV")
    print()
    print(f"  m_s: TIER 5 QUALITATIVE       ({m_s_predicted:>7.2f} MeV via m_mu / N_c)")
    print(f"       62% deviation vs PDG -- needs a precision factor")
    print()
    print(f"  m_d: TIER 5 QUALITATIVE       ({m_d_predicted:>7.4f} MeV via N_c * m_e)")
    print(f"       67% deviation vs PDG -- needs a precision factor")
    print()
    print("Honest assessment of the user's request:")
    print()
    print("  'Derive down-type quark masses at Tier 4 precision' is achieved for m_b")
    print("  but NOT for m_s, m_d. The cascade currently has Tier 4 numerical content")
    print("  for the bottom quark only; m_s and m_d are at the qualitative-pattern")
    print("  level (Tier 5) because no precision factor analogous to e has been")
    print("  derived for the lighter generations.")
    print()
    print("To genuinely derive m_s and m_d at Tier 4 precision, the cascade would")
    print("need to identify what factor (analogous to e for the bottom) corrects the")
    print("qualitative N_c / (1/N_c) GJ pattern at the appropriate cascade scale,")
    print("OR adopt a cascade-internal RG running prescription to translate from")
    print("GJ scale to PDG MS-bar scales.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
