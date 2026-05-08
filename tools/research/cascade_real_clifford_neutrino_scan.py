#!/usr/bin/env python3
"""
Numerical scan: do real-Clifford hairy-ball cascade layers
d in {23, 27, 31, 39, 43, 47, ...} have suggestive mass scales for
a Majorana / sterile neutrino sector?

Context.  ROADMAP item 2 (lighter neutrinos, PMNS) discusses three
candidate cascade routes.  The d=29, 37, 45 sources (complex Dirac,
d mod 8 = 5) cover the active Dirac sector.  Real-Clifford hairy
ball layers (d mod 8 in {1, 3, 7}) are unused for matter content
except at d_0=7 (G_2/SU(3) algebra source).

This scan asks two questions:

  Q1: What mass scale does the cascade Bott formula give at non-Dirac
      hairy-ball layers d in {23, 27, 31, ...}?  Treating the formula
      as a cascade-internal source mass (geometric channel +
      topological obstruction count for descent path), what does
      it produce numerically?

  Q2: Do any cascade-natural alpha(d*)/chi^k filter pairings of these
      source masses produce mass scales relevant to:
        - active neutrino splittings (meV scale)
        - sterile neutrino dark matter (keV scale)
        - any other observed dark sector?

The scan is exploratory.  The cascade Bott formula was derived for
Dirac fermions (per-layer locality + Berezin + chirality halving);
extending it to non-Dirac layers is an extrapolation that needs
structural justification.  The point of this scan is to surface
suggestive numerical patterns that would motivate further
investigation, not to commit to a closure.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, os.path.join(TOOLS_DIR, "research"))

from cascade_constants import alpha as alpha_cas, R, p, pi  # noqa: E402
from cascade_gram_bott_tower import Phi_cascade  # noqa: E402

ALPHA_S = 0.1159
V_CAS = 243.7  # GeV, Gram-corrected
TWO_SQRT_PI = 2 * math.sqrt(pi)
CHI = 2

# Observational benchmarks (eV)
M_NU_3_PDG = 0.0506   # heaviest active, atmospheric
M_NU_2_PDG = 0.0087   # solar
M_NU_1_BOUND = 0.005  # lightest, NH bound rough
SIGMA_NU_DESI = 0.072

# Sterile DM mass-window benchmarks (eV)
KEV = 1e3
WDM_LOWER = 5 * KEV       # warm dark matter cosmological lower bound
XRAY_LINE = 7 * KEV       # 3.5 keV line -> 7 keV sterile (m_s = 2*E_photon)
WDM_UPPER = 100 * KEV     # rough upper bound for keV-scale sterile DM


def n_D_in_descent(d: int) -> int:
    """Count Dirac layers (d mod 8 = 5) crossed in descent from d down to d=4.

    For a Dirac source d, includes d itself.  For non-Dirac source,
    counts strictly-below Dirac layers that the descent path traverses.
    """
    return sum(1 for k in range(5, d + 1) if k % 8 == 5)


def cascade_source_mass_eV(d: int) -> float:
    """Cascade Bott formula at layer d, interpreted as source mass.

    Geometric channel: exp(-Phi(d)).
    Topological channel: (2 sqrt(pi))^-(n_D + 1)
        where n_D = Dirac layers in descent (including d if Dirac).
        +1 is the universal observer Yukawa baseline.
    """
    n_D = n_D_in_descent(d)
    n_topo = n_D + 1
    return 1e9 * ALPHA_S * V_CAS / math.sqrt(2) * \
        math.exp(-Phi_cascade(d)) * TWO_SQRT_PI ** (-n_topo)


def clifford_class(d: int) -> str:
    """Cascade Clifford class at layer d (Lorentzian signature)."""
    r = d % 8
    return {
        0: "real (Majorana)", 1: "real (Majorana)",
        2: "real (Majorana)", 3: "real (Majorana)",
        4: "complex Weyl",    5: "complex Dirac",
        6: "complex Weyl",    7: "real (Majorana)",
    }[r]


def report_source_masses() -> None:
    print("=" * 88)
    print("CASCADE SOURCE MASSES at hairy-ball layers d in [5, 47]")
    print("=" * 88)
    print()
    print(f"{'d':>3}  {'d mod 8':>7}  {'Clifford':>20}  {'mass (eV)':>15}  {'mass scale':>16}")
    print("-" * 88)
    for d in [5, 7, 11, 13, 15, 19, 21, 23, 27, 29, 31, 35, 37, 39, 43, 45, 47]:
        if d % 2 == 0:
            continue  # need odd d for hairy ball on S^(d-1) even-dim
        m = cascade_source_mass_eV(d)
        scale = scale_of(m)
        print(f"{d:>3}  {d%8:>7}  {clifford_class(d):>20}  {m:>15.4e}  {scale:>16}")
    print()


def scale_of(m: float) -> str:
    """Categorise mass scale for human reading."""
    if m > 1e6:
        return f"{m/1e6:.1f} MeV"
    if m > 1e3:
        return f"{m/1e3:.1f} keV"
    if m > 1:
        return f"{m:.1f} eV"
    if m > 1e-3:
        return f"{m*1e3:.1f} meV"
    if m > 1e-6:
        return f"{m*1e6:.1f} ueV"
    return f"{m:.2e} eV"


def scan_filters(d_source: int, target_mass: float, tol: float = 0.05) -> list:
    """Scan alpha(d*)/chi^k pairings; report ones that match target_mass."""
    m_s = cascade_source_mass_eV(d_source)
    matches = []
    d_stars = [5, 7, 12, 13, 14, 19, 21]
    for d_star in d_stars:
        a = alpha_cas(d_star)
        for k in range(0, 25):
            f = a / CHI**k
            m_pred = m_s * f
            if m_pred == 0:
                continue
            rel = abs(m_pred - target_mass) / target_mass
            if rel < tol:
                matches.append((d_star, k, f, m_pred, rel))
    return matches


def report_active_neutrino_filter_scan() -> None:
    print("=" * 88)
    print("Q1: alpha(d*)/chi^k filters from d=23, 27, 31 -> active-neutrino scale")
    print("=" * 88)
    print()
    targets = [
        ("solar splitting m_2", M_NU_2_PDG),
        ("atmospheric splitting m_3", M_NU_3_PDG),
    ]
    for d_source in [23, 27, 31]:
        m_s = cascade_source_mass_eV(d_source)
        print(f"  d_source = {d_source} ({clifford_class(d_source)}), "
              f"source mass = {scale_of(m_s)}")
        for label, target in targets:
            matches = scan_filters(d_source, target, tol=0.10)
            if not matches:
                print(f"    -> {label} ({scale_of(target)}): NO 10%-match pairing found")
                continue
            for d_star, k, f, m_pred, rel in sorted(matches, key=lambda x: x[4]):
                sign_str = f"alpha({d_star})/chi^{k}" if k > 0 else f"alpha({d_star})"
                print(f"    -> {label}: m_s * {sign_str} = "
                      f"{scale_of(m_pred)}  (dev {rel*100:+.2f}%)")
        print()


def report_sterile_dm_window() -> None:
    print("=" * 88)
    print("Q2: are any of these source masses themselves at sterile-DM scale?")
    print("=" * 88)
    print()
    print("  WDM lower bound (cosmological structure): ~5 keV")
    print("  3.5 keV X-ray line proposal:              ~7 keV sterile")
    print("  WDM upper bound:                        ~100 keV")
    print()
    print(f"{'d':>3}  {'cascade source mass':>22}  {'in sterile-DM window?':>30}")
    print("-" * 88)
    for d in [23, 27, 31, 35, 39, 43]:
        if d % 2 == 0:
            continue
        m = cascade_source_mass_eV(d)
        in_window = WDM_LOWER < m < WDM_UPPER
        marker = "*** IN WINDOW ***" if in_window else ("near window" if 1*KEV < m < 200*KEV else "")
        print(f"{d:>3}  {scale_of(m):>22}  {marker:>30}")
    print()


def report_filtered_sterile_candidates() -> None:
    """Look for a candidate sterile DM mass via alpha(d*)/chi^k filter."""
    print("=" * 88)
    print("Q3: alpha(d*)/chi^k filtered to sterile-DM window")
    print("=" * 88)
    print()
    print("Targets: 7 keV (X-ray line), 5-100 keV (WDM cosmological)")
    print()
    for d_source in [23, 27, 31, 35, 39]:
        if d_source % 2 == 0:
            continue
        m_s = cascade_source_mass_eV(d_source)
        # Search for filters bringing into 5-100 keV window
        matches = []
        for d_star in [5, 7, 12, 13, 14, 19, 21]:
            a = alpha_cas(d_star)
            for k in range(0, 12):
                f = a / CHI**k
                m_pred = m_s * f
                if WDM_LOWER < m_pred < WDM_UPPER:
                    matches.append((d_star, k, m_pred))
        if matches:
            print(f"  d_source = {d_source} (source mass = {scale_of(m_s)}):")
            for d_star, k, m_pred in matches:
                sign_str = f"alpha({d_star})/chi^{k}" if k > 0 else f"alpha({d_star})"
                print(f"    {sign_str:<22} -> {scale_of(m_pred)}")
            print()


def report_summary() -> None:
    print("=" * 88)
    print("HEADLINE NUMBERS")
    print("=" * 88)
    print()
    for d in [23, 27, 31]:
        m = cascade_source_mass_eV(d)
        print(f"  d={d} ({clifford_class(d)}): source mass = {scale_of(m)}")
    print()


if __name__ == "__main__":
    report_source_masses()
    print()
    report_summary()
    print()
    report_active_neutrino_filter_scan()
    print()
    report_sterile_dm_window()
    print()
    report_filtered_sterile_candidates()
