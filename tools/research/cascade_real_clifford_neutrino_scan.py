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
      hairy-ball layers d in {23, 27, 31, ...}?  The Dirac-derived
      formula

          m(d) = (alpha_s * v / sqrt(2)) * exp(-Phi(d)) * (2*sqrt(pi))^-(n_D+1)

      relies on four structural ingredients:
        (1) per-layer locality
        (2) Berezin integration of m * psi-bar * psi over independent
            Grassmann fields, giving Z_f = m
        (3) chirality halving 1/chi = 1/2 from Poincare-Hopf
        (4) Gaussian-vs-Berezin Jacobian 1/sqrt(pi)

      For Majorana fields at real-Clifford layers, ingredients (2),
      (3), (4) may modify.  We explore six candidate formulas:

        Formula A: same as Dirac (conservative extrapolation)
        Formula B: no topological channel (pure exp(-Phi(d)))
        Formula C: no universal Yukawa baseline (drop the +1)
        Formula D: Pfaffian half-power ((2sqrt(pi))^-(n_D+1)/2)
        Formula E: Majorana /2 normalization (extra factor 1/2)
        Formula F: cascade-native Majorana derivation
                   (per-layer 1/sqrt(pi) from missing chirality halving)

  Q2: Which results are robust across formula conventions, and which
      are convention-dependent?  Robust qualitative claims survive;
      sharp quantitative numbers do not.

  Q3: Formula F's structural form is fixed by cascade primitives, but
      its dimensional anchor is not.  We sweep four anchor candidates
      (M_Pl,red bare; M_Pl,red * exp(-pi/alpha(5)); v_EW; alpha_s*v/sqrt2)
      and report which Majorana mass scales each produces at the
      real-Clifford layers.  See report_F_under_anchors().

The scan is exploratory.  The cascade Bott formula was derived for
Dirac fermions; extending it to non-Dirac layers needs structural
justification.  The point is to see what range of mass scales the
cascade primitives can produce at real-Clifford layers and whether
any specific (d, formula) combination has special significance.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, os.path.join(TOOLS_DIR, "research"))

from cascade_constants import alpha as alpha_cas, R, p, pi, M_PL_RED_GEV  # noqa: E402
from cascade_gram_bott_tower import Phi_cascade  # noqa: E402

ALPHA_S = 0.1159
V_CAS = 243.7  # GeV, Gram-corrected
TWO_SQRT_PI = 2 * math.sqrt(pi)
CHI = 2

# ---------------------------------------------------------------------
# Anchor candidates for Formula F
# ---------------------------------------------------------------------
#
# Formula F's overall mass scale requires a dimensional anchor.  Unlike
# the Dirac case (where alpha_s * v / sqrt(2) traces to the Yukawa-Higgs
# coupling that gives charged-fermion masses), Majorana mass terms have
# no Yukawa-Higgs analog, so the anchor is not uniquely fixed by cascade
# primitives.  Four natural cascade-internal candidates are:
#
#   1. M_Pl,red bare.  The "raw" cascade mass scale, before any
#      electroweak structure is invoked.  Reduced Planck mass.
#   2. M_Pl,red * exp(-pi/alpha(5)).  Cascade-native non-perturbative
#      suppression by the d=5 layer's gauge-instanton-style factor.
#      Numerically ~2 TeV (verified: alpha(5) = R(5)^2/4 ~ 0.0904, so
#      pi/alpha(5) ~ 34.7, exp(-34.7) ~ 8.2e-16, product ~ 2 TeV).
#   3. v (electroweak VEV).  The natural mass scale at the gauge-window
#      boundary d_gw = 14.  Cascade-native via Part IVa.
#   4. alpha_s * v / sqrt(2).  Same anchor as the Dirac formula,
#      including QCD prefactor.  ~20 GeV.
#
# Anchors 1 -> 4 differ by the cascade's electroweak/QCD descent
# structure.  Numerical results under each anchor reveal which mass
# scales the cascade primitives can generate at real-Clifford layers.

ANCHOR_2_GEV = M_PL_RED_GEV * math.exp(-pi / alpha_cas(5))
ANCHOR_4_GEV = ALPHA_S * V_CAS / math.sqrt(2)

ANCHORS = [
    ("1: M_Pl,red bare",          M_PL_RED_GEV),
    ("2: M_Pl,red*exp(-pi/a(5))", ANCHOR_2_GEV),
    ("3: v_EW",                   V_CAS),
    ("4: alpha_s*v/sqrt(2)",      ANCHOR_4_GEV),
]

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


# ---------------------------------------------------------------------
# Cascade-internal book-keeping
# ---------------------------------------------------------------------

def n_D_in_descent(d: int) -> int:
    """Count Dirac layers (d mod 8 = 5) in descent from d down to d=4.

    For a Dirac source d, includes d itself.  For non-Dirac source,
    counts strictly-below Dirac layers that the descent path traverses.
    """
    return sum(1 for k in range(5, d + 1) if k % 8 == 5)


def n_M_in_descent(d: int) -> int:
    """Count Majorana (real-Clifford) layers in descent from d to d=4.

    Real-Clifford layers have d mod 8 in {1, 3, 7} (the Lorentzian
    Cl(1, d-1) classes that give real spinors per Lounesto's table).
    For a Majorana source d, includes d itself.  For Dirac source,
    counts strictly-below Majorana layers that the descent traverses.
    """
    real_residues = {1, 3, 7}
    return sum(1 for k in range(5, d + 1) if k % 8 in real_residues)


def base_geom_eV(d: int) -> float:
    """Pure geometric channel: (alpha_s * v / sqrt(2)) * exp(-Phi(d)) in eV.

    Uses anchor 4 (alpha_s * v / sqrt(2)) by default for backward
    compatibility with formulas A-E.  For anchor variants, see
    base_geom_anchored_eV.
    """
    return 1e9 * ALPHA_S * V_CAS / math.sqrt(2) * math.exp(-Phi_cascade(d))


def base_geom_anchored_eV(d: int, anchor_gev: float) -> float:
    """Geometric channel with arbitrary anchor (in GeV), result in eV."""
    return 1e9 * anchor_gev * math.exp(-Phi_cascade(d))


# ---------------------------------------------------------------------
# Five candidate mass formulas
# ---------------------------------------------------------------------

def mass_A(d: int) -> float:
    """Formula A: conservative Dirac extrapolation.

    Same as the standard cascade Bott formula.  Treats real-Clifford
    layer as if it were Dirac for purposes of mass calculation:
    chirality halving applies, universal Yukawa baseline applies,
    Berezin integration is determinant-style.
    """
    n_D = n_D_in_descent(d)
    return base_geom_eV(d) * TWO_SQRT_PI ** (-(n_D + 1))


def mass_B(d: int) -> float:
    """Formula B: no topological channel.

    Drops the (2sqrt(pi))^-(n_D+1) factor entirely.  Treats the
    layer as having no Dirac obstruction structure -- pure
    geometric attenuation only.
    """
    return base_geom_eV(d)


def mass_C(d: int) -> float:
    """Formula C: no universal Yukawa baseline.

    Drops the +1 from (n_D + 1).  Counts only Dirac layers crossed
    in descent, not the observer's own d=5 universal Yukawa
    obstruction.  Justification: Majorana mass terms don't go through
    Yukawa-Higgs coupling.
    """
    n_D = n_D_in_descent(d)
    return base_geom_eV(d) * TWO_SQRT_PI ** (-n_D)


def mass_D(d: int) -> float:
    """Formula D: Pfaffian half-power.

    Berezin integration of a Majorana mass term gives a Pfaffian
    rather than a determinant; for one mode, Pf = sqrt(det), so the
    per-layer fermion partition function scales as sqrt(m) rather
    than m.  This halves the topological-channel power.
    """
    n_D = n_D_in_descent(d)
    return base_geom_eV(d) * TWO_SQRT_PI ** (-(n_D + 1) / 2)


def mass_E(d: int) -> float:
    """Formula E: Majorana /2 normalization.

    Same as A but with extra factor of 1/2 from the Majorana mass
    term's standard 1/2 prefactor: S_M = (m/2) * psi^T C psi.
    """
    return mass_A(d) / 2


def mass_F(d: int) -> float:
    """Formula F: cascade-native Majorana derivation.

    Derived from cascade primitives:
      (1) Per-layer locality applies to Majorana fields (same as
          Dirac; structural property of cascade, not spinor).
      (2) Berezin integration of (1/2) m psi^T C psi for one mode
          gives Z_f^M = m * Pf(C) = m (canonical Pf(C)=1).
          Same form as Dirac.
      (3) NO chirality halving for real spinors: m_M(d) = R(d),
          NOT R(d)/chi.  The S = S^+ \\oplus S^- decomposition
          requires complex spinors; absent at real-Clifford layers.
      (4) Same Gaussian/Beta Jacobian for Z_s = sqrt(pi)*R(d).

    Per-layer Majorana ratio: Z_f^M / Z_s = R/(sqrt(pi)*R) = 1/sqrt(pi),
    d-independent.  This is 1/sqrt(pi) per Majorana layer crossed,
    instead of Dirac's 1/(2sqrt(pi)).  Factor of 2 difference is
    exactly the missing chirality halving.

    Anchor uncertainty: no Yukawa-Higgs analog for Majorana mass.
    Using same anchor as Dirac (alpha_s * v / sqrt(2)) for
    numerical comparability; this is convention-dependent.  See
    mass_F_anchored() and report_F_under_anchors() for the
    anchor sweep.

    No universal Yukawa baseline: Majorana mass terms are primary,
    no observer-side Dirac obstruction propagates to them.
    """
    return mass_F_anchored(d, ANCHOR_4_GEV)


def mass_F_anchored(d: int, anchor_gev: float) -> float:
    """Formula F with explicit anchor (in GeV).

    m_F(d; anchor) = anchor * exp(-Phi(d)) * pi^(-n_M(d)/2)

    The structural form (per-layer 1/sqrt(pi) ratio, n_M layer count,
    Phi(d) descent action) is fixed by cascade primitives.  Only the
    overall dimensional anchor varies among the four candidates.
    """
    n_M = n_M_in_descent(d)
    return base_geom_anchored_eV(d, anchor_gev) * math.sqrt(pi) ** (-n_M)


# ---------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------

FORMULAS = [
    ("A: Dirac extrap.",       mass_A),
    ("B: no topological",      mass_B),
    ("C: no univ. Yukawa",     mass_C),
    ("D: Pfaffian half",       mass_D),
    ("E: Majorana /2",         mass_E),
    ("F: cascade-native Maj.", mass_F),
]


def clifford_class(d: int) -> str:
    """Cascade Clifford class at layer d (Lorentzian signature)."""
    r = d % 8
    return {
        0: "real (Maj)", 1: "real (Maj)", 2: "real (Maj)", 3: "real (Maj)",
        4: "complex Weyl", 5: "complex Dirac", 6: "complex Weyl",
        7: "real (Maj)",
    }[r]


def scale_of(m: float) -> str:
    """Categorise mass scale for human reading."""
    if m == 0:
        return "0"
    if m > 1e9:
        return f"{m/1e9:.1f} GeV"
    if m > 1e6:
        return f"{m/1e6:.1f} MeV"
    if m > 1e3:
        return f"{m/1e3:.1f} keV"
    if m > 1:
        return f"{m:.2f} eV"
    if m > 1e-3:
        return f"{m*1e3:.2f} meV"
    if m > 1e-6:
        return f"{m*1e6:.2f} ueV"
    return f"{m:.2e} eV"


def in_window(m: float, low: float, high: float) -> str:
    if low <= m <= high:
        return "*"
    return " "


# ---------------------------------------------------------------------
# Reports
# ---------------------------------------------------------------------

def report_layers_under_each_formula() -> None:
    print("=" * 100)
    print("CASCADE SOURCE MASSES at hairy-ball layers under candidate formula conventions")
    print("=" * 100)
    print()
    print("Formulas:")
    for label, _ in FORMULAS:
        print(f"  {label}")
    print()
    header = f"{'d':>3} {'Clifford':>12}"
    for label, _ in FORMULAS:
        # Use first 12 chars of label after the colon
        short = label.split(":")[0].strip()
        header += f" {short:>12}"
    print(header)
    print("-" * (16 + 13 * len(FORMULAS)))
    for d in [5, 7, 11, 13, 15, 19, 21, 23, 27, 29, 31, 35, 37, 39, 43, 45, 47]:
        if d % 2 == 0:
            continue
        masses = [f(d) for _, f in FORMULAS]
        line = f"{d:>3} {clifford_class(d):>12}"
        for m in masses:
            line += f" {scale_of(m):>12}"
        print(line)
    print()


def report_realclifford_summary() -> None:
    print("=" * 100)
    print("REAL-CLIFFORD HAIRY-BALL LAYERS: spread across formula conventions")
    print("=" * 100)
    print()
    n_F = len(FORMULAS)
    print(f"{'d':>3} {'mod 8':>5} {'min':>12} {'max':>12} {'min/max ratio':>14}  notes")
    print("-" * 100)
    for d in [23, 27, 31, 35, 39, 43, 47]:
        if d % 8 == 5:  # skip Dirac
            continue
        masses = [f(d) for _, f in FORMULAS]
        m_min, m_max = min(masses), max(masses)
        ratio = m_max / m_min if m_min > 0 else 0
        notes = []
        wdm_count = sum(1 for m in masses if WDM_LOWER <= m <= WDM_UPPER)
        if wdm_count > 0:
            notes.append(f"in WDM window: {wdm_count}/{n_F}")
        meV_count = sum(1 for m in masses if 0.001 <= m <= 0.1)
        if meV_count > 0:
            notes.append(f"in meV (active nu) range: {meV_count}/{n_F}")
        notes_str = "; ".join(notes) if notes else ""
        print(f"{d:>3} {d%8:>5} {scale_of(m_min):>12} {scale_of(m_max):>12} "
              f"{ratio:>14.1f}x  {notes_str}")
    print()


def report_window_assignments() -> None:
    print("=" * 100)
    print("PHYSICAL-WINDOW ASSIGNMENTS by formula and layer")
    print("=" * 100)
    print()
    print("Windows: meV (active neutrino, 1 meV - 100 meV)")
    print("         keV/WDM (warm dark matter, 5 keV - 100 keV)")
    print("         X-ray (3.5 keV photon line proposes m_s = 7 keV)")
    print()
    header = f"{'d':>3} {'Clifford':>12}"
    for label, _ in FORMULAS:
        header += f" {label[:9]:>12}"
    print(header)
    print("-" * 100)
    for d in [23, 27, 31, 35, 39, 43, 47]:
        if d % 2 == 0 or d % 8 == 5:
            continue
        line = f"{d:>3} {clifford_class(d):>12}"
        for _, f in FORMULAS:
            m = f(d)
            mark = ""
            if 0.001 <= m <= 0.1:
                mark = "[meV]"
            elif WDM_LOWER <= m <= WDM_UPPER:
                if abs(m - XRAY_LINE) / XRAY_LINE < 0.30:
                    mark = "[Xray]"
                else:
                    mark = "[WDM]"
            elif 1e3 <= m < WDM_LOWER:
                mark = "[~keV]"
            elif 1 <= m < 1e3:
                mark = "[eV]"
            elif 0.1 <= m < 1:
                mark = "[100meV]"
            line += f" {scale_of(m):>5} {mark:>6}"
        print(line)
    print()


def report_robustness() -> None:
    n_F = len(FORMULAS)
    print("=" * 100)
    print("WHICH RESULTS ARE ROBUST ACROSS FORMULAS?")
    print("=" * 100)
    print()
    print(f"For each layer, count how many of the {n_F} formulas produce a mass")
    print("in each physical window.  Robust = same window across multiple formulas.")
    print()
    layers = [d for d in [23, 27, 31, 35, 39, 43, 47] if d % 8 != 5]
    print(f"{'d':>3} {'Clifford':>12} {'WDM (5-100 keV)':>18} {'meV (active)':>14} "
          f"{'eV-keV (sub-WDM)':>20}")
    print("-" * 100)
    for d in layers:
        masses = [f(d) for _, f in FORMULAS]
        n_wdm = sum(1 for m in masses if WDM_LOWER <= m <= WDM_UPPER)
        n_meV = sum(1 for m in masses if 0.001 <= m <= 0.1)
        n_eVkeV = sum(1 for m in masses if 1 <= m < WDM_LOWER)
        print(f"{d:>3} {clifford_class(d):>12} {n_wdm:>3}/{n_F} formulas "
              f"     {n_meV:>3}/{n_F} formulas  {n_eVkeV:>3}/{n_F} formulas")
    print()
    print(f"Robust results (3+/{n_F} formulas in same window):")
    for d in layers:
        masses = [f(d) for _, f in FORMULAS]
        if sum(1 for m in masses if WDM_LOWER <= m <= WDM_UPPER) >= 3:
            print(f"  d={d}: keV-range WDM (3+ formulas)")
        if sum(1 for m in masses if 0.001 <= m <= 0.1) >= 3:
            print(f"  d={d}: meV-range active neutrino (3+ formulas)")
        if sum(1 for m in masses if 1 <= m < WDM_LOWER) >= 3:
            print(f"  d={d}: sub-keV (eV to keV) (3+ formulas)")
    print()
    # Cross-check: compare Formula A (Dirac extrapolation) vs Formula F
    # (cascade-native Majorana derivation).  These are the two most
    # structurally-grounded formulas; their agreement is meaningful.
    print("STRUCTURAL CROSS-CHECK: Formula A (Dirac extrap.) vs Formula F")
    print("(cascade-native Majorana derivation):")
    print()
    print(f"{'d':>3} {'Formula A':>14} {'Formula F':>14} {'F/A ratio':>12}")
    print("-" * 100)
    for d in layers:
        m_A = mass_A(d)
        m_F = mass_F(d)
        if m_A > 0:
            ratio = m_F / m_A
            print(f"{d:>3} {scale_of(m_A):>14} {scale_of(m_F):>14} {ratio:>12.3f}")
    print()
    print("d=27 has F/A ratio close to 1.0 (Formulas A and F agree at the")
    print("X-ray DM scale).  Other layers have larger A vs F discrepancies.")
    print()


def report_xray_match() -> None:
    print("=" * 100)
    print("X-RAY LINE TARGET: which (d, formula) gives 7 keV ± 30%?")
    print("=" * 100)
    print()
    print("3.5-keV X-ray line implies sterile m_s = 7 keV (decay m_s/2).")
    print("Tolerance ±30% (i.e., 4.9 - 9.1 keV).")
    print()
    print(f"{'d':>3} {'formula':>20} {'mass':>14}  match?")
    print("-" * 100)
    for d in [23, 27, 31, 35]:
        if d % 2 == 0 or d % 8 == 5:
            continue
        for label, f in FORMULAS:
            m = f(d)
            tol = 0.30
            if abs(m - XRAY_LINE) / XRAY_LINE < tol:
                rel = (m - XRAY_LINE) / XRAY_LINE
                print(f"{d:>3} {label:>20} {scale_of(m):>14}  HIT (dev {rel*100:+.1f}%)")
    print()


def report_F_under_anchors() -> None:
    """Sweep Formula F across the four cascade-native anchor candidates.

    The structural ingredients (per-layer 1/sqrt(pi), n_M counting,
    Phi(d) descent) are fixed by cascade primitives.  Only the overall
    dimensional anchor varies.  Show how Majorana masses move across
    physically-relevant windows as the anchor changes.
    """
    print("=" * 100)
    print("FORMULA F under each of the four cascade-native dimensional anchors")
    print("=" * 100)
    print()
    print("m_F(d; anchor) = anchor * exp(-Phi(d)) * pi^(-n_M(d)/2)")
    print()
    print("Anchors (GeV):")
    for label, val in ANCHORS:
        print(f"  Anchor {label:<26} = {val:>12.4g} GeV")
    print()
    layers = [d for d in [23, 27, 31, 35, 39, 43, 47] if d % 8 != 5]

    # Header
    header = f"{'d':>3} {'Cliff.':>10} {'n_M':>4}"
    for label, _ in ANCHORS:
        short = "A" + label.split(":")[0].strip()
        header += f" {short:>14}"
    print(header)
    print("-" * (19 + 15 * len(ANCHORS)))

    for d in layers:
        line = f"{d:>3} {clifford_class(d):>10} {n_M_in_descent(d):>4}"
        for _, anchor in ANCHORS:
            m = mass_F_anchored(d, anchor)
            line += f" {scale_of(m):>14}"
        print(line)
    print()

    # Window assignment under each anchor
    print("Window assignments per anchor:")
    print()
    header = f"{'d':>3} {'Cliff.':>10}"
    for label, _ in ANCHORS:
        short = "A" + label.split(":")[0].strip()
        header += f" {short:>14}"
    print(header)
    print("-" * (14 + 15 * len(ANCHORS)))

    def window_tag(m: float) -> str:
        if 0.001 <= m <= 0.1:
            return "[meV/active]"
        if WDM_LOWER <= m <= WDM_UPPER:
            if abs(m - XRAY_LINE) / XRAY_LINE < 0.30:
                return "[Xray-3.5keV]"
            return "[WDM]"
        if 1 <= m < WDM_LOWER:
            return "[eV-keV]"
        if 0.1 <= m < 1:
            return "[100meV]"
        if 1e5 <= m < 1e9:
            return "[100keV-GeV]"
        if 1e9 <= m < 1e12:
            return "[GeV-TeV]"
        if m >= 1e12:
            return "[>TeV]"
        if m < 0.001:
            return "[sub-meV]"
        return ""

    for d in layers:
        line = f"{d:>3} {clifford_class(d):>10}"
        for _, anchor in ANCHORS:
            m = mass_F_anchored(d, anchor)
            line += f" {window_tag(m):>14}"
        print(line)
    print()

    # X-ray line / WDM-window matches
    print("X-ray line (7 keV +/- 30%) hits across (d, anchor):")
    found = False
    for d in layers:
        for label, anchor in ANCHORS:
            m = mass_F_anchored(d, anchor)
            if abs(m - XRAY_LINE) / XRAY_LINE < 0.30:
                rel = (m - XRAY_LINE) / XRAY_LINE
                print(f"  d={d:>3} anchor {label:<28} -> {scale_of(m):>10}  "
                      f"(dev {rel*100:+.1f}%)")
                found = True
    if not found:
        print("  (none)")
    print()

    print("WDM cosmological window (5 keV - 100 keV) hits:")
    found = False
    for d in layers:
        for label, anchor in ANCHORS:
            m = mass_F_anchored(d, anchor)
            if WDM_LOWER <= m <= WDM_UPPER:
                print(f"  d={d:>3} anchor {label:<28} -> {scale_of(m):>10}")
                found = True
    if not found:
        print("  (none)")
    print()

    print("Active-neutrino window (1 meV - 100 meV) hits:")
    found = False
    for d in layers:
        for label, anchor in ANCHORS:
            m = mass_F_anchored(d, anchor)
            if 0.001 <= m <= 0.1:
                print(f"  d={d:>3} anchor {label:<28} -> {scale_of(m):>10}")
                found = True
    if not found:
        print("  (none)")
    print()


def report_alpha_chi_filters_window(target_low: float, target_high: float,
                                     label: str) -> None:
    """For each (formula, d_source), find filters bringing into window."""
    print("=" * 100)
    print(f"alpha(d*)/chi^k FILTERS landing in {label} ({scale_of(target_low)} - {scale_of(target_high)})")
    print("=" * 100)
    print()
    d_stars = [5, 7, 12, 13, 14, 19, 21]
    for d_source in [23, 27, 31, 35, 39]:
        if d_source % 2 == 0 or d_source % 8 == 5:
            continue
        any_match = False
        for label_f, f_mass in FORMULAS:
            m_s = f_mass(d_source)
            for d_star in d_stars:
                a = alpha_cas(d_star)
                for k in range(0, 25):
                    f_filter = a / CHI**k
                    m_pred = m_s * f_filter
                    if target_low <= m_pred <= target_high:
                        if not any_match:
                            print(f"d={d_source} ({clifford_class(d_source)}):")
                            any_match = True
                        sign_str = f"alpha({d_star})/chi^{k}" if k > 0 else f"alpha({d_star})"
                        print(f"  {label_f:>20} m_s({scale_of(m_s)}) * {sign_str:<22} "
                              f"= {scale_of(m_pred)}")
        if any_match:
            print()


# ---------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------

if __name__ == "__main__":
    report_layers_under_each_formula()
    print()
    report_realclifford_summary()
    print()
    report_window_assignments()
    print()
    report_robustness()
    print()
    report_xray_match()
    print()
    report_F_under_anchors()
    print()
    report_alpha_chi_filters_window(M_NU_2_PDG * 0.9, M_NU_2_PDG * 1.1,
                                     "active solar splitting m_2")
    report_alpha_chi_filters_window(M_NU_3_PDG * 0.9, M_NU_3_PDG * 1.1,
                                     "active atmospheric splitting m_3")
    report_alpha_chi_filters_window(WDM_LOWER, WDM_UPPER, "WDM cosmological window")
