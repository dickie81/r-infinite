#!/usr/bin/env python3
"""Test whether cascade scalar action's eigenmodes localize at distinguished layers.

Continues the structural derivation digging from
cascade_eigenmode_encompassment_test.py.

Goal: test a substantive structural conjecture — the cascade scalar
action's discrete Sturm–Liouville operator has eigenmodes that localize
at the distinguished cascade layers {d_V=5, d_0=7, d_gw=14, d_1=19,
d_2=217}, while other eigenmodes are extended/distributed across the
lattice. If this localization structure is real, it would derive the
sector exclusivity:

  - Source-selectable observables couple via OPEN-LINE source-coupling at
    a distinguished d*. Their cascade response is dominated by the
    eigenmode LOCALIZED at d*. The eigenmode's response gives α(d*)/χ^k
    (Family A).

  - Non-source-selectable observables couple via CLOSED-LOOP interaction
    at Dirac layers above the host. Their cascade response is dominated
    by EXTENDED/DISTRIBUTED eigenmodes across multiple Dirac layers.
    The cascade fermion-photon interaction at the m=1, k=1 slot
    aggregates these distributed contributions into Family B (h)+(f).

If eigenmodes localize at distinguished layers, the structural
derivation closes: each observable couples to ONE eigenmode (either
localized or extended), and the slot assignment follows from the mode
type. Mutual exclusivity is automatic at the eigenmode level.

If eigenmodes don't localize at distinguished layers, this structural
reading fails, and the sector exclusivity remains a cascade-internal
selection rule that hasn't been derived from cascade primitives.

This tool computes:
  1. The cascade Sturm–Liouville operator's eigenvalues and eigenvectors
  2. For each mode, the localization profile (which layers it concentrates on)
  3. Whether modes concentrate at distinguished layers {5, 7, 14, 19, 217}
  4. Whether other modes are extended/distributed across multiple layers

Result tells us whether eigenmode localization is the structural
mechanism for sector exclusivity.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, THIS_DIR)
sys.path.insert(0, os.path.join(TOOLS_DIR, "verifiers"))

import numpy as np  # noqa: E402

from cascade_constants import alpha as alpha_cas  # noqa: E402
from cascade_greens_function import build_operator  # noqa: E402

# Distinguished cascade layers
DISTINGUISHED = [5, 7, 14, 19, 217]
DISTINGUISHED_LABELS = {5: "d_V (vol max)", 7: "d_0 (area max)",
                        14: "d_gw (gauge window)", 19: "d_1 (phase)",
                        217: "d_2 (Planck sink)"}


def localization_metric(eigvec: np.ndarray, layers: list[int]) -> dict:
    """Compute localization metrics for an eigenvector.

    Returns dict with:
      - peak_layer: layer where |eigvec|^2 is maximized
      - peak_amplitude: |eigvec[peak]|^2
      - effective_support: 1/Σ|ψ|^4 (inverse participation ratio)
      - distinguished_concentration: total |ψ|^2 at distinguished layers
    """
    psi2 = eigvec ** 2
    psi2 /= psi2.sum()  # normalize

    peak_idx = int(np.argmax(psi2))
    peak_layer = layers[peak_idx]
    peak_amp = float(psi2[peak_idx])

    # Inverse participation ratio (IPR): 1/Σ|ψ|^4 ~ effective number of layers
    sum_psi4 = float((psi2 ** 2).sum())
    ipr = 1.0 / sum_psi4 if sum_psi4 > 0 else 0.0

    # Distinguished concentration
    dist_conc = sum(float(psi2[layers.index(d)]) for d in DISTINGUISHED if d in layers)

    return {
        "peak_layer": peak_layer,
        "peak_amplitude": peak_amp,
        "effective_support": ipr,
        "distinguished_concentration": dist_conc,
    }


def main() -> None:
    print("=" * 96)
    print("CASCADE SCALAR ACTION EIGENMODE LOCALIZATION TEST")
    print("=" * 96)
    print()
    print("Test the structural conjecture: do cascade Sturm-Liouville eigenmodes")
    print("localize at distinguished cascade layers {d_V=5, d_0=7, d_gw=14,")
    print("d_1=19, d_2=217}?")
    print()
    print("If yes: source-selectable observables couple to localized eigenmodes,")
    print("giving Family A. Non-source-selectable to distributed eigenmodes,")
    print("giving Family B. Sector exclusivity is at the eigenmode level.")
    print()
    print("If no: the localization conjecture fails. Sector exclusivity remains")
    print("an open structural commitment at the cascade-interaction level.")
    print()

    # Build the cascade Sturm-Liouville operator
    d_min, d_max = 4, 217
    M = build_operator(d_min, d_max)
    layers = list(range(d_min, d_max + 1))

    print(f"Cascade lattice: d ∈ [{d_min}, {d_max}], N = {len(layers)} layers")
    print(f"Operator: discrete Sturm-Liouville with weights 1/α(d)")
    print()

    # Compute eigenvalues and eigenvectors
    # Note: M is built with Neumann at d_min, Dirichlet at d_max
    # Eigenvalues should be real and positive (positive-definite)
    eigvals, eigvecs = np.linalg.eigh(0.5 * (M + M.T))  # symmetrize for stability
    # Sort by eigenvalue (ascending)
    idx_sort = np.argsort(eigvals)
    eigvals = eigvals[idx_sort]
    eigvecs = eigvecs[:, idx_sort]

    print(f"Computed {len(eigvals)} eigenmodes.")
    print(f"Eigenvalue range: [{eigvals[0]:.4e}, {eigvals[-1]:.4e}]")
    print()

    # Examine the lowest 15 modes
    print("=" * 96)
    print("Lowest 15 eigenmodes — localization analysis:")
    print("=" * 96)
    print()
    print(f"{'mode':>5}  {'eigval':>10}  {'peak layer':>11}  "
          f"{'peak amp':>10}  {'eff support':>12}  {'dist conc':>10}  notes")
    print("-" * 96)

    for n in range(min(15, len(eigvals))):
        loc = localization_metric(eigvecs[:, n], layers)
        peak_d = loc["peak_layer"]
        is_distinguished = peak_d in DISTINGUISHED
        notes = ""
        if is_distinguished:
            notes = f"<<< localizes at {DISTINGUISHED_LABELS[peak_d]}"
        elif loc["effective_support"] > 50:
            notes = "(extended/distributed)"
        elif loc["effective_support"] < 5:
            notes = f"(localized at d={peak_d})"

        print(f"  {n:>3}   {eigvals[n]:>10.4e}  {peak_d:>11}  "
              f"{loc['peak_amplitude']:>10.4f}  {loc['effective_support']:>12.2f}  "
              f"{loc['distinguished_concentration']:>10.4f}  {notes}")
    print()

    # Search for modes peaked at each distinguished layer
    print("=" * 96)
    print("Mode peaked at each distinguished layer:")
    print("=" * 96)
    print()
    print(f"{'d*':>4}  {'label':>22}  {'peaked mode #':>14}  {'peak amp':>10}  "
          f"{'eff support':>12}")
    print("-" * 96)

    for d_dist in DISTINGUISHED:
        if d_dist not in layers:
            continue
        idx_d = layers.index(d_dist)
        # For each eigenmode, find amplitude squared at d_dist
        amps = (eigvecs[idx_d, :] ** 2)
        # Normalize each eigenvector
        norms = (eigvecs ** 2).sum(axis=0)
        amps_norm = amps / norms

        # Mode with maximum amplitude at d_dist
        best_mode = int(np.argmax(amps_norm))
        loc = localization_metric(eigvecs[:, best_mode], layers)

        print(f"  {d_dist:>2}  {DISTINGUISHED_LABELS[d_dist]:>22}  "
              f"{best_mode:>14}  {amps_norm[best_mode]:>10.4f}  "
              f"{loc['effective_support']:>12.2f}")
    print()

    print("=" * 96)
    print("STRUCTURAL VERDICT")
    print("=" * 96)
    print()

    # Count localized vs distributed in lowest 15 modes
    localized_at_distinguished = 0
    extended_modes = 0
    other_localized = 0
    for n in range(min(15, len(eigvals))):
        loc = localization_metric(eigvecs[:, n], layers)
        if loc["peak_layer"] in DISTINGUISHED:
            localized_at_distinguished += 1
        elif loc["effective_support"] > 50:
            extended_modes += 1
        else:
            other_localized += 1

    print(f"Among lowest 15 eigenmodes:")
    print(f"  Localized at distinguished layers: {localized_at_distinguished}")
    print(f"  Extended/distributed:               {extended_modes}")
    print(f"  Localized at non-distinguished:     {other_localized}")
    print()

    if localized_at_distinguished >= 3:
        print("CONJECTURE SUPPORTED: multiple low-lying eigenmodes localize at")
        print("distinguished cascade layers. The eigenmode localization reading")
        print("of sector exclusivity has empirical numerical support.")
    elif localized_at_distinguished >= 1:
        print("CONJECTURE PARTIALLY SUPPORTED: at least one low-lying eigenmode")
        print("localizes at a distinguished layer, but most modes are extended.")
        print("The eigenmode reading is suggestive but not strongly forced.")
    else:
        print("CONJECTURE NOT SUPPORTED: low-lying eigenmodes do not preferentially")
        print("localize at distinguished cascade layers. The eigenmode-localization")
        print("reading of sector exclusivity FAILS.")
    print()
    print("Implication for the structural derivation:")
    print()
    print("If the eigenmodes localize at distinguished layers:")
    print("  - Family A's α(d*)/χ^k is the localized-eigenmode response at d*")
    print("  - Family B's (h)+(f) is the extended-eigenmode response distributed")
    print("    across Dirac layers above the host")
    print("  - Source-selection's (P, L, G) flags select between localized vs")
    print("    extended eigenmode coupling")
    print("  - Sector exclusivity is automatic at the eigenmode level")
    print()
    print("If the eigenmodes do NOT localize at distinguished layers:")
    print("  - The eigenmode reading fails")
    print("  - Family A and Family B come from genuinely independent cascade")
    print("    sectors (cascade scalar action vs cascade fermion-photon interaction)")
    print("  - Sector exclusivity remains an open cascade-interaction-level")
    print("    selection rule, not derived from cascade scalar action's spectrum")


if __name__ == "__main__":
    main()
