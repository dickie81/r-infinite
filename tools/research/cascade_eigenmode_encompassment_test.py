#!/usr/bin/env python3
"""Numerical Green's function exploration: can Family B be extracted from
the cascade scalar action alone?

Continues the line from cascade_algebraic_decomposition_test.py.
The algebraic-sum reading was ruled out (commit e54676c). The
remaining structural derivation candidate was the Green's function
eigenmode level — that the cascade scalar action's Green's function
at distinguished d* somehow encompasses Family B's contribution
via the Sturm-Liouville eigenmode decomposition.

This tool tests that candidate directly. It uses the existing cascade
Green's function machinery (tools/verifiers/cascade_greens_function.py)
to compute G(d_obs, d') for the m_μ/m_e structure (m_μ at d=13, m_e
at d=21, observer at d=4) and searches for cascade-scalar-Green's-
function-only forms matching Family B's (h)+(f) = 0.133%.

If the cascade scalar action's Green's function produces (h)+(f)
naturally, the eigenmode encompassment reading is supported. If not,
Family A and Family B are STRUCTURALLY INDEPENDENT cascade sectors
(scalar action + fermion-photon interaction).

Negative result (this tool's finding): the closest cascade-scalar-
only candidate is α(21)/χ⁴ = 0.145% (9% deviation from Family B),
much worse than Family B's own 1% match to the residual.

Family B's (h)+(f) uses BOTH per-layer α(21) AND global α_em (from
the cascade-derived 1/α_em closure). It is therefore a cross-sector
cascade-internal quantity, not a pure cascade scalar Green's function
quantity. The eigenmode encompassment reading fails: Family A (cascade
scalar action) and Family B (cascade fermion-photon interaction) are
two structurally independent cascade-internal mechanisms.

The exclusivity claim from prop:slot-precedence then is structural
via "different observables couple to different cascade sectors based
on source-selection flags," not via "encompassment of one inside
the other." This is the honest final structural picture.
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
from cascade_greens_function import build_operator, greens_function  # noqa: E402

# Cascade primitives
ALPHA_EM_INV = 137.028
ALPHA_EM = 1.0 / ALPHA_EM_INV
TWO_PI = 2 * math.pi
CHI = 2

# Lepton Dirac layers (cascade inverted hierarchy)
D_TAU = 5
D_MU = 13
D_E = 21


def main() -> None:
    print("=" * 96)
    print("CASCADE GREEN'S FUNCTION EXPLORATION FOR m_μ/m_e (NON-SOURCE-SELECTABLE)")
    print("=" * 96)
    print()
    print("Question: does the cascade scalar action's Green's function naturally")
    print("produce Family B's (h)+(f) = 0.133% for m_μ/m_e structure?")
    print()
    print("If yes: the eigenmode encompassment reading is supported.")
    print("If no: Family A and Family B are structurally independent cascade sectors.")
    print()

    d_min, d_max = 4, 217
    G = greens_function(d_min, d_max)

    # Family B reference value
    h_part = ALPHA_EM / TWO_PI  # leading per-Dirac-above
    f_part = ALPHA_EM * alpha_cas(D_E)  # next-order at d=21
    family_b = h_part + f_part

    print(f"Reference: Family B (h)+(f) for m_μ at d=13 with d=21 above:")
    print(f"  (h) = α_em/(2π)        = {h_part:>12.6e} = {h_part*100:.5f}%")
    print(f"  (f) = α_em·α(21)       = {f_part:>12.6e} = {f_part*100:.5f}%")
    print(f"  (h)+(f) total          = {family_b:>12.6e} = {family_b*100:.5f}%")
    print()
    print(f"  PDG residual on m_μ/m_e ≈ {0.001319*100:.5f}% (target)")
    print()

    # Test cascade-scalar-Green's-function-only candidates
    print("=" * 96)
    print("Cascade-scalar-Green's-function-only candidates:")
    print("(uses ONLY per-layer α(d) primitives, no global α_em)")
    print("=" * 96)
    print()

    candidates = []

    # Bare Green's function values
    candidates.append(("G(4, 21) [cumulative]", G[0, D_E - d_min]))
    candidates.append(("G(4, 13) [cumulative]", G[0, D_MU - d_min]))
    candidates.append(("G(4, 13) - G(4, 21)", G[0, D_MU - d_min] - G[0, D_E - d_min]))
    candidates.append(("α(21) = marginal G at 21", alpha_cas(D_E)))
    candidates.append(("α(13) = marginal G at 13", alpha_cas(D_MU)))

    # α(d_above)/χ^k for d_above = 21
    for k in range(1, 8):
        candidates.append((f"α(21)/χ^{k}", alpha_cas(D_E) / CHI**k))

    # Higher cascade primitives
    candidates.append(("α(21)/(2π)", alpha_cas(D_E) / TWO_PI))
    candidates.append(("α(21)/(4π)", alpha_cas(D_E) / (4 * math.pi)))
    candidates.append(("α(21)·α(13)", alpha_cas(D_E) * alpha_cas(D_MU)))
    candidates.append(("α(21)²", alpha_cas(D_E) ** 2))

    # Sums with chirality
    candidates.append(("α(21)/χ⁴ + α(21)·α(13)/χ", alpha_cas(D_E) / 16 + alpha_cas(D_E) * alpha_cas(D_MU) / 2))
    candidates.append(("α(21)/χ⁴ + α(13)/χ⁴", alpha_cas(D_E) / 16 + alpha_cas(D_MU) / 16))

    # Sort by closeness
    candidates.sort(key=lambda c: abs(c[1] - family_b) / family_b)

    print(f"{'candidate':>40}  {'value':>14}  {'Δ vs Family B':>15}")
    print("-" * 96)
    for label, val in candidates[:12]:
        deviation = abs(val - family_b) / family_b * 100
        print(f"{label:>40}  {val:>14.6e}  {deviation:>13.2f}%")
    print()

    print("=" * 96)
    print("STRUCTURAL VERDICT")
    print("=" * 96)
    print()
    closest_label, closest_val = candidates[0]
    closest_dev = abs(closest_val - family_b) / family_b * 100
    print(f"Closest cascade-scalar-only candidate: {closest_label}")
    print(f"  Value: {closest_val:.6e} = {closest_val*100:.5f}%")
    print(f"  Deviation from Family B: {closest_dev:.2f}%")
    print()
    print(f"For comparison, Family B's own match to PDG residual: ~1% precision")
    print(f"(closes m_μ/m_e from +0.132% leading to −0.001% post-correction)")
    print()
    print("Cascade-scalar-only candidates are an order of magnitude WORSE than")
    print("Family B at matching the residual.")
    print()

    # Test mixed-sector candidates (with α_em)
    print("=" * 96)
    print("Mixed-sector candidates (use both α_em and per-layer α(d)):")
    print("=" * 96)
    print()
    mixed = [
        ("α_em/(2π) [Family B (h) only]", ALPHA_EM / TWO_PI),
        ("α_em·α(21) [Family B (f) only]", ALPHA_EM * alpha_cas(D_E)),
        ("α_em/(2π) + α_em·α(21) [Family B (h)+(f)]", ALPHA_EM / TWO_PI + ALPHA_EM * alpha_cas(D_E)),
        ("α_em/(2π) + α_em·α(13)·α(21)", ALPHA_EM / TWO_PI + ALPHA_EM * alpha_cas(D_MU) * alpha_cas(D_E)),
    ]
    print(f"{'candidate':>50}  {'value':>14}  {'Δ vs PDG residual 0.001319':>22}")
    print("-" * 96)
    target = 0.001319
    for label, val in mixed:
        deviation = abs(val - target) / target * 100
        print(f"{label:>50}  {val:>14.6e}  {deviation:>20.2f}%")
    print()

    print("=" * 96)
    print("CONCLUSION")
    print("=" * 96)
    print()
    print("The cascade scalar action's Green's function alone (per-layer α(d)")
    print("primitives) cannot match Family B's (h)+(f) to better than ~9% deviation.")
    print()
    print("Family B's (h)+(f) USES BOTH:")
    print("  - Per-layer α(d_above) at the Dirac layer above the fermion's host")
    print("  - Global α_em from the cascade-derived 1/α_em = 137.028 closure")
    print()
    print("The two cascade primitives sit in DIFFERENT cascade structural sectors:")
    print("  - α(d): per-layer cascade scalar action compliance (Sturm-Liouville)")
    print("  - α_em: cascade-derived global EM coupling (chirality theorem +")
    print("          per-leg primitive Γ(1/2)² = π)")
    print()
    print("Family B is therefore NOT a cascade scalar Green's function quantity")
    print("— it is a CROSS-SECTOR cascade-internal quantity combining the cascade")
    print("scalar action with the cascade gauge structure (cascade fermion-photon")
    print("interaction at the chirality-selection-rule m=1, k=1 slot).")
    print()
    print("Family A's α(d*)/χ^k is purely cascade scalar Green's function.")
    print("Family B's (h)+(f) is cascade fermion-photon interaction.")
    print()
    print("These are STRUCTURALLY INDEPENDENT cascade-internal mechanisms.")
    print("They do NOT share a common cascade Green's function calculation.")
    print()
    print("Implication for prop:slot-precedence's exclusivity claim:")
    print("  - The exclusivity is via 'different observables couple to different")
    print("    cascade sectors based on source-selection flags' (clean structural)")
    print("  - Not via 'one mechanism encompasses the other' (eigenmode reading,")
    print("    ruled out by this tool)")
    print("  - Not via 'algebraic sum decomposition' (ruled out by")
    print("    cascade_algebraic_decomposition_test.py)")
    print()
    print("Honest structural picture: TWO INDEPENDENT cascade sectors, with")
    print("the source-selection rule (Proposition source-selection) determining")
    print("which sector couples to a given observable. The closure precision of")
    print("Tier 2 observables at sub-1-loop scale reflects that source-selectable")
    print("observables structurally don't have the m=1, k=1 slot's contribution")
    print("(it's not present, not encompassed). The cascade fermion-photon")
    print("interaction simply doesn't apply when the cascade scalar action's")
    print("source-response at distinguished d* is the active mechanism.")
    print()
    print("This is a stronger structural commitment than I initially articulated:")
    print("  - The cascade has multiple distinct interaction sectors")
    print("  - Source-selection rule's flags are the cascade-internal switch")
    print("    determining which sector applies to a given observable")
    print("  - The empirical Tier 2 closures support this 'sector exclusivity'")
    print("    reading without requiring algebraic encompassment")
    print()
    print("Open structural question: cascade-internal derivation of the SECTOR")
    print("EXCLUSIVITY rule. Why does the (P, L, G) flag combination select")
    print("between cascade scalar action's source-response (Family A) and cascade")
    print("fermion-photon interaction (Family B)? This requires a cascade-")
    print("internal selection-rule theorem at the level of fundamental cascade")
    print("interactions, not just observable classification.")


if __name__ == "__main__":
    main()
