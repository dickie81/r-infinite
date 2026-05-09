#!/usr/bin/env python3
"""Algebraic decomposition test: does α(d*)/χ^k = cascade tree + (h)+(f) + higher?

Open question from rem:family-a-net (Part IVb): the cascade-net interpretation
of Family A's α(d*)/χ^k claims that this single correction encompasses the
1-loop cascade radiative content (h)+(f) implicitly. Empirically supported
by Tier 2 closures landing 10×-1000× below the 1-loop scale α_em/(2π).

This tool tests the strong algebraic version of the claim: can α(d*)/χ^k
be DECOMPOSED into (h)+(f) plus a structurally identifiable "cascade tree
shift" using only cascade primitives? If yes, the algebraic structure is:
    α(d*)/χ^k = (cascade tree shift) + (h)+(f) + higher
and the cascade tree shift has a closed cascade-primitive form.

For each source-selectable Tier 2 observable, the test:
  1. Compute α(d*)/χ^k (Family A's known closure value).
  2. Compute (h)+(f) for that observable's structure (lepton pair, etc.).
  3. Compute residual = α(d*)/χ^k - (h)+(f) — this is the "cascade tree
     shift" if the algebraic decomposition holds.
  4. Search for closed-form cascade-primitive expressions matching the
     residual: powers of α(d*), α_em, ratios involving χ, Γ(1/2), N(d).
  5. Report whether the residual is cascade-primitive-clean or just
     "leftover number."

Honest expectation: if the algebraic decomposition is the cleanest reading,
the residuals should match identifiable cascade-primitive forms across
multiple observables. If the residuals are unstructured numbers, the
algebraic-sum reading is wrong, and the cascade-net interpretation must
be at the "Green's function eigenmode encompassment" level (not literal
algebraic sum).
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, THIS_DIR)

from cascade_gram_bott_tower import alpha_cascade  # noqa: E402

# Cascade primitives
ALPHA_EM_INV = 137.028
ALPHA_EM = 1.0 / ALPHA_EM_INV
TWO_PI = 2 * math.pi
SQRT_PI = math.sqrt(math.pi)
PI = math.pi
CHI = 2

# Lepton Dirac layers (cascade inverted hierarchy: heavier at lower d)
D_TAU = 5
D_MU = 13
D_E = 21

# Active particle-host segment Dirac layers
ACTIVE_DIRAC_SEGMENT = [5, 13, 21]


def dirac_above(d_f: int) -> list[int]:
    return [d for d in ACTIVE_DIRAC_SEGMENT if d > d_f]


def family_b_per_fermion(d_f: int) -> float:
    """Family B (h)+(f) per-fermion correction at Dirac layer d_f."""
    above = dirac_above(d_f)
    h = ALPHA_EM / TWO_PI * len(above)
    f = ALPHA_EM * sum(alpha_cascade(d) for d in above)
    return h + f


def family_b_ratio(d_heavy: int, d_light: int) -> float:
    """Family B ratio correction m(d_light)/m(d_heavy)."""
    delta_h = family_b_per_fermion(d_heavy)
    delta_l = family_b_per_fermion(d_light)
    return (1 + delta_h) / (1 + delta_l) - 1.0


# ---------------------------------------------------------------------
# Closed-form candidate library for cascade tree shift
# ---------------------------------------------------------------------

def candidate_forms(d_star: int, target: float) -> list[tuple[str, float, float]]:
    """Cascade-primitive candidate forms; return (label, value, residual_pct)."""
    a = alpha_cascade(d_star)
    candidates = []

    # Pure α(d*) and powers
    for k in [1, 2, 3, 4]:
        for sign in [+1, -1]:
            val = sign * a / CHI**k
            candidates.append((f"{'+' if sign>0 else '-'}α({d_star})/χ^{k}", val))
        for k in [1, 2]:
            val = a**(k+1) * 0  # placeholder; α^2 too small
        # α(d*)·n with n integer
        for n in [1, 2, 3, 4]:
            candidates.append((f"+α({d_star})·{n}", a * n))
            candidates.append((f"-α({d_star})·{n}", -a * n))

    # Combinations with cascade primitives
    candidates.append((f"α({d_star})/(2π)", a / TWO_PI))
    candidates.append((f"α({d_star})/(4π)", a / (4 * PI)))
    candidates.append((f"α({d_star})·χ", a * CHI))
    candidates.append((f"α({d_star})·χ²", a * CHI**2))
    candidates.append((f"α({d_star})·π", a * PI))
    candidates.append((f"α({d_star})·π/2", a * PI / 2))
    candidates.append((f"α({d_star})/π", a / PI))

    # Special algebraic identities
    candidates.append((f"α({d_star})/χ - α_em·α({d_star})", a / CHI - ALPHA_EM * a))
    candidates.append((f"α({d_star})/χ - α_em/(2π)", a / CHI - ALPHA_EM / TWO_PI))

    # Sort by closeness to target
    results = []
    for label, val in candidates:
        if abs(val) > 0:
            rel = abs(val - target) / abs(target)
        else:
            rel = float('inf')
        results.append((label, val, rel))
    results.sort(key=lambda x: x[2])
    return results[:5]  # top 5 closest


# ---------------------------------------------------------------------
# Tier 2 closures to decompose
# ---------------------------------------------------------------------

TIER2 = [
    {
        "name": "m_τ/m_μ",
        "d_star": 14,
        "k": 1,
        "sign": +1,
        "type": "ratio",
        "d_heavy": D_TAU,
        "d_light": D_MU,
    },
    {
        "name": "α_s(M_Z)",
        "d_star": 14,
        "k": 1,
        "sign": +1,
        "type": "scalar",  # gauge coupling, not a fermion ratio
        "d_heavy": None,
        "d_light": None,
    },
    {
        "name": "m_τ abs",
        "d_star": 19,
        "k": 1,
        "sign": +1,
        "type": "scalar",
        "d_heavy": None,
        "d_light": None,
    },
    {
        "name": "ℓ_A",
        "d_star": 19,
        "k": 1,
        "sign": +1,
        "type": "scalar",
        "d_heavy": None,
        "d_light": None,
    },
    {
        "name": "sin²θ_W",
        "d_star": 5,
        "k": 3,
        "sign": +1,
        "type": "scalar",
        "d_heavy": None,
        "d_light": None,
    },
    {
        "name": "Ω_m",
        "d_star": 5,
        "k": 3,
        "sign": -1,
        "type": "scalar",
        "d_heavy": None,
        "d_light": None,
    },
    {
        "name": "θ_C",
        "d_star": 7,
        "k": 2,
        "sign": -1,
        "type": "scalar",
        "d_heavy": None,
        "d_light": None,
    },
    {
        "name": "b/s",
        "d_star": 7,
        "k": 4,
        "sign": -1,
        "type": "scalar",
        "d_heavy": None,
        "d_light": None,
    },
]


# ---------------------------------------------------------------------
# Main analysis
# ---------------------------------------------------------------------

def analyze(obs: dict) -> None:
    """For each Tier 2 observable, compute the algebraic decomposition test."""
    print(f"  {obs['name']:<20} d*={obs['d_star']}, k={obs['k']}, sign={obs['sign']:+d}")

    # Family A (closed-form Tier 2 correction)
    family_a = obs['sign'] * alpha_cascade(obs['d_star']) / CHI**obs['k']
    print(f"    Family A α(d*)/χ^k:    {obs['sign']*alpha_cascade(obs['d_star']) / CHI**obs['k']:+.6e}"
          f" = {family_a*100:+.5f}%")

    # Family B for the observable
    if obs['type'] == 'ratio':
        family_b = family_b_ratio(obs['d_heavy'], obs['d_light'])
    elif obs['type'] == 'scalar':
        # For scalar observables (couplings, single masses, angles), Family B
        # isn't directly defined per-fermion. Skip.
        family_b = None

    if family_b is None:
        print(f"    Family B:               (not defined for type=scalar)")
        print(f"    Skipping decomposition.")
        return

    print(f"    Family B (h)+(f):      {family_b:+.6e} = {family_b*100:+.5f}%")

    # Residual = Family A - Family B (would be "cascade tree shift")
    residual = family_a - family_b
    print(f"    Residual (Tree shift): {residual:+.6e} = {residual*100:+.5f}%")

    # Search for cascade-primitive candidate forms matching the residual
    if abs(residual) > 1e-10:
        candidates = candidate_forms(obs['d_star'], residual)
        print(f"    Top cascade-primitive candidates for residual:")
        for label, val, rel in candidates:
            print(f"        {label:<35} = {val:+.6e}  (residual {rel*100:+.2f}%)")
    print()


def main() -> None:
    print("=" * 100)
    print("ALGEBRAIC DECOMPOSITION TEST: α(d*)/χ^k = (h)+(f) + cascade tree shift?")
    print("=" * 100)
    print()
    print("For each Tier 2 source-selectable observable, compute:")
    print("  Family A = α(d*)/χ^k  (the cascade correction)")
    print("  Family B = (h)+(f)    (the chirality-selection-rule m=1, k=1 contribution)")
    print("  Residual = Family A − Family B  (would be 'cascade tree shift' if algebraic)")
    print()
    print("Search for cascade-primitive forms matching the residual:")
    print("  Powers of α(d*), α(d*)/χ^k, α(d*)·χ^k, α(d*)·π, α(d*)/(2π), …")
    print()
    print("If a CLEAN cascade-primitive form matches across multiple observables,")
    print("the algebraic decomposition is supported. If the residuals are unstructured")
    print("numbers, the 'algebraic sum' reading is wrong; the cascade-net")
    print("interpretation lives at a different structural level.")
    print()

    print("=" * 100)
    print("RATIO observables (where Family B is per-fermion-defined):")
    print("=" * 100)
    print()

    for obs in TIER2:
        analyze(obs)

    print("=" * 100)
    print("STRUCTURAL VERDICT")
    print("=" * 100)
    print()
    print("Examined Tier 2 observables of type 'ratio' (m_τ/m_μ).")
    print()
    print("Open question: does the residual α(d*)/χ^k − (h)+(f) have a")
    print("clean cascade-primitive form?")
    print()
    print("If yes: the algebraic decomposition holds; α(d*)/χ^k = (cascade")
    print("tree shift) + (h)+(f), with both pieces cascade-internal. Family A")
    print("LITERALLY contains Family B.")
    print()
    print("If no: the algebraic-sum reading fails; α(d*)/χ^k and (h)+(f) are")
    print("DIFFERENT cascade structural quantities that don't combine algebraically.")
    print("The cascade-net interpretation must be at the 'Green's function eigenmode")
    print("encompassment' level — Family A's value reflects the FULL cascade")
    print("Green's function response at the source mode, including loop-like")
    print("contributions implicitly via Sturm-Liouville structure.")
    print()
    print("The empirical evidence (Tier 2 closures at sub-1-loop precision)")
    print("constrains but doesn't force one reading over the other:")
    print("  - Algebraic: would predict residual matches cascade primitives cleanly")
    print("  - Eigenmode: implies cascade Green's function at d* has built-in")
    print("    higher-order structure not separable from the tree-level α(d*)")
    print()


if __name__ == "__main__":
    main()
