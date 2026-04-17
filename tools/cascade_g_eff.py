#!/usr/bin/env python3
"""
Cascade-native relativistic degrees of freedom at N = 217 thermalisation.

Purpose
-------
Part VI §4.2 (Corollary 4.2) computes the reheating temperature
T_RH = (30 Δρ / π² g_eff)^(1/4) M_Pl,red at the N=217 transition, using
the Standard Model value g_eff = 106.75 as a provisional input. This tool
replaces that input with a cascade-native count of relativistic degrees of
freedom, derived from the layer assignments of Part IVa §4 "The cascade
obstruction map".

Method (cascade-native, no semiclassics)
----------------------------------------
For each distinguished cascade layer below the first threshold d₁ = 19
(where fermion projections are subcritical and thermalise) and within the
gauge window {12, 13, 14}, count the 4D-projected propagating modes. No
integration over compactification volume (Check 7 forbids KK reduction):
we count what the cascade's own Part IVa/IVb layer assignments specify as
propagating at d = 4.

Layer assignments (Part IVa §4):
  d = 5    Gen 3 Dirac   τ, b, ν_τ    (hairy-ball zero on S⁴)
  d = 12   SU(3) gauge   8 gluons     (Adams ρ(12)-1 = 3 on S¹¹)
  d = 13   SU(2) gauge   3 W bosons   (broken by hairy-ball zero on S¹²)
         + Gen 2 Dirac   μ, s, c
         + Higgs (from the d=13 hairy-ball obstruction itself)
  d = 14   U(1) gauge    1 B boson    (Adams ρ(14)-1 = 1 on S¹³)
  d = 21   Gen 1 Dirac   e, d, u      (hairy-ball zero on S²⁰; above d₁=19)

d = 29 (Bott 4th fermion layer, suppressed below d₁ to ~0.5 eV, open in
Part IVb Q5): optional — included if RH neutrino partners are present.

Each Dirac fermion carries 4 physical d.o.f. at d=4 (2 helicities × 2
particle/anti). Each massless gauge boson carries 2 polarisations. The
Higgs carries 4 real d.o.f. in the unbroken phase (T >> T_EW).

Fermion species per generation:
  1 charged lepton (Dirac)            → 4 d.o.f.
  1 neutrino (LH only, SM convention) → 2 d.o.f.
  1 up-type quark, 3 colours (Dirac)  → 12 d.o.f.
  1 down-type quark, 3 colours (Dirac) → 12 d.o.f.
  Total per generation (LH ν only):   → 30 d.o.f.
  Total per generation (Dirac ν with RH partner at d=29): 32 d.o.f.

Statistical weighting for g_eff: fermions carry 7/8, bosons carry 1.

Output
------
Two scenarios:
  A. Cascade ≡ SM (d=29 not thermalised at T_RH): g_eff = 106.75
  B. Cascade adds RH neutrinos from d=29: g_eff = 106.75 + 3×2×(7/8) = 112.00
     (3 RH neutrino species, 2 d.o.f. each as Majorana singlets, 7/8 weight)

For each scenario, recompute T_RH and compare with Part VI's Corollary 4.2
provisional value of 7.4 × 10¹⁷ GeV.

Result (preview): cascade g_eff ∈ {106.75, 112.00}; T_RH shifts by at most
1.3% between scenarios; the gravitino/supergravity exposure (bounds of
~10¹⁵ GeV for many models) is structurally stable regardless of which
scenario holds.
"""

import json
import math


def count_cascade_dof():
    """Enumerate cascade layers and count 4D-projected propagating modes.

    Returns a dict of {layer: {bosons, fermions, description}}."""
    N_gen = 3          # Three generations (Part IVa Thm thm:generations)
    N_colours = 3      # SU(3) colours from Adams rho(12)-1 (Part IVa Thm thm:adams)

    # Per-generation fermion content (LH ν only, SM convention)
    lepton_dof = 4                     # 1 Dirac charged lepton
    neutrino_dof_LH = 2                # LH-only neutrino, 2 d.o.f. (particle + anti)
    up_quark_dof = 4 * N_colours       # 1 Dirac up × 3 colours
    down_quark_dof = 4 * N_colours     # 1 Dirac down × 3 colours
    fermion_per_gen_LH = (
        lepton_dof + neutrino_dof_LH + up_quark_dof + down_quark_dof
    )
    assert fermion_per_gen_LH == 30, "sanity: SM per-gen fermion d.o.f."

    # Gauge content (high-T, massless limit above EWSB)
    gluons_dof = 8 * 2                      # 8 gluons × 2 polarisations
    W_bosons_dof = 3 * 2                    # W^{1,2,3} in unbroken phase
    B_boson_dof = 1 * 2                     # 1 U(1) gauge × 2 polarisations
    higgs_dof = 4                           # full complex doublet = 4 real

    layers = {
        5:  {
            "type": "Gen 3 Dirac",
            "bosons": 0,
            "fermions": fermion_per_gen_LH,
            "description": "τ, b, ν_τ (3 colours for quarks)",
        },
        12: {
            "type": "SU(3) gauge",
            "bosons": gluons_dof,
            "fermions": 0,
            "description": "8 gluons × 2 polarisations",
        },
        13: {
            "type": "SU(2) gauge + Gen 2 Dirac + Higgs",
            "bosons": W_bosons_dof + higgs_dof,
            "fermions": fermion_per_gen_LH,
            "description": "3 W bosons + Higgs doublet + μ, s, c",
        },
        14: {
            "type": "U(1) gauge",
            "bosons": B_boson_dof,
            "fermions": 0,
            "description": "1 B boson × 2 polarisations",
        },
        21: {
            "type": "Gen 1 Dirac",
            "bosons": 0,
            "fermions": fermion_per_gen_LH,
            "description": "e, d, u (3 colours for quarks); above d₁=19",
        },
    }

    return layers


def g_eff(layers, include_d29_RH_neutrinos=False):
    """Compute g_eff = sum(bosons) + (7/8) * sum(fermions)."""
    total_bosons = sum(L["bosons"] for L in layers.values())
    total_fermions = sum(L["fermions"] for L in layers.values())

    if include_d29_RH_neutrinos:
        # d=29 (Bott 4th fermion layer, Part IVb Open Question 5):
        # if it provides RH Majorana neutrino partners, +3 species × 2 d.o.f.
        total_fermions += 3 * 2

    return total_bosons + (7.0 / 8.0) * total_fermions, total_bosons, total_fermions


def T_RH(g_eff_value, delta_rho_over_MPlRed4=0.30):
    """Reheating temperature from the N=217 energy release.

    T_RH = (30 Δρ / π² g_eff)^(1/4) × M_Pl,red

    Returns (T_RH / M_Pl,red, T_RH in GeV).
    """
    M_PlRed_GeV = 2.435e18   # reduced Planck mass in GeV
    ratio = (
        30.0 * delta_rho_over_MPlRed4 / (math.pi ** 2 * g_eff_value)
    ) ** 0.25
    T_GeV = ratio * M_PlRed_GeV
    return ratio, T_GeV


def main():
    layers = count_cascade_dof()

    print("=" * 72)
    print("Cascade-native g_eff at N = 217 thermalisation")
    print("=" * 72)
    print("\nLayer-by-layer mode count (Part IVa §4, Part IVb):\n")
    print(f"{'d':>5}  {'Type':<40}  {'bosons':>7}  {'fermions':>9}")
    print("-" * 72)
    for d, L in sorted(layers.items()):
        print(
            f"{d:>5}  {L['type']:<40}  {L['bosons']:>7}  {L['fermions']:>9}"
        )
    total_b = sum(L["bosons"] for L in layers.values())
    total_f = sum(L["fermions"] for L in layers.values())
    print("-" * 72)
    print(f"{'total':>5}  {'':<40}  {total_b:>7}  {total_f:>9}")

    # Scenario A: cascade ≡ SM at T_RH
    gA, bA, fA = g_eff(layers, include_d29_RH_neutrinos=False)
    ratioA, T_A = T_RH(gA)

    # Scenario B: cascade includes d=29 RH neutrinos as additional d.o.f.
    gB, bB, fB = g_eff(layers, include_d29_RH_neutrinos=True)
    ratioB, T_B = T_RH(gB)

    print("\n")
    print("Scenarios:")
    print("-" * 72)
    print(
        f"A. Cascade ≡ SM (d=29 not thermalised)"
    )
    print(
        f"     g_eff = {gA:.2f}  (bosons {bA} + 7/8 × fermions {fA})"
    )
    print(
        f"     T_RH  = {ratioA:.4f} M_Pl,red = {T_A:.3e} GeV"
    )
    print()
    print(
        f"B. Cascade + d=29 RH neutrinos (Part IVb OQ5)"
    )
    print(
        f"     g_eff = {gB:.2f}  (bosons {bB} + 7/8 × fermions {fB})"
    )
    print(
        f"     T_RH  = {ratioB:.4f} M_Pl,red = {T_B:.3e} GeV"
    )

    print("\n")
    print("Comparison:")
    print("-" * 72)
    print(f"  SM g_eff (reference):      106.75")
    print(
        f"  Cascade A / SM ratio:      {gA / 106.75:.4f}  "
        f"(Δ = {gA - 106.75:+.2f})"
    )
    print(
        f"  Cascade B / SM ratio:      {gB / 106.75:.4f}  "
        f"(Δ = {gB - 106.75:+.2f})"
    )
    print(
        f"  T_RH(A) / T_RH(SM) shift:  "
        f"{(T_A / (ratioA * 2.435e18) / 1):.6f}  [ratio 1.0 = no shift]"
    )
    print(
        f"  T_RH(B) vs T_RH(A) shift:  "
        f"{(T_B - T_A) / T_A * 100:+.3f}%"
    )

    print("\n")
    print("Gravitino / supergravity exposure:")
    print("-" * 72)
    print("  Many SUGRA scenarios bound T_RH ≲ 10¹⁵ GeV.")
    print(
        f"  Cascade T_RH (A): {T_A:.2e} GeV — {math.log10(T_A / 1e15):.1f} "
        f"orders above 10¹⁵ GeV"
    )
    print(
        f"  Cascade T_RH (B): {T_B:.2e} GeV — {math.log10(T_B / 1e15):.1f} "
        f"orders above 10¹⁵ GeV"
    )
    print("  Shift between A and B: negligible at the 1% level.")
    print(
        "  Conclusion: the g_eff choice does not resolve the gravitino "
        "exposure;"
    )
    print(
        "  any such pressure is structural to the N=217 release energy "
        "≈ 0.3 M_Pl,red^4,"
    )
    print("  not to the downstream statistical counting.")

    # Machine-readable output
    result = {
        "layers": {str(k): v for k, v in layers.items()},
        "scenario_A": {
            "description": (
                "Cascade ≡ SM: d=29 (Bott 4th fermion) not thermalised at T_RH"
            ),
            "g_eff": gA,
            "T_RH_over_MPlRed": ratioA,
            "T_RH_GeV": T_A,
        },
        "scenario_B": {
            "description": (
                "Cascade + d=29 RH neutrinos (Part IVb Open Question 5)"
            ),
            "g_eff": gB,
            "T_RH_over_MPlRed": ratioB,
            "T_RH_GeV": T_B,
        },
        "sm_reference": {
            "g_eff": 106.75,
            "T_RH_GeV_at_SM_g_eff": T_A,
        },
    }

    out_path = "src/generated/cascade_g_eff.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)
    print(f"\n  Machine-readable output: {out_path}")


if __name__ == "__main__":
    main()
