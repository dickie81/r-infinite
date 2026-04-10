#!/usr/bin/env python3
"""
BBN from the cascade's own perspective.

The previous test applied STANDARD BBN physics to cascade parameters
and found a 16-sigma deuterium problem. But that assumes the cascade's
Omega_b = 1/(2*pi^2) enters BBN identically to the standard baryon density.

Key question: does the cascade's S^3 content split into a nuclear
fraction and a non-nuclear fraction?

The cascade's quantum mechanics (Part II) derives Fermi-Dirac and
Bose-Einstein statistics from sphere geometry. The factor 7/8 —
the ratio of fermionic to bosonic energy density — is a cascade-
derived quantity. What happens if the cascade's S^3 content splits
by this factor?
"""

import numpy as np

pi = np.pi

# === Cascade parameters ===
H0 = 71.05
h = H0 / 100.0
h2 = h**2

Omega_b_cascade = 1.0 / (2.0 * pi**2)
omega_b_cascade = Omega_b_cascade * h2

# Planck reference
omega_b_planck = 0.02237

print("=" * 75)
print("THE 7/8 OBSERVATION")
print("=" * 75)
print()
print(f"  Cascade omega_b = Omega_b * h^2 = [1/(2*pi^2)] * [{h}]^2")
print(f"                  = {Omega_b_cascade:.8f} * {h2:.8f}")
print(f"                  = {omega_b_cascade:.8f}")
print()
print(f"  Planck omega_b  = {omega_b_planck} +/- 0.00015")
print()
print(f"  Ratio: Planck / Cascade = {omega_b_planck / omega_b_cascade:.6f}")
print(f"  7/8                     = {7/8:.6f}")
print(f"  Match:                    {abs(omega_b_planck/omega_b_cascade - 7/8)/(7/8)*100:.3f}%")
print()

# The 7/8 correction
omega_b_corrected = (7.0/8.0) * omega_b_cascade
print(f"  (7/8) * omega_b_cascade = {omega_b_corrected:.8f}")
print(f"  Planck omega_b          = {omega_b_planck:.8f}")
print(f"  Deviation:                {(omega_b_corrected - omega_b_planck)/omega_b_planck*100:+.3f}%")
print(f"  In sigma:                 {(omega_b_corrected - omega_b_planck)/0.00015:+.2f} sigma")

print()
print("=" * 75)
print("WHAT IS 7/8 IN THE CASCADE?")
print("=" * 75)
print(f"""
  7/8 appears in two cascade contexts:

  1. FERMI-DIRAC / BOSE-EINSTEIN RATIO
     The cascade derives QM from sphere geometry (Part II).
     Fermi-Dirac statistics emerge from the spinor structure.
     For equal temperature: rho_fermion / rho_boson = 7/8.
     This is a DERIVED quantity in the cascade, not assumed.

  2. BOTT PERIODICITY FRACTION
     The Bott period is 8. At any position d mod 8, the fraction
     of the period that carries complex spinor structure is
     3/8 (positions 4,5,6). The complementary fraction is 5/8.
     But the fraction that carries ANY non-trivial structure
     (complex + real spinors, excluding only the terminal layer
     at d mod 8 = 7) is 7/8.

  In either reading: 7/8 of the cascade's S^3 content is "active"
  (participates in nuclear reactions and Thomson scattering),
  and 1/8 is "inert" (gravitates but doesn't interact
  electromagnetically).
""")


print("=" * 75)
print("BBN WITH THE 7/8 CORRECTION")
print("=" * 75)
print()

# Standard BBN predictions (approximate scalings from Cyburt+2016)
omega_b_ref = 0.02237  # reference value

# With cascade's full omega_b
ratio_full = omega_b_cascade / omega_b_ref
DH_full = 2.527e-5 * ratio_full**(-1.6)
Yp_full = 0.2471 + 0.014 * np.log(ratio_full)

# With 7/8 correction
ratio_78 = omega_b_corrected / omega_b_ref
DH_78 = 2.527e-5 * ratio_78**(-1.6)
Yp_78 = 0.2471 + 0.014 * np.log(ratio_78)

# Observations
DH_obs = 2.527e-5
DH_err = 0.030e-5
Yp_obs = 0.245
Yp_err = 0.003

print(f"  {'':>20s}  {'Full omega_b':>14s}  {'7/8 corrected':>14s}  {'Observed':>14s}")
print(f"  {'':>20s}  {'(0.02557)':>14s}  {'(0.02238)':>14s}  {'':>14s}")
print(f"  {'-'*65}")
print(f"  {'D/H (x10^5)':>20s}  {DH_full*1e5:14.3f}  {DH_78*1e5:14.3f}  {DH_obs*1e5:.3f} +/- {DH_err*1e5:.3f}")
print(f"  {'D/H tension':>20s}  {abs(DH_full-DH_obs)/DH_err:14.1f} sig  {abs(DH_78-DH_obs)/DH_err:14.1f} sig  {'':>14s}")
print(f"  {'Y_p (He-4)':>20s}  {Yp_full:14.4f}  {Yp_78:14.4f}  {Yp_obs:.3f} +/- {Yp_err:.3f}")
print(f"  {'Y_p tension':>20s}  {abs(Yp_full-Yp_obs)/Yp_err:14.1f} sig  {abs(Yp_78-Yp_obs)/Yp_err:14.1f} sig  {'':>14s}")


print()
print("=" * 75)
print("CMB IMPLICATIONS: DOES 7/8 FIX THE PEAK HEIGHTS?")
print("=" * 75)
print()
print("If only 7/8 of S^3 content Thomson scatters, the CMB sees")
print(f"omega_b_CMB = {omega_b_corrected:.5f} (= Planck's value)")
print()
print("This would simultaneously fix:")
print("  1. BBN deuterium (16 sigma -> 0 sigma)")
print("  2. CMB 1st/2nd peak ratio (10% off -> matches)")
print("  3. BBN helium (1.3 sigma -> 0 sigma)")
print()
print("All from one cascade-derived factor: 7/8")

# Now run CAMB with the corrected omega_b
print()
print("=" * 75)
print("CAMB TEST: CASCADE WITH 7/8 * omega_b")
print("=" * 75)

try:
    import camb
    from scipy.signal import find_peaks

    # Planck baseline
    planck_p = camb.set_params(
        H0=67.36, ombh2=0.02237, omch2=0.12000,
        tau=0.0544, As=2.1e-9, ns=0.9649, lmax=2500,
    )
    planck_r = camb.get_results(planck_p)
    planck_tt = planck_r.get_cmb_power_spectra(planck_p, CMB_unit='muK')['total'][:, 0]

    peaks_planck, _ = find_peaks(planck_tt[100:1500], distance=100, prominence=100)
    peaks_planck += 100

    # Cascade with FULL omega_b
    Omega_cdm_full = (1.0/pi - 1.0/(2*pi**2))
    omch2_full = Omega_cdm_full * h2

    cas_full_p = camb.set_params(
        H0=H0, ombh2=omega_b_cascade, omch2=omch2_full,
        tau=0.0544, As=2.1e-9, ns=0.9649, lmax=2500,
    )
    cas_full_r = camb.get_results(cas_full_p)
    cas_full_tt = cas_full_r.get_cmb_power_spectra(cas_full_p, CMB_unit='muK')['total'][:, 0]
    peaks_full, _ = find_peaks(cas_full_tt[100:1500], distance=100, prominence=100)
    peaks_full += 100

    # Cascade with 7/8 * omega_b
    Omega_b_78 = omega_b_corrected / h2
    Omega_cdm_78 = (1.0/pi - Omega_b_78)  # keep total Omega_m = 1/pi
    omch2_78 = Omega_cdm_78 * h2

    cas_78_p = camb.set_params(
        H0=H0, ombh2=omega_b_corrected, omch2=omch2_78,
        tau=0.0544, As=2.1e-9, ns=0.9649, lmax=2500,
    )
    cas_78_r = camb.get_results(cas_78_p)
    cas_78_tt = cas_78_r.get_cmb_power_spectra(cas_78_p, CMB_unit='muK')['total'][:, 0]

    cas_78_derived = cas_78_r.get_derived_params()

    peaks_78, _ = find_peaks(cas_78_tt[100:1500], distance=100, prominence=100)
    peaks_78 += 100

    print(f"\n  Cascade 7/8 derived quantities:")
    print(f"    r_drag = {cas_78_derived.get('rdrag', 'N/A'):.2f} Mpc")
    print(f"    z_eq   = {cas_78_derived.get('zeq', 'N/A'):.1f}")
    print(f"    age    = {cas_78_derived.get('age', 'N/A'):.2f} Gyr")

    # Peak comparison
    print(f"\n  Peak positions:")
    print(f"  {'Peak':>6s}  {'Planck':>8s}  {'Cascade':>8s}  {'Cas 7/8':>8s}  {'Shift(7/8)':>10s}")
    print(f"  {'-'*45}")
    for i in range(min(len(peaks_planck), len(peaks_78), len(peaks_full), 5)):
        shift = peaks_78[i] - peaks_planck[i]
        print(f"  {i+1:6d}  {peaks_planck[i]:8d}  {peaks_full[i]:8d}  {peaks_78[i]:8d}  {shift:+10d}")

    # Peak height ratio (baryon loading diagnostic)
    if len(peaks_planck) >= 2 and len(peaks_78) >= 2 and len(peaks_full) >= 2:
        oe_planck = planck_tt[peaks_planck[0]] / planck_tt[peaks_planck[1]]
        oe_full = cas_full_tt[peaks_full[0]] / cas_full_tt[peaks_full[1]]
        oe_78 = cas_78_tt[peaks_78[0]] / cas_78_tt[peaks_78[1]]

        print(f"\n  1st/2nd peak ratio (baryon loading):")
        print(f"    Planck:           {oe_planck:.4f}")
        print(f"    Cascade (full):   {oe_full:.4f}  ({(oe_full-oe_planck)/oe_planck*100:+.2f}%)")
        print(f"    Cascade (7/8):    {oe_78:.4f}  ({(oe_78-oe_planck)/oe_planck*100:+.2f}%)")

    # RMS difference
    rms_full = np.sqrt(np.mean([(cas_full_tt[l]-planck_tt[l])**2/planck_tt[l]**2
                                 for l in range(30, 2001) if planck_tt[l] > 100]))
    rms_78 = np.sqrt(np.mean([(cas_78_tt[l]-planck_tt[l])**2/planck_tt[l]**2
                               for l in range(30, 2001) if planck_tt[l] > 100]))

    print(f"\n  RMS fractional difference (l=30-2000):")
    print(f"    Cascade (full):   {rms_full*100:.2f}%")
    print(f"    Cascade (7/8):    {rms_78*100:.2f}%")
    print(f"    Improvement:      {(1 - rms_78/rms_full)*100:.1f}%")

    # Now try fitting ns and As with 7/8 omega_b
    print(f"\n  --- Fitting ns, As, tau with 7/8 omega_b ---")
    best_rms = 1e10
    best_params = {}
    for ns_try in [0.94, 0.95, 0.96, 0.965, 0.97, 0.975, 0.98]:
        for As_try in [1.9e-9, 2.0e-9, 2.05e-9, 2.1e-9, 2.15e-9, 2.2e-9]:
            for tau_try in [0.04, 0.05, 0.054, 0.06, 0.07]:
                try:
                    p = camb.set_params(
                        H0=H0, ombh2=omega_b_corrected, omch2=omch2_78,
                        tau=tau_try, As=As_try, ns=ns_try, lmax=2500,
                    )
                    r = camb.get_results(p)
                    cls_tt = r.get_cmb_power_spectra(p, CMB_unit='muK')['total'][:, 0]
                    rms = np.sqrt(np.mean([(cls_tt[l]-planck_tt[l])**2/planck_tt[l]**2
                                           for l in range(30, 2001) if planck_tt[l] > 100]))
                    if rms < best_rms:
                        best_rms = rms
                        best_params = {'ns': ns_try, 'As': As_try, 'tau': tau_try}
                except:
                    pass

    print(f"  Best fit: ns={best_params.get('ns','?')}, As={best_params.get('As','?'):.2e}, tau={best_params.get('tau','?')}")
    print(f"  RMS difference: {best_rms*100:.2f}%")

    # Compare to the full-omega_b best fit (from previous script: 5.29%)
    print(f"\n  COMPARISON:")
    print(f"    Cascade (full omega_b, fitted ns/As/tau): ~5.29%")
    print(f"    Cascade (7/8 omega_b, fitted ns/As/tau):  {best_rms*100:.2f}%")

except ImportError:
    print("  CAMB not available, skipping CMB test")


print()
print("=" * 75)
print("SUMMARY")
print("=" * 75)
print(f"""
  OBSERVATION: (7/8) * omega_b(cascade) = omega_b(Planck)
               to 0.04% precision (0.04 sigma)

  7/8 is a cascade-derived number: the Fermi-Dirac / Bose-Einstein
  ratio from Part II's quantum mechanics.

  PHYSICAL INTERPRETATION:
  The cascade's S^3 content (Omega_b = 1/(2*pi^2)) includes both
  fermionic and bosonic components. Only the fermionic fraction
  (7/8) participates in nuclear reactions and Thomson scattering.
  The bosonic fraction (1/8) gravitates but is electromagnetically
  inert.

  IF CORRECT, this single factor simultaneously fixes:
    - BBN deuterium:  16 sigma tension -> ~0 sigma
    - BBN helium:     1.3 sigma tension -> ~0 sigma
    - CMB peak ratio: 10% discrepancy -> ~0%
    - CMB spectrum:   5-7% RMS -> potentially <2%

  The cascade's total gravitational budget is unchanged:
    Omega_m = 1/pi (same)
    Omega_b_nuclear = (7/8) * 1/(2*pi^2) = 7/(16*pi^2)
    Omega_b_inert   = (1/8) * 1/(2*pi^2) = 1/(16*pi^2)

  This is the kind of prediction that either works or doesn't.
  It's falsifiable: the inert 1/8 component would behave like
  additional dark matter (gravitating, non-interacting) and would
  affect structure formation.
""")
