#!/usr/bin/env python3
"""
THE DECISIVE TEST: Cascade parameters vs the CMB power spectrum.

The CMB angular power spectrum is measured by Planck to sub-percent
precision. It has ~2500 data points (multipoles l = 2 to 2500).

This script runs CAMB (the standard Boltzmann solver) with:
  (a) Planck best-fit LCDM parameters
  (b) Cascade parameters (H0, Omega_b, Omega_m from pi)
  (c) Cascade parameters with n_s, A_s, tau fitted to Planck data

If (b) or (c) produce an acceptable power spectrum, the cascade
survives the most stringent test in cosmology.
If not, the cascade has a serious problem.

Also computes BBN predictions for the cascade's omega_b.
"""

import numpy as np
import camb

pi = np.pi

# ===================================================================
# PLANCK BEST-FIT LCDM (baseline)
# ===================================================================
print("=" * 75)
print("PLANCK BEST-FIT LCDM (TT,TE,EE+lowE+lensing, 2018)")
print("=" * 75)

planck = camb.set_params(
    H0=67.36,
    ombh2=0.02237,
    omch2=0.1200,
    tau=0.0544,
    As=2.1e-9,
    ns=0.9649,
    lmax=2500,
    WantTransfer=True,
)
planck_results = camb.get_results(planck)
planck_cls = planck_results.get_cmb_power_spectra(planck, CMB_unit='muK')['total']
planck_tt = planck_cls[:, 0]  # TT spectrum

print(f"  H0     = 67.36 km/s/Mpc")
print(f"  ombh2  = 0.02237")
print(f"  omch2  = 0.12000")
print(f"  tau    = 0.0544")
print(f"  ns     = 0.9649")
print(f"  As     = 2.1e-9")

# Peak positions
ls = np.arange(len(planck_tt))
# Find peaks in l range 100-1500
from scipy.signal import find_peaks
peaks_planck, _ = find_peaks(planck_tt[100:1500], distance=100, prominence=100)
peaks_planck += 100
print(f"\n  Peak positions: {peaks_planck[:6]}")
print(f"  First peak: l = {peaks_planck[0]}, amplitude = {planck_tt[peaks_planck[0]]:.1f} muK^2")

# Derived quantities from Planck
planck_derived = planck_results.get_derived_params()
print(f"\n  Derived: z_eq = {planck_derived.get('zeq', 'N/A')}")
print(f"  Derived: r_drag = {planck_derived.get('rdrag', 'N/A')} Mpc")
print(f"  Derived: age = {planck_derived.get('age', 'N/A')} Gyr")

# ===================================================================
# CASCADE PARAMETERS (direct translation)
# ===================================================================
print("\n" + "=" * 75)
print("CASCADE PARAMETERS (direct)")
print("=" * 75)

H0_cas = 71.05
h_cas = H0_cas / 100.0
Omega_b_cas = 1.0 / (2.0 * pi**2)
Omega_m_cas = 1.0 / pi
Omega_cdm_cas = Omega_m_cas - Omega_b_cas

ombh2_cas = Omega_b_cas * h_cas**2
omch2_cas = Omega_cdm_cas * h_cas**2

print(f"  H0     = {H0_cas} km/s/Mpc")
print(f"  h      = {h_cas:.4f}")
print(f"  Omega_b = 1/(2*pi^2) = {Omega_b_cas:.5f}")
print(f"  Omega_m = 1/pi = {Omega_m_cas:.5f}")
print(f"  Omega_cdm = {Omega_cdm_cas:.5f}")
print(f"  ombh2  = {ombh2_cas:.5f}  (Planck: 0.02237, diff: {(ombh2_cas-0.02237)/0.02237*100:+.1f}%)")
print(f"  omch2  = {omch2_cas:.5f}  (Planck: 0.12000, diff: {(omch2_cas-0.12000)/0.12000*100:+.1f}%)")

# Run with cascade parameters but Planck's (tau, ns, As)
# This tests: are the cascade's geometric parameters compatible with the CMB?
cascade_direct = camb.set_params(
    H0=H0_cas,
    ombh2=ombh2_cas,
    omch2=omch2_cas,
    tau=0.0544,       # use Planck's tau (cascade doesn't predict this)
    As=2.1e-9,        # use Planck's As (cascade doesn't predict this)
    ns=0.9649,        # use Planck's ns (cascade doesn't predict this)
    lmax=2500,
    WantTransfer=True,
)
cascade_results = camb.get_results(cascade_direct)
cascade_cls = cascade_results.get_cmb_power_spectra(cascade_direct, CMB_unit='muK')['total']
cascade_tt = cascade_cls[:, 0]

cascade_derived = cascade_results.get_derived_params()
print(f"\n  Derived: z_eq = {cascade_derived.get('zeq', 'N/A')}")
print(f"  Derived: r_drag = {cascade_derived.get('rdrag', 'N/A')} Mpc")
print(f"  Derived: age = {cascade_derived.get('age', 'N/A')} Gyr")

# Peak positions
peaks_cas, _ = find_peaks(cascade_tt[100:1500], distance=100, prominence=100)
peaks_cas += 100
print(f"\n  Peak positions: {peaks_cas[:6]}")
if len(peaks_cas) > 0:
    print(f"  First peak: l = {peaks_cas[0]}, amplitude = {cascade_tt[peaks_cas[0]]:.1f} muK^2")

# Compare peaks
print(f"\n  Peak position comparison:")
print(f"  {'Peak':>6s}  {'Planck l':>10s}  {'Cascade l':>10s}  {'Shift':>8s}  {'Shift %':>8s}")
print(f"  {'-'*50}")
for i in range(min(len(peaks_planck), len(peaks_cas), 5)):
    shift = peaks_cas[i] - peaks_planck[i]
    pct = shift / peaks_planck[i] * 100
    print(f"  {i+1:6d}  {peaks_planck[i]:10d}  {peaks_cas[i]:10d}  {shift:+8d}  {pct:+7.2f}%")

# Fractional difference in TT spectrum
frac_diff = np.zeros(2501)
for l in range(2, 2501):
    if planck_tt[l] > 0:
        frac_diff[l] = (cascade_tt[l] - planck_tt[l]) / planck_tt[l]

print(f"\n  RMS fractional difference (l=2-2500): {np.sqrt(np.mean(frac_diff[2:2501]**2))*100:.2f}%")
print(f"  RMS fractional difference (l=2-800):  {np.sqrt(np.mean(frac_diff[2:800]**2))*100:.2f}%")
print(f"  RMS fractional difference (l=800-2500): {np.sqrt(np.mean(frac_diff[800:2501]**2))*100:.2f}%")
print(f"  Max fractional difference: {np.max(np.abs(frac_diff[2:2501]))*100:.2f}% at l={np.argmax(np.abs(frac_diff[2:2501]))+2}")

# ===================================================================
# CASCADE WITH ADJUSTED (tau, ns, As)
# ===================================================================
print("\n" + "=" * 75)
print("CASCADE WITH FITTED (tau, ns, As)")
print("=" * 75)
print()
print("The cascade doesn't predict tau, ns, or As. Can we fit them")
print("to bring the CMB spectrum closer to Planck?")

# Try different ns values
best_rms = 1e10
best_ns = 0.96
best_As = 2.1e-9
best_tau = 0.054

for ns_try in [0.93, 0.94, 0.95, 0.96, 0.965, 0.97, 0.98, 0.99, 1.00]:
    for As_try in [1.8e-9, 1.9e-9, 2.0e-9, 2.1e-9, 2.2e-9, 2.3e-9]:
        for tau_try in [0.04, 0.05, 0.06, 0.07]:
            try:
                p = camb.set_params(
                    H0=H0_cas, ombh2=ombh2_cas, omch2=omch2_cas,
                    tau=tau_try, As=As_try, ns=ns_try,
                    lmax=2500, WantTransfer=True,
                )
                r = camb.get_results(p)
                cls = r.get_cmb_power_spectra(p, CMB_unit='muK')['total'][:, 0]

                # Compute weighted RMS difference (weight by 1/l to emphasize large scales)
                rms = 0.0
                count = 0
                for l in range(30, 2001):
                    if planck_tt[l] > 100:  # only compare where signal is significant
                        rms += ((cls[l] - planck_tt[l]) / planck_tt[l])**2
                        count += 1
                rms = np.sqrt(rms / count) if count > 0 else 1e10

                if rms < best_rms:
                    best_rms = rms
                    best_ns = ns_try
                    best_As = As_try
                    best_tau = tau_try
            except:
                pass

print(f"  Best fit: ns = {best_ns}, As = {best_As:.2e}, tau = {best_tau}")
print(f"  RMS fractional difference: {best_rms*100:.2f}%")

# Run with best fit
cascade_fit = camb.set_params(
    H0=H0_cas, ombh2=ombh2_cas, omch2=omch2_cas,
    tau=best_tau, As=best_As, ns=best_ns,
    lmax=2500, WantTransfer=True,
)
cascade_fit_results = camb.get_results(cascade_fit)
cascade_fit_cls = cascade_fit_results.get_cmb_power_spectra(cascade_fit, CMB_unit='muK')['total']
cascade_fit_tt = cascade_fit_cls[:, 0]

peaks_fit, _ = find_peaks(cascade_fit_tt[100:1500], distance=100, prominence=100)
peaks_fit += 100

print(f"\n  Peak position comparison (fitted):")
print(f"  {'Peak':>6s}  {'Planck l':>10s}  {'Cascade l':>10s}  {'Shift':>8s}")
print(f"  {'-'*40}")
for i in range(min(len(peaks_planck), len(peaks_fit), 5)):
    shift = peaks_fit[i] - peaks_planck[i]
    print(f"  {i+1:6d}  {peaks_planck[i]:10d}  {peaks_fit[i]:10d}  {shift:+8d}")

frac_fit = np.zeros(2501)
for l in range(2, 2501):
    if planck_tt[l] > 0:
        frac_fit[l] = (cascade_fit_tt[l] - planck_tt[l]) / planck_tt[l]

print(f"\n  RMS difference (l=30-2000): {best_rms*100:.2f}%")
print(f"  RMS difference (l=2-2500): {np.sqrt(np.mean(frac_fit[2:2501]**2))*100:.2f}%")

# ===================================================================
# KEY DIAGNOSTIC: PEAK RATIOS AND SPACING
# ===================================================================
print("\n" + "=" * 75)
print("DIAGNOSTIC: PEAK HEIGHTS AND SPACING")
print("=" * 75)

print(f"\n  The CMB peak structure encodes specific physics:")
print(f"  - Peak POSITIONS: angular diameter distance / sound horizon")
print(f"  - Peak HEIGHTS: baryon loading (Omega_b h^2)")
print(f"  - Odd/even RATIO: baryon-to-photon ratio")
print()

# Peak heights
print(f"  {'Peak':>6s}  {'Planck height':>14s}  {'Cascade height':>14s}  {'Ratio':>8s}")
print(f"  {'-'*50}")
for i in range(min(len(peaks_planck), len(peaks_cas), 5)):
    h_p = planck_tt[peaks_planck[i]]
    h_c = cascade_tt[peaks_cas[i]]
    print(f"  {i+1:6d}  {h_p:14.1f}  {h_c:14.1f}  {h_c/h_p:8.3f}")

# Odd/even peak ratio (sensitive to baryon loading)
if len(peaks_planck) >= 3 and len(peaks_cas) >= 3:
    oe_planck = planck_tt[peaks_planck[0]] / planck_tt[peaks_planck[1]]
    oe_cascade = cascade_tt[peaks_cas[0]] / cascade_tt[peaks_cas[1]]
    print(f"\n  1st/2nd peak ratio (baryon loading):")
    print(f"    Planck:  {oe_planck:.3f}")
    print(f"    Cascade: {oe_cascade:.3f}")
    print(f"    Difference: {(oe_cascade-oe_planck)/oe_planck*100:+.2f}%")

# Peak spacing (sensitive to sound horizon)
if len(peaks_planck) >= 3 and len(peaks_cas) >= 3:
    spacing_planck = peaks_planck[2] - peaks_planck[0]
    spacing_cascade = peaks_cas[2] - peaks_cas[0]
    print(f"\n  Peak spacing (1st to 3rd):")
    print(f"    Planck:  {spacing_planck}")
    print(f"    Cascade: {spacing_cascade}")
    print(f"    Difference: {(spacing_cascade-spacing_planck)/spacing_planck*100:+.2f}%")


# ===================================================================
# BBN CHECK
# ===================================================================
print("\n" + "=" * 75)
print("BBN CHECK: PRIMORDIAL ELEMENT ABUNDANCES")
print("=" * 75)

print(f"""
  The cascade predicts omega_b = {ombh2_cas:.5f} (vs Planck 0.02237)
  This is {(ombh2_cas - 0.02237)/0.02237*100:+.1f}% higher.

  BBN predictions scale approximately as:
  - Y_p (He-4): increases with omega_b (~+0.01 per +0.001 in omega_b)
  - D/H: DECREASES sharply with omega_b (~-15% per +10% in omega_b)

  Standard BBN with omega_b = 0.02237: Y_p = 0.2471, D/H = 2.54e-5
  Cascade with omega_b = {ombh2_cas:.5f}:

  Approximate scaling (Cyburt et al. 2016):
    Y_p ~ 0.2471 + 0.014 * ln(omega_b/0.02237) * (Neff/3.0)
    D/H ~ 2.54e-5 * (omega_b/0.02237)^(-1.6)
""")

# Approximate BBN predictions
omega_b_ratio = ombh2_cas / 0.02237
Yp_cascade = 0.2471 + 0.014 * np.log(omega_b_ratio)
DH_cascade = 2.54e-5 * omega_b_ratio**(-1.6)

print(f"  Predicted Y_p (He-4): {Yp_cascade:.4f}")
print(f"    Observed: 0.245 +/- 0.003")
print(f"    Tension: {abs(Yp_cascade - 0.245)/0.003:.1f} sigma")

print(f"\n  Predicted D/H: {DH_cascade:.3e}")
print(f"    Observed: (2.527 +/- 0.030) x 10^-5")
print(f"    Tension: {abs(DH_cascade - 2.527e-5)/0.030e-5:.1f} sigma")

# With N_eff = 3.0 instead of 3.044
print(f"\n  Effect of cascade N_eff = 3.0 (vs standard 3.044):")
print(f"    Lower N_eff -> slightly lower Y_p (helps)")
print(f"    delta_Yp from N_eff: ~ -0.014 * (3.044-3.0)/3.0 = {-0.014*0.044/3.0:.5f}")
Yp_corrected = Yp_cascade - 0.014 * 0.044 / 3.0
print(f"    Corrected Y_p: {Yp_corrected:.4f} (tension: {abs(Yp_corrected-0.245)/0.003:.1f} sigma)")
print(f"    D/H unchanged by N_eff at first order")


# ===================================================================
# SUMMARY
# ===================================================================
print("\n" + "=" * 75)
print("SUMMARY: DOES THE CASCADE SURVIVE THE CMB?")
print("=" * 75)

print(f"""
  Three tests were performed:

  1. CMB POWER SPECTRUM (cascade params, Planck tau/ns/As):
     - Peak positions shift by ~{abs(peaks_cas[0]-peaks_planck[0]) if len(peaks_cas)>0 else 'N/A'} multipoles ({abs(peaks_cas[0]-peaks_planck[0])/peaks_planck[0]*100 if len(peaks_cas)>0 else 0:.1f}%)
     - RMS fractional difference: {np.sqrt(np.mean(frac_diff[2:2501]**2))*100:.1f}%
     - Peak heights change due to higher omega_b (baryon loading)

  2. CMB with fitted (tau, ns, As):
     - Best ns = {best_ns}, As = {best_As:.1e}, tau = {best_tau}
     - RMS difference reduced to: {best_rms*100:.2f}%

  3. BBN:
     - He-4: {abs(Yp_cascade-0.245)/0.003:.1f} sigma tension
     - D/H: {abs(DH_cascade-2.527e-5)/0.030e-5:.1f} sigma tension
     - Deuterium is the CRITICAL test
""")
