#!/usr/bin/env python3
"""
Case B: the m_H/m_W residual (+0.80% from pi/2) -- can it be closed?

Source (Check 1): part4b:3040-3095 (the geodesic pi/2 lives ON S^12, the
SU(2) window sphere: window-SPHERE content, no descent exponential) and
part4b:3276-3293 (V(theta) = cos^2(theta)/2, geodesic identification
theta = (pi/2) h/v STATED, not action-derived -- their Tier-3 caveat).

Findings: (1) widening the G flag to capture the fitting Gauge member is
REFUTED by the sin2thW guard (15 sigma); (2) at current m_H precision
the needed shift is underdetermined (>= 3 candidates within ~1 sigma);
(3) resolution paths: HL-LHC m_H (~25 MeV) separates candidates at ~6
sigma, or the action-derived geodesic normalisation forces the answer.
"""
import math

def R(d): return math.gamma((d+1)/2)/math.gamma((d+2)/2)
def a(d): return R(d)**2/4

# needed shift for m_H/m_W
obs = 125.25/80.377; lead = math.pi/2
need = math.log(obs/lead)
sig  = math.hypot(0.17/125.25, 0.012/80.377)
print(f"m_H/m_W: needed shift {need:+.5f} +/- {sig:.5f}  ({need/sig:.1f} sigma from zero)")

print("\nGUARD TEST: widening G to 'any window occupancy' must not break")
print("established rows.  sin2thW also contains window-layer statics")
print("(N(13), N(14)); under widened G it would move Observer -> Gauge:")
s2w_need = 0.01125; s2w_sig = 0.00017
print(f"  sin2thW needed +{s2w_need:.5f} +/- {s2w_sig:.5f};"
      f" Gauge member alpha(14)/chi^2 = {a(14)/4:.5f}"
      f" -> {abs(a(14)/4 - s2w_need)/s2w_sig:.0f} sigma  ** KILLED **")
print("  => the widening is REFUTED: window-layer static VALUES must stay")
print("     Observer; only window DESCENT exponentials are Gauge.  The flag")
print("     system's integrity blocks the cheap closure.")

print("\nCANDIDATE TABLE at current precision (sigma = 0.00137):")
aem = 1/137.035999
cands = [
    ("-alpha(5)/chi^3   (flag-assigned Observer)", -a(5)/8),
    ("-alpha(14)/chi^2  (Gauge member)",           -a(14)/4),
    ("-alpha(19)/chi^2",                           -a(19)/4),
    ("-alpha_em         (radiative slot, m-k=0?)", -aem),
    ("-alpha_em/(2pi) x 7  (n_above=7, unforced)", -aem/(2*math.pi)*7),
    ("-alpha_s(MZ)/4pi",                           -0.1179/(4*math.pi)),
]
for lab, v in cands:
    print(f"  {lab:<46} {v:+.5f}  ({abs(v-need)/sig:4.1f} sigma)")
print("  => UNDERDETERMINED: >= 3 candidates within ~1 sigma.  Any 'closure'")
print("     today would be selection, not forcing.")

print("\nDISCRIMINATION PATHS:")
new_sig = math.hypot(0.025/125.25, 0.005/80.377)   # HL-LHC-era m_H ~ 25 MeV
print(f"  HL-LHC (m_H to ~25 MeV): sigma_shift -> {new_sig:.5f};")
print(f"  separation alpha(14)/chi^2 vs alpha_em = "
      f"{abs(a(14)/4 - aem):.5f} = {abs(a(14)/4-aem)/new_sig:.0f} new-sigma")
print("  -> the candidates become experimentally distinguishable.")
print("  Theory route: compute d(theta)/dh from the cascade action (the")
print("  papers' own Tier-3 caveat: geodesic identification 'stated rather")
print("  than computed') -- an anharmonic/normalisation correction to pi/2")
print("  of definite size would be the forced closure.")
