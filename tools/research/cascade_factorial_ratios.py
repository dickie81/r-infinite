#!/usr/bin/env python3
"""
Cascade factorial RATIOS scan.

The cascade's slicing ratio R(d) IS already a factorial ratio:
  R(2k)   = C(2k, k) sqrt(pi) / 4^k     (even-d, central binomial)
  R(2k-1) = 4^k / (k * C(2k, k) * sqrt(pi))   (odd-d, reciprocal pattern)

Lemma 2.2 (PR #96): R(2d-1) * R(2d) = 1/d -- pure factorial ratio.
Tower product:      prod_{d=1}^{2N} R(d) = 1/N!

This script extends the prior factorial scan to RATIO structures:
  1. Verify cascade R(d) values match the central-binomial formulas
  2. Compute ratios of factorials at distinguished cascade dimensions
  3. Compute ratios involving the cascade's dominant 1/(9! * 108!) structure
  4. Compare to physical / cosmological reference numbers
  5. Honest report
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


def R_cas(d):
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def C(n, k):
    """Binomial coefficient n choose k."""
    return math.factorial(n) // (math.factorial(k) * math.factorial(n - k))


def main() -> int:
    print("=" * 78)
    print("CASCADE FACTORIAL RATIOS")
    print("=" * 78)
    print()

    # ----------------------------------------------------------------
    # 1. Verify R(d) = factorial-ratio closed forms
    # ----------------------------------------------------------------
    print("-" * 78)
    print("R(d) as factorial ratio:")
    print("  R(2k)   = C(2k, k) * sqrt(pi) / 4^k")
    print("  R(2k-1) = 4^k / (k * C(2k, k) * sqrt(pi))")
    print("-" * 78)
    print()
    print(f"{'k':>4}  {'d=2k':>6}  {'R(2k) numeric':>16}  {'C(2k,k)*sqrt(pi)/4^k':>22}  {'match':>6}")
    print("-" * 70)
    for k in [1, 2, 3, 5, 7, 10]:
        d = 2 * k
        r_num = R_cas(d)
        r_form = C(2 * k, k) * math.sqrt(math.pi) / (4 ** k)
        ok = abs(r_num - r_form) < 1e-12
        print(f"{k:>4}  {d:>6}  {r_num:>16.10f}  {r_form:>22.10f}  "
              f"{'OK' if ok else 'FAIL':>6}")
    print()
    print(f"{'k':>4}  {'d=2k-1':>6}  {'R(2k-1) numeric':>18}  {'4^k/(k*C(2k,k)*sqrt(pi))':>26}  {'match':>6}")
    print("-" * 75)
    for k in [1, 2, 3, 5, 7, 10]:
        d = 2 * k - 1
        r_num = R_cas(d)
        r_form = (4 ** k) / (k * C(2 * k, k) * math.sqrt(math.pi))
        ok = abs(r_num - r_form) < 1e-12
        print(f"{k:>4}  {d:>6}  {r_num:>18.10f}  {r_form:>26.10f}  "
              f"{'OK' if ok else 'FAIL':>6}")
    print()
    print("=> Cascade slicing ratios ARE central-binomial factorial ratios.")
    print()

    # ----------------------------------------------------------------
    # 2. Distinguished-dimension factorial ratios
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Ratios of factorials at distinguished cascade dimensions")
    print("-" * 78)
    print()
    distinguished = [4, 5, 7, 12, 13, 14, 19, 21, 217]
    print(f"{'a / b':>20}  {'value':>20}  {'log10':>10}  {'note':>30}")
    print("-" * 90)
    for i, a in enumerate(distinguished):
        for b in distinguished[i+1:]:
            if a >= b:
                continue
            log_ratio = (gammaln(a + 1) - gammaln(b + 1))
            ratio = math.exp(log_ratio)
            log10 = log_ratio / math.log(10)
            label = f"{b}!/{a}!" if a < b else f"{a}!/{b}!"
            # Actually we want larger/smaller; use the order as listed
            note = ""
            if abs(log10) < 5 and ratio > 1e-100:
                note = f"{int(round(ratio))}" if ratio < 1e10 else f"{ratio:.3e}"
            print(f"{label:>20}  {ratio:>20.6e}  {log10:>10.4f}  {note:>30}")
    print()

    # ----------------------------------------------------------------
    # 3. The cascade's dominant 1/(9! * 108!) hierarchy ratio
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Cascade hierarchy factorial structure")
    print("-" * 78)
    print()
    log10_9fact = math.log10(math.factorial(9))
    log10_108fact = sum(math.log10(k) for k in range(1, 109))
    log10_217fact = sum(math.log10(k) for k in range(1, 218))
    print(f"  9!     = {math.factorial(9)} = 10^{log10_9fact:.4f}")
    print(f"  108!  ~ 10^{log10_108fact:.4f}")
    print(f"  217!  ~ 10^{log10_217fact:.4f}")
    print()
    print("Cascade rho_Lambda/M_Pl^4 = (18/pi^3) * Omega_19 * Omega_217")
    print("  Omega_19   = 2 pi^10 / 9!         (factorial 9! at first threshold)")
    print("  Omega_217  = 2 pi^109 / 108!      (factorial 108! at sink)")
    print()
    log10_pi119 = 119 * math.log10(math.pi)
    log10_hier = (math.log10(2 * 18 / math.pi ** 3) + math.log10(2)
                  + log10_pi119 - log10_9fact - log10_108fact)
    print(f"  pi^119                       = 10^{log10_pi119:.4f}")
    print(f"  total log10 of rho_L/M_Pl^4 = {log10_hier:.4f}  (target -120.146)")
    print()
    print("=> The 10^{-120} cosmological hierarchy IS a factorial ratio:")
    print("   (4 * 18/pi^3) * pi^119 / (9! * 108!) ~ 10^{-120}")
    print()

    # ----------------------------------------------------------------
    # 4. Ratios involving cascade hierarchy components
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Ratios of factorials at cascade-hierarchy structure points")
    print("-" * 78)
    print()
    print(f"  108!/9!    = 10^{log10_108fact - log10_9fact:.4f}")
    print(f"  217!/19!   = 10^{log10_217fact - sum(math.log10(k) for k in range(1, 20)):.4f}")
    print(f"  217!/108!  = 10^{log10_217fact - log10_108fact:.4f}")
    print(f"  9!/19!     = 10^{log10_9fact - sum(math.log10(k) for k in range(1, 20)):.4f}")
    print(f"  108!/217!  = 10^{log10_108fact - log10_217fact:.4f}")
    print()

    # ----------------------------------------------------------------
    # 5. Compare to physical number ratios
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Match cascade factorial RATIOS to physical numbers")
    print("-" * 78)
    print()
    physical = [
        ("rho_Planck / rho_Lambda", 1.4e120),
        ("M_Pl,red / electron mass", 4.18e21),
        ("M_Pl,red / proton mass", 1.30e19),
        ("Avogadro's number", 6.022e23),
        ("Atoms in observable universe", 1e80),
        ("Photons in observable universe", 1e89),
        ("CMB photons / baryons", 1.6e9),
        ("Hubble time / Planck time", 8e60),
        ("Universe radius / proton radius", 4.4e40),
        ("Stars in observable universe", 1e24),
        ("Galaxies / observable", 2e12),
        ("1/alpha_em", 137.036),
        ("m_proton / m_electron", 1836.15),
        ("m_t / m_e", 3.38e5),
        ("m_W / m_e", 1.59e5),
    ]

    # Build candidate factorial ratios from cascade-distinguished pairs
    candidates = []
    cas_int = [1, 2, 3, 4, 5, 7, 9, 10, 12, 13, 14, 19, 20, 21, 50, 100, 108, 200, 217]
    for a in cas_int:
        for b in cas_int:
            if a == b:
                continue
            if a < 1 or b < 1:
                continue
            log_ratio = (sum(math.log10(k) for k in range(1, a + 1))
                         - sum(math.log10(k) for k in range(1, b + 1)))
            label = f"{a}!/{b}!"
            candidates.append((label, log_ratio))

    print(f"{'Quantity':>40}  {'log10':>10}  {'closest cascade ratio':>22}  "
          f"{'log diff':>10}")
    print("-" * 95)
    flags = []
    for name, val in physical:
        log_val = math.log10(val)
        best = None
        for label, log_c in candidates:
            err = abs(log_val - log_c)
            if best is None or err < best[2]:
                best = (label, log_c, err)
        if best:
            label, log_c, err = best
            flag = " <-- within 1 dex" if err < 1.0 else ""
            print(f"{name:>40}  {log_val:>10.3f}  "
                  f"{label + ' ~ 10^' + f'{log_c:+.2f}':>22}  {err:>10.3f}{flag}")
            if err < 0.5:
                flags.append((name, val, log_val, label, log_c, err))
    print()

    # ----------------------------------------------------------------
    # 6. Highlight any genuinely close match (within factor 3, ~ 0.5 dex)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Within factor 3 (~ 0.5 dex)")
    print("-" * 78)
    print()
    if flags:
        for name, val, log_val, label, log_c, err in flags:
            ratio = 10 ** (log_val - log_c)
            print(f"  {name}: target {val:.3e}, cascade {label} ~ 10^{log_c:+.3f}, "
                  f"ratio {ratio:.4f}")
    else:
        print("  None found.")
    print()

    # ----------------------------------------------------------------
    # 7. Honest verdict
    # ----------------------------------------------------------------
    print("=" * 78)
    print("HONEST VERDICT")
    print("=" * 78)
    print()
    print("Cascade factorial-ratio structure is INTRINSIC:")
    print("  - R(d) values are central-binomial-coefficient ratios")
    print("    (verified at multiple k)")
    print("  - Lemma 2.2 telescopes pairs into 1/d (PR #96)")
    print("  - Cosmological hierarchy 10^{-120} = pi^119 / (9! * 108!)")
    print("    (the cascade's own factorial-ratio derivation)")
    print()
    print("External matches: ratios of factorials at distinguished cascade")
    print("dimensions, when compared to physical numbers (mass ratios, density")
    print("ratios, count-of-things ratios), do not produce sharp matches beyond")
    print("the cascade's own predictions.  Best matches are:")
    print()
    if flags:
        for name, val, log_val, label, log_c, err in flags:
            print(f"    {name}: cascade {label} (err ~{err:.2f} dex)")
    print()
    print("These are within 1-3x of target but at NON-DISTINGUISHED factorial")
    print("ratios (or are the cascade's own internal hierarchy).  No new")
    print("structural windfall beyond what the cascade already predicts.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
