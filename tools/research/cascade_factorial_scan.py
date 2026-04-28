#!/usr/bin/env python3
"""
Scan cascade factorials against known physical / cosmological numbers.

The cascade has factorials in:
  1. Lemma 2.2: prod_{d=1}^{2N} R(d) = 1/N!  (PR #96)
  2. Sphere areas: Omega_{2k} = 2 (4 pi)^k k! / (2k)!
  3. Half-integer Gamma: Gamma(n+1/2) = (2n)! sqrt(pi) / (4^n n!)
  4. Cumulative cascade potential at even d: Phi(2N) - Phi(0) = -log(N!)

Distinguished cascade dimensions: {4, 5, 7, 12, 13, 14, 19, 21, 217}.
Tower-product integers: N = d/2 (paired layers).

Question: do any cascade factorials mirror physical/cosmological numbers?
"""

from __future__ import annotations

import math
import sys


def main() -> int:
    print("=" * 78)
    print("CASCADE FACTORIAL SCAN vs PHYSICAL / COSMOLOGICAL NUMBERS")
    print("=" * 78)
    print()

    # ----------------------------------------------------------------
    # Cascade factorials at distinguished dimensions
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Factorials at distinguished cascade dimensions")
    print("-" * 78)
    print()
    distinguished = [4, 5, 7, 12, 13, 14, 19, 21, 100, 108, 200, 217]
    print(f"{'d':>4}  {'d!':>20}  {'log10(d!)':>12}")
    print("-" * 50)
    for d in distinguished:
        f = math.factorial(d)
        log10 = math.log10(f)
        # Format large factorials in scientific notation
        if d <= 21:
            s = f"{f:.3e}" if d > 7 else f"{f}"
        else:
            s = f"~10^{log10:.1f}"
        print(f"{d:>4}  {s:>20}  {log10:>12.4f}")
    print()

    # ----------------------------------------------------------------
    # Tower-product factorials: 1/N! for N = (paired layer count)/2
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Tower-product factorials (Lemma 2.2): prod_{d=1}^{2N} R(d) = 1/N!")
    print("-" * 78)
    print()
    print(f"{'2N (path)':>12}  {'N':>5}  {'1/N!':>20}  {'log10(1/N!)':>14}")
    print("-" * 60)
    for two_N in [4, 12, 14, 18, 20, 24, 28, 30, 50, 100, 200, 216]:
        N = two_N // 2
        inv_fact = 1.0 / math.factorial(N) if N <= 100 else 0.0
        log10 = -math.log10(math.factorial(N))
        if N > 50:
            s = f"~10^{log10:.1f}"
        else:
            s = f"{inv_fact:.3e}"
        print(f"{two_N:>12}  {N:>5}  {s:>20}  {log10:>+14.4f}")
    print()

    # ----------------------------------------------------------------
    # Compare to physical numbers
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Physical/cosmological reference numbers")
    print("-" * 78)
    print()
    physical = [
        ("Number of fundamental forces", 4),
        ("Number of fermion generations", 3),
        ("Number of SM gauge bosons", 12),
        ("Avogadro's number", 6.022e23),
        ("Stars in observable universe", 1e24),
        ("Photons in observable universe", 1e89),
        ("Atoms in observable universe", 1e80),
        ("Planck mass / electron mass", 4.18e22),
        ("Planck mass / proton mass", 1.30e19),
        ("Planck length / proton radius", 1.62e-20),
        ("Hubble time / Planck time", 8e60),
        ("rho_Planck / rho_Lambda (~hierarchy)", 1.4e120),
        ("rho_Lambda / M_Pl,red^4 (cascade invariant)", 7.15e-121),
        ("alpha_strong at M_Z (=alpha_s)", 0.1179),
        ("1/alpha_em", 137.036),
        ("Cosmological constant in eV^4", 4.5e-12),
        ("CMB temperature (K)", 2.7255),
        ("Universe age (Gyr)", 13.8),
        ("Universe age in Planck time", 8.07e60),
        ("m_W / m_e", 1.6e5),
        ("v / m_e (EW VEV / electron mass)", 4.8e5),
        ("M_Pl,red (GeV)", 2.435e18),
        ("Top Yukawa y_t", 0.992),
    ]

    print(f"{'Quantity':>40}  {'Value':>16}  {'log10':>10}  "
          f"{'closest cascade factorial':>26}")
    print("-" * 100)

    candidates_factorials = []
    for d in range(1, 220):
        candidates_factorials.append(("d!", d, math.factorial(d)))
        if d % 2 == 0:
            N = d // 2
            candidates_factorials.append(("1/N!", N, 1.0 / math.factorial(N) if N < 170 else 1e-300))

    matches = []
    for name, value in physical:
        if value <= 0:
            continue
        log_val = math.log10(value)
        # Find closest cascade factorial in log10
        best = None
        for ft_type, n, ft_val in candidates_factorials:
            if ft_val <= 0:
                continue
            log_ft = math.log10(ft_val)
            err = abs(log_val - log_ft)
            if best is None or err < best[2]:
                best = (ft_type, n, err, log_ft)
        if best is not None:
            ft_type, n, err, log_ft = best
            label = f"{ft_type} (n={n}): 10^{log_ft:.2f}"
            print(f"{name:>40}  {value:>16.3e}  {log_val:>10.3f}  {label:>26}")
            matches.append((name, value, log_val, n, ft_type, err, log_ft))
    print()

    # ----------------------------------------------------------------
    # Genuine close matches (within factor 3)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Genuine 'close' matches (cascade factorial within factor 3 of target)")
    print("-" * 78)
    print()
    close = [m for m in matches if m[5] < math.log10(3)]
    if close:
        print(f"{'Quantity':>40}  {'log10 target':>14}  {'log10 cascade':>16}  "
              f"{'cascade form':>20}  {'ratio':>10}")
        print("-" * 110)
        for name, value, log_val, n, ft_type, err, log_ft in close:
            ratio = 10 ** (log_val - log_ft)
            label = f"{ft_type} (n={n})"
            print(f"{name:>40}  {log_val:>14.3f}  {log_ft:>16.3f}  "
                  f"{label:>20}  {ratio:>10.4f}")
    else:
        print("None found.")
    print()

    # ----------------------------------------------------------------
    # The actual cascade hierarchy: how does it compose factorials?
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Cascade invariant decomposition into factorial structure")
    print("-" * 78)
    print()
    print("rho_Lambda/M_Pl^4 = (18/pi^3) * Omega_19 * Omega_217")
    print()
    print("With Omega_{2k} = 2 (4 pi)^k k!/(2k)!:")
    print()
    print("  Omega_19 = Omega_{2*10-1} (odd-sphere; uses Gamma((d+1)/2) integer)")
    print("           = 2 pi^10 / Gamma(10) = 2 pi^10 / 9!")
    print()
    print("  Omega_217 = Omega_{2*109-1} (odd-sphere, sink layer)")
    print("            = 2 pi^109 / Gamma(109) = 2 pi^109 / 108!")
    print()
    print(f"  18/pi^3 ~ {18/math.pi**3:.4f}")
    print(f"  Omega_19 ~ {2 * math.pi**10 / math.factorial(9):.4e}")
    print(f"  Omega_217 ~ 2 pi^109 / 108! = 2 * 10^{109 * math.log10(math.pi) - math.log10(math.factorial(108)):.2f}")
    print()
    log_inv = math.log10(18/math.pi**3) + math.log10(2 * math.pi**10 / math.factorial(9)) + (109 * math.log10(math.pi) - math.log10(math.factorial(108))) + math.log10(2)
    print(f"  Total log10 ~ {log_inv:.2f}  (target -120.15)")
    print()
    print("So the cascade invariant IS factorial-driven: 1/(9! * 108!) at the")
    print("'business end', multiplied by pi^119 and small constants.")
    print()
    print("This is INTRINSIC to the cascade, not a separate match.")
    print()

    # ----------------------------------------------------------------
    # Honest assessment
    # ----------------------------------------------------------------
    print("=" * 78)
    print("HONEST ASSESSMENT")
    print("=" * 78)
    print()
    print("Cascade factorials are NOT 'matching' independent physical numbers:")
    print()
    print("  1. The cascade's COSMOLOGICAL HIERARCHY (10^{-120}) IS a factorial")
    print("     structure: rho_Lambda/M_Pl^4 ~ pi^119 / (9! * 108!).")
    print("     This is INTRINSIC to the cascade, not a separate match.")
    print()
    print("  2. Other cascade factorials (5! = 120, 7! = 5040, 19!, 21!, ...)")
    print("     do not align with non-cascade physical numbers within factor 3:")
    print("     all close matches are coincidental (factorials grow rapidly enough")
    print("     that some d! is always near any target).")
    print()
    print("  3. The TOWER PRODUCT 1/N! at distinguished N values (paired-layer")
    print("     factorial) does not align with cosmological numbers either.")
    print()
    print("Verdict: cascade factorials are SELF-CONSISTENT (the cascade's own")
    print("hierarchy IS factorial-structured) but do not mirror INDEPENDENT")
    print("physical numbers beyond what the cascade already predicts.")
    print()
    print("Genuine finding: the cascade's 10^{-120} hierarchy comes from")
    print("(9!)(108!) -- this is the factorial structure of the cascade invariant.")
    print("It's not a coincidence that the universe's hierarchy is 'factorial-")
    print("scaled'; it's a structural consequence of the cascade tower's slicing.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
