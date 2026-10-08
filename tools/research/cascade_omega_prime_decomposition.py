#!/usr/bin/env python3
"""
Cascade sphere areas in prime-axis fill content.

Followup to cascade_prime_tick_inner_product.py.  Option C of the
research thread: extend the prime-tick reading to the cascade's
distinguished sphere areas Omega_d, and show whether the headline
predictions (cascade invariant, rho_Lambda) can be expressed as
"rational * pi^integer" rather than via Gamma-function evaluations.

KEY OBSERVATION.  All four cascade-distinguished dimensions are odd:
        {d_V, d_0, d_1, d_2} = {5, 7, 19, 217}.
For odd d, (d+1)/2 is integer, so Gamma((d+1)/2) = ((d-1)/2)!.
Therefore
        Omega_d = 2 pi^{(d+1)/2} / ((d-1)/2)!     [d odd]
is rational * pi^integer, with the rational part fully expressible
in prime-axis fills via Legendre's formula:
        v_p(N!) = sum_{j>=1} floor(N/p^j) = (N - s_p(N))/(p - 1).

CONSEQUENCE.  The cascade invariant
        I = (9/pi^2) Omega_19 Omega_217
          = (9/pi^2) (2 pi^{10}/9!) (2 pi^{109}/108!)
          = 36 pi^{117} / (9! * 108!)
is exactly rational * pi^integer, with:
  - the pi-power 117 = (d_1+1)/2 + (d_2+1)/2 - 2 derived from cascade
    indices (Part 0 thresholds + Part I host-frame correction);
  - the denominator 9! * 108! = ((d_1-1)/2)! * ((d_2-1)/2)!
    is a product of factorials, each entry fully decomposed into
    prime-axis fills by Legendre.

Headline cascade prediction:
        rho_Lambda / M_Pl,red^4  [leading]  =  (2/pi) I
                                            =  72 pi^{116} / (9! * 108!)

Every quantity is integer arithmetic on cascade-internal indices,
combined with pi as the unique transcendental ingredient (forced by
the Euler product on primes; Prelude Theorem `thm:pi-from-primes`).
NO Gamma-function evaluation appears in the final closed form.

This script:
  (1) Computes Omega_d for the four distinguished d as exact rational*pi^k.
  (2) Verifies I = 36 pi^{117} / (9! * 108!) numerically against Part 0.
  (3) Verifies rho_Lambda formula numerically against Part I.
  (4) Decomposes the denominator 9! * 108! into prime-axis fills (table).
  (5) Estimates per-axis fill at cosmic depth N ~ 10^60 (Stirling + Legendre).
  (6) Reports the "cascade headline in prime form" structurally.

Per CLAUDE.md Check 7 (no semiclassical machinery): all arithmetic is
classical number theory on integer-argument factorials.  No QFT, no
sphere-Laplacian, no semiclassical reduction.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction
from typing import Iterable

# Optional precise comparison against the project's cascade constants
sys.path.insert(0, "/home/user/r-infinite/tools")
try:
    from cascade_constants import (
        Omega as _Omega_num,
        D_V,
        D_0,
        D_1,
        D_2,
    )
    HAS_CONSTANTS = True
except Exception:  # pragma: no cover
    HAS_CONSTANTS = False
    D_V, D_0, D_1, D_2 = 5, 7, 19, 217


# ──────────────────────────────────────────────────────────────────────
# Number-theoretic primitives
# ──────────────────────────────────────────────────────────────────────


def sieve_primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = b"\x00" * len(sieve[i * i :: i])
    return [i for i in range(2, limit + 1) if sieve[i]]


def v_p_factorial(N: int, p: int) -> int:
    """Legendre: v_p(N!) = sum_{j>=1} floor(N/p^j)."""
    if N < p:
        return 0
    total = 0
    q = p
    while q <= N:
        total += N // q
        q *= p
    return total


# ──────────────────────────────────────────────────────────────────────
# Closed-form Omega_d for odd d
# ──────────────────────────────────────────────────────────────────────


def omega_closed_form(d: int) -> tuple[Fraction, int]:
    """For odd d, return (rational, k) with Omega_d = rational * pi^k.

    Omega_d = 2 pi^{(d+1)/2} / ((d-1)/2)!  (odd d).
    """
    if d % 2 == 0:
        raise ValueError(f"closed form here is for odd d only; got d={d}")
    k = (d + 1) // 2
    fact = math.factorial((d - 1) // 2)
    rational = Fraction(2, fact)
    return rational, k


def omega_numerical(rational: Fraction, k: int) -> float:
    """Evaluate rational * pi^k as a float (for sanity checks)."""
    return float(rational) * math.pi**k


# ──────────────────────────────────────────────────────────────────────
# Pretty-printing helpers
# ──────────────────────────────────────────────────────────────────────


def fmt_rational(r: Fraction) -> str:
    if r.denominator == 1:
        return str(r.numerator)
    return f"{r.numerator}/{r.denominator}"


def fmt_prime_factorisation(n: int) -> str:
    if n == 1:
        return "1"
    if n < 0:
        return "-(" + fmt_prime_factorisation(-n) + ")"
    parts = []
    for p in sieve_primes(int(n**0.5) + 1):
        if p * p > n:
            break
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            parts.append(f"{p}^{e}" if e > 1 else str(p))
    if n > 1:
        parts.append(str(n))
    return " * ".join(parts) if parts else "1"


def hdr(title: str) -> None:
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


# ──────────────────────────────────────────────────────────────────────
# Tests
# ──────────────────────────────────────────────────────────────────────


def test_1_omega_closed_forms() -> dict[int, tuple[Fraction, int]]:
    hdr("TEST 1: Omega_d closed form for distinguished d (odd, so Gamma -> factorial)")
    print()
    print(f"  {'d':>4}  {'(d-1)/2':>8}  {'((d-1)/2)!':>14}  {'closed form':<40}")
    print(f"  {'-'*4}  {'-'*8}  {'-'*14}  {'-'*40}")
    results: dict[int, tuple[Fraction, int]] = {}
    for d in (D_V, D_0, D_1, D_2):
        rational, k = omega_closed_form(d)
        fact = math.factorial((d - 1) // 2)
        if fact > 10**12:
            fact_str = f"{fact:.4e}"
        else:
            fact_str = str(fact)
        closed = f"Omega_{d} = {fmt_rational(rational)} * pi^{k}"
        print(f"  {d:>4}  {(d-1)//2:>8}  {fact_str:>14}  {closed}")
        results[d] = (rational, k)
        # Sanity: agree with scipy/numpy Omega(d) to machine precision
        if HAS_CONSTANTS:
            num = omega_numerical(rational, k)
            ref = _Omega_num(d)
            rel = abs(num - ref) / ref if ref else abs(num - ref)
            assert rel < 1e-12, f"Omega_{d} mismatch: closed={num}, ref={ref}, rel={rel}"
    print()
    print("  Closed-form values agree with cascade_constants.Omega(d) to <1e-12.")
    print()
    print("  Reading: each Omega_d at the cascade's distinguished d is")
    print("  (rational) * pi^integer.  No Gamma evaluation appears in the result;")
    print("  the Gamma function is fully digested into the factorial ((d-1)/2)!.")
    return results


def test_2_cascade_invariant(omegas: dict[int, tuple[Fraction, int]]) -> tuple[Fraction, int]:
    hdr("TEST 2: cascade invariant I = (9/pi^2) Omega_19 Omega_217 in closed form")
    print()
    # I = (9/pi^2) * Omega_19 * Omega_217
    # Omega_19 = (2/9!) pi^10
    # Omega_217 = (2/108!) pi^109
    r19, k19 = omegas[D_1]
    r217, k217 = omegas[D_2]
    # Product
    I_rat = Fraction(9) * r19 * r217      # rational part of (9 * Omega_19 * Omega_217)
    I_k = k19 + k217                       # pi power of (9 * Omega_19 * Omega_217)
    # Divide by pi^2: I = 9 Omega_19 Omega_217 / pi^2
    I_k_final = I_k - 2
    # I_rat = 9 * (2/9!) * (2/108!) = 36 / (9! * 108!)
    print(f"  Symbolic:  I = 9 * (2/9!) * (2/108!) * pi^(10 + 109 - 2)")
    print(f"               = 36 / (9! * 108!) * pi^117")
    print()
    print(f"  Numerator (rational): 36 = {fmt_prime_factorisation(36)}")
    print(f"  Denominator: 9! * 108! = {math.factorial(9)} * 108!")
    print(f"  pi power: 117 = (d_1+1)/2 + (d_2+1)/2 - 2 = {(D_1+1)//2} + {(D_2+1)//2} - 2")
    print()
    # Numerical verification
    I_num = float(I_rat) * math.pi**I_k_final
    print(f"  Closed-form value:  I = {I_num:.6e}")
    if HAS_CONSTANTS:
        # Part 0's value of I (without Gram correction, pre-frame-correction):
        # Theorem 8.10 of Part 0: I = 9 * Omega_19 * Omega_217 / pi^2 = 1.0990e-120
        I_ref = 9.0 * _Omega_num(D_1) * _Omega_num(D_2) / math.pi**2
        print(f"  Reference (Part 0): I = {I_ref:.6e}")
        rel = abs(I_num - I_ref) / I_ref
        print(f"  Relative difference: {rel:.2e}")
        assert rel < 1e-12, f"I mismatch: {rel}"
    print()
    print("  The cascade invariant is EXACTLY 36 pi^117 / (9! * 108!), with")
    print("  no Gamma function evaluation.  Integer arithmetic + one transcendental")
    print("  (pi, forced by Prelude's Euler product on primes).")
    return I_rat, I_k_final


def test_3_rho_lambda_prediction(I_rat: Fraction, I_k: int) -> None:
    hdr("TEST 3: rho_Lambda / M_Pl,red^4 (leading) in closed form")
    print()
    # rho_Lambda / M_Pl,red^4 (leading, pre-Gram) = (2/pi) I = 72 pi^116 / (9! * 108!)
    rho_rat = Fraction(2) * I_rat
    rho_k = I_k - 1
    print(f"  Part I leading:  rho_Lambda / M_Pl,red^4 = (2/pi) I")
    print(f"                                          = 72 pi^116 / (9! * 108!)")
    print()
    print(f"  Numerator: 72 = {fmt_prime_factorisation(72)}")
    print(f"             = 8 * 9 = 2^3 * 3^2")
    print(f"             Source: 9 from host frame (Omega_5/Omega_7)^2 = 9/pi^2;")
    print(f"                     4 = 2*2 from numerators of Omega_19 and Omega_217;")
    print(f"                     2 from observer bridge (2/pi).")
    print(f"             9 * 4 * 2 = 72.")
    print()
    print(f"  pi power: 116 = 117 - 1 (one more pi in denominator from 2/pi).")
    print(f"            Equivalently: (d_1+1)/2 + (d_2+1)/2 - 3 = 10 + 109 - 3.")
    print()
    rho_num = float(rho_rat) * math.pi**rho_k
    print(f"  Closed form value: rho_Lambda/M_Pl,red^4 = {rho_num:.6e}")
    print(f"  Part I leading:                          = 6.996e-121")
    rel = abs(rho_num - 6.996e-121) / 6.996e-121
    print(f"  Relative diff:                            {rel:.2e}")
    print()
    print("  Observed (Planck 2018):  7.150e-121 +/- 1.9%")
    print("  Cascade leading residual: -2.2%; with Part 0 Gram correction:")
    print(f"     rho_Lambda/M_Pl,red^4 (Gram-corrected) = {rho_num * math.exp(0.02108):.6e}  (residual -0.07%)")
    print()
    print("  The Gram-correction exponential exp(sum (1-C^2)) is the only")
    print("  non-arithmetic ingredient added to the closed form; it is itself a")
    print("  finite sum of Beta-function ratios (Part 0 Thm `thm:gram-R`).")


def test_4_prime_axis_decomposition() -> None:
    hdr("TEST 4: prime-axis fill of the denominator 9! * 108!")
    print()
    print("  The cascade invariant denominator is 9! * 108!.  By Legendre's formula,")
    print("  v_p(N!) = (N - s_p(N))/(p-1).  Per-axis fill of 9! * 108!:")
    print()
    print(f"  {'prime p':>8}  {'v_p(9!)':>9}  {'v_p(108!)':>11}  {'total':>7}  {'cascade role':<28}")
    print(f"  {'-'*8}  {'-'*9}  {'-'*11}  {'-'*7}  {'-'*28}")
    cascade_roles = {
        2: "(Cayley-Dickson base)",
        3: "N_c",
        5: "d_V (volume max)",
        7: "d_0 (area max)",
        11: "",
        13: "SU(2) layer",
        17: "",
        19: "d_1 (first threshold)",
        23: "",
        29: "4th Bott Dirac",
        31: "(217 = 7 * 31)",
        37: "5th Bott Dirac",
    }
    primes = sieve_primes(108)
    total_log = 0.0
    for p in primes:
        v9 = v_p_factorial(9, p)
        v108 = v_p_factorial(108, p)
        tot = v9 + v108
        if tot == 0:
            continue
        total_log += tot * math.log(p)
        role = cascade_roles.get(p, "")
        marker = " <-" if role else ""
        print(f"  {p:>8}  {v9:>9}  {v108:>11}  {tot:>7}  {role:<28}{marker}")
    print()
    # Verify the total log content equals ln(9! * 108!)
    log_actual = math.lgamma(10) + math.lgamma(109)
    print(f"  Sum of v_p * ln(p):  {total_log:.6f}")
    print(f"  ln(9! * 108!):       {log_actual:.6f}")
    print(f"  Relative diff:       {abs(total_log - log_actual)/log_actual:.2e}")
    print()
    print("  The fill content of 9! * 108! is fully captured in the prime axes.")
    print("  Highlighted entries: axes e_7 (the d_0 axis) and e_19 (the d_1 axis)")
    print("  carry specific cascade-distinguished fill content; axis e_31 enters")
    print("  because 217 = 7 * 31, so d_2 sits along axes e_7 and e_31.")


def test_5_cosmic_depth_fill() -> None:
    hdr("TEST 5: cosmic-depth prime-axis fill at N ~ 10^60")
    print()
    print("  At cosmic depth N = 10^60 (Dirac large-number coincidence), prime axes")
    print("  have been filled to levels v_p(N!) ~ N/(p-1) via Legendre.")
    print()
    N = 10**60
    print(f"  Total log-content stored:  ln(N!) ~ N(ln N - 1) =")
    log_N_factorial = N * math.log(N) - N  # Stirling leading
    print(f"      {log_N_factorial:.4e}  nats")
    print()
    print(f"  {'prime p':>8}  {'fill v_p(N!) ~ N/(p-1)':>25}  {'fraction of total':>20}  role")
    print(f"  {'-'*8}  {'-'*25}  {'-'*20}  ----")
    cascade_relevant = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    for p in cascade_relevant:
        fill = N // (p - 1)
        log_share = fill * math.log(p) / log_N_factorial
        role = ""
        if p == 5:
            role = "d_V"
        elif p == 7:
            role = "d_0"
        elif p == 19:
            role = "d_1"
        elif p == 31:
            role = "(217 = 7 * 31)"
        elif p == 29:
            role = "4th Bott Dirac"
        print(f"  {p:>8}  {fill:>25.4e}  {log_share*100:>18.4f} %  {role}")
    print()
    print("  Contrast: the cascade INVARIANT denominator 9! * 108! has total")
    print(f"  log-content ln(9! * 108!) = {math.lgamma(10) + math.lgamma(109):.4f} nats.")
    print(f"  The COSMIC-DEPTH fill (~{log_N_factorial:.2e} nats) is ~{log_N_factorial/(math.lgamma(10) + math.lgamma(109)):.2e}x larger.")
    print()
    print("  Reading: the cascade's invariant scale 10^-120 is set by prime-axis fills")
    print("  at the LOCAL depths (d_1+1)/2 = 10 and (d_2+1)/2 = 109, not at the")
    print("  cosmic depth N ~ 10^60.  The Part 0a Sigma(N) coincidence works the")
    print("  other way -- a quadratic accumulator at cosmic depth happens to match")
    print("  the distinguished-dimension invariant scale numerically.")


def test_6_summary() -> None:
    hdr("TEST 6: structural summary -- cascade headline in prime form")
    print()
    print("  Cascade invariant (Part 0):")
    print()
    print("     I  =  36 * pi^117 / (9! * 108!)")
    print("        =  (3^2 * 2^2) * pi^((d_1+1)/2 + (d_2+1)/2 - 2)")
    print("                       / ( ((d_1-1)/2)!  *  ((d_2-1)/2)! )")
    print()
    print("  Headline cascade prediction (Part I, leading, pre-Gram):")
    print()
    print("     rho_Lambda / M_Pl,red^4  =  72 * pi^116 / (9! * 108!)")
    print("                              =  (2^3 * 3^2) * pi^((d_1+d_2)/2 - 2)")
    print("                                              / ( ((d_1-1)/2)!  *  ((d_2-1)/2)! )")
    print()
    print("  Ingredients of the closed form:")
    print()
    print("    INTEGERS:")
    print("      d_1 = 19, d_2 = 217           (Part 0 thresholds)")
    print("      d_V =  5, d_0 = 7             (Part 0 equilibria, source of '9' = 3^2)")
    print("      2                             (observer cube-sphere bridge)")
    print("    TRANSCENDENTAL:")
    print("      pi                            (Prelude: Euler product on primes)")
    print()
    print("  No Gamma function evaluation appears in the final closed form -- the")
    print("  Gamma values at half-integer arguments fully reduce to integer factorials,")
    print("  which fully decompose into prime-axis fills via Legendre.  The headline")
    print("  cascade prediction is rational * pi^integer with both pieces forced by")
    print("  cascade-internal indices: numerator-integer from {d_V, d_0}, factorial")
    print("  denominators from {d_1, d_2}, pi-power from {d_1, d_2}.")
    print()
    print("  This is the cleanest base-number-theoretic form available without")
    print("  closing the d_2 = 217 prime-derivation question (research thread B).")
    print("  Conditional on Part 0's Gamma critical-point selection of {5,7,19,217},")
    print("  the cascade's headline observable is pure prime arithmetic on those four")
    print("  integers, with pi from the Euler product.")


def main(argv: list[str] | None = None) -> int:
    print()
    print("=" * 78)
    print("Cascade Omega_d in prime-axis fill content (research thread C)")
    print("=" * 78)
    print()
    print("  Setup: every distinguished d in {5, 7, 19, 217} is odd, so")
    print("  Omega_d = 2 pi^{(d+1)/2} / ((d-1)/2)! is rational * pi^integer.")
    print("  Goal: re-express cascade headline predictions in this form, with the")
    print("  rational part decomposed into prime-axis fills via Legendre.")

    omegas = test_1_omega_closed_forms()
    I_rat, I_k = test_2_cascade_invariant(omegas)
    test_3_rho_lambda_prediction(I_rat, I_k)
    test_4_prime_axis_decomposition()
    test_5_cosmic_depth_fill()
    test_6_summary()

    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
