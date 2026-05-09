#!/usr/bin/env python3
"""Cascade topological extension: m_η'² = Λ²·(ρ(12)−1)·(ρ(8)−1) double-Adams.

Goal. Extend thm:strong-cp (Part IVb §6, π_3(S^11) = 0 → θ_QCD = 0)
to derive the U(1)_A axial-anomaly mass m_η'² = Λ²·N_c·d_0 from
cascade topology. The empirical sub-percent match (rem:cascade-beta0,
this PR) on m_η' = Λ·√(N_c·d_0) needs a structural derivation.

Discovery. The cascade-primitive form

    m_η'² = Λ²·N_c·d_0 = Λ²·3·7 = 21·Λ²

has a double-Adams reading:

    N_c   = ρ(12) − 1 = 3   (Adams: vector fields on S^11; gives SU(3))
    d_0   = ρ(8)  − 1 = 7   (Adams: vector fields on S^7; octonion
                              parallelizability — S^7 is the LAST
                              parallelizable sphere by Adams)

so

    m_η'² = Λ²·(ρ(12) − 1)·(ρ(8) − 1)        (DOUBLE ADAMS)

Both factors are Adams' theorem outputs. The first is the gauge
sector at d_g = 12 (already used in thm:strong-cp Step 1). The
second is the octonion-sphere parallelizability at d = 8 (S^7),
which numerically coincides with the cascade's Γ-area-maximum
distinguished dimension d_0 = 7 (Part 0).

Topological structure. G_2 ⊂ Aut(O) acts on S^7 (octonions). The
quotient G_2/SU(3) = S^6 sits at the cascade's d_0 = 7 layer (where
SU(3)'s algebra is sourced). So the cascade-topological link between
d=8 (S^7, octonion) and d_0=7 (S^6, G_2/SU(3) quotient) is the
Hopf-fibration / quotient structure G_2 → G_2/SU(3) = S^6.

Topological reading of the U(1)_A anomaly mass:
  - N_c factor: color-trace contribution from gauge bundle at d_g=12
                (same Adams count that gives SU(3) in thm:strong-cp)
  - d_0 factor: octonion-quotient Adams count from G_2/SU(3) = S^6
                source layer at d_0=7
  - Product:    cascade-internal topological invariant at the
                (d_g=12, d_0=7) layer pair, sourcing the η' mass

This tool documents the double-Adams structure and tests its
consistency with Witten-Veneziano (cascade-internal χ_top derivation).
"""

from __future__ import annotations

import math


def adams_rho(n: int) -> int:
    """Adams' rho function. ρ(n) - 1 = max number of linearly independent
    nowhere-zero vector fields on S^(n-1).

    Formula: write n = 2^e · m with m odd; let a = e // 4, b = e % 4;
    then ρ(n) = 8a + 2^b.
    """
    if n == 0:
        return 0
    e = 0
    m = n
    while m % 2 == 0:
        m //= 2
        e += 1
    a, b = e // 4, e % 4
    return 8*a + 2**b


N_C = 3              # = ρ(12) - 1, Adams gauge count at d_g=12
D_0 = 7              # = ρ(8) - 1, Adams octonion count at d=8 (also Γ area max)
LAMBDA_PDG = 0.210   # GeV
M_ETA_PRIME = 0.95778
M_ETA = 0.54786


def main() -> None:
    print("=" * 96)
    print("CASCADE TOPOLOGICAL EXTENSION: m_η'² = Λ²·(ρ(12)−1)·(ρ(8)−1)")
    print("=" * 96)
    print()

    print("Adams' ρ at relevant cascade layers:")
    print(f"  ρ(12) = {adams_rho(12)}, vector fields on S^11 = {adams_rho(12)-1} = N_c (gauge)")
    print(f"  ρ(8)  = {adams_rho(8)},  vector fields on S^7  = {adams_rho(8)-1} = d_0 (octonion)")
    print(f"  ρ(8)  = 8 is the Adams MAXIMUM among small spheres; S^7 is the LAST")
    print(f"  parallelizable sphere (Adams' theorem on Hopf invariant).")
    print()

    print(f"Cascade primitive product: N_c · d_0 = {N_C * D_0}")
    print(f"Adams product:             (ρ(12)−1)·(ρ(8)−1) = {(adams_rho(12)-1)*(adams_rho(8)-1)}")
    assert N_C * D_0 == (adams_rho(12)-1) * (adams_rho(8)-1)
    print("Match. The cascade's m_η'² coefficient is DOUBLE-ADAMS.")
    print()

    print("=" * 96)
    print("Topological identification")
    print("=" * 96)
    print()
    print("Layer d_g = 12 (gauge sector):")
    print("  S^11 admits ρ(12)−1 = 3 nowhere-zero vector fields (Adams).")
    print("  These are the quaternionic units {i, j, k} acting as right-")
    print("  multiplications on the Hopf fibration S^3 → S^7 → S^4.")
    print("  Cascade reading: SU(3) generators (Paper IVa Theorem 2.3).")
    print("  Topological consequence: π_3(S^11) = 0 (since 3 < 11) →")
    print("  θ_QCD = 0 (Theorem strong-cp, Part IVb §6).")
    print()
    print("Layer d = 8 (octonion sphere S^7):")
    print("  S^7 admits ρ(8)−1 = 7 nowhere-zero vector fields (Adams MAX).")
    print("  These are octonion right-multiplications. S^7 is parallelizable.")
    print("  G_2 = Aut(O) acts on S^7; the quotient G_2/SU(3) = S^6 sits")
    print("  at d_0 = 7, where the cascade's SU(3) algebra is sourced.")
    print("  Numerical coincidence: d_0 (Γ area max, Part 0) = ρ(8) − 1.")
    print()
    print("Joint structure (d_g=12, d_0=7):")
    print("  The U(1)_A anomaly couples gauge bundle (S^11 at d_g=12)")
    print("  to algebra source (S^6 at d_0=7). The S^6 = G_2/SU(3) quotient")
    print("  carries the octonion structure of S^7 (at d=8) modulo SU(3).")
    print("  Cascade-topological invariant for the layer pair: product of")
    print("  Adams counts (gauge × octonion) = (ρ(12)−1)·(ρ(8)−1) = 21.")
    print()

    print("=" * 96)
    print("Proposition: m_η'² = Λ²·(ρ(12)−1)·(ρ(8)−1)")
    print("=" * 96)
    print()
    factor = (adams_rho(12) - 1) * (adams_rho(8) - 1)
    m_eta_prime_pred = LAMBDA_PDG * math.sqrt(factor)
    dev = (m_eta_prime_pred - M_ETA_PRIME) / M_ETA_PRIME
    print(f"  Cascade form:  m_η'² = Λ²·{factor} = Λ²·N_c·d_0")
    print(f"  Predicted m_η': {m_eta_prime_pred*1000:.2f} MeV")
    print(f"  PDG m_η':       {M_ETA_PRIME*1000:.2f} MeV")
    print(f"  Deviation:      {dev*100:+.2f}%")
    print()

    print("=" * 96)
    print("Structural argument (Tier 4b, parallel to thm:strong-cp Tier 4b)")
    print("=" * 96)
    print()
    print("Step 1 (gauge-sector Adams count → N_c).")
    print("  Same as thm:strong-cp Step 1. By Adams' theorem on S^11,")
    print("  ρ(12) − 1 = 3 linearly independent nowhere-zero vector fields,")
    print("  giving SU(3) gauge structure. The U(1)_A anomalous divergence")
    print("  ∂_μ J^μ_5 ∝ N_c·tr(F∧F) inherits the color-trace factor N_c.")
    print()
    print("Step 2 (octonion-quotient Adams count → d_0).")
    print("  S^7 (at d=8) is parallelizable with ρ(8) − 1 = 7 vector fields,")
    print("  the Adams maximum among small spheres. The octonion structure")
    print("  on S^7 has G_2 = Aut(O) automorphism group, and G_2/SU(3) = S^6")
    print("  is the cascade's d_0 = 7 layer where SU(3)'s algebra is sourced.")
    print("  The d_0 factor in m_η'² thus reflects the octonion-quotient")
    print("  Adams count carried by the algebra source layer.")
    print()
    print("Step 3 (cascade descent → Λ²).")
    print("  The QCD scale Λ_QCD = M_Z·exp(-2π) (cascade-native, this Remark)")
    print("  with cascade↔MS-bar conversion √(N_c/N(0)). The η' mass scale")
    print("  is the descent scale Λ², modulated by the topological factors.")
    print()
    print("Combined: m_η'² = Λ²·(gauge Adams)·(octonion-quotient Adams)")
    print("                = Λ²·(ρ(12)−1)·(ρ(8)−1)")
    print("                = Λ²·N_c·d_0 = 21·Λ²")
    print()
    print("Witten-Veneziano consistency (cascade inputs):")
    n_f = 3
    f_pi_sq = LAMBDA_PDG**2 * (2/3)**4  # = (4/9)²
    m_eta_8_sq = LAMBDA_PDG**2 * (4*50/9 - 4/9)/3  # = 196/27
    chi_top = (m_eta_prime_pred**2 - m_eta_8_sq) * f_pi_sq / (2 * n_f)
    chi_top_quartic = chi_top**0.25
    print(f"  m_η_0² (singlet Adams) = {factor}·Λ² = {LAMBDA_PDG**2*factor:.6f} GeV²")
    print(f"  m_η_8² (cascade GMO)   = 196/27·Λ² = {m_eta_8_sq:.6f} GeV²")
    print(f"  m_anomaly²           = (m_η_0² - m_η_8²) = {(LAMBDA_PDG**2*factor - m_eta_8_sq):.6f} GeV²")
    print(f"  → χ_top = m_anomaly²·f_π²/(2N_f) = {chi_top:.4e} GeV⁴")
    print(f"  → χ_top^(1/4) = {chi_top_quartic*1000:.2f} MeV")
    print(f"  Lattice χ_top^(1/4) ≈ 178 MeV → deviation {(chi_top_quartic-0.178)/0.178*100:+.2f}%")
    print()

    print("=" * 96)
    print("ACKNOWLEDGED GAPS (Tier 4b)")
    print("=" * 96)
    print()
    print("1. The structural argument that the SPECIFIC topological invariant")
    print("   for U(1)_A anomaly mass at the (d_g=12, d_0=7) layer pair is")
    print("   the Adams PRODUCT (rather than e.g. Adams sum, or a different")
    print("   Adams pairing). The empirical sub-percent match is the")
    print("   evidence; cascade-internal mechanism remains to be derived.")
    print()
    print("2. The connection to Witten-Veneziano. The cascade-primitive form")
    print("   reproduces lattice χ_top to within a few percent, but the")
    print("   identification (m_anomaly² = 6χ_top/f_π²) is borrowed from QCD's")
    print("   1/N_c expansion. A cascade-internal derivation of why χ_top")
    print("   takes the cascade-primitive value (m_anomaly² · f_π²/6) at the")
    print("   d_0=7 layer is the missing rigorous step.")
    print()
    print("3. Numerical coincidence d_0 = ρ(8) − 1. The Γ-area-maximum d_0=7")
    print("   (Part 0) and the Adams maximum count ρ(8)−1=7 are independently")
    print("   derived (different theorems). Their numerical equality is")
    print("   deeply suggestive but not currently proved as structural; it")
    print("   may be an artifact of the cascade's small-integer landscape,")
    print("   or it may reflect a hidden identity between Γ critical points")
    print("   and Adams parallelizability that the program has not surfaced.")
    print()
    print("This is at the SAME tier as thm:strong-cp itself (Tier 4b: claim")
    print("supported by topological argument, with structural gaps explicitly")
    print("acknowledged). The extension preserves thm:strong-cp's Step 1")
    print("(N_c from S^11 Adams count) and adds a SECOND Adams count from")
    print("the octonion S^7 / d_0 = G_2/SU(3) quotient layer.")
    print()
    print("=" * 96)
    print("VERDICT")
    print("=" * 96)
    print()
    print("Tier 4b extension of thm:strong-cp achieved at the structural-")
    print("connection level: m_η'² = Λ²·(ρ(12)−1)·(ρ(8)−1) is a double-")
    print("Adams product, both factors being Adams' theorem outputs of the")
    print("cascade. The η' anomaly mass-squared sits on the SAME class of")
    print("topological invariants (Adams parallelizability counts) that")
    print("anchor SU(3) at d_g=12 and the parallelizable sphere S^7.")
    print()
    print("This SHARPENS the Tier 2 promotion target: the missing piece is")
    print("not 'derive m_η' from QCD' but 'show that the cascade's U(1)_A")
    print("anomaly machinery picks out the Adams PRODUCT at (d_g=12, d=8)")
    print("rather than other topological combinations.' Same Adams-theorem")
    print("apparatus already proven for SU(3) selection, applied to a new")
    print("observable.")


if __name__ == "__main__":
    main()
