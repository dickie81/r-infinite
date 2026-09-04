#!/usr/bin/env python3
"""
The matter ledge at one-sixth of the hierarchy: a two-capacity derivation.

Empirical input (see Addendum 6 tooling): expressed as exponents of the
cascade's 120.146-decade hierarchy, every charged-fermion and hadronic mass
sits in a thin band q in [0.140, 0.186] ("all matter at one-sixth"), with
the neutrino and vacuum scale together near q = 1/4.  Saying q = 1/6 is
algebraically identical to Zel'dovich's 1967 relation rho_L = m^6 / M_Pl^2
(and to Weinberg's temporal form H ~ m_pi^3 / M_Pl^2).

Derivation (one postulate, cascade-admissible ingredients only):
  1. The Omega-floor rho_L = 7.15e-121 M^4 (Part I) fixes a STATIC de
     Sitter radius R = sqrt(3/rho_L)  [GR identity; w = -1 preserved,
     nothing downstream drifts].
  2. The horizon carries S = A/4 = pi R^2 bits (derived natively in
     Part II=III -- no semiclassical machinery).
  3. Two sectors, two saturation laws (THE POSTULATE -- the adelic
     selection rule of Addendum 6 elevated from reading to premise):
       - archimedean sector (vacuum/energy/geometry): bounded by the
         ENERGY capacity E <= R (Cohen-Kaplan-Nelson no-collapse) ->
         saturation scale Lambda_E = R^(-1/2): the quarter, rho^(1/4).
       - arithmetic sector (matter = information-bearing content):
         bounded by the INFORMATION capacity -- distinguishable modes
         cannot exceed the horizon's bits: m^3 * (4pi/3) R^3 = pi R^2.
  4. Solve: m = (S/V)^(1/3) -> q = 1/6 exactly up to O(1) factors
     (one-sixth = the area-to-volume scaling ratio 2/3 times the
     vacuum's quarter), and eliminating R gives rho_L ~ m^6/M^2:
     Zel'dovich derived, causal arrow vacuum -> matter.

Pricing (audit conventions): the assembly is known physics (CKN bounds,
holographic counting) plus ONE new selection rule; the observed band
occupies 4.6% of the available exponent range and the derivation lands at
its centre with no mass input -> ~4.4 bits.  Predicts ledge location
(~17 MeV, light-quark territory) and staticness (tied to R_dS); does NOT
predict band width, individual masses, or the electroweak adjacency.
Falsifier: confirmed dark-energy evolution (DESI w(z)) breaks the
staticness this construction requires.
"""

import math

MRED = 2.435e18                      # reduced Planck mass, GeV
RHO = 7.15e-121                      # cascade Omega-floor: rho_L / M_red^4
H_DEC = 120.146                      # hierarchy decades


def main():
    print("=" * 74)
    print("Two-capacity derivation of the matter ledge")
    print("=" * 74)

    R = math.sqrt(3.0 / RHO)
    print(f"1. de Sitter radius   R = sqrt(3/rho)      = {R:.3e} l_Pl,red")

    S = math.pi * R * R
    print(f"2. horizon capacity   S = pi R^2           = {S:.3e} nats")

    lamE = R ** -0.5
    print(f"3a. energy saturation  Lambda_E = R^(-1/2) = "
          f"{lamE * MRED * 1e12:.1f} meV   (rho^(1/4) = "
          f"{RHO ** 0.25 * MRED * 1e12:.1f} meV)")

    V = (4.0 / 3.0) * math.pi * R ** 3
    m = (S / V) ** (1.0 / 3.0)
    q = -math.log10(m) / H_DEC
    print(f"3b. entropy saturation m = (S/V)^(1/3)     = "
          f"{m * MRED * 1e3:.1f} MeV   q = {q:.4f}   (1/6 = {1/6:.4f})")

    print(f"4. identity check: rho = {RHO:.2e}  vs  m^6 (O(1) loose) = "
          f"{m ** 6:.2e}")

    print()
    print("observed fermion band: q in [0.140 (top), 0.186 (electron)],")
    print("centre 0.163; derived scale lands inside with no mass input.")
    print(f"band = 4.6% of available exponent -> "
          f"{-math.log2(0.046):.1f} bits against a free-ledge null")


if __name__ == "__main__":
    main()
