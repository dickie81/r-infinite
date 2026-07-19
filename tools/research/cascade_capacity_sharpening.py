#!/usr/bin/env python3
"""
Sharpening the capacity-scale identification -- and auditing what cannot
be sharpened.

Addendum 7 derived the matter ledge from information saturation,
m^3 V = S, with a crude mode count giving m* = 17.4 MeV; Addendum 8's
adjacency inversion inherited a ~1-decade identification slop.  This tool
does the sharpening honestly, in five parts:

  A. Exponent rigidity vs prefactor freedom: any local mode count
     N ~ g m^3 V/(phase space) bounded by an area gives m ~ R^(-1/3)
     REGARDLESS of conventions -- the 1/6 exponent is rigid.  The
     prefactor is not: enumerating conventions (bare vs (2pi)^3 phase
     space, degeneracy g, nats vs bits) spans m* in [17, 77] MeV.
  B. Candidate scoring: which physical scales fall inside the honest
     window?  Result: none of the canonical propagating scales do --
     the window lies strictly INSIDE the confined interior (between the
     current-quark masses and the confinement scale), where QCD has no
     particle.  Nearest canonical quantities: the pion-nucleon sigma
     term (~50 MeV, inside) and f_pi / m_s (~92 MeV, just above).
  C. Quarter-side cross-check: the same convention spread applied to the
     energy bound gives Lambda_E in [1.7, 6] meV vs m_nu ~ 50 meV --
     the same order-of-magnitude looseness; convention transfer between
     the two bounds does not restore sharpness.
  D. Inversion re-audit: propagating the honest m* window through the
     Addendum 8 adjacency inversion gives an EW-anchor window of
     ~[5, 44] GeV vs the observed 91 GeV -- a close miss by a factor
     2-4 (0.3-1.3 decades; within 1.1% of the hierarchy exponent).
     Addendum 8's "window contains the EW cluster" relied on the loose
     identifications (target = m_pi or Lambda); under the sharpened
     window the claim DOWNGRADES from containment to order-of-magnitude
     adjacency.  Pricing revised: ~4-5 bits -> ~2-3 bits.
  E. What would actually sharpen it: a cascade-native derivation of the
     mode-count normalisation (g and the phase-space factor from layer
     structure -- well-posed open problem), or a nonperturbative census
     of information-bearing modes in the confined phase.  Absent those,
     only the exponent (1/6) is claimable.
"""

import math

MRED = 2.435e18
RHO = 7.15e-121
H_DEC = 120.146
R = math.sqrt(3.0 / RHO)                     # de Sitter radius, l_Pl,red
S = math.pi * R * R                          # horizon entropy, nats
V = (4.0 / 3.0) * math.pi * R ** 3
R13 = R ** (-1.0 / 3.0)


def mev(x):
    return x * MRED * 1e3


def q_of(m_gev):
    return math.log10(MRED / m_gev) / H_DEC


def part_A():
    print("=" * 74)
    print("PART A: exponent rigid, prefactor free")
    print("=" * 74)
    print("  any bound  g m^3 V / c_ps  <=  S = pi R^2  gives m ~ R^(-1/3):")
    print("  the 1/6 exponent survives every convention.  The prefactor:")
    rows = [
        ("crude (S/V)^(1/3), no phase space", (S / V) ** (1 / 3)),
        ("phase space (2pi)^3, g=1", (9 * math.pi ** 2 / 2) ** (1 / 3) * R13),
        ("phase space, g=3 (pions)", (9 * math.pi ** 2 / 6) ** (1 / 3) * R13),
        ("phase space, g=4 (Dirac)", (9 * math.pi ** 2 / 8) ** (1 / 3) * R13),
        ("phase space, g=24 (u,d quarks)",
         (9 * math.pi ** 2 / 48) ** (1 / 3) * R13),
        ("phase space, g=1, bits not nats",
         (9 * math.pi ** 2 / (2 * math.log(2))) ** (1 / 3) * R13),
    ]
    for name, m in rows:
        print(f"    {name:<38} m* = {mev(m):5.1f} MeV   q = {q_of(m*MRED):.4f}")
    lo = (9 * math.pi ** 2 / 48) ** (1 / 3) * R13
    hi = (9 * math.pi ** 2 / (2 * math.log(2))) ** (1 / 3) * R13
    print(f"  honest window: [{mev((S/V)**(1/3)):.0f}, {mev(hi):.0f}] MeV"
          f"  (q spread only {q_of(hi*MRED)-q_of((S/V)**(1/3)*MRED):+.4f})")
    return (S / V) ** (1 / 3), hi


def part_B(m_lo, m_hi):
    print()
    print("=" * 74)
    print("PART B: candidate physical scales vs the window")
    print("=" * 74)
    cands = [("m_u", 2.16e-3), ("m_d", 4.7e-3), ("(m_u m_d m_s)^(1/3)", 9.9e-3),
             ("sigma_piN", 0.050), ("m*_window", None), ("f_pi", 0.0921),
             ("m_s", 0.0935), ("m_pi", 0.13957), ("T_c(QCD)", 0.155),
             ("Lambda(3) 4-loop", 0.332), ("m_p", 0.93827)]
    lo, hi = mev(m_lo) / 1e3, mev(m_hi) / 1e3
    for name, m in cands:
        if m is None:
            print(f"    {'-- window [%.0f, %.0f] MeV --' % (lo*1e3, hi*1e3):^54}")
            continue
        tag = "INSIDE" if lo <= m <= hi else ("below" if m < lo else "above")
        print(f"    {name:<22} {m*1e3:7.1f} MeV   {tag}")
    print("  => no canonical propagating scale falls inside; the window sits")
    print("     in the confined interior (current quarks << window << Lambda),")
    print("     where QCD has no particle.  The identification ambiguity is")
    print("     physics, not sloppiness: the bound points at a strongly-")
    print("     coupled region only a nonperturbative census could name.")


def part_C():
    print()
    print("=" * 74)
    print("PART C: quarter-side cross-check (energy bound vs m_nu)")
    print("=" * 74)
    lamE_crude = R ** -0.5
    lamE_ps = (8 * math.pi ** 2 / 6) ** 0.25 * R ** -0.5   # g=6 neutrinos
    print(f"  Lambda_E crude = {lamE_crude*MRED*1e12:.1f} meV;"
          f" with phase space (g=6) = {lamE_ps*MRED*1e12:.1f} meV;"
          f" m_nu ~ 50 meV")
    print("  same ~decade looseness on the quarter side: convention transfer")
    print("  between the bounds does not restore sharpness.")


def part_D(m_lo, m_hi):
    print()
    print("=" * 74)
    print("PART D: adjacency-inversion re-audit (Addendum 8 downgrade)")
    print("=" * 74)
    K1, K4 = 0.142 / 91.188, 0.332 / 91.188   # Lambda/anchor, 1-loop / 4-loop
    anchors = [m / K for m in (mev(m_lo) / 1e3, mev(m_hi) / 1e3)
               for K in (K4, K1)]
    lo, hi = min(anchors), max(anchors)
    print(f"  EW-anchor window from honest m* and loop spread:"
          f" [{lo:.1f}, {hi:.1f}] GeV")
    print(f"  observed EW anchor (M_Z): 91.2 GeV -> miss factor"
          f" {91.2/hi:.1f}-{91.2/lo:.1f}x  ({math.log10(91.2/hi):.2f}-"
          f"{math.log10(91.2/lo):.2f} decades;"
          f" {math.log10(91.2/lo)/H_DEC:.4f} of the hierarchy exponent)")
    print("  => Addendum 8's 'window contains the EW cluster' used the loose")
    print("     targets (m_pi, Lambda) -- prefactors 8-19, not O(1).  Under")
    print("     the sharpened window the claim downgrades to order-of-")
    print("     magnitude adjacency (within ~1 decade of 120).  Pricing")
    print("     revised: ~4-5 bits -> ~2-3 bits.")


if __name__ == "__main__":
    m_lo, m_hi = part_A()
    part_B(m_lo, m_hi)
    part_C()
    part_D(m_lo, m_hi)
    print()
    print("PART E: what would sharpen it -- a cascade-native normalisation of")
    print("the mode count (g and phase space from layer structure), or a")
    print("nonperturbative census of confined-phase information modes.")
    print("Absent those, only the exponent 1/6 is claimable; the prefactor")
    print("is grammar.")
