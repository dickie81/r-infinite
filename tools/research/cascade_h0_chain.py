#!/usr/bin/env python3
"""THE H0 CHAIN, GATED (the part5:532 editorial residue): the
Hubble-constant proof's displayed steps made consistent and the
final digit's precision honestly stated.  Registered as F73-3
(rounds 73-74, cosmetic: 4-figure displayed intermediates whose
literal product was 1.4242 against the shown exact-input 1.4244;
the final 66.78 unaffected).  This file commits the gates the
corrected display cites.

Category note: unlike the 1i-1s arc this file is not category (a)
pure arithmetic -- it uses the CODATA physical constants (G, hbar,
the parsec) exactly as Part V's H0 theorem does.  No fitted
parameter enters; the cascade input is the exact invariant.

THE CHAIN (Part V, thm:H0):  H0 = M_Pl,red sqrt(2I/(3(pi-1))),
converted to km/s/Mpc via hbar and the megaparsec.

  C1 EXACT-INPUT CHAIN.  I = 1.09894538952e-120 (part0's exact
     value), M_Pl,red = CODATA (M_Pl = sqrt(hbar c/G) = 1.22089e19
     GeV; /sqrt(8 pi) = 2.435323e18): H0 = 66.77523 -> the
     recorded 66.78 is the correct 2-d.p. round of the
     exact-input chain.
  C2 THE DISPLAYED 5-S.F. STEPS COMPOUND CONSISTENTLY.
     a = 3.4210e-121, b = sqrt -> 5.8489e-61, M x b -> 1.4244e-42
     GeV, -> 66.78: each literal step from the displayed figures
     reproduces the next displayed figure (the F73-3 defect --
     2.435 x 5.849 = 1.4242 vs shown 1.4244 -- is gone).
  C3 THE LAST DIGIT'S PRECISION, STATED.  G's u_r = 2.2e-5 maps
     to +-0.00073 on H0 (H0 ~ G^(-1/2)); the band
     [66.7745, 66.7760] straddles the 2-d.p. rounding boundary
     66.775.  And the repository's stored 4-figure anchor
     M_PL_RED_GEV = 2.435e18 gives 66.766 -> 66.77.  So the
     display's second decimal is anchor-sensitive: honest
     statement is 66.78 +- 0.01 (the width = the anchor-
     sensitivity spread at display precision -- the 4-figure
     chain sits 0.009 below the exact chain; G's band alone is
     +-0.0007 -- round-86 F3 stated the provenance), against
     Planck's 67.4 +- 0.5 -- the -0.9% leading deviation is
     untouched at this precision.
  C4 NO DOWNSTREAM DRIFT.  (2/pi) I = 6.996e-121 (the remark's
     value) and the -0.9% deviation vs Planck 67.4 are re-gated
     from the same inputs.

No number changes on any recorded surface (H0 = 66.78 stands as
the exact-input round); the part5 proof's display is corrected to
compound consistently with the anatomy and the precision note
stated.  No closure.
"""

import mpmath as mp

mp.mp.dps = 30

HBAR_GEV_S = mp.mpf("6.582119569e-25")
MPC_KM = mp.mpf("3.0856775814913673e19")
G_SI = mp.mpf("6.67430e-11")
G_UR = mp.mpf("2.2e-5")
HBAR_SI = mp.mpf("1.054571817e-34")
C_SI = mp.mpf("299792458")
J_PER_GEV = mp.mpf("1.602176634e-10")
I_EXACT = mp.mpf("1.09894538952e-120")


def h0_of(M_red_gev, I):
    return M_red_gev * mp.sqrt(2 * I / (3 * (mp.pi - 1))) \
        / HBAR_GEV_S * MPC_KM


def main():
    print("=" * 74)
    print("THE H0 CHAIN, GATED (part5:532 residue)")
    print("=" * 74)

    MPl = mp.sqrt(HBAR_SI * C_SI / G_SI) * C_SI ** 2 / J_PER_GEV
    Mred = MPl / mp.sqrt(8 * mp.pi)

    # ---- C1: the exact-input chain
    print()
    print("C1 exact-input chain:")
    ok1 = abs(MPl - mp.mpf("1.22089e19")) < 5e13
    ok1 &= abs(Mred - mp.mpf("2.435323e18")) < 5e11
    # round-87 F1: the twelve-digit input constant is now gated against
    # the invariant's DEFINITION (I = (Om5/Om7)^2 Om19 Om217 =
    # (9/pi^2) Om19 Om217, Om(d) = 2/Gamma_R(d+1)) at half-ULP of the
    # 12th digit -- before this conjunct the finest transitive gate
    # resolved ~7 digits (an 8th-digit corruption passed the battery):

    def om(d):
        return 2 * mp.pi ** ((d + 1) / mp.mpf(2)) \
            / mp.gamma((d + 1) / mp.mpf(2))

    I_def = (om(5) / om(7)) ** 2 * om(19) * om(217)
    ok1 &= abs(I_def - I_EXACT) < mp.mpf("5e-132")
    H0 = h0_of(Mred, I_EXACT)
    ok1 &= abs(H0 - mp.mpf("66.77523")) < 5e-6   # half-ULP (round-86 F1)
    # (a redundant 2-d.p. round-check conjunct removed round 86, F5:
    # implied by the half-ULP window, which lies entirely above 66.775)
    print(f"   M_Pl = {mp.nstr(MPl, 6)} GeV, M_Pl,red = {mp.nstr(Mred, 7)};")
    print(f"   H0 = {mp.nstr(H0, 7)} km/s/Mpc -> 66.78 at 2 d.p. (the")
    print("   recorded value is the exact-input round)   "
          + ("PASS" if ok1 else "FAIL"))

    # ---- C2: the displayed steps compound literally
    print()
    print("C2 the corrected display's literal compounding (5 s.f.):")
    a = 2 * I_EXACT / (3 * (mp.pi - 1))
    ok2 = mp.nstr(a, 5) == "3.421e-121"        # displays as 3.4210e-121
    # all literal-step tolerances at HALF-ULP of the last displayed
    # digit (round-86 F1: the first draft used 5-ULP windows -- the
    # product gate passed the defect value 1.4242 itself):
    b_lit = mp.sqrt(mp.mpf("3.4210e-121"))
    ok2 &= abs(b_lit - mp.mpf("5.8489e-61")) < 5e-66   # sqrt step literal
    prod_lit = mp.mpf("2.4353e18") * mp.mpf("5.8489e-61")
    ok2 &= abs(prod_lit - mp.mpf("1.4244e-42")) < 5e-47  # product literal
    ok2 &= not abs(mp.mpf("1.4242e-42")
                   - mp.mpf("1.4244e-42")) < 5e-47  # the defect now FAILS
    H0_lit = mp.mpf("1.4244e-42") / HBAR_GEV_S * MPC_KM
    ok2 &= abs(H0_lit - mp.mpf("66.78")) < 5e-3          # final literal
    old_prod = mp.mpf("2.435e18") * mp.mpf("5.849e-61")
    ok2 &= abs(old_prod - mp.mpf("1.4242e-42")) < 5e-47  # the F73-3 defect
    print("   3.4210e-121 -> sqrt = 5.8489e-61 -> x 2.4353e18 = 1.4244e-42")
    print(f"   -> {mp.nstr(H0_lit, 6)} -> 66.78: every literal step lands on")
    print("   the next displayed figure (the old 4-figure display's literal")
    print("   product 2.435 x 5.849 = 1.4242 vs shown 1.4244 -- gated as")
    print("   the removed defect)   " + ("PASS" if ok2 else "FAIL"))

    # ---- C3: the last digit's precision
    print()
    print("C3 the second decimal's honest precision:")
    dH = H0 * G_UR / 2                      # H0 ~ G^(-1/2)
    lo, hi = H0 - dH, H0 + dH
    ok3 = abs(dH - mp.mpf("0.00073")) < 5e-6   # half-ULP (round-86 F1)
    ok3 &= lo < mp.mpf("66.775") < hi       # the band straddles the boundary
    H0_anchor = h0_of(mp.mpf("2.435e18"), I_EXACT)
    ok3 &= abs(H0_anchor - mp.mpf("66.766")) < 5e-4   # half-ULP
    print(f"   G's u_r = 2.2e-5 -> +-{mp.nstr(dH, 2)} on H0; the band")
    print(f"   [{mp.nstr(lo, 7)}, {mp.nstr(hi, 7)}] straddles 66.775 (gated);")
    print(f"   the stored 4-figure anchor 2.435e18 gives {mp.nstr(H0_anchor, 5)}")
    print("   -> 66.77: the second decimal is anchor-sensitive -- honest")
    print("   statement 66.78 +- 0.01 (width = the anchor spread at display")
    print("   precision, 0.009; G's band alone +-0.0007) vs Planck")
    print("   67.4 +- 0.5   " + ("PASS" if ok3 else "FAIL"))

    # ---- C4: no downstream drift
    print()
    print("C4 downstream values unchanged:")
    two_over_pi_I = 2 / mp.pi * I_EXACT
    ok4 = abs(two_over_pi_I - mp.mpf("6.996e-121")) < 5e-125  # half-ULP
    dev = (H0 - mp.mpf("67.4")) / mp.mpf("67.4")
    ok4 &= abs(dev + mp.mpf("0.0093")) < 5e-5   # half-ULP (round-86 F1)
    print(f"   (2/pi) I = {mp.nstr(two_over_pi_I, 4)} (the remark's 6.996e-121,")
    print(f"   gated); deviation vs Planck 67.4 = {mp.nstr(dev * 100, 3)}% (the")
    print("   recorded -0.9% leading deviation, untouched)   "
          + ("PASS" if ok4 else "FAIL"))

    print()
    print("=" * 74)
    print("READING")
    print("=" * 74)
    print("  The recorded H0 = 66.78 is the correct 2-d.p. round of the")
    print("  exact-input chain (66.77523).  The corrected part5 display")
    print("  compounds literally at 5 s.f.; the second decimal sits within")
    print("  G's experimental reach and flips under the repository's own")
    print("  4-figure anchor -- stated, not hidden.  No number changes on")
    print("  any recorded surface; no closure.")


if __name__ == "__main__":
    main()
