#!/usr/bin/env python3
"""
Cascade-rotation interpretation of mass: testing whether 'particles
sample cascade rotation at fraction m/M_Pl per Planck tick' gives an
independent derivation of the mass spectrum.

PROPOSAL
========
Under the user's reading:
  - Cascade rotates by pi/2 per Planck tick (Paper II forced precession +
    Paper VI 1-tick-per-d-collapse)
  - Particles ARE waves through time = cumulative cascade rotation samples
  - Mass = fraction of full cascade rotation a particle samples per tick,
    in units of Planck mass

If this gives a NEW derivation of mass, we'd find m_g / M_Pl = (some
cascade-internal fraction directly), independent of Part IVb's
Yukawa-formula route.

If it's a RE-FRAMING (same numbers, different language), m_g / M_Pl
will trace back to Part IVb's ingredients (descent factor, obstruction,
universal Yukawa baseline) plus Planck mass conversion.

This tool tests both and reports honestly which it is.

CHECK 7 COMPLIANCE: 1D cascade lattice quantities only.  The cascade
rotation pi/2 per tick is Paper II Theorem 6.1 (forced precession),
already established.
"""

from __future__ import annotations

import math
from scipy.special import gamma, digamma


# --- Cascade primitives ---

def N_d(d): return math.sqrt(math.pi) * gamma((d + 1) / 2) / gamma((d + 2) / 2)
def R_d(d): return gamma(d / 2 + 1) / gamma((d + 3) / 2)
def alpha_d(d): return R_d(d) ** 2 / 4
def p_d(d): return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_cascade(d, d_min=4):
    if d <= d_min:
        return 0.0
    return sum(p_d(dprime) for dprime in range(d_min + 1, d + 1))


# --- Constants (PDG 2024) ---

M_TAU = 1.77686       # GeV
M_MU  = 0.10566       # GeV
M_E   = 5.10999e-4    # GeV
M_T   = 172.69        # GeV
M_B   = 4.18          # GeV
M_C   = 1.27          # GeV
M_S   = 0.093         # GeV
M_U   = 2.2e-3        # GeV
M_D   = 4.7e-3        # GeV

V_HIGGS = 246.22      # GeV (electroweak VEV)
ALPHA_S = 0.1179      # strong coupling at M_Z

# Reduced Planck mass: M_Pl,red = M_Pl / sqrt(8 pi)
M_PL_RED = 2.4350e18  # GeV
M_PL = 1.2209e19      # GeV (full Planck mass)

# Cascade structural constants
PI = math.pi
TWO_SQRT_PI = 2 * math.sqrt(math.pi)
CHI = 2

# Generations
GEN_LAYERS = {1: 21, 2: 13, 3: 5}
N_D_COUNT = {1: 3, 2: 2, 3: 1}


def main():
    print("=" * 78)
    print("Cascade-rotation-fraction reading of mass: test against Part IVb")
    print("=" * 78)
    print()

    # --- Step 1: observed mass fractions in Planck units ---
    print("STEP 1: observed mass fractions m_g / M_Pl (reduced Planck mass)")
    print("-" * 78)
    masses = {"tau": M_TAU, "mu": M_MU, "e": M_E,
              "top": M_T, "bottom": M_B, "charm": M_C, "strange": M_S,
              "up": M_U, "down": M_D}
    for name, m in masses.items():
        frac = m / M_PL_RED
        log_frac = math.log10(frac)
        print(f"  {name:>8}: m = {m:>10.4f} GeV  m/M_Pl = {frac:.4e}  log10 = {log_frac:+.2f}")
    print()
    print("  Charged leptons span log10(m/M_Pl) range:")
    print(f"    tau: {math.log10(M_TAU/M_PL_RED):+.2f}")
    print(f"    mu : {math.log10(M_MU/M_PL_RED):+.2f}")
    print(f"    e  : {math.log10(M_E/M_PL_RED):+.2f}")
    print()

    # --- Step 2: Part IVb's cascade-derivation route ---
    print("STEP 2: Part IVb's cascade derivation of mass fractions")
    print("-" * 78)
    print()
    print("  Formula: m_g = (alpha_s v / sqrt(2)) * exp(-Phi(d_g)) * (2sqrt(pi))^-(n_D+1)")
    print()
    C_universal = ALPHA_S * V_HIGGS / math.sqrt(2)  # GeV
    print(f"  Universal Yukawa baseline C = alpha_s v/sqrt(2) = {C_universal:.4f} GeV")
    print(f"  C / M_Pl = {C_universal/M_PL_RED:.4e}  (log10 = {math.log10(C_universal/M_PL_RED):+.2f})")
    print()

    # Cascade descent factors
    Phi_5  = Phi_cascade(5,  d_min=4)
    Phi_13 = Phi_cascade(13, d_min=4)
    Phi_21 = Phi_cascade(21, d_min=4)
    print(f"  Phi(5)  = {Phi_5:+.4f}")
    print(f"  Phi(13) = {Phi_13:+.4f}")
    print(f"  Phi(21) = {Phi_21:+.4f}")
    print()

    # Compute predicted masses
    print(f"  Cascade leading predictions vs observed:")
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GEN_LAYERS[gen]
        n_D = N_D_COUNT[gen]
        Phi = Phi_cascade(d_g, d_min=4)
        pred = C_universal * math.exp(-Phi) * (TWO_SQRT_PI ** -(n_D + 1))
        obs = {"tau": M_TAU, "mu": M_MU, "e": M_E}[label]
        dev = (pred - obs) / obs * 100
        print(f"    {label}: cascade leading {pred:>10.4f} GeV  observed {obs:>10.4f} GeV  ({dev:+.2f}%)")
    print()

    # --- Step 3: cascade-rotation-fraction interpretation ---
    print("STEP 3: cascade-rotation-fraction interpretation")
    print("-" * 78)
    print()
    print("  Hypothesis: m_g / M_Pl = (cascade rotation fraction sampled per Planck tick)")
    print()
    print("  The cascade rotates by pi/2 per dimensional collapse (Paper II Thm 6.1).")
    print("  Under tower-growth (Paper VI), this is per Planck tick.")
    print("  A particle of mass m at rest has phase advance per tick = m/M_Pl (Planck units).")
    print()
    print("  For the cascade-rotation reading to GIVE A NEW DERIVATION of m/M_Pl,")
    print("  we'd need a closed-form cascade-internal expression for the fraction.")
    print()
    print("  Test: try direct cascade-internal candidates for m/M_Pl:")
    print()

    # Candidate 1: just the descent factor exp(-Phi(d_g))
    print(f"  Candidate (a): m/M_Pl = exp(-Phi(d_g))")
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GEN_LAYERS[gen]
        Phi = Phi_cascade(d_g, d_min=4)
        pred_frac = math.exp(-Phi)
        obs_frac = {"tau": M_TAU, "mu": M_MU, "e": M_E}[label] / M_PL_RED
        ratio = pred_frac / obs_frac
        print(f"    {label}: pred = {pred_frac:.4e}  obs = {obs_frac:.4e}  ratio pred/obs = {ratio:.2e}")
    print(f"    Result: way off -- factor ~10^17 too large.  This direct reading fails.")
    print()

    # Candidate 2: descent through full cascade exp(-(Phi(217)-Phi(d_g)))
    print(f"  Candidate (b): m/M_Pl = exp(-(Phi(217) - Phi(d_g)))")
    Phi_217 = Phi_cascade(217, d_min=4)
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GEN_LAYERS[gen]
        Phi = Phi_cascade(d_g, d_min=4)
        delta = Phi_217 - Phi
        pred_frac = math.exp(-delta)
        obs_frac = {"tau": M_TAU, "mu": M_MU, "e": M_E}[label] / M_PL_RED
        log_ratio = math.log10(pred_frac / obs_frac)
        print(f"    {label}: Phi(217)-Phi({d_g}) = {delta:.2f}  log10(pred/obs) = {log_ratio:+.1f}")
    print(f"    Result: way off -- factor ~10^100 too small.  This reading fails.")
    print()

    # The key insight: NO simple cascade-internal fraction gives the right answer.
    # The needed factor is (alpha_s v)/M_Pl, which is the universal Yukawa baseline.
    print(f"  Candidate (c): m/M_Pl = (C/M_Pl) * exp(-Phi(d_g)) * (2sqrt(pi))^-(n_D+1)")
    print(f"     where C/M_Pl = {C_universal/M_PL_RED:.4e} is the universal Yukawa baseline")
    print(f"     and the rest is Part IVb's formula.")
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GEN_LAYERS[gen]
        n_D = N_D_COUNT[gen]
        Phi = Phi_cascade(d_g, d_min=4)
        pred_frac = (C_universal / M_PL_RED) * math.exp(-Phi) * (TWO_SQRT_PI ** -(n_D + 1))
        obs_frac = {"tau": M_TAU, "mu": M_MU, "e": M_E}[label] / M_PL_RED
        ratio = pred_frac / obs_frac
        print(f"    {label}: pred = {pred_frac:.4e}  obs = {obs_frac:.4e}  pred/obs = {ratio:.4f}")
    print(f"    Result: matches observation to ~few % -- this IS Part IVb's formula.")
    print()

    # --- Step 4: where does the cascade-rotation reading add content? ---
    print("STEP 4: where (if anywhere) the cascade-rotation reading adds new content")
    print("-" * 78)
    print()

    # Decompose the universal Yukawa baseline C/M_Pl
    log_C_M_Pl = math.log(C_universal / M_PL_RED)
    log_v_M_Pl = math.log(V_HIGGS / M_PL_RED)
    log_alpha_s = math.log(ALPHA_S)
    print(f"  C/M_Pl decomposes as:")
    print(f"    log(C/M_Pl) = {log_C_M_Pl:.3f}")
    print(f"    log(alpha_s/sqrt(2)) = {log_alpha_s - 0.5*math.log(2):.3f}")
    print(f"    log(v/M_Pl) = {log_v_M_Pl:.3f}")
    print(f"  Bulk comes from v/M_Pl ~ 10^-17 (electroweak hierarchy)")
    print()
    print(f"  Part IVb derives v cascade-internally via:")
    print(f"    v = M_Pl_red * alpha_GUT * exp(Phi_{{12->4}}) * exp(-pi/alpha(5))")
    print(f"  The bulk of the smallness is exp(-pi/alpha(5)) ~ 10^-10")
    pi_alpha5 = math.pi / alpha_d(5)
    print(f"    alpha(5) = R(5)^2/4 = {alpha_d(5):.4f}")
    print(f"    pi/alpha(5) = {pi_alpha5:.2f}")
    print(f"    exp(-pi/alpha(5)) = {math.exp(-pi_alpha5):.2e}")
    print()
    print(f"  This is the cascade non-perturbative factor at d=5 (volume max).")
    print(f"  Cascade-rotation interpretation does NOT provide an independent derivation")
    print(f"  of this factor.  The electroweak hierarchy is set by cascade structure")
    print(f"  at d=5, not by cascade rotation per se.")
    print()

    # --- Step 5: cascade-rotation per tick at Planck mass ---
    print("STEP 5: per-tick rotation rate -- structural check")
    print("-" * 78)
    print()
    print(f"  Cascade per-tick rotation: pi/2 = {PI/2:.4f} radians (forced precession)")
    print(f"  QM per-tick phase at Planck mass: m_Pl c^2 t_Pl / hbar = 1 radian (in Planck units)")
    print(f"  Ratio: cascade rate / Planck-mass-QM rate = pi/2 = {PI/2:.4f}")
    print()
    print(f"  Interpretation: a particle of mass M_Pl samples cascade rotation at")
    print(f"  fraction 1/(pi/2) = 2/pi = {2/PI:.4f} per tick.  To sample at full cascade")
    print(f"  rate, particle must have mass (pi/2)*M_Pl ~ 1.91e18 GeV.")
    print()
    print(f"  This pi/2 factor IS already in Part IVb's mass formula:")
    print(f"    The (2*sqrt(pi))^-(n_D+1) factor includes the per-step rotation amplitude.")
    print(f"    Specifically: sqrt(pi) per step is the 'quarter-turn obstruction' (Paper IVb")
    print(f"    Theorem obstruction, step (b)).  This is the cascade rotation amplitude")
    print(f"    when integrated over a Gaussian normalization.")
    print()
    print(f"  So the pi/2 cascade rotation IS in Part IVb already, just expressed via")
    print(f"  sqrt(pi) per topological obstruction crossing.  Not new content.")
    print()

    # --- Step 6: Honest summary ---
    print("STEP 6: honest assessment")
    print("-" * 78)
    print()
    print("  CASCADE-ROTATION-FRACTION INTERPRETATION OF MASS:")
    print()
    print("  - Conceptually elegant: 'particles ARE waves through time' = 'particles")
    print("    sample cascade dimensional rotation at fraction m/M_Pl per tick'")
    print("  - Structurally consistent with Paper II's forced-precession-derives-QM")
    print("  - Maps cleanly onto Part IVb's existing mass derivation")
    print()
    print("  BUT it does NOT provide an independent derivation:")
    print()
    print("  1. The bulk of m/M_Pl comes from C/M_Pl ~ 10^-17, which depends on:")
    print("     - The electroweak VEV v/M_Pl ~ 10^-17 (from Part IVb Thm vev,")
    print("       which uses exp(-pi/alpha(5)) at d=5 as the non-perturbative factor)")
    print("     - The strong coupling alpha_s/sqrt(2)")
    print("     - These are cascade-derived but go via CASCADE STRUCTURE, not cascade")
    print("       rotation per se.")
    print()
    print("  2. The per-generation hierarchy comes from exp(-Phi(d_g)) and (2sqrt(pi))^-(n_D+1)")
    print("     - These are cascade descent quantities (Paper II + IVb)")
    print("     - The sqrt(pi) is the cascade rotation amplitude (quarter-turn obstruction)")
    print("     - So this ingredient IS the cascade rotation, in Part IVb's language.")
    print()
    print("  3. The pi/2 cascade rotation per tick is structurally consistent with the")
    print("     factor sqrt(pi) per topological-obstruction crossing in Part IVb.")
    print()
    print("  CONCLUSION: the cascade-rotation interpretation is a RE-FRAMING of")
    print("  Part IVb's mass derivation, not a new derivation.  The structural ingredients")
    print("  (descent, obstruction, electroweak VEV) are the same; the language is just")
    print("  'mass = fraction of cascade rotation per tick' instead of 'mass = Yukawa")
    print("  coupling times VEV times descent factors'.")
    print()
    print("  This is structurally elegant and validates Paper II's already-established")
    print("  forced-precession-derives-QM result.  But it doesn't supply new predictive")
    print("  content; Part IVb's existing derivation IS the cascade-rotation derivation.")
    print()
    print("  The genuine new content (if any) under this reading is conceptual:")
    print("  - QM's 'wave nature' is not a separate postulate; it IS dimensional rotation.")
    print("  - The 'i' in i hbar partial_t = H psi IS the cascade's pi/2 precession.")
    print("  - 'Particles as waves through time' is a literal statement about cascade")
    print("    rotation samples, with mass setting the sampling fraction.")
    print()
    print("  These conceptual refinements are valuable but don't shift any cascade")
    print("  numerical prediction.  They might shape how to think about Planck-scale")
    print("  particle physics or quantum-gravity dispersion (Reading 2 from earlier).")


if __name__ == "__main__":
    main()
