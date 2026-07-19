#!/usr/bin/env python3
"""
The registered-predictions ledger, and one new pointing: the vector
nonet under enumerate-first discipline.

PART A prints the formal ledger: every number the session's machinery
forces for quantities that are unmeasured or facing imminent
remeasurement, each with its kill condition.  These are the bias-
burners: none can be adjusted after the fact.

PART B points the dictionary at the sector the papers declare beyond
their machinery (the J = 1 nonet, part4b: 'the boundary at J=1').
Discipline: the anchor candidate space is enumerated BEFORE fine
comparison; if more than one dictionary form lands, the anchor is
REFUSED and only anchor-free ratios are registered.  The candidate
ratio structure: one factor sec(pi/6) per strange leg (the inverse
Eisenstein projection -- the same atom that attached to down-type
light quarks in Addendum 19), tested across the nonet with the phi
strain reported, not hidden.
"""

import itertools
import math

from scipy.special import digamma

SQRTPI = math.sqrt(math.pi)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def part_A():
    print("=" * 74)
    print("PART A: THE REGISTERED LEDGER (kill conditions attached)")
    print("=" * 74)
    rows = [
        ("m_H", "125.194 GeV (zero corrections)", "HL-LHC m_H to ~25 MeV",
         "miss > 3 sigma kills the height lemma chain"),
        ("y_t", "exp(-alpha(14)/4) = 0.991421", "m_t + G_F refinements",
         "kills the Yukawa filter"),
        ("m_c(m_c)", "1.2714 GeV", "next FLAG/lattice average",
         "kills the t/c Observer assignment"),
        ("m_s(2GeV)", "93.48 MeV; m_s/m_ud = 27.35", "lattice",
         "kills the projection/threshold chain"),
        ("m_u/m_d", "0.4593", "lattice", "kills the threshold ladder"),
        ("m_b/m_tau", "e cos(pi/6) = 2.35405 (MS-bar)",
         "Belle II m_tau + m_b refinements", "kills the Cartan projection"),
        ("Sigma m_nu", "61-63 meV, NORMAL ordering, m_1 = 1.7-3.2 meV",
         "DESI/CMB-S4 + JUNO", "kills the capacity postulate"),
        ("m_tau", "papers' closed 1776.82 MeV; also the pi^6/945 vs",
         "Belle II (~0.02 MeV era)", "adjudicates the adelic survivor"),
        ("", "alpha(14)/2 discrimination", "", ""),
        ("w(z)", "-1 exactly, no evolution", "DESI DR3+",
         "kills the floor, the staticness, everything downstream"),
        ("theta_QCD", "0 exactly", "nEDM experiments",
         "papers' forced negative"),
        ("structure", "no anyons in free 3+1D; no 4th generation",
         "any discovery", "kills the roots-of-unity/Bott architecture"),
    ]
    for name, pred, test, kill in rows:
        if name:
            print(f"  {name:<12} {pred}")
            print(f"  {'':>12} test: {test};  kill: {kill}")
        else:
            print(f"  {'':>12} {pred}")


def part_B():
    print()
    print("=" * 74)
    print("PART B: the vector nonet -- enumerate first, then speak")
    print("=" * 74)
    LAM = 0.2086                      # papers' Lambda_PDG (GeV)
    rho_obs = 0.77526
    target = rho_obs / LAM
    atoms = {
        "chi": 2.0, "N_c": 3.0, "G(1/2)": SQRTPI, "2sqrt(pi)": 2 * SQRTPI,
        "e": math.e, "sqrt(e)": math.sqrt(math.e), "pi": math.pi,
        "cos30": math.cos(math.pi / 6), "sec30": 1 / math.cos(math.pi / 6),
        "e^(a5/2)": math.exp(alpha(5) / 2), "e^(a7/4)": math.exp(alpha(7) / 4),
        "e^(a14/2)": math.exp(alpha(14) / 2),
        "e^(a19/2)": math.exp(alpha(19) / 2),
    }
    hits = []
    for r in (1, 2, 3):
        for combo in itertools.combinations_with_replacement(atoms, r):
            v = 1.0
            for k in combo:
                v *= atoms[k]
            if abs(v / target - 1) < 0.01:
                hits.append((" * ".join(combo), v))
    print(f"  anchor m_rho/Lambda = {target:.4f}: dictionary forms within 1%:"
          f" {len(hits)}")
    for lab, v in hits[:6]:
        print(f"    {lab:<40} {v:.4f}  ({(v/target-1)*100:+.2f}%)")
    print("  => ANCHOR REFUSED (grammar-open: multiple forms land; the")
    print("     hyperfine machinery must derive it, not select it).")
    print()
    print("  anchor-free ratios (registered): one sec(pi/6) per strange leg")
    for name, ns, obs, sig in [("K*0/rho0", 1, 0.89555 / 0.77526, 0.0015),
                               ("phi/rho0", 2, 1.01946 / 0.77526, 0.0015)]:
        pred = (1 / math.cos(math.pi / 6)) ** ns
        print(f"    m_{name} (n_s={ns}): predicted {pred:.5f}"
              f"   observed {obs:.5f}  ({(pred-obs)/ (obs*sig):+.1f} sigma)")
    print("  K*0/rho lands (-0.3 sigma with honest ~0.15% pole-definition")
    print("  systematics); phi/rho STRAINS at +1.4% -- the known ideal-")
    print("  mixing region.  REGISTERED AS A PATTERN WITH A RECORDED STRAIN:")
    print("  if the hyperfine machinery, once derived, does not produce the")
    print("  phi deviation from omega-phi mixing, the sec(pi/6) ladder dies.")


if __name__ == "__main__":
    part_A()
    part_B()
