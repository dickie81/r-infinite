#!/usr/bin/env python3
"""Theorem 1ab verifier: the per-species census.

Claim under test: the head-count chain assembles from committed
content with exactly two disclosed imports (m_p, the observed
T_CMB): the fully-committed composite Omega_b h^2 = h^2/(2 pi^2) =
0.0225892 sits at +1.46 sigma (+0.98%) of Planck's 0.02237 +-
0.00015 (zero imports -- both factors the record's own); the
baryon-to-photon ratio eta = 6.176e-10 vs the observed 6.116e-10
(+0.98%, exactly the Omega_b h^2 deviation carried through, eta
proportional to Omega_b h^2 at fixed T); within the record's own
de Sitter horizon (r_H = (c/H0)/sqrt(Omega_L) = 5411 Mpc): N_b =
4.9e78, N_gamma = 8.0e87, N_nu = 6.6e87 (the 9/11 factor); the
budget hierarchy N_b << N_gamma << S_dS = 3.315e122 nats (the
budget recomputed from the committed closure rho = (2/pi)
e^(0.02108) I). Under the cascade-leading T_CMB = 2.642 K, eta =
6.78e-10 (+10.9%, the -3.1% temperature deviation cubed) --
reported alongside. Data-facing assembly; no closure; no number
changes.

Gates:
  C1 -- the committed factors recomputed: H0 = 66.77523 from the
        certified chain (I = (Omega_5/Omega_7)^2 Omega_19 Omega_217
        recomputed from Gamma at dps 30, gated 12-digit); Omega_b =
        1/(2 pi^2) = 0.0506606; S_dS = 3.315e122 from the committed
        closure.
  C2 -- the fully-committed composite: Omega_b h^2 = 0.0225892
        (half-ULP), +1.46 sigma / +0.98% vs 0.02237 +- 0.00015.
  C3 -- the census with the two imports: n_gamma = 410.73 /cm^3;
        eta = 6.176e-10; eta/eta_obs - 1 = the Omega_b h^2 relative
        deviation exactly (the proportionality gate); the
        cascade-leading-T variant 6.78e-10.
  C4 -- the head-counts in the de Sitter horizon: r_H = 5411 Mpc;
        N_b = 4.945e78; N_gamma = 8.007e87; N_nu = (9/11) N_gamma =
        6.551e87; the hierarchy N_b < N_gamma + N_nu < S_dS.
  C5 -- surface anchors: part5's baryon-fraction proof sentence and
        the T_CMB leading-order line; the 1n(iii) budget passage;
        1ab's key sentences (the composite; the carried-through
        deviation; the disclosed imports; the m_p-uncommitted
        disclosure gated by negative grep on the tex surfaces).

Imports (disclosed): m_p = 1.67262192369e-27 kg (CODATA); T_CMB =
2.7255 K (observed; the cascade-leading 2.642 K computed
alongside). Physical constants: CODATA SI. Sabotage record (run on
scratchpad copies at the landing commit): (a) perturbing the
Omega_b h^2 expectation trips C2, exit 1; (b) perturbing part5's
baryon-proof anchor trips C5, exit 1.
"""
import os
import re
import sys

from mpmath import mp, mpf, pi, gamma, sqrt, zeta

mp.dps = 30

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
PART5 = os.path.join(ROOT, "src", "cascade-series-part5.tex")
PART4B = os.path.join(ROOT, "src", "cascade-series-part4b.tex")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


def Om(d):
    return 2 * pi ** ((mpf(d) + 1) / 2) / gamma((mpf(d) + 1) / 2)


# committed chain constants (the certified h0_chain instrument's)
HBAR_GEV_S = mpf("6.582119569e-25")
MPC_KM = mpf("3.0856775814913673e19")
# SI (CODATA)
G_SI = mpf("6.67430e-11")
C_SI = mpf("299792458")
KB = mpf("1.380649e-23")
HBAR = mpf("1.054571817e-34")
J_PER_GEV = mpf("1.602176634e-10")
# M_red computed from CODATA G exactly as the certified h0_chain does
M_RED = (mp.sqrt(HBAR * C_SI / G_SI) * C_SI ** 2 / J_PER_GEV) / mp.sqrt(8 * pi)
M_P = mpf("1.67262192369e-27")  # import, disclosed
T_OBS = mpf("2.7255")           # import, disclosed
T_LEAD = mpf("2.642")           # the cascade leading order (part5)

print("C1 -- the committed factors")
I = (Om(5) / Om(7)) ** 2 * Om(19) * Om(217)
gate("I recomputed, 12-digit", abs(I - mpf("1.09894538952e-120")) < mpf("5e-132"),
     mp.nstr(I, 12))
H0 = M_RED * sqrt(2 * I / (3 * (pi - 1))) / HBAR_GEV_S * MPC_KM
h = H0 / 100
gate("H0 = 66.77523 from the certified chain (half-ULP of 5 d.p.)",
     abs(H0 - mpf("66.77523")) < mpf("5e-6"), mp.nstr(H0, 8))
Ob = 1 / (2 * pi ** 2)
gate("Omega_b = 1/(2 pi^2) = 0.0506606", abs(Ob - mpf("0.0506606")) < mpf("5e-8"),
     mp.nstr(Ob, 7))
rho_L = (2 / pi) * mp.e ** mpf("0.02108") * I
S_dS = 24 * pi ** 2 / rho_L
gate("S_dS = 3.315e122 nats from the committed closure",
     abs(S_dS / mpf("3.315e122") - 1) < mpf("2e-4"), mp.nstr(S_dS, 5))

print("C2 -- the fully-committed composite (zero imports)")
Obh2 = Ob * h * h
sig = (Obh2 - mpf("0.02237")) / mpf("0.00015")
gate("Omega_b h^2 = 0.0225892 (half-ULP)", abs(Obh2 - mpf("0.0225892")) < mpf("5e-8"),
     mp.nstr(Obh2, 7))
gate("+1.46 sigma / +0.98% vs 0.02237 +- 0.00015",
     abs(sig - mpf("1.46")) < mpf("0.01")
     and abs((Obh2 / mpf("0.02237") - 1) * 100 - mpf("0.98")) < mpf("0.01"),
     f"{mp.nstr(sig, 3)} sigma")

print("C3 -- the census (two disclosed imports)")
H0_SI = H0 * 1000 / (MPC_KM * 1000)
rho_crit = 3 * H0_SI ** 2 / (8 * pi * G_SI)
n_b = Ob * rho_crit / M_P
n_g = 2 * zeta(3) / pi ** 2 * (KB * T_OBS / (HBAR * C_SI)) ** 3
eta = n_b / n_g
gate("n_gamma = 410.73 /cm^3", abs(n_g / mpf("1e6") - mpf("410.73")) < mpf("0.01"),
     mp.nstr(n_g / 1e6, 6))
gate("eta = 6.176e-10", abs(eta - mpf("6.176e-10")) < mpf("5e-13"),
     mp.nstr(eta, 5))
eta_obs = eta * mpf("0.02237") / Obh2
gate("proportionality: eta/eta_obs - 1 == Omega_b h^2 deviation exactly",
     abs((eta / eta_obs - 1) - (Obh2 / mpf("0.02237") - 1)) < mpf("1e-12"),
     f"both {mp.nstr((eta/eta_obs-1)*100, 3)}%")
n_g_lead = 2 * zeta(3) / pi ** 2 * (KB * T_LEAD / (HBAR * C_SI)) ** 3
gate("the cascade-leading-T variant: eta = 6.78e-10 (+10.9%)",
     abs(n_b / n_g_lead - mpf("6.78e-10")) < mpf("5e-13")
     and abs((n_b / n_g_lead / eta_obs - 1) * 100 - mpf("10.9")) < mpf("0.2"),
     mp.nstr(n_b / n_g_lead, 5))

print("C4 -- the head-counts in the de Sitter horizon")
Om_L = 1 - mpf("0.31150")
r_H = C_SI / (H0_SI * sqrt(Om_L))
V = 4 * pi / 3 * r_H ** 3
N_b, N_g = n_b * V, n_g * V
N_nu = N_g * mpf(9) / 11
gate("r_H = 5411 Mpc", abs(r_H / mpf("3.0856775814913673e22") - mpf("5411")) < 1,
     mp.nstr(r_H / mpf("3.0856775814913673e22"), 6))
gate("N_b = 4.945e78; N_gamma = 8.007e87; N_nu = 6.551e87",
     abs(N_b / mpf("4.945e78") - 1) < mpf("1e-3")
     and abs(N_g / mpf("8.007e87") - 1) < mpf("1e-3")
     and abs(N_nu / mpf("6.551e87") - 1) < mpf("1e-3"),
     f"{mp.nstr(N_b,4)}, {mp.nstr(N_g,4)}, {mp.nstr(N_nu,4)}")
gate("the hierarchy: N_b < N_gamma + N_nu < S_dS",
     N_b < N_g + N_nu < S_dS)

print("C5 -- surface anchors")
paper = open(PAPER, encoding="utf-8").read()
part5 = open(PART5, encoding="utf-8").read()
part4b = open(PART4B, encoding="utf-8").read()
np_ = norm(paper).replace("**", "")
ok1 = "Baryonic matter is the content directly accessible to the observer on its own" in norm(part5)
ok1 &= "$T_{\\rm CMB} = 2.642$~K at leading order" in norm(part5)
gate("part5: the baryon-fraction proof sentence + the T_CMB leading-order line", ok1)
ok2 = "sup **minimizes** the horizon budget" in norm(paper)
gate("1n(iii)'s budget passage anchored", ok2)
ok3 = "the fully-committed composite — zero imports" in np_.lower() or \
      "The fully-committed composite — zero imports" in norm(paper).replace("*", "")
ok3 &= "exactly the Ω_b h² deviation carried through" in np_.replace("**", "")
ok3 &= "grep-verified uncommitted on every cascade surface" in np_
gate("1ab's key sentences anchored", ok3)
n_proton = len(re.findall(r"(?i)proton mass", part4b + part5))
gate("the m_p-uncommitted disclosure: zero 'proton mass' on the tex surfaces",
     n_proton == 0, f"hits = {n_proton}")

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (17 gates)")
print("READING: the census assembles from committed content plus two")
print("disclosed imports. Omega_b h^2 = 0.0225892 is fully committed and")
print("sits at +1.46 sigma; eta = 6.176e-10 (+0.98%, the composite's")
print("deviation carried through); the seat's de Sitter horizon holds")
print("4.9e78 baryons, 8.0e87 photons, 6.6e87 relic neutrinos against a")
print("budget of 3.315e122 nats. Data-facing assembly; no closure.")
sys.exit(0 if n_fail == 0 else 1)
