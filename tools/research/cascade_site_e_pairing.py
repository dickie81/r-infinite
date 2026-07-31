#!/usr/bin/env python3
"""Theorem 1y verifier: the site-E pairing entailed; member one closes.

Claim under test: the site-E pairing p(d) := P(d+1) -- 1k's "data-
anchored convention," member one's last conventional content after
the adoption resolved the sup anchor -- is an IDENTITY of Gamma-
argument arithmetic, entailed by committed content: (a) Part 0
defines p intrinsically in the d frame (the sphere-area decay rate,
p(d) = -1/2 ln pi + 1/2 psi((d+1)/2), with p = -d/dd log Omega_d
exactly); (b) Omega_d = 2/Gamma_R(d+1) exactly -- Part 0's area IS
the Definition-2.1 weight (and the formulation's T1 already commits
p(d) = (log Gamma_R)'(d+1) as a proved elementary identity); (c)
hence p(d) = P(d+1) with the "+1" the argument already inside
Omega_d, Definition 2.1, and A1 -- never a frame choice; (d) the
alternative p(d) := P(d) is the log-derivative of the forsworn
avatar 2/Gamma_R(d) = Omega_{d-1} (the PREVIOUS layer's area),
excluded by the committed dictionary, not by data. Member one
closes; the class keeps two members; the seven-item count stands.

Gates:
  E1 -- the identity chain: Omega_d = 2/Gamma_R(d+1) over d = 1..300
        (dps 50); p(d) = -d/dd log Omega_d (numeric derivative vs
        closed form); p(d) = P(d+1) as functions; Part 0's table
        rows Omega_5 = pi^3, Omega_7 = pi^4/3 exact.
  E2 -- the labels: bands B1 = {7..19}, B2 = {20..217} and integer
        argmax V = 5 under the entailed pairing (labels {5,7,19,217});
        the alternative P(d) reproduces 1k's gated exhibit
        {5,8,20,218}; Omega_{d-1} = 2/Gamma_R(d) (the avatar
        identity) gated.
  E3 -- source anchors, verbatim: Part 0's intrinsic definition and
        log-area identity; the formulation T1's committed
        p(d) = (log Gamma_R)'(d+1) line; the paper's avatar-
        forswearing Remark quote and "Definition-2.1-consistent
        pairing" naming.
  E4 -- the member-accounting sweep: the "three members and the
        seven-item count stand(s)" formula censused (7 paper, 5
        formulation, whitespace-normalized) with a 1y net-state
        marker at every occurrence (7 + 5 gated), plus the four
        targeted paper markers and one formulation open-routes
        marker (total "Theorem 1y round 107" = 11 paper; "T1y of
        the review paper, round 107" = 6 formulation).
  E5 -- 1y's key sentences (the entailment, the closure, the
        end-to-end assignment sentence) and the avatar falsifier
        anchored.

No data consumed; no number changes anywhere. Sabotage record (run
on scratchpad copies at the landing commit): (a) corrupting the E3
formulation anchor flips E3, exit 1; (b) deleting one formula
marker flips E4, exit 1.
"""
import os
import re
import sys

from mpmath import mp, mpf, pi, gamma, digamma, log, diff

mp.dps = 50

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
FORM = os.path.join(ROOT, "cascade-riemann-formulation.md")
PART0 = os.path.join(ROOT, "src", "cascade-series-part0.tex")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def GR(s):
    return pi ** (-mpf(s) / 2) * gamma(mpf(s) / 2)


def Om(d):
    return 2 * pi ** ((mpf(d) + 1) / 2) / gamma((mpf(d) + 1) / 2)


def p(d):
    return -mpf(log(pi)) / 2 + digamma((mpf(d) + 1) / 2) / 2


def P(s):
    return -mpf(log(pi)) / 2 + digamma(mpf(s) / 2) / 2


print("E1 -- the identity chain")
err1 = max(abs(Om(d) - 2 / GR(d + 1)) / Om(d) for d in range(1, 301))
gate("Omega_d = 2/Gamma_R(d+1) exactly, d = 1..300", err1 < mpf("1e-40"),
     f"max rel err {float(err1):.1e}")
err2 = max(abs(-diff(lambda x: log(Om(x)), mpf(d)) - p(d))
           for d in (1, 5, 7, 19, 100, 217))
gate("p(d) = -d/dd log Omega_d (numeric vs closed form)", err2 < mpf("1e-35"),
     f"max abs err {float(err2):.1e}")
err3 = max(abs(p(d) - P(d + 1)) for d in (1, 5, 7, 19, 217, 300))
gate("p(d) = P(d+1) as functions (Gamma-argument arithmetic)", err3 == 0
     or err3 < mpf("1e-49"), f"max abs err {float(err3):.1e}")
gate("Part 0's table rows: Omega_5 = pi^3, Omega_7 = pi^4/3 exact",
     abs(Om(5) - pi ** 3) < mpf("1e-45") and abs(Om(7) - pi ** 4 / 3) < mpf("1e-45"))

print("E2 -- the labels under each pairing")
c1, c2 = log(gamma(mpf(1) / 2)), gamma(mpf(1) / 2)
B1 = [d for d in range(1, 300) if 0 < p(d) < c1]
B2 = [d for d in range(1, 300) if c1 < p(d) < c2]


def V(d):
    return pi ** (mpf(d) / 2) / gamma(mpf(d) / 2 + 1)


argmax = max(range(1, 30), key=V)
gate("entailed pairing: {argmax V, min B1, max B1, max B2} = {5, 7, 19, 217}",
     argmax == 5 and B1[0] == 7 and B1[-1] == 19 and B2[-1] == 217,
     f"argmax {argmax}; B1 [{B1[0]},{B1[-1]}]; max B2 {B2[-1]}")
B1a = [d for d in range(1, 300) if 0 < P(d) < c1]
B2a = [d for d in range(1, 300) if c1 < P(d) < c2]
gate("alternative P(d) reproduces 1k's exhibit {5, 8, 20, 218}",
     argmax == 5 and B1a[0] == 8 and B1a[-1] == 20 and B2a[-1] == 218,
     f"B1' [{B1a[0]},{B1a[-1]}]; max B2' {B2a[-1]}")
err4 = max(abs(Om(d - 1) - 2 / GR(d)) / Om(d - 1) for d in range(2, 301))
gate("the avatar identity: Omega_(d-1) = 2/Gamma_R(d) (the previous layer)",
     err4 < mpf("1e-40"), f"max rel err {float(err4):.1e}")

print("E3 -- source anchors (verbatim)")
part0 = open(PART0, encoding="utf-8").read()
paper = open(PAPER, encoding="utf-8").read()
form = open(FORM, encoding="utf-8").read()


def norm(s):
    return " ".join(s.split())


ok1 = "The sphere-area decay rate decomposes as" in norm(part0)
ok1 &= "p(d) = -\\tfrac{1}{2}\\ln\\pi +" in part0
ok1 &= "first derivative of the log-area, which is $-p(d)$" in norm(part0)
gate("Part 0: the intrinsic definition + the log-area identity anchored", ok1)
ok2 = "p(d) = (log Γ_ℝ)′(d+1)  (potential = logarithmic derivative)" in form
gate("formulation T1: the committed p(d) = (log Gamma_R)'(d+1) line anchored", ok2)
ok3 = "The paper never uses the avatar; the arithmetic is primary" in norm(paper)
ok3 &= "the Definition-2.1-consistent pairing" in norm(paper)
gate("paper: the avatar-forswearing Remark + Definition-2.1 naming anchored", ok3)

print("E4 -- the member-accounting sweep census")
FORMULA = r"(?i)three\s+members\s+and\s+the\s+seven-item\s+count\s+stands?"
n_pp = len(re.findall(FORMULA, paper))
n_ff = len(re.findall(FORMULA, form))
gate("formula census: 7 paper, 5 formulation occurrences",
     n_pp == 7 and n_ff == 5, f"paper {n_pp}, formulation {n_ff}")
mp_marker = norm("Net-state, Theorem 1y round 107: member one closes — the "
                 "site-E pairing entailed given the tower's dictionary")
mf_marker = norm("Net-state, T1y of the review paper, round 107: member one "
                 "closes — the pairing entailed given the dictionary")
n_mp = norm(paper).count(mp_marker)
n_mf = norm(form).count(mf_marker)
gate("one 1y formula-marker per occurrence: 7 paper, 5 formulation",
     n_mp == 7 and n_mf == 5, f"paper {n_mp}, formulation {n_mf}")
n_all_p = norm(paper).count("Theorem 1y round 107")
n_all_f = norm(form).count("T1y of the review paper, round 107")
gate("total 1y markers: 11 paper (7 formula + 4 targeted), 6 formulation",
     n_all_p == 11 and n_all_f == 6, f"paper {n_all_p}, formulation {n_all_f}")

print("E5 -- 1y's key sentences + the falsifier")
np_ = norm(paper)
ok4 = "p(d) = P(d+1) is Γ-argument arithmetic" in np_.replace("**", "")
ok4 &= "Member one closes. The class keeps two members" in np_.replace("**", "")
ok4 &= "entailed end-to-end given the amended axioms" in np_.replace("**", "")
gate("the entailment, the closure, and the end-to-end sentence anchored", ok4)
ok5 = ("any committed surface found reading a layer's potential at the avatar "
       "argument" in np_.replace("**", ""))
gate("the avatar falsifier anchored", ok5)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (15 gates)")
print("READING: the site-E pairing is entailed -- Part 0's intrinsic p,")
print("the exact identity Omega_d = 2/Gamma_R(d+1) (Definition 2.1's")
print("weight, T1's committed line), and Gamma-argument arithmetic close")
print("member one; the alternative pairing is the forsworn avatar's")
print("log-derivative, excluded by the dictionary, not by data. The class")
print("keeps two members; the seven-item count stands.")
sys.exit(0 if n_fail == 0 else 1)
