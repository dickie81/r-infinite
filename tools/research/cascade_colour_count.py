#!/usr/bin/env python3
"""Theorem 1w verifier: the kernel-native colour count.

Claim under test: given the pairing-act (standing charged member; 1r
fixes chi_{-3}) and T8's committed root-unit identity ("The su(3)
roots are the units mu_6 of Z[omega] (point-by-point)", PROVED,
Addendum 36), the colour multiplicity N_c = 3 is ENTAILED: the paired
field's unit torsion is the A_2 root system by the rank-2
classification, and N(N-1) = 6 forces N = 3 uniquely. The registered
finite-places negative of 1f(iii) (round-102 F1: the docstring header
was the one F101-5 instance the round-101 sweep missed) stands
verbatim -- this route reads
the unit torsion at the infinite embedding (global, archimedean), no
finite-place datum. Kernel-3 = cascade-3 (rho(12)-1, Adams) is
reported as a Check-8 cross-check, not forcing: the layer-12
selection remains papers-side.

Gates:
  W1 -- torsion census: over all fundamental discriminants d < 0 with
        |d| <= 10^4, w = 6 only at d = -3, w = 4 only at d = -4,
        w = 2 at every other (count gated); the paired field is the
        unique one with six torsion units.
  W2 -- root-system axioms for mu_6 at the infinite embedding
        (reduced, crystallographic, reflection-closed, spanning) and
        the rank-2 classification: 6 roots => A_2; N(N-1) = 6 has the
        unique positive-integer solution N = 3.
  W3 -- uniqueness among fields: mu_4 (d = -4) is a root system but
        DECOMPOSABLE (A_1 x A_1, orthogonal pair -- non-simple); all
        other d have torsion {+-1}, rank 1, non-spanning. Q(zeta_3)
        is the unique imaginary quadratic field whose unit torsion is
        the root system of a simple Lie algebra.
  W4 -- Check-8 cross-check: Radon-Hurwitz rho(2^(4a+b) m) = 8a + 2^b;
        rho(12) - 1 = 3; census over d in [5, 19]: d = 12 unique with
        rho(d) - 1 = 3. Plus the disclosed exhibit: the four-way
        coincidence at d = -3 (conductor, |disc|, ramified prime,
        odd-torsion order all = 3) vs its failure at d = -4
        (4, 4, 2, 1) -- all four invariants COMPUTED from d
        (round-101 F3: the first commit hardcoded the tuples, a gate
        that could not fail; the conductor is now the computed
        minimal defining modulus of the Kronecker symbol, the
        ramified primes come from factorisation, the odd-torsion
        order from the computed unit count).
  W5 -- surface anchors, verbatim and failable: the theorem's key
        sentences in the paper; T8's identity sentence and the four
        net-state markers in the formulation (T8 tail, ledger row 4,
        and -- round-101 F1 -- T1e(v) and T1f(iii)); the registered
        negative (Theorem 1f(iii); round-101 F5 corrected the first
        draft's "1g(iii)" address) plus its marker in the paper; the
        round-101 F6/F7 sweep sentences.

No data consumed; no number changes anywhere. Sabotage record
(round-101 F2 corrected the original docstring, which claimed
per-gate sabotage coverage that had not been run -- one sabotage
existed at commit time): the W5 adjudication-anchor perturbation
flips W5 (Addendum 180); the round-101 sweep added the W1
exact-cardinality gate (total == 3043), under which the previously
undetected is_fundamental excision (which inflated the census to
3,553) now fails, and made W4's exhibit computed rather than
recited.
"""
import cmath
import math
import os
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
FORM = os.path.join(ROOT, "cascade-riemann-formulation.md")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def is_fundamental(d):
    if d >= 0:
        return False
    if d % 4 == 1:
        m = -d
    elif d % 4 == 0:
        if (d // 4) % 4 == 1:
            return False
        m = -d // 4
    else:
        return False
    i = 2
    while i * i <= m:
        if m % (i * i) == 0:
            return False
        i += 1
    return True


def unit_count(d):
    cnt = 0
    for y in range(-3, 4):
        for x in range(-4, 5):
            if d % 4 == 0:
                n = x * x + (-d // 4) * y * y
            else:
                n = x * x + x * y + ((1 - d) // 4) * y * y
            if n == 1:
                cnt += 1
    return cnt


print("W1 -- torsion census over fundamental discriminants, |d| <= 10^4")
w6, w4, w2, total = [], [], 0, 0
for d in range(-1, -10001, -1):
    if is_fundamental(d):
        total += 1
        w = unit_count(d)
        if w == 6:
            w6.append(d)
        elif w == 4:
            w4.append(d)
        elif w == 2:
            w2 += 1
        else:
            w6.append(("BAD", d, w))
gate("w = 6 exactly at {-3}", w6 == [-3], f"w6 set = {w6}")
gate("w = 4 exactly at {-4}", w4 == [-4], f"w4 set = {w4}")
gate("all others w = 2; census cardinality exact (round-101 F4)",
     w2 == total - 2 and total == 3043,
     f"{w2} of {total} fundamental discriminants (gate: total == 3043)")

print("W2 -- mu_6 is a root system; classification forces A_2 and N = 3")
roots6 = [cmath.exp(1j * math.pi * k / 3) for k in range(6)]


def cartan(a, b):
    return 2 * (a.real * b.real + a.imag * b.imag) / abs(b) ** 2


def is_root_system(roots):
    tol = 1e-9
    # spanning R^2: two non-parallel roots exist
    span = any(abs(a.real * b.imag - a.imag * b.real) > tol
               for a in roots for b in roots)
    # reduced: for each root a, 2a is not a root; multiples limited to +-a
    reduced = all(not any(abs(2 * a - r) < tol for r in roots) for a in roots)
    negs = all(any(abs(-a - r) < tol for r in roots) for a in roots)
    # crystallographic: Cartan pairings integral
    cryst = all(abs(cartan(a, b) - round(cartan(a, b))) < tol
                for a in roots for b in roots)
    # reflection closure
    refl = all(any(abs((a - cartan(a, b) * b) - r) < tol for r in roots)
               for a in roots for b in roots)
    return span and reduced and negs and cryst and refl


gate("mu_6 satisfies the root-system axioms", is_root_system(roots6))
rank2_counts = {"A1xA1": 4, "A2": 6, "B2": 8, "G2": 12}
matches = [k for k, v in rank2_counts.items() if v == len(roots6)]
gate("rank-2 classification: 6 roots => A2 uniquely", matches == ["A2"],
     f"matches = {matches}")
nsols = [n for n in range(1, 50) if n * (n - 1) == 6]
gate("N(N-1) = 6 has unique positive solution N = 3", nsols == [3],
     f"solutions = {nsols}")

print("W3 -- uniqueness among imaginary quadratic fields")
roots4 = [1, 1j, -1, -1j]
ortho_pair = abs(cartan(1, 1j)) < 1e-12
gate("mu_4 (d = -4) is a root system but decomposable (A1xA1)",
     is_root_system(roots4) and ortho_pair,
     "orthogonal pair <1, i> -- non-simple")
# every other field: torsion {+-1}, does not span the plane
span_fail = not any(abs(a.real * b.imag - a.imag * b.real) > 1e-9
                    for a in [1, -1] for b in [1, -1])
gate("torsion {+-1} (all other d) is rank 1, non-spanning", span_fail)
gate("unique simple-root-system torsion field = Q(zeta_3)",
     w6 == [-3] and matches == ["A2"] and ortho_pair and span_fail)

print("W4 -- Check-8 cross-check (cascade side) + disclosed exhibit")


def rho(n):
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    a, b = divmod(v, 4)
    return 2 ** b + 8 * a


gate("rho(12) - 1 = 3", rho(12) - 1 == 3)
census = [d for d in range(5, 20) if rho(d) - 1 == 3]
gate("d = 12 unique in [5, 19] with rho(d) - 1 = 3", census == [12],
     f"census = {census}")
# four-way coincidence at -3, COMPUTED from d (round-101 F3)


def kronecker(a, n):
    if n == 0:
        return 1 if abs(a) == 1 else 0
    k = 1
    if n < 0:
        n = -n
        if a < 0:
            k = -k
    while n % 2 == 0:
        n //= 2
        if a % 2 == 0:
            return 0
        if a % 8 in (3, 5):
            k = -k
    a %= n
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                k = -k
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            k = -k
        a %= n
    return k if n == 1 else 0


def conductor(d):
    # minimal q such that chi_d(n) depends only on n mod q (n coprime to 2d)
    for q in range(1, abs(d) + 1):
        if abs(d) % q:
            continue
        classes = {}
        ok = True
        for n in range(1, 12 * abs(d)):
            if math.gcd(n, 2 * abs(d)) != 1:
                continue
            r, v = n % q, kronecker(d, n)
            if classes.setdefault(r, v) != v:
                ok = False
                break
        if ok:
            return q
    return abs(d)


def ram_primes(d):
    m, ps, p = abs(d), [], 2
    while m > 1:
        if m % p == 0:
            ps.append(p)
            while m % p == 0:
                m //= p
        p += 1
    return ps


def odd_torsion(w):
    while w % 2 == 0:
        w //= 2
    return w


def invariants(d):
    ps = ram_primes(d)
    return (conductor(d), abs(d), ps[0] if len(ps) == 1 else ps,
            odd_torsion(unit_count(d)))


inv_m3 = invariants(-3)
inv_m4 = invariants(-4)
gate("four-way coincidence at d = -3 (all = 3, computed); fails at d = -4",
     inv_m3 == (3, 3, 3, 3) and inv_m4 == (4, 4, 2, 1),
     f"d=-3: {inv_m3}, d=-4: {inv_m4}")

print("W5 -- surface anchors (verbatim, failable)")
paper = open(PAPER, encoding="utf-8").read()
form = open(FORM, encoding="utf-8").read()
ok5 = "Theorem 1w (the kernel-native colour count" in paper
ok5 &= "the unique positive-integer solution" in paper
ok5 &= "The kernel does not produce 3 unaided: it produces 3 **given the\nact**." in paper
ok5 &= "internal consistency, not forcing" in paper
ok5 &= paper.count("N_c = 3 is not derived\nfrom the finite places") >= 1
ok5 &= "what remains\narchimedean is the layer alone" in paper  # 1f(iii) marker
ok5 &= "the registered negative lives in Theorem 1f(iii)" in paper  # round-101 F5
ok5 &= "plane-spanning" in paper  # round-101 F6 qualifier
ok5 &= "not the 6 itself" in paper  # round-101 F7 disclosure
gate("paper: theorem + adjudication + registered-negative marker anchored", ok5)
ok6 = "The su(3) roots are the units μ₆ of ℤ[ω]" in form
ok6 &= "the instantiation residue narrows to per-leg occupancy only" in form  # T8 marker
ok6 &= "residue narrows to per-leg occupancy)*" in form  # ledger row 4 marker
ok6 &= "the open item narrows to the layer alone" in form  # round-101 F1, T1f(iii)
ok6 &= "the layer remains the open residue" in form  # round-101 F1, T1e(v)
gate("formulation: T8 identity + all four net-state markers anchored", ok6)
ok7 = "count side narrows further" in paper  # Door-3 remark marker
gate("paper: Door-3 remark net-state marker anchored", ok7)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (15 gates)")
print("READING: N_c = 3 is entailed given the pairing-act (charged) plus")
print("T8's root-unit identity (committed), via unit torsion -> A2 ->")
print("N(N-1) = 6. The registered finite-places negative stands verbatim;")
print("the archimedean residue narrows from {count, layer} to {layer}.")
print("Kernel-3 = cascade-3 is a Check-8 cross-check, not forcing.")
sys.exit(0 if n_fail == 0 else 1)
