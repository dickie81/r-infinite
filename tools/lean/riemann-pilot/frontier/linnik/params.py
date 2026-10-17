"""Exact-arithmetic check of the parameter choices in ARGUMENT.md section 3 (README round 519).

For each instance (A, theta0) and each eta, with the choices of section 3.1
    delta1 = eta/(2A),  T = q^delta1,  x = q^(A+eta),
    delta  = eta(1 - theta0)/(4(A + eta)),  k = ceil(2 + 2A/eta),
it checks, in exact rationals, the exponent inequalities that sections 3.1, 3.10 and 3.11 use, in the
forms the text uses:
    (h) A >= 2 and 1/2 <= theta0 < 1 and 0 < eta <= 1: the theorem's hypotheses       (1, 3.1)
    (a) 0 < delta <= (1 - theta0)/12, so theta0 + delta < 1                           (3.1, 3.6)
    (b) A*delta1 - eta = -eta/2 < 0: (2qT)^A/x -> 0                                     (3.10)
    (c) 1 - (A+eta)/2 + (A+eta)*delta <= -eta/4: phi(q) x^(delta - 1/2) -> 0           (3.10, first term)
    (d) (A+eta)*delta - eta(1-theta0)/2 = -eta(1-theta0)/4 < 0                         (3.10, second term)
    (e) delta1*(k - 1) >= 1 + eta/(2A): phi(q) T^(1-k) <= q^(-eta/(2A))                 (3.10, third term)
    (f) (A+eta)/2 >= 1 + eta/2: x^(1/2) >= q^(1 + eta/2)                               (3.11)
These are the exponents of q; the logarithmic factors are absorbed because each margin is a fixed
negative power of q.

Scope. For every A >= 2, 1/2 <= theta0 < 1 and 0 < eta <= 1, rows (a)-(f) follow from the formulas
above, so a pass on the 20 committed cases shows only that the formulas were transcribed into the
inequalities correctly; it is not an independent fact. To show that the rows can fail, the script
also runs four mutations (three mis-transcribed parameter choices and an instance with A < 2) and
requires each to fail at least one case; a mutation that passes everywhere counts as a failure.
The script checks arithmetic only, not the analysis.
"""
from fractions import Fraction as F
from math import ceil

INSTANCES = [
    ("Huxley 12/5, stack half-plane 11/12", F(12, 5), F(11, 12)),
    ("Chen-Gupta-Li 7/3, stack half-plane 11/12", F(7, 3), F(11, 12)),
    ("round 518 route over characters, 1 + 2*(11/12) = 17/6", F(17, 6), F(11, 12)),
    ("Huxley 12/5, the release's 7/8", F(12, 5), F(7, 8)),
    ("round 518 route at 7/8, 1 + 2*(7/8) = 11/4", F(11, 4), F(7, 8)),
]
ETAS = [F(1), F(1, 10), F(1, 100), F(1, 1000)]


def choices(A, th, eta):
    """The parameter choices of section 3.1."""
    return eta / (2 * A), eta * (1 - th) / (4 * (A + eta)), ceil(2 + 2 * A / eta)


def rows(A, th, eta, d1, d, k):
    return {
        "h": A >= 2 and F(1, 2) <= th < 1 and 0 < eta <= 1,
        "a": (0 < d <= (1 - th) / 12) and (th + d < 1),
        "b": A * d1 - eta == -eta / 2 and A * d1 - eta < 0,
        "c": 1 - (A + eta) / 2 + (A + eta) * d <= -eta / 4,
        "d": (A + eta) * d - eta * (1 - th) / 2 == -eta * (1 - th) / 4
             and (A + eta) * d - eta * (1 - th) / 2 < 0,
        "e": d1 * (k - 1) >= 1 + eta / (2 * A),
        "f": (A + eta) / 2 >= 1 + eta / 2,
    }


MUTATIONS = [
    ("delta1 = eta/A", lambda A, th, eta: (eta / A,) + choices(A, th, eta)[1:], INSTANCES),
    ("delta twice as large", lambda A, th, eta: (choices(A, th, eta)[0], eta * (1 - th) / (2 * (A + eta)),
                                                  choices(A, th, eta)[2]), INSTANCES),
    ("k = ceil(1 + 2A/eta)", lambda A, th, eta: choices(A, th, eta)[:2] + (ceil(1 + 2 * A / eta),), INSTANCES),
    ("an instance with A = 9/5 < 2", choices, [("A = 9/5, theta0 = 11/12", F(9, 5), F(11, 12))]),
]


def census(param, instances):
    """The number of failing (case, row) pairs and the number of cases."""
    fails, cases = 0, 0
    for _, A, th in instances:
        for eta in ETAS:
            fails += sum(1 for ok in rows(A, th, eta, *param(A, th, eta)).values() if not ok)
            cases += 1
    return fails, cases


def main():
    fails = 0
    for name, A, th in INSTANCES:
        print(f"{name}: A = {A}, theta0 = {th}, L = A + eta")
        for eta in ETAS:
            d1, d, k = choices(A, th, eta)
            bad = [key for key, ok in rows(A, th, eta, d1, d, k).items() if not ok]
            fails += len(bad)
            print(f"  eta = {eta}: delta1 = {d1}, delta = {d}, k = {k}; "
                  f"checks h,a-f {'pass' if not bad else 'FAIL ' + ','.join(bad)}")
    print(f"{len(INSTANCES) * len(ETAS)} cases, {fails} failures")
    uncaught = 0
    for name, param, instances in MUTATIONS:
        mfails, mcases = census(param, instances)
        caught = mfails > 0
        uncaught += 0 if caught else 1
        print(f"mutation '{name}': {mfails} failing rows over {mcases} cases, {'caught' if caught else 'NOT CAUGHT'}")
    print(f"{len(MUTATIONS)} mutations, {len(MUTATIONS) - uncaught} caught")
    return 1 if fails or uncaught else 0


if __name__ == "__main__":
    raise SystemExit(main())
