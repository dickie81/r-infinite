"""Exact-arithmetic check of the parameter choices in ARGUMENT.md section 3 (README round 519).

For each instance (A, theta0) and each eta, with the choices of section 3.1
    delta1 = eta/(2A),  T = q^delta1,  x = q^(A+eta),
    delta  = eta(1 - theta0)/(4(A + eta)),  k = ceil(2 + 2A/eta),
it checks, in exact rationals, every exponent inequality the proof uses:
    (a) 0 < delta <= (1 - theta0)/12, so theta0 + delta < 1                     (3.1, 3.6)
    (b) A*delta1 - eta = -eta/2 < 0: (2qT)^A/x -> 0                               (3.10)
    (c) 1 - (A+eta)/2 + (A+eta)*delta <= -eta/4: phi(q) x^(delta - 1/2) -> 0     (3.10, first term)
    (d) (A+eta)*delta - eta(1-theta0)/2 = -eta(1-theta0)/4 < 0                   (3.10, second term)
    (e) 1 - delta1*(k - 1) < 0: phi(q) T^(1-k) -> 0                               (3.10, third term)
    (f) (A+eta)/2 > 1: q log x = o(x^(1/2))                                      (3.11)
These are the exponents of q; the logarithmic factors are absorbed because each margin is a fixed
negative power of q. The script checks arithmetic only, not the analysis.
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


def check(A, th, eta):
    d1 = eta / (2 * A)
    d = eta * (1 - th) / (4 * (A + eta))
    k = ceil(2 + 2 * A / eta)
    rows = {
        "a": (0 < d <= (1 - th) / 12) and (th + d < 1),
        "b": A * d1 - eta == -eta / 2 and A * d1 - eta < 0,
        "c": 1 - (A + eta) / 2 + (A + eta) * d <= -eta / 4,
        "d": (A + eta) * d - eta * (1 - th) / 2 == -eta * (1 - th) / 4,
        "e": 1 - d1 * (k - 1) < 0,
        "f": (A + eta) / 2 > 1,
    }
    return d1, d, k, rows


def main():
    fails = 0
    for name, A, th in INSTANCES:
        assert A >= 2 and th < 1
        print(f"{name}: A = {A}, theta0 = {th}, L = A + eta")
        for eta in ETAS:
            d1, d, k, rows = check(A, th, eta)
            bad = [key for key, ok in rows.items() if not ok]
            fails += len(bad)
            print(f"  eta = {eta}: delta1 = {d1}, delta = {d}, k = {k}; "
                  f"checks a-f {'pass' if not bad else 'FAIL ' + ','.join(bad)}")
    print(f"{len(INSTANCES) * len(ETAS)} cases, {fails} failures")
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(main())
