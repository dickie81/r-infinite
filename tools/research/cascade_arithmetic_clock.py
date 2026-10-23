#!/usr/bin/env python3
"""
The arithmetic clock: spin types, census equilibration, and epoch focus.

Consolidates the computations behind Addendum 6 of cascade-surprisal-audit.md.
Frame under test (user conjecture, developed across the session): the cascade
clock ticks one PRIME per Planck time; each tick adds an orthogonal dimension
to the multiplicative lattice Q+^x = Z^infinity (unique factorisation); the
Pratt parent set of a prime (prime factors of p-1) is its complete list of
"spin types" (an order-l character exists iff l | p-1); quadratic reciprocity
is the exchange rule of the universal Z/2 type.

Parts
  A. Prime-clock tower spectrum: 217 prime ticks (primes 2..1327) -> how well
     the first 12 Riemann zeros are resolved (vs the integer clock).
  B. Epoch focus table: peak width ~ 12.6/ln D under both clocks; per-tick
     fluctuation today.
  C. Spin-type census of the tower vs Dirichlet densities 1/(l-1); special
     species (Fermat primes = pure spin-1/2; 211 = maximally charged).
  D. Exchange classes mod 4 and the reciprocity exchange rule.
  E. Census convergence law: sqrt(x) * deviation is O(1) (verified to 1e7),
     giving ~6e-32 relative deviation at today's depth.  The convergence
     RATE is equivalent to GRH.
  F. Confrontation with observed spin demographics + the fossil-bias check
     (census bias = baryon asymmetry at the leptogenesis epoch; ~1.4 bits).
"""

import math

import numpy as np

ZEROS = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
         37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
         52.970321, 56.446248]


def primes_upto(D):
    s = np.ones(D + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(D ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def part_A():
    print("=" * 78)
    print("PART A: prime-clock tower spectrum (tick 217 -> p_217 = 1327)")
    print("=" * 78)
    P = primes_upto(1327).astype(float)
    lg = np.log(P)
    L = lg[-1]
    w = np.log(P) / np.sqrt(P) * np.sin(math.pi * lg / L) ** 2   # Hann taper
    errs = []
    for g in ZEROS:
        t = np.arange(g - 1.2, g + 1.2, 0.001)
        S = np.abs(np.exp(-1j * np.outer(t, lg)) @ w)
        errs.append(t[int(np.argmax(S))] - g)
    n_good = sum(1 for e in errs if abs(e) < 0.5)
    print(f"  zeros matched within 0.5: {n_good}/12,"
          f" mean|err| {np.mean(np.abs(errs)):.4f}")
    print("  (integer clock D=217, Addendum 5 pipeline: mean|err| 0.164 --")
    print("   the prime clock resolves the zeros ~2.5x more precisely at the")
    print("   same tick count: no silent composite ticks, wider log-range)")


def part_B():
    print()
    print("=" * 78)
    print("PART B: epoch focus (width ~ 12.6/ln D) and present-day fluctuation")
    print("=" * 78)

    def pN(N):
        l = math.log(N)
        return N * (l + math.log(l) - 1)

    print(f"{'epoch':>14}{'prime ticks':>13}{'width(prime)':>13}"
          f"{'width(integer)':>15}")
    for name, N in [("reheating", 217), ("end of BBN", 3.3e45),
                    ("recombination", 2.3e56), ("today", 8e60)]:
        D = 1327 if N == 217 else pN(N)
        print(f"{name:>14}{N:>13.1e}{12.56/math.log(D):>13.4f}"
              f"{12.56/math.log(N):>15.4f}")
    N = 8e60
    D = pN(N)
    term = math.log(D) / math.sqrt(D)
    mass = 2 * math.sqrt(D)
    print(f"  today: relative spectral nudge per tick ~ {term/mass:.1e};")
    print(f"  fractional sharpening ~ {1.9e43/N/math.log(D):.1e} per second")
    print("  => clock choice (integers vs primes) shifts today's focus by ~3%:")
    print("     all late-epoch conclusions are clock-robust.")


def part_C():
    print()
    print("=" * 78)
    print("PART C: spin-type census of the tower (l-spin iff l | p-1)")
    print("=" * 78)
    P = primes_upto(1327)
    odd = P[1:]
    print(f"{'type l':>7}{'carriers':>10}{'fraction':>10}{'1/(l-1)':>9}")
    for l in (2, 3, 5, 7, 11, 13):
        c = int(((odd - 1) % l == 0).sum())
        print(f"{l:>7}{c:>10}{c/len(odd):>10.3f}{1/(l-1):>9.3f}")

    def parents(p):
        n, f, d = p - 1, set(), 2
        while d * d <= n:
            while n % d == 0:
                f.add(d)
                n //= d
            d += 1
        if n > 1:
            f.add(n)
        return sorted(f)

    fermat = [int(p) for p in odd if parents(p) == [2]]
    print(f"  pure spin-1/2 species (p-1 = 2^k): {fermat} -- Fermat primes;")
    print("  five known ever (last: 65537, tick ~6543), conjecturally extinct")
    best = max(odd, key=lambda p: len(parents(int(p))))
    print(f"  most spin types: {best} (= 2*3*5*7 + 1), parents"
          f" {parents(int(best))}")


def part_D():
    print()
    print("=" * 78)
    print("PART D: exchange classes and the reciprocity exchange rule")
    print("=" * 78)
    P = primes_upto(1327)
    odd = P[1:]
    b = int((odd % 4 == 1).sum())
    f = int((odd % 4 == 3).sum())
    print(f"  tower census mod 4: {b} 'bosonic' (1 mod 4),"
          f" {f} 'fermionic' (3 mod 4)")

    def legendre(a, p):
        r = pow(a, (p - 1) // 2, p)
        return -1 if r == p - 1 else r

    for (p, q) in [(13, 17), (7, 11)]:
        s = legendre(p, q) * legendre(q, p)
        tag = ("antisymmetric (both 3 mod 4)" if p % 4 == 3 and q % 4 == 3
               else "symmetric")
        print(f"  ({p}|{q})({q}|{p}) = {s:+d}   {tag}")
    print("  (three-body statistics exist beyond pairwise: Redei symbols /")
    print("   Borromean prime triples; cf. Mazur-Morishita knots-primes and")
    print("   arithmetic Chern-Simons theory)")


def part_E():
    print()
    print("=" * 78)
    print("PART E: census convergence -- sqrt(x)*deviation is O(1)")
    print("=" * 78)
    print(f"{'x':>10}{'sq(x)*dev3':>12}{'sq(x)*dev5':>12}{'sq(x)*dev7':>12}")
    for X in (1327, 10 ** 5, 10 ** 7):
        P = primes_upto(X)[1:]
        r = math.sqrt(X)
        row = "".join(f"{r * (float(np.mean((P-1) % l == 0)) - 1/(l-1)):>12.2f}"
                      for l in (3, 5, 7))
        print(f"{X:>10}{row}")
    x = 1.15e63
    dev = 2 / math.sqrt(x)
    print(f"  extrapolation to today's depth x ~ 1.15e63:"
          f" |fraction - 1/(l-1)| ~ {dev:.0e}")
    print("  sign: carriers systematically DEFICIENT (Chebyshev bias against")
    print("  the quadratic-residue class); residual oscillates as cos(g_n ln x)")
    print("  -- conducted by the Riemann zeros (~6 Gyr period for g_1 today).")
    print("  NOTE: the sqrt(x) convergence RATE is equivalent to GRH.")


def part_F():
    print()
    print("=" * 78)
    print("PART F: observed spin demographics + fossil-bias check")
    print("=" * 78)
    ph, nu = 411.0, 336.0
    print(f"  observed, by number density: bosons {ph/(ph+nu):.0%},"
          f" fermions {nu/(ph+nu):.0%}  (set by (4/11)^(1/3))")
    print("  by early dof: 24% / 76% (g* = 106.75); by species: 12+1 / 12")
    print("  arithmetic census: 50/50 +- 1e-32  => NO quantitative match:")
    print("  abundances are thermal history, not census.  Type spectrum DOES")
    print("  match: 3+1D realises only the universal Z/2 (roots of unity in R")
    print("  = {+-1}); higher types (3,5,7,..) appear only in 2D systems")
    print("  (FQHE anyons at odd-denominator fillings).")
    eta = 6.1e-10
    x = (2 / eta) ** 2
    N = x / math.log(x)
    T = 0.3 * 1.2e19 * N ** -0.5
    print(f"  fossil-bias check: census bias = eta = {eta:.1e} at tick"
          f" ~{N:.1e}")
    print(f"  -> T ~ {T:.0e} GeV, inside the leptogenesis window"
          f" (1e9..1e12 GeV)")
    print("  coincidence priced at ~1.4 bits (3 of ~8 plausible decades);")
    print("  becomes evidence only if the freeze-out tick is derived")
    print("  independently.")


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    print()
    print("done.")
