#!/usr/bin/env python3
"""Fold attack, instrument 1: the displacement structure function
D(l) = E[(delta_{n+l} - delta_n)^2], delta_n = Nbar(gamma_n) - n,
measured for (a) the 380 zeros and (b) CUE unfolded to the Riemann
density -- overlaid with the two ANALYTIC candidates:

  CUE:  D(l) = (1/pi^2)(ln(2 pi l) + gamma_E + 1)     [GUE/CUE
        counting variance; displacement increments = counting]
  zeta: D(l) = (2/pi^2) sum_{p^k <= T/2pi} (1/(k^2 p^k))
                  * (1 - cos(k ln p * l / rho(T))),
        rho(T) = ln(T/2pi)/(2 pi)   [explicit formula, diagonal
        counting; primes resolved to the Heisenberg scale; the
        large-l saturation is (2/pi^2)(ln ln(T/2pi) + M + k>=2
        terms), the primes' budget]

Empirical D from sliding windows centered at heights T0 in the
1bc ladder range so the analytic T-dependence is testable.
"""
import numpy as np, math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ckpt_key

TWO_PI = 2*math.pi
EULER = 0.5772156649015329
MERTENS = 0.2614972128476428


def Nbar(x):
    return x/TWO_PI*(np.log(x/TWO_PI) - 1) + 7.0/8


def inv_Nbar(t, g0=20.0):
    g = g0
    for _ in range(80):
        g -= (Nbar(g) - t)/(np.log(g/TWO_PI)/TWO_PI)
        g = max(g, 8.0)   # clamp above 2 pi: Newton diverges for t <~ 0
    return g


def zeros380():
    par = {"n": 380, "dps": 13}
    st = ckpt_key.load("fold_zeros", __file__, par)
    if st is None:
        from mpmath import mp, zetazero
        mp.dps = 13
        st = [float(zetazero(k).imag) for k in range(1, 381)]
        ckpt_key.save("fold_zeros", __file__, par, st)
    return np.array(st)


def primes_upto(n):
    sieve = np.ones(n + 1, bool); sieve[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = False
    return np.nonzero(sieve)[0]


def D_emp(delta, lmax):
    return np.array([np.mean((delta[l:] - delta[:-l])**2)
                     for l in range(1, lmax + 1)])


def D_cue_analytic(l):
    return (np.log(TWO_PI*l) + EULER + 1)/math.pi**2


def D_zeta_analytic(l, T):
    X = T/TWO_PI
    rho = math.log(X)/TWO_PI
    ps = primes_upto(int(X) + 1)
    tot = np.zeros_like(np.atleast_1d(l), dtype=float)
    for p in ps:
        k, pk = 1, int(p)
        while pk <= X:
            w = 1.0/(k*k*pk)
            tot += w*(1 - np.cos(k*math.log(p)*np.atleast_1d(l)/rho))
            k += 1
            pk *= int(p)
    return tot/math.pi**2   # E[sin^2] = 1/2: prefactor 1/pi^2, not 2/pi^2


def D_zeta_sat(T):
    X = T/TWO_PI
    ps = primes_upto(int(X) + 1)
    s = sum(1.0/p for p in ps)
    s2 = 0.0
    for p in ps:
        k, pk = 2, int(p)*int(p)
        while pk <= X:
            s2 += 1.0/(k*k*pk)
            k += 1
            pk *= int(p)
    return (s + s2)/math.pi**2, (math.log(math.log(X)) + MERTENS)/math.pi**2


if __name__ == "__main__":
    Z = zeros380()
    lmax = 48
    lags = np.arange(1, lmax + 1)
    # empirical zeta D over the 1bc window (zeros 40..340 ~ heights 130-500)
    dz = Nbar(Z) - np.arange(1, len(Z) + 1) + 0.5
    Dz = D_emp(dz[40:340], lmax)
    # empirical CUE D: eigenphases of dim-380 CUE (uniform density --
    # exact unfolding, no edge; the 1bc headline comparator class)
    from scipy.stats import unitary_group
    rng_seeds = (11, 23, 47, 61, 83, 101, 131, 151, 173, 199)
    Dc_all = []
    for s in rng_seeds:
        U = unitary_group(dim=380, seed=s).rvs()
        ph = np.sort(np.angle(np.linalg.eigvals(U)))
        u = (ph - ph[0])*380/TWO_PI       # level units: mean spacing 1
        Dc_all.append(D_emp(u - np.arange(len(u)), lmax))
    Dc = np.mean(Dc_all, axis=0)
    T0 = 320.0                             # window center height
    Dza = D_zeta_analytic(lags.astype(float), T0)
    Dca = D_cue_analytic(lags.astype(float))
    sat_true, sat_llX = D_zeta_sat(T0)
    print("  l   D_zeta(emp)  D_zeta(analytic)  D_cue(emp)  D_cue(analytic)")
    for i in (0, 1, 3, 7, 11, 15, 23, 31, 47):
        print(f" {lags[i]:3d}   {Dz[i]:.3f}        {Dza[i]:.3f}          "
              f"{Dc[i]:.3f}       {Dca[i]:.3f}")
    print(f"\n zeta saturation: prime-sum {sat_true:.3f}; "
          f"lnln form {sat_llX:.3f}; measured plateau (l=16..32) "
          f"{np.mean(Dz[15:32]):.3f}")
    print(f" CUE at l=16..32: measured {np.mean(Dc[15:32]):.3f}; "
          f"analytic {np.mean(Dca[15:32]):.3f}")
    print(f" ratio zeta/CUE (16..32): measured "
          f"{np.mean(Dz[15:32])/np.mean(Dc[15:32]):.3f}; analytic "
          f"{np.mean(Dza[15:32])/np.mean(Dca[15:32]):.3f}")
