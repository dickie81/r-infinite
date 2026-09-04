#!/usr/bin/env python3
"""
Can Part II's complex structure J rescue the cascade's spectral rigidity?

Context: cascade_lattice_spectrum.py showed the cascade's native layer-chain
operator is a spectral crystal (mean gap ratio 0.993+), nowhere near the GUE
statistics of the Riemann zeros.  GUE requires broken time-reversal symmetry,
i.e. complex structure.  Part II supplies exactly one complex object: the
forced-precession complex structure J (part2 thm:complex, J^2 = -Id from two
quarter-turns), entering evolution as the scalar L(d) = i N(d)
(thm:discrete-schrodinger) with cumulative propagator phase i^(D-d).

Three questions, priors stated before computation:

  A. Does J-twisting the layer chain (hopping -w_d -> -i w_d) change its
     spectrum?  Prior: NO, exactly -- bond phases on a path graph are gauge-
     removable (no cycles => no flux).  This is a theorem; the computation
     is a check.
  B. Do the two possible axis-pairings of J (planes (12)(34).. vs (23)(45)..,
     the pairing offset the papers do not fix) generate a clean quaternionic
     structure (anticommuting J1, J2)?  Numerical check.
  C. The minimal object where J CAN act spectrally: the two-leg flux ladder
     -- legs = elastic chain (weights w_d = 1/(2 alpha(d))), rungs = lapse
     coupling N(d) carrying the cascade's own cumulative phase i^d, giving
     genuine flux pi/2 per plaquette (not gauge-removable).  Prior: still
     not GUE -- a deterministic quasi-1-D ladder is regular, not chaotic.

Verdict standard: mean adjacent-gap ratio <r~> against Poisson 0.3863 /
GOE 0.5307 / GUE 0.5996 / crystal ~1.0, with spacing CV as cross-check.
"""

import math

import numpy as np

D_MIN, D_MAX = 4, 217


def lnR(d):
    return math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0)


def alpha(d):
    return math.exp(2.0 * lnR(d)) / 4.0


def N_lapse(d):
    return math.sqrt(math.pi) * math.exp(lnR(d))


def gap_ratio(e):
    s = np.diff(np.sort(e))
    s = s[s > 1e-12]
    r = np.minimum(s[1:], s[:-1]) / np.maximum(s[1:], s[:-1])
    return float(np.mean(r))


def spacing_cv(e):
    s = np.diff(np.sort(e))
    s = s[s > 1e-12]
    k = 9
    loc = np.array([np.mean(s[max(0, i - k // 2):i + k // 2 + 1])
                    for i in range(len(s))])
    u = s / loc
    return float(np.std(u) / np.mean(u))


def chain(weights, phase=None):
    """Jacobi matrix; hopping -w_j, optionally with complex phases."""
    n = len(weights) + 1
    H = np.zeros((n, n), dtype=complex)
    for j, w in enumerate(weights):
        t = w * (phase[j] if phase is not None else 1.0)
        H[j, j] += w
        H[j + 1, j + 1] += w
        H[j, j + 1] = -np.conj(t)
        H[j + 1, j] = -t
    return H


def part_A():
    print("=" * 78)
    print("PART A: J-twisted layer chain (gauge-triviality check)")
    print("=" * 78)
    d = np.arange(D_MIN, D_MAX + 1)
    w = np.array([1.0 / (2.0 * alpha(int(x))) for x in d[:-1]])
    e_real = np.linalg.eigvalsh(chain(w))
    e_tw = np.linalg.eigvalsh(chain(w, phase=np.full(len(w), 1j)))
    print(f"  max |eigenvalue difference| real vs i-twisted:"
          f" {np.max(np.abs(e_real - e_tw)):.2e}")
    print("  => exactly isospectral: on a path graph the quarter-turn phase")
    print("     is a gauge transformation.  J alone cannot alter the layer")
    print("     chain's crystal spectrum.  (Prior confirmed; this is the")
    print("     discrete no-flux theorem, checked numerically.)")
    return e_real


def pairing_J(n_axes, offset):
    """Complex structure pairing axes (k,k+1) for k = offset, offset+2, ..."""
    J = np.zeros((n_axes, n_axes))
    k = offset
    while k + 1 < n_axes:
        J[k + 1, k] = 1.0
        J[k, k + 1] = -1.0
        k += 2
    return J


def part_B():
    print()
    print("=" * 78)
    print("PART B: the two axis-pairings of J (offset ambiguity)")
    print("=" * 78)
    n = 12
    J1, J2 = pairing_J(n, 0), pairing_J(n, 1)
    anti = J1 @ J2 + J2 @ J1
    comm = J1 @ J2 - J2 @ J1
    print(f"  n = {n} axes: ||{{J1,J2}}|| = {np.linalg.norm(anti):.3f},"
          f"  ||[J1,J2]|| = {np.linalg.norm(comm):.3f}")
    sh = J2 @ J1
    nz = sorted((i, j) for i in range(n) for j in range(n)
                if abs(sh[i, j]) > 0.5)
    print(f"  J2 J1 nonzeros (row,col): {nz[:8]} ...")
    print("  => neither commuting nor anticommuting (no clean quaternionic")
    print("     structure); J2 J1 acts as a signed two-step SHIFT along the")
    print("     axis chain -- a translation operator, interesting but not an")
    print("     un-gaugeable flux source by itself.")


def part_C():
    print()
    print("=" * 78)
    print("PART C: minimal J-dynamical operator -- the pi/2 flux ladder")
    print("=" * 78)
    print("  legs: elastic chain w_d = 1/(2 alpha(d)); rungs: lapse N(d)")
    print("  with the propagator's cumulative phase i^d  =>  flux pi/2 per")
    print("  plaquette (NOT gauge-removable; the ladder has cycles).")
    d = np.arange(D_MIN, D_MAX + 1)
    n = len(d)
    w = np.array([1.0 / (2.0 * alpha(int(x))) for x in d[:-1]])
    rung = np.array([N_lapse(int(x)) * (1j ** int(x)) for x in d])
    H = np.zeros((2 * n, 2 * n), dtype=complex)
    for leg in (0, 1):
        off = leg * n
        for j, wj in enumerate(w):
            H[off + j, off + j] += wj
            H[off + j + 1, off + j + 1] += wj
            H[off + j, off + j + 1] = -wj
            H[off + j + 1, off + j] = -wj
    for j, c in enumerate(rung):
        H[j, n + j] = c
        H[n + j, j] = np.conj(c)
    assert np.allclose(H, H.conj().T)
    e = np.linalg.eigvalsh(H)
    # flux check on first plaquette
    loop = (-w[0]) * rung[1] * (-w[0]) * np.conj(rung[0])
    print(f"  plaquette phase arg = {np.angle(loop)/math.pi:+.2f} pi"
          f"   (0 would mean gauge-trivial)")
    print(f"  spectrum: {len(e)} levels in [{e[0]:.2f}, {e[-1]:.2f}]")
    print(f"  <r~> = {gap_ratio(e):.4f}    CV(unfolded) = {spacing_cv(e):.4f}")
    lo, hi = np.percentile(e, [10, 90])
    bulk = e[(e > lo) & (e < hi)]
    print(f"  bulk only (10th-90th pct): <r~> = {gap_ratio(bulk):.4f}"
          f"    CV = {spacing_cv(bulk):.4f}")
    print("  reference: Poisson 0.3863 | GOE 0.5307 | GUE 0.5996 |"
          " crystal ~1.0")
    return e


if __name__ == "__main__":
    part_A()
    part_B()
    e = part_C()
    print()
    print("VERDICT")
    r = gap_ratio(e)
    if r > 0.75:
        v = "still crystalline -- J's flux does not break the rigidity"
    elif abs(r - 0.5996) < 0.02:
        v = "GUE-compatible (!!) -- would demand immediate follow-up"
    elif abs(r - 0.5307) < 0.02:
        v = "GOE-like -- time-reversal effectively unbroken"
    elif abs(r - 0.3863) < 0.03:
        v = "Poisson-like -- integrable, uncorrelated levels"
    else:
        v = "intermediate statistics -- regular, none of the RMT classes"
    print(f"  {v}")
