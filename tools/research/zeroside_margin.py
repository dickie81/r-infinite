#!/usr/bin/env python3
"""THE ZERO SIDE OF THE MARGIN CURVE -- a research probe (not a tower
member; not cited by the paper; float64, NOT a certificate).

THE IDENTITY. Weil's explicit formula applied to the autocorrelation
h = g * g~ of a real test function g supported on [-a, a] reads

    sum_rho G(rho) G(1 - rho)  =  (1/2pi) int |ghat(r)|^2 [Re psi(1/4 + ir/2) - log pi] dr
                                  - sum_{p^k} (2 log p / p^{k/2}) h(log p^k)  +/-  2 <chi, g>^2,

G(s) = int g(t) e^{(s - 1/2) t} dt, ghat(r) = G(1/2 + ir) = int g(t) e^{irt} dt,
chi = cosh(t/2) (even, +) / sinh(t/2) (odd, -).  The right side is the
paper's semi-local form Q(g) with every prime power inside the
window (log p^k < delta = 2a) -- the FULL functional on the window.
Under the Riemann Hypothesis every zero is rho = 1/2 + i gamma and the
left side is sum_gamma |ghat(gamma)|^2 >= 0.  Hence, under RH,

    lambda_1(delta) = min_{|g|_2 = 1, supp g in [-a, a]} sum_gamma |ghat(gamma)|^2,

the same number the prime-side pipeline (twoprime_margin.py) computes
from the archimedean kernel and the primes 2, 3 -- with NO prime and NO
window in sight: the zero side does not know where log 4 is.

WHAT THE PROBE COMPUTES (float64).  Per parity and delta, the ground
state of the Gram  G_ij = 2 sum_{n <= N} ghat_i(gamma_n) ghat_j(gamma_n)
in a 27/28-function basis on [-a, a] (integer and half-integer
cosines / sines; NOT mutually orthogonal, so the generalised eigen-
problem against the L^2 mass matrix, whitened), the sum over the
first N zeros (mpmath zetazero, cached in checkpoints/zeta_zeros_N.txt)
completed beyond gamma_N by the Riemann-von Mangoldt density integral
int_T^TMAX |ghat|^2 (1/2pi) log(x/2pi) dx and the edge asymptotic past
TMAX.  It reports, per cell: lambda_1, lambda_1 without the tail,
lambda_2, the zero-by-zero profile of the ground state's form (which
zeros carry it), the prime-side value from the committed margin
checkpoint where one exists, and finally a fit of the decay law
d log10 lambda_1 / d delta against e^delta.

WHAT IT IS NOT.  Not a proof of anything: the zero side is conditional
(the zeros used are the verified ones, the identity's positivity needs
all of them on the line), the tail is a density approximation, and
float64 sets a floor near 1e-14 relative (cells at or below it are
flagged by the tail share).  Checks 7/8 clean: Weil's explicit formula,
Paley-Wiener, IEEE-754 -- classical; no hypothesis input; Riemann-side
pure mathematics.  No RH consequence is claimed.

Usage: python3 zeroside_margin.py [N_zeros=3000] [K=13] [deltas...]
"""
import sys, os, math, json, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CK = os.path.join(HERE, "checkpoints")
TMAX = 5.0e4
DX = 0.25


def zeros(N):
    """The first N ordinates of the zeta zeros (mpmath), cached."""
    fn = os.path.join(CK, f"zeta_zeros_{N}.txt")
    if os.path.exists(fn):
        g = np.array([float(l.split()[1]) for l in open(fn) if l.strip()])
        if len(g) == N:
            return g
    import mpmath as mp
    mp.mp.dps = 20
    t0 = time.time()
    with open(fn, "w") as f:
        for n in range(1, N + 1):
            f.write("%d %.16f\n" % (n, float(mp.zetazero(n).imag)))
            if n % 200 == 0:
                f.flush(); print(f"  zeros {n}/{N} {time.time()-t0:.0f}s", flush=True)
    return zeros(N)


def basis(a, parity, K):
    fs = []
    if parity == "even":
        fs.append((0.0, "cos", 1/math.sqrt(2*a)))
        for k in range(1, K+1):
            fs.append((k*math.pi/a, "cos", 1/math.sqrt(a)))
            fs.append(((k-0.5)*math.pi/a, "cos", 1/math.sqrt(a)))
    else:
        for k in range(1, K+1):
            fs.append((k*math.pi/a, "sin", 1/math.sqrt(a)))
            fs.append(((k-0.5)*math.pi/a, "sin", 1/math.sqrt(a)))
    return fs


def _sinc_a(y, a):
    y = np.asarray(y, float)
    small = np.abs(y) < 1e-12
    return np.where(small, a, np.sin(y*a)/np.where(small, 1.0, y))


def fhat(f, a, x):
    """int_{-a}^{a} f(t) cos(xt) dt (cos family) or int f(t) sin(xt) dt (sin
    family): the real amplitude whose square is |ghat(x)|^2."""
    w, kind, c = f
    x = np.asarray(x, float)
    if kind == "cos":
        return c*(_sinc_a(x - w, a) + _sinc_a(x + w, a))
    return c*(_sinc_a(x - w, a) - _sinc_a(x + w, a))


def edge(f, a):
    w, kind, c = f
    return c*(math.cos(w*a) if kind == "cos" else math.sin(w*a))


def mass(fs, a):
    m = len(fs); M = np.zeros((m, m))
    for i, (wi, ki, ci) in enumerate(fs):
        for j, (wj, kj, cj) in enumerate(fs):
            if ki == kj:
                M[i, j] = ci*cj*fhat((wj, kj, 1.0), a, np.array([wi]))[0]
    return M


def whiten(M, cut=1e-10):
    e, U = np.linalg.eigh(M)
    keep = e > cut*e.max()
    return U[:, keep]/np.sqrt(e[keep])


def cell(gam, a, parity, K):
    N = len(gam); T = gam[-1]
    fs = basis(a, parity, K)
    V = np.array([fhat(f, a, gam) for f in fs])
    G = 2*V @ V.T
    x = np.arange(T, TMAX, DX)
    dens = np.log(x/(2*math.pi))/(2*math.pi)
    W = np.array([fhat(f, a, x) for f in fs])
    Gt = 2*(W*dens) @ W.T*DX
    e = np.array([edge(f, a) for f in fs])
    far = np.outer(e, e)*4*(math.log(TMAX/(2*math.pi)) + 1)/(2*math.pi*TMAX)
    P = whiten(mass(fs, a))
    w, v = np.linalg.eigh(P.T @ (G + Gt + far) @ P)
    w0, _ = np.linalg.eigh(P.T @ G @ P)
    g = P @ v[:, 0]
    per = 2*(g @ V)**2
    return dict(lambda1=w[0], lambda1_notail=w0[0], lambda2=w[1], per=per,
                tail_share=(w[0] - per.sum())/w[0])


def prime_side():
    """The committed margin-curve checkpoint (twoprime_margin.py), the
    right regime per delta."""
    out = {}
    for fn in os.listdir(CK):
        if fn.startswith("twoprime_margin_") and "partial" not in fn:
            st = json.load(open(os.path.join(CK, fn)))["state"]
            for k, v in st.items():
                reg, par, d = k.split(":"); d = float(d)
                ok = ((reg == "arch" and d < math.log(2)) or
                      (reg == "one" and math.log(2) <= d < math.log(3)) or
                      (reg == "two" and d >= math.log(3)))
                if ok:
                    out[(par, round(d, 4))] = v["lambda1"]
    return out


def prolate0(c, M=400):
    """Slepian's most-concentrated function psi_0 for bandwidth-interval
    product c on [-1, 1] (Nystrom on the sinc kernel at M Gauss-Legendre
    nodes): nodes, weights, psi_0 at the nodes, the eigenvalue lambda_0(c)."""
    x, w = np.polynomial.legendre.leggauss(M)
    D = x[:, None] - x[None, :]
    K = np.where(np.abs(D) < 1e-14, c/math.pi,
                 np.sin(c*D)/(math.pi*np.where(np.abs(D) < 1e-14, 1.0, D)))
    A = np.sqrt(w)[:, None]*K*np.sqrt(w)[None, :]
    e, U = np.linalg.eigh(A)
    return x, w, U[:, -1]/np.sqrt(w), e[-1]


def prolate_extend(c, T, xg, wg, psi, lam0, xs):
    Dm = xs[:, None]/T - xg[None, :]
    Kx = np.where(np.abs(Dm) < 1e-14, c/math.pi,
                  np.sin(c*Dm)/(math.pi*np.where(np.abs(Dm) < 1e-14, 1.0, Dm)))
    return (Kx*wg[None, :]) @ psi/lam0


def ground_state(gam, a, parity, K):
    """The zero-side ground state's coefficient vector and basis."""
    fs = basis(a, parity, K); N = len(gam); T = gam[-1]
    V = np.array([fhat(f, a, gam) for f in fs]); G = 2*V @ V.T
    x = np.arange(T, TMAX, DX); dens = np.log(x/(2*math.pi))/(2*math.pi)
    W = np.array([fhat(f, a, x) for f in fs]); Gt = 2*(W*dens) @ W.T*DX
    e = np.array([edge(f, a) for f in fs])
    far = np.outer(e, e)*4*(math.log(TMAX/(2*math.pi)) + 1)/(2*math.pi*TMAX)
    P = whiten(mass(fs, a)); w, v = np.linalg.eigh(P.T @ (G + Gt + far) @ P)
    return P @ v[:, 0], fs


def prolate_test(gam, deltas, K=13, parity="even"):
    """THE MECHANISM TEST (A421). For each delta: the overlap of the ground
    state's ghat with Slepian's psi_0 on [-T0, T0], T0 = 2 pi e^delta (the
    Beurling sampling threshold for exponential type a = delta/2: above it
    the zeros are denser than a/pi), its mass inside, its real zeros below
    T0 against the zeta zeros below T0, and the best-fit prolate interval
    T_eff (scanned over [0.6, 1.6] T0) with its overlap."""
    tr = np.trapezoid
    print(f"prolate test ({parity}): T0 = 2 pi e^delta; c = a T0")
    for d in deltas:
        a = d/2; T0 = 2*math.pi*math.exp(d); c = a*T0
        g, fs = ground_state(gam, a, parity, K)
        xs = np.linspace(-T0, T0, 4001); gh = g @ np.array([fhat(f, a, xs) for f in fs])
        xg, wg, psi, lam0 = prolate0(c); px = prolate_extend(c, T0, xg, wg, psi, lam0, xs)
        ov = abs(tr(gh*px, xs))/math.sqrt(tr(gh**2, xs)*tr(px**2, xs))
        inside = tr(gh**2, xs)/(2*math.pi)
        pos = xs > 0; s = np.sign(gh[pos]); zc = xs[pos][:-1][np.diff(s) != 0]
        best = (0.0, 0.0)
        for Tf in np.linspace(0.6*T0, 1.6*T0, 21):
            cc = a*Tf; xg2, wg2, psi2, l2 = prolate0(cc)
            xs2 = np.linspace(-Tf, Tf, 2001); gh2 = g @ np.array([fhat(f, a, xs2) for f in fs])
            p2 = prolate_extend(cc, Tf, xg2, wg2, psi2, l2, xs2)
            o = abs(tr(gh2*p2, xs2))/math.sqrt(tr(gh2**2, xs2)*tr(p2**2, xs2))
            if o > best[0]:
                best = (o, Tf)
        print(f"  delta {d:5.3f}: T0 {T0:5.1f} c {c:5.2f}; overlap with psi0 on [-T0,T0] {ov:.4f}; "
              f"mass inside {inside:.4f}; ghat zeros in (0,T0) {np.round(zc, 1)} vs zeta {np.round(gam[gam < T0], 1)}; "
              f"T_eff {best[1]:.1f} = {best[1]/T0:.2f} T0 (overlap {best[0]:.4f})", flush=True)


if __name__ == "__main__" and "--prolate" in sys.argv:
    sys.argv.remove("--prolate")
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    deltas = [float(s) for s in sys.argv[2:]] or [0.8, 1.0, 1.2, 1.386, 1.5]
    prolate_test(zeros(N), deltas)
    sys.exit(0)

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 13
    deltas = [float(s) for s in sys.argv[3:]] or \
        [0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.3, 1.386, 1.5, 1.6]
    gam = zeros(N)
    ps = prime_side()
    print(f"zero side: N = {N} zeros to gamma_N = {gam[-1]:.2f}; tail density to {TMAX:.0e}; basis K = {K}")
    print(f"{'delta':>6} {'par':>4} {'lambda1 (zeros)':>16} {'lambda1 (primes)':>17} {'ratio':>7} {'lambda2':>10} {'50%@#':>6} {'90%@#':>6} {'tail':>6}")
    curves = {"even": [], "odd": []}
    for d in deltas:
        for par in ("even", "odd"):
            r = cell(gam, d/2, par, K)
            cs = np.cumsum(r["per"])/r["lambda1"]
            i50 = min(int(np.searchsorted(cs, 0.5)), N-1) + 1
            i90 = min(int(np.searchsorted(cs, 0.9)), N-1) + 1
            p = ps.get((par, round(d, 4)))
            ratio = r["lambda1"]/p if p else float("nan")
            flag = "" if 0 < r["tail_share"] < 0.1 else "  (float floor)"
            print(f"{d:6.3f} {par:>4} {r['lambda1']:16.4e} {(p if p else float('nan')):17.4e} {ratio:7.3f} "
                  f"{r['lambda2']:10.3e} {i50:6d} {i90:6d} {r['tail_share']:6.3f}{flag}", flush=True)
            if 0 < r["tail_share"] < 0.1 and r["lambda1"] > 1e-14:
                curves[par].append((d, math.log10(r["lambda1"])))
    # the decay law: d log10 lambda1 / d delta against e^delta
    print("\ndecay law: slope s(delta) = -d log10 lambda1 / d delta between successive cells, and s / e^delta")
    for par in ("even", "odd"):
        pts = curves[par]
        ratios = []
        for (d0, l0), (d1, l1) in zip(pts, pts[1:]):
            dm = 0.5*(d0 + d1); s = -(l1 - l0)/(d1 - d0)
            ratios.append(s/math.exp(dm))
            print(f"  {par:>4} delta {dm:5.3f}: s = {s:5.2f} decades/unit, s/e^delta = {s/math.exp(dm):5.2f}")
        if len(ratios) >= 3:
            print(f"  {par:>4} s/e^delta over the last three intervals: mean {np.mean(ratios[-3:]):.2f}, "
                  f"over all: {np.mean(ratios):.2f} +/- {np.std(ratios):.2f}")
