#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE B1, ROUND 3 -- rough- and
fractional-edge trials with analytic tail closure: the even-sector
unlock attempt, and the adjudication of round 2's odd numbers.

Commission: "1 pls" (the first next move at the round-2 landing:
the identified even-sector unlock -- fractional edge exponents,
which uniform grids provably cannot carry).

THE EDGE DISCOVERY THAT RESHAPED THE ROUND (caught by this
instrument's own tail analysis before any number landed): the odd
half-integer sines sin((m + 1/2) pi t/a) DO NOT VANISH at the
support edges -- they are s = 0 rough-edge modes with r^-1
transform decay. Two consequences. (a) Round 2's truncation
discipline estimated the odd sector's S-errors with the
linear-edge template (r^-2 tails, error ~ w^2 log^2 R/R^3); for
s = 0 modes the true error scale is ~log^2(R)/R -- orders larger
-- so the round-2 odd closures (0.90 robust, 1.05 semi-robust)
are SUSPECT until re-adjudicated here, where the tails are closed
analytically. The old-span calibration column of this instrument
performs that adjudication. (b) The even union has never
contained its s = 0 directions at all (the half-integer cosines
all vanish at the edges): the integer-cosine family
cos(m pi t/a), m = 0..16, is added here as the even sector's
rough-edge family -- by the S4/S5/push roughness trend, a prime
suspect for the missing even residual.

THE TRIAL FAMILIES.
  old (even):   cos((m + 1/2) pi t/a), m = 0..32 (the round-2
                span: the window-recombination identity collapses
                fam1 + p = 1 windowed onto exactly these);
  old (odd):    sin((m + 1) pi t/a), m = 0..23, union
                sin((m + 1/2) pi t/a), m = 0..31 (the round-2
                span; contains s = 0 modes -- see above);
  rough (even): cos(m pi t/a), m = 0..16 (s = 0, new);
  fractional:   G_n(t) = (1 - (t/a)^2)^s C_n^{(nu)}(t/a),
                s = nu - 1/2, nu in {0.75, 1.0} (s = 0.25, 0.5),
                n even 0..14 / odd 1..15 per parity, whose
                transforms are EXACTLY Bessel:
                q_n(r) = c_n J_{nu+n}(ra)/(ra)^nu (the classical
                Gegenbauer-Bessel identity; c_n determined
                numerically at one reference r and the identity
                verified at independent r -- gate gF4).

THE SEMI-ANALYTIC SCHEME. Every needed matrix is a pure
one-dimensional integral:
  N_ij = (1/2pi) int q_i q_j dr                    (Plancherel),
  M_ij = (1/2pi) int W q_i q_j dr + ps 2 v_i v_j,
  S_ij = (1/2pi) int W^2 q_i q_j dr  -  Out_ij
         + ps 2 (v_j <X_i, chi>_a + v_i <X_j, chi>_a)
         + 4 v_i v_j ||chi||_a^2,
with r-integrals = main [0, 12000] at dr 0.05 (exact scipy jv /
closed sinc forms) + far [12000, 1e6] at dr 0.5 (Bessel
amplitude-phase asymptotics; sinc closed forms) + THE ANALYTIC DC
CLOSURE on [1e6, oo): every mode carries an asymptotic template
q_i(r) ~ amp_i cos(ra - phi_i)/r^{pw_i} (pw = 1 for s = 0 modes,
2 for the vanishing-edge harmonics, nu + 1/2 for Gegenbauer), so
each pair's tail has DC coefficient D_ij = amp_i amp_j
cos(phi_i - phi_j)/2 against the closed-form log-moments
  T0(p) = R^{1-p}/(p-1),  T1 = R^{-s}(L/s + 1/s^2),
  T2 = R^{-s}(L^2/s + 2L/s^2 + 2/s^3)   [s = p-1, L = log(R/2pi)]
(W's DC is log(r/2pi); W^2's DC is log^2 + C2^2/2; the h_+
curvature corrections are O(r^-2) down). The NEGLECTED oscillatory
parts integrate by parts to O(log^2(R)/(2a R^p)) -- at R = 1e6
that is < 1e-9 in normalized units for every pair, asserted (gFT).
The coarse grids are spectrally accurate (all integrands are
transforms of functions supported in |u| < 3; dr = 0.5 aliases
only content beyond 2pi/0.5 = 12.6, where the arch kernel's
e^{-u} tail is ~1e-5 of an already-small component).
  Out_ij = int_{|t|>a} X_i X_j dt (the projection correction to
S): outside the support X = X_arch + X_prime is EXPLICIT --
X_prime(t) = -(C2/2)[G(t - log 2) + G(t + log 2)] (closed form,
support < a + log 2, with a quadrature breakpoint at t = a + log2
where it jumps for s = 0 modes) and X_arch(t) =
-int e^{u/2} G(t-u)/(2 sinh u) du over u in (t-a, t+a) (the arch
operator's sinh-kernel form -- the identity the bridge gated at
1e-5), by log-substituted Gauss-Legendre; for s = 0 modes X_arch
has an integrable log singularity at t = a+, so the first outside
segment is log-substituted in t as well. <X_i, chi>_a needs no
pointwise X inside: it is (1/2pi) int W q_i vchi dr with vchi the
closed-form transform of restricted chi (template-closed tail).

GATES. gF4: the Gegenbauer-Bessel identity at independent r (rel
< 1e-8). gF1: the M sub-block on the 24 certified fam1 modes vs
build_Q64's Q (rel Frobenius < 5e-4, the certified instrument's
own truncation class). gFT: the oscillatory tail-closure
remainder < 1e-9 normalized. Printed: whitened dims, the
old-span-only Temple column (the run-3 calibration AND the odd
adjudication), the fractional/rough weight of the optimum.

CHECKS. 7: classical (Bessel asymptotics, spectral bounds). 8: no
hypothesis input.

Keying law: every producing file in every key.
"""
import hashlib, math, os, sys

import numpy as np
from scipy.linalg import eigh as scipy_eigh
from scipy.special import jv, roots_jacobi, eval_gegenbauer

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_bridge import build_Q64
from oneprime_certificate import Wker, psign
from oneprime_push import temple_opt

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSF = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "oneprime_bridge.py",
                              "oneprime_certificate.py",
                              "oneprime_push.py",
                              "oneprime_fractional.py")}
KEYFILE = os.path.join(HERE, "oneprime_fractional.py")

LOG2 = math.log(2.0)
C2 = math.sqrt(2.0)*LOG2
TWO_PI = 2*math.pi
NUS = (0.75, 1.0)
NFR = 8
NROUGH = 17
RMAIN, DRM = 12000.0, 0.05
RFAR, DRF = 1.0e6, 0.5

# ------------------------------------------------ grids and kernel
def main_grid():
    r = np.arange(0.0, RMAIN + DRM/2, DRM)
    w = np.full(len(r), DRM)
    w[0] = w[-1] = DRM/2
    r[0] = 1e-9
    return r, w

def far_chunks():
    edges = np.linspace(RMAIN, RFAR, 9)
    for lo, hi in zip(edges[:-1], edges[1:]):
        r = np.arange(lo, hi, DRF)
        w = np.full(len(r), DRF)
        w[0] = DRF/2
        yield r, w

def bessel_asym(order, x):
    mu = 4.0*order*order
    om = x - order*np.pi/2 - np.pi/4
    P = 1.0 - (mu - 1)*(mu - 9)/(2*(8*x)**2)
    Q = (mu - 1)/(8*x)
    return np.sqrt(2.0/(np.pi*x))*(np.cos(om)*P - np.sin(om)*Q)

def vchi(r, a, parity):
    y = 0.5
    if parity == "even":
        return 2*(y*np.cos(r*a)*math.sinh(y*a)
                  + r*np.sin(r*a)*math.cosh(y*a))/(r*r + y*y)
    return 2*(y*np.sin(r*a)*math.cosh(y*a)
              - r*np.cos(r*a)*math.sinh(y*a))/(r*r + y*y)

def tail_T(p, R=RFAR):
    s = p - 1.0
    L = math.log(R/TWO_PI)
    T0 = R**(-s)/s
    T1 = R**(-s)*(L/s + 1/s**2)
    T2 = R**(-s)*(L**2/s + 2*L/s**2 + 2/s**3)
    return T0, T1, T2

# ------------------------------------------------ the mode catalog
class Modes:
    """Raw union with per-mode asymptotic templates
    (amp, phi, pw): q(r) ~ amp cos(ra - phi)/r^pw."""
    def __init__(self, a, parity):
        self.a, self.parity = a, parity
        self.kind, self.w = [], []
        if parity == "even":
            for m in range(33):
                self.kind.append("harm"); self.w.append((m + 0.5)*np.pi/a)
            for m in range(NROUGH):
                self.kind.append("harm"); self.w.append(m*np.pi/a)
        else:
            ws = sorted(list((np.arange(24) + 1.0)*np.pi/a)
                        + list((np.arange(32) + 0.5)*np.pi/a))
            for w in ws:
                self.kind.append("harm"); self.w.append(w)
        self.nharm = len(self.w)
        self.frac = []
        ns = (np.arange(NFR)*2 if parity == "even"
              else np.arange(NFR)*2 + 1)
        for nu in NUS:
            s = nu - 0.5
            xj, wj = roots_jacobi(220, s, s)
            for n in ns:
                cn, devs = self._calibrate(nu, n, xj, wj)
                self.frac.append({"nu": nu, "n": int(n), "cn": cn,
                                  "xj": xj, "wj": wj, "gF4": devs})
        self.n = self.nharm + len(self.frac)
        self.amp, self.phi, self.pw = self._templates()

    def _templates(self):
        a = self.a
        amp, phi, pw = [], [], []
        for w in self.w:
            sw, cw = math.sin(w*a), math.cos(w*a)
            if self.parity == "even":
                if abs(sw) > 0.5:      # half-integer: vanishing edge
                    amp.append(-2*w*sw); phi.append(0.0); pw.append(2.0)
                else:                  # integer: s = 0 edge
                    amp.append(2*cw); phi.append(np.pi/2); pw.append(1.0)
            else:
                if abs(sw) > 0.5:      # half-integer sine: s = 0
                    amp.append(-2*sw); phi.append(0.0); pw.append(1.0)
                else:                  # integer sine: vanishing edge
                    amp.append(2*w*cw); phi.append(np.pi/2); pw.append(2.0)
        for fr in self.frac:
            nu, n, cn = fr["nu"], fr["n"], fr["cn"]
            amp.append(cn*math.sqrt(2/(np.pi*a))*a**(-nu))
            phi.append((nu + n)*np.pi/2 + np.pi/4)
            pw.append(nu + 0.5)
        return np.array(amp), np.array(phi), np.array(pw)

    def _quad_q(self, nu, n, r, xj, wj):
        f = np.cos if self.parity == "even" else np.sin
        return self.a*np.sum(
            wj*eval_gegenbauer(n, nu, xj)*f(r*self.a*xj))

    def _calibrate(self, nu, n, xj, wj):
        # calibration and verification points sit ABOVE the Bessel
        # turning point x ~ nu + n (below it J is exponentially
        # small and the constant would amplify quadrature noise)
        for xref in (nu + n + 6.0, nu + n + 7.3, nu + n + 8.1):
            den = jv(nu + n, xref)/xref**nu
            if abs(den) > 1e-3:
                break
        cn = self._quad_q(nu, n, xref/self.a, xj, wj)/den
        devs = []
        for xv in (nu + n + 9.7, nu + n + 15.3):
            qq = self._quad_q(nu, n, xv/self.a, xj, wj)
            qf = cn*jv(nu + n, xv)/xv**nu
            devs.append(abs(qq - qf)/max(abs(qq), 1e-300))
        return cn, devs

    def q_on(self, r, far=False):
        a = self.a
        out = np.empty((self.n, len(r)))
        s = lambda x: np.sinc(x/np.pi)
        sgn = 1.0 if self.parity == "even" else -1.0
        for i, w in enumerate(self.w):
            out[i] = a*(s((r - w)*a) + sgn*s((r + w)*a))
        for j, fr in enumerate(self.frac):
            nu, n, cn = fr["nu"], fr["n"], fr["cn"]
            x = r*a
            J = bessel_asym(nu + n, x) if far else jv(nu + n, x)
            out[self.nharm + j] = cn*J/x**nu
        return out

    def t_eval(self, t):
        a = self.a
        out = np.zeros((self.n, len(t)))
        inside = np.abs(t) <= a
        ti = t[inside]
        f = np.cos if self.parity == "even" else np.sin
        for i, w in enumerate(self.w):
            out[i, inside] = f(w*ti)
        x = ti/a
        wt = np.clip(1.0 - x*x, 0.0, None)
        for j, fr in enumerate(self.frac):
            out[self.nharm + j, inside] = (
                wt**(fr["nu"] - 0.5)*eval_gegenbauer(fr["n"],
                                                     fr["nu"], x))
        return out

    def pole_v(self):
        a = self.a
        v = np.empty(self.n)
        v[:self.nharm] = vchi(np.array(self.w), a, self.parity)
        f = np.cosh if self.parity == "even" else np.sinh
        for j, fr in enumerate(self.frac):
            v[self.nharm + j] = a*np.sum(
                fr["wj"]*eval_gegenbauer(fr["n"], fr["nu"],
                                         fr["xj"])*f(a*fr["xj"]/2))
        return v

# ------------------------------------------- the outside integral
def outside_nodes(a):
    x, w = np.polynomial.legendre.leggauss(64)
    ts, ws = [], []
    # first segment log-substituted in (t - a): the s = 0 modes'
    # X_arch has an integrable log singularity at the edge
    lo, hi = math.log(1e-10), math.log(0.4)
    v = 0.5*(hi - lo)*x + 0.5*(hi + lo)
    ts.append(a + np.exp(v))
    ws.append(0.5*(hi - lo)*w*np.exp(v))
    for lo, hi in ((a + 0.4, a + LOG2), (a + LOG2, a + 1.5),
                   (a + 1.5, a + 5.0), (a + 5.0, a + 15.0),
                   (a + 15.0, a + 42.0)):
        ts.append(0.5*(hi - lo)*x + 0.5*(hi + lo))
        ws.append(0.5*(hi - lo)*w)
    return np.concatenate(ts), np.concatenate(ws)

def X_outside(md, tout):
    a = md.a
    xg, wg = np.polynomial.legendre.leggauss(128)
    X = np.zeros((md.n, len(tout)))
    for k, t in enumerate(tout):
        lo, hi = math.log(max(t - a, 1e-14)), math.log(t + a)
        v = 0.5*(hi - lo)*xg + 0.5*(hi + lo)
        u = np.exp(v)
        wu = 0.5*(hi - lo)*wg*u
        ker = np.exp(u/2)/(2*np.sinh(u))
        Gv = md.t_eval(t - u)
        X[:, k] = -(Gv*(wu*ker)[None, :]).sum(axis=1)
    X += -(C2/2)*(md.t_eval(tout - LOG2) + md.t_eval(tout + LOG2))
    return X

# ------------------------------------------------------- assembly
def cell_matrices(a, parity):
    md = Modes(a, parity)
    gf4 = max(max(fr["gF4"]) for fr in md.frac)
    r, wr = main_grid()
    W = Wker(r)
    Q = md.q_on(r)
    vc = vchi(r, a, parity)
    N = (Q*wr[None, :]) @ Q.T
    M = (Q*(W*wr)[None, :]) @ Q.T
    S = (Q*(W*W*wr)[None, :]) @ Q.T
    Sx = Q @ (W*vc*wr)
    for rf, wf in far_chunks():
        Wf = Wker(rf)
        Qf = md.q_on(rf, far=True)
        N += (Qf*wf[None, :]) @ Qf.T
        M += (Qf*(Wf*wf)[None, :]) @ Qf.T
        S += (Qf*(Wf*Wf*wf)[None, :]) @ Qf.T
        Sx += Qf @ (Wf*vchi(rf, a, parity)*wf)
    # the analytic DC closure on [RFAR, oo)
    D = 0.5*np.outer(md.amp, md.amp)*np.cos(
        md.phi[:, None] - md.phi[None, :])
    P = md.pw[:, None] + md.pw[None, :]
    T0 = np.empty_like(P); T1 = np.empty_like(P); T2 = np.empty_like(P)
    for p in np.unique(P):
        t0, t1, t2 = tail_T(float(p))
        T0[P == p] = t0; T1[P == p] = t1; T2[P == p] = t2
    N += D*T0
    M += D*T1
    S += D*(T2 + 0.5*C2*C2*T0)
    if parity == "even":
        ampx, phix = 2*math.cosh(a/2), np.pi/2
    else:
        ampx, phix = -2*math.sinh(a/2), 0.0
    Dx = 0.5*md.amp*ampx*np.cos(md.phi - phix)
    for i in range(md.n):
        _, t1x, _ = tail_T(float(md.pw[i] + 1.0))
        Sx[i] += Dx[i]*t1x
    # gFT: the neglected oscillatory remainder, normalized
    dn = 1.0/np.sqrt(np.diag(N))
    L2R = math.log(RFAR/TWO_PI)**2 + 0.5*C2*C2
    osc = (0.5*np.abs(np.outer(md.amp, md.amp))*L2R
           / (2*a*RFAR**P))*np.outer(dn, dn)
    gft = float(np.max(osc))/np.pi
    assert gft < 1e-9, f"gFT FAIL: osc remainder {gft:.1e}"
    N *= 2/TWO_PI; M *= 2/TWO_PI; S *= 2/TWO_PI; Sx *= 2/TWO_PI
    ps = psign(parity)
    v = md.pole_v()
    M += ps*2*np.outer(v, v)
    tout, wout = outside_nodes(a)
    X = X_outside(md, tout)
    Out = 2*(X*wout[None, :]) @ X.T
    chin2 = (math.sinh(a) + a if parity == "even"
             else math.sinh(a) - a)
    S = (S - Out + ps*2*(np.outer(v, Sx) + np.outer(Sx, v))
         + 4*chin2*np.outer(v, v))
    N, M, S = (N + N.T)/2, (M + M.T)/2, (S + S.T)/2
    return md, N, M, S, gf4, gft

def ladder(N, M, S, l2sec, l2c):
    out = {}
    for tag, ell2 in (("l2sec", l2sec), ("l2cos24", l2c),
                      ("half", 0.5*l2sec)):
        mu, c = temple_opt(N, M, S, ell2)
        if c is not None:
            nn = float(c @ N @ c)
            rho = float(c @ M @ c)/nn
            sig = math.sqrt(max(float(c @ S @ c)/nn - rho*rho, 0.0))
        else:
            rho = sig = float("nan")
        out[tag] = {"ell2": ell2, "temple": mu, "rho": rho,
                    "sigma": sig, "_c": c}
    return out


def run():
    params = {"deps": DEPSF, "nus": NUS, "nfr": NFR,
              "nrough": NROUGH, "rmain": RMAIN, "rfar": RFAR}
    st = ckpt_key.load("oneprime_frac", KEYFILE, params)
    if st is not None:
        return st
    st = {}
    cells = [("even", 0.6931), ("even", 0.80), ("even", 0.85),
             ("even", 0.90), ("even", 0.95), ("even", 1.00),
             ("even", 1.05), ("even", 1.09),
             ("odd", 0.90), ("odd", 1.05), ("odd", 1.09)]
    for parity, delta in cells:
        a = delta/2
        md, N, M, S, gf4, gft = cell_matrices(a, parity)
        assert gf4 < 1e-8, f"gF4 FAIL {parity}:{delta:g}: {gf4:.1e}"
        Qc, Gc, _, _, _ = build_Q64(delta, parity=parity)
        if parity == "even":
            idx = np.arange(24)
        else:
            wcert = (np.arange(24) + 1.0)*np.pi/a
            idx = np.array([int(np.argmin(np.abs(
                np.array(md.w) - w))) for w in wcert])
        gf1 = float(np.linalg.norm(M[np.ix_(idx, idx)] - Qc)
                    / np.linalg.norm(Qc))
        assert gf1 < 5e-4, f"gF1 FAIL {parity}:{delta:g}: {gf1:.1e}"
        l2c = float(scipy_eigh(Qc, Gc, eigvals_only=True)[1])

        # old-only sub-span (the round-2 span): even = the 33
        # half-integer modes; odd = the whole harmonic set
        nold_sub = 33 if parity == "even" else md.nharm

        def white(sub):
            Ns = N[np.ix_(sub, sub)]
            d = 1.0/np.sqrt(np.diag(Ns))
            Nn = d[:, None]*Ns*d[None, :]
            ev, U = np.linalg.eigh(Nn)
            keep = ev > 1e-10
            Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T
                  * d[None, :])
            Nw = Wh @ Ns @ Wh.T
            Mw = Wh @ M[np.ix_(sub, sub)] @ Wh.T
            Sw = Wh @ S[np.ix_(sub, sub)] @ Wh.T
            return (Wh, (Nw + Nw.T)/2, (Mw + Mw.T)/2,
                    (Sw + Sw.T)/2)
        WhA, NA, MA, SA = white(np.arange(md.n))
        WhO, NO, MO, SO = white(np.arange(nold_sub))
        l2A = float(scipy_eigh(MA, NA, eigvals_only=True)[1])
        l2O = float(scipy_eigh(MO, NO, eigvals_only=True)[1])
        LA = ladder(NA, MA, SA, l2A, l2c)
        LO = ladder(NO, MO, SO, l2O, l2c)
        c = LA["l2sec"]["_c"]
        if c is not None:
            craw = WhA.T @ c
            nn = np.sum(craw**2)
            fw = float(np.sum(craw[nold_sub:]**2)/nn)
        else:
            fw = float("nan")
        for L in (LA, LO):
            for k in L:
                L[k].pop("_c")
        st[f"{parity}:{delta:g}"] = {
            "dimA": NA.shape[0], "dimO": NO.shape[0], "gF1": gf1,
            "gF4": gf4, "gFT": gft, "l2c": l2c, "union": LA,
            "old": LO, "new_weight": fw}
        print(f"FRAC {parity} delta {delta:g} (dimA {NA.shape[0]} "
              f"dimO {NO.shape[0]} gF1 {gf1:.1e} gFT {gft:.1e}): "
              f"old Temple {LO['l2sec']['temple']:+.3e} (sig "
              f"{LO['l2sec']['sigma']:.3e}) | union Temple "
              f"{LA['l2sec']['temple']:+.3e} (rho "
              f"{LA['l2sec']['rho']:+.3e} sig "
              f"{LA['l2sec']['sigma']:.3e} nw {fw:.3f}) l2cos24 "
              f"{LA['l2cos24']['temple']:+.3e} half "
              f"{LA['half']['temple']:+.3e}", flush=True)
    ckpt_key.save("oneprime_frac", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("one-prime rough/fractional-edge round complete", flush=True)
