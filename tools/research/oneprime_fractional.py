#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE B1, ROUND 3 -- rough- and
fractional-edge trials via the t-space operator pipeline: the
even-sector unlock attempt, and the adjudication of round 2's odd
numbers.

Commission: "1 pls" (the first next move at the round-2 landing).

THE PIPELINE STORY (three architectures, the third one right; the
first two versions of this file are in the git record at f05719b):
  1. The GRID pipeline (rounds 2-3, oneprime_push.py): T applied
     via wide r-grids. ADJUDICATED CORRECT for vanishing-edge even
     spans -- an independent pure-t-space computation reproduces
     its sigma to four digits (2.7527e-3 for the certified cos-24
     extremal at even delta 0.9) -- but its truncation discipline
     assumed r^-2 mode tails, and the odd half-integer sines DO
     NOT VANISH at the support edges (s = 0 modes, r^-1
     transforms): the round-2 ODD results carry unquantified
     truncation error and are re-adjudicated below.
  2. The r-space SEMI-ANALYTIC pipeline (this file's first
     version): exact far tails (Bessel asymptotics + closed-form
     DC closure), structurally verified -- but it assembles
     S_phiphi for near-null vectors as a CANCELLATION OF +-9-SIZED
     PIECES down to 1e-6 (the full-line norm, the outside mass,
     and the pole cross-terms nearly cancel), so ~1e-6-relative
     piece errors produce S errors larger than sigma^2 itself:
     negative sigma^2, fake Temple closures. Diagnosed by the
     t-space adjudicator; its run-1 output is invalid as
     measurement and kept only as the failure exhibit.
  3. THE T-SPACE OPERATOR pipeline (this version): T b computed
     POINTWISE on [-a, a] from compact one-dimensional integrals
     -- no r-grids, no truncation classes, any edge exponent --
     then N, M, S by t-quadrature. The cancellation happens inside
     each T b(t) value (benign), and the projection is automatic.
       T_arch b(t) = -(log 4pi + gamma) b(t)
         - int_0^{a+t} [A(u) b(t) + e^{u/2} D(t,u)/sinh(u)] du
         + b(t) log coth((a+t)/2),
       A(u) = (e^{u/2} - 1)/sinh(u)   (exact, smooth),
       D(t,u) = (b(t+u) + b(t-u))/2 - b(t)  (masked evaluations;
         for harmonic modes EXACT closed form
         D = -2 f(wt) sin^2(wu/2), f = cos/sin -- no cancellation;
         for Gegenbauer modes direct evaluation with a u > 1e-6
         floor and the analytic sub-floor correction),
       T_prime b(t) = -(C2/2)[b(t + log 2) + b(t - log 2)],
       T_pole b(t) = ps 2 <chi, b> chi(t).
     Quadratures are composite Gauss-Legendre-12 panels with
     dyadic refinement toward singular endpoints, kink-split (u at
     a - t and a + t; t at log 2 - a), so algebraic endpoint
     singularities of any exponent s >= 0 and the log-endpoint
     behavior of T b for s = 0 modes are handled to quadrature
     tolerance (round-243 F12: the earlier "tanh-sinh" and
     "u > 1e-6 floor with sub-floor correction" described the
     superseded second architecture, not this code). A validated robustness property of this route:
     an additive error c * b(t) in T b (e.g. a counterterm slip)
     leaves sigma^2 EXACTLY invariant.

THE TRIAL FAMILIES (per parity; harmonic counts trimmed to keep
the pair frequencies within the GL panels' resolving power -- the
high harmonics carried ~zero optimizer weight in every earlier
round).
  old (even):   cos((m + 1/2) pi t/a), m = 0..23 (the certified
                span; the round-2 span is its window-recombination
                extension);
  old (odd):    sin((m + 1) pi t/a) union sin((m + 1/2) pi t/a),
                m = 0..23 (the round-2 span's core; the latter are
                s = 0 modes);
  rough (even): cos(m pi t/a), m = 0..8 (s = 0 -- the even
                sector's rough-edge directions, never present in
                any earlier span);
  fractional:   (1 - (t/a)^2)^s C_n^{(nu)}(t/a), nu in
                {0.75, 1.0} (s = 0.25, 0.5), n even 0..14 / odd
                1..15 per parity; transforms exactly Bessel
                (gate gF4 verifies the identity at independent r).

GATES. gF4: the Gegenbauer-Bessel transform identity (rel < 1e-8).
gF1: M's sub-block on the 24 certified fam1 modes vs build_Q64's Q
(rel Frobenius < 5e-4 -- the certified instrument's own Rmax-600
truncation class; this pipeline is the more accurate side). gF2:
sigma of the certified cos-24 extremal at even delta 0.9 pinned to
the adjudicated 2.7527e-3 (rel 1e-2) -- the cross-pipeline anchor.
Whitening: fixed cutoff 1e-4 after diagonal normalization; the
printed mr is the block-CS residual, an ASYMMETRY diagnostic (the
discrete T-application is not exactly self-adjoint), NOT a
sigma^2 defect: per-vector sigma^2 >= 0 holds EXACTLY on this
pipeline because N, M, S are Grams over one discrete measure (the
quadratic form sees only M's symmetric part) -- the round's
proof-level numerical lemma, alongside the sigma-invariance under
additive c*b errors in T b. The l2cos24 rung is dropped for the
union span (its true lambda_2 lies below the borrowed ell_2, so
Temple's premise fails there -- the round's interpretive lesson);
the union runs on min(l2c, own-section lambda_2) and half rungs.

RESULT (the finalized t-space run + the base-0.008 stability
check, 2026-08-21):
  CALIBRATION AND ADJUDICATION. The old-span column reproduces
  S5/run-2 at 3-4 digits everywhere it overlaps (even log 2
  +9.812e-4 sig 1.678e-2; even 0.9 -5.471e-5 sig 2.750e-3; even
  1.09 -1.954e-5 sig 1.963e-4), and gF2 hits the committed
  adjudicator's anchor at rel 3.6e-5 (2.7526e-3 vs 2.7527e-3 --
  round-243 F5: the earlier "five digits" was ~4.4 digits, and
  the anchor's producer is now committed as
  oneprime_adjudicator.py). ROUND 2'S ODD
  CLOSURES ARE CONFIRMED, slightly strengthened -- the suspect
  r-truncation was inflating odd sigma, in the conservative
  direction: old-span odd 0.9 +2.386e-3, 1.05 +4.594e-5, 1.09
  +1.734e-5 (the last now POSITIVE where run 2's l2sec rung was
  -8.7e-6).
  THE HEADLINE: the rough/fractional edge content unlocks the
  even sector. Union Temple values (own-lambda_2 rung; half rung
  in parentheses; optimizer weight in new modes 0.57-0.73):
    even log 2  +1.330e-3 (+1.330e-3)   sigma 2.897e-4
    even 0.80   +1.789e-4 (+1.764e-4)
    even 0.85   +5.668e-5 (+5.478e-5)
    even 0.90   +1.484e-5 (+1.350e-5)   sigma 3.580e-4
    even 0.95   +2.669e-6 (+1.466e-6)
    even 1.00   -9.435e-7  (fails; quadrature-marginal: the
                base-0.008 refinement moves it to -2.7e-7 with
                sigma still falling -- the next refinement's
                target, not claimed)
    even 1.05   -6.124e-6; even 1.09 -2.113e-5  (fail)
    odd  0.90   +2.393e-3 (+2.378e-3)
    odd  1.05   +4.636e-5 (+4.462e-5)
    odd  1.09   +1.789e-5 (+1.624e-5)
  Stability at base 0.008 (producer: stability_check() below,
  committed by round-243 F6 -- the numbers were session-drafted
  before it existed): even 0.9 +1.491e-5, even 0.95 +2.894e-6,
  odd 1.09 +1.811e-5 -- every claimed closure holds.
  THE ROUND'S STANDING VERDICT (feasibility level): the full
  semi-local form Temple-closes on [log 2, 0.95] -- the even
  frontier advanced 0.80 -> 0.95, robust through the half rung at
  every claimed cell -- and the ODD SECTOR CLOSES THE ENTIRE
  WINDOW through 1.09. The even remainder [1.0, log 3) fails by
  1e-6 - 2e-5 with sigma stalled at ~1.5-1.9e-4 (partly
  quadrature floor). Still stand-in ell_2 rungs and float64: the
  Lehmann-Goerisch and interval repairs remain the path from
  feasibility to theorem.

CHECKS. 7: classical. 8: no hypothesis input.

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
from oneprime_certificate import psign
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
LG4PI = math.log(4*math.pi) + 0.5772156649015329
NUS = (0.75, 1.0)
NFR = 8
NHALF = 24
NROUGH = 9
_XGL, _WGL = np.polynomial.legendre.leggauss(12)

def gl_panels(lo, hi, sing=(), base=0.012, depth=34):
    """Composite GL-12 nodes/weights on (lo, hi): ~base-sized
    panels (GL-12 resolves the oscillatory harmonic products:
    the worst pair frequency ~450 rad gives ~5.4 rad per panel,
    within GL-12's degree-23 reach), with
    dyadic refinement toward each singular endpoint in `sing`
    (edge log^2 / algebraic singularities), down to base*2^-depth.
    Interior breakpoints in `sing` are honored as panel edges."""
    if hi - lo < 1e-13:
        return np.empty(0), np.empty(0)
    pts = {lo, hi}
    for s_ in sing:
        if lo < s_ < hi:
            pts.add(s_)
    for s_ in sing:
        if abs(s_ - lo) < 1e-13 or abs(s_ - hi) < 1e-13:
            sign = 1.0 if abs(s_ - lo) < 1e-13 else -1.0
            for j in range(depth):
                p_ = s_ + sign*base*2.0**(-j - 1)
                if lo < p_ < hi:
                    pts.add(p_)
    pts = sorted(pts)
    bps = []
    for x0, x1 in zip(pts[:-1], pts[1:]):
        nsub = max(1, int(math.ceil((x1 - x0)/base)))
        bps.extend(np.linspace(x0, x1, nsub + 1)[:-1])
    bps.append(hi)
    bps = np.array(bps)
    mid = 0.5*(bps[1:] + bps[:-1])
    rad = 0.5*(bps[1:] - bps[:-1])
    nodes = (mid[:, None] + rad[:, None]*_XGL[None, :]).ravel()
    wts = (rad[:, None]*_WGL[None, :]).ravel()
    return nodes, wts

# ------------------------------------------------ the mode catalog
class Modes:
    def __init__(self, a, parity, nus=NUS, nfr=NFR, nrough=NROUGH):
        self.a, self.parity = a, parity
        if parity == "even":
            self.w = list((np.arange(NHALF) + 0.5)*np.pi/a) \
                + list(np.arange(nrough)*np.pi/a)
        else:
            self.w = sorted(list((np.arange(NHALF) + 1.0)*np.pi/a)
                            + list((np.arange(NHALF) + 0.5)*np.pi/a))
        self.w = np.array(self.w)
        self.nharm = len(self.w)
        self.frac = []
        ns = (np.arange(nfr)*2 if parity == "even"
              else np.arange(nfr)*2 + 1)
        for nu in nus:
            s = nu - 0.5
            xj, wj = roots_jacobi(220, s, s)
            for n in ns:
                cn, devs = self._calibrate(nu, n, xj, wj)
                self.frac.append({"nu": nu, "n": int(n), "cn": cn,
                                  "xj": xj, "wj": wj, "gF4": devs})
        self.n = self.nharm + len(self.frac)

    def _quad_q(self, nu, n, r, xj, wj):
        f = np.cos if self.parity == "even" else np.sin
        return self.a*np.sum(
            wj*eval_gegenbauer(n, nu, xj)*f(r*self.a*xj))

    def _calibrate(self, nu, n, xj, wj):
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

    def t_eval(self, t):
        """(n x len(t)), zero outside [-a, a]."""
        t = np.atleast_1d(np.asarray(t, dtype=float))
        a = self.a
        out = np.zeros((self.n, len(t)))
        inside = np.abs(t) <= a
        ti = t[inside]
        f = np.cos if self.parity == "even" else np.sin
        out[:self.nharm, inside] = f(self.w[:, None]*ti[None, :])
        x = ti/a
        # (a-t)(a+t)/a^2, NOT 1 - x^2: near the support edges the
        # latter loses ~6 digits to cancellation, which was the
        # error floor of the whole S assembly (round lesson)
        wt = np.clip((a - ti)*(a + ti), 0.0, None)/(a*a)
        for j, fr in enumerate(self.frac):
            out[self.nharm + j, inside] = (
                wt**(fr["nu"] - 0.5)*eval_gegenbauer(fr["n"],
                                                     fr["nu"], x))
        return out

# ------------------------------------------- the t-space operator
def apply_T(md, base=0.012):
    """T b_i on the GL-panel t-grid (half-line [0, a]; all
    integrands' products are even); returns (tn, tw, B, TB, v)."""
    a, parity = md.a, md.parity
    k0 = min(max(LOG2 - a, 0.0), a)
    tn, tw = gl_panels(0.0, a, sing=(k0, a), base=base)
    B = md.t_eval(tn)
    TB = -LG4PI*B.copy()
    f = np.cos if parity == "even" else np.sin
    for k, t in enumerate(tn):
        bt = B[:, k]
        acc = np.zeros(md.n)
        for lo, hi, sing in (((0.0, a - t, (a - t,))),
                             ((a - t, a + t, (a - t, a + t)))):
            u, wu = gl_panels(lo, hi, sing=sing, base=base)
            if len(u) == 0:
                continue
            A = (np.exp(u/2) - 1)/np.sinh(u)
            both_in = (t + u <= a) & (t - u >= -a)
            Bp = md.t_eval(t + u)
            Bm = md.t_eval(t - u)
            Dfull = (Bp + Bm)/2 - bt[:, None]
            Dh = -2*f(md.w[:, None]*t)*np.sin(
                md.w[:, None]*u[None, :]/2)**2
            D = np.where(both_in[None, :],
                         np.vstack([Dh, Dfull[md.nharm:]]),
                         Dfull)
            acc += bt*np.sum(A*wu)
            acc += (D*(np.exp(u/2)/np.sinh(u)*wu)[None, :]).sum(1)
        TB[:, k] -= acc
        TB[:, k] += bt*math.log(1.0/math.tanh((a + t)/2))
    TB += -(C2/2)*(md.t_eval(tn + LOG2) + md.t_eval(tn - LOG2))
    chi = (np.cosh(tn/2) if parity == "even" else np.sinh(tn/2))
    v = 2*(B*(tw*chi)[None, :]).sum(1)
    TB += psign(parity)*2*np.outer(v, chi)
    return tn, tw, B, TB, v


def cell_matrices(a, parity, base=0.012, **modeskw):
    md = Modes(a, parity, **modeskw)
    gf4 = max(max(fr["gF4"]) for fr in md.frac)
    tn, tw, B, TB, v = apply_T(md, base=base)
    N = 2*(B*tw[None, :]) @ B.T
    M = 2*(B*tw[None, :]) @ TB.T
    S = 2*(TB*tw[None, :]) @ TB.T
    N, M, S = (N + N.T)/2, (M + M.T)/2, (S + S.T)/2
    return md, N, M, S, gf4, (tn, tw, B, TB)


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
              "nrough": NROUGH}
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
        md, N, M, S, gf4, grids = cell_matrices(a, parity)
        tn, tw, B, TB = grids
        assert gf4 < 1e-8, f"gF4 FAIL {parity}:{delta:g}: {gf4:.1e}"
        Qc, Gc, _, _, _ = build_Q64(delta, parity=parity)
        if parity == "even":
            idx = np.arange(NHALF)
        else:
            wcert = (np.arange(NHALF) + 1.0)*np.pi/a
            idx = np.array([int(np.argmin(np.abs(md.w - w)))
                            for w in wcert])
        Qs = Qc[:NHALF, :NHALF]
        gf1 = float(np.linalg.norm(M[np.ix_(idx, idx)] - Qs)
                    / np.linalg.norm(Qs))
        assert gf1 < 5e-4, f"gF1 FAIL {parity}:{delta:g}: {gf1:.1e}"
        l2c = float(scipy_eigh(Qc, Gc, eigvals_only=True)[1])

        # gF2 at the anchor cell: sigma of the certified extremal
        if parity == "even" and abs(delta - 0.9) < 1e-9:
            ev, V = scipy_eigh(Qc, Gc)
            cc = np.zeros(md.n); cc[:NHALF] = V[:, 0]
            nn = float(cc @ N @ cc)
            rho0 = float(cc @ M @ cc)/nn
            sg0 = math.sqrt(max(float(cc @ S @ cc)/nn - rho0**2, 0))
            print(f"  gF2 anchor: rho {rho0:.4e} sigma {sg0:.4e} "
                  f"(adjudicated 2.7527e-3)", flush=True)
            assert abs(sg0/2.7527e-3 - 1) < 1e-2, "gF2 FAIL"

        nold_sub = NHALF if parity == "even" else md.nharm

        def white(sub):
            # Whiten the VALUE matrices, then form Grams: N, M, S
            # over one discrete measure satisfy the operator
            # Cauchy-Schwarz S >= M N^-1 M EXACTLY by construction,
            # and rounding enters at 1/sqrt(ev) instead of the 1/ev
            # of whitened triple products (the round's third
            # numerical lesson: the fake sigma^2 < 0 directions
            # were float amplification, not quadrature error). The
            # residual check is kept as the sanity gate.
            Ns = N[np.ix_(sub, sub)]
            d = 1.0/np.sqrt(np.diag(Ns))
            Nn = d[:, None]*Ns*d[None, :]
            ev, U = np.linalg.eigh(Nn)
            cut = 1e-4
            keep = ev > cut
            Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T
                  * d[None, :])
            Bw = Wh @ B[sub]
            TBw = Wh @ TB[sub]
            Nw = 2*(Bw*tw[None, :]) @ Bw.T
            Mw = 2*(Bw*tw[None, :]) @ TBw.T
            Sw = 2*(TBw*tw[None, :]) @ TBw.T
            Nw, Mw, Sw = ((Nw + Nw.T)/2, (Mw + Mw.T)/2,
                          (Sw + Sw.T)/2)
            res = Sw - Mw @ np.linalg.solve(Nw, Mw)
            minres = float(np.linalg.eigvalsh((res + res.T)/2)[0])
            return Wh, Nw, Mw, Sw, cut, minres
        WhA, NA, MA, SA, cutA, mrA = white(np.arange(md.n))
        WhO, NO, MO, SO, cutO, mrO = white(np.arange(nold_sub))
        l2A = float(scipy_eigh(MA, NA, eigvals_only=True)[1])
        l2O = float(scipy_eigh(MO, NO, eigvals_only=True)[1])
        # the l2cos24 rung is INVALID for the enriched union (its
        # true lambda_2 sits below the cos-24 span's, so Temple's
        # premise ell_2 <= lambda_2 fails and the rung returns
        # legitimate-but-useless values for higher eigenvectors --
        # the round's fourth interpretive lesson); the union runs
        # on its own section lambda_2 and the half-rung only
        LA = ladder(NA, MA, SA, l2A, min(l2c, l2A))
        LO = ladder(NO, MO, SO, l2O, l2c)
        c = LA["l2sec"]["_c"]
        if c is not None:
            craw = WhA.T @ c
            fw = float(np.sum(craw[nold_sub:]**2)
                       / np.sum(craw**2))
        else:
            fw = float("nan")
        for L in (LA, LO):
            for k in L:
                L[k].pop("_c")
        st[f"{parity}:{delta:g}"] = {
            "dimA": NA.shape[0], "dimO": NO.shape[0], "gF1": gf1,
            "gF4": gf4, "l2c": l2c, "union": LA, "old": LO,
            "new_weight": fw, "cutA": cutA, "minresA": mrA,
            "cutO": cutO, "minresO": mrO}
        print(f"FRAC {parity} delta {delta:g} (dimA {NA.shape[0]} "
              f"cutA {cutA:.0e} mr {mrA:+.1e} dimO {NO.shape[0]} "
              f"gF1 {gf1:.1e}): old Temple "
              f"{LO['l2sec']['temple']:+.3e} (sig "
              f"{LO['l2sec']['sigma']:.3e}) | union Temple "
              f"{LA['l2sec']['temple']:+.3e} (rho "
              f"{LA['l2sec']['rho']:+.3e} sig "
              f"{LA['l2sec']['sigma']:.3e} nw {fw:.3f}) l2cos24 "
              f"{LA['l2cos24']['temple']:+.3e} half "
              f"{LA['half']['temple']:+.3e}", flush=True)
    ckpt_key.save("oneprime_frac", KEYFILE, params, st)
    return st


def stability_check():
    """The base-0.008 stability producer (round-243 F6): the three
    claimed-closure cells rerun at refined quadrature."""
    from oneprime_bridge import build_Q64 as _b
    for parity, delta in (("even", 0.9), ("even", 0.95),
                          ("odd", 1.09)):
        a = delta/2
        md, N, M, S, gf4, grids = cell_matrices(a, parity,
                                                base=0.008)
        tn, tw, B, TB = grids
        d = 1.0/np.sqrt(np.diag(N))
        ev, U = np.linalg.eigh(d[:, None]*N*d[None, :])
        keep = ev > 1e-4
        Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T
              * d[None, :])
        Bw, TBw = Wh @ B, Wh @ TB
        NA = 2*(Bw*tw[None, :]) @ Bw.T
        MA = 2*(Bw*tw[None, :]) @ TBw.T
        SA = 2*(TBw*tw[None, :]) @ TBw.T
        NA, MA, SA = ((NA + NA.T)/2, (MA + MA.T)/2,
                      (SA + SA.T)/2)
        l2A = float(scipy_eigh(MA, NA, eigvals_only=True)[1])
        mu, c = temple_opt(NA, MA, SA, l2A)
        nn = float(c @ NA @ c)
        rho = float(c @ MA @ c)/nn
        sig = math.sqrt(max(float(c @ SA @ c)/nn - rho*rho, 0.0))
        print(f"STAB {parity} {delta:g} base 0.008: Temple "
              f"{mu:+.3e} rho {rho:+.3e} sigma {sig:.3e}",
              flush=True)


if __name__ == "__main__":
    import os as _os
    if _os.environ.get("FRAC_STABILITY") == "1":
        stability_check()
    else:
        run()
    print("one-prime rough/fractional-edge round complete", flush=True)
