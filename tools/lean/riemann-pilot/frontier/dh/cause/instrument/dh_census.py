#!/usr/bin/env python3
"""dh_census.py -- resumable zero census of the Davenport-Heilbronn function.

Objects
-------
    kappa = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1) = 0.2840790438...,   theta = arctan(kappa)
    chi   = chi_5 with chi(1..4) = (1, i, -i, -1),  chi(0) = 0          (residues mod 5)
    f(s)  = sum_n u(n mod 5) n^-s,   u = (0, 1, kappa, -kappa, -1)
          = c1 L(s, chi) + c2 L(s, chibar),   c1 = (1 - i kappa)/2,  c2 = (1 + i kappa)/2

Everything is computed from the four Hurwitz values H_a(s) = zeta(s, a/5), a = 1..4
(python-flint ball arithmetic):  with A = H_1 - H_4 and B = H_2 - H_3,
    f = 5^-s (A + kappa B),   L(s, chi) = 5^-s (A + i B),   L(s, chibar) = 5^-s (A - i B).
On the critical line s = 1/2 + it, with vartheta(t) = (t/2) log(5/pi) + Im lgamma(3/4 + it/2),
    Z_f(t)      = Re(e^{i vartheta} f),
    Z_chi(t)    = Re(e^{i vartheta} e^{-i theta} L(s, chi)),
    Z_chibar(t) = Re(e^{i vartheta} e^{+i theta} L(s, chibar)),
whose imaginary parts vanish (functional equations; checked on every evaluation).

What a census does (README_instrument.md has the derivations and the validation)
----------------------------------------------------------------------------
The height range [t0, t1] is cut into checkpoint windows of nominal length dt.  Per window:
  1. Z_f, Z_chi, Z_chibar are sampled with step <= h(t) = 2 pi/(16 log(5t/2pi)); every sign change
     is refined by Brent's method to |dt| < 1e-9; same-sign local minima of |Z| that are small
     relative to their neighbours are minimised by golden section, and a crossing found there adds
     the two roots of a close pair.  A sample whose sign is uncertain (ball contains 0) is
     re-evaluated at twice the working precision.
  2. Window ends are shifted down by at most 0.5 to the sample maximising min_k |Z_k|/rms_k, and the
     zero counts N_f, N_chi, N_chibar at the ends come from continuous phase tracking
     (argument principle with the reflection; increments < 0.25 rad).
  3. Accounting: Delta N_chi = #roots(Z_chi), Delta N_chibar = #roots(Z_chibar), and
     K = (Delta N_f - n_f)/2 must be a non-negative integer (K = zeros of f with Re s > 1/2).
     Any inconsistency is localised by bisection with intermediate counts and the offending
     sub-window is re-sampled more finely; what stays inconsistent is flagged.
  4. Exactly K zeros with 1/2 < Re s < 2 are located by Newton iteration (prec, then 2 prec),
     started from the wrong-sign extrema of Z_f, with bisection + |f|-grid fallback.
  5. One JSON line per window is appended (fsync); a rerun resumes after the last complete line.

Pre-registration guard: a census never evaluates anything above its own t1 (window ends move
down only; Newton and the fallback grids are confined below t1).

Usage
-----
  dh_census.py --t0 A --t1 B --out FILE.jsonl [--dt 25] [--prec 53]   census (resumable)
  dh_census.py --selftest                                              self-tests and exit
  dh_census.py --timing [--heights 1000,3000,5000,10000] [--reps 20]  time the evaluator alone
  dh_census.py --summary FILE.jsonl [FILE.jsonl ...]                   aggregate and cross-check
  dh_census.py --plan NCORES --t0 A --t1 B [--dt 25] [--evals-per-zero E] [--timing-file F]
                                                                       cost model + balanced split
"""

import argparse
import bisect
import collections
import json
import math
import os
import sys
import time

from flint import acb, arb, ctx

FORMAT = "dh_census/1"
NAMES = ("f", "chi", "chibar")
PI = math.pi
EPS = 2.0 ** -52

# Float copies of the constants, for bookkeeping only (evaluations use arb constants).
KAPPA = (math.sqrt(10.0 - 2.0 * math.sqrt(5.0)) - 2.0) / (math.sqrt(5.0) - 1.0)
THETA = math.atan(KAPPA)

# ---------------------------------------------------------------------------------------------
# Tunables (all documented in README_instrument.md)
# ---------------------------------------------------------------------------------------------
SAMPLES_PER_SPACING = 16      # on-line samples per mean zero spacing 2 pi/log(5t/2pi)
H_CAP = 0.1                   # largest sampling step (low heights, where the spacing formula fails)
SHIFT = 0.5                   # a window end moves down by at most this much
CLOSE_RATIO = 0.3             # close-pair trigger: |Z| at a same-sign local min < 0.3 x larger nbr
ROOT_XTOL = 2e-10             # Brent tolerance; final bracket <= ~2e-10 (< 1e-9 required)
GOLD_TOL = 1e-9               # golden-section bracket width at which a dip is declared crossing-free
GOLD_SAFETY = 8.0             # early stop when min g > 8 * curvature * width^2 (no crossing possible)
MAX_INC = 0.25                # largest accepted phase increment (rad) in argument tracking
MIN_TRACK_STEP = 1e-9         # tracking step floor (a zero this close to the segment is flagged)
INT_TOL = 0.05                # each N must lie within this of an integer
NEWTON_D = (0.01, 0.03, 0.08, 0.2, 0.35)  # offsets d of the Newton starts 1/2 + d + i t_ext
ACCEPT_F = 1e-12              # |f(rho)| at 2 prec for acceptance
ACCEPT_RE = 1e-7              # Re rho > 1/2 + ACCEPT_RE
DISTINCT = 1e-6               # accepted zeros differ by more than this
LOC_MIN_LEN = 1.0             # localisation bisection stops at sub-windows this short
REPAIR_SAMPLES = 16           # count repair bisects until a sub-window holds <= this many samples
DENSIFY = (16, 256)           # re-sampling factors (local step <= h/factor) for a short sub-window
GRID_STAGES = ((0.505, 1.3, 0.01), (1.3, 1.99, 0.01))   # (sigma_lo, sigma_hi, step) fallback grids
GRID_DT = 0.05                # fallback grid step in t
SELFTEST_HEIGHTS = (7.3, 51.1, 133.7)   # startup self-test heights (all below 200)


# ---------------------------------------------------------------------------------------------
# Sampling geometry.  Everything here depends only on the nominal ends, so two runs that share a
# nominal end (e.g. [1, 200] and [200, 10000]) choose the same shifted end and tile the line.
# ---------------------------------------------------------------------------------------------
def mean_spacing(t):
    """Mean spacing 2 pi/log(5t/2pi) of the zeros of f (and of each channel) at height t."""
    L = math.log(5.0 * t / (2.0 * PI)) if t > 0 else 0.0
    return 2.0 * PI / L if L > 0 else math.inf


def h_of_t(t):
    """On-line sampling step at height t: 16 samples per mean spacing, capped at H_CAP."""
    return min(H_CAP, mean_spacing(t) / SAMPLES_PER_SPACING)


def end_step(b):
    """Grid step hb = SHIFT/J <= h(b) anchored at the nominal end b (J an integer)."""
    J = int(math.ceil(SHIFT / h_of_t(b) - 1e-12))
    return J, SHIFT / J


def end_candidates(b):
    """Candidate shifted ends b - j hb, j = J..0 (ascending), tiling [b - 0.5, b]."""
    J, hb = end_step(b)
    return [b - j * hb for j in range(J, -1, -1)]


def window_grid(a, b):
    """Sample grid of the nominal window [a, b]: b - j hb for j = 0, 1, ... down to a, plus a.
    Since h(t) decreases with t, hb <= h(b) <= h(t) on the whole window.  The top J+1 points are
    exactly end_candidates(b) (same floating-point expressions)."""
    J, hb = end_step(b)
    M = int(math.ceil((b - a) / hb - 1e-6))
    pts = [b - j * hb for j in range(M)]
    pts.append(a)
    pts.reverse()
    return pts


def nominal_ends(t0, t1, dt):
    """Nominal window ends t0, t0 + dt, ..., t1; a remainder shorter than dt/2 joins the last window."""
    n = int(math.floor((t1 - t0) / dt + 1e-9))
    ends = [t0 + k * dt for k in range(n + 1)]
    if t1 - ends[-1] > 1e-9:
        if len(ends) >= 2 and t1 - ends[-1] < 0.5 * dt:
            ends[-1] = t1
        else:
            ends.append(t1)
    return ends


# ---------------------------------------------------------------------------------------------
# Evaluator
# ---------------------------------------------------------------------------------------------
class HeightCeiling(Exception):
    """A census evaluation was requested above the run's t1 (pre-registration guard)."""


class TrackingError(Exception):
    """Argument tracking could not keep the phase increments small (zero on/near the segment)."""


class Consts:
    """arb/acb constants at one working precision."""

    def __init__(self, prec, theta_sign):
        with ctx.workprec(prec):
            five = arb(5)
            sq5 = five.sqrt()
            self.kappa = ((10 - 2 * sq5).sqrt() - 2) / (sq5 - 1)
            self.theta = theta_sign * self.kappa.atan()
            self.two_cos = 2 * self.theta.cos()
            self.log5 = five.log()
            self.logq = (five / arb.pi()).log()            # log(5/pi)
            self.inv_sqrt5 = 1 / sq5
            self.avals = [acb(a) / 5 for a in (1, 2, 3, 4)]
            self.i = acb(0, 1)
            self.rot_chi = acb(0, -self.theta).exp()       # e^{-i theta}
            self.rot_chib = acb(0, self.theta).exp()       # e^{+i theta}


class Evaluator:
    """f, L(s,chi), L(s,chibar) and the three rotated critical-line values, all from the same four
    Hurwitz values.  Counts evaluations per precision and keeps the running self-test maxima."""

    def __init__(self, prec=53, theta_sign=1, ceiling=None):
        self.prec = prec
        self.hi = 2 * prec
        self.theta_sign = theta_sign
        self.ceiling = ceiling
        self._consts = {}
        self.nevals = collections.Counter()
        self.reset_selftest()

    def reset_selftest(self):
        self.st_im = 0.0   # max over line evaluations of |Im R_k| / (1e-8 (1 + |R_k|))
        self.st_id = 0.0   # max of |Z_f - (Z_chi + Z_chibar)/(2 cos theta)| / (1e-10 (1 + |Z_f|))

    def consts(self, prec):
        c = self._consts.get(prec)
        if c is None:
            c = self._consts[prec] = Consts(prec, self.theta_sign)
        return c

    def _guard(self, t):
        if self.ceiling is not None and t > self.ceiling:
            raise HeightCeiling(t)

    @staticmethod
    def _ab(s, c):
        h = [acb.zeta(s, a) for a in c.avals]
        return h[0] - h[3], h[1] - h[2]

    def values_s(self, s, prec=None):
        """(f(s), L(s,chi), L(s,chibar)) as acb balls for an acb point s."""
        prec = prec or self.prec
        self._guard(float(s.imag.mid()))
        c = self.consts(prec)
        with ctx.workprec(prec):
            s = acb(s)
            A, B = self._ab(s, c)
            p = (-s * c.log5).exp()
            out = (p * (A + c.kappa * B), p * (A + c.i * B), p * (A - c.i * B))
        self.nevals[prec] += 1
        return out

    def values(self, sigma, t, prec=None):
        """(f, L(.,chi), L(.,chibar)) at sigma + it (floats; exact as binary numbers)."""
        prec = prec or self.prec
        self._guard(t)
        with ctx.workprec(prec):
            s = acb(sigma, t)
        return self.values_s(s, prec)

    def vartheta(self, t, prec=None):
        prec = prec or self.prec
        c = self.consts(prec)
        with ctx.workprec(prec):
            return arb(t) / 2 * c.logq + acb(0.75, t / 2).lgamma().imag

    def rotated(self, t, prec=None):
        """R = (e^{iv} f, e^{iv} e^{-i th} L(chi), e^{iv} e^{+i th} L(chibar)) at s = 1/2 + it,
        v = vartheta(t).  Real parts: Z_f, Z_chi, Z_chibar.  Updates the self-test maxima."""
        prec = prec or self.prec
        self._guard(t)
        c = self.consts(prec)
        with ctx.workprec(prec):
            s = acb(0.5, t)
            A, B = self._ab(s, c)
            # e^{i vartheta} 5^{-s} = 5^{-1/2} e^{i (vartheta - t log 5)}
            ph = arb(t) / 2 * c.logq + acb(0.75, t / 2).lgamma().imag - arb(t) * c.log5
            r = acb(0, ph).exp() * c.inv_sqrt5
            R = (r * (A + c.kappa * B), r * c.rot_chi * (A + c.i * B), r * c.rot_chib * (A - c.i * B))
            two_cos = float(c.two_cos)
        self.nevals[prec] += 1
        z = [float(x.real) for x in R]
        for x in R:
            ratio = abs(float(x.imag)) / (1e-8 * (1.0 + float(abs(x))))
            if ratio > self.st_im:
                self.st_im = ratio
        ratio = abs(z[0] - (z[1] + z[2]) / two_cos) / (1e-10 * (1.0 + abs(z[0])))
        if ratio > self.st_id:
            self.st_id = ratio
        return R

    def line(self, t):
        """Z values at height t.  If any sign is uncertain (ball contains 0) the point is
        re-evaluated at 2 prec.  Returns (z tuple, all-signs-certain flag)."""
        R = self.rotated(t)
        if any(0 in x.real for x in R):
            R = self.rotated(t, self.hi)
        return tuple(float(x.real) for x in R), all(0 not in x.real for x in R)

    def zval(self, t, ch):
        """Z_ch(t) with the same escalation rule, for one channel.  Returns (value, certain)."""
        x = self.rotated(t)[ch].real
        if 0 in x:
            x = self.rotated(t, self.hi)[ch].real
        return float(x), 0 not in x


# ---------------------------------------------------------------------------------------------
# Self-tests and real-axis data
# ---------------------------------------------------------------------------------------------
def selftest(prec=53, heights=SELFTEST_HEIGHTS):
    """Determine the root-number convention: with theta_sign = +1 the rotated values must be real
    (|Im| < 1e-8 (1 + |value|)) and Z_f = (Z_chi + Z_chibar)/(2 cos theta) to 1e-10.  Both signs
    are reported; the first passing sign is returned.  Also cross-checks L(s, chi) from the Hurwitz
    values against flint's independent acb.dirichlet_l."""
    from flint import dirichlet_char
    report = {}
    passing = None
    for sign in (1, -1):
        ev = Evaluator(prec, sign)
        for t in heights:
            ev.rotated(t)
        ok = ev.st_im < 1.0 and ev.st_id < 1.0
        report["theta_sign=%+d" % sign] = {"max_im_ratio": ev.st_im, "max_id_ratio": ev.st_id,
                                           "pass": ok}
        if ok and passing is None:
            passing = sign
    # independent cross-check of the Hurwitz construction of L(s, chi)
    ev = Evaluator(prec, passing or 1)
    chi = dirichlet_char(5, 2)          # values (1, i, -i, -1) on 1..4
    worst = 0.0
    with ctx.workprec(prec):
        for t in heights:
            _, lc, _ = ev.values(0.5, t)
            ref = acb.dirichlet_l(acb(0.5, t), chi)
            worst = max(worst, float(abs(lc - ref)) / float(abs(ref)))
    report["dirichlet_l_rel_diff"] = worst
    report["heights"] = list(heights)
    return passing, report


def real_axis_data(ev, n=151):
    """Data on the real segment [1/2, 2] needed by the counting formulas:
    f(sigma) > 0 (checked on a grid, balls), the continuous change D of arg L(sigma, chi) from 1/2
    to 2, Arg L(2, chi), and the sign of the real number e^{-i theta} L(1/2, chi)."""
    sig = [0.5 + 1.5 * j / n for j in range(n + 1)]     # n = 151: never hits the pole s = 1
    fmin, fimag, D, prev = math.inf, 0.0, 0.0, None
    for s_ in sig:
        F = ev.values(s_, 0.0)
        if not F[0].real > 0:
            raise SystemExit("real-axis check failed: f(%g) not certified positive" % s_)
        fmin = min(fmin, float(F[0].real))
        fimag = max(fimag, abs(float(F[0].imag)))
        if prev is not None:
            inc = float((F[1] / prev).arg())
            if abs(inc) >= MAX_INC:
                raise SystemExit("real-axis tracking step too coarse")
            D += inc
        else:
            L_half = F[1]
        prev = F[1]
    c = ev.consts(ev.prec)
    with ctx.workprec(ev.prec):
        real_half = float((c.rot_chi * L_half).real)
        imag_half = float((c.rot_chi * L_half).imag)
    return {"D_chi": D, "D_chibar": -D,
            "arg2_chi": float(prev.arg()), "arg2_chibar": -float(prev.arg()),
            "rotL_half": real_half, "rotL_half_imag": imag_half,
            "f_min_on_[1/2,2]": fmin, "f_imag_max": fimag,
            "f_half": float(ev.values(0.5, 0.0)[0].real)}


# ---------------------------------------------------------------------------------------------
# Small numerical helpers
# ---------------------------------------------------------------------------------------------
def brent_root(fun, a, b, fa, fb, xtol=ROOT_XTOL, maxiter=200):
    """Brent's method on [a, b] with fa*fb < 0, stopping when the bracket is below ~2 xtol.
    fun(t) -> (value, certain); a value whose sign is uncertain even at 2 prec means |Z| is below
    the 2-prec ball radius (~1e-26 at t = 1e4), i.e. t is a root far inside the tolerance."""
    c, fc = a, fa
    d = e = b - a
    for _ in range(maxiter):
        if (fb > 0) == (fc > 0):
            c, fc = a, fa
            d = e = b - a
        if abs(fc) < abs(fb):
            a, b, c = b, c, b
            fa, fb, fc = fb, fc, fb
        tol1 = 2.0 * EPS * abs(b) + 0.5 * xtol
        xm = 0.5 * (c - b)
        if abs(xm) <= tol1 or fb == 0.0:
            return b
        if abs(e) >= tol1 and abs(fa) > abs(fb):
            s = fb / fa
            if a == c:
                p, q = 2.0 * xm * s, 1.0 - s
            else:
                q, r = fa / fc, fb / fc
                p = s * (2.0 * xm * q * (q - r) - (b - a) * (r - 1.0))
                q = (q - 1.0) * (r - 1.0) * (s - 1.0)
            if p > 0:
                q = -q
            p = abs(p)
            if 2.0 * p < min(3.0 * xm * q - abs(tol1 * q), abs(e * q)):
                e, d = d, p / q
            else:
                d = e = xm
        else:
            d = e = xm
        a, fa = b, fb
        b = b + d if abs(d) > tol1 else b + math.copysign(tol1, xm)
        fb, certain = fun(b)
        if not certain:
            return b
    raise RuntimeError("Brent did not converge on [%r, %r]" % (a, b))


def parabola(t0, t1, t2, y0, y1, y2):
    """Vertex t*, value y*, and a with y ~ a (t - t*)^2 + y* for the parabola through 3 points."""
    d01 = (y1 - y0) / (t1 - t0)
    d12 = (y2 - y1) / (t2 - t1)
    a = (d12 - d01) / (t2 - t0)
    if a <= 0:
        return t1, y1, 0.0
    ts = 0.5 * (t0 + t1) - d01 / (2.0 * a)
    ts = min(max(ts, t0), t2)
    ys = y0 + d01 * (ts - t0) + a * (ts - t0) * (ts - t1)
    return ts, ys, a


class Dip:
    """A same-sign local minimum of |Z| at an interior sample (wrong-sign extremum of Z)."""
    __slots__ = ("t", "g", "ratio", "curv", "tl", "tr")

    def __init__(self, t, g, ratio, curv, tl, tr):
        self.t, self.g, self.ratio, self.curv, self.tl, self.tr = t, g, ratio, curv, tl, tr

    def d_est(self):
        """Distance to the line of an off-line pair rho, 1 - conj rho producing this dip:
        |Lambda(1/2 + it)| ~ (t - gamma)^2 + beta^2, so beta ~ sqrt(min/curvature)."""
        if self.curv > 0 and self.g > 0:
            return math.sqrt(self.g / self.curv)
        return None


# ---------------------------------------------------------------------------------------------
# The census
# ---------------------------------------------------------------------------------------------
class Census:
    def __init__(self, t0, t1, dt, prec, out, log=sys.stderr):
        self.t0, self.t1, self.dt, self.prec, self.out = t0, t1, dt, prec, out
        self.log = log
        self.ends = nominal_ends(t0, t1, dt)
        self.params = {"t0": t0, "t1": t1, "dt": dt, "prec": prec}
        self.startup = None

    # ---------------- run / resume ----------------
    def run(self):
        """Validate/resume the output file, run the start-up self-tests, then process the
        remaining windows, appending one record each."""
        recs, good_bytes, torn = load_records(self.out)
        for r in recs:
            if r.get("format") != FORMAT or r.get("params", {}) .get("t0") != self.t0 or \
                    r["params"].get("t1") != self.t1 or r["params"].get("dt") != self.dt or \
                    r["params"].get("prec") != self.prec:
                raise SystemExit("%s holds records of a different run (params %r); use a new --out"
                                 % (self.out, r.get("params")))
        for i, r in enumerate(recs):
            if r["k"] != i or (i and r["T0"] != recs[i - 1]["T1"]):
                raise SystemExit("%s: records are not a contiguous window sequence" % self.out)
        if torn:
            with open(self.out, "r+b") as fh:
                fh.truncate(good_bytes)
            self._say("truncated a torn trailing line of %s" % self.out)
        nwin = len(self.ends) - 1
        if len(recs) >= nwin:
            self._say("census %s already complete (%d windows)" % (self.out, nwin))
            return

        sign, st = selftest(self.prec)
        if sign is None:
            raise SystemExit("self-test failed for both theta signs: %r" % st)
        self.ev = Evaluator(self.prec, sign, ceiling=self.t1)
        self.ra = real_axis_data(self.ev)
        self.startup = {"selftest": st, "theta_sign": sign, "real_axis": self.ra,
                        "kappa": KAPPA, "theta": THETA, "resumed_at_window": len(recs)}
        self.params["theta_sign"] = sign
        self._say("self-test: theta_sign %+d  %s" % (sign, json.dumps(st)))

        # starting end and its counts
        self.S, self.Ncache, self.flags = {}, {}, set()
        self.diag = collections.Counter()
        if recs:
            last = recs[-1]
            T0s = last["T1"]
            N0 = (tuple(last[k][0] for k in ("Nf1", "Nchi1", "Nchib1")),
                  tuple(last[k][1] for k in ("Nf1", "Nchi1", "Nchib1")))
            a = self.ends[len(recs)]
            for t in end_candidates(a):
                if t >= T0s:
                    self._sample(t)
        else:
            T0s, N0 = self._end_and_counts(self.ends[0])
        self.start_flags = set(self.flags)
        carry = {t: self.S[t] for t in self.S if t >= T0s}

        t_run = time.time()
        for k in range(len(recs), nwin):
            rec = self._window(k, T0s, N0, carry)
            if self.startup is not None:
                rec["startup"] = self.startup
                self.startup = None
            append_record(self.out, rec)
            done = k + 1 - len(recs)
            rate = (time.time() - t_run) / done
            self._say("window %d/%d [%.4f, %.4f] roots f/chi/chibar %d/%d/%d K=%d flags=%s "
                      "%.1fs (ETA %.0fs)" % (k + 1, nwin, rec["T0"], rec["T1"], len(rec["roots_f"]),
                                             len(rec["roots_chi"]), len(rec["roots_chibar"]),
                                             rec["K"], rec["flags"], rec["seconds"],
                                             rate * (nwin - k - 1)))
            T0s = rec["T1"]
            N0 = (tuple(rec[k_][0] for k_ in ("Nf1", "Nchi1", "Nchib1")),
                  tuple(rec[k_][1] for k_ in ("Nf1", "Nchi1", "Nchib1")))
            carry = self._carry

    def _say(self, msg):
        print(msg, file=self.log, flush=True)

    # ---------------- sampling ----------------
    def _sample(self, t):
        if t not in self.S:
            z, sure = self.ev.line(t)
            if not sure:
                self.flags.add("uncertain_sample")
                # a value that is 0 to 2 prec: give it a definite (tiny) sign so that counting
                # stays well defined; the accounting decides whether that was right
                z = tuple(x if x != 0.0 else 1e-300 for x in z)
            self.S[t] = z
        return self.S[t]

    def _end_and_counts(self, b):
        """Shifted end in [b - 0.5, b] and its counts.  The candidates b - j hb are ranked by
        min_k |Z_k|/rms_k (rms over the candidates); the best-ranked one whose counts track cleanly
        (integral and parity-consistent) is taken.  The choice depends only on b, so runs sharing a
        nominal end agree on it."""
        cands = end_candidates(b)
        zs = [self._sample(t) for t in cands]
        rms = [math.sqrt(sum(z[k] ** 2 for z in zs) / len(zs)) or 1.0 for k in range(3)]
        ranked = sorted(zip(cands, zs),
                        key=lambda p: (-min(abs(p[1][k]) / rms[k] for k in range(3)), -p[0]))
        first = None
        for t, _ in ranked:
            try:
                raw, ints, ok, par = self._N_at(t)
            except TrackingError:
                self.diag["end_retries"] += 1
                continue
            if ok and par:
                return t, (raw, ints)
            first = first or (t, (raw, ints))
            self.diag["end_retries"] += 1
        if first is None:
            raise SystemExit("no window end near %r admits argument tracking" % b)
        self.flags.add("end_counts_unclean")
        return first

    # ---------------- counting by argument tracking ----------------
    def _track(self, T, max_inc):
        """Continuous change of arg(f, L chi, L chibar) along sigma: 2 -> 1/2 at height T.
        Returns (principal args at 2 + iT, increments summed, number of steps, smallest step)."""
        F = self.ev.values(2.0, T)
        for x in F:   # |F - 1| < 1 on Re s = 2, so Re F > 0 and the principal arg is continuous
            if not x.real > 0:
                raise TrackingError("Re F(2 + iT) not positive at T = %r" % T)
        a2 = [float(x.arg()) for x in F]
        tot = [0.0, 0.0, 0.0]
        sig, step, nsteps, smallest = 2.0, 0.125, 0, 1.0
        while sig > 0.5:
            new = max(0.5, sig - step)
            G = self.ev.values(new, T)
            inc = [float((G[k] / F[k]).arg()) for k in range(3)]
            m = max(abs(x) for x in inc)
            if m >= max_inc:
                step *= 0.5
                if step < MIN_TRACK_STEP:
                    raise TrackingError("tracking step below %g at sigma %r, T %r"
                                        % (MIN_TRACK_STEP, sig, T))
                continue
            for k in range(3):
                tot[k] += inc[k]
            smallest = min(smallest, sig - new)
            sig, F = new, G
            nsteps += 1
            step = min(0.25, step * min(2.0, max(0.5, 0.6 * max_inc / max(m, 1e-9))))
        return a2, tot, nsteps, smallest

    def _N_at(self, T):
        """(raw N_f, N_chi, N_chibar), rounded integers, integrality ok, parity ok) at height T."""
        if T in self.Ncache:
            return self.Ncache[T]
        ra = self.ra
        vt = float(self.ev.vartheta(T))
        for max_inc in (MAX_INC, MAX_INC / 5):
            a2, tot, nsteps, smallest = self._track(T, max_inc)
            raw = ((vt + a2[0] + tot[0]) / PI,
                   (vt + ra["D_chi"] + (a2[1] - ra["arg2_chi"]) + tot[1]) / PI,
                   (vt + ra["D_chibar"] + (a2[2] - ra["arg2_chibar"]) + tot[2]) / PI)
            ints = tuple(int(round(x)) for x in raw)
            ok = all(abs(x - n) < INT_TOL for x, n in zip(raw, ints))
            if ok:
                break
        # parity: N_f is odd iff Z_f(T) < 0; N_chi(bar) odd iff Z(T) < 0 xor e^{-i th} L(1/2,chi) < 0
        z = self.S.get(T) or self.ev.line(T)[0]
        half_neg = ra["rotL_half"] < 0
        par = (ints[0] % 2 == (z[0] < 0), ints[1] % 2 == ((z[1] < 0) != half_neg),
               ints[2] % 2 == ((z[2] < 0) != half_neg))
        res = (raw, ints, ok, all(par))
        self.Ncache[T] = res
        self.diag["N_evals"] += 1
        self.diag["track_steps"] += nsteps
        if smallest < self.diag.get("min_track_step", 1.0):
            self.diag["min_track_step"] = smallest
        return res

    # ---------------- root detection ----------------
    def _zfun(self, ch):
        def fun(t):
            return self.ev.zval(t, ch)
        return fun

    def _known_in(self, ch, a, b):
        L = self.known[ch]
        i = bisect.bisect_right(L, a)
        j = bisect.bisect_left(L, b)
        return L[i:j]

    def _add_known(self, ch, r):
        """Cache a refined root (a root re-found within 2e-9 of a cached one is not added twice)."""
        L = self.known[ch]
        i = bisect.bisect_left(L, r)
        if (i < len(L) and L[i] - r < 2e-9) or (i > 0 and r - L[i - 1] < 2e-9):
            return
        L.insert(i, r)

    def _golden(self, ch, tl, tm, tr, zl, zm, zr):
        """Minimise g = sgn Z over [tl, tr] (sgn = sign of the three samples).  Returns
        ('pair', (left bracket), (right bracket)) if g < 0 is found, else ('dip', t_min, g_min)."""
        sgn = 1.0 if zm > 0 else -1.0
        pts = [(tl, sgn * zl), (tm, sgn * zm), (tr, sgn * zr)]
        self.diag["golden"] += 1

        def g(t):
            v, sure = self.ev.zval(t, ch)
            if not sure:
                self.flags.add("double_root_suspect_" + NAMES[ch])
                v = 0.0
            pts.append((t, sgn * v))
            return sgn * v

        def pair_from(tn):
            left = max((p for p in pts if p[0] < tn and p[1] > 0), key=lambda p: p[0])
            right = min((p for p in pts if p[0] > tn and p[1] > 0), key=lambda p: p[0])
            gn = [p[1] for p in pts if p[0] == tn][0]
            return ("pair", (left[0], tn, sgn * left[1], sgn * gn), (tn, right[0], sgn * gn,
                                                                      sgn * right[1]))

        ts_, _, curv = parabola(tl, tm, tr, sgn * zl, sgn * zm, sgn * zr)
        if curv > 0 and tl < ts_ < tr and ts_ != tm:
            if g(ts_) < 0:
                return pair_from(ts_)
        a, b = tl, tr
        gr = (math.sqrt(5.0) - 1.0) / 2.0
        x1, x2 = b - gr * (b - a), a + gr * (b - a)
        g1, g2 = g(x1), g(x2)
        while True:
            if g1 < 0:
                return pair_from(x1)
            if g2 < 0:
                return pair_from(x2)
            w = b - a
            gmin = min(g1, g2)
            if w < GOLD_TOL or gmin == 0.0:
                break
            if curv > 0 and gmin > GOLD_SAFETY * curv * w * w:
                break
            if g1 < g2:
                b, x2, g2 = x2, x1, g1
                x1 = b - gr * (b - a)
                g1 = g(x1)
            else:
                a, x1, g1 = x1, x2, g2
                x2 = a + gr * (b - a)
                g2 = g(x2)
        tmin, gmin = min(pts, key=lambda p: p[1])
        return ("dip", tmin, gmin)

    def _detect(self, ch, ts):
        """On-line roots of channel ch strictly inside (ts[0], ts[-1]) and the same-sign dips."""
        zs = [self.S[t][ch] for t in ts]
        fun = self._zfun(ch)
        roots, dips = [], []
        for i in range(len(ts) - 1):
            if (zs[i] > 0) != (zs[i + 1] > 0):
                kn = self._known_in(ch, ts[i], ts[i + 1])
                if len(kn) == 1:
                    roots.append(kn[0])
                else:
                    r = brent_root(fun, ts[i], ts[i + 1], zs[i], zs[i + 1])
                    self.diag["brent"] += 1
                    self._add_known(ch, r)
                    roots.append(r)
        for i in range(1, len(ts) - 1):
            zl, zm, zr = zs[i - 1], zs[i], zs[i + 1]
            if not ((zl > 0) == (zm > 0) == (zr > 0)):
                continue
            al, am, ar = abs(zl), abs(zm), abs(zr)
            if not (am < al and am <= ar):
                continue
            tv, gv, curv = parabola(ts[i - 1], ts[i], ts[i + 1], al, am, ar)
            dip = Dip(tv, gv, am / max(al, ar), curv, ts[i - 1], ts[i + 1])
            if am < CLOSE_RATIO * max(al, ar):
                kn = self._known_in(ch, ts[i - 1], ts[i + 1])
                key = (ch, ts[i - 1], ts[i + 1])
                if len(kn) == 2:
                    roots.extend(kn)
                    dip = None
                elif key in self.golden_cache:
                    res = self.golden_cache[key]
                    dip.t, dip.g = res[1], res[2]
                else:
                    res = self._golden(ch, ts[i - 1], ts[i], ts[i + 1], zl, zm, zr)
                    if res[0] == "pair":
                        self.diag["close_pairs"] += 1
                        for (u, v, fu, fv) in res[1:]:
                            r = brent_root(fun, u, v, fu, fv)
                            self.diag["brent"] += 1
                            self._add_known(ch, r)
                            roots.append(r)
                        dip = None
                    else:
                        self.golden_cache[key] = res
                        dip.t, dip.g = res[1], res[2]
            if dip is not None:
                dips.append(dip)
        roots = sorted(set(roots))
        for x, y in zip(roots, roots[1:]):
            if y - x < 1e-8:
                self.flags.add("near_double_root_" + NAMES[ch])
        return roots, dips

    def _redetect(self):
        self.ts = sorted(t for t in self.S if self.T0s <= t <= self.T1s)
        for ch in range(3):
            self.roots[ch], self.dips[ch] = self._detect(ch, self.ts)

    def _count(self, ch, a, b):
        L = self.roots[ch]
        return bisect.bisect_left(L, b) - bisect.bisect_right(L, a)

    def _densify(self, a, b, factor):
        """Re-sample [a, b] with local step <= h/factor."""
        step = self.h_win / factor
        inside = [t for t in self.ts if a <= t <= b]
        new = []
        for u, v in zip(inside, inside[1:]):
            m = int(math.ceil((v - u) / step - 1e-9))
            new.extend(u + j * (v - u) / m for j in range(1, m))
        for t in new:
            self._sample(t)
        self.diag["densified"] += len(new)
        self._redetect()

    def _split(self, a, b):
        """(m, counts at m) for a split height: a sample in the middle half of (a, b) with all three
        |Z| well away from zero (best of up to five whose counts track cleanly), or None."""
        L = b - a
        cand = [t for t in self.ts if a + 0.25 * L <= t <= b - 0.25 * L] or \
               [t for t in self.ts if a < t < b]
        cand.sort(key=lambda t: -min(abs(self.S[t][k]) / self.rms[k] for k in range(3)))
        for t in cand[:5]:
            try:
                raw, ints, ok, par = self._N_at(t)
            except TrackingError:
                continue
            if ok and par:
                return t, (raw, ints)
        return None

    def _bad(self, a, b, Na, Nb):
        """Channels whose counts on (a, b) are inconsistent."""
        bad = []
        for ch in range(3):
            d = Nb[1][ch] - Na[1][ch] - self._count(ch, a, b)
            if (ch > 0 and d != 0) or (ch == 0 and (d < 0 or d % 2)):
                bad.append(ch)
        return bad

    def _repair(self, a, b, Na, Nb, depth=0):
        """Localise an inconsistent count by bisection, then re-sample the short sub-window."""
        if not self._bad(a, b, Na, Nb):
            return True
        self.diag["repairs"] += 1
        nin = sum(1 for t in self.ts if a < t < b)
        if nin > REPAIR_SAMPLES and depth < 24:
            sp = self._split(a, b)
            if sp is not None:
                m, Nm = sp
                r1 = self._repair(a, m, Na, Nm, depth + 1)
                r2 = self._repair(m, b, Nm, Nb, depth + 1)
                return r1 and r2
        for factor in DENSIFY:
            self._densify(a, b, factor)
            if not self._bad(a, b, Na, Nb):
                return True
        return False

    # ---------------- off-line zeros of f ----------------
    def _f_hp(self, z, prec):
        """f at an acb point z (precision prec)."""
        return self.ev.values_s(z, prec)[0]

    def _newton(self, z0, a, b):
        """Newton on f from z0 (complex): prec iterations, then polish at 2 prec with acb points.
        Returns (acb zero in the upper half with Re > 1/2 after mirroring, |f| at 2 prec) or None."""
        self.diag["newton_starts"] += 1
        z = complex(z0)
        h = 1e-5
        try:
            for _ in range(60):
                Fb = self.ev.values(z.real, z.imag)[0]
                if 0 in Fb:                  # zero to working precision: polish
                    break
                F = complex(Fb.mid())
                Fp = (complex(self.ev.values(z.real + h, z.imag)[0].mid())
                      - complex(self.ev.values(z.real - h, z.imag)[0].mid())) / (2 * h)
                if Fp == 0:
                    return None
                step = F / Fp
                if abs(step) > 0.2:
                    step *= 0.2 / abs(step)
                z -= step
                if not (-1.0 < z.real < 2.0 and a - 2.0 < z.imag < b + 2.0):
                    return None
                if abs(step) < 1e-8:
                    break
            else:
                return None
            # polish at 2 prec on acb points (a double cannot hold a zero at height 1e4 to 1e-12)
            hp = self.ev.hi
            with ctx.workprec(hp):
                Z = acb(z.real, z.imag)
                hh = acb(arb(2) ** -40)
            for _ in range(6):
                with ctx.workprec(hp):
                    Zp, Zm = Z + hh, Z - hh
                F, Fpl, Fmi = self._f_hp(Z, hp), self._f_hp(Zp, hp), self._f_hp(Zm, hp)
                with ctx.workprec(hp):
                    st = (F * 2 * hh / (Fpl - Fmi)).mid()
                    Z = (Z - st).mid()
                    small = abs(st) < arb(10) ** -25
                if small:
                    break
            with ctx.workprec(hp):
                if float(Z.real) < 0.5:                      # mirror 1 - conj(z) of a zero
                    Z = acb(1 - Z.real, Z.imag)
            absf = float(abs(self._f_hp(Z, hp)).mid())
        except HeightCeiling:
            self.diag["newton_ceiling"] += 1
            return None
        return Z, absf

    def _accept(self, res, a, b):
        if res is None:
            return False
        Z, absf = res
        s, t = float(Z.real), float(Z.imag)
        if not (absf < ACCEPT_F and s > 0.5 + ACCEPT_RE and s < 2.0 and a < t < b):
            return False
        for (s2, t2, _, _) in self.off:
            if abs(complex(s, t) - complex(s2, t2)) <= DISTINCT:
                return False
        with ctx.workprec(self.ev.hi):
            hp = (Z.real.str(25, radius=False), Z.imag.str(25, radius=False))
        self.off.append((s, t, absf, hp))
        self.off.sort(key=lambda x: x[1])
        return True

    def _found_in(self, a, b):
        return sum(1 for o in self.off if a < o[1] < b)

    def _try_dips(self, a, b, need):
        """Newton from the wrong-sign extrema of Z_f in (a, b), deepest first."""
        cands = sorted((d for d in self.dips[0] if a < d.t < b and d.t not in self.tried),
                       key=lambda d: d.ratio)
        for d in cands:
            if self._found_in(a, b) >= need:
                return
            self.tried.add(d.t)
            if any(abs(o[1] - d.t) < 1e-3 for o in self.off):
                continue
            starts = list(NEWTON_D)
            de = d.d_est()
            if de is not None and 1e-4 < de < 0.5:
                starts.insert(0, de)
            for dd in starts:
                if self._accept(self._newton(complex(0.5 + dd, d.t), a, b), a, b):
                    break

    def _grid_search(self, a, b, need, stage):
        """|f| on a sigma x t grid over (a, b); Newton from the grid's local minima, smallest first."""
        lo, hi, ds = stage
        sig = [lo + j * ds for j in range(int(round((hi - lo) / ds)) + 1)]
        nt = max(2, int(math.ceil((b - a) / GRID_DT)) + 1)
        tt = [a + (b - a) * i / (nt - 1) for i in range(nt)]
        V = [[float(abs(self.ev.values(s, t)[0])) for s in sig] for t in tt]
        self.diag["grid_points"] += len(sig) * len(tt)
        mins = []
        for i in range(len(tt)):
            for j in range(len(sig)):
                v = V[i][j]
                nb = [V[i + di][j + dj] for di in (-1, 0, 1) for dj in (-1, 0, 1)
                      if (di or dj) and 0 <= i + di < len(tt) and 0 <= j + dj < len(sig)]
                if all(v <= x for x in nb):
                    mins.append((v, sig[j], tt[i]))
        mins.sort()
        for v, s, t in mins:
            if self._found_in(a, b) >= need:
                return
            self._accept(self._newton(complex(s, t), a, b), a, b)

    def _locate(self, a, b, Na, Nb, depth=0):
        """Make the number of located off-line zeros in (a, b) match (Delta N_f - n_f)/2."""
        e = Nb[1][0] - Na[1][0] - self._count(0, a, b)
        if e < 0 or e % 2:
            self.flags.add("count_f")
            return
        missing = e // 2 - self._found_in(a, b)
        if missing <= 0:
            if missing < 0:
                self.flags.add("offline_excess")
            return
        self._try_dips(a, b, e // 2)
        if self._found_in(a, b) >= e // 2:
            return
        if b - a > LOC_MIN_LEN and depth < 24:
            sp = self._split(a, b)
            if sp is not None:
                m, Nm = sp
                self.diag["locate_splits"] += 1
                self._locate(a, m, Na, Nm, depth + 1)
                self._locate(m, b, Nm, Nb, depth + 1)
                return
        # short sub-window still missing zeros: hidden on-line pair?  then |f| grids
        self._densify(a, b, DENSIFY[0])
        e = Nb[1][0] - Na[1][0] - self._count(0, a, b)
        if e < 0 or e % 2:
            self.flags.add("count_f")
            return
        self._try_dips(a, b, e // 2)
        for stage in GRID_STAGES:
            if self._found_in(a, b) >= e // 2:
                return
            self._grid_search(a, b, e // 2, stage)
        if self._found_in(a, b) < e // 2:
            self.flags.add("offline_missing")

    # ---------------- one window ----------------
    def _window(self, k, T0s, N0, carry):
        """Process window k from the shared start T0s (counts N0, carried samples) and return its
        record; leaves the samples above the new end in self._carry for window k + 1."""
        t_start = time.time()
        ev0 = dict(self.ev.nevals)
        self.ev.reset_selftest()
        self.flags, self.start_flags = set(self.start_flags), set()
        self.diag = collections.Counter()
        self.Ncache = {}
        self.golden_cache = {}
        self.known = [[], [], []]
        self.roots, self.dips = [[], [], []], [[], [], []]
        self.off = []
        self.tried = set()
        a, b = self.ends[k], self.ends[k + 1]
        self.h_win = end_step(b)[1]

        # 1. samples: the carried part of the previous grid in [T0s, a], then this window's grid
        self.S = dict(carry)
        for t in window_grid(a, b):
            self._sample(t)
        self.Ncache[T0s] = (N0[0], N0[1], True, True)
        self.T0s = T0s

        # 2. shifted end and its counts (argument principle by phase tracking)
        T1s, N1 = self._end_and_counts(b)
        self.T1s = T1s
        self._carry = {t: self.S[t] for t in end_candidates(b) if t >= T1s}
        inwin = [self.S[t] for t in self.S if T0s <= t <= T1s]
        self.rms = [math.sqrt(sum(z[ch] ** 2 for z in inwin) / len(inwin)) or 1.0
                    for ch in range(3)]
        self._redetect()
        N0p = (N0[0], N0[1])

        # 3. accounting (repair by localisation + re-sampling when inconsistent)
        if self._bad(T0s, T1s, N0p, N1):
            self._repair(T0s, T1s, N0p, N1)
        for ch in self._bad(T0s, T1s, N0p, N1):
            self.flags.add("count_" + NAMES[ch])
        e = N1[1][0] - N0[1][0] - self._count(0, T0s, T1s)

        # 4. off-line zeros
        if e > 0 and e % 2 == 0:
            self._locate(T0s, T1s, N0p, N1)
        e = N1[1][0] - N0[1][0] - self._count(0, T0s, T1s)   # after any re-sampling
        K = e // 2 if (e >= 0 and e % 2 == 0) else None
        if K is not None and len(self.off) != K:
            self.flags.add("offline_missing" if len(self.off) < K else "offline_excess")
        if self.ev.st_im >= 1.0:
            self.flags.add("selftest_im")
        if self.ev.st_id >= 1.0:
            self.flags.add("selftest_id")

        def npair(N, i):
            return [N[0][i], N[1][i]]

        ev1 = self.ev.nevals
        rec = {
            "format": FORMAT, "k": k, "params": self.params,
            "T0_nom": a, "T1_nom": b, "T0": T0s, "T1": T1s,
            "Nf0": npair(N0p, 0), "Nf1": npair(N1, 0),
            "Nchi0": npair(N0p, 1), "Nchi1": npair(N1, 1),
            "Nchib0": npair(N0p, 2), "Nchib1": npair(N1, 2),
            "roots_f": [r for r in self.roots[0] if T0s < r < T1s],
            "roots_chi": [r for r in self.roots[1] if T0s < r < T1s],
            "roots_chibar": [r for r in self.roots[2] if T0s < r < T1s],
            "offline": [[o[0], o[1], o[2]] for o in self.off],
            "offline_hp": [list(o[3]) for o in self.off],
            "K": K if K is not None else -1,
            "flags": sorted(self.flags),
            "seconds": round(time.time() - t_start, 3),
            "n_samples": len(self.ts),
            "evals": {str(p): ev1[p] - ev0.get(p, 0) for p in sorted(ev1)},
            "selftest": {"max_im_ratio": self.ev.st_im, "max_id_ratio": self.ev.st_id},
            "diag": dict(self.diag),
        }
        return rec


# ---------------------------------------------------------------------------------------------
# Files
# ---------------------------------------------------------------------------------------------
def load_records(path):
    """Complete records of a census file, the byte length they occupy, and whether a torn
    (unterminated or unparsable) trailing line follows them."""
    recs, good = [], 0
    if not os.path.exists(path):
        return recs, 0, False
    with open(path, "rb") as fh:
        data = fh.read()
    pos = 0
    while pos < len(data):
        nl = data.find(b"\n", pos)
        if nl < 0:
            break
        try:
            recs.append(json.loads(data[pos:nl].decode()))
        except ValueError:
            break
        pos = nl + 1
        good = pos
    return recs, good, good < len(data)


def append_record(path, rec):
    line = json.dumps(rec, separators=(",", ":")) + "\n"
    with open(path, "a") as fh:
        fh.write(line)
        fh.flush()
        os.fsync(fh.fileno())


# ---------------------------------------------------------------------------------------------
# Summary, timing, plan
# ---------------------------------------------------------------------------------------------
def summary(paths):
    """Aggregate census files: continuity of shared ends and counts, global accounting, flags,
    off-line zeros."""
    recs = []
    for p in paths:
        r, _, torn = load_records(p)
        if torn:
            print("warning: %s has a torn trailing line (ignored)" % p, file=sys.stderr)
        recs.extend(r)
    recs.sort(key=lambda r: r["T0"])
    problems = []
    for r1, r2 in zip(recs, recs[1:]):
        if r1["T1"] != r2["T0"]:
            problems.append("gap/overlap between %r and %r" % (r1["T1"], r2["T0"]))
        for a_, b_ in (("Nf1", "Nf0"), ("Nchi1", "Nchi0"), ("Nchib1", "Nchib0")):
            if r1[a_][1] != r2[b_][1]:
                problems.append("%s/%s mismatch at %r" % (a_, b_, r1["T1"]))
    out = {"windows": len(recs)}
    if recs:
        nf = sum(len(r["roots_f"]) for r in recs)
        nc = sum(len(r["roots_chi"]) for r in recs)
        ncb = sum(len(r["roots_chibar"]) for r in recs)
        off = [o for r in recs for o in r["offline"]]
        dNf = recs[-1]["Nf1"][1] - recs[0]["Nf0"][1]
        dNc = recs[-1]["Nchi1"][1] - recs[0]["Nchi0"][1]
        dNcb = recs[-1]["Nchib1"][1] - recs[0]["Nchib0"][1]
        out.update({
            "T_start": recs[0]["T0"], "T_end": recs[-1]["T1"],
            "N_f": [recs[0]["Nf0"][1], recs[-1]["Nf1"][1]],
            "N_chi": [recs[0]["Nchi0"][1], recs[-1]["Nchi1"][1]],
            "N_chibar": [recs[0]["Nchib0"][1], recs[-1]["Nchib1"][1]],
            "online_roots": {"f": nf, "chi": nc, "chibar": ncb},
            "offline_count": len(off), "K_sum": sum(r["K"] for r in recs if r["K"] >= 0),
            "windows_K_undefined": [r["k"] for r in recs if r["K"] < 0],
            "accounting_f": dNf == nf + 2 * len(off),
            "accounting_chi": dNc == nc, "accounting_chibar": dNcb == ncb,
            "flagged_windows": [[r["k"], r["T0"], r["T1"], r["flags"]] for r in recs if r["flags"]],
            "offline": off,
            "seconds": round(sum(r["seconds"] for r in recs), 1),
            "evals": dict(sum((collections.Counter(r["evals"]) for r in recs),
                              collections.Counter())),
            "max_selftest_im_ratio": max(r["selftest"]["max_im_ratio"] for r in recs),
            "max_selftest_id_ratio": max(r["selftest"]["max_id_ratio"] for r in recs),
        })
    out["continuity_problems"] = problems
    return out


def time_evaluator(heights, reps=20, prec=53):
    """Wall time of one evaluator call (four Hurwitz values, vartheta, the three rotated values) at
    each height: median and minimum over reps nearby heights.  Also an accuracy report at the same
    points: largest ball radius of Z at prec, largest |Z(prec) - Z(2 prec)|, and the self-test
    maxima.  Evaluation only -- no counting or zero search of any kind."""
    res = {}
    for t in heights:
        ev = Evaluator(prec, 1)
        ev.rotated(t)             # warm-up
        ts, rad, dev = [], 0.0, 0.0
        for r in range(reps):
            x = t + 0.0137 * r
            t0 = time.perf_counter()
            R = ev.rotated(x)
            ts.append(time.perf_counter() - t0)
            Rh = ev.rotated(x, ev.hi)
            for k in range(3):
                rad = max(rad, float(R[k].real.rad()))
                dev = max(dev, abs(float(R[k].real) - float(Rh[k].real)))
        ts.sort()
        res[t] = {"median_ms": 1e3 * ts[len(ts) // 2], "min_ms": 1e3 * ts[0],
                  "max_ball_radius": rad, "max_dev_vs_2prec": dev,
                  "selftest_im_ratio": ev.st_im, "selftest_id_ratio": ev.st_id}
    return res


def zeros_below(T):
    """Main term of N(T) for f and for each channel: vartheta(T)/pi ~ (T/2pi) log(5T/2pi e) + 1/8."""
    if T <= 0:
        return 0.0
    return (T / (2.0 * PI)) * (math.log(5.0 * T / (2.0 * PI)) - 1.0) + 0.125


def plan(t0, t1, dt, ncores, evals_per_zero, timing):
    """Cost model: evaluations per unit height = evals_per_zero x zero density, times the evaluator
    cost interpolated (power law, log-log) from the timing table; balanced split for ncores."""
    hs = sorted(timing)
    cs = [timing[h] for h in hs]

    def cost(t):
        if t <= hs[0]:
            return cs[0] * (t / hs[0]) ** max(0.0, math.log(cs[1] / cs[0]) / math.log(hs[1] / hs[0]))
        for (h0, c0), (h1, c1) in zip(zip(hs, cs), zip(hs[1:], cs[1:])):
            if t <= h1:
                p = math.log(c1 / c0) / math.log(h1 / h0)
                return c0 * (t / h0) ** p
        p = math.log(cs[-1] / cs[-2]) / math.log(hs[-1] / hs[-2])
        return cs[-1] * (t / hs[-1]) ** p

    ends = nominal_ends(t0, t1, dt)
    work = []
    for a, b in zip(ends, ends[1:]):
        nz = zeros_below(b) - zeros_below(a)
        work.append(evals_per_zero * nz * cost(0.5 * (a + b)) / 1e3)   # seconds
    total = sum(work)
    target = total / ncores
    splits, acc, parts = [ends[0]], 0.0, []
    for i, w in enumerate(work):
        acc += w
        if acc >= target * len(splits) and len(splits) < ncores and i < len(work) - 1:
            splits.append(ends[i + 1])
    splits.append(ends[-1])
    for a, b in zip(splits, splits[1:]):
        i0, i1 = ends.index(a), ends.index(b)
        parts.append({"t0": a, "t1": b, "seconds": sum(work[i0:i1])})
    return {"total_seconds_one_core": total, "zeros_per_channel": zeros_below(t1) - zeros_below(t0),
            "parts": parts, "wall_seconds_parallel": max(p["seconds"] for p in parts)}


# ---------------------------------------------------------------------------------------------
def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--t0", type=float)
    ap.add_argument("--t1", type=float)
    ap.add_argument("--out")
    ap.add_argument("--dt", type=float, default=25.0)
    ap.add_argument("--prec", type=int, default=53)
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--timing", action="store_true")
    ap.add_argument("--heights", default="1000,3000,5000,10000")
    ap.add_argument("--reps", type=int, default=20)
    ap.add_argument("--summary", nargs="+")
    ap.add_argument("--plan", type=int)
    ap.add_argument("--evals-per-zero", type=float, default=34.0)   # measured on [64, 200]
    ap.add_argument("--timing-file")
    args = ap.parse_args(argv)

    if args.selftest:
        sign, rep = selftest(args.prec)
        ev = Evaluator(args.prec, sign or 1)
        rep["real_axis"] = real_axis_data(ev)
        rep["theta_sign"] = sign
        print(json.dumps(rep, indent=1))
        return 0 if sign is not None else 1
    if args.timing:
        hs = [float(x) for x in args.heights.split(",")]
        print(json.dumps(time_evaluator(hs, args.reps, args.prec), indent=1))
        return 0
    if args.summary:
        print(json.dumps(summary(args.summary), indent=1))
        return 0
    if args.plan:
        if args.t0 is None or args.t1 is None:
            ap.error("--plan needs --t0 and --t1")
        if args.timing_file:
            with open(args.timing_file) as fh:
                tim = {float(k): v["median_ms"] for k, v in json.load(fh).items()}
        else:
            tim = {k: v["median_ms"] for k, v in
                   time_evaluator([float(x) for x in args.heights.split(",")], args.reps,
                                  args.prec).items()}
        print(json.dumps(plan(args.t0, args.t1, args.dt, args.plan, args.evals_per_zero, tim),
                         indent=1))
        return 0
    if args.t0 is None or args.t1 is None or args.out is None:
        ap.error("a census needs --t0, --t1 and --out")
    if not (0 < args.t0 < args.t1) or args.dt < 2.0:
        ap.error("need 0 < t0 < t1 and dt >= 2")
    Census(args.t0, args.t1, args.dt, args.prec, args.out).run()
    return 0


if __name__ == "__main__":
    sys.exit(main())
