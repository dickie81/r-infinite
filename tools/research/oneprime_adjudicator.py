#!/usr/bin/env python3
"""The sigma adjudicator (committed by round 243, F5): the
pure-t-space computation that adjudicated the three S-pipeline
architectures of Stage B1 round 3. It applies T to the certified
cos-24 extremal at even delta 0.9 via the u-integral operator form
-- no r-grids, no far tails, projection automatic -- and prints
rho and sigma. Its sigma anchors gF2 in oneprime_fractional.py.

History: the adjudication originally ran as an uncommitted
scratchpad script (round-243 finding F5 -- session runs are
drafting until they land in committed code); this file is that
script with its one known defect fixed (the tail counterterm's
sign, whose slip demonstrated the sigma-invariance lemma: an
additive c*phi error in T phi leaves sigma^2 exactly invariant).

Expected output (float64): sigma = 2.7527e-3 -- THE anchor (the
sigma-invariance lemma protects it against additive-phi errors;
the round-3 t-space pipeline reproduces it at rel 3.6e-5, the
grid pipeline at rel 2e-4). rho ~ +1.83e-5, within ~2e-7 of the
section lambda_1 = 1.8439e-5: rho is NOT invariance-protected and
carries the ~1e-8-relative errors of the O(9)-sized T-values, so
it is a consistency readout, not an anchor.
"""
import math, sys, os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from oneprime_bridge import build_Q64
from scipy.linalg import eigh

LOG2 = math.log(2.0)
C2 = math.sqrt(2.0)*LOG2
LG = math.log(4*math.pi) + 0.5772156649015329

delta, a = 0.9, 0.45

Q, G, _, _, _ = build_Q64(delta, parity="even")
ev, V = eigh(Q, G)
c = V[:, 0]
w = (np.arange(24) + 0.5)*np.pi/a

def phi(t):
    t = np.atleast_1d(t)
    return np.where(np.abs(t) <= a,
                    (c[:, None]*np.cos(w[:, None]*t[None, :]))
                    .sum(0), 0.0)

xg, wg = np.polynomial.legendre.leggauss(96)

def glseg(fn, lo, hi):
    x = 0.5*(hi - lo)*xg + 0.5*(hi + lo)
    return 0.5*(hi - lo)*np.sum(wg*fn(x))

def T_phi(t):
    U = 2*a + 1.0
    pts = ([0.0] + [k for k in sorted({a - t, a + t})
                    if 1e-12 < k < U] + [U])
    def integ(u):
        return (np.exp(u/2)*(phi(t + u) + phi(t - u))/2
                - phi(np.array([t]))[0])/np.sinh(u)
    s = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        if lo == 0.0:
            llo, lhi = math.log(1e-13), math.log(hi)
            s += glseg(lambda v: integ(np.exp(v))*np.exp(v),
                       llo, lhi)
        else:
            s += glseg(integ, lo, hi)
    # the tail counterterm enters with PLUS sign (the scratch
    # version's minus was the sigma-invariant slip)
    val = (-LG*phi(np.array([t]))[0] - s
           + phi(np.array([t]))[0]*math.log(1/math.tanh(U/2)))
    val += -(C2/2)*(phi(np.array([t + LOG2]))[0]
                    + phi(np.array([t - LOG2]))[0])
    return val

xg2, wg2 = np.polynomial.legendre.leggauss(200)
tt, wt = a*xg2, a*wg2
vchi_phi = float(np.sum(wt*np.cosh(tt/2)*phi(tt)))
nphi = float(np.sum(wt*phi(tt)**2))

segpts = sorted({-a, a, a - LOG2, LOG2 - a})
tnodes, tws = [], []
for lo, hi in zip(segpts[:-1], segpts[1:]):
    tnodes.extend(0.5*(hi - lo)*xg2 + 0.5*(hi + lo))
    tws.extend(0.5*(hi - lo)*wg2)
tnodes, tws = np.array(tnodes), np.array(tws)

if __name__ == "__main__":
    Tv = np.array([T_phi(t) for t in tnodes])
    Tv += 2*vchi_phi*np.cosh(tnodes/2)
    rho = float(np.sum(tws*phi(tnodes)*Tv))/nphi
    Spp = float(np.sum(tws*Tv*Tv))/nphi
    sig = math.sqrt(max(Spp - rho*rho, 0.0))
    print(f"adjudicator: rho {rho:.6e}  sigma {sig:.6e}  "
          f"(anchor 2.7527e-3)", flush=True)
    assert abs(rho - 1.8439e-5) < 5e-7, \
        "rho outside its consistency window"
    assert abs(sig/2.7527e-3 - 1) < 1e-3, "sigma off the anchor"
    print("adjudicator anchors verified", flush=True)
