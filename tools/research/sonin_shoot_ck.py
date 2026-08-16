#!/usr/bin/env python3
"""1bd rebuild: the C-M shooting instrument (arXiv:2112.05500).
W_lam = -d/dx (lam^2-x^2) d/dx + (2 pi lam)^2 x^2 on (lam, inf);
analytic Frobenius branch at x = lam (Eq 17 kills the log branch);
tails ~ sin(2 pi lam x)/x (even, Eq 18) or cos(2 pi lam x)/x (odd,
Eq 19). Eigenvalues mu < 0; E = sqrt(-mu); s = 2E. Harvest targets:
c0(lam=1) = 1.3809 +- 0.0029 (vs log 4); c0(lam=sqrt2) = 0.6772 +-
0.0077 (vs log 2); merged count of s_n <= 240 at lam=sqrt2 = 103."""
import numpy as np, math, time
from scipy.integrate import solve_ivp
def series_start(lam, mu, t0, nterms=24):
    # u = sum a_k t^k, t = x - lam; ((t(t+2lam))u')' + (q - mu)u = 0
    # q(lam+t) = (2 pi lam)^2 (lam+t)^2 = q0 + q1 t + q2 t^2
    w = (2*math.pi*lam)**2
    q0 = w*lam*lam - mu; q1 = 2*w*lam; q2 = w
    a = [1.0, 0.0] + [0.0]*(nterms - 1)
    # expand: sum_k [ (k+1)^2*2lam*a_{k+1} + k^2*a_k ] t^k + (q0 a + q1 a_-1 + q2 a_-2) = 0
    # from ((t^2+2lam t)u')' = sum k^2 a_k t^k ... derive: d/dt[(t^2+2lam t) sum k a_k t^{k-1}]
    #  = d/dt[ sum k a_k (t^{k+1} + 2lam t^k) ] = sum k(k+1) a_k t^k + 2lam k^2 a_k t^{k-1}
    # coefficient of t^k: k(k+1)a_k + 2lam (k+1)^2 a_{k+1} + q0 a_k + q1 a_{k-1} + q2 a_{k-2} = 0
    a[1] = -(q0*a[0])/(2*lam)
    for k in range(1, nterms):
        rhs = k*(k+1)*a[k] + q0*a[k] + (q1*a[k-1] if k >= 1 else 0.0) + (q2*a[k-2] if k >= 2 else 0.0)
        a[k+1] = -rhs/(2*lam*(k+1)**2)
    u = sum(a[k]*t0**k for k in range(nterms + 1))
    up = sum(k*a[k]*t0**(k-1) for k in range(1, nterms + 1))
    return u, up
def AB(lam, mu, X=110.0, t0=0.04):
    u0, up0 = series_start(lam, mu, t0)
    w = (2*math.pi*lam)**2
    def rhs(x, y):
        u, up = y
        p = x*x - lam*lam
        return [up, ((mu - w*x*x)*u - 2*x*up)/p]
    sol = solve_ivp(rhs, (lam + t0, X), [u0, up0], rtol=1e-10, atol=1e-300, method="RK45", dense_output=False)
    u, up = sol.y[0][-1], sol.y[1][-1]
    v = X*u; vp = u + X*up
    th = 2*math.pi*lam*X; k = 2*math.pi*lam
    A = v*math.sin(th) + (vp/k)*math.cos(th)
    B = v*math.cos(th) - (vp/k)*math.sin(th)
    nrm = math.hypot(A, B)
    return A/nrm, B/nrm
import json, os
CKDIR = "/home/user/r-infinite/tools/research/checkpoints"
def ck_path(key):
    return os.path.join(CKDIR, "sonin_" + key.replace(":", "_").replace(".", "p") + ".json")
def load_key(key):
    try: return json.load(open(ck_path(key)))
    except Exception: return None
def save_key(key, st):
    json.dump(st, open(ck_path(key), "w"), indent=0)
def find_eigs(lam, parity, Emax, dE=0.18):
    # even: B = 0; odd: A = 0 -- resumable: state under key lam:parity
    key = f"{lam:.6f}:{parity}"
    st = load_key(key) or {"E_done": 0.6, "eigs": [], "prev": None}
    disc = (lambda a, b: b) if parity == "even" else (lambda a, b: a)
    eigs = list(st["eigs"]); prev = tuple(st["prev"]) if st["prev"] else None
    E = st["E_done"]
    if prev is None and E <= 0.6:
        a, b = AB(lam, -0.6*0.6); prev = (0.6, disc(a, b)); E = 0.6
    nsave = 0
    while E < Emax:
        E = min(E + dE, Emax)
        a, b = AB(lam, -E*E)
        d = disc(a, b)
        if prev[1]*d < 0:
            lo, hi = prev[0], E
            for _ in range(40):
                mid = (lo + hi)/2
                am, bm = AB(lam, -mid*mid)
                dm = disc(am, bm)
                if prev[1]*dm < 0: hi = mid
                else: lo = mid
            eigs.append((lo + hi)/2)
        prev = (E, d)
        nsave += 1
        if nsave % 25 == 0:
            save_key(key, {"E_done": E, "eigs": eigs, "prev": list(prev)})
    save_key(key, {"E_done": Emax, "eigs": eigs, "prev": list(prev), "complete": True})
    return np.array(eigs)
def fit_c0(eigs, lam):
    # n = (E/2pi)(log(E/2pi) - 1 + c0) + C  -> lsq in (c0, C)
    E = np.array(eigs); n = np.arange(1, len(E) + 1)
    base = (E/(2*math.pi))*(np.log(E/(2*math.pi)) - 1)
    M = np.column_stack([E/(2*math.pi), np.ones(len(E))])
    (c0, C), *_ = np.linalg.lstsq(M, n - base, rcond=None)
    resid = n - base - M @ [c0, C]
    return c0, C, float(np.sqrt(np.mean(resid**2)))
import sys
if len(sys.argv) == 3:
    lam = 1.0 if sys.argv[1] == "1" else math.sqrt(2)
    find_eigs(lam, sys.argv[2], 120.0)
    print(f"pass complete: lam={lam:.4f} {sys.argv[2]}", flush=True)
    raise SystemExit(0)
t0 = time.time()
for lam, label, target in ((1.0, "log4", math.log(4)), (math.sqrt(2), "log2", math.log(2))):
    kv = f"{lam:.6f}:even"; ko = f"{lam:.6f}:odd"
    sv = load_key(kv); so = load_key(ko)
    if not (sv and sv.get("complete") and so and so.get("complete")):
        print(f"lam={lam:.4f}: passes incomplete", flush=True); continue
    ev = np.array(sv["eigs"]); od = np.array(so["eigs"])
    c0e, Ce, re_ = fit_c0(ev, lam)
    c0o, Co, ro_ = fit_c0(od, lam)
    print(f"lam={lam:.4f}: even {len(ev)} eigs, c0 = {c0e:.4f} (rms {re_:.3f}); "
          f"odd {len(od)} eigs, c0 = {c0o:.4f} (rms {ro_:.3f}); "
          f"mean c0 = {(c0e+c0o)/2:.4f} vs {label} = {target:.4f}", flush=True)
    if abs(lam - math.sqrt(2)) < 1e-9:
        s = np.sort(np.concatenate([2*ev, 2*od]))
        print(f"  merged: {len(s)} s_n total; {int((s <= 240).sum())} below 240 "
              f"(banked 103); first five s: {np.round(s[:5], 3)}", flush=True)
        np.save("/tmp/claude-0/-home-user-r-infinite/2640f710-2e63-5a66-b23b-f6146b8d7017/scratchpad/s_dirac.npy", s)
print(f"done in {(time.time()-t0)/60:.1f} min", flush=True)
