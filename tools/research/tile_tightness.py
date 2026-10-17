"""THE TILE'S TIGHTNESS (owner: "Investigate the tile"; Addendum 422). A research
probe -- not a tower member, not cited by the paper; float64; nothing certified.
The semi-local
tile S = {inf} u {p <= P} defines the S-local Weil form Q_S.  On its
window (support length delta below the next prime-power lag log q) Q_S IS
the full functional; past the window it is the wrong form.  Measured
here, float64 (twoprime_recon's operator generalised to arbitrary
(lag, weight) terms, base 0.012): per parity, the S-form's ground state
lambda_1^S(delta) past the window's end, the first negative
(delta_1(S) = log q + eps_1), and the decomposition on the S ground
state c:  lambda_1^S = Q_full(c) - Q_q(c)  (Q_q the missing q-term's form,
= -C_q h_c(log q)), plus the edge value g(a)^2/|g|^2 -- the tradeoff that
sets eps_1.  Scratch research probe; nothing certified.
Usage: tile_tightness.py [base]"""
import sys, math, json, time
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import twoprime_recon as R

LOG2, LOG3, LOG4 = math.log(2), math.log(3), math.log(4)
def term(n):
    """(lag, weight) for the prime power n: (log n, 2 Lambda(n)/sqrt n)."""
    p = {2: 2, 3: 3, 4: 2, 5: 5}[n]
    return (math.log(n), 2.0*math.log(p)/math.sqrt(n))

def apply_T_terms(md, terms, base):
    a, parity = md.a, md.parity
    kinks = tuple(sorted({min(max(lag - a, 0.0), a) for lag, w in terms}))
    tn, tw = R.gl_panels(0.0, a, sing=kinks + (a,), base=base)
    B = md.t_eval(tn)
    TB = -R.LG4PI*B.copy()
    f = np.cos if parity == "even" else np.sin
    for k, t in enumerate(tn):
        bt = B[:, k]
        acc = np.zeros(md.n)
        for lo, hi, sing in (((0.0, a - t, (a - t,))), ((a - t, a + t, (a - t, a + t)))):
            u, wu = R.gl_panels(lo, hi, sing=sing, base=base)
            if len(u) == 0:
                continue
            A = (np.exp(u/2) - 1)/np.sinh(u)
            both_in = (t + u <= a) & (t - u >= -a)
            Bp = md.t_eval(t + u); Bm = md.t_eval(t - u)
            Dfull = (Bp + Bm)/2 - bt[:, None]
            Dh = -2*f(md.w[:, None]*t)*np.sin(md.w[:, None]*u[None, :]/2)**2
            D = np.where(both_in[None, :], np.vstack([Dh, Dfull[md.nharm:]]), Dfull)
            acc += bt*np.sum(A*wu)
            acc += (D*(np.exp(u/2)/np.sinh(u)*wu)[None, :]).sum(1)
        TB[:, k] -= acc
        TB[:, k] += bt*math.log(1.0/math.tanh((a + t)/2))
    Tq = {}
    for lag, w in terms:
        Tq[lag] = -(w/2)*(md.t_eval(tn + lag) + md.t_eval(tn - lag))
        TB += Tq[lag]
    chi = (np.cosh(tn/2) if parity == "even" else np.sinh(tn/2))
    v = 2*(B*(tw*chi)[None, :]).sum(1)
    TB += R.psign(parity)*2*np.outer(v, chi)
    return tn, tw, B, TB, Tq

def cell(a, parity, S_terms, full_terms, base):
    md = R.Modes(a, parity)
    tn, tw, B, TBf, Tq = apply_T_terms(md, full_terms, base)
    missing = [t for t in full_terms if t not in S_terms]
    TBs = TBf.copy()
    for lag, w in missing:
        TBs -= Tq[lag]
    N = 2*(B*tw[None, :]) @ B.T
    d = 1.0/np.sqrt(np.diag(N))
    ev, U = np.linalg.eigh(d[:, None]*N*d[None, :])
    keep = ev > 1e-4
    Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T*d[None, :])
    Bw = Wh @ B
    NA = 2*(Bw*tw[None, :]) @ Bw.T
    def M(TB):
        TBw = Wh @ TB; MA = 2*(Bw*tw[None, :]) @ TBw.T; return (MA + MA.T)/2
    MS, MF = M(TBs), M(TBf)
    NA = (NA + NA.T)/2
    lam, vec = R.scipy_eigh(MS, NA)
    lamF = R.scipy_eigh(MF, NA, eigvals_only=True)
    c = vec[:, 0]; nn = float(c @ NA @ c)
    qS = float(c @ MS @ c)/nn; qF = float(c @ MF @ c)/nn
    craw = Wh.T @ c
    ga = float(craw @ md.t_eval(np.array([a]))[:, 0])
    return dict(lam1_S=float(lam[0]), lam2_S=float(lam[1]), lam1_full=float(lamF[0]),
                qS=qS, qF=qF, q_missing=qF - qS, edge2=ga*ga/nn, dim=int(NA.shape[0]))

if __name__ == "__main__":
    base = float(sys.argv[1]) if len(sys.argv) > 1 else 0.012
    T2, T3, T4 = term(2), term(3), term(4)
    plan = [("S={inf}", [], [T2], LOG2, [0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4]),
            ("S={inf,2}", [T2], [T2, T3], LOG3, [0.002, 0.005, 0.01, 0.015, 0.02, 0.025, 0.03, 0.04, 0.05, 0.07, 0.1]),
            ("S={inf,2,3}", [T2, T3], [T2, T3, T4], LOG4, [0.005, 0.01, 0.02, 0.03, 0.05, 0.07, 0.1, 0.15, 0.2])]
    out = {}
    print(f"tile tightness, base {base}; columns: delta  eps=delta-logq  lam1_S  lam1_full  Q_full(c_S)  Q_missing(c_S)  g(a)^2/|g|^2  lam2_S", flush=True)
    for name, S, F, lq, epss in plan:
        for par in ("even", "odd"):
            print(f"-- {name} {par}: window ends at log q = {lq:.4f}", flush=True)
            for e in epss:
                d = lq + e; t0 = time.time()
                r = cell(d/2, par, S, F, base)
                out[f"{name}:{par}:{d:.4f}"] = r
                print(f"   {d:.4f} {e:6.3f} {r['lam1_S']:+.4e} {r['lam1_full']:+.4e} {r['qF']:+.4e} {r['q_missing']:+.4e} {r['edge2']:.3e} {r['lam2_S']:+.3e}  ({time.time()-t0:.0f}s)", flush=True)
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'checkpoints', f'tile_tightness_base{base}.json'), 'w'), indent=1)
    print("done", flush=True)
