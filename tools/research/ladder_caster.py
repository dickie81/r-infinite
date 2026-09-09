#!/usr/bin/env python3
"""Keyed producer: THE LADDER'S CASTER at the seven cells (Theorem 1bu's substrate). From the true form's Gram
(weil_prime_gram, the even cosine basis on [-a, a], delta = 2a) at the 1bn/1br cells, the lowest eigenvectors
(flint's approximate eigensolver on the midpoints at prec bits) and their transforms
    ghat(r) = 2 sin(r a) sum_k (-1)^k v_k r/(r^2 - omega_k^2),   omega_k = k pi/a
(the cosine coefficients are the Nyquist samples ghat(omega_k) = (-1)^k a v_k). Stored per cell:

THE GROUND STATE. ln lambda_1 (the approximate eigenvalue), ln ghat_1(0)^2, the curvature kappa' = sum over the
transform's zeros of 1/tau^2 = -ghat_1''(0)/(2 ghat_1(0)) (arb finite differences), the second moment <r^2> of
ghat_1^2, the DODGING EDGE (the real zeros of ghat_1 on (0, 2.2 T_0) at step 0.05 refined by bisection: the first
zeta zero missed and the first zero that is not a zeta zero, both from the double-precision list within 0.05),
and the EXTERIOR PROFILE on the 800 zeros known to 100 digits (checkpoints/zeta_zeros_800_100dps.json, data):
w_gamma = ghat_1(gamma)^2 in arb, the zero side ln(2 sum w) against the prime side, the balayage formula's
minimum F(T*) = min_T [4 sum_{gamma<T} arccosh(T/gamma) - delta T] on the double list, and the anatomy of
1bm(v)'s c(delta) = ln lambda_1 - F(T*) = [ln ghat_1(0)^2] + [ln(2 w_max/ghat_1(0)^2) - F(T*)] + [ln(sum w/w_max)]
+ [the far tail beyond the 800]: origin value, peak excess over the balayage level, effective count.

THE DEEP RUNGS (ln(1 - chi_{2k}) < -2 by the same criterion as Theorem 1br; the count taken from the prolate
leakage at c = T_0 computed here as in weil_spectrum_ladder.prolate_even_leakage), up to rung 12 (KMAX; the nodes of
the higher polynomials spread beyond the census region). For rung k: the real zeros of ghat_k on (0, min(100, 0.8 x
the ground state's dodging edge)) at step 0.03 refined by bisection, a double zero without sign change detected as
a dip of |ghat| below 1e-6 times both neighbours (counted twice); the HOLE ZEROS = the located zeros left after one
dodging zero per zeta zero (the nearest located zero within 0.2) is removed -- a node that converges onto the first
zeta zero is a hole zero next to a dodging zero, not a displaced dodging zero;
the k-LEVEL BALAYAGE FORMULA F_k = min_T [4 sum_{tau < T} arccosh(T/tau) - delta T] over the zeta zeros plus the
hole zeros, its minimiser T_k, and the residual c_k = ln lambda_k - F_k.

THE NODES. The positive zeros of the even orthogonal polynomials P_{2m} of the weight ghat_1(r)^2 dr on [0, 1.6 T_0]
(Stieltjes in s = r^2 on 6000 Gauss-Legendre nodes, floats), m = 1..min(deep, 12): the polynomial ladder's
prediction for rung m + 1's hole zeros.

State per cell. Usage: ladder_caster.py [cell ...]"""
import sys, os, json, math, time, hashlib
from flint import arb, acb, arb_mat, acb_mat, ctx
import numpy as np
from scipy.optimize import minimize_scalar

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from weil_prime_gram import gram
from weil_spectrum_ladder import prolate_even_leakage

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("ladder_caster.py",), HERE))}
KEYFILE = os.path.join(HERE, "ladder_caster.py")
CK = os.path.join(HERE, "checkpoints")
ZP = os.path.join(CK, "zeta_zeros_800_100dps.json")
ZD = os.path.join(CK, "zeta_zeros_6700.json")

CELLS = {
    "d1.0":  dict(delta=1.0,        K=120, prec=600,  m=10, tprec=400),
    "d1.38": dict(delta=1.3828125,  K=140, prec=600,  m=12, tprec=400),
    "d2.0":  dict(delta=2.0,        K=160, prec=700,  m=18, tprec=500),
    "d2.3":  dict(delta=2.3,        K=260, prec=900,  m=22, tprec=500),
    "d2.6":  dict(delta=2.6,        K=320, prec=1000, m=28, tprec=550),
    "d3.0":  dict(delta=3.0,        K=400, prec=1100, m=42, tprec=650),
    "d3.5":  dict(delta=3.5,        K=540, prec=1300, m=68, tprec=750),
}
RMAX_HOLE = 100.0; STEP_HOLE = 0.03; STEP_DODGE = 0.05; TOL = 0.05; TOL_HOLE = 0.2; EDGE_FRAC = 0.8; NODES_MAX = 12; KMAX = 12; DEEP = -2.0; DIP = 1e-6

def _sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()

def ghat_factory(v, a, K):
    om = [arb(k)*arb.pi()/a for k in range(K)]; sg = [v[k] if k % 2 == 0 else -v[k] for k in range(K)]
    def gh(r):
        r2 = r*r; s = arb(0)
        for k in range(K): s += sg[k]*r/(r2 - om[k]*om[k])
        return 2*(r*a).sin()*s
    return gh

def real_zeros(gh, rmax, step, dips=False):
    """sign changes on the grid refined by bisection; with dips=True also a DOUBLE ZERO without sign change: a grid
    point whose |ghat| is below DIP times both neighbours' (|ghat| ~ (r - r0)^2 at a double zero), counted twice."""
    n = int(rmax/step); rs = [step*0.3141592653 + i*step for i in range(n)]
    vals = [gh(arb(r)) for r in rs]; out = []
    for i in range(n - 1):
        x, y = vals[i], vals[i + 1]
        if (x < 0 and y > 0) or (x > 0 and y < 0):
            lo, hi, flo = arb(rs[i]), arb(rs[i + 1]), x
            for _ in range(40):
                mid = (lo + hi)/2; fm = gh(mid)
                if (fm < 0) == (flo < 0): lo, flo = mid, fm
                else: hi = mid
            out.append(float((lo + hi)/2))
    if dips:
        for i in range(1, n - 1):
            a_, b_, c_ = abs(vals[i - 1]), abs(vals[i]), abs(vals[i + 1])
            if b_ < DIP*a_ and b_ < DIP*c_ and not any(abs(z - rs[i]) < 2*step for z in out):
                out.extend([rs[i], rs[i]])
    return sorted(out)

def classify(zs, ZS, tol):
    """one dodging zero per zeta zero (the nearest located zero within tol); every other located zero is a hole zero."""
    zs = list(zs); dodging = set()
    for g in ZS:
        cand = [(abs(z - g), i) for i, z in enumerate(zs) if abs(z - g) < tol and i not in dodging]
        if cand: dodging.add(min(cand)[1])
    return [z for i, z in enumerate(zs) if i not in dodging], len(dodging)

def balayage_min(Z, delta, T0):
    Z = np.asarray(Z, dtype=float)
    F = lambda T: 4*float(np.sum(np.arccosh(T/Z[Z < T]))) - delta*T
    grid = np.linspace(1.2*T0, 2.6*T0, 3001); fv = np.array([F(T) for T in grid]); k = int(np.argmin(fv))
    r = minimize_scalar(F, bounds=(grid[max(k - 1, 0)], grid[min(k + 1, 3000)]), method="bounded")
    return min(float(r.fun), float(fv[k])), float(r.x)

def poly_nodes(x, w, mmax):
    s = x*x; al = []; be = []; out = []
    p_prev = np.zeros_like(s); p = np.ones_like(s); nrm_prev = 1.0
    for m in range(mmax + 1):
        nrm = float(np.sum(w*p*p)); a_m = float(np.sum(w*s*p*p)/nrm); b_m = nrm/nrm_prev if m > 0 else 0.0
        al.append(a_m); be.append(b_m)
        if m >= 1:
            J = np.diag(al[:m]) + np.diag(np.sqrt(be[1:m]), 1) + np.diag(np.sqrt(be[1:m]), -1)
            out.append([float(v) for v in np.sqrt(np.maximum(np.linalg.eigvalsh(J), 0))])
        p_next = (s - a_m)*p - b_m*p_prev; p_prev, p, nrm_prev = p, p_next, nrm
    return out

def run(cell):
    cfg = CELLS[cell]
    params = {"deps": DEPS, "cell": cell, **cfg, "zeros100": _sha(ZP), "zeros6700": _sha(ZD), "rmax_hole": RMAX_HOLE,
              "step_hole": STEP_HOLE, "step_dodge": STEP_DODGE, "tol": TOL, "tol_hole": TOL_HOLE, "edge_frac": EDGE_FRAC, "kmax": KMAX, "dip": DIP, "nodes_max": NODES_MAX, "deep": DEEP, "round": 2}
    name = f"ladder_caster_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None: return st
    d, K, prec, m = cfg["delta"], cfg["K"], cfg["prec"], cfg["m"]; a = d/2; T0 = 2*math.pi*math.exp(d)
    ZS = np.array(json.load(open(ZD)), dtype=float); Z40 = json.load(open(ZP))
    t0 = time.time()
    # the deep count from the prolate ladder at c = T_0 (as Theorem 1br)
    with ctx.workprec(cfg["tprec"]):
        c = 2*arb.pi()*arb(d).exp()
        pro = prolate_even_leakage(c, int(float(c)) + 300, 2*m + 1, cfg["tprec"])
    deep = sum(1 for k in range(1, m + 1) if pro[2*k] is not None and pro[2*k] < DEEP)
    G, N, pp = gram(d, K, prec); t1 = time.time()
    with ctx.workprec(prec):
        Dm = arb_mat(K, K)
        for i in range(K): Dm[i, i] = 1/N[i].sqrt()
        E, Rv = acb_mat((Dm*G*Dm).mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: float(E[i].real.mid()))
        t2 = time.time()
        aa = arb(a)
        vecs = []; lams = []
        for j in range(min(deep, KMAX) + 1):
            v = [Rv[i, order[j]].real.mid()/N[i].sqrt() for i in range(K)]
            nrm = arb(0)
            for i in range(K): nrm += N[i]*v[i]*v[i]
            vecs.append([x/nrm.sqrt() for x in v]); lams.append(E[order[j]].real.mid())
        # ---- the ground state
        gh = ghat_factory(vecs[0], aa, K)
        g0 = gh(arb(10)**(-8)); h = arb(1)/1000
        g2 = (gh(h) - 2*g0 + gh(-h))/(h*h); kappa = float((-g2/(2*g0)).mid())
        z = real_zeros(gh, 2.2*T0, STEP_DODGE)
        missed = [float(g) for g in ZS[ZS < 2.2*T0] if not any(abs(x - g) < TOL for x in z)]
        free = [x for x in z if float(np.min(np.abs(ZS - x))) >= TOL]
        gam = [arb(s) for s in Z40]; gf = np.array([float(s) for s in Z40])
        lnw = np.array([float((gh(g)**2).log()) for g in gam])
        ln_lam1 = float(lams[0].log()); ln_g0sq = float((g0*g0).log())
        mx = lnw.max(); S = float(np.exp(lnw - mx).sum()); ln_zero = math.log(2*S) + mx
        imax = int(np.argmax(lnw)); part = S*S/float(np.sum(np.exp(2*(lnw - mx))))
        cum = np.cumsum(np.exp(lnw - mx))/S
        shares = {str(f): float(cum[gf < f*T0][-1]) if np.any(gf < f*T0) else 0.0 for f in (2, 3, 4, 6, 10)}
        F1, T1 = balayage_min(ZS, d, T0)
        c1 = ln_lam1 - F1; far = ln_lam1 - ln_zero
        peak = (math.log(2) + lnw[imax] - ln_g0sq) - F1; count = math.log(S) + (mx - lnw[imax])
        # the weight ghat_1^2 in floats for the nodes and <r^2>
        vf = np.array([float(x.mid()) for x in vecs[0]]); omf = np.arange(K)*np.pi/a; sgf = vf*np.where(np.arange(K) % 2 == 0, 1.0, -1.0)
        def ghf(r):
            r = np.asarray(r, dtype=float)[:, None]; t = r/(r*r - omf*omf)
            return 2*np.sin(r[:, 0]*a)*(t*sgf).sum(axis=1)
        R = 1.6*T0; x, wq = np.polynomial.legendre.leggauss(6000); x = 0.5*R*(x + 1) + 1e-7; wq = 0.5*R*wq
        Ew = ghf(x); w = wq*Ew*Ew; m2 = float(np.sum(w*x*x)/np.sum(w))
        nodes = poly_nodes(x, w, min(deep, NODES_MAX))
        ground = {"ln_lam1": ln_lam1, "ln_g0sq": ln_g0sq, "kappa": kappa, "r2_mean": m2, "first_missed": min(missed) if missed else None,
                  "first_free": min(free) if free else None, "n_dodged": len(z) - len(free), "ln_zero_side_800": ln_zero, "far_tail": far,
                  "Tstar": T1, "F1": F1, "c1": c1, "origin": ln_g0sq, "peak_excess": peak, "count_800": count, "participation_800": part,
                  "w_max_at": float(gf[imax]), "shares": shares}
        t3 = time.time()
        # ---- the deep rungs
        rungs = [{"k": 1, "ln_lam": ln_lam1, "hole": [], "Fk": F1, "Tk": T1, "ck": c1}]
        for j in range(1, min(deep, KMAX) + 1):
            ghj = ghat_factory(vecs[j], aa, K)
            rmax_k = min(RMAX_HOLE, EDGE_FRAC*(ground["first_free"] or 2.2*T0))      # below the dodging edge only
            zj = real_zeros(ghj, rmax_k, STEP_HOLE, dips=True)
            hole, _nd = classify(zj, ZS[ZS < rmax_k], TOL_HOLE)                         # one dodging zero per zeta zero; the rest are hole zeros
            Fk, Tk = balayage_min(np.concatenate([ZS, hole]), d, T0)
            lnl = float(lams[j].log())
            rungs.append({"k": j + 1, "ln_lam": lnl, "prolate_4k": pro[2*j] if 2*j < len(pro) else None, "hole": hole, "Fk": Fk, "Tk": Tk, "ck": lnl - Fk})
        t4 = time.time()
    st = {"cell": cell, "delta": d, "T0": T0, "K": K, "prec": prec, "m": m, "deep": deep, "gamma1": float(ZS[0]), "ground": ground,
          "nodes": nodes, "rungs": rungs, "prolate_ln_leakage": pro, "gram_s": t1 - t0, "eig_s": t2 - t1, "ground_s": t3 - t2, "rungs_s": t4 - t3,
          "verdict": "COMPUTED (approximate eigenvectors; zeros located by sign change and bisection in balls at the working precision)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or list(CELLS)):
        st = run(cell); g = st["ground"]
        print(f"{st['cell']:6s} delta {st['delta']:<9} deep {st['deep']:2d} | ln lam_1 {g['ln_lam1']:.3f}, ln g(0)^2 {g['ln_g0sq']:.4f}, kappa' {g['kappa']:.5f}, sqrt<r^2> {math.sqrt(g['r2_mean']):.3f}; "
              f"edge: missed {g['first_missed']}, free {g['first_free']} (T* {g['Tstar']/st['T0']:.3f} T0); c = {g['c1']:.3f} = {g['origin']:.3f} + {g['peak_excess']:.3f} + {g['count_800'] + g['far_tail']:.3f}"
              f" | first hole zeros: " + ", ".join(f"{r['hole'][0]:.3f}" if r['hole'] else "-" for r in st['rungs'][1:5]) + " vs nodes " + ", ".join(f"{n[0]:.3f}" for n in st['nodes'][:4])
              + f" | c_k: " + ", ".join(f"{r['ck']:.2f}" for r in st['rungs'][:9]) + f" [gram {st['gram_s']:.0f}s eig {st['eig_s']:.0f}s ground {st['ground_s']:.0f}s rungs {st['rungs_s']:.0f}s]", flush=True)
