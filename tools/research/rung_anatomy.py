#!/usr/bin/env python3
"""The excited states' exact anatomy at a cell (Theorem 1bw's keyed producer). For rungs 1..NR of the true form's window
(cosine basis, K modes; the Gram of weil_prime_gram, the pencil's eigenvectors as ladder_caster):

THE FULL CENSUS of every rung: all K - 1 designed zero pairs of ghat_k located on the real line (the census region doubling
from 2 omega_{K-1} to 8 omega_{K-1} as for the ground state), the sum rule kappa_k = sum tau^-2 + (a/pi)^2 sum_{j>=K} j^-2 with
kappa_k = -ghat_k''(0)/(2 ghat_k(0)) by Richardson about the exact origin value 2 a v_0; a pair not located is a complex pair
(n_complex = K - 1 - n_designed). The rung's own dodging edge (the first zeta zero with no located zero within TOL_HOLE), the
dodging zeros (one per zeta zero below the edge, with their displacements from the ground state's), the HOLE ZEROS (the
non-dodging zeros below the edge; k - 1 for a safely deep rung), the EXTERIOR (every located zero at or beyond the edge).

THE LAWS (the factorisation, the curvature law, the bi-orthogonal law) are computed by rung_laws.py from this checkpoint.

Checkpoints rung_anatomy_<cell>_<key>.json, content-keyed (ckpt_key.code_key over the executable content of the import closure).
Floating point beyond the census (which is in balls at the working precision); no Riemann Hypothesis consequence."""
import sys, os, json, math, time, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from flint import arb, acb, arb_mat, acb_mat, ctx
from weil_prime_gram import gram
import ladder_caster as LC
import ckpt_key

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(ckpt_key.producer_closure(("rung_anatomy.py",), HERE))}
KEYFILE = os.path.join(HERE, "rung_anatomy.py")
CELLS = {"d2.0": 5, "d2.3": 10, "d2.6": 13, "d3.0": 13, "d3.5": 13}       # NR: rungs 1..NR

def _sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()

def params_for(cell):
    """the checkpoint's parameters (the key's inputs) for a cell; rung_laws.py keys its own checkpoint on this key"""
    return {"deps": DEPS, "cell": cell, **LC.CELLS[cell], "NR": CELLS[cell], "zeros6700": _sha(LC.ZD), "tol_hole": LC.TOL_HOLE,
            "step_dodge": LC.STEP_DODGE, "step_hole": LC.STEP_HOLE, "rmax_hole": LC.RMAX_HOLE, "edge_frac": LC.EDGE_FRAC, "dip": LC.DIP, "round": 1}

def run(cell):
    cfg = LC.CELLS[cell]; NR = CELLS[cell]
    params = params_for(cell)
    name = f"rung_anatomy_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None: return st
    d, K, prec = cfg["delta"], cfg["K"], cfg["prec"]; a = d/2; T0 = 2*math.pi*math.exp(d)
    ZS = np.array(json.load(open(LC.ZD)), dtype=float)
    t0 = time.time()
    G, N, pp = gram(d, K, prec); t1 = time.time()
    rungs = []
    with ctx.workprec(prec):
        Dm = arb_mat(K, K)
        for i in range(K): Dm[i, i] = 1/N[i].sqrt()
        E, Rv = acb_mat((Dm*G*Dm).mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: float(E[i].real.mid())); t2 = time.time()
        aa = arb(a); omf = np.arange(K)*np.pi/a
        def _designed(zs, R):
            sinc = [i*math.pi/a for i in range(K, int(R/(math.pi/a)) + 2) if i*math.pi/a < R]
            return [x for x in zs if not any(abs(x - w) < 1e-6 for w in sinc)]
        tail = float((aa/arb.pi())**2*acb(K).polygamma(1).real)
        vecs = []
        for j in range(NR):
            v = [Rv[i, order[j]].real.mid()/N[i].sqrt() for i in range(K)]
            nrm = arb(0)
            for i in range(K): nrm += N[i]*v[i]*v[i]
            vecs.append([x/nrm.sqrt() for x in v])
        for j in range(NR):
            tj = time.time(); v = vecs[j]
            lam = E[order[j]].real.mid(); lnl = float(lam.log()) if lam > 0 else None
            gh = LC.ghat_factory(v, aa, K); g0 = 2*aa*v[0]
            def _kfd(h): return float((-(gh(h) - 2*g0 + gh(-h))/(h*h)/(2*g0)).mid())
            kfd = _kfd(arb(2)/10000); kappa = (4*_kfd(arb(1)/10000) - kfd)/3
            R_ext = 2.0*float(omf[K - 1]); z_ext = LC.real_zeros(gh, R_ext, LC.STEP_DODGE, dips=True); designed = _designed(z_ext, R_ext)
            while len(designed) < K - 1 and R_ext < 8.0*float(omf[K - 1]) - 1e-9:
                R_ext = 2.0*R_ext; z_ext = LC.real_zeros(gh, R_ext, LC.STEP_DODGE, dips=True); designed = _designed(z_ext, R_ext)
            n_dips = sum(1 for i in range(1, len(z_ext)) if z_ext[i] == z_ext[i - 1])
            sum_rule = sum(1.0/(x*x) for x in designed) + tail
            missed = [float(g) for g in ZS[ZS < R_ext] if not any(abs(z - g) < LC.TOL_HOLE for z in designed)]
            edge = min(missed) if missed else R_ext
            below = [z for z in designed if z < edge]
            dodging = {}
            for g in ZS[ZS < edge]:
                cand = [z for z in below if abs(z - float(g)) < LC.TOL_HOLE and z not in dodging.values()]
                if cand: dodging[float(g)] = min(cand, key=lambda z: abs(z - float(g)))
            holes = [z for z in below if z not in dodging.values()]
            exterior = [z for z in designed if z >= edge]
            rz = LC.real_zeros(gh, min(LC.RMAX_HOLE, LC.EDGE_FRAC*edge), LC.STEP_HOLE, dips=True)
            holes_fine, _ = LC.classify(rz, ZS[ZS < LC.EDGE_FRAC*edge], LC.TOL_HOLE)
            holes_fine = [z for z in holes_fine if z < LC.EDGE_FRAC*edge]
            rungs.append({"k": j + 1, "ln_lam": lnl, "g0": float(g0), "kappa": kappa, "kappa_fd": kfd, "n_designed": len(designed), "K_minus_1": K - 1,
                          "n_complex": K - 1 - len(designed), "sum_rule_residual": sum_rule - kappa, "R_ext": R_ext, "n_dips": n_dips, "edge": edge,
                          "n_zeta_below_edge": int(np.sum(ZS < edge)), "dodging": [[g, z] for g, z in sorted(dodging.items())], "holes": holes,
                          "holes_fine": holes_fine, "exterior": exterior, "secs_census": time.time() - tj})
        t3 = time.time()
    st = {"cell": cell, "delta": d, "T0": T0, "K": K, "prec": prec, "NR": NR, "gamma1": float(ZS[0]), "rungs": rungs,
          "gram_s": t1 - t0, "eig_s": t2 - t1, "census_s": t3 - t2, "vecs": [[float(x) for x in v] for v in vecs],
          "verdict": "COMPUTED (approximate eigenvectors; zeros located by sign change and bisection in balls at the working precision)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or list(CELLS)):
        st = run(cell)
        print(f"{cell}: K {st['K']}, NR {st['NR']}; gram {st['gram_s']:.0f}s eig {st['eig_s']:.0f}s census {st['census_s']:.0f}s")
        for r in st["rungs"]:
            print(f"  rung {r['k']:2d}: ln lam {r['ln_lam']}; designed {r['n_designed']}/{r['K_minus_1']} (complex {r['n_complex']}, dips {r['n_dips']}); sum rule {r['sum_rule_residual']:.1e}; "
                  f"edge {r['edge']:.2f} (dodging {len(r['dodging'])}); holes {len(r['holes_fine'])}; exterior {len(r['exterior'])}; {r['secs_census']:.0f}s", flush=True)
