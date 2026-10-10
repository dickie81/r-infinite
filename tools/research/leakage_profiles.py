#!/usr/bin/env python3
"""The exact leakage profiles of the ladder at a cell (Theorem 1bz's keyed producer). For rungs 1..NR of the true form's
window (cosine basis, K modes; the Gram of weil_prime_gram; the pencil (G, N) as ladder_caster and rung_anatomy):

THE POLISHED EIGENVECTORS: the pencil's eigenvectors from the arb eigensolver at the working precision (the symmetric
form D G D, D = N^{-1/2}, as rung_anatomy), each polished by two steps of inverse iteration on the pencil at the shift
lambda (1 - 10^-12) and N-normalised, the eigenvalue the Rayleigh quotient of the polished vector; the pencil residual
max_i |(G x - lambda N x)_i| / max_i |(N x)_i| recorded (log10).

THE PROFILE of every rung: ln|ghat_k| at every zeta zero of Theorem 1bm's 6700-zero list (the first 800 to 100 digits,
Theorem 1bu's list, so a dodged zero's residual ghat is the eigenvector's and not the zero's rounding) and at the midpoints
between consecutive zeta zeros below 4 T_0 (the envelope's samples), in arb, stored as logs rounded to four decimals
(a rounding of 10^-4 in ln|ghat|, 2 x 10^-4 in a leakage share); ln(2 sum_list ghat^2) unrounded; ln lambda, ghat_k(0) = 2 a v_0
and the N-norm of the polished vector.

Float64 coefficients cannot carry the leakage (a dodged zero's ghat is a cancellation of ~K terms to 10^-30 and below), so the
vectors are recomputed and polished in arb here; the eigenvalues cross-check rung_anatomy's census (the verifier gates them).

Checkpoints leakage_profiles_<cell>_<key>.json, content-keyed (ckpt_key.code_key over the executable content of the import
closure; the two zero lists' hashes among the inputs). Floating point beyond the profile (which is in arb at the working
precision); no Riemann Hypothesis consequence."""
import sys, os, json, math, time, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from flint import arb, acb, arb_mat, acb_mat, ctx
from weil_prime_gram import gram
import ladder_caster as LC
import ckpt_key

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(ckpt_key.producer_closure(("leakage_profiles.py",), HERE))}
KEYFILE = os.path.join(HERE, "leakage_profiles.py")
CELLS = {"d2.0": 5, "d2.3": 10, "d2.6": 13, "d3.0": 13, "d3.5": 13}       # NR: rungs 1..NR (rung_anatomy's census counts)
SHIFT = "1e-12"                                                          # the inverse iteration's shift offset, lambda (1 - SHIFT)
ITER = 2                                                                 # inverse-iteration steps
MID_HORIZONS = 4.0                                                       # midpoints stored below MID_HORIZONS * T_0
ROUND = 4                                                                # decimals kept in the stored logs

def _sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()

def params_for(cell):
    """the checkpoint's parameters (the key's inputs) for a cell"""
    return {"deps": DEPS, "cell": cell, **LC.CELLS[cell], "NR": CELLS[cell], "zeros6700": _sha(LC.ZD), "zeros100": _sha(LC.ZP),
            "shift": SHIFT, "iter": ITER, "mid_horizons": MID_HORIZONS, "round_dec": ROUND, "round": 1}

def run(cell):
    cfg = LC.CELLS[cell]; NR = CELLS[cell]
    params = params_for(cell)
    name = f"leakage_profiles_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None: return st
    d, K, prec = cfg["delta"], cfg["K"], cfg["prec"]; a = d/2; T0 = 2*math.pi*math.exp(d)
    ZS = json.load(open(LC.ZD)); ZP = json.load(open(LC.ZP))              # the 6700 floats; the first 800 to 100 digits (strings)
    n_mid = int(np.searchsorted(np.array(ZS, dtype=float), MID_HORIZONS*T0)) - 1
    t0 = time.time()
    G, N, pp = gram(d, K, prec); t1 = time.time()
    rungs = []
    with ctx.workprec(prec):
        ZA = [arb(ZP[i]) if i < len(ZP) else arb(ZS[i]) for i in range(len(ZS))]   # parsed at prec (the 100-digit zeros intact)
        MA = [(ZA[i] + ZA[i + 1])/2 for i in range(max(n_mid, 0))]
        Dm = arb_mat(K, K)
        for i in range(K): Dm[i, i] = 1/N[i].sqrt()
        E, Rv = acb_mat((Dm*G*Dm).mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: float(E[i].real.mid())); t2 = time.time()
        Gm = G.mid(); Nm = arb_mat(K, K)
        for i in range(K): Nm[i, i] = N[i]
        aa = arb(a); om = [arb(i)*arb.pi()/aa for i in range(K)]
        for j in range(NR):
            tj = time.time()
            x = arb_mat(K, 1)
            for i in range(K): x[i, 0] = Rv[i, order[j]].real.mid()/N[i].sqrt()
            lam_eig = E[order[j]].real.mid()
            lam = (x.transpose()*Gm*x)[0, 0]/(x.transpose()*Nm*x)[0, 0]
            for it in range(ITER):                                              # inverse iteration on the pencil
                A = Gm - Nm*(lam*(1 - arb(SHIFT)))
                y = A.solve(Nm*x).mid()
                nr = (y.transpose()*Nm*y)[0, 0].sqrt(); x = arb_mat(K, 1)
                for i in range(K): x[i, 0] = y[i, 0]/nr
                lam = (x.transpose()*Gm*x)[0, 0]/(x.transpose()*Nm*x)[0, 0]
            res = Gm*x - Nm*x*lam; nx = Nm*x
            resid = max(abs(float(res[i, 0].mid())) for i in range(K))/max(abs(float(nx[i, 0].mid())) for i in range(K))
            v = [x[i, 0] for i in range(K)]; nrm = (x.transpose()*Nm*x)[0, 0]
            sg = [v[i] if i % 2 == 0 else -v[i] for i in range(K)]; g0 = 2*aa*v[0]
            def ev(pts):
                out = []; s2 = arb(0)
                for r in pts:
                    s = arb(0)
                    for i in range(K): s += sg[i]*r/(r*r - om[i]*om[i])
                    val = 2*(r*aa).sin()*s; s2 += val*val
                    out.append(round(float(abs(val).log()), ROUND) if val != 0 else -1e9)
                return out, s2
            lng, s2 = ev(ZA); lnm, _ = ev(MA)
            lamf = float(lam.mid())
            rungs.append({"k": j + 1, "ln_lam": math.log(lamf) if lamf > 0 else None, "ln_lam_eig": float(lam_eig.log()) if lam_eig > 0 else None,
                          "log10_resid": math.log10(resid) if resid > 0 else -999.0, "norm": float(nrm), "g0": float(g0),
                          "ln_sum2_list": float((2*s2).log()), "ln_abs_g_at_zeros": lng, "ln_abs_g_at_mid": lnm, "secs": time.time() - tj})
            print(f"  {cell} rung {j + 1}: ln lam {rungs[-1]['ln_lam']}, resid 1e{rungs[-1]['log10_resid']:.0f}, {time.time() - tj:.0f}s", flush=True)
        t3 = time.time()
    st = {"cell": cell, "delta": d, "T0": T0, "K": K, "prec": prec, "NR": NR, "n_zeros": len(ZS), "n_mid": max(n_mid, 0), "rungs": rungs,
          "gram_s": t1 - t0, "eig_s": t2 - t1, "profile_s": t3 - t2,
          "verdict": "COMPUTED (eigenvectors polished by inverse iteration at the working precision; the profile in arb, stored as rounded logs)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or list(CELLS)):
        st = run(cell)
        print(f"{cell}: K {st['K']}, NR {st['NR']}; gram {st['gram_s']:.0f}s eig {st['eig_s']:.0f}s profiles {st['profile_s']:.0f}s; midpoints {st['n_mid']}")
        for r in st["rungs"]:
            print(f"  rung {r['k']:2d}: ln lam {r['ln_lam']} (eig {r['ln_lam_eig']}); resid 1e{r['log10_resid']:.0f}; ln 2 sum {r['ln_sum2_list']:.4f}; norm {r['norm']:.12f}; {r['secs']:.0f}s", flush=True)
