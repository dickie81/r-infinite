#!/usr/bin/env python3
"""Keyed producer: certified upper bounds on the TRUE Weil form's ground state
at the slack law's seven cells (Theorem 1bn's substrate), from the prime-side
Gram of weil_prime_gram.py (balls; primes <= e^delta, digamma archimedean
term, closed-form pole) and two trial vectors per cell -- the Gram minimiser
in the even cosine basis (K1 and K2 modes, the pair measuring the basis
convergence) and Connes-Consani-Moscovici's k_lambda = E(h_lambda)
(ccm_trial_vector.py, K2 modes). Every printed bound is the upper end of a
ball enclosing the Rayleigh quotient of a stated vector: an unconditional
upper bound on lambda_1(delta) = min Q(g)/||g||^2 over L^2(-a, a).

Also computed per cell (not certified; a comparison target): the prolate
deficit 1 - chi_2 = 1 - sqrt(lambda_4(c)) at c = 2 pi e^delta from the
finite Fourier eigenvalue of psi_4 (|mu_4|^2 = 2 pi lambda_4 / c), at two
points x whose agreement is stored.

State per cell: the ball fields of the two minimisers and the CCM trial
(mid, log2 radius, upper, ln upper), the prime powers, the trial's
diagnostics, the 1 - chi_2 value, timings.
Usage: true_form_cells.py [cell ...]     (all cells when none given)
"""
import sys, os, json, math, time
from flint import arb, acb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from weil_prime_gram import gram, minimiser, rayleigh
from ccm_trial_vector import build, prolate_coeffs, legendre_eval

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("true_form_cells.py",), HERE))}
KEYFILE = os.path.join(HERE, "true_form_cells.py")

CELLS = {
    "d1.0":  dict(delta=1.0,        K1=70,  K2=120, prec=600,  nodes=400,  tprec=400),
    "d1.38": dict(delta=1.3828125,  K1=80,  K2=140, prec=600,  nodes=500,  tprec=400),
    "d2.0":  dict(delta=2.0,        K1=100, K2=160, prec=700,  nodes=900,  tprec=500),
    "d2.3":  dict(delta=2.3,        K1=170, K2=260, prec=900,  nodes=1200, tprec=500),
    "d2.6":  dict(delta=2.6,        K1=220, K2=320, prec=1000, nodes=1500, tprec=550),
    "d3.0":  dict(delta=3.0,        K1=280, K2=400, prec=1100, nodes=2200, tprec=650),
    "d3.5":  dict(delta=3.5,        K1=420, K2=540, prec=1300, nodes=3000, tprec=750),
}

def ball_fields(rq, prec):
    with ctx.workprec(prec):
        up = rq.upper(); rad = rq.rad()
        return {"mid": rq.mid().str(30, radius=False),
                "rad_log2": float(rad.log()/arb(2).log()) if rad > 0 else None,
                "upper": up.str(30, radius=False),
                "ln_upper": float(up.log()) if up > 0 else None,
                "positive": bool(rq.lower() > 0)}

KMAX_EXTRA = 300   # Legendre cutoff c + 300 for the prolates: the c + 120 default of ccm_trial_vector truncates at
                   # |d_k| ~ 1e-83, enough for a trial vector (its Q error is quadratic in the truncation) but not for
                   # 1 - chi_2 at delta >= 3 (A454: kmax = c + 120 gave -3.5e-85 at delta = 3; c + 300 and c + 500 agree)

def chi2_deficit(delta, prec):
    """1 - chi_2 = 1 - sqrt(lambda_4(c)), c = 2 pi e^delta, without quadrature: the finite Fourier eigenvalue
    relation at x = 0, int psi_4 = mu_4 psi_4(0) with int psi_4 = sqrt(2) d_0 and |mu_4|^2 = 2 pi lambda_4 / c,
    gives lambda_4 = (c/pi) (d_0 / psi_4(0))^2. Returned at two Legendre cutoffs (c + KMAX_EXTRA and c + KMAX_EXTRA
    + 200) whose agreement is the convergence check."""
    with ctx.workprec(prec):
        c = 2*arb.pi()*arb(delta).exp()
        out = []
        for extra in (KMAX_EXTRA, KMAX_EXTRA + 200):
            kmax = int(float(c)) + extra
            ks, d0, d4, chi0, chi4 = prolate_coeffs(c, kmax, prec)
            lam4 = c/arb.pi()*(d4[0]/legendre_eval(ks, d4, arb(0), prec))**2
            out.append(1 - lam4.sqrt())
        return out

def run(cell):
    cfg = CELLS[cell]
    params = {"deps": DEPS, "cell": cell, **cfg, "round": 1}
    name = f"true_form_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None:
        return st
    d, K1, K2, prec = cfg["delta"], cfg["K1"], cfg["K2"], cfg["prec"]
    t0 = time.time()
    G2, N2, pp = gram(d, K2, prec); t1 = time.time()
    c2, ev2 = minimiser(G2, N2, prec); rq2 = rayleigh(G2, N2, c2, prec); t2 = time.time()
    G1, N1, _ = gram(d, K1, prec)
    c1, ev1 = minimiser(G1, N1, prec); rq1 = rayleigh(G1, N1, c1, prec); t3 = time.time()
    tr = build(d, K2, cfg["tprec"], cfg["nodes"], int(2*math.pi*math.exp(d)) + KMAX_EXTRA); t4 = time.time()
    with ctx.workprec(prec):
        cc = [arb(x) for x in tr["coeffs"]]
        rqc = rayleigh(G2, N2, cc, prec)
    t5 = time.time()
    dchi = chi2_deficit(d, cfg["tprec"]); t6 = time.time()
    with ctx.workprec(prec):
        st = {"cell": cell, "delta": d, "K1": K1, "K2": K2, "prec": prec, "prime_powers": pp,
              "min_K1": ball_fields(rq1, prec), "min_K2": ball_fields(rq2, prec),
              "eig_K1": float(ev1.log()) if ev1 > 0 else None, "eig_K2": float(ev2.log()) if ev2 > 0 else None,
              "ccm": ball_fields(rqc, prec),
              "ccm_trial": {k: tr[k] for k in ("K", "prec", "nodes", "kmax", "c", "chi0", "chi4",
                                                "fourier_check_psi0", "fourier_check_psi4", "odd_part_max",
                                                "k_at_a", "k_at_minus_a", "norm2", "coeff_tail")},
              "one_minus_chi2": [x.str(20, radius=False) for x in dchi],
              "ln_one_minus_chi2": [float(x.log()) if x > 0 else None for x in dchi],
              "gram_s": t1 - t0, "eig_K2_s": t2 - t1, "K1_s": t3 - t2, "trial_s": t4 - t3, "chi_s": t6 - t5,
              "verdict": "CERTIFIED (each bound the upper end of a Rayleigh ball on the true form; no zeros)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or list(CELLS)):
        st = run(cell)
        f3 = lambda x: f"{x:9.3f}" if x is not None else "     None"
        print(f"{cell:6s} delta {st['delta']:<9} min K1 ln {f3(st['min_K1']['ln_upper'])}  min K2 ln {f3(st['min_K2']['ln_upper'])}  "
              f"CCM ln {f3(st['ccm']['ln_upper'])}  1-chi2 ln {f3(st['ln_one_minus_chi2'][0])} (cutoff +200: {f3(st['ln_one_minus_chi2'][1])})  "
              f"rad log2 {st['min_K2']['rad_log2']}  primes {len(st['prime_powers'])}  "
              f"gram {st['gram_s']:.0f}s eig {st['eig_K2_s']:.0f}s trial {st['trial_s']:.0f}s", flush=True)
