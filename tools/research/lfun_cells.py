#!/usr/bin/env python3
"""Keyed producer: the cross-L-function test (Theorem 1bq's substrate). For
the four forms L(s, chi_-3), L(s, chi_-4), L(s, chi_8) (real primitive
Dirichlet characters, degree 1, conductors 3, 4, 8) and L(Delta, s)
(Ramanujan's cusp form, degree 2, level 1), at the seven slack-law cells
delta = 1.0, 1.3828125, 2.0, 2.3, 2.6, 3.0, 3.5:

  (1) CERTIFIED UPPER BOUNDS on lambda_1(delta) = min Q_L(g)/||g||^2 over
      L^2(-a, a): the Rayleigh ball of the generalised Gram's approximate
      minimiser (lfun_gram.py; K1 and K2 modes, the pair measuring the basis
      convergence), every bound the upper end of a ball, no zeros consulted.
  (2) THE TWO-DIRECTION KNIFE-EDGE: for every prime p <= e^delta with
      c(p) != 0 (the unramified primes), the shells of p moved by +eta and by
      -eta (position and weight, as weil_knife_edge.py; the shell weights
      carry the local coefficients c(p^k)), the fixed-vector search in both
      directions from eta = lambda_1 doubling, capped at eta = log(p)/2: the
      direction that brackets (a certified negative Rayleigh ball of g_1 at
      eta_hi) and the direction that does not below the cap. The SIGN RULE the
      verifier gates: the witnessed direction is downward exactly when the
      first shell's coefficient c(p) is positive (chi(p) = +1; tau(p) > 0),
      upward when negative -- the linear response of Theorem 1bp with the
      sign of the shell weight.
  (3) the horizon T_0 = 2 pi (e^delta / q)^{1/d} and the prime-power list.

The finite-delta formula on each form's own zeros and the offsets c_L(delta)
are computed by the verifier live from the zero lists (lfun_zeros.py), not
here. K per cell: 4 (2 a T_0 / pi) + 100 modes, at least 120 (the same
rule as the zeta cells' K2 within 10 percent); prec 600 bits.
State per (form, cell): the K1/K2 balls, the coefficients, per prime the two
searches; timings. Usage: lfun_cells.py [form ...] [--cell d2.0 ...]
"""
import sys, os, json, math, time
from flint import arb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from lfun_gram import gram_L, dirichlet_coef, delta_coef, horizon
from weil_prime_gram import minimiser, rayleigh
from weil_knife_edge import Autocorr, geomid, ball_fields, TOL

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("lfun_cells.py",), HERE))}
KEYFILE = os.path.join(HERE, "lfun_cells.py")

FORMS = {"chi_-3": lambda: dirichlet_coef(-3), "chi_-4": lambda: dirichlet_coef(-4), "chi_8": lambda: dirichlet_coef(8), "Delta": delta_coef}
CELLS = {"d1.0": 1.0, "d1.38": 1.3828125, "d2.0": 2.0, "d2.3": 2.3, "d2.6": 2.6, "d3.0": 3.0, "d3.5": 3.5}
PREC = 600
ETA_CAP_FRAC = 0.5      # the search stops at eta = log(p)/2 (beyond it the shell is no longer "p moved")

def K_for(delta, L):
    T0 = horizon(delta, L)
    return max(120, int(4*delta*T0/math.pi) + 100)

def prime_shells_c(fg, p, eta, coef, prec):
    """P_p(eta)(g) = 2 sum_k (log p + eta) c(p^k) e^{-u_k/2} f_g(u_k), u_k = k (log p + eta) < 2a."""
    with ctx.workprec(prec):
        lp = arb(p).log() + arb(eta)
        tot = arb(0); k = 1
        while k*lp < fg.twoa:
            u = k*lp
            c = coef(p, k); c = arb(c) if not isinstance(c, arb) else c
            tot += 2*lp*c*(-u/2).exp()*fg(u)
            k += 1
        return tot

def search(num, den, fg, p, coef, lam_up, prec, sign):
    with ctx.workprec(prec):
        P0 = prime_shells_c(fg, p, 0, coef, prec)
        def q(eta):
            return (num + P0 - prime_shells_c(fg, p, sign*eta, coef, prec))/den
        cap = ETA_CAP_FRAC*math.log(p)
        evals = 0; eta = float(lam_up); lo = 0.0; r_lo = None
        while True:
            r = q(eta); evals += 1
            if r.upper() < 0: hi = eta; r_hi = r; break
            if not (r.lower() > 0): return {"status": "ambiguous", "eta": eta, "evals": evals}
            lo = eta; r_lo = r; eta *= 2
            if eta > cap: return {"status": "no crossing below cap", "cap": cap, "eta_lo": lo, "q_lo": ball_fields(r_lo, prec), "evals": evals}
        while lo == 0 or hi/lo > 1 + TOL:
            mid = geomid(lo, hi)
            if not (lo < mid < hi): return {"status": "bracket stalled", "eta_lo": lo, "eta_hi": hi, "evals": evals}
            r = q(mid); evals += 1
            if r.upper() < 0: hi = mid; r_hi = r
            elif r.lower() > 0: lo = mid; r_lo = r
            else: return {"status": "ambiguous", "eta": mid, "evals": evals}
            if evals > 20000: return {"status": "evaluation cap", "eta_lo": lo, "eta_hi": hi, "evals": evals}
        return {"status": "bracketed", "sign": sign, "eta_lo": lo, "eta_hi": hi, "q_lo": ball_fields(r_lo, prec), "q_hi": ball_fields(r_hi, prec),
                "evals": evals, "hi_over_lambda": hi/float(lam_up)}

def run(form, cell):
    L = FORMS[form](); delta = CELLS[cell]; K2 = K_for(delta, L); K1 = int(0.7*K2)
    params = {"deps": DEPS, "form": form, "cell": cell, "delta": delta, "K1": K1, "K2": K2, "prec": PREC, "cap_frac": ETA_CAP_FRAC, "round": 1}
    name = f"lfun_{form}_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None:
        return st
    t0 = time.time()
    G2, N2, pp = gram_L(delta, K2, PREC, L); c2, ev2 = minimiser(G2, N2, PREC); rq2 = rayleigh(G2, N2, c2, PREC); t1 = time.time()
    G1, N1, _ = gram_L(delta, K1, PREC, L); c1, ev1 = minimiser(G1, N1, PREC); rq1 = rayleigh(G1, N1, c1, PREC); t2 = time.time()
    with ctx.workprec(PREC):
        a = arb(delta)/2
        c = [arb(x) for x in c2]
        v = arb_mat(K2, 1)
        for i in range(K2): v[i, 0] = c[i]
        num = (v.transpose()*G2*v)[0, 0]
        den = arb(0)
        for i in range(K2): den += N2[i]*c[i]*c[i]
        lam_up = rq2.upper()
        fg = Autocorr(c, a, PREC)
        primes = sorted({next(q for q in range(2, n + 1) if n % q == 0) for n in pp})
        per = {}
        for p in primes:
            c1p = L["coef"](p, 1); c1p = float(c1p) if not isinstance(c1p, float) else c1p
            res = {"c_p": c1p}
            for sign in (-1, +1):
                res["down" if sign < 0 else "up"] = search(num, den, fg, p, L["coef"], lam_up, PREC, sign)
            per[str(p)] = res
        t3 = time.time()
        st = {"form": form, "cell": cell, "delta": delta, "q": L["q"], "d": L["d"], "K1": K1, "K2": K2, "prec": PREC,
              "T0": horizon(delta, L), "prime_powers": pp, "primes": primes,
              "min_K2": {**ball_fields(rq2, PREC), "eig_ln": float(ev2.log()) if ev2 > 0 else None},
              "min_K1": {**ball_fields(rq1, PREC), "eig_ln": float(ev1.log()) if ev1 > 0 else None},
              "coeffs": [x.mid().str(int(PREC*0.31) + 10, radius=False) for x in c],
              "per_prime": per, "K2_s": t1 - t0, "K1_s": t2 - t1, "knife_s": t3 - t2,
              "verdict": "CERTIFIED (each bound the upper end of a Rayleigh ball on the true form of L; no zeros); the knife-edge searches as recorded"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    args = sys.argv[1:]
    forms = [a for a in args if a in FORMS] or list(FORMS)
    cells = [a for a in args if a in CELLS] or list(CELLS)
    for form in forms:
        for cell in cells:
            st = run(form, cell)
            def fmt(r): return f"{r['eta_hi']:.2e}({r['hi_over_lambda']:.1f})" if r.get("status") == "bracketed" else "-"
            pr = " ".join(f"{p}[{'+' if r['c_p'] > 0 else '-' if r['c_p'] < 0 else '0'}]:d{fmt(r['down'])}/u{fmt(r['up'])}" for p, r in st["per_prime"].items())
            print(f"{form:6s} {cell:6s} T0 {st['T0']:7.2f} K {st['K1']}/{st['K2']} ln K2 {st['min_K2']['ln_upper']:9.3f} K1 {st['min_K1']['ln_upper']:9.3f} pos={st['min_K2']['positive']} | {pr} [{st['K2_s']:.0f}s {st['K1_s']:.0f}s {st['knife_s']:.0f}s]", flush=True)
