#!/usr/bin/env python3
"""Keyed producer: the LINEAR-RESPONSE LAW of the knife-edge (Theorem 1bp's
substrate). At each of the seven cells, from the certified minimiser g_1 of
Theorem 1bn/1bo (weil_knife_edge.py's checkpoint: the coefficients, the
lambda_1 ball, the certified brackets), in balls:

  (1) THE SLOPE. For every prime p <= e^delta the first derivative of the
      form at g_1 with respect to the shift of log p (position and weight of
      every shell of p):
        d/d eta Q^eta(g_1)|_0 = -d/d eta P_p(eta)|_0,
        d/d eta P_p = 2 sum_k e^{-u_k/2} [(1 - u_k/2) f(u_k) + u_k f'(u_k)],  u_k = k log p,
      f the autocorrelation of g_1 and f' its derivative, both O(K) closed forms
      (f' collapses like f: f'(u) = sum_k c_k^2 f_kk'(u) + 2 sum_l (-1)^l c_l
      omega_l^2 cos(omega_l u) A_l). D_p := -(dP_p/d eta)/||g_1||^2, a ball.
  (2) THE LAW. eta_lin(p) := lambda_1/D_p (balls). The claim gated by the
      verifier: eta_lin lies inside the certified bracket [eta_lo, eta_hi] of
      weil_knife_edge.py at every (cell, prime) -- the certified crossing is
      the first-order crossing (bracket width 1e-3).
  (3) THE SIGN. D_p > 0 at every (cell, prime): to first order g_1's quotient
      rises for every upward shift, so g_1 witnesses no upward crossing.
  (4) THE DILATION EDGE. All shells rescaled at once, log p -> (1 - eps) log p
      for every p <= e^delta (the relative scale of the finite places against
      the real place): the bracket [eps_lo, eps_hi] of the fixed-vector
      crossing (negative ball at eps_hi), and the first-order composition
      eps_lin = lambda_1 / sum_p (log p) D_p -- the pins compose additively.
  (5) THE ARCHIMEDEAN PIN. The constant psi(1/4) - log pi enters the Gram only
      on the diagonal, as (psi(1/4) - log pi) N_kk (weil_prime_gram.py): for
      every vector the Rayleigh quotient of the form with log pi -> log pi +
      eps is the quotient minus eps exactly, so positivity on [-a, a] is lost
      at eps = lambda_1(delta) upward and never downward. Stored: the quotient
      of g_1 on G - eps N at eps = lambda_1's upper end (a ball straddling or
      below zero) and at eps = -lambda_1 (positive), the identity checked by
      the verifier on a live Gram.

State per cell: per prime D_p (ball ends), eta_lin (ball ends), the bracket
containment flags; the dilation bracket and its composition; the archimedean
values; timings. Usage: weil_linear_response.py [cell ...]
"""
import sys, os, json, math, time
from flint import arb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from weil_prime_gram import gram, rayleigh
from weil_knife_edge import run as run_KE, CELLS, Autocorr, prime_shells, geomid, TOL, ball_fields

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("weil_linear_response.py",), HERE))}
KEYFILE = os.path.join(HERE, "weil_linear_response.py")

class AutocorrDeriv(Autocorr):
    """f_g'(u) by the same O(K) collapse as f_g(u)."""
    def deriv(self, u):
        with ctx.workprec(self.prec):
            c, om, twoa = self.c, self.om, self.twoa
            f = -c[0]*c[0]
            for k in range(1, self.K):
                f += c[k]*c[k]*(-(om[k]*u).cos() - (twoa - u)*om[k]*(om[k]*u).sin()/2)
            s = arb(0)
            for l in range(self.K):
                t = c[l]*om[l]*om[l]*(om[l]*u).cos()*self.A[l]
                s += -t if l % 2 else t
            return f + 2*s

def dP_deta(fg, p, prec):
    """d/d eta P_p(eta) at eta = 0: 2 sum_k e^{-u_k/2} [(1 - u_k/2) f(u_k) + u_k f'(u_k)]."""
    with ctx.workprec(prec):
        lp = arb(p).log(); tot = arb(0); k = 1
        while k*lp < fg.twoa:
            u = k*lp
            tot += 2*(-u/2).exp()*((1 - u/2)*fg(u) + u*fg.deriv(u))
            k += 1
        return tot

def bstr(x, prec):
    with ctx.workprec(prec):
        return {"mid": x.mid().str(30, radius=False), "lower": x.lower().str(30, radius=False), "upper": x.upper().str(30, radius=False),
                "rad_log2": float(x.rad().log()/arb(2).log()) if x.rad() > 0 else None}

def run(cell):
    cfg = CELLS[cell]
    params = {"deps": DEPS, "cell": cell, "delta": cfg["delta"], "K": cfg["K"], "prec": cfg["prec"], "round": 1}
    name = f"linear_response_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None:
        return st
    ke = run_KE(cell)
    d, K, prec = ke["delta"], ke["K"], ke["prec"]
    t0 = time.time()
    G, N, pp = gram(d, K, prec)
    with ctx.workprec(prec):
        a = arb(d)/2
        c = [arb(x) for x in ke["coeffs"]]
        v = arb_mat(K, 1)
        for i in range(K): v[i, 0] = c[i]
        num = (v.transpose()*G*v)[0, 0]
        den = arb(0)
        for i in range(K): den += N[i]*c[i]*c[i]
        rq = num/den; lam = rq
        fg = AutocorrDeriv(c, a, prec)
        per = {}; sumD = arb(0)
        for p in ke["primes"]:
            dP = dP_deta(fg, p, prec)
            D = -dP/den
            eta_lin = lam/D
            r = ke["per_prime"][str(p)]
            per[str(p)] = {"D": bstr(D, prec), "eta_lin": bstr(eta_lin, prec), "D_positive": bool(D.lower() > 0),
                           "eta_lo": r["eta_lo"], "eta_hi": r["eta_hi"],
                           "lin_in_bracket": bool(eta_lin.lower() >= r["eta_lo"] and eta_lin.upper() <= r["eta_hi"]),
                           "lin_over_hi": float(eta_lin.mid()/r["eta_hi"])}
            sumD += arb(p).log()*D
        t1 = time.time()
        # (4) the dilation edge: all shells rescaled, bracket of the fixed-vector crossing
        P0 = {p: prime_shells(fg, p, 0, prec) for p in ke["primes"]}
        P0sum = sum(P0.values(), arb(0))
        logp = {p: arb(p).log() for p in ke["primes"]}
        def q(eps):
            e = arb(eps); s = arb(0)
            for p in ke["primes"]:
                s += prime_shells(fg, p, -e*logp[p], prec)
            return (num + P0sum - s)/den
        evals = 0; eps = float(lam.upper()); lo = 0.0; r_lo = None; status = "bracketed"; hi = None; r_hi = None
        while True:
            r = q(eps); evals += 1
            if r.upper() < 0: hi = eps; r_hi = r; break
            if not (r.lower() > 0): status = "ambiguous"; break
            lo = eps; r_lo = r; eps *= 2
            if eps > 4: status = "no crossing below 4"; break
        if status == "bracketed":
            while lo == 0 or hi/lo > 1 + TOL:
                mid = geomid(lo, hi)
                if not (lo < mid < hi): status = "bracket stalled"; break
                r = q(mid); evals += 1
                if r.upper() < 0: hi = mid; r_hi = r
                elif r.lower() > 0: lo = mid; r_lo = r
                else: status = "ambiguous"; break
        eps_lin = lam/sumD
        dil = {"status": status, "eps_lo": lo, "eps_hi": hi, "evals": evals,
               "q_lo": ball_fields(r_lo, prec) if r_lo is not None else None, "q_hi": ball_fields(r_hi, prec) if r_hi is not None else None,
               "eps_lin": bstr(eps_lin, prec), "lin_in_bracket": bool(hi is not None and eps_lin.lower() >= lo and eps_lin.upper() <= hi),
               "harmonic": float(hi*sum(math.log(p)/ke["per_prime"][str(p)]["eta_hi"] for p in ke["primes"])) if hi is not None else None}
        t2 = time.time()
        # (5) the archimedean pin: the quotient of g_1 on G - eps N
        def q_arch(eps):
            e = arb(eps); Ge = arb_mat(G)
            for i in range(K): Ge[i, i] = Ge[i, i] - e*N[i]
            return rayleigh(Ge, N, c, prec)
        up = lam.upper()
        arch = {"at_plus_lambda_upper": ball_fields(q_arch(up), prec), "at_minus_lambda_upper": ball_fields(q_arch(-up), prec),
                "at_half_lambda": ball_fields(q_arch(up/2), prec)}
        t3 = time.time()
        st = {"cell": cell, "delta": d, "K": K, "prec": prec, "primes": ke["primes"], "lambda1": ball_fields(lam, prec),
              "per_prime": per, "sum_logp_D": bstr(sumD, prec), "dilation": dil, "archimedean": arch,
              "slope_s": t1 - t0, "dilation_s": t2 - t1, "arch_s": t3 - t2,
              "verdict": "COMPUTED (balls; the containment flags are the claims the verifier gates)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or list(CELLS)):
        st = run(cell)
        pr = " ".join(f"p={p}:D={float(r['D']['mid']):.4f} lin/hi={r['lin_over_hi']:.5f} in={r['lin_in_bracket']}" for p, r in st["per_prime"].items())
        dl = st["dilation"]
        print(f"{cell:6s} {pr} | dilation {dl['status']} eps_hi {dl['eps_hi']} lin_in {dl['lin_in_bracket']} harmonic {dl['harmonic']} | arch +lam: {st['archimedean']['at_plus_lambda_upper']['upper']} -lam: {st['archimedean']['at_minus_lambda_upper']['lower']} [{st['slope_s']:.0f}s {st['dilation_s']:.0f}s {st['arch_s']:.0f}s]", flush=True)
