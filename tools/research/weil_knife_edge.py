#!/usr/bin/env python3
"""Keyed producer: the KNIFE-EDGE of Weil positivity in the primes at the
seven slack-law cells (Theorem 1bo's substrate). For each cell delta and
each prime p <= e^delta, the shift eta of log p at which the true Weil form
on [-a, a] (delta = 2a; weil_prime_gram.py's Gram in balls) stops being
positive -- certified by a NEGATIVE Rayleigh ball of an explicit vector on
the perturbed form.

THE PERTURBED FORM. Q^eta moves the shells of one prime: every n = p^k has
log n -> k (log p + eta) and Lambda(n) = log p -> log p + eta, the other
primes and the archimedean term untouched:
  Q^eta(g) = Q(g) + [P_p(0) - P_p(eta)](g),
  P_p(eta)(g) = 2 sum_{k >= 1, u_k < 2a} (log p + eta) e^{-u_k/2} f_g(u_k),  u_k = k (log p + eta),
f_g the autocorrelation of g. A shell that leaves the window drops out
(f_g(u) = 0 for u >= 2a); one that enters is included.

THE VECTOR AND THE EVALUATION. g_1 = the Gram minimiser at K2 modes (the
certified 1bn vector, recomputed here: flint's approximate eigenvector,
its Rayleigh ball reproduced). With g_1 = sum c_k cos(omega_k t), the
autocorrelation at lag u is O(K):
  f_g(u) = sum_k c_k^2 f_kk(u) + 2 sum_l (-1)^l c_l omega_l sin(omega_l u) A_l,
  A_l = sum_{j != l} (-1)^j c_j / (omega_j^2 - omega_l^2)      (u-independent)
(the off-diagonal double sum of weil_prime_gram's f_jl collapses because the
bracket [omega_l sin omega_l u - omega_j sin omega_j u] splits). At eta = 0
this reproduces c^T P c from the Gram (gated by the verifier).

THE SEARCH. Downward shifts (log p -> log p - eta, eta > 0) for EVERY prime:
a geometric bracket from eta = lambda_1 doubled until the Rayleigh ball of
g_1 on Q^{-eta} is negative at its upper end, then geometric bisection to
relative width TOL: eta_lo (ball positive at its lower end) < eta_hi (ball
negative at its upper end). eta_hi is a certified point where Q^{-eta} is
NOT positive; eta_lo says only that g_1 does not witness it there. For
p = 2 at the cells flagged two_sided, both directions with the perturbed
Gram RE-MINIMISED at every step (its own approximate eigenvector, its
Rayleigh ball certified): the crossing of the perturbed ground state itself
to TOL; the re-minimised downward crossing must not exceed the fixed-vector
one (gated).

State per cell: the lambda_1 ball of g_1 and g_1's coefficients; per
prime: eta_lo, eta_hi, the two Rayleigh balls' ends, the evaluation count,
the O(K) shell sum at eta = 0; the two-sided record; timings. Usage: weil_knife_edge.py [cell ...]     (all cells when none given)
"""
import sys, os, json, math, time
from flint import arb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from weil_prime_gram import gram, minimiser, rayleigh

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("weil_knife_edge.py",), HERE))}
KEYFILE = os.path.join(HERE, "weil_knife_edge.py")

# the 1bn cells (delta, K2, prec as in true_form_cells.CELLS -- gated equal by the verifier)
CELLS = {
    "d1.0":  dict(delta=1.0,        K=120, prec=600,  two_sided=True),
    "d1.38": dict(delta=1.3828125,  K=140, prec=600,  two_sided=True),
    "d2.0":  dict(delta=2.0,        K=160, prec=700,  two_sided=True),
    "d2.3":  dict(delta=2.3,        K=260, prec=900,  two_sided=False),
    "d2.6":  dict(delta=2.6,        K=320, prec=1000, two_sided=False),
    "d3.0":  dict(delta=3.0,        K=400, prec=1100, two_sided=False),
    "d3.5":  dict(delta=3.5,        K=540, prec=1300, two_sided=False),
}
TOL = 1e-3          # relative width of the certified bracket
TOL2 = 1e-2         # for the re-minimised two-sided search
EVAL_CAP = 20000    # a search that has not bracketed by then reports it (the first run at delta = 3.5 spun on a midpoint of 0)

def geomid(lo, hi):
    """The geometric midpoint of a bracket, in log space: math.sqrt(lo*hi) underflows to 0 once lo*hi < 1e-308
    (delta = 3.5 has eta ~ 4e-167), and a midpoint of 0 re-evaluates the unperturbed form forever."""
    if lo == 0: return hi/2
    return math.exp(0.5*(math.log(lo) + math.log(hi)))

def ball_fields(rq, prec):
    with ctx.workprec(prec):
        up = rq.upper(); lo = rq.lower(); rad = rq.rad()
        return {"mid": rq.mid().str(30, radius=False),
                "rad_log2": float(rad.log()/arb(2).log()) if rad > 0 else None,
                "upper": up.str(30, radius=False), "lower": lo.str(30, radius=False),
                "ln_upper": float(up.log()) if up > 0 else None,
                "positive": bool(lo > 0), "negative": bool(up < 0)}

def primes_of(pp):
    out = []
    for n in pp:
        p = next(q for q in range(2, n + 1) if n % q == 0)
        if p not in out: out.append(p)
    return out

class Autocorr:
    """f_g(u) for g = sum c_k cos(omega_k t) on [-a, a], O(K) per lag."""
    def __init__(self, c, a, prec):
        self.prec = prec
        with ctx.workprec(prec):
            K = len(c); self.K = K; self.a = a; self.twoa = 2*a
            pi = arb.pi()
            self.om = [arb(k)*pi/a for k in range(K)]
            self.c = c
            om2 = [o*o for o in self.om]
            self.A = []
            for l in range(K):
                s = arb(0)
                for j in range(K):
                    if j != l:
                        s += (-c[j] if j % 2 else c[j])/(om2[j] - om2[l])
                self.A.append(s)
    def __call__(self, u):
        with ctx.workprec(self.prec):
            c, om, twoa = self.c, self.om, self.twoa
            f = c[0]*c[0]*(twoa - u)
            for k in range(1, self.K):
                f += c[k]*c[k]*((twoa - u)*(om[k]*u).cos() - (om[k]*u).sin()/om[k])/2
            s = arb(0)
            for l in range(self.K):
                t = c[l]*om[l]*(om[l]*u).sin()*self.A[l]
                s += -t if l % 2 else t
            return f + 2*s

def prime_shells(fg, p, eta, prec):
    """P_p(eta)(g) = 2 sum_k (log p + eta) e^{-u_k/2} f_g(u_k), u_k = k (log p + eta) < 2a."""
    with ctx.workprec(prec):
        lp = arb(p).log() + arb(eta)
        tot = arb(0); k = 1
        while k*lp < fg.twoa:
            u = k*lp
            tot += 2*lp*(-u/2).exp()*fg(u)
            k += 1
        return tot

def perturbed_gram(G, p, eta, K, a, prec):
    """G + P_p(0) - P_p(eta) as a matrix (for the re-minimised search)."""
    with ctx.workprec(prec):
        twoa = 2*a; pi = arb.pi(); om = [arb(k)*pi/a for k in range(K)]
        M = arb_mat(K, K)
        for e, sign in ((arb(0), 1), (arb(eta), -1)):
            lp = arb(p).log() + e; kk = 1
            while kk*lp < twoa:
                u = kk*lp; w = 2*lp*(-u/2).exp()*sign
                su = [(o*u).sin() for o in om]; cu = [(o*u).cos() for o in om]
                for j in range(K):
                    for k in range(j, K):
                        if j == k:
                            v = w*((twoa - u) if k == 0 else ((twoa - u)*cu[k] - su[k]/om[k])/2)
                        else:
                            sg = -1 if (j + k) % 2 else 1
                            v = w*sg*(om[k]*su[k] - om[j]*su[j])/(om[j]*om[j] - om[k]*om[k])
                        M[j, k] += v
                        if j != k: M[k, j] += v
                kk += 1
        # note: the loop above SUBTRACTS P_p(eta) (sign -1) and ADDS P_p(0) (sign +1): M = P_p(0) - P_p(eta)
        return G + M

def search_fixed(num, den, fg, p, lam_up, prec):
    """Downward shift, fixed vector: bracket [eta_lo, eta_hi] with Q^{-eta_lo}(g_1) > 0 and Q^{-eta_hi}(g_1) < 0 certified."""
    with ctx.workprec(prec):
        P0 = prime_shells(fg, p, 0, prec)
        def q(eta):
            return (num + P0 - prime_shells(fg, p, -eta, prec))/den
        evals = 0; eta = float(lam_up); lo = 0.0; r_lo = None
        while True:
            r = q(eta); evals += 1
            if r.upper() < 0: hi = eta; r_hi = r; break
            if not (r.lower() > 0): return {"status": "ambiguous", "eta": eta, "ball": ball_fields(r, prec), "evals": evals}
            lo = eta; r_lo = r; eta *= 2
            if eta > 4: return {"status": "no crossing below 4", "eta_lo": lo, "evals": evals}
        while lo == 0 or hi/lo > 1 + TOL:
            mid = geomid(lo, hi)
            if not (lo < mid < hi): return {"status": "bracket stalled", "eta_lo": lo, "eta_hi": hi, "evals": evals}
            r = q(mid); evals += 1
            if r.upper() < 0: hi = mid; r_hi = r
            elif r.lower() > 0: lo = mid; r_lo = r
            else: return {"status": "ambiguous", "eta": mid, "ball": ball_fields(r, prec), "evals": evals}
            if evals > EVAL_CAP: return {"status": "evaluation cap", "eta_lo": lo, "eta_hi": hi, "evals": evals}
        return {"status": "bracketed", "eta_lo": lo, "eta_hi": hi, "q_lo": ball_fields(r_lo, prec), "q_hi": ball_fields(r_hi, prec),
                "evals": evals, "hi_over_lambda": hi/float(lam_up)}

def search_reminimised(G, N, p, K, a, prec, sign, start):
    """Shift log p by sign*eta, re-minimise, certify; bracket to TOL2. Returns the crossing bracket."""
    with ctx.workprec(prec):
        def q(eta):
            Ge = perturbed_gram(G, p, sign*eta, K, a, prec)
            c, ev = minimiser(Ge, N, prec)
            return rayleigh(Ge, N, [arb(x) for x in c], prec)
        evals = 0; eta = start; lo = 0.0; r_lo = None
        while True:
            r = q(eta); evals += 1
            if r.upper() < 0: hi = eta; r_hi = r; break
            if not (r.lower() > 0): return {"status": "ambiguous", "eta": eta, "ball": ball_fields(r, prec), "evals": evals}
            lo = eta; r_lo = r; eta *= 2
            if eta > 4: return {"status": "no crossing below 4", "eta_lo": lo, "evals": evals}
        while lo == 0 or hi/lo > 1 + TOL2:
            mid = geomid(lo, hi)
            if not (lo < mid < hi): return {"status": "bracket stalled", "eta_lo": lo, "eta_hi": hi, "evals": evals}
            r = q(mid); evals += 1
            if r.upper() < 0: hi = mid; r_hi = r
            elif r.lower() > 0: lo = mid; r_lo = r
            else: return {"status": "ambiguous", "eta": mid, "ball": ball_fields(r, prec), "evals": evals}
        return {"status": "bracketed", "sign": sign, "eta_lo": lo, "eta_hi": hi, "q_lo": ball_fields(r_lo, prec),
                "q_hi": ball_fields(r_hi, prec), "evals": evals}

def run(cell):
    cfg = CELLS[cell]
    params = {"deps": DEPS, "cell": cell, **cfg, "tol": TOL, "tol2": TOL2, "round": 1}
    name = f"knife_edge_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None:
        return st
    d, K, prec = cfg["delta"], cfg["K"], cfg["prec"]
    t0 = time.time()
    G, N, pp = gram(d, K, prec); t1 = time.time()
    c, ev = minimiser(G, N, prec); t2 = time.time()
    with ctx.workprec(prec):
        a = arb(d)/2
        c = [arb(x) for x in c]
        v = arb_mat(K, 1)
        for i in range(K): v[i, 0] = c[i]
        num = (v.transpose()*G*v)[0, 0]
        den = arb(0)
        for i in range(K): den += N[i]*c[i]*c[i]
        rq = num/den
        lam_up = rq.upper()
        fg = Autocorr(c, a, prec)
        # consistency: the O(K) shell sum at eta = 0 against the Gram's own prime part is the verifier's; here we store both
        primes = primes_of(pp)
        per_prime = {}
        for p in primes:
            per_prime[str(p)] = search_fixed(num, den, fg, p, lam_up, prec)
            per_prime[str(p)]["shell_sum_eta0"] = (prime_shells(fg, p, 0, prec)/den).str(30, radius=False)
        t3 = time.time()
        two = None
        if cfg["two_sided"]:
            two = {"p": 2,
                   "minus": search_reminimised(G, N, 2, K, a, prec, -1, per_prime["2"]["eta_hi"]/4),
                   "plus": search_reminimised(G, N, 2, K, a, prec, +1, per_prime["2"]["eta_hi"])}
        t4 = time.time()
        st = {"cell": cell, "delta": d, "K": K, "prec": prec, "prime_powers": pp, "primes": primes,
              "lambda1": ball_fields(rq, prec), "eig_ln": float(ev.log()) if ev > 0 else None,
              "coeffs": [x.mid().str(int(prec*0.31) + 10, radius=False) for x in c],   # g_1 itself, for the verifier's live checks
              "per_prime": per_prime, "two_sided": two,
              "gram_s": t1 - t0, "eig_s": t2 - t1, "search_s": t3 - t2, "two_sided_s": t4 - t3,
              "verdict": "CERTIFIED (each eta_hi a downward shift of log p at which the perturbed form has a negative Rayleigh ball)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or list(CELLS)):
        st = run(cell)
        pr = "  ".join(f"p={p}: eta_hi {r['eta_hi']:.3e} ({r['hi_over_lambda']:.2f} lam)" if r.get("status") == "bracketed" else f"p={p}: {r['status']}"
                       for p, r in st["per_prime"].items())
        ts = ""
        if st["two_sided"]:
            m, q = st["two_sided"]["minus"], st["two_sided"]["plus"]
            ts = f"  | two-sided p=2: minus {m.get('eta_hi')} plus {q.get('eta_hi')}"
        print(f"{cell:6s} delta {st['delta']:<9} lambda1 ln {st['lambda1']['ln_upper']:.4f}  {pr}{ts}  "
              f"[gram {st['gram_s']:.0f}s eig {st['eig_s']:.0f}s search {st['search_s']:.0f}s two {st['two_sided_s']:.0f}s]", flush=True)
