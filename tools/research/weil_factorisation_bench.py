#!/usr/bin/env python3
"""The factorisation bench (Theorem 1bo(iv)): any CANDIDATE for the true
Weil form on a window -- a proposed factorisation Q(g) = ||S g||^2, a
proposed kernel, a proposed arithmetic -- is a Gram in the even cosine
basis of weil_prime_gram.py; the bench compares it with the TRUE Gram
(balls; primes <= e^delta, digamma archimedean term, closed-form pole) at a
cell, entry by entry and on the certified minimiser's Rayleigh quotient.
A candidate that does not reproduce the true Gram to the balls' width at
every cell is not the form; a candidate that does is not thereby a
factorisation (the bench is a filter, never a proof -- what it can prove
is a difference).

CANDIDATES BUILT IN (the calibrations):
  zeros(delta, K, prec)        the zero side as a quadratic form: 2 sum_gamma ghat(gamma)^2 over the 6700
                               verified zeros plus the smooth-density tail (mpmath, dps 40) -- the
                               'factorisation that knows the zeros'; on a C_c^inf bump it agrees with the
                               true form to 1e-16 (the calibration that the bench measures the right
                               object); on the minimiser, a near-null vector with edge structure, to ~1e-5
                               at delta = 1 -- the zero sum over 6700 zeros converges as log T / T there
  archimedean(delta, K, prec)  the true Gram with the primes dropped (P = 0): the geometry of the Gamma
                               factor alone -- rejected by the prime part, a certified margin
  shifted(delta, K, prec, p, eta)  the true Gram with log p -> log p + eta (weil_knife_edge.py's perturbed
                               form): rejected at eta = the knife-edge shift -- the bench resolves it (the
                               certified Rayleigh quotient of the minimiser turns negative on the candidate)

compare(G, C, N, vectors, prec) returns, for a ball candidate, the entrywise max |G - C| (upper end) and the
Frobenius-relative deviation, and for every candidate the Rayleigh quotients of the named vectors on both.
Usage: weil_factorisation_bench.py <zeros|archimedean|shifted> <delta> <K> <prec> [p eta]
"""
import sys, os, json, math
from flint import arb, acb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from weil_prime_gram import gram, minimiser, rayleigh

def true_gram(delta, K, prec):
    return gram(delta, K, prec)

def archimedean(delta, K, prec):
    """The true Gram with P = 0: recomputed by adding the prime part back (the shells of every prime <= e^delta)."""
    G, N, pp = gram(delta, K, prec)
    with ctx.workprec(prec):
        a = arb(delta)/2
        C = arb_mat(G)
        for n in pp:
            p = next(q for q in range(2, n + 1) if n % q == 0)
            C = C + _shell_matrix(arb(n).log(), arb(p).log(), K, a, prec)
        return C, N, pp

def shifted(delta, K, prec, p, eta):
    """The true Gram with the shells of p moved: log p -> log p + eta (weights and positions)."""
    G, N, pp = gram(delta, K, prec)
    with ctx.workprec(prec):
        a = arb(delta)/2; twoa = 2*a
        C = arb_mat(G)
        for e, sign in ((arb(0), +1), (arb(eta), -1)):
            lp = arb(p).log() + e; k = 1
            while k*lp < twoa:
                C = C + sign*_shell_matrix(k*lp, lp, K, a, prec)
                k += 1
        return C, N, pp

def _shell_matrix(u, lp, K, a, prec):
    """2 lp e^{-u/2} f_jk(u): one shell's contribution to the prime part P (positive; G carries -P)."""
    with ctx.workprec(prec):
        twoa = 2*a; pi = arb.pi(); om = [arb(k)*pi/a for k in range(K)]
        w = 2*lp*(-u/2).exp()
        su = [(o*u).sin() for o in om]; cu = [(o*u).cos() for o in om]
        M = arb_mat(K, K)
        for j in range(K):
            for k in range(j, K):
                if j == k:
                    v = w*((twoa - u) if k == 0 else ((twoa - u)*cu[k] - su[k]/om[k])/2)
                else:
                    sg = -1 if (j + k) % 2 else 1
                    v = w*sg*(om[k]*su[k] - om[j]*su[j])/(om[j]*om[j] - om[k]*om[k])
                M[j, k] = v; M[k, j] = v
        return M

def zeros(delta, K, prec, zeros_file=None, tail_to_inf=False):
    """The zero side as a quadratic form on coefficient vectors (mpmath floats, dps 40):
    q(c) = 2 sum_gamma ghat(gamma)^2 + the smooth-density tail above the last zero, ghat = sum c_k phihat_k.
    Returned as a callable (the tail is a single quadrature per vector; the entrywise Gram in the raw cosine
    basis converges only as log T / T over the zeros -- the basis elements are discontinuous at +-a -- so
    the calibration is on vectors: a C_c^inf bump agrees to 1e-16, the minimiser to ~1e-5 at delta = 1). The tail is
    integrated over [T, 100T] by default; tail_to_inf=True continues it to infinity (round-304 observation: at delta = 1
    the minimiser's deviation is 4.3e-5 with the tail to 100T and 5.2e-5 to infinity -- the truncation is not the cause)."""
    import mpmath as mp
    mp.mp.dps = 40
    zf = zeros_file or os.path.join(HERE, "checkpoints", "zeta_zeros_6700.json")
    gam = [mp.mpf(z) for z in json.load(open(zf))]
    a = mp.mpf(delta)/2
    def phihat(k, r):
        w = k*mp.pi/a
        if k == 0: return 2*mp.sin(r*a)/r
        return mp.sin((r + w)*a)/(r + w) + mp.sin((r - w)*a)/(r - w)
    vals = [[phihat(k, g) for k in range(K)] for g in gam]
    T = gam[-1]
    def q(c):
        cc = [mp.mpf(x.mid().str(60, radius=False)) if isinstance(x, arb) else mp.mpf(str(x)) for x in c]
        ghat = lambda r: sum(cc[k]*phihat(k, r) for k in range(K))
        s = 2*sum(sum(cc[k]*v[k] for k in range(K))**2 for v in vals)
        pts = [T, 2*T, 10*T, 100*T] + ([1000*T, 10000*T, mp.inf] if tail_to_inf else [])
        s += 2*mp.quad(lambda r: ghat(r)**2*mp.log(r/(2*mp.pi))/(2*mp.pi), pts)
        return s
    return q

def bump_vector(delta, K):
    """The cosine coefficients of the C_c^inf bump exp(-1/(1 - (t/a)^2)) on [-a, a] (mpmath, dps 40)."""
    import mpmath as mp
    mp.mp.dps = 40
    a = mp.mpf(delta)/2
    bump = lambda t: mp.e**(-1/(1 - (t/a)**2)) if abs(t) < a else mp.mpf(0)
    return [mp.quad(lambda t: bump(t)*mp.cos(k*mp.pi*t/a), [-a, 0, a])/(a if k else 2*a) for k in range(K)]

def compare(G, C, N, vectors, prec):
    """For a ball candidate C (arb_mat): the entrywise max |G - C| (upper end) and the Frobenius-relative
    deviation, plus the Rayleigh quotients of each vector on G and on C. For a callable candidate (a quadratic
    form q(c)): the Rayleigh quotients only. `vectors` is a dict name -> coefficient list."""
    with ctx.workprec(prec):
        K = G.nrows()
        out = {}
        if isinstance(C, arb_mat):
            mx = arb(0); fro_d = arb(0); fro_g = arb(0)
            for j in range(K):
                for k in range(K):
                    d = G[j, k] - C[j, k]; ad = abs(d)
                    if ad.upper() > mx.upper(): mx = ad
                    fro_d += d*d; fro_g += G[j, k]*G[j, k]
            out["max_abs"] = mx.upper().str(10, radius=False)
            out["fro_rel"] = (fro_d.sqrt()/fro_g.sqrt()).upper().str(10, radius=False)
        for name, c in vectors.items():
            ca = [x if isinstance(x, arb) else arb(str(x)) for x in c]
            den = arb(0)
            for i in range(K): den += N[i]*ca[i]*ca[i]
            rt = rayleigh(G, N, ca, prec)
            if isinstance(C, arb_mat):
                rc = rayleigh(C, N, ca, prec)
            else:
                rc = arb(str(C(c)))/den
            out[name] = {"rq_true": rt, "rq_cand": rc,
                         "rel": float(abs(rc.mid() - rt.mid())/abs(rt.mid())) if rt.mid() != 0 else None}
        return out

def bench(which, delta, K, prec, p=None, eta=None):
    G, N, pp = gram(delta, K, prec)
    c, ev = minimiser(G, N, prec)
    with ctx.workprec(prec):
        vectors = {"minimiser": [arb(x) for x in c]}
    if which == "zeros":
        C = zeros(delta, K, prec); vectors["bump"] = bump_vector(delta, K)
    elif which == "archimedean":
        C, _, _ = archimedean(delta, K, prec)
    elif which == "shifted":
        C, _, _ = shifted(delta, K, prec, p, eta)
    else:
        raise ValueError(which)
    r = compare(G, C, N, vectors, prec)
    r["candidate"] = which; r["delta"] = delta; r["K"] = K; r["prec"] = prec; r["prime_powers"] = pp
    return r

if __name__ == "__main__":
    which = sys.argv[1]; d = float(sys.argv[2]); K = int(sys.argv[3]); prec = int(sys.argv[4])
    p = int(sys.argv[5]) if len(sys.argv) > 5 else None; eta = float(sys.argv[6]) if len(sys.argv) > 6 else None
    r = bench(which, d, K, prec, p, eta)
    ent = f"max|G - C| {r['max_abs']}  Frobenius-rel {r['fro_rel']}  " if "max_abs" in r else ""
    vec = "  ".join(f"{n}: true {r[n]['rq_true'].str(12)} candidate {r[n]['rq_cand'].str(12)} rel {r[n]['rel']:.2e}"
                    for n in ("minimiser", "bump") if n in r)
    print(f"{which} delta {d} K {K}: {ent}{vec}", flush=True)
