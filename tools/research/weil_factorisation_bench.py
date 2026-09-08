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
                               verified zeros plus the smooth-density tail with its oscillation resolved
                               (mpmath, dps 40; floating point) -- the 'factorisation that knows the zeros';
                               on a C_c^inf bump it agrees with the true form to 2.6e-16 (the calibration
                               that the bench measures the right object), on the Gram's approximate
                               minimiser to 2.1e-7 at delta = 1, K = 48 at the 6700-zero cut (a fluctuation
                               draw of order ghat(T)^2 ~ 7e-7; see zeros())
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

def zeros(delta, K, prec, zeros_file=None, cut=None):
    """The zero side as a quadratic form on coefficient vectors (mpmath floats, dps 40):
    q(c) = 2 sum_gamma ghat(gamma)^2 + the smooth-density tail above the last zero, ghat = sum c_k phihat_k.
    Returned as a callable. THE TAIL (round-305 F305-1): in the cosine basis ghat(r) = sin(ra) R(r) exactly, with
    R(r) = sum_k (-1)^k c_k 2r/(r^2 - w_k^2) rational, so the tail integrand sin^2(ra) R^2 L (L = log(r/2pi)/2pi) oscillates
    with period pi/a -- about 1e5 periods on [T, 100T] -- and a plain mp.quad over a few break points cannot resolve it
    (the first version's 4.3e-5 'deviation' of the minimiser at delta = 1 was a 1 percent error in a 0.6 percent tail).
    Now: sin^2 = 1/2 - cos(2ar)/2; the smooth half integrated on log-spaced pieces to infinity; the oscillatory half by
    parts twice, -sin(2aT)F(T)/(2a) - cos(2aT)F'(T)/(4a^2) with F = R^2 L (the neglected remainder is bounded by
    int |F''|/(4a^2) ~ F(T)/(2 a^2 T) -- 2.3e-10 of the quotient for the K = 48 minimiser at delta = 1; the third by-parts
    term itself is 9e-14 of it -- round-306 F306-2 corrected the first statement of this bound). Calibrations at
    delta = 1, K = 48 (relative Rayleigh-quotient deviations, floating point): a C_c^inf bump agrees to 2.6e-16; the
    Gram's approximate minimiser to 2.1e-7 at the 6700-zero cut -- a draw of the counting function's fluctuation at
    the cut, of order ghat(T)^2 ~ 7e-7 of the quotient; the signed deviation (candidate - true)/true changes sign
    between neighbouring cuts -- 31 times over 41 cuts from 3000 to 6700, reaching 6.1e-6 at the cut 3500 (6700: -2.1e-7;
    6650: +1.7e-6; 6600: +1.1e-6; 6000: -3.0e-7; 3000: +3.1e-6) -- so no lower end is a property of the cuts
    (round-306 F306-1, round-307 F307-1)."""
    import mpmath as mp
    mp.mp.dps = 40
    zf = zeros_file or os.path.join(HERE, "checkpoints", "zeta_zeros_6700.json")
    gam = [mp.mpf(z) for z in json.load(open(zf))]
    if cut is not None: gam = gam[:cut]     # the first `cut` zeros only (the cross-cut calibration)
    a = mp.mpf(delta)/2
    def phihat(k, r):
        w = k*mp.pi/a
        if k == 0: return 2*mp.sin(r*a)/r
        return mp.sin((r + w)*a)/(r + w) + mp.sin((r - w)*a)/(r - w)
    vals = [[phihat(k, g) for k in range(K)] for g in gam]
    T = gam[-1]
    ws = [k*mp.pi/a for k in range(K)]
    def q(c):
        cc = [mp.mpf(x.mid().str(60, radius=False)) if isinstance(x, arb) else mp.mpf(str(x)) for x in c]
        s = 2*sum(sum(cc[k]*v[k] for k in range(K))**2 for v in vals)
        R = lambda r: sum(((-1)**k)*cc[k]*2*r/(r*r - ws[k]**2) for k in range(K))     # ghat(r) = sin(ra) R(r)
        F = lambda r: R(r)**2*mp.log(r/(2*mp.pi))/(2*mp.pi)
        smooth = mp.quad(F, [T*mp.mpf(10)**(i/3) for i in range(0, 25)] + [mp.inf])
        osc = -mp.sin(2*a*T)*F(T)/(2*a) - mp.cos(2*a*T)*mp.diff(F, T)/(4*a*a)
        s += 2*(smooth - osc)/2
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
