#!/usr/bin/env python3
"""The excited states' laws at a cell (Theorem 1bw's second keyed producer), from rung_anatomy's census checkpoint.

THE FACTORISATION. ghat_k = ghat_1 H_k C_k with H_k = prod_{holes} (1 - r^2/h^2) (degree 2(k - 1)) and C_k the ratio of the
remaining zero products of rung k and the ground state (the sinc zeros cancel): exact once every designed pair is located.
Rung k is "in the law" when it and every rung below it have every designed pair real -- located, or exactly one unlocated
and placed by the sum rule (1bu(ii)'s K - 2 branch: the remainder negative, |tau| = |remainder|^(-1/2), a real pair joining the
exterior product) -- and exactly k - 1 hole zeros.

THE CURVATURE LAW. ln C_k(r) = -Dkappa_k r^2 + O(r^4) with Dkappa_k = kappa_k - kappa_1 - sum_h h^-2 (the r^2 coefficient of
ln prod (1 - r^2/tau^2) is -sum tau^-2: an identity), with the accounting Dkappa_k = [sum_{E_k} tau^-2 - sum_{E_1} tau^-2] -
sum_{freed} z^-2 over the ground state's dodging zeros at the zeta zeros it dodges and rung k does not (the residual of the accounting is the
dodging displacements' part); the remainder measured as the ratio (-ln C_k(r)/r^2)/Dkappa_k at r = 5, 10, 20, 40; and
tau_eff = sqrt((k - 1)/(-Dkappa_k)), the effective height of the exterior pair each hole pair replaces.

THE BI-ORTHOGONAL LAW. The rungs are N-orthogonal, int ghat_j ghat_k = 0, so H_k is orthogonal to H_j (j < k) under the pair
weight ghat_1^2 C_k C_j: k - 1 linear conditions that determine the even polynomial H_k of degree 2(k - 1) up to scale. The
law is an interior statement (the Gaussian truncation of C grows beyond the interior), so the integrals run over [0, T_1/2],
T_1 the ground state's dodging edge at the hole tolerance 0.2 (1bu's T_D, at 0.05, lies 2.9-8.5% below it), where ghat_1^2 carries
all but a part below 1e-6 of its mass (mass_interior, the half-line integral against pi; measured 2.4e-8 at delta = 2.3).
Three solutions, each against the censused holes: (E) the exact census C's and census H_j (the factorisation's check);
(G) the Gaussian truncation C_j = exp(-Dkappa_j r^2) with census H_j; (R) the Gaussian truncation with the recursion's own
H_j -- the whole ladder of hole polynomials from ghat_1 and the numbers Dkappa_2..Dkappa_k alone; (M) the mangle, the
recursion with every Dkappa's sign flipped (the correction the wrong way). Also the naive nodes (A,
the orthogonal polynomials of ghat_1^2 on [0, 1.6 T_0], Theorem 1bu(iii)'s law) and the Gaussian-weight nodes (B, the
orthogonal polynomials of ghat_1^2 exp(-2 Dkappa_k r^2) on the same interior). Gauss-Legendre grids (6000 nodes; ghat_1 on the
grid from its census -- the Hadamard product over the designed pairs times the sinc tail in closed form, checked against the
direct evaluation on the low interior: g1_product_check), the linear solve and the roots at 80 digits (mpmath), the polynomial in s = (r/R)^2 with R the cutoff
(the moment matrix of the monomials on [0, 1] is Hilbert-like; the scale 10 with 40 digits lost the degrees above 6 at delta = 3.5).

Checkpoints rung_laws_<cell>_<key>.json, content-keyed over the executable content of the import closure (rung_anatomy.py
included) plus the census checkpoint's key. Floating point; no Riemann Hypothesis consequence."""
import sys, os, json, math, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import mpmath as mp
from flint import arb, ctx
import ladder_caster as LC
import rung_anatomy as RA
import ckpt_key

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(ckpt_key.producer_closure(("rung_laws.py",), HERE))}
KEYFILE = os.path.join(HERE, "rung_laws.py")
CUT = 0.5                      # the interior: [0, CUT x T_1], T_1 the ground state's dodging edge at the hole tolerance 0.2
R_EVAL = (5.0, 10.0, 20.0, 40.0)
NODES = 6000

def lnprod(zs, r):
    zs = np.asarray(zs, dtype=float); return float(np.sum(np.log(np.abs(1 - r*r/(zs*zs)))))

DPS = 80                       # the moment matrix of the monomials in s = (r/R)^2 on [0, 1] is Hilbert-like: 80 digits for degree 12

def biorth(k, lnCk, lnCj, Hj, x, wA, R):
    """the even polynomial H = sum_m c_m (r/R)^{2m}, c_{k-1} = 1 (R the interior's cutoff, so s = (r/R)^2 lies in [0, 1]),
    orthogonal to H_j (j < k) under ghat_1^2 C_k C_j on the grid x with the base weight wA = ghat_1^2 dr; its positive real
    roots in r (sorted) and the count of its other roots."""
    n = k - 1
    with mp.workdps(DPS):
        xs = [mp.mpf(float(t))/R for t in x]
        rows = []; rhs = []
        for j in range(1, k):
            w = wA*np.exp(lnCk + lnCj[j])
            Hjv = np.array([float(np.prod([1 - t*t/(h*h) for h in Hj[j]])) if Hj[j] else 1.0 for t in x])
            base = [mp.mpf(float(v)) for v in w*Hjv]
            rows.append([mp.fsum(base[i]*xs[i]**(2*m) for i in range(len(xs))) for m in range(n)])
            rhs.append(-mp.fsum(base[i]*xs[i]**(2*n) for i in range(len(xs))))
        c = mp.lu_solve(mp.matrix(rows), mp.matrix(rhs))
        coeffs = [c[m] for m in range(n)] + [mp.mpf(1)]
        roots = mp.polyroots(list(reversed(coeffs)), maxsteps=400, extraprec=400)
        out = sorted(float(R*mp.sqrt(rt.real)) for rt in roots if abs(rt.imag) < 1e-20 and rt.real > 0)
        return out, len(roots) - len(out)

def run(cell):
    cen = RA.run(cell)
    params = {"deps": DEPS, "cell": cell, "census_key": ckpt_key.code_key(RA.KEYFILE, RA.params_for(cell)), "cut": CUT, "r_eval": R_EVAL, "nodes": NODES, "dps": DPS, "round": 1}
    name = f"rung_laws_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None: return st
    t0 = time.time()
    d, K, prec, T0 = cen["delta"], cen["K"], cen["prec"], cen["T0"]; a = d/2
    rungs = cen["rungs"]; g1 = rungs[0]
    def placed(r):
        """1bu(ii)'s K - 2 branch: exactly one designed pair unlocated and the sum rule's remainder negative places a real pair at
        |tau| = |remainder|^(-1/2); it joins the exterior product. None when every pair is located; False when the remainder's
        sign or the count refuses the placement (a complex pair, or more than one unlocated)."""
        if r["n_complex"] == 0: return None
        if r["n_complex"] == 1 and r["sum_rule_residual"] < 0: return abs(r["sum_rule_residual"])**-0.5
        return False
    def zeros_of(r):
        p = placed(r); return [z for _, z in r["dodging"]] + list(r["holes"]) + list(r["exterior"]) + ([p] if p else [])
    def whole(r): return placed(r) is not False
    Z1 = zeros_of(g1); D1 = {round(g, 9): z for g, z in g1["dodging"]}
    assert whole(g1), "the ground state's census must be complete or placed"
    Rg = CUT*g1["edge"]
    # ghat_1 on the grids from its own census: the Hadamard product over the designed pairs (the placed one included) times the
    # sinc tail prod_{j >= K} (1 - r^2/omega_j^2) = [sin(ra)/(ra)]/prod_{1 <= j < K} (1 - r^2/omega_j^2) -- exact for an even entire
    # function of exponential type with sum |tau|^-2 < infinity (no exponential factor), as 1bu(ii). The eigenvector's float64
    # coefficients floor the transform at e^-42 across the dodging region (the true values fall far below), and the polynomial
    # factors of the pair weights then swamp the interior from that floor: the product has no floor.
    omf = np.arange(1, K)*np.pi/a
    def ln_g1sq(t): return 2*(math.log(abs(g1["g0"])) + lnprod(Z1, t) + math.log(abs(math.sin(t*a)/(t*a))) - lnprod(omf, t))
    x, wq = np.polynomial.legendre.leggauss(NODES); x = 0.5*Rg*(x + 1) + 1e-7; wq = 0.5*Rg*wq
    wA = wq*np.exp(np.array([ln_g1sq(t) for t in x]))
    RA_ = 1.6*T0; xA, wqA = np.polynomial.legendre.leggauss(NODES); xA = 0.5*RA_*(xA + 1) + 1e-7; wqA = 0.5*RA_*wqA
    wAA = wqA*np.exp(np.array([ln_g1sq(t) for t in xA]))
    # the self-check: the product against the direct evaluation (the coefficients in balls at the working precision) on the low
    # interior, where the direct evaluation is far above its float64 floor
    with ctx.workprec(prec):
        gh1 = LC.ghat_factory([arb(x_) for x_ in cen["vecs"][0]], arb(a), K)
        g1_check = max(abs(ln_g1sq(t) - 2*float(abs(gh1(arb(t))).log())) for t in (2.0, 5.0, 10.0, 20.0, 30.0))
    mass_in = float(np.sum(wA))/math.pi          # the half-line integral of ghat_1^2 over the interior against pi ||g||^2 = pi (Plancherel)
    nodesA = LC.poly_nodes(xA, wAA, min(len(rungs) - 1, LC.NODES_MAX))
    Cex = {1: np.zeros_like(x)}; Cga = {1: np.zeros_like(x)}; Hc = {1: []}; Hr = {1: []}
    laws = []
    for r in rungs[1:]:
        k = r["k"]; H = sorted(r["holes_fine"])
        ok_rung = whole(r) and len(H) == k - 1 and all(whole(rr) and len(rr["holes_fine"]) == rr["k"] - 1 for rr in rungs[1:k - 1])
        if not ok_rung: break
        Zk = zeros_of(r)
        dk = r["kappa"] - g1["kappa"] - sum(1.0/h/h for h in r["holes"])
        Dk = {round(g, 9): z for g, z in r["dodging"]}; freed = [z for g, z in D1.items() if g not in Dk]
        ext_k = list(r["exterior"]) + ([placed(r)] if placed(r) else []); ext_1 = list(g1["exterior"]) + ([placed(g1)] if placed(g1) else [])
        ext_diff = float(np.sum(1.0/np.asarray(ext_k)**2) - np.sum(1.0/np.asarray(ext_1)**2)); freed_sum = sum(1.0/z/z for z in freed)
        lnC0 = lnprod(Zk, 1e-3) - lnprod(Z1, 1e-3) - lnprod(r["holes"], 1e-3)
        ratio = {str(rv): (-(lnprod(Zk, rv) - lnprod(Z1, rv) - lnprod(r["holes"], rv) - lnC0)/rv/rv)/dk for rv in R_EVAL}
        lnC = np.array([lnprod(Zk, t) - lnprod(Z1, t) - lnprod(r["holes"], t) for t in x]); Cex[k] = lnC - lnC[0]; Cga[k] = -dk*x*x
        nB = LC.poly_nodes(x, wA*np.exp(2*Cga[k]), k - 1)[k - 2]
        nE, cE = biorth(k, Cex[k], Cex, Hc, x, wA, Rg)
        nG, cG = biorth(k, Cga[k], Cga, Hc, x, wA, Rg)
        nR, cR = biorth(k, Cga[k], Cga, Hr, x, wA, Rg)
        Cm = {j: -Cga[j] for j in Cga}; nM, cM = biorth(k, Cm[k], Cm, Hr, x, wA, Rg)          # the mangle: the correction's sign flipped
        Hc[k] = H; Hr[k] = nR
        dev = lambda n: max(abs(h - m)/m for h, m in zip(H, n)) if len(n) == len(H) else None
        nA = nodesA[k - 2] if k - 2 < len(nodesA) else None
        laws.append({"k": k, "holes": H, "placed": placed(r), "Dkappa": dk, "tau_eff": math.sqrt((k - 1)/(-dk)) if dk < 0 else None, "ext_diff": ext_diff, "freed_sum": freed_sum,
                     "n_freed": len(freed), "accounting_residual": dk - (ext_diff - freed_sum), "ratio_r": ratio,
                     "nodes_A": nA, "nodes_B": nB, "nodes_E": nE, "nodes_G": nG, "nodes_R": nR, "complex_E": cE, "complex_G": cG, "complex_R": cR,
                     "nodes_M": nM, "complex_M": cM, "dev_M": dev(nM),
                     "dev_A": dev(nA) if nA else None, "dev_B": dev(nB), "dev_E": dev(nE), "dev_G": dev(nG), "dev_R": dev(nR)})
    st = {"cell": cell, "delta": d, "T0": T0, "K": K, "cut": Rg, "mass_interior": mass_in, "g1_product_check": g1_check, "n_in_law": len(laws), "laws": laws, "placed_ground": placed(g1), "secs": time.time() - t0,
          "verdict": "COMPUTED (floating point, the bi-orthogonal solve at 80 digits, from the census checkpoint)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or list(RA.CELLS)):
        st = run(cell)
        print(f"{cell}: K {st['K']}, cut {st['cut']:.1f}, interior mass {st['mass_interior']:.6f}, product check {st['g1_product_check']:.1e}, rungs in the law {st['n_in_law']}; {st['secs']:.0f}s")
        for L in st["laws"]:
            print(f"  rung {L['k']:2d}: Dkappa {L['Dkappa']:+.4e} (tau_eff {L['tau_eff']:.1f}; accounting {L['accounting_residual']:+.1e}; ratio r=40 {L['ratio_r']['40.0']:.4f}); "
                  f"dev A {L['dev_A']:.1e} B {L['dev_B']:.1e} E {L['dev_E']:.1e} G {L['dev_G']:.1e} R {L['dev_R']:.1e} M {L['dev_M']:.1e}", flush=True)
