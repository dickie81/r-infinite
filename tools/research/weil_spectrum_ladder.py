#!/usr/bin/env python3
"""Keyed producer: the LOW SPECTRUM of the true Weil form at the seven cells
(Theorem 1br's substrate) -- certified upper bounds on lambda_k(delta), the
k-th eigenvalue of Q on L^2(-a, a) (even sector), for k = 1..m -- against
the PROLATE LEAKAGE LADDER 1 - chi_n(c) at the horizon c = T_0 = 2 pi e^delta.

THE LADDER (certified). Q's Rayleigh quotient on the even cosine span is the
pencil (G, N) of weil_prime_gram.py, every entry a ball. For the k lowest
approximate eigenvectors R = [v_1 .. v_k] (flint's approximate eigensolver on
the midpoints), the projected pencil (R^T G R, R^T N R) is a k x k pencil in
balls, and by Courant-Fischer
    lambda_k(Q) <= max_{v in span R} Q(v)/||v||^2 = lambda_max(R^T G R, R^T N R):
the largest eigenvalue of the projected pencil is a rigorous upper bound on
the k-th eigenvalue of the true form, whatever the vectors are. It is
enclosed by flint's certified eigenvalue enclosures of the ball matrix
M^{-1} A (similar to the symmetric M^{-1/2} A M^{-1/2}; the enclosures contain
the eigenvalues of every matrix in the ball, hence of the exact one). Stored
per k: the upper end (ln), the enclosure width, the approximate eigenvalue.

THE SHADOW (computed, not certified). The prolate spheroidal wave functions
psi_n at bandwidth c on [-1, 1] are the eigenfunctions of the finite Fourier
transform F_c psi(x) = int e^{icxy} psi(y) dy, eigenvalues mu_n = i^n |mu_n|,
|mu_n|^2 = 2 pi lambda_n / c with lambda_n the time-band concentration.
Theorems 1bm/1bn compared the ground state with 1 - chi_2 in the paper's
convention chi_j := sqrt(lambda_{2j}) (true_form_cells.chi2_deficit: 1 -
chi_2 = 1 - sqrt(lambda_4), the prolate of ORDER 4 -- CCM's h_lambda is built
from psi_0 and psi_4, the Fourier-(+1) eigenfunctions, orders n = 0 mod 4).
Here the whole ladder: for every even order n = 0, 2, ..., 4m, lambda_n =
(c/pi) (d_0^{(n)}/psi_n(0))^2 from the Legendre tridiagonal (ccm_trial_vector's
construction for all even orders), at two Legendre cutoffs (c + 300, c + 500)
whose agreement is the convergence check; stored as ln(1 - sqrt(lambda_n)),
the paper's ln(1 - chi_{n/2}). The rung-by-rung comparison the verifier
gates: rung k of the true form against ORDER 4k (the k-th Fourier-(+1)
prolate beyond psi_0; chi_{2k} in the paper's indexing), the observed
pattern being lambda_1 ~ 1 - chi_2, lambda_2 ~ 1 - chi_4, lambda_3 ~ 1 - chi_6
with offsets falling along the ladder.

State per cell: m, the certified ladder, the approximate ladder, the prolate
ladder at both cutoffs, timings. Usage: weil_spectrum_ladder.py [cell ...]
"""
import sys, os, json, math, time
from flint import arb, acb, arb_mat, acb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from weil_prime_gram import gram

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("weil_spectrum_ladder.py",), HERE))}
KEYFILE = os.path.join(HERE, "weil_spectrum_ladder.py")

# the 1bn cells (delta, K2, prec); m = the number of rungs; tprec the prolate precision (as true_form_cells)
CELLS = {
    "d1.0":  dict(delta=1.0,        K=120, prec=600,  m=10, tprec=400),
    "d1.38": dict(delta=1.3828125,  K=140, prec=600,  m=12, tprec=400),
    "d2.0":  dict(delta=2.0,        K=160, prec=700,  m=18, tprec=500),
    "d2.3":  dict(delta=2.3,        K=260, prec=900,  m=22, tprec=500),
    "d2.6":  dict(delta=2.6,        K=320, prec=1000, m=28, tprec=550),
    "d3.0":  dict(delta=3.0,        K=400, prec=1100, m=42, tprec=650),
    "d3.5":  dict(delta=3.5,        K=540, prec=1300, m=68, tprec=750),
}
KMAX_EXTRA = 300

def prolate_even_leakage(c, kmax, m, prec):
    """ln(1 - chi_n) for the even orders n = 0, 2, ..., 2(m-1) at bandwidth c: the Legendre tridiagonal's
    m lowest eigenpairs (ascending chi = the differential operator's eigenvalues ~ the order), then
    lambda_n = (c/pi) (d_0^{(n)}/psi_n(0))^2 with psi_n(0) = sum_k d_k^{(n)} sqrt(k + 1/2) P_k(0)."""
    with ctx.workprec(prec):
        ks = list(range(0, kmax + 1, 2)); M = len(ks)
        A = arb_mat(M, M); c2 = c*c
        for i, k in enumerate(ks):
            kk = arb(k)
            A[i, i] = kk*(kk + 1) + c2*(2*kk*(kk + 1) - 1)/((2*kk + 3)*(2*kk - 1))
            if i + 1 < M:
                v = c2*(kk + 2)*(kk + 1)/((2*kk + 3)*((2*kk + 1)*(2*kk + 5)).sqrt())
                A[i, i + 1] = v; A[i + 1, i] = v
        E, R = acb_mat(A.mid()).eig(right=True, algorithm="approx")
        order = sorted(range(M), key=lambda i: E[i].real.mid())
        # P_k(0) for even k: (-1)^{k/2} (k-1)!!/k!!
        P0 = {}
        val = arb(1)
        for k in ks:
            P0[k] = val
            val = -val*arb(k + 1)/arb(k + 2)
        out = []
        for j in range(m):
            idx = order[j]
            d = [R[i, idx].real.mid() for i in range(M)]
            psi0 = arb(0)
            for i, k in enumerate(ks):
                psi0 += d[i]*(arb(k) + arb(1)/2).sqrt()*P0[k]
            lam = c/arb.pi()*(d[0]/psi0)**2
            leak = 1 - lam.sqrt()          # the paper's 1 - chi (chi = sqrt(lambda), true_form_cells.chi2_deficit)
            out.append(float(leak.log()) if leak > 0 else None)
        return out

def run(cell):
    cfg = CELLS[cell]
    params = {"deps": DEPS, "cell": cell, **cfg, "kmax_extra": KMAX_EXTRA, "round": 1}
    name = f"spectrum_ladder_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None:
        return st
    d, K, prec, m = cfg["delta"], cfg["K"], cfg["prec"], cfg["m"]
    t0 = time.time()
    G, N, pp = gram(d, K, prec); t1 = time.time()
    with ctx.workprec(prec):
        Dm = arb_mat(K, K)
        for i in range(K): Dm[i, i] = 1/N[i].sqrt()
        Gs = Dm*G*Dm
        E, Rv = acb_mat(Gs.mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: float(E[i].real.mid()))
        approx = [float(E[order[j]].real.mid()) for j in range(m)]
        t2 = time.time()
        # the vectors in the original basis: v = Dm * (eigenvector of Gs)
        vecs = []
        for j in range(m):
            w = arb_mat(K, 1)
            for i in range(K): w[i, 0] = Rv[i, order[j]].real.mid()/N[i].sqrt()
            vecs.append(w)
        ladder = []
        for k in range(1, m + 1):
            Rk = arb_mat(K, k)
            for j in range(k):
                for i in range(K): Rk[i, j] = vecs[j][i, 0]
            A = Rk.transpose()*G*Rk
            Mm = arb_mat(k, k)
            for j in range(k):
                for l in range(k):
                    s = arb(0)
                    for i in range(K): s += N[i]*Rk[i, j]*Rk[i, l]
                    Mm[j, l] = s
            C = Mm.inv()*A
            ev = acb_mat(C).eig(nonstop=True)
            ups = [e.real.upper() for e in ev]
            top = max(ups, key=lambda x: float(x))
            widths = max(float(e.real.rad()) for e in ev)
            ladder.append({"k": k, "ln_upper": float(top.log()) if top > 0 else None, "upper": top.str(20, radius=False),
                           "enclosure_rad": widths, "ln_approx": math.log(approx[k - 1]) if approx[k - 1] > 0 else None})
        t3 = time.time()
    with ctx.workprec(cfg["tprec"]):
        c = 2*arb.pi()*arb(d).exp()
        pro = {}
        for extra in (KMAX_EXTRA, KMAX_EXTRA + 200):
            kmax = int(float(c)) + extra
            pro[str(extra)] = prolate_even_leakage(c, kmax, 2*m + 1, cfg["tprec"])   # even orders 0, 2, ..., 4m
    t4 = time.time()
    st = {"cell": cell, "delta": d, "K": K, "prec": prec, "m": m, "prime_powers": pp,
          "ladder": ladder, "prolate_ln_leakage": pro, "prolate_orders": list(range(0, 4*m + 1, 2)),
          "gram_s": t1 - t0, "eig_s": t2 - t1, "ladder_s": t3 - t2, "prolate_s": t4 - t3,
          "verdict": "CERTIFIED LADDER (each rung the upper end of a certified enclosure of the projected pencil's top eigenvalue); the prolate ladder computed"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or list(CELLS)):
        st = run(cell)
        L = st["ladder"]; P = st["prolate_ln_leakage"][str(KMAX_EXTRA)]
        print(f"{st['cell']:6s} delta {st['delta']:<9} rungs ln up: " + ", ".join(f"{r['ln_upper']:.2f}" if r['ln_upper'] is not None else "None" for r in L[:8])
              + " | prolate ln(1-chi) at orders 4k: " + ", ".join(f"{P[2*k]:.2f}" if P[2*k] is not None else "None" for k in range(1, 9))
              + f" | [gram {st['gram_s']:.0f}s eig {st['eig_s']:.0f}s ladder {st['ladder_s']:.0f}s prolate {st['prolate_s']:.0f}s]", flush=True)
