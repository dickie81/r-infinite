#!/usr/bin/env python3
"""Connes-Consani-Moscovici's trial vector k_lambda = E(h_lambda) restricted to
[lambda^{-1}, lambda] (Zeta spectral triples, arXiv 2511.22755, (7.6); their
"educated guess" for the ground state of the Weil form), in the additive
variable t = log u on [-a, a], a = log lambda = delta/2, expanded in the even
cosine basis of weil_prime_gram.py. The expansion is a TRIAL VECTOR: its
accuracy only affects how close the certified Rayleigh quotient sits to
Q(k_lambda); the certificate (weil_prime_gram.py) is rigorous for whatever
coefficients are handed to it.

THE CONSTRUCTION (CCM sec. 7, Lemma 7.1 and (7.5)-(7.6)). h_{n,lambda}(x) =
PS_{n,0}(2 pi lambda^2, x/lambda) on [-lambda, lambda], zero outside -- the
prolate spheroidal wave functions with bandwidth parameter c = 2 pi lambda^2
= 2 pi e^delta = T_0, the slack law's horizon; h_lambda the combination of
h_{0,lambda}, h_{4,lambda} with vanishing integral; E(f)(u) = u^{1/2}
sum_{n>=1} f(nu). So in t: k(t) = e^{t/2} sum_{1 <= n <= lambda e^{-t}}
h_lambda(n e^t / lambda). The even part (k(t) + k(-t))/2 is used (the
ground state is even; k is even up to the Poisson defect of the prolates).

PROLATES. Legendre expansion psi_n(x) = sum_k d_k P̄_k(x) (normalised
Legendre), d the eigenvectors of the symmetric tridiagonal (even k)
  A_kk = k(k+1) + c^2 (2k(k+1) - 1)/((2k+3)(2k-1)),
  A_{k,k+2} = c^2 (k+2)(k+1)/((2k+3) sqrt((2k+1)(2k+5))),
eigenvalues chi ascending (n = 0, 2, 4, ...). Checked in-script: psi_0 and
psi_4 are eigenfunctions of the finite Fourier transform on [-1, 1] with
c (proportionality at two points to 1e-20).

Output: checkpoints/ccm_trial_<delta>.json with the cosine coefficients
(strings) for K modes, computed with arb at `prec` bits from `nodes`
Gauss-Legendre nodes.
Usage: ccm_trial_vector.py <delta> <K> <prec> <nodes> [kmax]
"""
import sys, os, json, math, time
from flint import arb, acb, arb_mat, acb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))

def prolate_coeffs(c, kmax, prec):
    """Legendre coefficients (even k up to kmax) of psi_0 and psi_4 for bandwidth c."""
    with ctx.workprec(prec):
        ks = list(range(0, kmax + 1, 2)); m = len(ks)
        A = arb_mat(m, m)
        c2 = c*c
        for i, k in enumerate(ks):
            kk = arb(k)
            A[i, i] = kk*(kk + 1) + c2*(2*kk*(kk + 1) - 1)/((2*kk + 3)*(2*kk - 1))
            if i + 1 < m:
                v = c2*(kk + 2)*(kk + 1)/((2*kk + 3)*((2*kk + 1)*(2*kk + 5)).sqrt())
                A[i, i + 1] = v; A[i + 1, i] = v
        E, R = acb_mat(A.mid()).eig(right=True, algorithm="approx")
        order = sorted(range(m), key=lambda i: E[i].real.mid())
        i0, i4 = order[0], order[2]          # even-index block: n = 0, 2, 4 -> positions 0, 1, 2
        d0 = [R[i, i0].real.mid() for i in range(m)]
        d4 = [R[i, i4].real.mid() for i in range(m)]
        return ks, d0, d4, E[i0].real.mid(), E[i4].real.mid()

def legendre_eval(ks, d, x, prec):
    """sum_k d_k P̄_k(x) over even k (P̄_k = sqrt(k + 1/2) P_k) by the three-term recurrence."""
    with ctx.workprec(prec):
        kmax = ks[-1]
        p0 = arb(1); p1 = x; s = arb(0)
        # P_0 = 1, P_1 = x, (k+1) P_{k+1} = (2k+1) x P_k - k P_{k-1}
        vals = {0: p0, 1: p1}
        for k in range(1, kmax):
            p2 = ((2*k + 1)*x*p1 - k*p0)/(k + 1)
            vals[k + 1] = p2; p0, p1 = p1, p2
        for i, k in enumerate(ks):
            s += d[i]*(arb(k) + arb(1)/2).sqrt()*vals[k]
        return s

def build(delta, K, prec, nodes, kmax=None):
    with ctx.workprec(prec):
        a = arb(delta)/2; lam = a.exp(); c = 2*arb.pi()*lam*lam
        if kmax is None: kmax = int(float(c)) + 120
        ks, d0, d4, chi0, chi4 = prolate_coeffs(c, kmax, prec)
        # vanishing integral: int_{-1}^1 psi = sqrt(2) d_0 (P̄_0 = 1/sqrt 2)
        ratio = d0[0]/d4[0]
        h = lambda x: legendre_eval(ks, d0, x, prec) - ratio*legendre_eval(ks, d4, x, prec)
        # finite-Fourier check: F psi(x) = int_{-1}^1 e^{i c x y} psi(y) dy proportional to psi(x)
        def ffcheck(d):
            xg = [arb.legendre_p_root(200, i, weight=True) for i in range(200)]
            out = []
            for x in (arb('0.3'), arb('0.7')):
                fx = sum(w*(c*x*y).cos()*legendre_eval(ks, d, y, prec) for y, w in xg)
                out.append(fx/legendre_eval(ks, d, x, prec))
            return out
        mu0 = ffcheck(d0); mu4 = ffcheck(d4)
        # k(t) at Gauss-Legendre nodes on [-a, a]
        roots = [arb.legendre_p_root(nodes, i, weight=True) for i in range(nodes)]
        ts = [a*x for x, _ in roots]; ws = [a*w for _, w in roots]
        def kfun(t):
            s = arb(0); et = t.exp(); n = 1
            while arb(n)*et <= lam:
                s += h(arb(n)*et/lam); n += 1
            return (t/2).exp()*s
        kv = [kfun(t) for t in ts]
        # even part: nodes are symmetric (root i <-> nodes-1-i)
        kev = [(kv[i] + kv[nodes - 1 - i])/2 for i in range(nodes)]
        kodd = max(float(abs(kv[i] - kv[nodes - 1 - i])) for i in range(nodes))
        # cosine coefficients c_k = int k cos(omega_k t) dt / N_k
        coeffs = []
        pi = arb.pi()
        for k in range(K):
            om = arb(k)*pi/a
            s = arb(0)
            for i in range(nodes):
                s += ws[i]*kev[i]*(om*ts[i]).cos()
            coeffs.append(s/(a if k else 2*a))
        norm2 = sum((a if k else 2*a)*coeffs[k]*coeffs[k] for k in range(K))
        return {"delta": delta, "K": K, "prec": prec, "nodes": nodes, "kmax": kmax,
                "c": float(c), "chi0": str(chi0.str(20, radius=False)), "chi4": str(chi4.str(20, radius=False)),
                "fourier_check_psi0": [x.str(15, radius=False) for x in mu0],
                "fourier_check_psi4": [x.str(15, radius=False) for x in mu4],
                "odd_part_max": kodd, "k_at_a": kv[-1].str(15, radius=False), "k_at_minus_a": kv[0].str(15, radius=False),
                "norm2": norm2.str(20, radius=False),
                "coeffs": [x.str(int(prec*0.31) + 10, radius=False) for x in coeffs],   # full working precision: a 60-digit
                                                                                        # serialisation floored Q at 1e-120 (A455)
                "coeff_tail": [float(abs(x)) for x in coeffs[-5:]]}

if __name__ == "__main__":
    d = float(sys.argv[1]); K = int(sys.argv[2]); prec = int(sys.argv[3]); nodes = int(sys.argv[4])
    kmax = int(sys.argv[5]) if len(sys.argv) > 5 else None
    t0 = time.time()
    st = build(d, K, prec, nodes, kmax)
    st["seconds"] = time.time() - t0
    out = os.path.join(HERE, "checkpoints", f"ccm_trial_{d}.json")
    json.dump(st, open(out, "w"))
    print(f"delta {d} K {K}: c {st['c']:.3f} chi0 {st['chi0'][:12]} chi4 {st['chi4'][:12]} FF psi0 {st['fourier_check_psi0']} psi4 {st['fourier_check_psi4']} odd {st['odd_part_max']:.2e} k(a) {st['k_at_a'][:10]} k(-a) {st['k_at_minus_a'][:10]} tail {st['coeff_tail'][-1]:.2e} {st['seconds']:.0f}s -> {out}", flush=True)
