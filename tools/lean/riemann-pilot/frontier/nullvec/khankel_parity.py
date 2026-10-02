#!/usr/bin/env python3
"""Round 138: the reflection identity for the parity gap.
For a half-profile h on [0,a] put g_e = h(|t|), g_o = sgn(t) h(|t|) (same norm 2||h||^2). Then exactly
  Q(g_e) - Q(g_o) = 4 W1(h),  W1(h) = Lh(1/2)^2 + Lh(-1/2)^2 + (1/2pi) int Re[Lh(ir)^2] sigma_a(r) dr,
Lh(s) = int_0^a h(x) e^{s x} dx  (the Weil functional on the half-line SELF-convolution h*h, not an autocorrelation).
Consequences: lam_o <= lam_e - 4 W1(h_e)/N  (gap => W1(h_e) < 0, necessary);
              lam_e <= lam_o + 4 W1(h_o)/N  (W1(h_o) < 0 => gap, sufficient).
This script measures W1(h_e), W1(h_o) from the Gram instruments (Q(sgn * ground state) by basis change)."""
import sys, json
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
import weil_prime_gram as W
import weil_prime_gram_odd as WO

def tomp(x, dps): return mp.mpf(x.mid().str(dps + 10, radius=False))

def run(delta, K, Kbig, prec, dps):
    mp.mp.dps = dps
    a = mp.mpf(delta)/2
    Ge, Ne, _ = W.gram(delta, Kbig, prec)
    Go, No, _ = WO.gram_odd(delta, Kbig, prec)
    ge = mp.matrix(Kbig, Kbig); go = mp.matrix(Kbig - 1, Kbig - 1)
    for i in range(Kbig):
        for j in range(Kbig): ge[i, j] = tomp(Ge[i, j], dps)
    for i in range(Kbig - 1):
        for j in range(Kbig - 1): go[i, j] = tomp(Go[i, j], dps)
    ne = [tomp(x, dps) for x in Ne]; no = [tomp(x, dps) for x in No]
    def ground(g, n, k):
        D = [1/mp.sqrt(n[i]) for i in range(k)]
        S = mp.matrix(k, k)
        for i in range(k):
            for j in range(k): S[i, j] = D[i]*g[i, j]*D[j]
        E, V = mp.eigsy(S)
        i0 = min(range(k), key=lambda i: E[i])
        return E[i0], [V[m, i0]*D[m] for m in range(k)]          # coefficients, unit L^2[-a,a] norm
    qf = lambda g, c: mp.fsum(c[i]*g[i, j]*c[j] for i in range(len(c)) for j in range(len(c)))
    le, ce = ground(ge, ne, K)
    lo, co = ground(go, no, K - 1)                                # co[k-1] <-> sin(om_k t)
    # int_0^a sin(k pi t/a) cos(j pi t/a) dt = (a/pi) k (1 - (-1)^{k+j})/(k^2 - j^2), 0 if j = k
    I = lambda k, j: mp.mpf(0) if k == j else a/mp.pi*k*(1 - (-1)**(k + j))/(k*k - j*j)
    # sgn * odd  -> cosine basis: coeff_j = 2 sum_k co_k I(k,j) / N_j
    be = [2*mp.fsum(co[k - 1]*I(k, j) for k in range(1, K))/ne[j] for j in range(Kbig)]
    # sgn * even -> sine basis:   coeff_j = 2 sum_k ce_k I(j,k) / N_j   (j >= 1)
    bo = [2*mp.fsum(ce[k]*I(j, k) for k in range(K))/no[j - 1] for j in range(1, Kbig)]
    nbe = mp.fsum(be[j]**2*ne[j] for j in range(Kbig)); nbo = mp.fsum(bo[j - 1]**2*no[j - 1] for j in range(1, Kbig))
    Qe_from_o = qf(ge, be); Qo_from_e = qf(go, bo)
    W1_ho = (Qe_from_o - lo)/4            # exact norms are 1; truncation shows in nb*
    W1_he = (le - Qo_from_e)/4
    return {"delta": float(delta), "K": K, "Kbig": Kbig, "lam_e": mp.nstr(le, 6), "lam_o": mp.nstr(lo, 6),
            "Q(sgn*odd GS)": mp.nstr(Qe_from_o, 8), "Q(sgn*even GS)": mp.nstr(Qo_from_e, 8),
            "norm_trunc_e": mp.nstr(nbe, 10), "norm_trunc_o": mp.nstr(nbo, 10),
            "W1(h_e)": mp.nstr(W1_he, 8), "W1(h_o)": mp.nstr(W1_ho, 8)}

if __name__ == "__main__":
    print(json.dumps(run(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))), flush=True)
