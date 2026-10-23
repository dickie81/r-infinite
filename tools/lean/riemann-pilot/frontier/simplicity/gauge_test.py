import sys, math
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram
import numpy as np
def tofl(x): return float(x.mid())
for d in [0.2, 0.5, 1.0, 1.5, 2.0]:
    K = 30
    G, N, pp = gram(d, K, 200)
    Gm = np.array([[tofl(G[i, j]) for j in range(K)] for i in range(K)])
    Nv = np.array([tofl(x) for x in N])
    S = Gm / np.sqrt(np.outer(Nv, Nv))
    # best sign gauge: s_0 = 1, s_k = -sign(S_0k); count violations s_j s_k S_jk > 0
    s = np.array([1.0] + [-np.sign(S[0, k]) for k in range(1, K)])
    T = S * np.outer(s, s)
    off = T - np.diag(np.diag(T))
    viol = np.sum(off > 1e-14) // 2
    # also: worst positive entry relative
    ev = np.linalg.eigvalsh(S)
    print(f"delta {d}: cosine basis, gauge from row 0: {viol} positive off-diagonal pairs of {K*(K-1)//2}; max pos {off.max():.3g}; lam1 {ev[0]:.3g} lam2 {ev[1]:.3g}")
