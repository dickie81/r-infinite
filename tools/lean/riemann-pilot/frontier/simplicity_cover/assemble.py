"""Worker k of K: partial C = sum_i h_i F(t_i) F(t_i)^T over its share of the nodes, in arb.
F_n(t) = (-1)^(n/2) sqrt(2L(2n+1)) j_n(Lt), n = 0, 2, ..., 2N-2 (L = 1).
j_n at the two top orders by the power series with a rigorous alternating-tail bound; then the exact
three-term recurrence downwards in ball arithmetic (stable direction; arb tracks all rounding).
h_i = w_i (Psi(t_i) - beta)/pi with Psi = Re psi(1/4 + it/2) - log pi - sum c_n cos(t log n)."""
import sys, pickle, time
from flint import arb, acb, arb_mat, ctx, fmpz
from params import *
ctx.prec = PREC + 200
LG = consts()[0]
k, K = int(sys.argv[1]), int(sys.argv[2])
par = int(sys.argv[3]) if len(sys.argv) > 3 else 0     # 0: even orders 0..2N-2; 1: odd orders 1..2N-1
nodes = pickle.load(open("nodes.pkl", "rb"))["nodes"]
mine = nodes[k::K]
def _mk(me):
    m, e = me
    return arb(fmpz(m)) * arb(2) ** int(e)
def jseries(n, x, prec):
    ctx.prec = prec
    x2 = -(x * x) / 2
    T = arb(1); S = arb(1); kk = 0
    while True:
        kk += 1
        T = T * x2 / (kk * (2 * n + 2 * kk + 1))
        S += T
        ratio_next = (x * x / 2) / ((kk + 1) * (2 * n + 2 * kk + 3))
        if ratio_next < 1 and abs(T) * ratio_next < arb(2) ** (-prec - 20) * abs(S):
            # terms beyond kk: alternating, strictly decreasing in modulus (ratio decreasing in k)
            S += arb(0, 1) * (abs(T) * ratio_next).upper()
            break
    dfac = arb.fac_ui(2 * n + 1) / (arb(2) ** n * arb.fac_ui(n))
    return x ** n / dfac * S
def column(t):
    # x = L t is formed at the working precision: exact only for L = 1, and the recurrence amplifies its radius
    prec = int(1.5 * float(LG.mid()) * float(t.mid())) + 500
    ctx.prec = prec
    x = LG * t
    top = 2 * N - 1
    jn1 = jseries(top, x, prec); jn = jseries(top - 1, x, prec)
    ctx.prec = prec
    out = [None] * N
    # jn = j_{top-1}, jn1 = j_top ; recurrence j_{m-1} = (2m+1)/x j_m - j_{m+1}
    m = top - 1
    ix = 1 / x
    if par == 1: out[top // 2] = jn1
    while True:
        if m % 2 == par:
            out[m // 2] = jn
        if m == 0: break
        jm1 = (2 * m + 1) * ix * jn - jn1
        jn1, jn = jn, jm1; m -= 1
    ctx.prec = 256
    res = []
    for i in range(N):
        n = 2 * i + par
        v = (2 * LG * (2 * n + 1)).sqrt() * out[i]
        res.append(+v if i % 2 == 0 else -v)
    return res, prec
ctx.prec = 400
L, cn, AL, T, beta = consts()
lncn = [(arb(n).log(), c) for n, c in cn]
t0 = time.time()
ctx.prec = 256
C = None
BS = 512
for b0 in range(0, len(mine), BS):
    rows = []; hs = []
    for (tm, tr, wm, wr) in mine[b0:b0 + BS]:
        ctx.prec = PREC + 100
        t = _mk(tm) + arb(0, 1) * _mk(tr); w = _mk(wm) + arb(0, 1) * _mk(wr)
        ctx.prec = 400
        psi = (acb(arb(1) / 4, t / 2).digamma()).real - arb.pi().log() - sum(c * (t * l).cos() for l, c in lncn)
        h = w * (psi - beta) / arb.pi()
        col, pr = column(t)
        ctx.prec = 256
        rows.append(col); hs.append(+h)
        rad_max = max(float(v.rad()) for v in col)
        if rad_max > 1e-60 or float(h.rad()) > 1e-60:
            print("WARN radius", float(t.mid()), rad_max, float(h.rad()), flush=True)
    ctx.prec = 256
    V = arb_mat(len(rows), N, [v for r in rows for v in r])
    HV = arb_mat(len(rows), N, [hs[i] * v for i, r in enumerate(rows) for v in r])
    P = V.transpose() * HV
    C = P if C is None else C + P
    print(f"worker {k}: {b0 + len(rows)}/{len(mine)} nodes, {time.time() - t0:.0f}s", flush=True)
ser = []
for i in range(N):
    for j in range(i, N):
        e = C[i, j]
        ser.append((e.mid().man_exp(), e.rad().man_exp()))
ser = [((int(a[0]), int(a[1])), (int(b[0]), int(b[1]))) for a, b in ser]
pickle.dump(ser, open(f"part_{k}.pkl" if par == 0 else f"part_odd_{k}.pkl", "wb"))
print("done", k, time.time() - t0)
