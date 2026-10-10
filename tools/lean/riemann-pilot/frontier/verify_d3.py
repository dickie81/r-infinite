"""delta = 3.0: are all zeros of the ground state's transform in |r| < 60 real?
ghat(r) = 2 sin(ra) r F(r^2), F(s) = sum_k sg_k/(s - w_k^2)  (sg_k = (-1)^k c_k).
Zeros of ghat off the sinc lattice = zeros of P(s) = F(s) prod_j (s - w_j^2).
#roots of P in |s| < S = wind(F on |s| = S) + #{j : w_j^2 < S}. Real positive roots <-> real zeros of ghat."""
import sys, json, math, numpy as np
sys.path.insert(0, '../wt-review/tools/research')
from weil_prime_gram import gram, minimiser
from flint import arb, acb, ctx
mode = sys.argv[1]            # "full" (arb coefficients) or "float" (coefficients rounded to double)
delta, K, prec, R = 3.0, 400, 1100, 60.0
a = delta/2; S = R*R
G, N, pp = gram(delta, K, prec)
c, ev = minimiser(G, N, prec)
with ctx.workprec(prec):
    A = arb(a); w2 = [(arb(k)*arb.pi()/A)**2 for k in range(K)]
    cc = c if mode == "full" else [arb(float(x)) for x in c]
    sg = [cc[k] if k % 2 == 0 else -cc[k] for k in range(K)]
    def F(s):
        t = acb(0)
        for k in range(K): t += sg[k]/(s - w2[k])
        return t
    th = np.linspace(0, 2*math.pi, 20001)
    vals = np.array([complex(F(acb(S*math.cos(t), S*math.sin(t))).mid()) for t in th])
    wind = int(round(np.sum(np.diff(np.unwrap(np.angle(vals))))/(2*math.pi)))
    npoles = sum(1 for k in range(K) if float(w2[k]) < S)
    # real roots of P on (-S, S): sign changes of P(s) = F(s) prod (s - w_j^2), avoiding the poles
    xs = np.linspace(-S + 0.37, S - 0.37, 40001)
    def P(x):
        s = acb(x); f = F(s); pr = acb(1)
        for k in range(K):
            if float(w2[k]) < 2*S: pr *= (s - w2[k])
        return float((f*pr).real.mid())
    pv = [P(x) for x in xs]
    neg = sum(1 for i in range(len(xs)-1) if xs[i] < 0 and pv[i]*pv[i+1] < 0)
    pos = sum(1 for i in range(len(xs)-1) if xs[i] >= 0 and pv[i]*pv[i+1] < 0)
print(json.dumps({"mode": mode, "roots_P_in_disk": wind + npoles, "wind_F": wind, "poles_inside": npoles,
                  "real_pos_roots": pos, "real_neg_roots(=imaginary r zeros)": neg,
                  "nonreal_s_roots": wind + npoles - pos - neg}))
