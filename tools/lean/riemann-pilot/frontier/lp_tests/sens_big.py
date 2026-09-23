"""Sensitivity of the Jensen test: multiply the delta = 1.4 ground-state transform by
(1 - z^2/w0^2)(1 - z^2/conj(w0)^2), which adds one non-real zero pair at +-w0, +-conj(w0) and keeps every other
zero. Report whether some J^{d,n} (d <= 14) detects it, as the pair moves out."""
import sys, json
exec(open("jensen_big.py").read().split("mode = sys.argv[1]")[0])
from weil_prime_gram import gram, minimiser
mp.mp.dps = 250
d_, K, p = 1.4, 90, 500
a = d_ / 2
G, N, pp = gram(d_, K, p); c, ev = minimiser(G, N, p)
cm = [mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1]))) for x in c]
if cm[0] < 0: cm = [-x for x in cm]
g = lambda u: sum(cm[k] * mp.cos(k * mp.pi * u / a) for k in range(K))
mu = moments_on(g, a)
cz = [(-1)**j * mu[j] / mp.factorial(2 * j) for j in range(J)]          # F(z) = sum cz_j z^{2j}
out = []
for T in [16, 30]:
    for eta in [2.0]:
        w0 = mp.mpc(T, eta); s1 = 1 / w0**2; s2 = 1 / mp.conj(w0)**2
        b = [1, -(s1 + s2), s1 * s2]                                     # (1 - s1 x)(1 - s2 x), x = z^2 (real coeffs)
        cn = [sum(mp.re(b[i]) * cz[j - i] for i in range(3) if 0 <= j - i) for j in range(J)]
        gam = [mp.factorial(j) * (-1)**j * cn[j] for j in range(J)]
        fails=[]
        for dd in range(2, DMAX + 1):
            co=[mp.binomial(dd,i)*gam[i] for i in range(dd+1)]
            r=mp.polyroots(co[::-1],maxsteps=800,extraprec=1500)
            im=max(abs(mp.im(x))/abs(x) for x in r)
            if im>mp.mpf(10)**-30: fails.append((dd,float(im)))
        rep={"n_fail":len(fails),"first_fails":fails[:3]}
        out.append(dict(T=T, eta=eta, detected=rep["n_fail"] > 0, n_fail=rep["n_fail"], first=rep["first_fails"][:2]))
        print(json.dumps(out[-1]), flush=True)
