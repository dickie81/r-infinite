"""Can the ground state be a convolution g = s * h with s a ball slice (1 - u^2/r^2)^(nu - 1/2) on [-r, r]
(Paper 0's layer profiles: d = 2 nu - 1; nu = 1/2 box, 1 semicircle, 3/2 parabola, ...)?
Then ghat = shat * hhat, so every zero j_{nu,k}/r of shat is a zero of ghat. We compute the real zeros of ghat
on [0, Tmax] to high precision and test every radius r that puts the first slice zero on a ghat zero."""
import sys, json, math
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram, minimiser
import mpmath as mp
d, K, p, Tmax, dps = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
a = d / 2
G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
mp.mp.dps = dps
cm = [mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1]))) for x in c]
om = [k * mp.pi / a for k in range(K)]
def gh(z):
    s = cm[0] * 2 * mp.sin(z * a) / z
    for k in range(1, K):
        s += cm[k] * (-1)**k * 2 * z * mp.sin(z * a) / (z**2 - om[k]**2)
    return s
# real zeros by sign changes on a fine grid (step 0.02), refined by bisection-secant
step = mp.mpf('0.02'); t = mp.mpf('0.01'); prev = gh(t); zeros = []
while t < Tmax:
    t2 = t + step; cur = gh(t2)
    if cur == 0 or (prev > 0) != (cur > 0):
        zeros.append(mp.findroot(gh, (t, t2), solver='anderson'))
    t, prev = t2, cur
tol = mp.mpf('1e-8')
def is_zero(x):
    return min(abs(x - z) for z in zeros) < tol * x
res = {}
for nu2 in range(0, 21):                 # nu = nu2/2 in {0, 1/2, ..., 10}; nu > -1 gives real Bessel zeros
    nu = mp.mpf(nu2) / 2
    jz = [mp.besseljzero(nu, k) for k in range(1, 60)]
    survivors = []
    for x1 in zeros:
        r = jz[0] / x1
        ok = True; tested = 0
        for jk in jz[1:]:
            if jk / r > Tmax: break
            tested += 1
            if not is_zero(jk / r): ok = False; break
        if ok: survivors.append((float(r), tested))
    constrained = [s for s in survivors if s[1] > 0]
    res[str(float(nu))] = dict(max_radius_any=max((s[0] for s in survivors), default=0.0),
                               surviving_with_a_tested_second_zero=len(constrained),
                               radius_bound=float(jz[1] / Tmax))
print(json.dumps(dict(delta=d, Tmax=Tmax, n_real_zeros=len(zeros), first_zeros=[float(z) for z in zeros[:6]],
                      zeta=[14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178], per_nu=res)))
