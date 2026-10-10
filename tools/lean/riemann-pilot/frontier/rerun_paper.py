"""Rerun the hRR/hD/hkappa test on the paper's own ground state (the cosine-basis Gram of
tools/research/weil_prime_gram.py), and arbitrate against the step-function state of hrr2.py."""
import sys, json, math, time, numpy as np
sys.path.insert(0, sys.argv[1])            # tools/research
from weil_prime_gram import gram, minimiser, rayleigh
from flint import arb, acb, ctx
GAM = np.array(json.load(open(sys.argv[2])))
S2 = 0.023105003295796882
def analyse(delta, K, prec, R=60.0):
    t0 = time.time()
    G, N, pp = gram(delta, K, prec)
    c, ev = minimiser(G, N, prec)
    a = delta/2
    cm = [float(x) for x in c]
    if cm[0] < 0: cm = [-x for x in cm]
    # ghat(r) = sum_k c_k int cos(w_k t) e^{irt} = 2 sin(ra) sum_k (-1)^k c_k r/(r^2 - w_k^2)
    with ctx.workprec(prec):
        om = [arb(k)*arb.pi()/arb(a) for k in range(K)]
        sg = [arb(cm[k]) if k % 2 == 0 else -arb(cm[k]) for k in range(K)]
        def gh(r):
            r = acb(r); s = acb(0)
            for k in range(K): s += sg[k]*r/(r*r - om[k]*om[k])
            return 2*(r*arb(a)).sin()*s
        # real zeros (sign changes), avoiding the grid landing on w_k
        xs = np.arange(0.0314159, R, 0.02)
        vals = [float(gh(x).real) for x in xs]
        rz = []
        for i in range(len(xs)-1):
            if vals[i]*vals[i+1] < 0:
                lo, hi, flo = xs[i], xs[i+1], vals[i]
                for _ in range(45):
                    mid = (lo+hi)/2; fm = float(gh(mid).real)
                    if (fm < 0) == (flo < 0): lo, flo = mid, fm
                    else: hi = mid
                rz.append((lo+hi)/2)
        rz = np.array(rz)
        # argument principle on |r| = R (R chosen off the real zeros)
        th = np.linspace(0, 2*np.pi, 6001)
        vals_c = np.array([complex(gh(acb(R*math.cos(t), R*math.sin(t))).mid()) for t in th])
    wind = int(round(np.sum(np.diff(np.unwrap(np.angle(vals_c))))/(2*np.pi)))
    # sinc zeros j*pi/a with j >= K are real and lie beyond R here if K*pi/a > R
    gam = GAM[GAM < R - 5]
    near = np.array([rz[np.argmin(np.abs(rz - g))] for g in gam]) if len(rz) else np.array([])
    extra = [float(z) for z in rz if np.min(np.abs(GAM - z)) > 0.05]
    kap = (cm[0]*2*a**3/3 + sum(cm[k]*4*a*(-1)**k/(k*math.pi/a)**2 for k in range(1, K)))/(2*2*a*cm[0])
    return dict(delta=delta, K=K, lam1=float(ev.mid()) if hasattr(ev, 'mid') else float(ev),
                all_real=(wind == 2*len(rz)), wind=wind, n_real=2*len(rz), first_zeros=rz[:8].round(5).tolist(),
                max_err=float(np.abs(near-gam).max()) if len(near) else None,
                extra_below_R=extra[:10], n_extra=len(extra), kappa=kap, S2=S2, secs=time.time()-t0), (G, N, cm, a, K, prec)
if __name__ == "__main__":
    for spec in sys.argv[3:]:
        d, K, prec = spec.split(':')
        r, _ = analyse(float(d), int(K), int(prec))
        print(json.dumps(r)); sys.stdout.flush()
