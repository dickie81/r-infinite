"""Sign of eps_j = x_j - gamma_j at the ground state's zeros near zeta zeros.

The flow (round 27) at a pinned zero means x_j decreases onto gamma_j, i.e. eps_j > 0. Zeros of
ghat_delta are refined by Newton at the working precision (flow4.refine). gamma_j comes from
mpmath.zetazero at 60 digits. A zero counts as pinned when |eps_j| < 1e-2. Each cell is repeated
at several K, because basis truncation can move a zero by more than eps_j.
Usage: pinned.py <tools/research> delta:K:prec [...]"""
import sys, json
sys.path.insert(0, sys.argv[1]); sys.path.insert(0, 'debr')
import flow, flow4
import mpmath
from flint import ctx
mpmath.mp.dps = 60
GAM = [mpmath.zetazero(n).imag for n in range(1, 20)]
for spec in sys.argv[2:]:
    d, K, p = spec.split(':'); d, K, p = float(d), int(K), int(p)
    g, lam = flow.state(d, K, p)
    out = []
    with ctx.workprec(p):
        for x in flow.zeros(g, 60.0):
            r = flow4.refine(g, x, p)
            rs = r.str(radius=False, more=True) if hasattr(r, 'str') else str(r)
            xm = mpmath.mpf(r.mid().str(50, radius=False))
            j = min(range(len(GAM)), key=lambda i: abs(GAM[i] - xm))
            e = xm - GAM[j]
            if abs(e) < 1e-2: out.append([j + 1, mpmath.nstr(e, 6)])
    print(json.dumps(dict(delta=d, K=K, prec=p, lam1=lam, pinned=out))); sys.stdout.flush()
