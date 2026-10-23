"""Round 29: the law behind eps_j = x_j - gamma_j > 0.

Under RH, Q(g) = 2 sum_{gamma>0} ghat(gamma)^2 for even g. The ground state (||g|| = 1) then
satisfies lam ghat(w) = 2 sum_gamma ghat(gamma) k_a(w, gamma). At a pinned zero,
eps_j = -c_j/ghat'(gamma_j) with c_j = ghat(gamma_j). So eps_j > 0 for all pinned j (whose
ghat' alternate) is the same as the c_j alternating in sign along the zeta zeros.
Computed: c_k and ghat'(gamma_k) for the first 6700 zeros, at the working precision (gamma_1..40 at
60 digits); the balance 2 sum c_k^2 against lam; the sign pattern of c_k; and, per pinned zero,
-c_j/ghat'(gamma_j) against eps_j and its share 2c_j^2/lam.
Usage: law.py <tools/research> delta:K:prec [...]"""
import sys, json, math
sys.path.insert(0, sys.argv[1])
from weil_prime_gram import gram, minimiser, rayleigh
from flint import arb, ctx
import mpmath, numpy as np
mpmath.mp.dps = 60
Z = json.load(open('gapnum/zeros6700.json'))
HP = [mpmath.zetazero(n).imag for n in range(1, 41)]
for spec in sys.argv[2:]:
    d, K, p = spec.split(':'); d, K, p = float(d), int(K), int(p)
    G, N, pp = gram(d, K, p)
    c, ev = minimiser(G, N, p)
    with ctx.workprec(p):
        c = [arb(x) for x in c]
        if c[0] < 0: c = [-x for x in c]
        nrm = sum(N[i] * c[i] * c[i] for i in range(K)).sqrt()
        c = [x / nrm for x in c]
        lam = rayleigh(G, N, c, p)
        a = arb(d) / 2
        om2 = [(arb(k) * arb.pi() / a) ** 2 for k in range(K)]
        sg = [c[k] if k % 2 == 0 else -c[k] for k in range(K)]
        def gh(r):
            S = arb(0); D = arb(0)
            for k in range(K):
                dd = r * r - om2[k]; S += sg[k] * r / dd; D += sg[k] * (-(r * r + om2[k])) / (dd * dd)
            s, co = (r * a).sin(), (r * a).cos()
            return 2 * s * S, 2 * (a * co * S + s * D)
        vals, ders = [], []
        for k, gm in enumerate(Z):
            r = arb(mpmath.nstr(HP[k], 55)) if k < len(HP) else arb(gm)
            v, dv = gh(r); vals.append(v); ders.append(dv)
        S = 2 * sum(v * v for v in vals)
        lamf = float(lam.mid())
        sgn = [1 if float(v.mid()) > 0 else -1 for v in vals]
        alt = [sgn[k] != sgn[k + 1] for k in range(len(sgn) - 1)]
        first_nonalt = next((k + 1 for k, x in enumerate(alt) if not x), None)
        pinned = []
        for j in range(40):
            e = -vals[j] / ders[j]
            if abs(float(e.mid())) < 1e-2:
                pinned.append(dict(j=j + 1, c=float(vals[j].mid()), gprime=float(ders[j].mid()),
                                   eps_first_order=float(e.mid()), share=float((2 * vals[j] ** 2 / lam).mid())))
        # shares of the balance by zero-height band
        bands = {}
        for lo, hi in [(0, 50), (50, 100), (100, 500), (500, 7000)]:
            bands['%d-%d' % (lo, hi)] = float((2 * sum(v * v for v, gm in zip(vals, Z) if lo <= gm < hi) / lam).mid())
    print(json.dumps(dict(delta=d, K=K, lam=lamf, sum_over_6700_div_lam=float((S / lam).mid()),
        share_by_band=bands, alternating_fraction=sum(alt) / len(alt), first_non_alternation_between=first_nonalt,
        n_pinned=len(pinned), pinned=pinned)))
    sys.stdout.flush()
