"""De Branges / Hermite-Biehler test on the ground states of Weil's form.

THE FUNCTION TESTED. For even g decreasing on [0, a], E = 2 int_0^a g e^{-izt} has its zeros in
the UPPER half-plane (Kakeya), so E itself is never HB. Polya's mechanism is one derivative down:
  Et(z) = g(0) - (iz/2) E(z) = beta e^{-iza} + int_0^a h(t) e^{-izt} dt,  h = -g', beta = g(a),
  At = g(0) - z B/2,   Bt = z A/2 = z ghat/2.
Et is HB when h is nondecreasing (g concave; Kakeya), and then ghat is real-rooted. The test asks
whether Et stays HB past the concavity threshold. (The E below is the auxiliary one.)

E(z) = 2 int_0^a g(t) e^{-izt} dt = A(z) - i B(z),
  A(z) = 2 int_0^a g cos(zt) = ghat(z),   B(z) = 2 int_0^a g sin(zt).
E is Hermite-Biehler (|E(z)| > |E(conj z)| for Im z > 0; equivalently, for this
exponential-type E with mean type of E#/E = -a < 0, E has no zeros in Im z > 0) iff
the zeros of A and B are real and interlace. Then A = ghat is real-rooted. This is
the mechanism behind Polya's theorem, so it holds whenever g is concave.

In the cosine basis g = sum c_k cos(w_k t), w_k = k pi/a:
  A(r) = 2 sin(ra) S1(r),           S1 = sum (-1)^k c_k r/(r^2 - w_k^2)
  B(r) = 2 (S0(r) - cos(ra) S1(r)), S0 = sum c_k r/(r^2 - w_k^2)
(T1) zeros of E in the upper half-disc |z| < R, by the argument principle;
(T2) W(x) = A B' - A' B on the real grid (0, R]: HB requires W > 0.
Coefficients are kept at full precision (round 23's lesson).
Usage: debranges.py <tools/research> delta:K:prec [...]"""
import sys, math, json, time
sys.path.insert(0, sys.argv[1])
from weil_prime_gram import gram, minimiser
from flint import arb, acb, ctx
import numpy as np

def run(delta, K, prec, R=60.0):
    t0 = time.time()
    G, N, pp = gram(delta, K, prec)
    c, ev = minimiser(G, N, prec)
    with ctx.workprec(prec):
        a = arb(delta) / 2
        c = [arb(x) for x in c]
        if c[0] < 0: c = [-x for x in c]
        om2 = [(arb(k) * arb.pi() / a) ** 2 for k in range(K)]
        sg = [c[k] if k % 2 == 0 else -c[k] for k in range(K)]
        def AB(z, deriv=False):
            z = acb(z)
            S0 = acb(0); S1 = acb(0); D0 = acb(0); D1 = acb(0)
            for k in range(K):
                d = z * z - om2[k]
                q = z / d
                S0 += c[k] * q; S1 += sg[k] * q
                if deriv:
                    dq = -(z * z + om2[k]) / (d * d)
                    D0 += c[k] * dq; D1 += sg[k] * dq
            s, co = (z * a).sin(), (z * a).cos()
            A = 2 * s * S1
            B = 2 * (S0 - co * S1)
            if not deriv: return A, B
            Ap = 2 * (a * co * S1 + s * D1)
            Bp = 2 * (D0 + a * s * S1 - co * D1)
            return A, B, Ap, Bp
        g0 = sum(c)
        def ABt(z, deriv=False):
            z = acb(z)
            if not deriv:
                A, B = AB(z); return g0 - z * B / 2, z * A / 2
            A, B, Ap, Bp = AB(z, True)
            return g0 - z * B / 2, z * A / 2, -(B + z * Bp) / 2, (A + z * Ap) / 2
        # (T2) W on the real grid, avoiding w_k exactly
        xs = np.arange(0.00731, R, 0.01)
        Wmin, Wneg, xmin = None, 0, None
        Wrel_min = None
        for x in xs:
            A, B, Ap, Bp = ABt(x, True)
            W = (A * Bp - Ap * B).real
            Wm = float(W.mid())
            nrm = float((A * A + B * B).real.mid())
            rel = Wm / nrm if nrm > 0 else float('inf')    # = phase derivative phi'(x)
            if Wrel_min is None or rel < Wrel_min: Wrel_min, xmin = rel, x
            if W < 0: Wneg += 1
        # (T1) argument principle on the upper half-disc
        def E(z):
            A, B = ABt(z); return complex((A - acb(0, 1) * B).mid())
        n1, n2 = 24001, 40001
        path = [complex(x, 0) for x in np.linspace(-R, R, n1 + 1)] + \
               [R * complex(math.cos(t), math.sin(t)) for t in np.linspace(0, math.pi, n2)[1:]]
        vals = np.array([E(z) for z in path])
        ang = np.unwrap(np.angle(vals))
        wind = (ang[-1] - ang[0]) / (2 * math.pi)
        maxstep = float(np.max(np.abs(np.diff(ang))))
    return dict(delta=delta, K=K, prec=prec, lam1=float(ev.mid()) if hasattr(ev, 'mid') else float(ev),
                zeros_upper_half_disc=round(wind, 3), max_phase_step=maxstep,
                W_negative_points=Wneg, grid_points=len(xs), min_phase_derivative=Wrel_min, at_x=float(xmin),
                secs=round(time.time() - t0))

if __name__ == "__main__":
    for spec in sys.argv[2:]:
        d, K, p = spec.split(':')
        print(json.dumps(run(float(d), int(K), int(p)))); sys.stdout.flush()
