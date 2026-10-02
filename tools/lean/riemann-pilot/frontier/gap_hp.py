"""High-precision gap lambda_perp - lambda_1 in the paper's Gram: lambda_perp = min Q/||g||^2 over
g with <g, w> = sum_k c_k p_k = 0 (p_k = int cos(w_k t) e^{-t/2} = int cos(w_k t) cosh(t/2))."""
import sys, json, math
sys.path.insert(0, '../wt-review/tools/research')
from weil_prime_gram import gram, minimiser
from flint import arb, acb, arb_mat, acb_mat, ctx
for spec in sys.argv[1:]:
    d, K, prec = spec.split(':'); delta, K, prec = float(d), int(K), int(prec)
    G, N, pp = gram(delta, K, prec)
    with ctx.workprec(prec):
        a = arb(delta)/2; half = arb(1)/2
        p = [(2*(acb(half, arb(k)*arb.pi()/a)*a).sinh()/acb(half, arb(k)*arb.pi()/a)).real for k in range(K)]
        # N-orthonormal coordinates y = D c, D = diag(sqrt N); constraint q . y = 0 with q_k = p_k/sqrt(N_k)
        D = [N[k].sqrt() for k in range(K)]
        q = [p[k]/D[k] for k in range(K)]
        qn = sum((x*x for x in q), arb(0)).sqrt(); q = [x/qn for x in q]
        Gs = arb_mat(K, K)
        for i in range(K):
            for j in range(K): Gs[i, j] = G[i, j]/(D[i]*D[j])
        # projector P = I - q q^T ; lambda_perp = smallest eigenvalue of P Gs P on q-perp
        Pm = arb_mat(K, K)
        for i in range(K):
            for j in range(K): Pm[i, j] = (1 if i == j else 0) - q[i]*q[j]
        H = Pm*Gs*Pm
        E = acb_mat(H.mid()).eig(algorithm="approx")
        ev = sorted(float(e.real.mid()) for e in E)
        E0 = acb_mat(Gs.mid()).eig(algorithm="approx")
        ev0 = sorted(float(e.real.mid()) for e in E0)
        # H has a spurious 0 eigenvalue along q: drop the one closest to 0 only if it is the q direction
        lam_perp = min(e for e in ev if abs(e) > 1e-300 * 0 + 0) if False else None
        print(json.dumps({"delta": delta, "K": K, "lam1": ev0[0], "lam2": ev0[1], "H_low": ev[:3]}))
        sys.stdout.flush()
