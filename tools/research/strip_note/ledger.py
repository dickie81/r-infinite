#!/usr/bin/env python3
"""The prime-side LEDGER of Weil's truncated form at a cell (research instrument, uncommitted).

For a coefficient vector c in the even cosine basis on [-a, a] (delta = 2a), Weil's form splits exactly as
  Q(c) = 2 poleR(c)^2 + (psi(1/4) - ln pi) ||g||^2 + ARCH(c) - sum_n PRIME_n(c),
  ARCH(c)   = int_0^inf [f(0) - f(u)] e^{u/2}/sinh(u) du,
  PRIME_n(c)= 2 Lambda(n) n^{-1/2} f(ln n),   n = prime powers <= e^{2a},
with f = g * g~ the autocorrelation. Every piece is bilinear in c; this file builds the K x K matrices of each piece
in mpmath (mirroring weil_prime_gram.gram's closed forms: digamma/trigamma at 1/4 + i omega/2 with geometric tails),
so that any profile's ledger is read off exactly. Profiles: the ground state g_1 (from the certified Gram's minimiser),
the truncated Riemann kernel Phi_a (its K-term cosine projection), and their difference.
Usage: ledger.py <delta> [K prec [dps]]   (defaults from ladder_caster's cells; dps 80 -- the total Q resolves only when dps exceeds -log10 lambda_1 + 10, e.g. 120 at delta = 3)
"""
import sys, os, json, time, math
sys.path.insert(0, '/home/user/r-infinite/tools/research')
import mpmath as mp
from flint import arb, acb, arb_mat, ctx
from weil_prime_gram import gram, minimiser, rayleigh, prime_powers

CELLS = {2.0: (160, 700), 2.3: (260, 900), 2.6: (320, 1000), 3.0: (400, 1100), 3.5: (540, 1300), 1.0: (120, 600), 1.3828125: (140, 600)}
OUT = os.path.dirname(os.path.abspath(__file__))

def Phi(u):
    u = mp.mpf(u); s = mp.mpf(0)
    for n in range(1, 40):
        e = mp.exp(-mp.pi*n*n*mp.exp(2*u))
        if e == 0 and n > 3: break
        s += (2*mp.pi**2*n**4*mp.exp(mp.mpf(9)*u/2) - 3*mp.pi*n*n*mp.exp(mp.mpf(5)*u/2))*e
        if n > 3 and abs(e) < mp.mpf(10)**(-mp.mp.dps-5): break
    return s

def build(delta, K):
    """Matrices (mpmath) of the bilinear pieces in the cosine basis."""
    a = mp.mpf(delta)/2; twoa = 2*a
    om = [mp.mpf(k)*mp.pi/a for k in range(K)]
    quarter = mp.mpf(1)/4
    psi_q = mp.digamma(quarter); tri_q = mp.polygamma(1, quarter)
    psi = [mp.digamma(mp.mpc(quarter, o/2)) for o in om]
    tri = [mp.polygamma(1, mp.mpc(quarter, o/2)) for o in om]
    M = int(mp.mp.dps*math.log(10)/(2*float(delta))) + 6
    T0 = mp.mpf(0); Tu0 = mp.mpf(0)
    Tc = [mp.mpf(0)]*K; Tuc = [mp.mpf(0)]*K; Ts = [mp.mpf(0)]*K
    for m in range(M):
        s = mp.mpf(2*m) + mp.mpf(1)/2
        e = mp.exp(-twoa*s)
        T0 += 2*e/s; Tu0 += 2*e*(twoa/s + 1/(s*s))
        for k in range(1, K):
            w = mp.mpc(s, -om[k]); ew = mp.exp(-twoa*w); q = ew/w
            Tc[k] += 2*q.real; Ts[k] += 2*q.imag; Tuc[k] += 2*(ew*(twoa/w + 1/(w*w))).real
    S = [mp.mpf(0)]*K; C1 = [mp.mpf(0)]*K; U = [mp.mpf(0)]*K
    for k in range(1, K):
        S[k] = psi[k].imag - Ts[k]
        C1[k] = (psi[k].real - psi_q) - (T0 - Tc[k])
        U[k] = tri[k].real/2 - Tuc[k]
    U0 = tri_q/2 - Tu0
    pole = []
    for k in range(K):
        w = mp.mpc(mp.mpf(1)/2, om[k])
        pole.append((2*mp.sinh(w*a)/w).real)
    pp = prime_powers(int(math.floor(float(mp.exp(twoa)) + 1e-9)))
    pp = [(n, p) for n, p in pp if mp.log(n) < twoa]
    lam = [(mp.log(n), mp.log(p)/mp.sqrt(n)) for n, p in pp]
    N = [a]*K; N[0] = twoa
    A = mp.matrix(K, K)
    P = {n: mp.matrix(K, K) for n, _ in pp}
    sinl = [[mp.sin(om[k]*u) for k in range(K)] for u, _ in lam]
    cosl = [[mp.cos(om[k]*u) for k in range(K)] for u, _ in lam]
    for j in range(K):
        for k in range(j, K):
            if j == k:
                if k == 0:
                    A[0, 0] = U0 + twoa*T0
                    for i, (u, wgt) in enumerate(lam):
                        P[pp[i][0]][0, 0] = 2*wgt*(twoa - u)
                else:
                    A[k, k] = a*C1[k] + U[k]/2 + S[k]/(2*om[k]) + a*T0
                    for i, (u, wgt) in enumerate(lam):
                        P[pp[i][0]][k, k] = 2*wgt*((twoa - u)*cosl[i][k] - sinl[i][k]/om[k])/2
            else:
                sg = -1 if (j + k) % 2 else 1
                den = om[j]*om[j] - om[k]*om[k]
                A[j, k] = A[k, j] = sg*(om[j]*S[j] - om[k]*S[k])/den
                for i, (u, wgt) in enumerate(lam):
                    v = 2*wgt*sg*(om[k]*sinl[i][k] - om[j]*sinl[i][j])/den
                    P[pp[i][0]][j, k] = v; P[pp[i][0]][k, j] = v
    return dict(a=a, om=om, N=N, A=A, P=P, pp=pp, pole=pole, const=psi_q - mp.log(mp.pi), lam=lam)

def quad(Mx, c):
    K = len(c); s = mp.mpf(0)
    for j in range(K):
        cj = c[j]
        if cj == 0: continue
        row = mp.mpf(0)
        for k in range(K): row += Mx[j, k]*c[k]
        s += cj*row
    return s

def ledger(B, c):
    K = len(c)
    norm = sum(B['N'][k]*c[k]*c[k] for k in range(K))
    pr = sum(B['pole'][k]*c[k] for k in range(K))
    L = {'norm': norm, 'pole2': 2*pr*pr, 'const': B['const']*norm, 'arch': quad(B['A'], c)}
    L['prime'] = {n: quad(B['P'][n], c) for n, _ in B['pp']}
    L['Q'] = L['pole2'] + L['const'] + L['arch'] - sum(L['prime'].values())
    return L

def autocorr(B, c, u):
    """f_c(u) for 0 <= u <= 2a from the closed forms."""
    a = B['a']; om = B['om']; K = len(c); twoa = 2*a; u = mp.mpf(u)
    f = c[0]*c[0]*(twoa - u)
    for k in range(1, K):
        f += c[k]*c[k]*((twoa - u)*mp.cos(om[k]*u) - mp.sin(om[k]*u)/om[k])/2
        Bk = mp.mpf(0)
        for j in range(K):
            if j == k: continue
            Bk += ((-1)**(j + k))*c[j]*c[k]/(om[j]*om[j] - om[k]*om[k])
        f += 2*om[k]*Bk*mp.sin(om[k]*u)
    return f

def phi_coeffs(a, K):
    """Cosine coefficients of Phi on [-a, a]: v_0 = (1/a) int_0^a Phi, v_k = (2/a) int_0^a Phi cos(omega_k t)."""
    om = [mp.mpf(k)*mp.pi/a for k in range(K)]
    # fixed Gauss-Legendre grid: panels of length a/NP, 24 nodes each (the highest frequency (K-1) pi/a needs
    # ~ K/2 panels per unit a for 24-node exactness of the oscillation; we use 4K/... generous)
    NP = max(8*K//4, 200); deg = 24
    nodes, weights = mp.gauss_legendre(deg) if hasattr(mp, 'gauss_legendre') else (None, None)
    if nodes is None:
        import numpy as np
        xn, wn = np.polynomial.legendre.leggauss(deg)
        nodes = [mp.mpf(float(x)) for x in xn]; weights = [mp.mpf(float(w)) for w in wn]
        # refine nodes/weights to working precision by Newton on P_deg
        def legP(n, x):
            p0, p1 = mp.mpf(1), x
            for i in range(1, n): p0, p1 = p1, ((2*i + 1)*x*p1 - i*p0)/(i + 1)
            return p1
        def dlegP(n, x):
            return n*(x*legP(n, x) - legP(n - 1, x))/(x*x - 1)
        nodes = [x - legP(deg, x)/dlegP(deg, x) for x in nodes]
        nodes = [x - legP(deg, x)/dlegP(deg, x) for x in nodes]
        weights = [2/((1 - x*x)*dlegP(deg, x)**2) for x in nodes]
    ts = []; ws = []
    h = a/NP
    for p in range(NP):
        mid = (p + mp.mpf(1)/2)*h
        for x, w in zip(nodes, weights):
            ts.append(mid + x*h/2); ws.append(w*h/2)
    Ph = [Phi(t)*w for t, w in zip(ts, ws)]
    v = []
    for k in range(K):
        val = sum(P*mp.cos(om[k]*t) for P, t in zip(Ph, ts))   # int_0^a Phi cos(omega_k t) dt
        v.append(2*val/a if k else val/a)
    return v

def main():
    delta = float(sys.argv[1]); K, prec = CELLS[delta] if len(sys.argv) < 4 else (int(sys.argv[2]), int(sys.argv[3]))
    mp.mp.dps = int(sys.argv[4]) if len(sys.argv) > 4 else 80
    print(f'working precision {mp.mp.dps} digits', flush=True)
    t0 = time.time()
    G, N, pp = gram(delta, K, prec); c_arb, ev = minimiser(G, N, prec)
    rq = rayleigh(G, N, c_arb, prec)
    with ctx.workprec(prec):
        c1 = [mp.mpf(x.str(60, radius=False)) for x in c_arb]
        ln_lam1 = float(ev.log()) if ev > 0 else None
    print(f"gram+eig {time.time()-t0:.0f}s  ln lambda_1 = {ln_lam1}  rq = {rq.str(12)}", flush=True)
    t0 = time.time(); B = build(delta, K); print(f"pieces {time.time()-t0:.0f}s", flush=True)
    a = B['a']
    # normalise g_1
    n1 = mp.sqrt(sum(B['N'][k]*c1[k]*c1[k] for k in range(K))); c1 = [x/n1 for x in c1]
    # Phi_a projection, normalised
    t0 = time.time(); cP = phi_coeffs(a, K); print(f"Phi coeffs {time.time()-t0:.0f}s", flush=True)
    nP = mp.sqrt(sum(B['N'][k]*cP[k]*cP[k] for k in range(K))); cP = [x/nP for x in cP]
    # sign alignment and angle
    ip = sum(B['N'][k]*c1[k]*cP[k] for k in range(K))
    if ip < 0: c1 = [-x for x in c1]; ip = -ip
    sin2 = 1 - ip*ip
    L1 = ledger(B, c1); LP = ledger(B, cP)
    # check Q(g_1) against the certified Gram
    with ctx.workprec(prec):
        v = arb_mat(K, 1)
        for i in range(K): v[i, 0] = arb(mp.nstr(c1[i], 60))
        Qarb = (v.transpose()*G*v)[0, 0]
        print("Q(g_1) from Gram (arb):", Qarb.str(20), " ledger:", mp.nstr(L1['Q'], 20))
    print(f"delta={delta} K={K} T0={float(2*mp.pi*mp.exp(delta)):.3f}  sin^2(theta)(g_1,Phi_a^K) = {mp.nstr(sin2, 6)}  ln lambda_1 = {ln_lam1}")
    def show(name, L):
        print(f"--- {name}: Q = {mp.nstr(L['Q'], 12)}  (ln = {mp.nstr(mp.log(abs(L['Q'])), 8)})")
        print(f"    pole2 = {mp.nstr(L['pole2'], 25)}\n    const = {mp.nstr(L['const'], 25)}\n    arch  = {mp.nstr(L['arch'], 25)}")
        for n, val in L['prime'].items():
            print(f"    prime n={n:3d} (ln n = {mp.nstr(mp.log(n), 6)}): {mp.nstr(val, 25)}")
        print(f"    sum prime = {mp.nstr(sum(L['prime'].values()), 25)}   arch-side total = {mp.nstr(L['pole2']+L['const']+L['arch'], 25)}")
    show('ground state g_1', L1); show('Phi_a (K-term projection)', LP)
    print("--- DIFFERENCE g_1 - Phi_a (each ledger line):")
    for key in ['pole2', 'const', 'arch']:
        print(f"    {key}: {mp.nstr(L1[key]-LP[key], 12)}")
    for n in L1['prime']:
        print(f"    prime n={n:3d}: {mp.nstr(L1['prime'][n]-LP['prime'][n], 12)}")
    print(f"    Q: {mp.nstr(L1['Q']-LP['Q'], 12)}")
    # autocorrelation profiles at the prime logs and on a grid near the edge
    print("--- autocorrelation f(u) at ln n and near the edge 2a:")
    us = [B['lam'][i][0] for i in range(len(B['pp']))] + [2*a - mp.mpf(x)/10 for x in (8, 6, 4, 3, 2, 1)] + [2*a - mp.mpf('0.05'), 2*a - mp.mpf('0.02')]
    rows = []
    for u in us:
        f1 = autocorr(B, c1, u); fP = autocorr(B, cP, u)
        rows.append((float(u), mp.nstr(f1, 10), mp.nstr(fP, 10), mp.nstr(f1 - fP, 8), mp.nstr(f1/fP, 8) if fP != 0 else 'nan'))
        print(f"    u={float(u):.4f}  f_g1={rows[-1][1]:>16}  f_Phi={rows[-1][2]:>16}  diff={rows[-1][3]:>14}  ratio={rows[-1][4]}")
    # boundary values
    g1a = sum(c1[k]*mp.cos(B['om'][k]*a) for k in range(K)); gPa = sum(cP[k]*mp.cos(B['om'][k]*a) for k in range(K))
    print(f"    g_1(a) = {mp.nstr(g1a, 8)}   Phi_a^K(a) = {mp.nstr(gPa, 8)}   Phi(a) = {mp.nstr(Phi(a)/nP, 8)}")
    json.dump({'delta': delta, 'K': K, 'prec': prec, 'ln_lam1': ln_lam1, 'sin2': float(sin2),
               'ledger_g1': {k: (mp.nstr(v, 40) if not isinstance(v, dict) else {n: mp.nstr(x, 40) for n, x in v.items()}) for k, v in L1.items()},
               'ledger_Phi': {k: (mp.nstr(v, 40) if not isinstance(v, dict) else {n: mp.nstr(x, 40) for n, x in v.items()}) for k, v in LP.items()},
               'c1': [mp.nstr(x, 50) for x in c1], 'cP': [mp.nstr(x, 50) for x in cP], 'rows': rows},
              open(os.path.join(OUT, f'ledger_d{delta}.json'), 'w'))

if __name__ == '__main__':
    main()
