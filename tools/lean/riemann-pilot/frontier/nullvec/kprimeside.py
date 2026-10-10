#!/usr/bin/env python3
"""Round 118: the window chain rebuilt on the PRIME side of Weil's explicit formula (unconditional; no zero is used).

Zero side (kzeroside2.py): M = sum_{gamma>0} F F^T, F_k(t) = ghat_k(t) = (-1)^k 2t sin(ta)/(t^2 - w_k^2), w_k = k pi/a, a = ln(x)/2,
g = sum c_k cos(w_k u) on [-a, a]; K(0,0) = (2a)^2 (M^-1)_00.

Explicit formula (Guinand-Weil; unconditional, the sum over ALL nontrivial zeros rho = 1/2 + i gamma, gamma complex if off the line):
  sum_rho H(gamma) = H(i/2) + H(-i/2) - G(0) ln pi + (1/2pi) int H(r) Re psi(1/4 + ir/2) dr - 2 sum_n Lambda(n) n^-1/2 G(ln n),
with H = ghat^2 and G = g*g. Under RH, sum_rho = 2 sum_{gamma>0} |ghat|^2, so M_prime := A/2 is the zero-side M (all zeros).

Closed forms (no quadrature). Since ghat_j ghat_k = (-1)^{j+k} 4 [u_A - u_B]/(A - B), u_A(t) = A sin^2(ta)/(t^2 - A), A = w^2, every
linear functional L gives L(ghat_j ghat_k) = 4 (-1)^{j+k} DD[Phi](w_j, w_k), with Phi(w) = L(u_{w^2}) and DD the divided difference in
A = w^2 (the derivative dPhi/dA on the diagonal). With z = 1/4 + i w/2, beta_m = 2m + 1/2 and T(w) = sum_m x^-beta_m/(beta_m^2 + w^2):
  G(0):            Phi_G(w)   = w sin(2aw)/4
  G(u), 0<=u<=2a:  Phi_u(w)   = -(w/4)[sin(uw) - sin(2aw) cos(uw)]
  archimedean:     Phi_psi(w) = (w sin(2aw)/4) Re psi(z) + (w/4) Im psi(z) - (w^2/2) T(w)
(the last by Re psi(1/4+it/2) = -gamma_E + sum_m [1/(m+1) - 2 beta_m/(beta_m^2 + t^2)] and sum_m 1/(beta_m^2 + w^2) = Im psi(z)/(2w)).
The pole term is rank one: ghat_k(i/2) = (-1)^k sinh(a/2)/(w_k^2 + 1/4).

Usage: kprimeside.py Kfac x1 x2 ...     env: PS_DROP="2,3" drops those primes (all powers); PS_RESP="2,3,5,7,11" per-prime
first-order responses dlnK/deps = -y^T B_p y / y_0 (y = M^-1 e_0; round 113's response_kernel), B_p = prime p's term in M."""
import sys, json, math, os
from flint import arb, acb, arb_mat, ctx
from sympy import primerange

DROP = {int(s) for s in os.environ.get("PS_DROP", "").split(",") if s}
RESP = [int(s) for s in os.environ.get("PS_RESP", "").split(",") if s]
RESPN = [int(s) for s in os.environ.get("PS_RESPN", "").split(",") if s]   # single prime-power terms n = p^m
NOPRIME = os.environ.get("PS_NOPRIME", "") == "1"
KEEPN = {int(s) for s in os.environ.get("PS_KEEPN", "").split(",") if s}   # keep only these prime-power terms (Gamma + chosen terms)   # the Gamma-only form: poles + archimedean, no primes

def prime_powers(x):
    out = []
    for p in primerange(2, int(math.floor(x + 1e-9)) + 1):
        n = p
        while n <= x + 1e-9: out.append((p, n)); n *= p
    return out

N_val, N_dd = {}, {}   # per prime-power term, filled by phi_parts

def phi_parts(a, w, K, xv, pp):
    """Per-k values Phi(w_k) and diagonal DD(k,k) for the smooth part and for each prime's part."""
    pi = arb.pi(); lnpi = pi.log(); half = arb(1)/2; quarter = arb(1)/4
    # T(w) and T2(w) = sum q/(beta^2 + w^2)^2
    x = arb(repr(xv)); lx = x.log(); M = int(ctx.prec*0.7/(2*math.log(xv))) + 12   # exact decimal x (a double ln x breaks the form)
    q = [(-(2*m + half)*lx).exp() for m in range(M)]; bet2 = [(2*m + half)**2 for m in range(M)]
    # rigorous remainders (round 119): for m >= M, x^-beta_m/(beta_m^2 + w^2) <= x^-beta_M x^-2(m-M)/beta_M^2, a geometric series
    qM = (-(2*M + half)*lx).exp(); geo = 1/(1 - (-2*lx).exp()); bM2 = (2*M + half)**2
    remT = arb(0, float((qM*geo/bM2).upper()) * 1.01); remT2 = arb(0, float((qM*geo/(bM2*bM2)).upper()) * 1.01)
    S_val, S_dd = [arb(0)]*K, [arb(0)]*K
    P_val = {}; P_dd = {}; N_val.clear(); N_dd.clear()
    for k in range(K):
        wk = w[k]
        if k == 0:
            T0 = sum(qi/b for qi, b in zip(q, bet2)) + remT
            psi14 = acb(quarter).digamma().real; tri14 = acb.zeta(acb(2), acb(quarter)).real
            S_dd[0] = a/2*psi14 + tri14/8 - T0/2 - lnpi*a/2
            continue
        z = acb(quarter, wk/2); ps = z.digamma(); tri = acb.zeta(acb(2), z)
        w2 = wk*wk; T = sum(qi/(b + w2) for qi, b in zip(q, bet2)) + remT; T2 = sum(qi/(b + w2)**2 for qi, b in zip(q, bet2)) + remT2
        S_val[k] = wk/4*ps.imag - w2/2*T
        dpsi = a*wk/2*ps.real + ps.imag/4 + wk/8*tri.real - wk*T + wk*w2*T2
        dG = a*wk/2
        S_dd[k] = (dpsi - lnpi*dG)/(2*wk)
    for p, n in pp:
        c = -2*arb(p).log()/arb(n).sqrt(); u = arb(n).log()
        v, d = P_val.setdefault(p, [arb(0)]*K), P_dd.setdefault(p, [arb(0)]*K)
        vn, dn = N_val.setdefault(n, [arb(0)]*K), N_dd.setdefault(n, [arb(0)]*K)
        for k in range(K):
            if k == 0:
                d[0] += c*(2*a - u)/4; dn[0] += c*(2*a - u)/4; continue
            wk = w[k]; su, cu = (u*wk).sin(), (u*wk).cos()
            tv, td = c*(-wk/4*su), c*(-su/4 + wk/4*(2*a - u)*cu)/(2*wk)
            v[k] += tv; d[k] += td; vn[k] += tv; dn[k] += td
    return S_val, S_dd, P_val, P_dd

def assemble(K, w, val, dd, sign):
    Mx = arb_mat(K, K)
    for j in range(K):
        for k in range(j, K):
            if j == k: e = dd[k]
            else: e = (val[j] - val[k])/(w[j]*w[j] - w[k]*w[k])
            e = 2*sign[j]*sign[k]*e          # 4 (-1)^{j+k} DD, halved (M = A/2)
            Mx[j, k] = e; Mx[k, j] = e
    return Mx

if __name__ == "__main__":
    Kf = float(sys.argv[1])
    for xv in map(float, sys.argv[2:]):
        d = math.log(xv); K = max(40, int(Kf*xv) + 40); prec0 = int(96 + 2.1*4*math.pi*xv*1.4427)
        for fac in (1, 1.5, 2, 3, 4):     # adaptive: the prime-side entries cancel more than the zero-side rows
          prec = int(prec0*fac)
          with ctx.workprec(prec):
              # exact x: a double ln x shifts the window edge by 1e-16 against the exact prime positions ln n, which breaks positivity
              a = arb(repr(xv)).log()/2; pi = arb.pi(); w = [arb(k)*pi/a for k in range(K)]; sign = [1 if k % 2 == 0 else -1 for k in range(K)]
              pp = [] if NOPRIME else [(p, n) for p, n in prime_powers(xv) if p not in DROP and (not KEEPN or n in KEEPN)]
              S_val, S_dd, P_val, P_dd = phi_parts(a, w, K, xv, pp)
              val = list(S_val); dd = list(S_dd)
              for p in P_val:
                  for k in range(K): val[k] += P_val[p][k]; dd[k] += P_dd[p][k]
              M = assemble(K, w, val, dd, sign)
              Pk = [sign[k]*(a/2).sinh()/(w[k]*w[k] + arb(1)/4) for k in range(K)]
              for j in range(K):
                  for k in range(K): M[j, k] += Pk[j]*Pk[k]          # (2 P P^T)/2
              e = arb_mat(K, 1); e[0, 0] = arb(1)
              try: y = M.solve(e)
              except ZeroDivisionError: continue
              y0 = y[0, 0]; lk = ((2*a)**2*y0).log()
              if not (lk.is_finite() and float(lk.rad()) < 1e-8): continue
              out = {"x": xv, "K": K, "prec": prec, "drop": sorted(DROP), "noprime": NOPRIME, "keepn": sorted(KEEPN), "lnK00": ((2*a)**2*y0).log().mid().str(15, radius=False),
                     "lnK00_rad": float(((2*a)**2*y0).log().rad())}
              if RESP:
                  r = {}
                  for p in RESP:
                      if p not in P_val: r[p] = 0.0; continue
                      Bp = assemble(K, w, P_val[p], P_dd[p], sign)
                      r[p] = float((-(y.transpose()*Bp*y)[0, 0]/y0).mid())
                  out["resp"] = r
              if RESPN:
                  r = {}
                  for n in RESPN:
                      if n not in N_val: r[n] = 0.0; continue
                      Bn = assemble(K, w, N_val[n], N_dd[n], sign)
                      r[n] = float((-(y.transpose()*Bn*y)[0, 0]/y0).mid())
                  out["respn"] = r
              out["prec_factor"] = fac
              print(json.dumps(out), flush=True); break
