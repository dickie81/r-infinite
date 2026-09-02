#!/usr/bin/env python3
"""THE MECHANISM PROOF, ARB PORT (owner: "Install python-flint and port the
numerics layer to ARB and pull the algorithmic lever"; Addendum 425/427).
The substrate of Theorem 1bl (the 1bl landing; verifier
cascade_slepian_mechanism.py, tower member 21): every quantity is an
ARB ball (rigorous, arbitrary precision); the four certified cells are
content-addressed checkpoints produced by run(kernel, parity).

THE BOUND (Addendum 425).  For a real probe g on [-a, a] of fixed parity,
ghat its Fourier transform (exponential type a), the S-local Weil form
    Q(g) = (1/2pi) int_R |ghat|^2 W dr  +/-  2 <chi, g>^2,
    W(r) = Re psi(1/4 + ir/2) - log pi - sum_{(lag, w) in S} w cos(r lag),
is the full functional for support length 2a below the next prime-power
lag.  With Omega such that W_out := W_inf(Omega) - sum w > 0 (W_inf is
increasing), for EVERY g:  Q(g) >= <g, M g>,  M = A_in + W_out (I - K)
+/- 2 chi chi^T  (A_in the band form on |r| <= Omega, K the Slepian
concentration operator of (a, Omega)), and in the prolate basis the tail
is positive by concentration, so  lambda_min(Q) >= lambda_min of the 2x2
[[lambda_min(M_head), -b], [-b, q_perp]].

WHAT THE PORT CHANGES (against oneprime_slepian_certificate.py):
  * arithmetic: python-flint ARB/ACB balls at 256 bits (the Legendre
    recurrence at 400 bits, where naive ball propagation doubles the
    radius per step: 2^240 * 2^-400 = 2^-160);
  * prolates: the float eigenvectors of Slepian's tridiagonal are refined
    by inverse iteration in ball arithmetic (residuals ~1e-40), then the
    rigorous residual / Sturm count / gap chain as before;
  * the kernel: acb digamma at the nodes (radius ~1e-78); on the complex
    disks of the error bounds, the instrument's own shifted Stirling
    enclosure in complex balls (Binet remainder), since ARB's ball digamma
    does not enclose fat balls;
  * THE LEVER -- the band integral by Gauss-Legendre on cells with the
    ANALYTIC error bound: the integrand f = phi_j phi_k W_hol(Omega x) is
    holomorphic in the strip |Im x| < 1/(2 Omega) (W's poles sit at
    Im r = +/-(1/2 + 2m)); on a cell of half-width h/2 mapped to [-1,1] the
    Bernstein ellipse E_rho with semi-minor axis (rho - 1/rho)/2 * h/2 <
    1/(2 Omega) lies in the strip, and for f analytic in E_rho with |f| <= M
    the n-point Gauss-Legendre error is <= (64/15) M rho^{-2n} / (rho^2 - 1)
    (Trefethen, Approximation Theory and Approximation Practice, Thm 19.3);
    M = sup |phi_j| sup |phi_k| sup |W_hol| over the disk covering the
    ellipse, the polynomial sups by  |P_n(z)| <= rho_d^n  on the global
    ellipse of parameter rho_d = 1 + d + sqrt(2d + d^2) (every point within
    distance d of [-1,1] lies inside it), the kernel sup by the Stirling
    enclosure on the disk.  Nodes and weights: arb.legendre_p_root
    (rigorous).  30 nodes on cells of 5e-3 replace 10^4 Simpson cells, with
    errors ~1e-26 per cell instead of ~1e-11.
  * lambda_min of the head pencil: a verified Cholesky factorisation of
    M - sigma I in ball arithmetic (positive pivots prove M - sigma I > 0,
    hence lambda_min >= sigma; the near-degenerate cluster of high prolates
    at W_out defeats eigenvalue isolation but not this test).

Usage: slepian_arb_certificate.py <kernel: one|two> <parity: even|odd|both>
       [NH] [h] [Omega]
  one: a = 35/64  (delta 1.09375 < log 3), Omega 64, S = {2}
  two: a = 177/256 (delta 1.3828125 < log 4), Omega 128, S = {2, 3}
Checks 7/8 clean; no RH consequence is claimed.
"""
import sys, os, math, time, json
import numpy as np
from scipy.linalg import eigh_tridiagonal
from flint import arb, acb, arb_mat, acb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
PREC = 256
PREC_LEG = 400
# precision is set by ctx.workprec(...) context managers, never by a store on
# the imported context (the tower precheck's clause G, the 1bl landing)

BERN = [(1, 6), (-1, 30), (1, 42), (-1, 30), (5, 66), (-691, 2730), (7, 6), (-3617, 510),
        (43867, 798), (-174611, 330), (854513, 138)]        # B_2 .. B_22
XMIN_S = 25

def A_(x):
    return arb(x)

def bern(k):
    num, den = BERN[k - 1]
    return arb(num)/arb(den)

def psi_stirling_acb(z, K=10):
    """Rigorous enclosure (acb ball) of psi(z) for an acb ball z with
    Re z > 0: shift to w = z + n with Re w >= XMIN_S and Re w >= sqrt2 |Im w|,
    psi(z) = psi(w) - sum_{k<n} 1/(z+k); psi(w) by Binet's second formula
    expanded: ln w - 1/(2w) - sum_{k=1}^{K} B_{2k}/(2k w^{2k}) + R,
    |R| <= 2|B_{2K+2}|/(4(K+1)) / (|w|^{2K} d_w), d_w = min_t |t^2 + w^2| >= |w|^2
    when Re w >= |Im w|  (|t^2+w^2|^2 = (t^2 + x^2 - y^2)^2 + 4x^2y^2 >= |w|^4)."""
    x = z.real; y = z.imag
    xlo = float(x.lower()); yhi = float(abs(y).upper())
    n = max(math.ceil(XMIN_S - xlo), math.ceil(1.4142135623730951*yhi - xlo) + 1, 0)
    s = acb(0)
    for k in range(n):
        s = s + 1/(z + k)
    w = z + n
    wx = w.real; wy = w.imag
    assert float(wx.lower()) >= float(abs(wy).upper()), "shift too short"
    val = w.log() - 1/(2*w)
    winv2 = 1/(w*w)
    p = winv2
    for k in range(1, K + 1):
        val = val - bern(k)/(2*k)*p
        p = p*winv2
    num, den = BERN[K]
    b2k2 = arb(abs(num))/arb(den)
    modw2 = wx*wx + wy*wy
    modw2_lo = arb(float(modw2.lower()))
    rem = 2*b2k2/(4*(K + 1))/(modw2_lo**K*modw2_lo)
    rem_hi = float(rem.upper())
    val = val + acb(arb(0, rem_hi), arb(0, rem_hi))
    return val - s

def W_hol_acb(zr, terms):
    """The holomorphic extension of the kernel in the variable r (acb):
    (psi(1/4 + i r/2) + psi(1/4 - i r/2))/2 - log pi - sum w cos(r lag)."""
    I_ = acb(0, 1)
    z1 = acb(arb(1)/4) + I_*zr/2
    z2 = acb(arb(1)/4) - I_*zr/2
    val = (psi_stirling_acb(z1) + psi_stirling_acb(z2))/2 - arb.pi().log()
    for lag, w in terms:
        val = val - w*(zr*lag).cos()
    return val

def W_real(r, terms):
    """W(r) at a real ball r via acb digamma (rigorous, tight)."""
    z = acb(arb(1)/4, r/2)
    val = z.digamma().real - arb.pi().log()
    for lag, w in terms:
        val = val - w*(r*lag).cos()
    return val

# ------------------------------------------------------------ prolates
def tridiag(parity, nmax, c2):
    ns = list(range(0 if parity == "even" else 1, nmax, 2))
    d = []; e = []
    for n in ns:
        nA = arb(n)
        d.append(nA*(nA + 1) + c2*(2*nA*nA + 2*nA - 1)/((2*nA + 3)*(2*nA - 1)))
    for n in ns[:-1]:
        nA = arb(n)
        e.append(c2*(nA + 2)*(nA + 1)/((2*nA + 3)*((2*nA + 1)*(2*nA + 5)).sqrt()))
    return ns, d, e

def sturm_count(d, e, x, tail_widen):
    n = len(d); cnt = 0; p = None
    for i in range(n):
        di = d[i] - x
        if i == n - 1:
            di = di - arb(tail_widen/2, tail_widen/2)     # widen the last pivot downward by the Schur tail bound
        piv = di if i == 0 else di - e[i - 1]*e[i - 1]/p
        if piv.contains(arb(0)) or (i > 0 and p.contains(arb(0))):
            return cnt, False
        if float(piv.upper()) < 0:
            cnt += 1
        p = piv
    return cnt, True

def tri_solve(d, e, shift, rhs):
    """Solve (T - shift) w = rhs for a symmetric tridiagonal (arb), Thomas."""
    n = len(d)
    a = [d[i] - shift for i in range(n)]
    cp = [None]*n; dp = [None]*n
    cp[0] = e[0]/a[0]; dp[0] = rhs[0]/a[0]
    for i in range(1, n):
        m = a[i] - e[i - 1]*cp[i - 1]
        cp[i] = (e[i]/m) if i < n - 1 else arb(0)
        dp[i] = (rhs[i] - e[i - 1]*dp[i - 1])/m
    w = [None]*n
    w[-1] = dp[-1]
    for i in range(n - 2, -1, -1):
        w[i] = dp[i] - cp[i]*w[i + 1]
    return w

def verified_pswf(parity, NH, nmax, c2, log):
    ns, d, e = tridiag(parity, nmax, c2)
    dm = np.array([float(x.mid()) for x in d]); em = np.array([float(x.mid()) for x in e])
    chi, Vv = eigh_tridiagonal(dm, em)
    m = len(ns)
    nlast = ns[-1] + 2
    nA = arb(nlast)
    e_tail = c2*nA*(nA - 1)/((2*nA - 1)*((2*nA - 3)*(2*nA + 1)).sqrt())
    K = NH + 3
    x_max = float(chi[K]) + 100.0
    d_tail_min = float((nA*(nA + 1) - 2*e_tail - x_max).lower())     # a lower endpoint (round 287 F287-4)
    assert d_tail_min > 0
    tail_widen = float((e_tail*e_tail/d_tail_min).upper())
    out = []
    for k in range(K):
        v = [arb(float(x)) for x in Vv[:, k]]
        # inverse-iteration refinement in ball arithmetic (2 steps; the
        # midpoints are re-taken as exact numbers after each step)
        chik = arb(float(chi[k]))
        for _ in range(3):
            rhs = v
            try:
                w = tri_solve(d, e, chik + arb(1e-9), rhs)   # tiny shift keeps the solve nonsingular
            except ZeroDivisionError:
                break
            nrm = sum((x*x for x in w), arb(0)).sqrt()
            v = [(x/nrm).mid() for x in w]                  # exact 256-bit midpoints (zero radius)
            # Rayleigh quotient update
            Tv = [d[i]*v[i] + (e[i - 1]*v[i - 1] if i > 0 else 0) + (e[i]*v[i + 1] if i < m - 1 else 0) for i in range(m)]
            chik = sum((v[i]*Tv[i] for i in range(m)), arb(0)).mid()
        # rigorous residual of the exact stored vector (padded), with the tail coupling
        Tv = [d[i]*v[i] + (e[i - 1]*v[i - 1] if i > 0 else 0) + (e[i]*v[i + 1] if i < m - 1 else 0) for i in range(m)]
        res2 = sum(((Tv[i] - chik*v[i])**2 for i in range(m)), arb(0)) + (e_tail*v[-1])**2
        nv2 = sum((x*x for x in v), arb(0))
        r_k = float((res2.sqrt()/nv2.sqrt()).upper())
        out.append(dict(k=k, chi=float(chik.mid()), v=v, r=r_k, nv=nv2.sqrt()))
    for k in range(K):
        Dk = max(out[k]["r"], 1e-7*(1.0 + abs(out[k]["chi"])))
        done = False
        for _ in range(8):
            c1, ok1 = sturm_count(d, e, arb(out[k]["chi"] - Dk), tail_widen)
            c2_, ok2 = sturm_count(d, e, arb(out[k]["chi"] + Dk), tail_widen)
            if ok1 and ok2:
                assert c1 == k and c2_ == k + 1, f"Sturm count at k={k}: {c1},{c2_}"
                done = True; break
            Dk *= 10.0
        assert done, f"Sturm pivots indefinite at k={k}"
        assert out[k]["chi"] + Dk <= x_max, "Sturm point beyond the tail's dominance range"   # F286-8
        out[k]["D"] = Dk
        # the true eigenvector's Legendre tail beyond the truncation (F286-5): with
        # T the tail block, (T - chi) beta_tail = -e_tail beta_last e_1 and the tail
        # diagonally dominant (d_n - chi >= d_tail_min, off-diagonals <= e_tail), the
        # Neumann series gives |beta_{last+j}| <= e_tail |beta_last| q^(j-1) / (d_tail_min (1 - q)),
        # q = 2 e_tail / d_tail_min; |beta_last| <= |v_last| + eps (eps is an l2 bound)
        out[k]["vlast"] = float(abs(out[k]["v"][-1]).upper())
        out[k]["e_tail"] = float(e_tail.upper()); out[k]["d_tail"] = d_tail_min; out[k]["nlast"] = nlast
    for k in range(K - 1):
        gaps = []
        if k > 0: gaps.append(out[k]["chi"] - out[k]["D"] - (out[k-1]["chi"] + out[k-1]["D"]))
        gaps.append(out[k+1]["chi"] - out[k+1]["D"] - (out[k]["chi"] + out[k]["D"]))
        gap = min(gaps); assert gap > 0
        out[k]["gap"] = gap
        nv = float(out[k]["nv"].mid())
        out[k]["eps"] = math.sqrt(2.0)*out[k]["r"]/gap*(1 + 1e-12) + abs(1.0 - nv)*(1 + 1e-12) + 1e-40
    log(f"  prolates: {len(ns)} Legendre indices (n < {nmax}); chi range [{out[0]['chi']:.2f}, {out[K-2]['chi']:.2f}]; "
        f"max residual {max(p['r'] for p in out[:K-1]):.2e}, min gap {min(p['gap'] for p in out[:K-1]):.2f}, max eps {max(p['eps'] for p in out[:K-1]):.2e}")
    return ns, out[:K - 1]

# -------------------------------------------------------- Legendre tools
def legendre_P_at(x, nmax):
    """P_0..P_{nmax-1} at an arb point x, by the recurrence at PREC_LEG bits."""
    with ctx.workprec(PREC_LEG):
        vals = [arb(1), x]
        for n in range(1, nmax - 1):
            vals.append(((2*n + 1)*x*vals[n] - n*vals[n - 1])/(n + 1))
    with ctx.workprec(PREC):
        return [arb(v) for v in vals[:nmax]]

def P0_dP0(nmax):
    P0 = [arb(1), arb(0)]; dP0 = [arb(0), arb(1)]
    for n in range(1, nmax - 1):
        P0.append((-arb(n)*P0[n - 1])/arb(n + 1))
        dP0.append((arb(2*n + 1)*P0[n] - arb(n)*dP0[n - 1])/arb(n + 1))
    return P0[:nmax], dP0[:nmax]

def sph_in(n, s):
    """i_n(s) = sqrt(pi/(2s)) I_{n+1/2}(s)."""
    return (arb.pi()/(2*s)).sqrt()*s.bessel_i(arb(2*n + 1)/2)

# --------------------------------------------------------------- the proof
def certify(kernel, parity, NH=None, h=None, Omega=None, verbose=True):
    """The certified cell; every ball operation inside runs at PREC bits."""
    with ctx.workprec(PREC):
        return _certify(kernel, parity, NH, h, Omega, verbose)

def _certify(kernel, parity, NH=None, h=None, Omega=None, verbose=True):
    t0 = time.time()
    log = (lambda *a: print(*a, flush=True)) if verbose else (lambda *a: None)
    if kernel == "one":
        A = arb(35)/64; Omega = Omega or 64.0; terms = [(arb(2).log(), arb(2).sqrt()*arb(2).log())]
        NH = NH or 30; h = h or 1/256
    else:
        A = arb(177)/256; Omega = Omega or 128.0
        terms = [(arb(2).log(), arb(2).sqrt()*arb(2).log()), (arb(3).log(), 2*arb(3).log()/arb(3).sqrt())]
        NH = NH or 48; h = h or 1/512
    OmA = arb(Omega); c = A*OmA; c2 = c*c
    delta = float((2*A).mid())
    nmax = 2*(NH + 90) + 40
    log(f"[{kernel}/{parity}] a = {A.str(10)} (delta {delta:.7f}), Omega {Omega}, c = {c.str(8)}; NH+1 = {NH+1}; h = {h}; prec {PREC}")
    ns, pr = verified_pswf(parity, NH, nmax, c2, log)
    n_head = NH + 1
    par0 = 0 if parity == "even" else 1
    NF = [(arb(2*n + 1)/2).sqrt() for n in range(nmax)]
    P0, dP0 = P0_dP0(nmax)
    coefs = []
    for p in pr:
        cv = [arb(0)]*nmax
        for i, n in enumerate(ns):
            cv[n] = p["v"][i]
        coefs.append(cv)
    # (2) mu_k, lambda_k
    normP0 = sum(((P0[n]*NF[n])**2 for n in range(par0, nmax, 2)), arb(0)).sqrt()
    normdP0 = sum(((dP0[n]*NF[n])**2 for n in range(par0, nmax, 2)), arb(0)).sqrt()
    lam = []; mu = []; kstar = None
    for k, p in enumerate(pr):
        eps = arb(0, p["eps"])
        # the Legendre tail n >= nmax of the TRUE prolate (F286-5): geometric decay from
        # the diagonally dominant tail block; |NF_n P_n(0)| <= 1 (even) and
        # |NF_n P_n'(0)| <= 2n (odd, n >= 1) bound the basis values
        # every factor a ball (round 287 F287-4); the j-th tail coefficient (j >= 1)
        # has Legendre degree L + 2(j-1), so the odd sum is
        # sum_j q^(j-1) 2(L + 2(j-1)) = 2 (L/(1-q) + 2q/(1-q)^2)  (round 287 F287-2)
        q_t = 2*arb(p["e_tail"])/arb(p["d_tail"]); assert float(q_t.lower()) > 0 and float(q_t.upper()) < 1
        beta_last = arb(p["vlast"]) + p["eps"]
        tail_amp = arb(p["e_tail"])*beta_last/(arb(p["d_tail"])*(1 - q_t))      # sum_j |beta_{last+j}| <= tail_amp/(1-q)
        L = p["nlast"]
        tail_even = tail_amp/(1 - q_t)                                           # sum_j |beta| * 1
        tail_odd = tail_amp*2*(arb(L)/(1 - q_t) + 2*q_t/(1 - q_t)**2)            # sum_j |beta| * 2(L + 2(j-1))
        if parity == "even":
            psi0 = sum((coefs[k][n]*NF[n]*P0[n] for n in range(0, nmax, 2)), arb(0)) + eps*normP0 + arb(0, float(tail_even.upper()))
            num = arb(2).sqrt()*(coefs[k][0] + eps)
            mk = None if psi0.contains(arb(0)) else num/psi0
        else:
            dpsi0 = sum((coefs[k][n]*NF[n]*dP0[n] for n in range(1, nmax, 2)), arb(0)) + eps*normdP0 + arb(0, float(tail_odd.upper()))
            num = c*(arb(2)/3).sqrt()*(coefs[k][1] + eps)
            mk = None if dpsi0.contains(arb(0)) else num/dpsi0
        if mk is None or float(mk.rad()) > 0.5*float(abs(mk).upper()):
            kstar = k if kstar is None else kstar
            mu.append(None); lam.append(None)
        else:
            mu.append(mk)
            lk = c*mk*mk/(2*arb.pi())
            lam.append(lk)
    if kstar is None:
        kstar = len(pr)
    lam_star_hi = float(lam[kstar - 1].upper())
    for k in range(kstar, len(pr)):
        lam[k] = arb(lam_star_hi/2, lam_star_hi/2)
    if kstar - 1 < NH + 1:
        # the head is the resolvable prolates only; the tail starts at k*, whose
        # concentration is <= lambda_{k*-1} by monotonicity
        log(f"  head truncated to the resolvable prolates: NH {NH} -> {kstar - 2}")
        NH = kstar - 2; n_head = NH + 1
    log(f"  lambda_0 = {lam[0].str(12, radius=True)}; resolvable through k* = {kstar-1} (lambda ~ {float(lam[kstar-1].upper()):.2e}); lambda_NH+1 <= {float(lam[NH+1].upper()):.2e}  ({time.time()-t0:.0f}s)")
    # (3) Gram, pole vector
    Gam = [[sum((coefs[j][n]*coefs[k][n] for n in range(par0, nmax, 2)), arb(0)) for k in range(n_head)] for j in range(n_head)]
    s_arg = A/2
    inv = [sph_in(n, s_arg) for n in range(nmax)]
    cvec = [A.sqrt()*sum((coefs[k][n]*NF[n]*inv[n]*2 for n in range(par0, nmax, 2)), arb(0)) for k in range(n_head)]
    chi_norm2 = (A.sinh() + A) if parity == "even" else (A.sinh() - A)
    # (4) the band integral by Gauss-Legendre on cells with the analytic error bound
    # round 286 F286-1: the cells must tile [0, 1] EXACTLY -- h is a power of two,
    # so every boundary ci*h and every node/weight scaling is exact in binary
    # (a non-dyadic h left gaps/overlaps of ~1e-16 per boundary, an error term
    # outside the certified chain)
    ncell = int(round(1.0/h)); h = 1.0/ncell
    assert ncell & (ncell - 1) == 0 and ncell*h == 1.0, "cell width must be dyadic (exact tiling)"
    NGL = 30
    roots = [arb.legendre_p_root(NGL, k, weight=True) for k in range(NGL)]
    # global ellipse parameter for the disk radius d covering each cell's local ellipse
    rho = 3.0
    d_disk = (h/2)*(rho + 1/rho)/2
    rho_d = 1 + d_disk + math.sqrt(2*d_disk + d_disk*d_disk)
    # strip check: the local ellipse's semi-minor axis (in x) must be < 1/(2 Omega), and the covering disk must keep Re z > 0
    assert (h/2)*(rho - 1/rho)/2 < 0.5/Omega, "cells too wide for the strip"
    assert Omega*d_disk/2 < 0.25, "covering disk reaches the pole"
    # polynomial sups on the global ellipse: sum |beta_n| NF_n rho_d^n
    Mphi = []
    for k in range(n_head):
        tot = arb(0); rp = arb(1); rd = arb(rho_d)
        for n in range(nmax):
            if n % 2 == par0:
                tot = tot + abs(coefs[k][n])*NF[n]*rp
            rp = rp*rd
        Mphi.append(float(tot.upper()))
    log(f"  cells {ncell} x {NGL} GL nodes; disk radius {d_disk:.2e}, rho_d {rho_d:.5f}, max polynomial sup {max(Mphi):.3e}  ({time.time()-t0:.0f}s)")
    # nodes and values
    nodes = []; weights = []
    for ci in range(ncell):
        xl = ci*h
        for (rt, wt) in roots:
            nodes.append(arb(xl) + (h/2)*(rt + 1)); weights.append(wt*(h/2))
    nn = len(nodes)
    # phi values at nodes: P-matrix (nodes x nmax) times coefficient matrix (nmax x n_head), arb_mat products in C
    Pm = arb_mat(nn, nmax)
    for i, x in enumerate(nodes):
        Pv = legendre_P_at(x, nmax)
        for n in range(nmax):
            Pm[i, n] = Pv[n]*NF[n]
    Cm = arb_mat(nmax, n_head)
    for k in range(n_head):
        for n in range(nmax):
            Cm[n, k] = coefs[k][n]
    Phi = Pm*Cm                                                     # nn x n_head
    Wn = [W_real(OmA*x, terms) for x in nodes]
    log(f"  node values ready: {nn} nodes, phi radius max {max(float(Phi[i, k].rad()) for i in range(nn) for k in range(n_head)):.1e}, W radius max {max(float(w.rad()) for w in Wn):.1e}  ({time.time()-t0:.0f}s)")
    # kernel sups on the covering disks: W_hol on the acb disk (center x_c, radius d_disk) in r-units
    MW = []
    for ci in range(ncell):
        xc = (ci + 0.5)*h
        zr = acb(arb(OmA*arb(xc), float((OmA*arb(d_disk)).upper())), arb(0, float((OmA*arb(d_disk)).upper())))
        MW.append(float(W_hol_acb(zr, terms).abs_upper().upper()))
    M_W_band = max(float(abs(w).upper()) for w in Wn)
    log(f"  kernel disk sups: max {max(MW):.3f}; |W| on the band <= {M_W_band:.4f} (nodes) ({time.time()-t0:.0f}s)")
    # per-cell error factors: (64/15) rho^{-2 NGL}/(rho^2-1) * (h/2) * MW[cell]
    # (assembled in balls, upper endpoints -- round 286 F286-4: the scalar
    # assembly is directed, not round-to-nearest float)
    _ef = (arb(64)/15)*arb(rho)**(-2*NGL)/(arb(rho)*rho - 1)*(arb(h)/2)
    efac = [float((_ef*arb(MW[ci])).upper()) for ci in range(ncell)]
    efac_sum = float(sum((_ef*arb(MW[ci]) for ci in range(ncell)), arb(0)).upper())
    # band integrals I_jk = 2 * sum_nodes w_i phi_j phi_k W  +/- errors
    Wcol = arb_mat(nn, 1)
    for i in range(nn):
        Wcol[i, 0] = Wn[i]*weights[i]
    # I[j][k] = sum_i Phi[i,j] Phi[i,k] Wcol[i]  -> Phi^T diag(Wcol) Phi
    PhiW = arb_mat(nn, n_head)
    for i in range(nn):
        for k in range(n_head):
            PhiW[i, k] = Phi[i, k]*Wcol[i, 0]
    Iband = Phi.transpose()*PhiW
    err_tot = [[float((arb(efac_sum)*arb(Mphi[j])*arb(Mphi[k])).upper()) for k in range(n_head)] for j in range(n_head)]
    log(f"  band integrals: max quadrature error {max(max(r) for r in err_tot):.2e}, I_00 = {(2*Iband[0,0]).str(15, radius=True)}  ({time.time()-t0:.0f}s)")
    # (5) A_in, G, M_head
    # sup |W| on the REAL band: node maximum + M1 * (largest gap between consecutive nodes in r),
    # |W'| <= |psi'(1/4 + ir/2)|/2 + sum w lag <= (16 + pi^2/6)/2 + sum w lag  (the core's dW_majorant argument)
    M1a = (16 + arb.pi()**2/6)/2 + sum((w*lag for lag, w in terms), arb(0))
    M1 = float(M1a.upper())
    xs_up = sorted(float(x.upper()) for x in nodes); xs_lo = sorted(float(x.lower()) for x in nodes)
    max_gap = float((arb(max(max(b - a for a, b in zip(xs_lo[:-1], xs_up[1:])), xs_up[0], 1.0 - xs_lo[-1]))*OmA).upper())
    M_W = float((arb(M_W_band) + M1a*arb(max_gap)).upper())
    log(f"  |W| on the band <= {M_W:.4f} (node max {M_W_band:.4f} + M1 {M1:.2f} x max node gap {max_gap:.2e})")
    W_out = W_real(OmA, []) - sum((w for lag, w in terms), arb(0))
    W_out_lo = float(W_out.lower())
    fac = A*OmA/(2*arb.pi())
    Fnorm = (2*arb.pi()/c).sqrt()
    M_h = acb_mat(n_head, n_head)
    sign = 1 if parity == "even" else -1
    for j in range(n_head):
        for k in range(n_head):
            if mu[j] is None or mu[k] is None:
                lj = float(lam[j].upper()); lk = float(lam[k].upper())
                bnd = M_W*math.sqrt(lj*lk)
                Ain = arb(0, bnd); G = arb(0, math.sqrt(lj*lk)) if j != k else arb(lk/2, lk/2)
            else:
                ej = (Fnorm + abs(mu[j]))*arb(pr[j]["eps"]); ek = (Fnorm + abs(mu[k]))*arb(pr[k]["eps"])
                nj = Gam[j][j].sqrt(); nk = Gam[k][k].sqrt()
                slop = fac*(abs(mu[j])*nj*ek + abs(mu[k])*nk*ej + ej*ek)
                Ib = 2*Iband[j, k] + arb(0, 2*err_tot[j][k])      # the doubled half-integral carries twice the error (round 288 F288-1)
                Ain = fac*mu[j]*mu[k]*Ib + arb(0, M_W)*slop
                G = fac*mu[j]*mu[k]*Gam[j][k] + arb(0, 1)*slop
            M_h[j, k] = acb(Ain + arb(W_out_lo)*(Gam[j][k] - G) + sign*2*cvec[j]*cvec[k])
    # radius diagnostic: the widest entries and their parts
    diag = []
    for j in range(n_head):
        for k in range(j, n_head):
            diag.append((float(M_h[j, k].real.rad()), j, k))
    diag.sort(reverse=True)
    for rad_, j, k in diag[:3]:
        parts = ""
        if mu[j] is not None and mu[k] is not None:
            ej = (Fnorm + abs(mu[j]))*arb(pr[j]["eps"]); ek = (Fnorm + abs(mu[k]))*arb(pr[k]["eps"])
            slop = fac*(abs(mu[j])*Gam[j][j].sqrt()*ek + abs(mu[k])*Gam[k][k].sqrt()*ej + ej*ek)
            parts = (f"mu_j rad {float(mu[j].rad()):.1e} mu_k rad {float(mu[k].rad()):.1e} Iband rad {float(Iband[j,k].rad()):.1e} "
                     f"quad err {err_tot[j][k]:.1e} slop {float(slop.upper()):.1e} Gam rad {float(Gam[j][k].rad()):.1e} cvec rads {float(cvec[j].rad()):.1e},{float(cvec[k].rad()):.1e}")
        log(f"  widest entry ({j},{k}): radius {rad_:.2e} | {parts}")
    # symmetrize (union of the two enclosures)
    for j in range(n_head):
        for k in range(j + 1, n_head):
            u = M_h[j, k].real.union(M_h[k, j].real)
            M_h[j, k] = acb(u); M_h[k, j] = acb(u)
    # rigorous lower bound on lambda_min(M_head): verified Cholesky of M - sigma I in ball
    # arithmetic (all pivots positive  =>  M - sigma I positive definite  =>  lambda_min >= sigma);
    # sigma searched upward from the float minimum eigenvalue minus a margin
    Mr = [[M_h[j, k].real for k in range(n_head)] for j in range(n_head)]
    Mmid = np.array([[float(x.mid()) for x in row] for row in Mr])
    lam_float = float(np.linalg.eigvalsh((Mmid + Mmid.T)/2)[0])
    max_rad = max(float(x.rad()) for row in Mr for x in row)
    def chol_ok(sigma):
        L = [[arb(0)]*n_head for _ in range(n_head)]
        for j in range(n_head):
            sq = Mr[j][j] - sigma - sum((L[j][k]*L[j][k] for k in range(j)), arb(0))
            if not (float(sq.lower()) > 0):
                return False
            L[j][j] = sq.sqrt()
            for i in range(j + 1, n_head):
                L[i][j] = (Mr[i][j] - sigma - sum((L[i][k]*L[j][k] for k in range(j)), arb(0)))/L[j][j]
        return True
    lam_min_M = None; ev_rad = max_rad
    for margin in (2*n_head*max_rad*(1 + 1e-6) + 1e-40, 1e-14, 1e-12, 1e-10, 1e-9, 1e-8, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3):
        sigma = lam_float - margin
        if chol_ok(arb(sigma)):
            lam_min_M = sigma; break
    assert lam_min_M is not None, "no verified positive-definite shift found"
    log(f"  head: float lambda_min {lam_float:+.6e}; verified Cholesky at sigma = lambda_float - {lam_float - lam_min_M:.1e} (max entry radius {max_rad:.1e})")
    # Frobenius norm of Gamma - I in balls (>= the spectral norm), upper endpoint
    normEa = sum(((Gam[j][k] - (1 if j == k else 0))**2 for k in range(n_head) for j in range(n_head)), arb(0)).sqrt()
    normE = float(normEa.upper())
    lam_head = float((arb(lam_min_M)/(1 + normEa)).lower()) if lam_min_M >= 0 else float((arb(lam_min_M)/(1 - normEa)).lower())
    log(f"  lambda_min(M_head) >= {lam_head:.6e} (||Gamma - I|| <= {normE:.1e})  ({time.time()-t0:.0f}s)")
    # (6) tail and coupling -- every scalar a ball, taken at its safe endpoint (F286-4)
    Lam_tail_a = lam[NH + 1] + sum((lam[k]*arb(pr[k]["eps"])**2 for k in range(n_head)), arb(0))
    Lam_tail = float(Lam_tail_a.upper())
    cc = sum((cvec[k]*cvec[k] for k in range(n_head)), arb(0))
    Pperp2_a = chi_norm2 - cc/(1 + normEa)
    Pperp2 = max(0.0, float(Pperp2_a.upper()))
    q_perp = float((arb(W_out_lo)*(1 - arb(Lam_tail)) - arb(M_W)*arb(Lam_tail) - (2*arb(Pperp2) if parity == "odd" else 0)).lower())
    b = float(((arb(M_W) + W_out)*arb(Lam_tail).sqrt() + 2*(chi_norm2*arb(Pperp2)).sqrt()).upper())
    # the 2x2 minimum eigenvalue in ball arithmetic (a float guard factor here would
    # cost ~1e-12 * q_perp, comparable to the two-prime even head's margin)
    lh, qp, bb = arb(lam_head), arb(q_perp), arb(b)
    tr = lh + qp; det = lh*qp - bb*bb
    disc = tr*tr - 4*det
    assert float(disc.lower()) >= 0
    final = float((0.5*(tr - disc.sqrt())).lower())
    verdict = f"THEOREM: positive for every probe at delta = {delta:.7f} ({parity}), hence on [0, {delta:.7f}]" if final > 0 else "NOT CERTIFIED"
    log(f"  tail: Lambda_tail <= {Lam_tail:.2e}, ||P_perp chi||^2 <= {Pperp2:.2e}, q_perp >= {q_perp:.4f}, b <= {b:.2e}")
    log(f"  FINAL LOWER BOUND lambda_min(Q) >= {final:+.6e}  -> {verdict}  ({time.time()-t0:.0f}s)")
    return dict(kernel=kernel, parity=parity, a=float(A.mid()), delta=delta, Omega=Omega, NH=NH, h=h, NGL=NGL, nmax=nmax,
                prec=PREC, lam_head=lam_head, eig_radius=ev_rad, normE=normE, Lam_tail=Lam_tail, Pperp2=Pperp2,
                q_perp=q_perp, b=b, final=final, W_out_lo=W_out_lo, M_W=M_W, max_quad_err=max(max(r) for r in err_tot),
                max_residual=max(p["r"] for p in pr), min_gap=min(p["gap"] for p in pr), max_eps=max(p["eps"] for p in pr),
                kstar=kstar, verdict=verdict)

# ------------------------------------------------ keyed producer (the 1bl landing)
sys.path.insert(0, HERE)
import ckpt_key

DEPS_SM = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("slepian_arb_certificate.py",), HERE))}
KEYFILE = os.path.join(HERE, "slepian_arb_certificate.py")

CELLS = {"one": dict(NH=30, h=1/256, Omega=64.0), "two": dict(NH=48, h=1/512, Omega=128.0)}   # dyadic h (F286-1)

def run(kernel, parity):
    """The certified cell (kernel in one|two, parity in even|odd) at its
    current executable-content key: REUSED from checkpoints/ when the
    producing code and inputs match, else recomputed and saved."""
    cfg = CELLS[kernel]
    params = {"deps": DEPS_SM, "kernel": kernel, "parity": parity, "prec": PREC,
              "NH": cfg["NH"], "h": cfg["h"], "Omega": cfg["Omega"], "round": 1}
    name = f"slepian_mech_{kernel}_{parity}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None:
        return st
    st = certify(kernel, parity, NH=cfg["NH"], h=cfg["h"], Omega=cfg["Omega"])
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    kernel = sys.argv[1] if len(sys.argv) > 1 else "one"
    which = sys.argv[2] if len(sys.argv) > 2 else "both"
    for par in (("even", "odd") if which == "both" else (which,)):
        st = run(kernel, par)
        print(f"{kernel}/{par}: {st['verdict']} (lambda_min >= {st['final']:.6e})", flush=True)
