#!/usr/bin/env python3
"""THE MECHANISM PROOF OVER THE ONE-PRIME WINDOW, STAGE 1 (owner: "Do the
mechanism proof over the one-prime window"): an interval-rigorous LOWER
BOUND on the one-prime semi-local Weil form, uniform over every probe of
support length delta = 2a, by Slepian concentration -- no Temple trial, no
Birman-Schwinger count, no zero.

THE BOUND.  For real g on [-a, a] (parity fixed), ghat its Fourier
transform (type a), the one-prime form is
    Q(g) = (1/2pi) int_R |ghat|^2 W dr  +/-  2 <chi, g>^2,
    W(r) = Re psi(1/4 + ir/2) - log pi - C2 cos(r log 2),
the full functional for every delta < log 3 (Theorem 1bj(i); below log 2
the prime term vanishes on the autocorrelation, so it is the full form
there too).  Fix Omega with W >= W_out := W_inf(Omega) - C2 > 0 on
|r| >= Omega (W_inf = Re psi(1/4 + ir/2) - log pi is increasing in r > 0:
d/dr Re psi(1/4 + ir/2) = -(1/2) Im psi'(1/4 + ir/2) = sum_k r(1/4+k) /
|1/4+k+ir/2|^4 > 0).  Then for EVERY g,
    Q(g) >= <g, M g>,   M := A_in + W_out (I - K) +/- 2 chi chi^T,
A_in the form (1/2pi) int_{|r|<=Omega} |ghat|^2 W dr, K the Slepian
concentration operator of (a, Omega) on L^2[-a,a] (0 <= K <= I; its
eigenfunctions are the prolate spheroidal wave functions psi_k, doubly
orthogonal, K psi_k = lambda_k psi_k with lambda_k decreasing in k).
The proof consists of the numbers below, each an enclosure:
  (1) the first NH+1 prolates of the parity, verified: the Legendre-basis
      tridiagonal matrix of Slepian's commuting differential operator
      L = -d/dx(1-x^2)d/dx + c^2 x^2 (c = a Omega, EXACT here: a = 35/64,
      Omega = 64, c = 35), float eigenpairs, then for each k a rigorous
      residual r_k = ||(L - chi_k) v_k||, a rigorous Sturm count locating
      exactly one true eigenvalue in [chi_k - r_k, chi_k + r_k] and none
      between neighbours (the tail beyond the truncation is strictly
      diagonally dominant, so the count of the infinite operator equals
      the truncated count with the last pivot widened by the Schur bound),
      and the eigenvector bound eps_k = sqrt2 r_k / gap_k on
      ||psi_k - phi_k|| (phi_k := the float vector, an explicit
      polynomial, exactly as stored);
  (2) lambda_k = (c/2pi) |mu_k|^2 through the finite-Fourier eigen-
      relation  int_{-1}^{1} e^{icxy} psi_k(y) dy = mu_k psi_k(x)  at x = 0
      (even: mu = sqrt2 beta_0/psi(0); odd: |mu| = c sqrt(2/3) |beta_1| /
      |psi'(0)|), with eps_k propagated; beyond the resolvable range the
      monotone bound lambda_k <= lambda_{k*};
  (3) the head matrix in the explicit basis {phi_k}: the exact Gram
      Gamma = beta_j . beta_k; the band form A_in(j,k) = (a Omega mu_j
      mu_k / 2pi) int_{-1}^{1} phi_j phi_k W(Omega x) dx + the eigen-
      relation's residual bound; the concentration Gram G(j,k) = (a Omega
      mu_j mu_k/2pi) Gamma_jk + residual; the pole vector c_k = <chi,
      phi_k> by the modified spherical Bessel closed form  int_{-1}^{1}
      P_n(x) e^{sx} dx = 2 i_n(s); the band integral by Simpson on cells
      with the rigorous error (h^5/2880) sup|f''''| from interval Clenshaw
      hulls of phi^{(l)} on each cell and the kernel's derivative
      majorants M1..M4; W at the nodes by the committed W_batch;
  (4) M_head = A_in + W_out (Gamma - G) +/- 2 c c^T; lambda_min of the
      pencil (M_head, Gamma) from the verified eigensolver veigs;
  (5) the tail: for f orthogonal to the head, <f, K f> <= Lambda_tail :=
      lambda_{NH+1} + sum_{k<=NH} lambda_k eps_k^2, hence <f, M f> >=
      q_perp ||f||^2 with q_perp = W_out (1 - Lambda_tail) - M_W Lambda_tail
      - [odd] 2 ||P_perp chi||^2; the coupling |<g_n, M f>| <= b ||g_n|| ||f||
      with b = (M_W + W_out) sqrt(Lambda_tail) + 2 ||chi|| ||P_perp chi||;
  (6) lambda_min(M) >= lambda_min([[lambda_min(M_head, Gamma), -b], [-b, q_perp]]).
If the final number is > 0:  THEOREM.  The one-prime form is positive at
support length 2a in this parity for every probe, and by domain nesting at
every shorter support length -- i.e. Weil's full functional is positive on
[0, 2a] in this sector.

Usage: oneprime_slepian_certificate.py [even|odd|both] [NH=30] [h=1e-4]
Checks 7/8 clean: Slepian's theorems, the explicit formula, IEEE-754
intervals -- classical; no hypothesis input.  No RH consequence is claimed.
"""
import sys, os, math, time, json
import numpy as np
sys.path.insert(0, '/home/user/r-infinite/tools/research')
from oneprime_interval_core import (I, PI, TWO_PI, LOG2, LOGPI, C2I, _u, _d, iexp,
                                    repsi_quarter, W_enclose, dW_majorant, d2W_majorant)
from oneprime_interval_count import V, vup, vdn, W_batch, M3_majorant, M4_majorant, veigs
from scipy.linalg import eigh_tridiagonal

# ------------------------------------------------------------------ cell
A_NUM, A_DEN = 35, 64
A = A_NUM/A_DEN                      # 0.546875 exactly
AI = I(A)                            # exact
OMEGA = 64.0
CC = 35                              # c = a Omega exactly
CI = I(float(CC))
DELTA = 2*A                          # 1.09375 < log 3

def sqsum_I(v):
    s = I(0.0)
    for x in v:
        s = s + I(float(x)).sq()
    return s

# ------------------------------------------------------- (1) verified PSWFs
def tridiag_I(parity, nmax):
    """Interval entries of Slepian's differential operator in the
    normalized-Legendre basis, restricted to the parity: diag d_n and
    off-diagonal e_n (coupling n <-> n+2), n = parity, parity+2, ..."""
    ns = list(range(0 if parity == "even" else 1, nmax, 2))
    c2 = CI.sq()
    d = []; e = []
    for n in ns:
        nI = I(float(n))
        d.append(nI*(nI + 1) + c2*(nI.sq()*2 + nI*2 - 1)/((nI*2 + 3)*(nI*2 - 1)))
    for n in ns[:-1]:
        nI = I(float(n))
        e.append(c2*(nI + 2)*(nI + 1)/((nI*2 + 3)*((nI*2 + 1)*(nI*2 + 5)).sqrt()))
    return ns, d, e

def sturm_count(d, e, x, tail_widen):
    """Number of eigenvalues < x of the symmetric tridiagonal with interval
    entries (d, e), the LAST diagonal entry widened downward by tail_widen
    (the Schur bound for the infinite tail).  Returns (count, definite)."""
    n = len(d)
    cnt = 0
    p = None
    for i in range(n):
        di = d[i] - I(x)
        if i == n - 1:
            di = I(di.lo - tail_widen, di.hi)
        if i == 0:
            piv = di
        else:
            if p.contains(0.0):
                return cnt, False
            piv = di - e[i - 1].sq()/p
        if piv.contains(0.0):
            return cnt, False
        if piv.hi < 0:
            cnt += 1
        p = piv
    return cnt, True

def verified_pswf(parity, NH, nmax):
    """Float eigenpairs of the truncated tridiagonal, then rigorous
    residuals, Sturm-located eigenvalues, gaps, and eps_k."""
    ns, d, e = tridiag_I(parity, nmax)
    dm = np.array([x.mid for x in d]); em = np.array([x.mid for x in e])
    chi, Vv = eigh_tridiagonal(dm, em)
    m = len(ns)
    # Schur widening of the last pivot by the infinite tail beyond nmax:
    # the coupling e_last (index ns[-1] <-> ns[-1]+2) squared over the tail
    # block's smallest possible pivot (diagonal dominance: d_n - x - 2|e|)
    nlast = ns[-1] + 2
    nI = I(float(nlast))
    e_tail = CI.sq()*(nI)*(nI - 1)/((nI*2 - 1)*((nI*2 - 3)*(nI*2 + 1)).sqrt())   # e_{ns[-1]}
    K = NH + 3                                       # head + the first three beyond (the last one only brackets the gap)
    x_max = float(chi[K]) + 100.0                    # every Sturm test point lies below this
    d_tail_min = float((nI*(nI + 1)).lo) - 2*float(e_tail.hi) - x_max
    assert d_tail_min > 0, "truncation too short for the eigenvalue range"
    tail_widen = _u(float(e_tail.sq().hi)/d_tail_min)
    out = []
    for k in range(K):
        v = Vv[:, k]
        # rigorous residual of (L - chi_k) v with v exactly the float vector
        res = []
        for i in range(m):
            t = (d[i] - I(float(chi[k])))*I(float(v[i]))
            if i > 0:
                t = t + e[i - 1]*I(float(v[i - 1]))
            if i < m - 1:
                t = t + e[i]*I(float(v[i + 1]))
            res.append(t)
        # plus the tail coupling of the padded vector: e_tail * v[-1]
        r2 = sqsum_I([0.0])  # placeholder
        s = I(0.0)
        for t in res:
            s = s + t.sq()
        s = s + (e_tail*I(float(v[-1]))).sq()
        nv = sqsum_I(v)
        r_k = _u((s.sqrt()/nv.sqrt()).hi)
        out.append(dict(k=k, chi=float(chi[k]), v=v/np.sqrt(float(nv.mid)) if False else v, r=r_k))
    # Sturm counts: exactly one true eigenvalue in [chi_k - r_k, chi_k + r_k]
    # and none strictly between consecutive brackets
    for k in range(K):
        # a bracket wide enough for definite pivots (the residual r_k ~ 1e-12
        # is far inside the float eigenvalue's own rounding); the Sturm
        # count certifies exactly one true eigenvalue in the bracket, and the
        # residual then locates it within r_k
        Dk = max(out[k]["r"], 1e-7*(1.0 + abs(out[k]["chi"])))
        done = False
        for _ in range(8):
            lo, hi = out[k]["chi"] - Dk, out[k]["chi"] + Dk
            c1, ok1 = sturm_count(d, e, lo, tail_widen); c2, ok2 = sturm_count(d, e, hi, tail_widen)
            if ok1 and ok2:
                assert c1 == k and c2 == k + 1, f"Sturm count at k={k}: {c1},{c2} (bracket {Dk:.1e})"
                done = True; break
            Dk *= 10.0
        assert done, f"Sturm pivots indefinite at k={k}"
        out[k]["D"] = Dk
    # gaps and eps
    for k in range(K - 1):
        # gap from chi_k's bracket to the neighbouring certified brackets (the
        # Sturm counts certify exactly one true eigenvalue per bracket and
        # none between consecutive brackets, so the nearest other true
        # eigenvalue lies outside the neighbours' brackets)
        gaps = []
        if k > 0: gaps.append(out[k]["chi"] - out[k]["D"] - (out[k-1]["chi"] + out[k-1]["D"]))
        gaps.append(out[k+1]["chi"] - out[k+1]["D"] - (out[k]["chi"] + out[k]["D"]))
        gap = min(gaps); assert gap > 0
        out[k]["gap"] = gap
        # ||v/||v|| - psi|| <= sqrt2 r/gap; the stored float vector differs from v/||v|| by |1 - ||v|||
        nv = math.sqrt(sum(float(x)*float(x) for x in out[k]["v"]))
        out[k]["eps"] = _u(math.sqrt(2.0)*out[k]["r"]/gap + abs(1.0 - nv)*(1 + 1e-12) + 1e-15)
    return ns, out[:K - 1]

# ------------------------------------------------ Legendre-series tools (I/V)
def legendre_P0_dP0(nmax):
    """P_n(0) and P_n'(0) exact rationals as intervals, n < nmax."""
    P0 = [I(1.0), I(0.0)]; dP0 = [I(0.0), I(1.0)]
    for n in range(1, nmax - 1):
        # (n+1) P_{n+1}(x) = (2n+1) x P_n(x) - n P_{n-1}(x): at x = 0
        P0.append((-I(float(n))*P0[n - 1])/I(float(n + 1)))
        # derivative at 0: (n+1) P'_{n+1}(0) = (2n+1) P_n(0) - n P'_{n-1}(0)
        dP0.append((I(float(2*n + 1))*P0[n] - I(float(n))*dP0[n - 1])/I(float(n + 1)))
    return P0[:nmax], dP0[:nmax]

def norm_factors(nmax):
    return [(I(float(2*n + 1))/2).sqrt() for n in range(nmax)]

def legder_I(coef):
    """Legendre coefficients (unnormalized P_n basis, intervals) of the
    derivative of sum coef_n P_n: c'_n = (2n+1) sum_{m > n, m-n odd} coef_m."""
    nmax = len(coef)
    out = [I(0.0)]*nmax
    for n in range(nmax - 1):
        s = I(0.0)
        for mm in range(n + 1, nmax, 2):
            s = s + coef[mm]
        out[n] = I(float(2*n + 1))*s
    return out

U_EPS = 2.0**-53

def clenshaw_running(coef_mid, coef_rad, x):
    """sum_n coef_n P_n(x) at float points x (numpy array), coefficients
    given as midpoints + radii (intervals), by FLOAT Clenshaw with a
    rigorous running error bound: the computed value differs from the exact
    sum for the midpoint coefficients by at most  u * sum_k ( |c_k| +
    2|alpha_k x b_{k+1}| + 2|beta_{k+1} b_{k+2}| ) + 3u|y|  (every rounding
    written as an additive perturbation eta_k of the coefficient c_k, and
    |sum eta_k P_k(x)| <= sum |eta_k| since |P_k| <= 1 on [-1,1]), plus the
    coefficient radii sum (|P_k| <= 1).  Returns (value, error) arrays."""
    n = len(coef_mid); npts = len(x)
    b1 = np.zeros(npts); b2 = np.zeros(npts); acc = np.zeros(npts)
    for k in range(n - 1, 0, -1):
        alpha = (2*k + 1)/(k + 1); beta = (k + 1)/(k + 2)
        t1 = alpha*x*b1; t2 = beta*b2
        b0 = coef_mid[k] + t1 - t2
        acc += abs(coef_mid[k]) + 2*np.abs(t1) + 2*np.abs(t2)
        b2, b1 = b1, b0
    y = coef_mid[0] + x*b1 - 0.5*b2
    acc += abs(coef_mid[0]) + 2*np.abs(x*b1) + 2*np.abs(0.5*b2) + 3*np.abs(y)
    err = vup(U_EPS*acc*(1 + 1e-10) + float(np.sum(coef_rad)))
    return y, err

def markov_sup(coef_mid, coef_rad, l):
    """sup_{[-1,1]} |sum c_n P_n^{(l)}| <= sum |c_n| P_n^{(l)}(1),
    P_n^{(l)}(1) = (n+l)! / (2^l l! (n-l)!)  (Markov: the extremum at the endpoint)."""
    tot = I(0.0)
    for n in range(len(coef_mid)):
        cn = abs(coef_mid[n]) + coef_rad[n]
        if cn == 0.0 or n < l:
            continue
        pl = I(1.0)
        for j in range(1, l + 1):
            pl = pl*I(float(n + j))*I(float(n - j + 1))/(I(2.0)*I(float(j)))
        tot = tot + I(cn)*pl
    return tot.hi

# ---------------------------------------------- modified spherical Bessel i_n
def sph_in_I(n, s, terms=40):
    """i_n(s) = sum_m s^{n+2m} / (2^m m! (2n+2m+1)!!) for small s > 0,
    with a rigorous geometric tail bound."""
    sI = I(float(s))
    tot = I(0.0)
    term = None
    # first term s^n/(2n+1)!!
    dfac = I(1.0)
    for j in range(1, 2*n + 2, 2):
        dfac = dfac*I(float(j))
    sn = I(1.0)
    for _ in range(n):
        sn = sn*sI
    term = sn/dfac
    tot = term
    for m_ in range(1, terms):
        term = term*sI.sq()/(I(float(2*m_))*I(float(2*n + 2*m_ + 1)))
        tot = tot + term
    # tail: ratio of consecutive terms <= s^2/(2 terms (2n+2terms+1)) < 1/2 here
    ratio = (sI.sq()/(I(float(2*terms))*I(float(2*n + 2*terms + 1)))).hi
    assert ratio < 0.5
    tail = _u(term.abs_hi()*ratio/(1 - ratio))
    return tot + I(-tail, tail)

def kernel_majorants_cells(r_lo, r_hi, K=40):
    """Per-cell majorants |W^{(m)}(r)| <= (m!/2^m) sum_k |1/4+k+ir/2|^{-(m+1)}
    + C2 log^m 2 on r in [r_lo, r_hi] (r >= 0): the sum's first K terms
    with the smallest |r| of the cell (monotone decreasing in r) plus the
    integral tail  int_K^inf (1/4+t)^{-(m+1)} dt = (1/4+K)^{-m}/m."""
    r0 = np.asarray(r_lo, float)
    out = []
    L2 = float(LOG2.hi)
    fact = [1, 1, 2, 6, 24]
    for m in range(1, 5):
        ssum = np.zeros_like(r0)
        for k in range(K):
            ssum = ssum + ((0.25 + k)**2 + r0*r0/4.0)**(-(m + 1)/2.0)
        tail = (0.25 + K)**(-m)/m
        out.append(vup((fact[m]/2.0**m)*(ssum*(1 + 1e-14) + tail) + C2I.hi*L2**m))
    return out   # [M1(cells), M2, M3, M4]

# ----------------------------------------- a tighter kernel enclosure (Stirling)
BERN = [(1, 6), (-1, 30), (1, 42), (-1, 30), (5, 66), (-691, 2730), (7, 6), (-3617, 510),
        (43867, 798), (-174611, 330), (854513, 138)]        # B_2 .. B_22 exact
XMIN_S = 25.0

def repsi_stirling_V(r, K=10):
    """Vectorized rigorous enclosure of Re psi(1/4 + i r/2), r >= 0, tighter
    than the core's Binet-grid route.  Shift: psi(z0) = psi(z0 + n) -
    sum_{k<n} 1/(z0 + k) with n chosen so x = 1/4 + n >= XMIN_S and x >=
    sqrt2 y (as the core does).  For z = x + iy (x >= 25) use Binet's second
    formula  psi(z) = ln z - 1/(2z) - 2 int_0^inf t /((t^2 + z^2)(e^{2 pi t} - 1)) dt
    (Re z > 0) and expand  1/(t^2 + z^2) = sum_{k=0}^{K-1} (-1)^k t^{2k} z^{-2k-2}
    + (-1)^K t^{2K} / (z^{2K} (t^2 + z^2));  with  int_0^inf t^{2k+1}/(e^{2 pi t}-1) dt
    = (-1)^k B_{2k+2} / (4(k+1))  this gives the Stirling terms
    - sum_{k=1}^{K} B_{2k} / (2k z^{2k})  and the remainder
    R_K = (-1)^K 2 int t^{2K+1} / ((t^2+z^2) z^{2K} (e^{2 pi t}-1)) dt,
    |R_K| <= 2 |B_{2K+2}| / (4(K+1)) / (|z|^{2K} d_z),  d_z = min_{t>=0} |t^2 + z^2|
    >= min(|z|^2, 2xy)  (|t^2+z^2|^2 = (t^2+x^2-y^2)^2 + 4x^2y^2).  All
    arithmetic in V intervals; Re z^{-2k} by complex interval powers."""
    r = np.asarray(r, np.float64); npts = len(r)
    y = V.point(r)*V.scalar(0.5, npts)
    yh = np.maximum(np.abs(y.lo), np.abs(y.hi))
    nshift = np.maximum(math.ceil(XMIN_S - 0.25), np.ceil(1.4142135623730951*yh - 0.25).astype(int) + 1)
    nmax = int(nshift.max())
    x = V.point(0.25 + nshift.astype(np.float64))
    y2 = y.sq()
    ssum = V(np.zeros(npts), np.zeros(npts))
    for k in range(nmax):
        mask = k < nshift
        ak = V.point(np.full(npts, 0.25 + k))
        contrib = ak.divpos(ak.sq() + y2)
        ssum = V(np.where(mask, vdn(ssum.lo + contrib.lo), ssum.lo), np.where(mask, vup(ssum.hi + contrib.hi), ssum.hi))
    modz2 = x.sq() + y2
    relog = _vlog_local(modz2)*V.scalar(0.5, npts)              # Re ln z = (1/2) ln |z|^2
    re_inv2z = x.divpos(modz2*V.scalar(2.0, npts))              # Re 1/(2z) = x/(2|z|^2)
    # z^{-2} = (x - iy)^2 / |z|^4  ->  re = (x^2 - y^2)/|z|^4, im = -2xy/|z|^4
    m4 = modz2.sq()
    w_re = (x.sq() - y2).divpos(m4); w_im = -(x*y*V.scalar(2.0, npts)).divpos(m4)
    p_re, p_im = w_re, w_im                                     # z^{-2k}, k = 1
    stirl = V(np.zeros(npts), np.zeros(npts))
    for k in range(1, K + 1):
        num, den = BERN[k - 1]
        coef = I(float(num))/(I(float(den))*I(float(2*k)))         # B_{2k}/(2k)
        stirl = stirl + V.scalar(coef, npts)*p_re
        # next power z^{-2(k+1)} = z^{-2k} * z^{-2}
        n_re = p_re*w_re - p_im*w_im; n_im = p_re*w_im + p_im*w_re
        p_re, p_im = n_re, n_im
    num, den = BERN[K]                                           # B_{2K+2}
    b2k2 = abs(num)/den
    dz = np.minimum(modz2.lo, 2.0*x.lo*np.maximum(y.lo, 0.0))
    dz = np.where(y.lo <= 0, modz2.lo, dz)
    zpow = modz2.lo**K                                           # |z|^{2K}
    rem = vup(2*b2k2/(4*(K + 1))/(zpow*dz)*(1 + 1e-12))
    res = relog - re_inv2z - stirl - ssum
    return V(vdn(res.lo - rem), vup(res.hi + rem))

def _vlog_local(x):
    from oneprime_interval_core import _log_pt
    lo = np.empty_like(x.lo); hi = np.empty_like(x.hi)
    for i in range(len(x.lo)):
        lo[i] = _log_pt(x.lo[i], -1); hi[i] = _log_pt(x.hi[i], +1)
    return V(lo, hi)

def W_tight(r):
    """W(r) = Re psi(1/4 + ir/2) - log pi - C2 cos(r log 2) with the Stirling enclosure."""
    from oneprime_interval_count import vcos
    r = np.asarray(r, np.float64); npts = len(r)
    return repsi_stirling_V(r) - V.scalar(LOGPI, npts) - V.scalar(C2I, npts)*vcos(V.point(r)*V.scalar(LOG2, npts))

# --------------------------------------------------------------- the proof
def certify(parity, NH=30, h=1e-4, verbose=True):
    t0 = time.time()
    nmax = 2*(NH + 70) + 40
    ns, pr = verified_pswf(parity, NH, nmax)
    nl = len(ns)
    log = lambda *a: print(*a, flush=True) if verbose else None
    log(f"[{parity}] a = {A} (delta {DELTA}), Omega {OMEGA}, c {CC}; Legendre indices {nl} (n < {nmax}); chi range [{pr[0]['chi']:.2f}, {pr[-1]['chi']:.2f}]; "
        f"head NH+1 = {NH+1}; max residual {max(p['r'] for p in pr):.2e}, min gap {min(p['gap'] for p in pr):.2f}, "
        f"max eps {max(p['eps'] for p in pr):.2e}  ({time.time()-t0:.0f}s)")
    # full-length coefficient vectors (normalized Legendre) as intervals: the float vectors, exactly
    NF = norm_factors(nmax)
    P0, dP0 = legendre_P0_dP0(nmax)
    par0 = 0 if parity == "even" else 1
    coefs = []      # per k: list over n < nmax of I (normalized-Legendre coefficients), zeros off-parity
    for p in pr:
        cv = [I(0.0)]*nmax
        for i, n in enumerate(ns):
            cv[n] = I(float(p["v"][i]))
        coefs.append(cv)
    # ---- (2) mu_k, lambda_k
    normP0 = math.sqrt(sum(float((P0[n]*NF[n]).sq().hi) for n in range(par0, nmax, 2)))
    normdP0 = math.sqrt(sum(float((dP0[n]*NF[n]).sq().hi) for n in range(par0, nmax, 2)))
    lam = []; mu = []
    kstar = None
    for k, p in enumerate(pr):
        eps = p["eps"]
        if parity == "even":
            psi0 = sum((coefs[k][n]*NF[n]*P0[n] for n in range(0, nmax, 2)), I(0.0))
            psi0 = psi0 + I(-eps*normP0, eps*normP0)
            num = I(math.sqrt(2.0))*(coefs[k][0] + I(-eps, eps))          # int psi = sqrt2 beta_0
            mk = None if psi0.contains(0.0) else num/psi0
        else:
            dpsi0 = sum((coefs[k][n]*NF[n]*dP0[n] for n in range(1, nmax, 2)), I(0.0))
            dpsi0 = dpsi0 + I(-eps*normdP0, eps*normdP0)
            num = CI*I(math.sqrt(2.0/3.0))*(coefs[k][1] + I(-eps, eps))    # |mu| psi'(0) = c sqrt(2/3) |beta_1|
            mk = None if dpsi0.contains(0.0) else num/dpsi0
        if mk is None or (mk.abs_hi() > 0 and mk.width/mk.abs_hi() > 0.5):
            kstar = k if kstar is None else kstar
            mu.append(None); lam.append(None)
        else:
            mu.append(mk)
            lk = CI*mk.sq()/TWO_PI
            lam.append(I(max(0.0, lk.lo), min(1.0, lk.hi)))
    if kstar is None:
        kstar = len(pr)
    lam_star = lam[kstar - 1]        # monotone: lambda_k <= lambda_{k*-1} for k >= k*
    for k in range(kstar, len(pr)):
        lam[k] = I(0.0, lam_star.hi)
    log(f"  lambda_0 = [{lam[0].lo:.6f}, {lam[0].hi:.6f}]; resolvable through k* = {kstar-1} (lambda = {lam_star.hi:.2e}); "
        f"lambda_NH+1 <= {lam[NH+1].hi:.2e}")
    # ---- (3) head matrices
    n_head = NH + 1
    # exact Gram of the float vectors
    Gam = [[sum((coefs[j][n]*coefs[k][n] for n in range(par0, nmax, 2)), I(0.0)) for k in range(n_head)] for j in range(n_head)]
    # pole vector: c_k = <chi, phi_k>, phi_k(t) = psi_k(t/a)/sqrt(a):
    # int_{-a}^{a} phi_k chi dt = sqrt(a) sum_n beta_kn NF_n int_{-1}^{1} P_n(x) chi(a x) dx,
    # chi(ax) = cosh(ax/2) or sinh(ax/2): int P_n cosh(sx) = 2 i_n(s) (n even), int P_n sinh(sx) = 2 i_n(s) (n odd), s = a/2
    s_arg = A/2
    inv = [sph_in_I(n, s_arg) for n in range(nmax)]
    cvec = [AI.sqrt()*sum((coefs[k][n]*NF[n]*inv[n]*2 for n in range(par0, nmax, 2)), I(0.0)) for k in range(n_head)]
    from oneprime_interval_core import isinh
    sh = isinh(AI)                                              # rigorous sinh(a)
    chi_norm2 = (sh + AI) if parity == "even" else (sh - AI)    # int_{-a}^{a} chi^2 = sinh a +/- a
    # ---- band integral I_jk = int_{-1}^{1} phi_j phi_k W(Omega x) dx  (even integrand: 2 int_0^1)
    ncell = int(round(1.0/h)); h = 1.0/ncell
    xl = np.arange(ncell)*h; xr = xl + h; xm = xl + 0.5*h
    # phi values at nodes (point intervals) and derivative hulls on cells
    node_x = np.concatenate([xl, xm, np.array([1.0])])       # left nodes, midpoints, and the final right node
    nL = ncell
    # unnormalized-P_n coefficient vectors (fold NF in) and their derivative series (interval)
    Cu = []; Cd = []
    for k in range(n_head):
        cu = [coefs[k][n]*NF[n] for n in range(nmax)]
        Cu.append(cu)
        ders = [cu]
        for l in range(5):
            ders.append(legder_I(ders[-1]))
        Cd.append(ders)
    log(f"  coefficient vectors and derivative series ready ({time.time()-t0:.0f}s)")
    def mid_rad(cv):
        return np.array([c.mid for c in cv]), np.array([0.5*c.width for c in cv])
    # node values (float Clenshaw + running error) for phi_k and phi_k^{(l)}, l <= 4
    vals = []; verr = []; dvals = []; derr = []
    for k in range(n_head):
        mval, mrad = mid_rad(Cu[k]); y, e = clenshaw_running(mval, mrad, node_x); vals.append(y); verr.append(e)
        dv = []; de = []
        for l in range(1, 5):
            mval, mrad = mid_rad(Cd[k][l]); yl, el = clenshaw_running(mval, mrad, node_x); dv.append(yl); de.append(el)
        dvals.append(dv); derr.append(de)
    # cell sup bounds of |phi_k^{(l)}|, l = 0..4: max over the cell's three nodes + (h/2) sup|phi^{(l+1)}| (the top order by Markov)
    sup5 = [markov_sup(*mid_rad(Cd[k][5]), 0) for k in range(n_head)]     # sup |phi^{(5)}| via its own series' Markov bound at l = 0
    def cell_sup(k, l):
        arr = vals[k] if l == 0 else dvals[k][l - 1]; er = verr[k] if l == 0 else derr[k][l - 1]
        nodes_abs = np.abs(arr) + er
        m3 = np.maximum(np.maximum(nodes_abs[:nL], nodes_abs[nL:2*nL]), np.concatenate([nodes_abs[1:nL], [nodes_abs[2*nL]]]))
        nxt = (np.abs(dvals[k][l]) + derr[k][l]) if l < 4 else None
        if l < 4:
            nxt_cell = np.maximum(np.maximum(nxt[:nL], nxt[nL:2*nL]), np.concatenate([nxt[1:nL], [nxt[2*nL]]]))
            # sup on the cell <= max at the three nodes + (h/2) * sup|next|, sup|next| <= node max + (h/2) sup|next2| ... (two levels, then Markov)
            return vup(m3 + 0.5*h*(nxt_cell + 0.5*h*(sup5[k] if l == 3 else 1e300*0 + _cell_sup_next2(k, l))))
        return vup(m3 + 0.5*h*sup5[k])
    def _cell_sup_next2(k, l):
        # sup of |phi^{(l+2)}| on the cell: node max + (h/2) * Markov sup of the (l+3)-th derivative series
        arr = dvals[k][l + 1]; er = derr[k][l + 1]
        na = np.abs(arr) + er
        m3 = np.maximum(np.maximum(na[:nL], na[nL:2*nL]), np.concatenate([na[1:nL], [na[2*nL]]]))
        return vup(m3 + 0.5*h*markov_sup(*mid_rad(Cd[k][l + 3]), 0))
    hulls = [[cell_sup(k, l) for l in range(5)] for k in range(n_head)]
    log(f"  node values and cell sup bounds ready ({time.time()-t0:.0f}s)")
    Wn = W_tight(OMEGA*node_x)                                               # W(Omega x) at the nodes (Stirling enclosure)
    Wchk = W_batch(OMEGA*node_x[::997])                                        # cross-check against the committed enclosure at a few nodes
    assert np.all(Wn.lo[::997] <= Wchk.hi) and np.all(Wn.hi[::997] >= Wchk.lo), 'tight kernel disagrees with W_batch'
    log(f'  kernel enclosure: Stirling width max {np.max(Wn.width):.2e} (committed W_batch width max {np.max(Wchk.width):.2e} on the check nodes)')
    Mcell = kernel_majorants_cells(OMEGA*xl, OMEGA*xr)                       # per-cell M1..M4 in r
    M1g = dW_majorant(OMEGA)
    M_W = max(float(np.max(np.abs(Wn.lo))), float(np.max(np.abs(Wn.hi))))
    M_W = _u(M_W + M1g*OMEGA*h)                                              # sup over the band: node values + Lipschitz
    nL = ncell
    Vl = [V(vals[k][:nL] - verr[k][:nL], vals[k][:nL] + verr[k][:nL]) for k in range(n_head)]
    Vm = [V(vals[k][nL:2*nL] - verr[k][nL:2*nL], vals[k][nL:2*nL] + verr[k][nL:2*nL]) for k in range(n_head)]
    jr = np.concatenate([np.arange(1, nL), [2*nL]])
    Vr = [V(vals[k][jr] - verr[k][jr], vals[k][jr] + verr[k][jr]) for k in range(n_head)]
    Wl, Wm, Wr = Wn[np.arange(nL)], Wn[nL + np.arange(nL)], V(Wn.lo[jr], Wn.hi[jr])
    hV = V.scalar(I(h), nL)
    Mw_cells = [np.full(nL, M_W)] + [Mcell[0], Mcell[1], Mcell[2], Mcell[3]]  # index m -> |W~^{(m)}| <= Omega^m Mw_cells[m]
    def band_integral(j, k):
        fl = Vl[j]*Vl[k]*Wl; fm = Vm[j]*Vm[k]*Wm; fr = Vr[j]*Vr[k]*Wr
        simpson = (fl + fm*V.scalar(I(4.0), nL) + fr)*hV*V.scalar(I(1.0)/6, nL)
        binom = [[1], [1, 1], [1, 2, 1], [1, 3, 3, 1], [1, 4, 6, 4, 1]]
        err = np.zeros(nL)
        for i in range(5):
            Pi = np.zeros(nL)
            for l in range(i + 1):
                Pi = Pi + binom[i][l]*hulls[j][l]*hulls[k][i - l]
            err = err + binom[4][i]*Pi*(OMEGA**(4 - i))*Mw_cells[4 - i]
        err = vup(err*(h**5/2880.0)*(1 + 1e-12))
        lo = math.fsum(vdn(simpson.lo - err)); hi = math.fsum(vup(simpson.hi + err))
        return I(_d(2*lo), _u(2*hi))
    Iband = [[None]*n_head for _ in range(n_head)]
    for j in range(n_head):
        for k in range(j, n_head):
            Iband[j][k] = Iband[k][j] = band_integral(j, k)
    log(f"  band integrals done, width of I_00 {Iband[0][0].width:.2e} ({time.time()-t0:.0f}s)")
    # A_in and G with the eigen-relation and its residual: F_c phi_k = mu_k phi_k + eta_k, ||eta_k||_2 <= (sqrt(2pi/c) + |mu_k|) eps_k
    fac = AI*I(OMEGA)/TWO_PI
    A_in = [[None]*n_head for _ in range(n_head)]; G = [[None]*n_head for _ in range(n_head)]
    Fnorm = (TWO_PI/CI).sqrt()
    for j in range(n_head):
        for k in range(n_head):
            if mu[j] is None or mu[k] is None:
                lj = lam[j].hi; lk = lam[k].hi
                bnd = _u(M_W*math.sqrt(lj*lk))
                A_in[j][k] = I(-bnd, bnd); G[j][k] = I(-math.sqrt(lj*lk), math.sqrt(lj*lk)) if j != k else I(0.0, lk)
                continue
            ej = (Fnorm + mu[j].abs_hi())*pr[j]["eps"]; ek = (Fnorm + mu[k].abs_hi())*pr[k]["eps"]
            nj = Gam[j][j].sqrt(); nk = Gam[k][k].sqrt()
            slop = fac*(mu[j].abs_hi()*nj*ek + mu[k].abs_hi()*nk*ej + ej*ek)
            A_in[j][k] = fac*mu[j]*mu[k]*Iband[j][k] + I(-M_W, M_W)*slop
            G[j][k] = fac*mu[j]*mu[k]*Gam[j][k] + I(-1.0, 1.0)*slop
    sign = 1.0 if parity == "even" else -1.0
    W_out = repsi_quarter(I(OMEGA)) - LOGPI - C2I
    W_out_lo = W_out.lo
    log(f"  W_out >= {W_out_lo:.4f}; M_W <= {M_W:.4f}")
    Mh = [[A_in[j][k] + I(W_out_lo)*(Gam[j][k] - G[j][k]) + I(sign*2.0)*cvec[j]*cvec[k] for k in range(n_head)] for j in range(n_head)]
    # ---- (4) lambda_min of the pencil (Mh, Gam): Gam = I + E with ||E|| small -> use veigs on Mh and correct
    lo_m = np.array([[x.lo for x in row] for row in Mh]); hi_m = np.array([[x.hi for x in row] for row in Mh])
    lo_m = np.minimum(lo_m, lo_m.T); hi_m = np.maximum(hi_m, hi_m.T)
    dvals, rho = veigs((lo_m, hi_m))
    lam_min_M = _d(float(dvals[-1]) - rho)
    E = np.array([[x.hi if j == k else max(abs(x.lo), abs(x.hi)) for k, x in enumerate(row)] for j, row in enumerate(Gam)])
    Ed = np.abs(np.array([[ (Gam[j][k].lo - (1.0 if j == k else 0.0)) for k in range(n_head)] for j in range(n_head)]))
    Eu = np.abs(np.array([[ (Gam[j][k].hi - (1.0 if j == k else 0.0)) for k in range(n_head)] for j in range(n_head)]))
    normE = _u(float(np.linalg.norm(np.maximum(Ed, Eu)))*(1 + 1e-12))
    # pencil bound: for Gamma = I + E, ||E|| <= e < 1: lambda_min(M, Gamma) >= lambda_min(M)/(1 + e) if lambda_min(M) >= 0 else lambda_min(M)/(1 - e)
    lam_head = _d(lam_min_M/(1 + normE)) if lam_min_M >= 0 else _d(lam_min_M/(1 - normE))
    log(f"  lambda_min(M_head) >= {lam_head:.6e}  (float lambda_min {float(dvals[-1]):+.6e}, veigs radius {rho:.2e}, max entry width {max(x.width for row in Mh for x in row):.2e}, ||Gamma - I|| <= {normE:.2e})  ({time.time()-t0:.0f}s)")
    # ---- (5) the tail and the coupling
    Lam_tail = lam[NH + 1].hi
    for k in range(n_head):
        Lam_tail = _u(Lam_tail + lam[k].hi*pr[k]["eps"]**2)
    # ||P_perp chi||^2 = ||chi||^2 - c^T Gamma^{-1} c  >= 0 ; bound Gamma^{-1} by (1 - e)^{-1} ... use c^T c /(1 + e) as a LOWER bound on c^T Gamma^{-1} c
    cc = sum((cvec[k].sq() for k in range(n_head)), I(0.0))
    Pperp2 = _u(max(0.0, chi_norm2.hi - _d(cc.lo/(1 + normE))))
    q_perp = _d(W_out_lo*(1 - Lam_tail) - M_W*Lam_tail - (2*Pperp2 if parity == "odd" else 0.0))
    b = _u((M_W + W_out.hi)*math.sqrt(Lam_tail) + 2*math.sqrt(chi_norm2.hi*Pperp2))
    blk = np.array([[lam_head, -b], [-b, q_perp]])
    ev = np.linalg.eigvalsh(blk)[0]
    # rigorous 2x2 minimum eigenvalue: closed form
    tr = lam_head + q_perp; det = lam_head*q_perp - b*b
    disc = math.sqrt(max(tr*tr - 4*det, 0.0))
    final = _d(0.5*(tr - disc*(1 + 1e-12)) - 1e-300)
    log(f"  tail: Lambda_tail <= {Lam_tail:.2e}, ||P_perp chi||^2 <= {Pperp2:.2e}, q_perp >= {q_perp:.4f}, b <= {b:.2e}")
    verdict = "THEOREM: positive for every probe at delta = %g (%s), hence on [0, %g]" % (DELTA, parity, DELTA) if final > 0 else "NOT CERTIFIED"
    log(f"  FINAL LOWER BOUND lambda_min(Q) >= {final:+.6e}   -> {verdict}   ({time.time()-t0:.0f}s)")
    return dict(parity=parity, a=A, delta=DELTA, Omega=OMEGA, c=CC, NH=NH, h=h, nmax=nmax,
                lam0=[lam[0].lo, lam[0].hi], kstar=kstar, lam_NH1_hi=lam[NH + 1].hi,
                lam_head=lam_head, veigs_radius=rho, normE=normE, Lam_tail=Lam_tail,
                Pperp2=Pperp2, q_perp=q_perp, b=b, final=final, W_out_lo=W_out_lo, M_W=M_W,
                max_residual=max(p["r"] for p in pr), min_gap=min(p["gap"] for p in pr),
                max_eps=max(p["eps"] for p in pr), I00_width=Iband[0][0].width, verdict=verdict)

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "both"
    NH = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    h = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-4
    res = {}
    for par in (("even", "odd") if which == "both" else (which,)):
        res[par] = certify(par, NH=NH, h=h)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), f"slepian_cert_{which}_NH{NH}_h{h}.json")
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)
