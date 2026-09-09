#!/usr/bin/env python3
"""Keyed producer: THE ODD SECTOR of the true form at the seven cells (Theorem 1bv's substrate). The Weil form on the
ODD probes of [-a, a] (delta = 2a) in the sine basis phi_k = sin(omega_k t), omega_k = k pi/a, k = 1..K-1
(weil_prime_gram_odd.gram_odd: the prime-side Gram in balls, the pole term -2 p^2 with p = int g sinh(t/2) --
negative in the odd sector); the lowest eigenvectors (flint's approximate eigensolver on the midpoints) and their
transforms ghat(r)/i = 2 sin(ra) sum_k (-1)^k v_k omega_k/(r^2 - omega_k^2), odd in r, with ghat(omega_k) = i a v_k.
The odd probe's transform factors as ghat(r) = i r Ghat(r) with G(s) = int_{|s|}^a g(t) dt even and G(+-a) = 0, so the
odd sector is the even form with the multiplier gamma^2 on the zero side (Theorem 1bv(ii)); the census below is of
Ghat's zeros. Stored per cell:

THE GROUND STATE. ln lambda_1; Ghat_1(0)^2 = |ghat_1'(0)|^2; the curvature of Ghat_1 at the origin kappa = sum tau^-2
(central differences of ghat_1/r at h = 2e-4 and 1e-4, Richardson-extrapolated); <r^2> under ghat_1^2 (the weight
r^2 Ghat_1^2, in balls on 6000 Gauss-Legendre nodes of [0, 1.6 T_0]); the DODGING EDGE (the real zeros of Ghat_1 on
(0, 2.2 T_0) at step 0.05 refined by bisection: the first zeta zero missed and the first free zero); the DODGING
DISPLACEMENTS below the edge (the maximum, the maximum over the low half, the located zeros' sum tau^-2, their
contribution to the Xi-bound at r = 3); the FULL REAL-ZERO CENSUS of Ghat_1 on (0, R_ext), R_ext = 2 omega_{K-1}
doubled (to 8 omega_{K-1} at most) while a designed pair is missing -- Ghat_1 = 2 sin(ra) N(r^2)/(r prod_{0<k<K}(r^2 -
omega_k^2)) with N of degree K - 2, so the zeros are K - 2 designed pairs plus the sinc zeros omega_j (j >= K), the
sum rule kappa = sum_designed tau^-2 + (a/pi)^2 sum_{j>=K} j^-2 checking the census, an unlocated pair placed by
the sum rule -- and the census's dip count; the exterior mass of ghat_1^2 beyond T_D/4, T_D/2, T_D (the transform in
balls on a grid of spacing 0.1 to 4 T_0 plus the far-field tail: g(a) = 0 in the sine basis, so ghat ~ 2i g'(a) sin(ra)/r^2
and the mass beyond R is ~2 g'(a)^2/(3 R^3)); the EXTERIOR PROFILE on the 800 zeros known to 100 digits (w_gamma = |ghat_1(gamma)|^2
in arb, the zero side ln(2 sum w) against the prime side, the far tail), the balayage formula's minimum F(T*) on the
zeta zeros (as Theorem 1bm(v)) and c_1 = ln lambda_1 - F(T*); THE ODD ANATOMY Q = pole + const + archimedean +
primes with pole = -2 p^2 (p = sum_k v_k p_k, p_k = Im[2 sinh((1/2 + i omega_k) a)/(1/2 + i omega_k)]), const =
(psi(1/4) - ln pi), primes = -2 sum Lambda(n) n^{-1/2} f_1(ln n) with the sine-basis autocorrelations, the archimedean
term v^T A v from the Gram's own archimedean part (gram_odd(..., parts=True)), the identity lambda_1 = pole + const +
arch + primes then a check (its residual stored); the participation and the cumulative shares of the 800-zero sum.

THE DEEP RUNGS (the odd rung k at the prolate order 4k + 2: its leakage ln(1 - chi_{4k+2}) is index 2k + 1 of the even
list computed at c = T_0 as in weil_spectrum_ladder.prolate_even_leakage; deep = ln(1 - chi) < -2, up to rung 12).
For rung k: the real zeros of Ghat_k on (0, min(100, 0.8 x the ground state's dodging edge)) at step 0.03, a double zero
without sign change as a dip (counted twice); the HOLE ZEROS = the located zeros left after one dodging zero per zeta
zero (the nearest within 0.2) is removed, the census stopping at 0.8 x the rung's own dodging edge; the k-level
balayage formula F_k on the zeta zeros plus the hole zeros, T_k, c_k = ln lambda_k - F_k; the OFFSET ln lambda_k -
ln(1 - chi_{4k+2}) against the prolate order 4k + 2.

THE NODES. The positive zeros of the even orthogonal polynomials P_{2m} of the weight ghat_1(r)^2 dr on [0, 1.6 T_0]
(Stieltjes in s = r^2 at 40 digits), m = 1..min(deep, 12): the polynomial ladder's prediction for rung m + 1's hole
zeros (Theorem 1bu(iii) in the odd sector: the weight r^2 Ghat_1^2).

THE SELF-TEST cell "selftest": the odd Gram's Q against 2 sum_gamma |ghat(gamma)|^2 over the 6700 zeros plus the
density tail for the odd bump t e^{-1/(1 - (t/a)^2)} at delta = 1 (K 48) and 2 (K 80), in mpmath at 40 digits.

State per cell. Usage: odd_sector.py [cell ...]"""
import sys, os, json, math, time, hashlib
from flint import arb, acb, arb_mat, acb_mat, ctx
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from weil_prime_gram_odd import gram_odd, rayleigh_odd
from weil_prime_gram import prime_powers
from weil_spectrum_ladder import prolate_even_leakage
from ladder_caster import CELLS, real_zeros, classify, balayage_min, poly_nodes, RMAX_HOLE, STEP_HOLE, STEP_DODGE, TOL, TOL_HOLE, EDGE_FRAC, NODES_MAX, KMAX, DEEP

DEPS = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("odd_sector.py",), HERE))}
KEYFILE = os.path.join(HERE, "odd_sector.py")
CK = os.path.join(HERE, "checkpoints")
ZP = os.path.join(CK, "zeta_zeros_800_100dps.json")
ZD = os.path.join(CK, "zeta_zeros_6700.json")

def _sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()

def ghat_odd_factory(v, a, K):
    """ghat(r)/i for the sine coefficients v[k-1], k = 1..K-1 (odd in r)."""
    om = [arb(k)*arb.pi()/a for k in range(K)]; sg = [(v[k - 1] if k % 2 == 0 else -v[k - 1])*om[k] for k in range(1, K)]
    def gh(r):
        r2 = r*r; s = arb(0)
        for k in range(1, K): s += sg[k - 1]/(r2 - om[k]*om[k])
        return 2*(r*a).sin()*s
    return gh

def Ghat_factory(gh):
    """Ghat(r) = ghat(r)/(i r): even (never called at r = 0 -- the zero scans use offset grids; Ghat(0) is taken exactly, see Ghat0)."""
    def G(r): return gh(r)/r
    return G

def Ghat0(v, a, K):
    """Ghat(0) = lim ghat(r)/(i r) = -2a sum_{k>=1} (-1)^k v_k/omega_k exactly (the sine basis's Nyquist samples)."""
    om = [arb(k)*arb.pi()/a for k in range(K)]
    return -2*a*sum(((v[k - 1] if k % 2 == 0 else -v[k - 1])/om[k] for k in range(1, K)), arb(0))

def selftest_state():
    zeros = [float(z) for z in json.load(open(ZD))]
    import mpmath as mp
    mp.mp.dps = 40
    out = []
    for delta, K, prec in ((1.0, 48, 400), (2.0, 80, 400)):
        a = delta/2
        bump = lambda t: t*mp.e**(-1/(1 - (t/a)**2)) if abs(t) < a else mp.mpf(0)
        c = [mp.quad(lambda t: bump(t)*mp.sin(k*mp.pi*t/a), [-a, 0, a])/a for k in range(1, K)]
        G, N, pp = gram_odd(delta, K, prec)
        q_prime = rayleigh_odd(G, N, [arb(str(x)) for x in c], prec)
        den = sum(a*x**2 for x in c)
        def ghat_over_i(r):
            s = mp.mpf(0)
            for k in range(1, K):
                w = k*mp.pi/a; s += c[k - 1]*(mp.sin((r - w)*a)/(r - w) - mp.sin((r + w)*a)/(r + w))
            return s
        qz = 2*sum(ghat_over_i(g)**2 for g in zeros)
        tail = 2*mp.quad(lambda r: ghat_over_i(r)**2*mp.log(r/(2*mp.pi))/(2*mp.pi), [zeros[-1], 2*zeros[-1], 10*zeros[-1], 100*zeros[-1]])
        out.append({"delta": delta, "K": K, "prime_side_mid": float(q_prime.mid()), "prime_side_rad": float(q_prime.rad().str(5, radius=False)),
                    "zero_side": float((qz + tail)/den), "tail": float(tail/den), "prime_powers": pp})
    return {"cell": "selftest", "cases": out}

def run(cell):
    if cell == "selftest":
        params = {"deps": DEPS, "cell": cell, "zeros6700": _sha(ZD), "round": 1}
        st = ckpt_key.load("odd_sector_selftest", KEYFILE, params, kfun=ckpt_key.code_key)
        if st is not None: return st
        st = selftest_state(); ckpt_key.save("odd_sector_selftest", KEYFILE, params, st, kfun=ckpt_key.code_key); return st
    cfg = CELLS[cell]
    params = {"deps": DEPS, "cell": cell, **cfg, "zeros100": _sha(ZP), "zeros6700": _sha(ZD), "rmax_hole": RMAX_HOLE,
              "step_hole": STEP_HOLE, "step_dodge": STEP_DODGE, "tol": TOL, "tol_hole": TOL_HOLE, "edge_frac": EDGE_FRAC, "kmax": KMAX, "nodes_max": NODES_MAX, "deep": DEEP, "round": 1}
    name = f"odd_sector_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None: return st
    d, K, prec, m = cfg["delta"], cfg["K"], cfg["prec"], cfg["m"]; a = d/2; T0 = 2*math.pi*math.exp(d)
    ZS = np.array(json.load(open(ZD)), dtype=float); Z40 = json.load(open(ZP))
    t0 = time.time()
    with ctx.workprec(cfg["tprec"]):
        c = 2*arb.pi()*arb(d).exp()
        pro = prolate_even_leakage(c, int(float(c)) + 300, 2*m + 2, cfg["tprec"])
    deep = sum(1 for k in range(1, m + 1) if 2*k + 1 < len(pro) and pro[2*k + 1] is not None and pro[2*k + 1] < DEEP)
    G, N, pp, A_part = gram_odd(d, K, prec, parts=True); n = K - 1; t1 = time.time()
    with ctx.workprec(prec):
        Dm = arb_mat(n, n)
        for i in range(n): Dm[i, i] = 1/N[i].sqrt()
        E, Rv = acb_mat((Dm*G*Dm).mid()).eig(right=True, algorithm="approx")
        order = sorted(range(n), key=lambda i: float(E[i].real.mid())); t2 = time.time()
        aa = arb(a); twoa = 2*aa
        vecs = []; lams = []
        for j in range(min(deep, KMAX) + 1):
            v = [Rv[i, order[j]].real.mid()/N[i].sqrt() for i in range(n)]
            nrm = arb(0)
            for i in range(n): nrm += N[i]*v[i]*v[i]
            vecs.append([x/nrm.sqrt() for x in v]); lams.append(E[order[j]].real.mid())
        # ---- the ground state
        gh = ghat_odd_factory(vecs[0], aa, K); Gh = Ghat_factory(gh)
        G0 = Ghat0(vecs[0], aa, K); ln_G0sq = float((G0*G0).log())
        def _kfd(h): return float((-(Gh(h) - 2*G0 + Gh(-h))/(h*h)/(2*G0)).mid())
        kappa_fd = _kfd(arb(2)/10000); kappa = (4*_kfd(arb(1)/10000) - kappa_fd)/3
        omf = np.arange(K)*np.pi/a
        R = 1.6*T0; x, wq = np.polynomial.legendre.leggauss(6000); x = 0.5*R*(x + 1) + 1e-7; wq = 0.5*R*wq
        Ew = np.array([float(gh(arb(float(t))).mid()) for t in x]); w = wq*Ew*Ew; m2 = float(np.sum(w*x*x)/np.sum(w))
        nodes = poly_nodes(x, w, min(deep, NODES_MAX))
        z = real_zeros(Gh, 2.2*T0, STEP_DODGE, dips=True)
        missed = [float(g) for g in ZS[ZS < 2.2*T0] if not any(abs(xx - g) < TOL for xx in z)]
        free = [xx for xx in z if float(np.min(np.abs(ZS - xx))) >= TOL]
        TDv = min(missed) if missed else 2.2*T0
        disp = []
        for gmm in ZS[ZS < TDv]:
            cand = [xx for xx in z if abs(xx - gmm) < TOL]; disp.append((float(gmm), min(cand, key=lambda xx: abs(xx - gmm)) - float(gmm)))
        disp_max = max((abs(e) for _, e in disp), default=0.0)
        lowl = [abs(e) for gm, e in disp if gm < TDv/2]; disp_max_low = max(lowl) if lowl else None
        sum_inv_sq_located_below = sum(1.0/(gm + e)**2 for gm, e in disp)
        disp_term_r3 = sum(abs(math.log(abs(1 - 9.0/(gm + e)**2)) - math.log(abs(1 - 9.0/gm**2))) for gm, e in disp)
        # the full real-zero census of Ghat_1: K - 2 designed pairs plus the sinc zeros
        def _designed(zs, Rx):
            sinc = [j*math.pi/a for j in range(K, int(Rx/(math.pi/a)) + 2) if j*math.pi/a < Rx]
            return [xx for xx in zs if not any(abs(xx - ww) < 1e-6 for ww in sinc)]
        R_ext = 2.0*float(omf[K - 1]); z_ext = real_zeros(Gh, R_ext, STEP_DODGE, dips=True); designed = _designed(z_ext, R_ext)
        while len(designed) < K - 2 and R_ext < 8.0*float(omf[K - 1]) - 1e-9:
            R_ext = 2.0*R_ext; z_ext = real_zeros(Gh, R_ext, STEP_DODGE, dips=True); designed = _designed(z_ext, R_ext)
        n_dips = sum(1 for i in range(1, len(z_ext)) if z_ext[i] == z_ext[i - 1])
        tail_sum = float((aa/arb.pi())**2*acb(K).polygamma(1).real)
        sum_rule = sum(1.0/(xx*xx) for xx in designed) + tail_sum
        missing = None
        if len(designed) == K - 3 and sum_rule != kappa:
            missing = {"abs_tau": abs(sum_rule - kappa)**-0.5, "real": sum_rule < kappa}
        n_zeta_below_edge = int(np.sum(ZS < TDv)); n_located_below_edge = sum(1 for xx in z if xx < TDv)
        # the exterior profile on the 800 zeros
        gam = [arb(s) for s in Z40]; gf = np.array([float(s) for s in Z40])
        lnw = np.array([float((gh(g)**2).log()) for g in gam])
        ln_lam1 = float(lams[0].log())
        mx = lnw.max(); S = float(np.exp(lnw - mx).sum()); ln_zero = math.log(2*S) + mx
        imax = int(np.argmax(lnw)); part = S*S/float(np.sum(np.exp(2*(lnw - mx))))
        cum = np.cumsum(np.exp(lnw - mx))/S
        shares = {str(f): float(cum[gf < f*T0][-1]) if np.any(gf < f*T0) else 0.0 for f in (2, 3, 4, 6, 10)}
        F1, T1 = balayage_min(ZS, d, T0); c1 = ln_lam1 - F1; far = ln_lam1 - ln_zero
        # the odd anatomy
        pi = arb.pi(); half = arb(1)/2; quarter = arb(1)/4
        om = [arb(k)*pi/aa for k in range(K)]
        Pk = [(2*(acb(half, om[k])*aa).sinh()/acb(half, om[k])).imag for k in range(1, K)]
        v = vecs[0]; p = sum((v[k - 1]*Pk[k - 1] for k in range(1, K)), arb(0)); pole = float((-2*p*p).mid())
        const = float((quarter.digamma() - pi.log()).mid())
        pp2 = [(nn, q) for nn, q in prime_powers(int(math.floor(math.exp(2*a) + 1e-9))) if math.log(nn) < 2*a]
        terms = []
        for nn, q in pp2:
            u = arb(nn).log(); wgt = arb(q).log()/arb(nn).sqrt()
            sinl = [(om[k]*u).sin() for k in range(K)]; cosl = [(om[k]*u).cos() for k in range(K)]
            f = arb(0)
            for j in range(1, K):
                for k in range(1, K):
                    if j == k: fj = ((twoa - u)*cosl[k] + sinl[k]/om[k])/2
                    else:
                        sg = -1 if (j + k) % 2 else 1
                        fj = sg*(om[j]*sinl[k] - om[k]*sinl[j])/(om[j]*om[j] - om[k]*om[k])
                    f += v[j - 1]*v[k - 1]*fj
            terms.append((nn, q, float(f.mid()), float((-2*wgt*f).mid())))
        primes = sum(t[3] for t in terms); lam1f = float(lams[0].mid())
        # the archimedean term from the Gram's own archimedean part (gram_odd(..., parts=True)): the identity lambda_1 = pole + const + arch + primes is then a check, not a definition
        va = arb_mat(n, 1)
        for i in range(n): va[i, 0] = v[i]
        arch = float((va.transpose()*A_part*va)[0, 0].mid()); identity_residual = lam1f - (pole + const + arch + primes)
        # the exterior mass of ghat_1^2 beyond T_D/4, T_D/2, T_D
        xg = np.linspace(1e-7, 4*T0, int(4*T0/0.1) + 1); Eg = np.array([float(gh(arb(float(t))).mid()) for t in xg])
        gpa = float(sum(((v[k - 1] if k % 2 == 0 else -v[k - 1])*float(omf[k]) for k in range(1, K))))   # g'(a) = sum v_k omega_k cos(k pi); g(a) = 0 in the sine basis, so the far field is 2 g'(a) sin(ra)/r^2 and its tail beyond R is 2 g'(a)^2/(3 R^3)
        def mass_beyond(Rr):
            msk = xg >= Rr; return (float(np.trapezoid(Eg[msk]**2, xg[msk])) + 2*gpa*gpa/(3*(4*T0)**3))/math.pi
        mass = {"TD/4": mass_beyond(TDv/4), "TD/2": mass_beyond(TDv/2), "TD": mass_beyond(TDv)}
        ground = {"ln_lam1": ln_lam1, "ln_G0sq": ln_G0sq, "kappa": kappa, "kappa_fd": kappa_fd, "r2_mean": m2, "first_missed": min(missed) if missed else None,
                  "first_free": min(free) if free else None, "n_dodged": len(z) - len(free), "disp_max": disp_max, "disp_max_low": disp_max_low,
                  "sum_inv_sq_located_below": sum_inv_sq_located_below, "disp_term_r3": disp_term_r3,
                  "n_designed_real": len(designed), "K_minus_2": K - 2, "sum_rule": sum_rule, "sum_rule_residual": sum_rule - kappa, "R_ext": R_ext, "missing_pair": missing,
                  "n_dips_census": n_dips, "n_zeta_below_edge": n_zeta_below_edge, "n_located_below_edge": n_located_below_edge, "mass_beyond": mass, "boundary_slope": gpa,
                  "ln_zero_side_800": ln_zero, "far_tail": far, "Tstar": T1, "F1": F1, "c1": c1, "pole": pole, "const": const, "arch": arch, "primes": primes, "identity_residual": identity_residual,
                  "prime_terms": terms, "participation_800": part, "w_max_at": float(gf[imax]), "shares": shares}
        t3 = time.time()
        # ---- the deep rungs
        rungs = [{"k": 1, "ln_lam": ln_lam1, "hole": [], "prolate_4k2": pro[3] if 3 < len(pro) else None, "Fk": F1, "Tk": T1, "ck": c1}]
        for j in range(1, min(deep, KMAX) + 1):
            Gj = Ghat_factory(ghat_odd_factory(vecs[j], aa, K))
            rmax_k = min(RMAX_HOLE, EDGE_FRAC*(ground["first_free"] or 2.2*T0))
            zj = real_zeros(Gj, rmax_k, STEP_HOLE, dips=True)
            hole, _nd = classify(zj, ZS[ZS < rmax_k], TOL_HOLE)
            missed_k = [float(g) for g in ZS[ZS < rmax_k] if not any(abs(zz - g) < TOL_HOLE for zz in zj)]
            edge_k = min(missed_k) if missed_k else rmax_k/EDGE_FRAC
            hole = [zz for zz in hole if zz < EDGE_FRAC*edge_k]
            Fk, Tk = balayage_min(np.concatenate([ZS, hole]), d, T0)
            lnl = float(lams[j].log()); idx = 2*(j + 1) + 1
            rungs.append({"k": j + 1, "ln_lam": lnl, "prolate_4k2": pro[idx] if idx < len(pro) else None, "hole": hole, "edge": edge_k, "Fk": Fk, "Tk": Tk, "ck": lnl - Fk})
        t4 = time.time()
    st = {"cell": cell, "delta": d, "T0": T0, "K": K, "prec": prec, "m": m, "deep": deep, "gamma1": float(ZS[0]), "ground": ground,
          "nodes": nodes, "rungs": rungs, "prolate_ln_leakage": pro, "gram_s": t1 - t0, "eig_s": t2 - t1, "ground_s": t3 - t2, "rungs_s": t4 - t3,
          "verdict": "COMPUTED (approximate eigenvectors; zeros located by sign change and bisection in balls at the working precision)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    for cell in (sys.argv[1:] or ["selftest"] + list(CELLS)):
        st = run(cell)
        if cell == "selftest":
            for cs in st["cases"]: print(f"selftest delta {cs['delta']} K {cs['K']}: prime side {cs['prime_side_mid']:.15e} (+/- {cs['prime_side_rad']:.1e}) zero side {cs['zero_side']:.15e}", flush=True)
            continue
        g = st["ground"]
        print(f"{st['cell']:6s} delta {st['delta']:<9} deep {st['deep']:2d} | ln lam_1 {g['ln_lam1']:.3f} (zero side + far tail {g['ln_zero_side_800'] + g['far_tail']:.3f}), G(0)^2 {math.exp(g['ln_G0sq']):.4f}, kappa {g['kappa']:.5f}, sqrt<r^2> {math.sqrt(g['r2_mean']):.3f}; "
              f"edge: missed {g['first_missed']}, free {g['first_free']}; census {g['n_designed_real']}/{g['K_minus_2']} resid {g['sum_rule_residual']:.1e}; anatomy pole {g['pole']:+.4f} arch {g['arch']:+.4f} primes {g['primes']:+.4f}; c1 {g['c1']:.3f}"
              f" | first hole zeros: " + ", ".join(f"{r['hole'][0]:.3f}" if r['hole'] else "-" for r in st['rungs'][1:5]) + " vs nodes " + ", ".join(f"{nd[0]:.3f}" for nd in st['nodes'][:4])
              + f" | offsets: " + ", ".join(f"{r['ln_lam'] - r['prolate_4k2']:+.2f}" if r['prolate_4k2'] is not None else "-" for r in st['rungs'][:6]) + f" [gram {st['gram_s']:.0f}s eig {st['eig_s']:.0f}s ground {st['ground_s']:.0f}s rungs {st['rungs_s']:.0f}s]", flush=True)
