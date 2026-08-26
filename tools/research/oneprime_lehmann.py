#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE B1, ROUND 5 -- the hardening: a
RIGOROUS second-eigenvalue bound replaces the ell_2 stand-in.

Commission: "Attack B pls" (the second next move at the round-4
landing: Lehmann-Goerisch-class ell_2 -- the novelty-bearing step
from feasibility toward theorem).

THE CHAIN (each link elementary and checkable; the odd link
CORRECTED by hostile round 243 -- the first committed version
stated the interlacing BACKWARDS, lambda_2(T) >= lambda_3(PWP),
and shipped need = 2 against its own comment's correct need = 0;
every odd certificate of that version is struck, and the even
chain was independently confirmed sound by the same round).
  (1) POLE REDUCTION. Even sector: the pole is PSD rank one, so
      lambda_2(T) >= lambda_2(PWP): count <= 1 for the pole-free
      even-projected operator suffices. Odd sector: the pole is
      negative rank one, and rank-one interlacing gives
      lambda_2(T) >= lambda_1(PWP) -- the CORRECT direction -- so
      the odd route is two-stage: first LOWER-BOUND
      lambda_1(PWP_odd) itself by Kato-Temple on the pole-free
      form (whose own ell_2 needs only #{PWP_odd < nu'} <= 1),
      then use that bound nu1 as the full form's rigorous ell_2.
  (2) THE BIRMAN-SCHWINGER-TYPE SPLIT, PARITY-PROJECTED. For
      beta > 0, W - nu = max(W - nu, beta) - qt with
      qt = (nu + beta - W)_+ compactly supported, so
      #{PWP_par < nu} <= #{eig(P_par qt(D) P_par) > beta}.
      PWP and qt(D) commute with parity, so the sector counts are
      exact, and the projected compressions live on [0, a] with
      the image-charge kernels
        K_+/-(x, y) = qtcheck(|x - y|) +/- qtcheck(x + y)
      (+ even, - odd). Projection SHARPENS both sectors: the
      unprojected count charged each sector with the other's dip
      modes.
  (3) THE COUNT. Nystrom (GL-NNY on [0, a]) on the analytic
      kernels; gates: gLW the trace wiring check (the two trace
      expressions are the same sum by construction -- labeled as
      wiring, per round 243's F2: it CANNOT catch physics errors);
      gL2 the Hilbert-Schmidt identity vs the Nystrom mu-sum (real
      content against the discretization); gL4 the r-quadrature
      refinement gate (int qt at dr vs dr/2); gL3 the resolution
      gate (counts and top eigenvalues stable from NNY to 2*NNY;
      implemented -- round 243's F3 found the first version
      claimed this gate without shipping it).
  (4) THE CERTIFICATES. Even: the largest grid nu with even-
      projected count <= 1 gives lambda_2(T) >= nu*; Kato-Temple
      with ell_2 = nu*. Odd: the largest nu' with odd-projected
      count <= 1 feeds Temple on the POLE-FREE form (rho_free,
      sigma_free from the same t-space pipeline with the pole
      column removed), giving nu1 <= lambda_1(PWP_odd); then
      Temple on the full form with ell_2 = nu1. (N, M, S) from the
      round-3 pipeline at base 0.003.

WHAT THIS ROUND DOES AND DOES NOT CLAIM. It removes the ell_2
stand-in -- the certificate's one structural IOU -- so the bound
chain is now mathematically closed. It does NOT yet claim a
theorem: every number is float64 (the quadratures are
ladder-validated but not interval enclosures), W's pointwise
values are scipy digamma, and the Nystrom count is spectral-quality
numerics with its trace-power scaffold recorded for the future
interval pass. That pass (round 6) is mechanical: 1-d integrals of
explicit smooth functions and finite eigenproblems.

GATES: as listed in chain step (3) -- gLW (wiring), gL2 (HS vs
Nystrom), gL4 (r-refinement), gL3 (resolution doubling), plus
gF1/gF4 inherited per cell from the round-3 pipeline, and gL5
(round 244 F3: cross-pipeline count consistency -- the
Birman-Schwinger/Nystrom count must dominate the independent
t-space section's count below every nu on the grid; this is the
committed anchor tying the counting kernel qtcheck to a second
pipeline -- the earlier suite's comparisons were all
spline-vs-spline or spline-free (round-245 C2 wording fix), so
a uniform kernel rescale passed every gate).

RESULT (the round-243 corrected-chain run; the invalid prior
odd-chain claims were never in this file -- forensics showed the
round-5 RESULT edit raced a commit inside a background job and a
rollback recovery destroyed the uncommitted text, so those claims
live only in commit messages c07360d/80e8e0d/c18866f, struck by
round 243; the no-edits-inside-background-jobs rule was born
there. All gates gLW/gL2/gL3/gL4 + gF1/gF4 passed;
float64-modulo throughout, the interval pass still owed):
  THE PARITY PROJECTION SHARPENED EVERY CELL (the unprojected
  count had charged each sector with the other's dip modes):
    even log 2  nu* 0.15   Temple +1.330e-3
    even 0.80   nu* 0.15   Temple +1.763e-4
    even 0.90   nu* 0.04   Temple +1.316e-5
    even 0.95   nu* 0.03   Temple +2.485e-6
    even 1.00   nu* 0.01   Temple -7.151e-7  (the unchanged
                rigorous even frontier: the projected count flips
                to 2 at nu 0.013, below the needed ~0.018)
  THE TWO-STAGE ODD ROUTE (projected counts are 0 through
  nu ~ 0.015-0.02, flipping to 1 exactly at the pole-free
  lambda_1 values nu1 ~ 0.016-0.020 and staying <= 1 through
  nu* = 0.15/0.15/0.08, so stage one certifies the pole-free
  operator's lambda_1 with room to spare; round-244 F2
  correction: an earlier gloss put the zero-count regime at
  "0.02-0.04", contradicting the committed count curves at both
  ends):
    odd 0.90  rho_free +2.044e-2, sigma_free 2.44e-3
              -> nu1 +2.039e-2 -> Temple +1.798e-3
    odd 1.05  nu1 +1.903e-2 -> Temple +3.158e-5  (round-244 F4:
              an earlier double-round printed 1.904e-2)
    odd 1.09  nu1 +1.585e-2 -> Temple +1.123e-5
  THE ROUND'S STANDING VERDICT: the full semi-local form carries
  rigorous-ell2 Kato-Temple lower bounds -- no stand-in, the
  chain now CORRECT at every link -- on [log 2, 0.95], and the
  odd sector on the entire one-prime window through 1.09 (the
  sliver (1.09, log 3) by the arc's standing top-cell
  convention; round-245 C1); every certificate
  equals or beats the struck FINAL claims (c18866f) -- but not
  every struck interim number: vs the struck run-1 message
  (80e8e0d) the corrected odd 0.9 is 15% weaker (+1.798e-3 vs
  the invalid +2.12e-3). Round-244 F1 correction: the earlier
  sentence "every certificate equals or beats the struck
  commit-message claims" was unscoped and false at that cell.
  What separates this from a theorem remains the mechanical
  interval pass.

CHECKS. 7: classical (Birman-Schwinger counting, prolate-type
compressions, Kato-Temple). 8: no hypothesis input.

Keying law: every producing file in every key.
"""
import hashlib, json, math, os, sys

import numpy as np
from scipy.linalg import eigh as scipy_eigh

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_bridge import build_Q64
from oneprime_certificate import Wker
from oneprime_push import temple_opt
import oneprime_fractional as opf

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSL = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "oneprime_bridge.py",
                              "oneprime_certificate.py",
                              "oneprime_push.py",
                              "oneprime_fractional.py",
                              "oneprime_top.py",
                              "oneprime_lehmann.py")}
KEYFILE = os.path.join(HERE, "oneprime_lehmann.py")

NNY = 260          # Nystrom order
BASE = 0.003       # the round-3 pipeline's quadrature base here
NUGRID = (0.002, 0.005, 0.01, 0.013, 0.015, 0.02, 0.03, 0.04,
          0.08, 0.15)
BETAGRID = (1.0, 1.5, 2.0, 2.5, 3.0, 3.5)
UMAX = 1.2         # covers 2a for every cell in the window

_qcache = {}

# Partial-checkpoint support (owner's rule after the 2026-08-26
# container restart lost a 90-minute in-memory run: ALL long
# computations carry partial save points). Two content-addressed
# side files in checkpoints/ (ephemeral compute state, out of
# review scope, deleted when the final checkpoint lands): a JSON
# of completed cells and a compressed NPZ of the qt-profile cache
# -- the profile builds dominate the cost, and a resumed run
# rebuilds each spline from the identical (ug, qc) arrays, so
# resumed numbers are bit-identical to a straight-through run.
_PROF_PATH = None

def _save_profiles():
    if _PROF_PATH is None:
        return
    data = {"ug": np.arange(0.0, UMAX, 1e-4)}
    for (nu, beta), (_spl, intqt, _ug, qc) in _qcache.items():
        tag = f"{nu:.9f}|{beta:.9f}"
        data["qc_" + tag] = qc
        data["meta_" + tag] = np.array([nu, beta, intqt])
    tmp = _PROF_PATH + ".tmp.npz"
    np.savez_compressed(tmp, **data)
    os.replace(tmp, _PROF_PATH)

def _load_profiles():
    if _PROF_PATH is None or not os.path.exists(_PROF_PATH):
        return
    from scipy.interpolate import CubicSpline
    z = np.load(_PROF_PATH)
    ug = z["ug"]
    n = 0
    for name in z.files:
        if not name.startswith("qc_"):
            continue
        tag = name[3:]
        nu, beta, intqt = z["meta_" + tag]
        qc = z[name]
        _qcache[(round(float(nu), 9), round(float(beta), 9))] = (
            CubicSpline(ug, qc), float(intqt), ug, qc)
        n += 1
    print(f"  partial: reloaded {n} qt profiles", flush=True)

def qt_profile(nu, beta, rmax=1500.0):
    """qtcheck(u) on a fine u-grid (CELL-INDEPENDENT), as a cubic
    spline plus exact trace ingredients; cached per (nu, beta).
    The r-grid is COMPOSITE: base dr 0.01 with dr 1e-4 refinement
    zones around every support-edge kink of qt. Round-245 F1
    re-diagnosis of the round-243 gL4 first-firing story: the
    3.5e-4 gL4 caught was the round-5 RECTANGLE rule's O(dr)
    endpoint error at r = 0, where qt is largest -- the closed
    form qt(0)(dr1-dr2)/int reproduces the measured 3.503e-4 to
    four digits -- NOT a support-edge kink error; the kink class
    sits at ~3e-8 on an honest uniform trapezoid grid at these
    (nu, beta), below this composite grid's own ~1.3e-6
    zone-structure residual. The earlier attribution ("the
    uniform grid's kink error ... caught by gL4") is struck: gL4
    gates the O(dr) weight-defect class (a rectangle regression
    trips it at 70x tolerance) and dr^2 refinement stability, not
    kink placement; the counting kernel's independent anchor is
    gL5."""
    key = (round(nu, 9), round(beta, 9))
    if key in _qcache:
        return _qcache[key]
    print(f"  profile ({nu:g}, {beta:g})", flush=True)
    r, wr = _qt_grid(nu, beta, rmax, 0.01)
    qt = np.clip(nu + beta - Wker(r), 0.0, None)
    assert qt[r > rmax - 2.0].max() == 0.0, "qt support hit rmax"
    ug = np.arange(0.0, UMAX, 1e-4)
    qc = np.empty(len(ug))
    qw = qt*wr
    for i in range(0, len(ug), 500):
        uu = ug[i:i + 500]
        qc[i:i + 500] = (np.cos(np.outer(uu, r)) @ qw)/np.pi
    from scipy.interpolate import CubicSpline
    spl = CubicSpline(ug, qc)
    intqt = 2*float(np.sum(qw))    # int over the full line
    _qcache[key] = (spl, intqt, ug, qc)
    _save_profiles()
    return _qcache[key]

def _qt_grid(nu, beta, rmax, base):
    """Composite trapz grid: base spacing, with 1e-4 spacing in
    +-0.05 zones around each sign change of nu + beta - W."""
    r0 = np.arange(0.0, rmax, base)
    r0[0] = 1e-9
    g0 = (nu + beta - Wker(r0)) > 0
    flips = r0[1:][g0[1:] != g0[:-1]]
    zones = sorted(set(float(f) for f in flips))
    segs = []
    lo = 0.0
    for z in zones:
        zl, zh = max(z - 0.05, lo), min(z + 0.05, rmax)
        if zl > lo:
            segs.append((lo, zl, base))
        segs.append((zl, zh, 1e-4))
        lo = zh
    segs.append((lo, rmax, base))
    rs, ws = [], []
    for slo, shi, h in segs:
        n = max(2, int(np.ceil((shi - slo)/h)) + 1)
        rr = np.linspace(slo, shi, n)
        ww = np.full(n, (shi - slo)/(n - 1))
        ww[0] /= 2; ww[-1] /= 2
        rs.append(rr); ws.append(ww)
    r = np.concatenate(rs)
    w = np.concatenate(ws)
    r[r < 1e-9] = 1e-9
    return r, w

def qtcheck_matrix(a, nu, beta, parity, nny=None):
    """Nystrom matrix of the PARITY-PROJECTED compression of
    qt(D) to [-a, a]: image-charge kernel on [0, a],
    K(x,y) = qtcheck(|x-y|) + s*qtcheck(x+y), s = +1 even / -1
    odd. Returns (mu descending, gate dict)."""
    if nny is None:
        nny = NNY
    spl, intqt, ug, qc = qt_profile(nu, beta)
    s = 1.0 if parity == "even" else -1.0
    x, w = np.polynomial.legendre.leggauss(nny)
    xs, ws = a*(x + 1)/2, a*w/2
    K = spl(np.abs(xs[:, None] - xs[None, :])) \
        + s*spl(xs[:, None] + xs[None, :])
    sw = np.sqrt(ws)
    Ks = sw[:, None]*K*sw[None, :]
    mu = np.linalg.eigvalsh((Ks + Ks.T)/2)[::-1]
    tr_ny = float(np.trace(Ks))
    m2 = ug < 2*a
    integ = (qc*qc*(2*a - ug))[m2]
    tr2_full = 2*(float(np.sum(integ)) - integ[0]/2)*1e-4
    return mu, {"tr_ny": tr_ny, "intqt": intqt,
                "tr2_full": tr2_full}

def gate_suite(a, nu, beta):
    """gLW/gL2/gL4/gL3 on one (nu, beta): the round-243 gate
    repair -- gLW is labeled wiring; the rest have real content."""
    mue, ge = qtcheck_matrix(a, nu, beta, "even")
    muo, go = qtcheck_matrix(a, nu, beta, "odd")
    spl, intqt, ug, qc = qt_profile(nu, beta)
    trfull = 2*a*float(spl(0.0))
    assert abs((ge["tr_ny"] + go["tr_ny"])/trfull - 1) < 1e-10, \
        "gLW FAIL"
    hs_ny = float(np.sum(mue*mue) + np.sum(muo*muo))
    assert abs(hs_ny/ge["tr2_full"] - 1) < 1e-5, \
        f"gL2 FAIL {hs_ny:.6e} vs {ge['tr2_full']:.6e}"
    r1, w1 = _qt_grid(nu, beta, 1500.0, 0.01)
    r2, w2 = _qt_grid(nu, beta, 1500.0, 0.005)
    i1 = 2*float(np.sum(np.clip(nu + beta - Wker(r1), 0, None)*w1))
    i2 = 2*float(np.sum(np.clip(nu + beta - Wker(r2), 0, None)*w2))
    # residual ~1.3e-6 is the composite grid's own zone-structure
    # convergence (round-245 F1: the earlier "kink error killed by
    # the composite zones" was struck -- an honest uniform trapz
    # sits at ~3e-8 here; what gL4 genuinely gates is the O(dr)
    # weight-defect class, e.g. the round-5 rectangle rule's
    # 3.5e-4 endpoint error, 70x this tolerance); count margins
    # sit four orders above this scale
    assert abs(i1/i2 - 1) < 5e-6, f"gL4 FAIL {i1:.6e} {i2:.6e}"
    for par, mu1 in (("even", mue), ("odd", muo)):
        mu2, _ = qtcheck_matrix(a, nu, beta, par, nny=2*NNY)
        for b in BETAGRID:
            assert int(np.sum(mu1 > b)) == int(np.sum(mu2 > b)), \
                f"gL3 FAIL count {par} beta {b}"
        assert max(abs(mu1[:3]/mu2[:3] - 1)) < 1e-8, "gL3 FAIL mu"
    return True

def certified_count(mu, beta, m=3):
    """The Nystrom count above beta, plus the trace-power scaffold
    1 + sum_{j>=2} (mu_j/beta)^{2m} (what an interval pass would
    bound); both returned."""
    cnt = int(np.sum(mu > beta))
    scaff = 1.0 + float(np.sum((np.clip(mu[1:], 0, None)/beta)
                               ** (2*m)))
    return cnt, scaff


def run():
    params = {"deps": DEPSL, "nny": NNY, "base": BASE,
              "nugrid": NUGRID, "betagrid": BETAGRID, "round": 243}
    st = ckpt_key.load("oneprime_lehmann", KEYFILE, params)
    if st is not None:
        return st
    k12 = ckpt_key.key(KEYFILE, params)[:12]
    ckdir = os.path.join(HERE, "checkpoints")
    pjson = os.path.join(
        ckdir, f"oneprime_lehmann_partial_{k12}.json")
    global _PROF_PATH
    _PROF_PATH = os.path.join(
        ckdir, f"oneprime_lehmann_profiles_{k12}.npz")
    _load_profiles()
    part = {}
    try:
        part = json.load(open(pjson))["state"]
        done = [c for c in part if not c.startswith("__")]
        print(f"  partial: resuming with {len(done)} cells done "
              f"({', '.join(done)})", flush=True)
    except Exception:
        pass
    st = {}
    cells = [("even", 0.6931), ("even", 0.80), ("even", 0.90),
             ("even", 0.95), ("even", 1.00),
             ("odd", 0.90), ("odd", 1.05), ("odd", 1.09)]
    gates_done = set(part.get("__gates_done__", []))
    for parity, delta in cells:
        cellk = f"{parity}:{delta:g}"
        if cellk in part:
            st[cellk] = part[cellk]
            continue
        a = delta/2
        if a not in gates_done:
            gate_suite(a, 0.01, 2.0)
            gates_done.add(a)
        best = {}
        for nu in NUGRID:
            kbest, srec = None, None
            for beta in BETAGRID:
                mu, _ = qtcheck_matrix(a, nu, beta, parity)
                cnt, scaff = certified_count(mu, beta)
                if kbest is None or cnt < kbest:
                    kbest = cnt
                    srec = {"beta": beta,
                            "mu123": [float(mu[0]), float(mu[1]),
                                      float(mu[2])],
                            "scaffold": scaff}
            best[f"{nu:g}"] = {"count": kbest, **srec}
        # both sectors need projected count <= 1: even for
        # lambda_2(PWP_even) >= nu directly; odd for the
        # pole-free Temple's own ell_2 (stage one)
        nustar = max((float(k) for k, v in best.items()
                      if v["count"] <= 1), default=None)
        md, N, M, S, gf4, grids = opf.cell_matrices(
            a, parity, base=BASE)
        assert gf4 < 1e-8, "gF4 FAIL"
        tn, tw, B, TB = grids
        Qc, Gc, _, _, _ = build_Q64(delta, parity=parity)
        if parity == "even":
            idx = np.arange(opf.NHALF)
        else:
            wcert = (np.arange(opf.NHALF) + 1.0)*np.pi/a
            idx = np.array([int(np.argmin(np.abs(md.w - w)))
                            for w in wcert])
        Qs = Qc[:opf.NHALF, :opf.NHALF]
        gf1 = float(np.linalg.norm(M[np.ix_(idx, idx)] - Qs)
                    / np.linalg.norm(Qs))
        assert gf1 < 5e-4, "gF1 FAIL"
        d = 1.0/np.sqrt(np.diag(N))
        Nn = d[:, None]*N*d[None, :]
        ev, U = np.linalg.eigh(Nn)
        keep = ev > 1e-4
        Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :])
              .T*d[None, :])
        chi = (np.cosh(tn/2) if parity == "even"
               else np.sinh(tn/2))
        Bw, TBw = Wh @ B, Wh @ TB
        vfull = 2*(Bw*(tw*chi)[None, :]).sum(1)
        TBfree = TBw - opf.psign(parity)*2*np.outer(vfull, chi)
        NA = 2*(Bw*tw[None, :]) @ Bw.T
        MA = 2*(Bw*tw[None, :]) @ TBw.T
        SA = 2*(TBw*tw[None, :]) @ TBw.T
        MF = 2*(Bw*tw[None, :]) @ TBfree.T
        SF = 2*(TBfree*tw[None, :]) @ TBfree.T
        NA, MA, SA = ((NA + NA.T)/2, (MA + MA.T)/2,
                      (SA + SA.T)/2)
        MF, SF = (MF + MF.T)/2, (SF + SF.T)/2
        l2sec = float(scipy_eigh(MA, NA, eigvals_only=True)[1])
        evF = scipy_eigh(MF, NA, eigvals_only=True)
        l1free = float(evF[0])
        # gL5 (round 244 F3): cross-pipeline count consistency.
        # Rayleigh-Ritz sections bound eigenvalues from above, so
        # #{section eigs < nu} <= #{PWP eigs < nu} <= the
        # Birman-Schwinger/Nystrom count, for every beta and hence
        # for the min over beta. One-sided by construction: it
        # catches undercounting -- the direction that could fake a
        # certificate -- while overcounting only weakens nustar.
        # A uniform kernel rescale below ~1 trips it (the mangle
        # class the pre-244 suite passed).
        for nu in NUGRID:
            scnt = int(np.sum(evF < nu))
            assert best[f"{nu:g}"]["count"] >= scnt, \
                f"gL5 FAIL {parity} d {delta:g} nu {nu:g}: " \
                f"count {best[f'{nu:g}']['count']} < sec {scnt}"
        row = {"count_curve": best, "nustar": nustar,
               "l2sec": l2sec, "l1_polefree_sec": l1free,
               "gF1": gf1}
        ell2 = None
        if parity == "even" and nustar is not None:
            ell2 = nustar
        elif parity == "odd" and nustar is not None:
            muF, cF = temple_opt(NA, MF, SF, nustar)
            if cF is not None:
                nnF = float(cF @ NA @ cF)
                rhoF = float(cF @ MF @ cF)/nnF
                sigF = math.sqrt(max(
                    float(cF @ SF @ cF)/nnF - rhoF*rhoF, 0.0))
                nu1 = (rhoF - sigF*sigF/(nustar - rhoF)
                       if nustar > rhoF else float("-inf"))
                row.update({"rho_free": rhoF,
                            "sigma_free": sigF, "nu1": nu1})
                if nu1 > 0:
                    ell2 = nu1
        if ell2 is not None and ell2 > 0:
            mu, c = temple_opt(NA, MA, SA, min(ell2, l2sec))
            nn = float(c @ NA @ c)
            rho = float(c @ MA @ c)/nn
            sig = math.sqrt(max(float(c @ SA @ c)/nn - rho*rho,
                                0.0))
            lam = (rho - sig*sig/(ell2 - rho)
                   if ell2 > rho else float("-inf"))
            row.update({"ell2_cert": ell2, "rho": rho,
                        "sigma": sig, "temple_rig": lam})
            extra = (f" [two-stage: rho_free "
                     f"{row.get('rho_free', float('nan')):+.3e} "
                     f"sigma_free "
                     f"{row.get('sigma_free', float('nan')):.3e}"
                     f" -> nu1 {ell2:+.4e}]"
                     if parity == "odd" else "")
            print(f"LEH {parity} delta {delta:g}: nustar "
                  f"{nustar:g} (proj counts "
                  f"{[best[f'{nu:g}']['count'] for nu in NUGRID]}"
                  f", l1_polefree_sec {l1free:+.3e}){extra} -> "
                  f"RIGOROUS-ell2 {ell2:.4g} Temple {lam:+.3e} "
                  f"(rho {rho:+.3e} sigma {sig:.3e}; stand-in "
                  f"l2sec {l2sec:.3e})", flush=True)
        else:
            print(f"LEH {parity} delta {delta:g}: NO certificate "
                  f"(nustar {nustar}, proj counts "
                  f"{[best[f'{nu:g}']['count'] for nu in NUGRID]}"
                  f", l1_polefree_sec {l1free:+.3e})", flush=True)
        st[cellk] = row
        part[cellk] = row
        part["__gates_done__"] = sorted(gates_done)
        json.dump({"key": ckpt_key.key(KEYFILE, params),
                   "state": part}, open(pjson, "w"), indent=0)
    ckpt_key.save("oneprime_lehmann", KEYFILE, params, st)
    for p in (pjson, _PROF_PATH):
        if os.path.exists(p):
            os.remove(p)
    return st


if __name__ == "__main__":
    run()
    print("one-prime rigorous-ell2 round complete", flush=True)
