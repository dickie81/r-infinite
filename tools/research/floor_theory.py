#!/usr/bin/env python3
"""The floor-law derivation, phase 1 (owner's commission: "pursue the
derivation" -- the analytic twin theory of the crossing).

TARGET. Derive the certified 1bg/1bh floor law m ~ m_sat 10^(-beta d)
from the section's own Slepian spectrum, as an identity-level
composition:

  (D1) THE LEAKAGE IDENTITY: the dodging margin is the sampled
       leakage of the minimizer -- m ~ sum over OUT-of-band zeros of
       |f_min(gamma)|^2, approximated by (local density) x
       (out-of-window energy). Testable exactly: split the minimizer's
       sampled energy in/out of band, and compare the out-band sum to
       rho x the continuous out-of-window integral.
  (D2) THE CONSTRAINT PRICE: one in-band zero imposes one COMPLEX
       vanishing condition = two REAL constraints on the
       real-parameterized section -- the candidate derivation of the
       certified "~2 modes per added zero" occupancy-edge advance.
       Testable: the minimizer's occupancy edge k_edge vs n_b.
  (D3) THE RATE COMPOSITION: beta = (edge advance per zero) x
       (per-mode decade-rate of the leakage ladder 1 - lambda_k below
       the plunge), with lambda_k the section's own concentration
       eigenvalues (computed, not asymptotic). Then compare the
       computed per-mode rate against the Landau-Widom logit slope
       (the classical asymptotic) and adjudicate the certified
       "beta ~ 1.1, approximately c-flat" against LW's 1/ln c.
  (D4) M_SAT: the saturation scale from the plunge-center leakage x
       the density -- consistency with the certified feature-local
       0.18-0.42 band.

All deterministic (the comb configuration -- zero jitter); the twin's
jitter discount and the height drift are phase 2. Check 7: Slepian
concentration spectra, finite eigenproblems -- classical. Check 8: no
hypothesis input. Keying per the standing law: every producing file
in the key (this file + fold_D + fold_surrogate), full config,
z-independent (comb only).
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import inv_Nbar, TWO_PI
from fold_surrogate import Sect, psi_hat_batch, A, NZ


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPST = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "floor_theory.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")


def concentration_spectrum(S, nq=3000):
    """lambda_k for each prolate mode: fraction of gamma-side energy
    inside the window |s| <= c (s = A(gamma - tau0)); total energy by
    the same quadrature over a wide domain (type-A functions decay
    fast beyond the window for low modes, slowly for plunge modes --
    integrate to 8c and add nothing: the tail beyond is the residual
    disclosed in the result)."""
    c = S.c
    xg, wg = np.polynomial.legendre.leggauss(nq)
    # in-window
    s_in = c*xg
    V_in = psi_hat_batch(S.P, s_in)
    Ein = np.sum((np.abs(V_in)**2)*(c*wg)[None, :], axis=1)
    # out-of-window, |s| in [c, 8c]
    s_out = c + (8*c - c)*(xg + 1)/2
    V_out = psi_hat_batch(S.P, np.concatenate([s_out, -s_out]))
    w2 = (7*c/2)*wg
    Eout = (np.sum((np.abs(V_out[:, :nq])**2)*w2[None, :], axis=1)
            + np.sum((np.abs(V_out[:, nq:])**2)*w2[None, :], axis=1))
    lam = Ein/(Ein + Eout)
    return lam, Ein, Eout


def margin_full(S, zeros, tau0):
    """Margin + minimizer + diagnostics (in/out band split, occupancy,
    continuous leakage of the minimizer)."""
    s_all = np.concatenate([(zeros - tau0)*A, (-zeros - tau0)*A])
    V = psi_hat_batch(S.P, s_all)*A
    Q = V @ V.conj().T
    Q = (Q + Q.conj().T)/2
    ev, W = scipy_eigh(Q, S.G)
    m, w = float(ev[0]), W[:, 0]
    # sampled energy per ordinate for the minimizer
    amp2 = np.abs(w.conj() @ V)**2
    inband = np.abs(s_all) <= S.c
    occ = np.abs(w)**2 * np.real(np.diag(S.G))
    occ = occ/occ.sum()
    # occupancy edge: largest k with cumulative occupancy <= 99%
    k_edge = int(np.searchsorted(np.cumsum(occ), 0.99))
    return {"m": m, "in_sum": float(amp2[inband].sum()),
            "out_sum": float(amp2[~inband].sum()),
            "occ": occ, "k_edge": k_edge, "w": w}


def leakage_of(S, w, tau0, nq=3000):
    """Continuous out-of-window |f_min|^2 integral (gamma-side), for
    the density x leakage approximation."""
    c = S.c
    xg, wg = np.polynomial.legendre.leggauss(nq)
    s_out = c + 7*c*(xg + 1)/2
    V = psi_hat_batch(S.P, np.concatenate([s_out, -s_out]))*A
    f2 = np.abs(w.conj() @ V)**2
    w2 = (7*c/2)*wg
    return float((f2[:nq]*w2).sum() + (f2[nq:]*w2).sum())


def run():
    params = {"deps": DEPST, "phase": 1}
    st = ckpt_key.load("floor_theory_p1", KEYFILE, params)
    if st is not None:
        print("REUSED phase-1 state"); return st
    comb = np.array([inv_Nbar(float(k)) for k in range(1, NZ + 1)])
    st = {"spectrum": {}, "ladder": {}, "identity": {}}
    # ---- the spectrum and its per-mode leakage rate, per c ----
    for c in (60.0, 90.0, 120.0, 170.0):
        S = Sect(c)
        lam, Ein, Eout = concentration_spectrum(S)
        Nsh = 2*c/math.pi
        # per-mode decade rate of (1 - lambda_k) below the plunge:
        # fit log10(1-lambda) over the modes k in [Nsh-10, Nsh-2]
        ks = np.arange(len(lam))
        sel = (ks >= Nsh - 10) & (ks <= Nsh - 2) & (lam < 1 - 1e-13)
        slope = float(np.polyfit(ks[sel],
                                 np.log10(1 - lam[sel]), 1)[0])
        # Landau-Widom logit slope for comparison (classical):
        # d/dk logit(lambda) = -pi^2/ln(kappa c); report the measured
        # logit slope instead of assuming kappa
        logit = np.log((1 - lam[sel])/lam[sel])
        lw_slope = float(np.polyfit(ks[sel], logit, 1)[0])
        st["spectrum"][f"{c:g}"] = {
            "Nsh": Nsh, "n": S.n,
            "lam_edge": [float(lam[int(Nsh) + j]) for j in (-4, -2, 0, 2)],
            "dec_per_mode": slope, "logit_slope": lw_slope,
            "ln_c": math.log(c)}
        print(f"c={c:5.0f}: Nsh {Nsh:6.2f} | 1-lam decade/mode "
              f"{slope:+.4f} | logit slope {lw_slope:+.4f} "
              f"(pi^2/slope -> ln(kappa c) = {math.pi**2/abs(lw_slope):.2f}"
              f" vs ln c = {math.log(c):.2f})", flush=True)
    # ---- the comb ladder at c = 120: margins, edges, the identity --
    S = Sect(120.0)
    lam120, _, _ = concentration_spectrum(S)
    Nsh = 2*120.0/math.pi
    rows = []
    for t0 in (250.0, 260.0, 270.0, 280.0, 290.0, 300.0, 310.0,
               320.0, 330.0, 340.0, 350.0):
        r = margin_full(S, comb, t0)
        nb = int(np.sum(np.abs((comb - t0)*A) <= S.c))
        rho = math.log(t0/TWO_PI)/TWO_PI          # zeros per unit gamma
        leak = leakage_of(S, r["w"], t0)
        # the leakage identity: out_sum vs rho * leak * A-scaling
        # (s-units: density in s is rho/A; ds = A dgamma so the
        # continuous integral in s-units samples at density rho/A...
        # both computed in s-units here: predicted = (rho/A) * leak_s
        # with leak_s the s-side integral; leakage_of integrates in
        # s -- so predicted out_sum = (rho/A)*leak)
        pred = (rho/A)*leak
        rows.append({"t0": t0, "nb": nb, "d": Nsh - nb, "m": r["m"],
                     "in": r["in_sum"], "out": r["out_sum"],
                     "k_edge": r["k_edge"], "pred_out": pred})
        print(f"t0={t0:5.0f}: nb {nb} (d {Nsh-nb:+5.2f}) m {r['m']:.3e}"
              f" | in/out {r['in_sum']:.2e}/{r['out_sum']:.2e}"
              f" | edge k {r['k_edge']} | rho*leak {pred:.2e}"
              f" (ratio {r['out_sum']/max(pred,1e-300):.2f})", flush=True)
    st["ladder"]["120"] = rows
    # beta from the climb rows (1e-12 < m < 1e-2), vs the composition
    sel = [r for r in rows if 1e-12 < r["m"] < 1e-2]
    if len(sel) >= 3:
        beta = -float(np.polyfit([r["nb"] for r in sel],
                                 [math.log10(r["m"]) for r in sel],
                                 1)[0])
        edges = np.polyfit([r["nb"] for r in sel],
                           [r["k_edge"] for r in sel], 1)[0]
        comp = -edges*st["spectrum"]["120"]["dec_per_mode"]
        print(f"\nbeta(comb, c=120) = {beta:.3f} decades/zero | "
              f"edge advance {edges:+.2f} modes/zero | "
              f"composition (advance x decade/mode) = {comp:.3f}",
              flush=True)
        st["identity"] = {"beta": beta, "edge_advance": float(edges),
                          "composition": float(comp)}
    ckpt_key.save("floor_theory_p1", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("floor-theory phase 1 complete", flush=True)
