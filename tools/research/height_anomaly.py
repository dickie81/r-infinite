#!/usr/bin/env python3
"""The anomaly attack (commissioned after the height arc's first
RESULT): why does the A = 1.5 rung sit 4-5 decades BELOW the
height-uniform matched-deficit scale?

Hypotheses on record (height_uniformity.py RESULT (4)):
  H1 MIRROR PROXIMITY (instrument geometry): at tau0 ~ 110-130,
     A = 1.5, the reflected ordinates -gamma sit at s =
     A(gamma + tau0) >= 186 -- only ~66 s-units beyond the band
     edge c = 120, inside leakage reach -- adding effective
     constraints the band count does not see. At A >= 2 the
     mirrors sit 400+ s-units out.
  H2 LOW-HEIGHT STATISTICS: the zeros at heights 90-170 carry
     different spacing statistics.

Experiments:
  E1 MIRROR ABLATION (decisive): the A = 1.5 ladder with the
     mirror set REMOVED from the form (direct-side ordinates and
     statistics untouched). Anomaly vanishes -> H1; persists ->
     H2. Control: the same ablation at A = 2.5 (mirrors far;
     ablation must change nothing within noise).
  E2 THE MIRROR PRESSURE, quantified per rung at the crossing:
     mirror counts within |s| <= c + W (W = 50, 100), the mirror
     form's Frobenius norm and top generalized eigenvalue on the
     section, and its value on the with-mirror minimizer -- the
     "unseen constraint" strength, comparable across apertures.

Check 7: finite linear algebra on the committed section machinery.
Check 8: no hypothesis input. Keying per the standing law (A361):
DEPS = the producing modules (incl. height_uniformity.py, whose
ASect this imports); params carry the config + z_sha.

RESULT (E1 + the follow-on E3 gradient test; both hypotheses on
the commissioning record are REFUTED and the anomaly is RESOLVED):

  E1 MIRROR ABLATION -- H1 refuted, with the sign lesson: Q_mirror
     is PSD, so mirrors can only RAISE margins (m_full >= m_dir
     identically); the ablated margins are MORE anomalous (m_dir /
     m_full = 0.003-0.8 on the A = 1.5 ladder), and the far-mirror
     control moves <= 3%. Mirror proximity cannot produce a
     depression; the commissioning hypothesis had the sign
     backwards.
  E3 THE GRADIENT TEST -- H3 (deterministic band geometry)
     CONFIRMED, H2 (low-height statistics) refuted with it: the
     smooth-counting comb (inv_Nbar positions -- the density
     gradient with NO fluctuations) reproduces the anomalous depth
     at both A = 1.5 points (7.5e-12 vs the zeros' 4.7e-11 at
     tau0 = 116.5; 3.4e-7 vs 1.5e-7 at 130) while the
     constant-density comb sits 7-9 DECADES higher (1.0e-2 /
     2.26); at the A = 3 control all three agree within 2x.
     MECHANISM: at A = 1.5 the local Nyquist line L(gamma) = 2A
     sits at gamma = 126, INSIDE the +-80 band -- the low-gamma
     side is sub-Nyquist (free directions) at every tau0 near the
     crossing, so the transition smears across the band instead of
     being a sharp tau0-event. The relative density variation
     across the band scales like (c/A)/tau* -- negligible for
     A >= 2 at c = 120, order-unity at A = 1.5.
     (The minimizer band-position diagnostic returned
     high-gamma-edge peaks, opposite the naive sub-Nyquist-camp
     expectation -- recorded, not interpreted; the margin verdict
     does not rest on it.)

NET: the height-uniformity RESULT's low-height anomaly is a
COMPUTABLE, deterministic geometry correction (the band-integrated
local deficit replaces the point deficit when the band straddles
the local Nyquist line), not a height effect and not arithmetic:
the uniformity claim strengthens -- no measured deviation from
height uniformity remains anywhere in the arc.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import zeros380
from fold_surrogate import psi_hat_batch
from height_uniformity import ASect, ext_zeros_to


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSA = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "height_uniformity.py",
    "height_anomaly.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")


def _zsha(a):
    return hashlib.sha256(
        np.ascontiguousarray(a).tobytes()).hexdigest()[:16]


C0 = 120.0
LADDERS_AB = [
    (1.5, [100.0, 110.0, 112.0, 116.5, 120.0, 130.0, 140.0], 380),
    (2.5, [550.0, 630.0, 715.0], 810),          # far-mirror control
]


def forms(S, Z, tau0, Ap):
    """Direct-only and mirror-only forms plus the G matrix."""
    G = Ap*S.gram
    sd = (Z - tau0)*Ap
    sm = (-Z - tau0)*Ap
    Vd = psi_hat_batch(S.P, sd)*Ap
    Vm = psi_hat_batch(S.P, sm)*Ap
    Qd = Vd @ Vd.conj().T
    Qd = (Qd + Qd.conj().T)/2
    Qm = Vm @ Vm.conj().T
    Qm = (Qm + Qm.conj().T)/2
    return G, Qd, Qm


def run():
    Z380 = zeros380()
    S = ASect(C0)
    for Ap, t0s, kmax in LADDERS_AB:
        ZE = ext_zeros_to(kmax)
        Z = np.concatenate([Z380, ZE]) if len(ZE) else Z380
        params = {"deps": DEPSA, "A": Ap, "c": C0, "t0s": t0s,
                  "kmax": kmax, "z_sha": _zsha(Z)}
        name = f"anom_A{Ap:.1f}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            rows = []
            for t0 in t0s:
                G, Qd, Qm = forms(S, Z, t0, Ap)
                Q = Qd + Qm
                evF, VF = scipy_eigh(Q, G)
                m_full, wF = float(evF[0]), VF[:, 0]
                m_dir = float(scipy_eigh(Qd, G, eigvals_only=True)[0])
                # mirror pressure
                sm = np.abs((-Z - t0)*Ap)
                n50 = int(np.sum(sm <= C0 + 50))
                n100 = int(np.sum(sm <= C0 + 100))
                lam_m = float(scipy_eigh(Qm, G, eigvals_only=True)[-1])
                mir_on_min = float(np.real(np.conj(wF) @ Qm @ wF))
                rows.append({"t0": t0, "m_full": m_full,
                             "m_dir": m_dir,
                             "ratio": m_full/m_dir if m_dir > 0 else None,
                             "n50": n50, "n100": n100,
                             "frob_m": float(np.linalg.norm(Qm)),
                             "lam_m": lam_m,
                             "mir_on_min": mir_on_min})
            st = {"A": Ap, "rows": rows}
            ckpt_key.save(name, KEYFILE, params, st)
        print(f"== A={Ap:.1f}:", flush=True)
        for r in st["rows"]:
            print(f"   t0={r['t0']:6.1f}: m_full {r['m_full']:+.3e} "
                  f"m_dir {r['m_dir']:+.3e} "
                  f"(x{r['m_dir']/max(r['m_full'],1e-300):.1e}) | "
                  f"mir n50/n100 {r['n50']}/{r['n100']} "
                  f"frob {r['frob_m']:.2e} lam {r['lam_m']:.2e} "
                  f"on-min {r['mir_on_min']:.2e}", flush=True)


if __name__ == "__main__":
    run()
    print("anomaly probes complete", flush=True)
