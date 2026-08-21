#!/usr/bin/env python3
"""Theorem 1bg verifier: the floor arc -- the Slepian floor law for
the dodging margin, the conjugacy structure of the certified
arithmetic build, the operator-level closure of the windowed
explicit formula on concentrated sections, and the end-to-end
derivation of the certified 1bf g4 proximity as pure horizon
mismatch.

The chain (four commissioned attacks, each with its committed
instrument and RESULT):
(1) THE FLOOR LAW (floor_probe.py / floor_probe2.py): on tau0
    ladders at c = 60 and 120 (52 points), the truncated dodging
    margin obeys m_Z ~ m_sat 10^(-beta (N* - nb)) on the climb,
    with the pinning count N* equal to the Shannon number 2c/pi
    to 1-2%, beta = 1.2-1.5 decades per in-band zero, and
    beta/(Slepian plunge rate) ~ 2.4 at BOTH c under the landing
    recipe [round-234 F1: struck on the paper at 359579b -- a
    (recipe, basis)-conditioned ratio, not a structural constant;
    retained here only as the landing stage's pin description]. Below the
    horizon the margin is numerical zero (free directions inside
    the concentrated subspace); on the climb the minimizer
    migrates into the plunge; at saturation (m ~ 0.25 at c = 120)
    it is concentrated again. The certified deep margins are the
    plunge attenuation, quantitatively.
(2) THE CONJUGACY (floor_probe3.py): the certified 1bb-lineage
    arithmetic build satisfies Q_W_code ~= conj(Q_Z) (defect
    0.2-0.7%) -- equivalently (machine-exact parity algebra) the
    zero form with the ordinates reflected about tau0. All the
    arc's mysteries follow: isospectrality (the g4 proximity),
    w_W = conj(w_Z) (conjugate overlap 1.0000), the antisymmetry
    T(w_Z) = -T(w_W), the pencil symmetry.
(3) THE GAUGE VERDICT + PARTITION REFUTATION (floor_probe4.py):
    rebuilding ARCH in the true gauge (complex vhat) gives
    ||ARCH_true - conj(ARCH_code)|| = 0 to machine precision
    (measured ~3e-12 relative; round-234 F3): the build is the
    CONJUGATE of the explicit-formula operator (a phase-gauge
    convention; every certified scalar is conjugation-blind), and
    the "reflection identity" deflates to the plain windowed
    explicit formula. The formula is window-local (beta(T)
    plateaus at -1 from T ~ 400), per-prime resolved (beta_n = -1
    for every prime power of non-tiny norm), and tail-free (280
    further ordinates project at 0.0000; round-234 F2 -- the
    landing's 269 was the T = 1000 trajectory count).
(4) THE DEFECT CLOSURE (floor_probe5.py): the residual is the
    arch/zero HORIZON MISMATCH, entirely -- quadrature share zero
    (NR/2 = base = NRx2 to every printed digit; round-235 F7);
    matching the arch window to the ordinate coverage
    collapses the defect 40-70x, and with
    the 660-ordinate list at matched +-1013 it is 2-3e-5,
    tau0-uniform. The g4 ratio dm/m = +0.019/+0.047/+0.001 at the
    code windows -> -0.000/-0.001/+0.000 matched: THE CERTIFIED
    g4 OBSERVATION IS A DERIVED QUANTITY.

Stage: floor_landing.landing_stage() (the producing code is in
the substrate per round-229 F7), content-addressed on all ten
module shas + the config + the content of both ordinate lists
(z_sha and zext_sha, round-235 F1); sub-stages are content-keyed
(the landing shares no keys with the attack instruments'
intent-keyed runs -- round-235 F4). The landing battery runs the stage
fresh once (CASCADE_COMPUTE=fresh), per the instrument rules.

Gates:
  g0  pins set
  g1  regimes pinned: below-horizon |m_Z| < 1e-11; climb
      1.150e-9 / 1.139e-7 / 3.760e-4 (rel 0.05); the c = 120
      saturation plateau within (0.250, 0.258)
  g2  the pinning count: N* / N_sh in (0.94, 1.03) at both c
  g3  the climb rate: beta in (1.0, 1.6) decades/zero and
      beta/plunge in (2.2, 2.6) at both c
  g4  the c-ratio pin (the 'Landau-Widom scaling' reading is
      struck, round-234 F1/round-235 F5): the c60/c120 ratios of
      beta and of the plunge rate each within 10% of ln 120/ln 60
  g5  the minimizer migration: plunge mass < 0.02 below the
      horizon, in (0.30, 0.60) at (120,340), < 0.05 at saturation
  g6  the conjugacy: rel_conj pinned (rel 0.3) and < 1e-2 at the
      four regime points; rel_raw > 0.5 at each; the parity
      identity < 1e-12
  g7  w_W = conj(w_Z): conjugate overlap > 0.999 at all four
      points; plain overlap < 0.7
  g8  the g4 accounting: |dm - D(conj w_Z)| / |dm| < 0.15 at the
      four points (first-order perturbation in the defect closes)
  g9  the gauge verdict: ||ARCH_true - conj(ARCH_code)|| < 1e-4
      rel; true-orientation vs Q_Z < 0.008 with crossed pairs
      > 0.4 at the three defect points
  g10 the partition refutation: beta(T = 400) and beta(653.7)
      within 0.01 of -1; |beta(tail)| < 1e-3; per-prime beta_n
      within 0.15 of -1 for every prime power of norm > 1.5
  g11 the defect closure: MATCHED rel < 2e-4 and ext-MATCH rel
      < 5e-5 at all three points; NR invariance (base vs NR/2
      rel difference < 1e-5)
  g12 the margin closure: |dm/m| < 0.002 at ext-MATCH at all
      three points (the g4 ratio vanishes under matching)
  g13 the chain obligation to cascade_twosided_witness.py
      (Theorem 1bf) met
  g14 the 1bg paper needles and the footer census (backticked
      >= 2; the anchored count and range needles)

Sabotage suite (live at the landing battery; edit-run-observe-
restore; the family keying localizes the recompute cost):
  (a) substrate mangle -- floor_probe3.py conj_point's conjugation
      target (D = QW - conj(QZ) -> QW - QZ; the originally planned
      parity-sign mangle is undetectable by construction, a global
      sign cancels in P Q P, and was replaced) -> OBSERVED: the
      conjugacy family + DEPSL-keyed stages self-invalidate and
      recompute (~13 min; ladders and defect families REUSE),
      g6+g8 FAIL, exit 1. Incident on the record: the second fresh
      battery's wrapper had a pending final tick that auto-
      committed the probe's mangled-KEY checkpoint data files
      (never the mangled source); swept by the reachability pass
      -- probes now wait for WRAPPER-COMPLETE.
  (b) pin mangle -- g1 climb pin 1.150e-9 -> 2.150e-9 ->
      OBSERVED: REUSED, g1 FAIL alone, exit 1
  (c) census revert -- footer 83 -> 82 -> OBSERVED: the chain
      gate prints the missing census string, g13 + g14 FAIL,
      exit 1 (two-gate detection)
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from floor_landing import load_or_run

PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

st = load_or_run()
F, R = st["fits"], st["regimes"]
CJ, GA, DF, PT = st["conj"], st["gauge"], st["defects"], st["partition"]

print(f"  fits: c60 beta {F['60']['beta']:.3f} N* {F['60']['nstar']:.1f}"
      f"/{F['60']['nsh']:.1f} ratio {F['60']['ratio']:.2f} | c120 "
      f"beta {F['120']['beta']:.3f} N* {F['120']['nstar']:.1f}"
      f"/{F['120']['nsh']:.1f} ratio {F['120']['ratio']:.2f}", flush=True)
print(f"  regimes: below {R['below']:.1e} climb {R['climb1']:.3e}/"
      f"{R['climb2']:.3e}/{R['climb3']:.3e} sat [{R['sat_lo']:.3f},"
      f"{R['sat_hi']:.3f}] pm {R['pm_below']:.3f}/{R['pm_mid']:.3f}/"
      f"{R['pm_sat']:.3f}", flush=True)
for p in CJ:
    print(f"  conj ({p['c']:.0f},{p['t0']:.0f}): rel {p['rel_conj']:.4f} "
          f"raw {p['rel_raw']:.3f} ovc {p['ov_conj']:.4f} "
          f"dm {p['dm']:+.2e} D {p['D_conjwZ']:+.2e}", flush=True)
for g in GA:
    print(f"  gauge ({g['c']:.0f},{g['t0']:.0f}): archg {g['arch_gauge']:.6f} "
          f"tQZ {g['true_vs_QZ']:.4f} tcQZ {g['true_vs_cQZ']:.3f} "
          f"cQZ {g['code_vs_QZ']:.3f}", flush=True)
for k, v in sorted(DF.items()):
    print(f"  defect {k}: rel {v['rel']:.5f} dm/m "
          f"{v['dm_rel'] if v['dm_rel'] is not None else 0:+.4f}", flush=True)
print(f"  partition: beta400 {PT['betas']['400.0']:+.4f} beta653 "
      f"{PT['betas']['653.7']:+.4f} btail {PT['btail']:+.5f} "
      f"per-n n={len(PT['per_n'])}", flush=True)

# ---------------------------------------------------------------- g0
PIN_CLIMB = [1.150e-9, 1.139e-7, 3.760e-4]
PIN_CONJ = [0.0022, 0.0032, 0.0037, 0.0069]
gate("g0 pins set", all(v is not None for v in PIN_CLIMB + PIN_CONJ))

# ---------------------------------------------------------------- g1
ok = abs(R["below"]) < 1e-11
ok &= all(abs(v/p - 1) < 0.05 for v, p in
          zip((R["climb1"], R["climb2"], R["climb3"]), PIN_CLIMB))
ok &= 0.250 < R["sat_lo"] and R["sat_hi"] < 0.258
gate("g1 regimes pinned: numerical zero below the horizon; the "
     "climb points; the c=120 saturation plateau", ok)

# ---------------------------------------------------------------- g2
ok = all(0.94 < F[c]["nstar"]/F[c]["nsh"] < 1.03 for c in ("60", "120"))
gate("g2 the pinning count N* = the Shannon number 2c/pi (1-2% "
     "measured; gated 6%/3%)", ok)

# ---------------------------------------------------------------- g3
ok = all(1.0 < F[c]["beta"] < 1.6 for c in ("60", "120"))
ok &= all(2.2 < F[c]["ratio"] < 2.6 for c in ("60", "120"))
gate("g3 the climb rate: beta in (1.0, 1.6) decades/zero; "
     "beta/plunge in (2.2, 2.6) at both c", ok)

# ---------------------------------------------------------------- g4
lw = math.log(120)/math.log(60)
rb = F["60"]["beta"]/F["120"]["beta"]
rp = F["60"]["plunge"]/F["120"]["plunge"]
ok = abs(rb/lw - 1) < 0.10 and abs(rp/lw - 1) < 0.10
gate("g4 the c-ratios of beta and of the plunge rate within 10% "
     "of ln120/ln60 (a pin of the landing recipe; the Landau-Widom "
     "interpretation is struck per the paper (ii) correction -- "
     "round-234 F1)", ok)

# ---------------------------------------------------------------- g5
ok = R["pm_below"] < 0.02 and 0.30 < R["pm_mid"] < 0.60 \
     and R["pm_sat"] < 0.05
gate("g5 the minimizer migration: concentrated below the horizon, "
     "plunge-dwelling mid-climb, concentrated at saturation", ok)

# ---------------------------------------------------------------- g6
ok = all(abs(p["rel_conj"]/pin - 1) < 0.3
         for p, pin in zip(CJ, PIN_CONJ))
ok &= all(p["rel_conj"] < 1e-2 and p["rel_raw"] > 0.5 for p in CJ)
ok &= all(p["rel_parity_ident"] < 1e-12 for p in CJ)
gate("g6 the conjugacy Q_W_code ~= conj(Q_Z): defects pinned, "
     "raw > 0.5, the parity identity machine-exact", ok)

# ---------------------------------------------------------------- g7
ok = all(p["ov_conj"] > 0.999 and p["ov_plain"] < 0.7 for p in CJ)
gate("g7 w_W = conj(w_Z): conjugate overlap > 0.999 at the four "
     "regime points (plain overlap < 0.7)", ok)

# ---------------------------------------------------------------- g8
ok = all(abs(p["dm"] - p["D_conjwZ"]) < 0.15*abs(p["dm"])
         for p in CJ)
gate("g8 the g4 accounting: m_W - m_Z = D(conj w_Z) to 15% at "
     "every regime point (first-order in the defect)", ok)

# ---------------------------------------------------------------- g9
ok = all(g["arch_gauge"] < 1e-4 for g in GA)
ok &= all(g["true_vs_QZ"] < 0.008 for g in GA)
ok &= all(g["true_vs_cQZ"] > 0.4 and g["code_vs_QZ"] > 0.4
          for g in GA)
gate("g9 the gauge verdict: ARCH_true = conj(ARCH_code) to machine "
     "precision (~3e-12 measured; gated < 1e-4); the true orientation "
     "satisfies the formula directly", ok)

# --------------------------------------------------------------- g10
ok = abs(PT["betas"]["400.0"] + 1) < 0.01
ok &= abs(PT["betas"]["653.7"] + 1) < 0.01
ok &= abs(PT["btail"]) < 1e-3
ok &= all(abs(b + 1) < 0.15 for _, b in PT["per_n"])
gate("g10 the partition refutation: window-local beta = -1, the "
     "tail invisible, per-prime beta_n = -1", ok)

# --------------------------------------------------------------- g11
ok = all(DF[f"MATCHED|{c:.0f}|{t0:.0f}"]["rel"] < 2e-4
         for c, t0 in ((60, 200), (120, 300), (120, 420)))
ok &= all(DF[f"ext-MATCH|{c:.0f}|{t0:.0f}"]["rel"] < 5e-5
          for c, t0 in ((60, 200), (120, 300), (120, 420)))
ok &= abs(DF["base|60|200"]["rel"] - DF["NR-2|60|200"]["rel"]) < 1e-5
gate("g11 the defect closure: matched horizons collapse the defect "
     "(< 2e-4; ext-matched < 5e-5, tau0-uniform); quadrature share "
     "zero", ok)

# --------------------------------------------------------------- g12
ok = all(abs(DF[f"ext-MATCH|{c:.0f}|{t0:.0f}"]["dm_rel"]) < 2e-3
         for c, t0 in ((60, 200), (120, 300), (120, 420)))
gate("g12 the margin closure: the g4 ratio |dm/m| < 0.002 under "
     "matched horizons at every point (derived, not observed)", ok)

# --------------------------------------------------------------- g13
from cascade_tower import chain_ok
gate("g13 the chain obligation to cascade_twosided_witness.py "
     "(Theorem 1bf) met", chain_ok("cascade_twosided_witness.py"))

# --------------------------------------------------------------- g14
import re
normp = re.sub(r"\s+", " ", paper)
plain = normp.replace("**", "")
needles = [
    "Theorem 1bg (the floor arc",
    "the floor law",
    "the pinning count is the Shannon number",
    "the plain windowed explicit formula seen through that",
    "the horizon mismatch, entirely",
    "a derived quantity, not an observation",
    "no RH leverage claimed",
]
ok = all(nd in plain for nd in needles)
for nd in needles:
    if nd not in plain:
        print(f"  g14 MISSING: {nd!r}", flush=True)
ok &= paper.count("`cascade_floor_closure.py`") >= 2
ok &= "the **85 scripts cited in place** above" in normp
ok &= "extended by Theorems 1i–1bi:" in normp
gate("g14 the 1bg paper needles and the footer census (backticked "
     ">= 2; the anchored count and range needles)", ok)

print(("\nALL GATES PASS (15/15)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
