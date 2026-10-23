#!/usr/bin/env python3
"""val_extra.py -- independent cross-checks and sabotage tests for dh_census.py, on t <= 200 only.

  python3 val_extra.py rect   [--t0 1 --t1 200 --delta 0.001]  argument principle for f around the
                                                              rectangle [1/2+delta, 2] x [t0, t1]
  python3 val_extra.py tail   REF.jsonl                       close (T1, 200]: N at 200, roots in between
  python3 val_extra.py dirl   REF.jsonl                       channel roots re-checked with acb.dirichlet_l
  python3 val_extra.py compare REF.jsonl OTHER.jsonl          same roots / off-line zeros?  (tolerance 1e-8)
  python3 val_extra.py run    OUT.jsonl MODE [--t0 1 --t1 200 --dt 25]
        MODE = fine      64 samples per spacing (4x the instrument's density)
               coarse    2 samples per spacing, H_CAP 0.6: forces missed roots -> repair path
               nogolden  2 samples per spacing and no close-pair detection: repair by re-sampling only
               harsh     0.75 samples per spacing (ends may shift by 2): many missed roots ->
                         count repair by bisection + re-sampling; f misses go through _locate
               harsh_nogolden  the same without close-pair detection
               nodips    Newton starts from dips disabled: off-line zeros via bisection + |f| grid
"""
import argparse
import json
import math
import sys

from flint import acb, arb, ctx, dirichlet_char

import dh_census as D

CEIL = 200.0   # pre-registration: nothing above this height


def track_polyline(ev, verts, max_inc=0.25):
    """Continuous change of arg f along the polyline verts (complex vertices)."""
    tot = 0.0
    for z0, z1 in zip(verts, verts[1:]):
        F = ev.values(z0.real, z0.imag)[0]
        u, step = 0.0, 0.01
        while u < 1.0:
            un = min(1.0, u + step)
            z = z0 + (z1 - z0) * un
            G = ev.values(z.real, z.imag)[0]
            inc = float((G / F).arg())
            if abs(inc) >= max_inc:
                step *= 0.5
                if step < 1e-12:
                    raise RuntimeError("tracking failed near %r" % z)
                continue
            tot += inc
            u, F = un, G
            step = min(0.05, step * 1.5)
    return tot


def rect(t0, t1, delta):
    """Zeros of f in [1/2 + delta, 2] x [t0, t1] by the argument principle (counter-clockwise)."""
    assert t1 <= CEIL
    ev = D.Evaluator(53, 1, ceiling=CEIL)
    s = 0.5 + delta
    verts = [complex(s, t0), complex(2.0, t0), complex(2.0, t1), complex(s, t1), complex(s, t0)]
    tot = track_polyline(ev, verts)
    return tot / (2 * math.pi), dict(ev.nevals)


def tail(ref):
    """Zeros of f, chi, chibar in (T1_last, 200]: counts at 200 by phase tracking, roots by dense
    sampling (step h/4) between."""
    recs, _, _ = D.load_records(ref)
    last = recs[-1]
    c = D.Census(last["params"]["t0"], CEIL, last["params"]["dt"], last["params"]["prec"], "/dev/null")
    c.ev = D.Evaluator(53, 1, ceiling=CEIL)
    c.ra = D.real_axis_data(c.ev)
    c.S, c.Ncache, c.flags, c.diag = {}, {}, set(), D.collections.Counter()
    T = CEIL
    a = last["T1"]
    h = D.h_of_t(T) / 4
    n = int(math.ceil((T - a) / h))
    ts = [a + (T - a) * j / n for j in range(n + 1)]
    for t in ts:
        c._sample(t)
    c.known, c.golden_cache = [[], [], []], {}
    out = {"from": a, "to": T}
    Na = (tuple(last[k][0] for k in ("Nf1", "Nchi1", "Nchib1")),
          tuple(last[k][1] for k in ("Nf1", "Nchi1", "Nchib1")))
    raw, ints, ok, par = c._N_at(T)
    out["N_at_200"] = {"raw": raw, "int": ints, "integral": ok, "parity": par}
    for ch in range(3):
        roots, dips = c._detect(ch, ts)
        out["roots_" + D.NAMES[ch]] = roots
        out["dN_" + D.NAMES[ch]] = ints[ch] - Na[1][ch]
    out["K_tail"] = (out["dN_f"] - len(out["roots_f"])) / 2
    return out


def dirl(ref):
    """|L(1/2 + i gamma, chi)| at the Z_chi roots (and chibar) through flint's dirichlet_l, an
    implementation independent of the Hurwitz construction; also |f| at the Z_f roots."""
    recs, _, _ = D.load_records(ref)
    chi, chib = dirichlet_char(5, 2), dirichlet_char(5, 3)
    worst = {"chi": 0.0, "chibar": 0.0, "f": 0.0}
    k = D.Consts(53, 1)
    with ctx.workprec(53):
        for r in recs:
            for g in r["roots_chi"]:
                worst["chi"] = max(worst["chi"], float(abs(acb.dirichlet_l(acb(0.5, g), chi))))
            for g in r["roots_chibar"]:
                worst["chibar"] = max(worst["chibar"], float(abs(acb.dirichlet_l(acb(0.5, g), chib))))
            for g in r["roots_f"]:
                s = acb(0.5, g)
                fv = (1 - k.i * k.kappa) / 2 * acb.dirichlet_l(s, chi) + \
                     (1 + k.i * k.kappa) / 2 * acb.dirichlet_l(s, chib)
                worst["f"] = max(worst["f"], float(abs(fv)))
    return worst


def compare(ref, other, tol=1e-8):
    """Pool the roots of both files over the common height range and compare them one to one."""
    A, _, _ = D.load_records(ref)
    B, _, _ = D.load_records(other)
    lo = max(A[0]["T0"], B[0]["T0"])
    hi = min(A[-1]["T1"], B[-1]["T1"])
    res = {"range": [lo, hi]}
    for key in ("roots_f", "roots_chi", "roots_chibar"):
        ra = sorted(x for r in A for x in r[key] if lo < x < hi)
        rb = sorted(x for r in B for x in r[key] if lo < x < hi)
        same = len(ra) == len(rb) and all(abs(x - y) < tol for x, y in zip(ra, rb))
        res[key] = {"n": [len(ra), len(rb)], "same": same,
                    "max_diff": max((abs(x - y) for x, y in zip(ra, rb)), default=0.0)}
    oa = sorted(tuple(o[:2]) for r in A for o in r["offline"] if lo < o[1] < hi)
    ob = sorted(tuple(o[:2]) for r in B for o in r["offline"] if lo < o[1] < hi)
    res["offline"] = {"n": [len(oa), len(ob)],
                      "same": len(oa) == len(ob) and all(abs(complex(*x) - complex(*y)) < tol
                                                         for x, y in zip(oa, ob))}
    res["flags"] = [[r["k"], r["flags"]] for r in B if r["flags"]]
    tot = D.collections.Counter()
    for r in B:
        tot.update({k: v for k, v in r["diag"].items() if not k.startswith("min_")})
    mins = [r["diag"]["min_track_step"] for r in B if "min_track_step" in r["diag"]]
    res["diag_total"] = dict(tot, min_track_step=min(mins) if mins else None)
    return res


def run(out, mode, t0, t1, dt):
    assert t1 <= CEIL
    if mode == "fine":
        D.SAMPLES_PER_SPACING, D.H_CAP = 64, 0.025
    elif mode == "coarse":
        D.SAMPLES_PER_SPACING, D.H_CAP = 2, 0.6
    elif mode == "nogolden":
        D.SAMPLES_PER_SPACING, D.H_CAP, D.CLOSE_RATIO = 2, 0.6, 0.0
    elif mode == "harsh":
        D.SAMPLES_PER_SPACING, D.H_CAP, D.SHIFT = 0.75, 3.0, 2.0
    elif mode == "harsh_nogolden":
        D.SAMPLES_PER_SPACING, D.H_CAP, D.SHIFT, D.CLOSE_RATIO = 0.75, 3.0, 2.0, 0.0
    elif mode == "nodips":
        D.Census._try_dips = lambda self, a, b, need: None
    else:
        raise SystemExit("unknown mode " + mode)
    D.Census(t0, t1, dt, 53, out).run()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd")
    ap.add_argument("args", nargs="*")
    ap.add_argument("--t0", type=float, default=1.0)
    ap.add_argument("--t1", type=float, default=200.0)
    ap.add_argument("--dt", type=float, default=25.0)
    ap.add_argument("--delta", type=float, default=0.001)
    a = ap.parse_args()
    if a.cmd == "rect":
        n, ev = rect(a.t0, a.t1, a.delta)
        print(json.dumps({"rect": [0.5 + a.delta, 2.0, a.t0, a.t1], "zeros": n, "evals": ev}))
    elif a.cmd == "tail":
        print(json.dumps(tail(a.args[0])))
    elif a.cmd == "dirl":
        print(json.dumps(dirl(a.args[0])))
    elif a.cmd == "compare":
        print(json.dumps(compare(a.args[0], a.args[1]), indent=1))
    elif a.cmd == "run":
        run(a.args[0], a.args[1], a.t0, a.t1, a.dt)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
