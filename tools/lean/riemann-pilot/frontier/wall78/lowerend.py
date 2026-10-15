"""What pins Sang's inputs at 0.8745077: the lower end of ell (README round 501).

Round 500 found that with Sang's inputs a lower low side buys only 3.8e-4: the boundary stops at 0.8745077, with the
walls E, 6 kappa ell > 3/4 and ell >= 1/6. This script reads the lower end and computes what lies below it.

The reading. Sang (arXiv 2610.15291, v5) states his range 1/6 <= ell <= 1/5 for the low estimate (lines 498, 569) and
in his admissibility list (line 1144), with 6 kappa ell > 3/4 (line 1148). His introduction gives the reason for the
lower end: the low estimate "permits the total prime length ell to exceed 1/6" (lines 182-183), and B(ell) =
11/12 - ell/4, of which "Longer prime windows improve the candidate boundary" (line 559), is at least 7/8 for
ell <= 1/6. In his source every
other bound below on ell is the supply ell/d > 1/5 or 21/100 of his row count and short gate (lines 807, 1233); and
6 kappa ell > 3/4 has one use, the slope bound "above by 2" (line 1314). Read this way, the lower end is the low side's
range and not the high side's. The reading drops both rows; the slope bound then holds for every ell >= 1/8 (gate R1),
and the supply, the short gate and every other row stay. The release's lemmas that Sang cites are not re-read for
ell < 1/6.

The model is offslice.py's on Sang's slice with the crossing cost on the first branch only (crossing.py), the low side
lowered by s where stated, and the levers, bootstrap and least stage of levers.py. Every number here is a statement
about this exponent system, not a theorem.

Gates (exit status 1 if any fails):
  R1  in exact arithmetic: with ell >= 1/8, kappa >= 13/18, q <= 5/12, l_y < 1/2 and R <= 1, Sang's two slopes
      1 - z0 + q/(12 kappa) and 1 - z0 + q l_y/(36 kappa^2 ell) stay below 2; every optimum in this script has
      ell >= 1/8
  L1  the reading with the release's low side: each of the fifteen configurations within 2e-6 of its recorded value.
      The eight that keep the Gram term are unchanged; Sang's inputs + Gram term removed go from 0.8745078 to
      0.8710998, with all readings from 0.8745012 to 0.8694550, and everything from 0.8613056 to 0.8612731
  L2  the low side removed (s = 10): each configuration within 2e-6 of its recorded value, with ell >= 1/6 and under
      the reading; Sang's inputs give 0.8745077 and 0.87, his principal edge
  L3  Sang's inputs, low side lowered by s: with ell >= 1/6 the boundary is 0.8745077 at s = 1/500, 1/250, 1/200 and
      3/500; under the reading it falls (0.8733461, 0.8718248, 0.8710723, 0.8703257) and first reaches 0.87 at
      s* = 0.00644 (bisection to 1e-6), where the walls are E, the low side and the principal edge, with ell < 1/6;
      with all readings it goes on below 0.87, to 0.8657514 at s = 3/250
"""
import sys
from fractions import Fraction as Fr
from concurrent.futures import ProcessPoolExecutor
import offslice as O
import levers as LV
import crossing as X


class Reading(X.Variant):
    """crossing.Variant (crossing cost on the first branch, low side lowered by s) with the lower end of ell read as
    the low side's range: the rows 'ell>=1/6' and '6k.ell>3/4' dropped."""

    def __init__(self, kappa, read=False, **kw):
        self.read = read
        super().__init__(kappa, **kw)

    def fixed_rows(self):
        rows = super().fixed_rows()
        return [x for x in rows if not (self.read and x[0] in ('ell>=1/6', '6k.ell>3/4'))]


def run(args):
    """levers.py's bootstrap and least stage on Sang's slice."""
    cfg, s, read = args
    kappa, fp = 3 / 4, []
    for _ in range(O.STAGES):
        if kappa < 13 / 18:
            break
        o = Reading(kappa, read=read, s=s, mode='slice', **cfg)
        sol = o.solve()
        if sol is None:
            break
        fp.append((kappa, sol, o))
        if abs(2 * sol['v'][3] - 1 - kappa) < 1e-10:
            break
        kappa = 2 * sol['v'][3] - 1
    least = min(x['v'][3] for _, x, _ in fp)
    i = max(j for j in range(len(fp)) if fp[j][1]['v'][3] <= least + 1e-7)
    kap, sol, o = fp[i]
    return dict(B=sol['v'][3], kappa=kap, v=sol['v'], walls=o.walls(sol), ell_min=min(x['v'][2] for _, x, _ in fp))


READ_LOW = {   # the reading with the release's low side (s = 0)
    "Sang's inputs": 0.8748866, "Sang's inputs + all readings": 0.8748866,
    "Sang's inputs + Gram removed": 0.8710998, "Sang's inputs + Gram removed + all readings": 0.8694550,
    "Sang's inputs + amplifier x2": 0.8741924, "Sang's inputs + amplifier to the caps": 0.8741773,
    "Sang's inputs + DH counts": 0.8701164, "Sang's inputs + DH counts + all readings": 0.8667866,
    "Lindelof on average": 0.8701164, "Lindelof + rotated floor": 0.8700000, "Lindelof + floor 1/1000": 0.8700000,
    "Lindelof + Gram removed": 0.8700000, "Lindelof + all readings": 0.8667866,
    "Lindelof + all readings + Gram removed": 0.8618569, "everything": 0.8612731,
}
NO_LOW = {   # the low side removed: (ell >= 1/6, the reading)
    "Sang's inputs": (0.8745077, 0.8700000), "Sang's inputs + all readings": (0.8745011, 0.8612453),
    "Sang's inputs + Gram removed": (0.8745077, 0.8700000),
    "Sang's inputs + Gram removed + all readings": (0.8745011, 0.8612453),
    "Sang's inputs + amplifier x2": (0.8715333, 0.8700000),
    "Sang's inputs + amplifier to the caps": (0.8715333, 0.8700000),
    "Sang's inputs + DH counts": (0.8700000, 0.8700000),
    "Sang's inputs + DH counts + all readings": (0.8403320, 0.8278539),
    "Lindelof on average": (0.8700000, 0.8700000), "Lindelof + rotated floor": (0.8700000, 0.8700000),
    "Lindelof + floor 1/1000": (0.8700000, 0.8700000), "Lindelof + Gram removed": (0.8700000, 0.8700000),
    "Lindelof + all readings": (0.8339167, 0.8153251), "Lindelof + all readings + Gram removed": (0.8339167, 0.8153251),
    "everything": (0.8339167, 0.8100953),
}
CURVE = {0.002: 0.8733461, 0.004: 0.8718248, 0.005: 0.8710723, 0.006: 0.8703257}
READ_CURVE = (0.012, 0.8657514)   # Sang's inputs + all readings under the reading, low side lowered by 3/250
S_STAR = 0.00644


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    names = [nm for nm, _, _ in LV.CONFIGS]
    cfgs = [cfg for _, cfg, _ in LV.CONFIGS]
    sang = cfgs[names.index("Sang's inputs")]
    jobs = ([(c, 0.0, True) for c in cfgs] + [(c, 10.0, False) for c in cfgs] + [(c, 10.0, True) for c in cfgs]
            + [(sang, s, rd) for rd in (False, True) for s in sorted(CURVE)]
            + [(cfgs[names.index("Sang's inputs + all readings")], READ_CURVE[0], True)])
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = list(ex.map(run, jobs))
    n = len(cfgs)
    rl, nl0, nl1, cv = res[:n], res[n:2 * n], res[2 * n:3 * n], res[3 * n:]

    lo, hi = 0.006, 0.007
    while hi - lo > 1e-6:
        mid = (lo + hi) / 2
        if run((sang, mid, True))['B'] <= 0.87 + 1e-9:
            hi = mid
        else:
            lo = mid
    star = run((sang, hi, True))
    allres = rl + nl0 + nl1 + cv + [star]

    z0, q, ly, k_lo, l_lo = Fr(17, 50), Fr(5, 12), Fr(1, 2), Fr(13, 18), Fr(1, 8)
    slope1 = 1 - z0 + q / (12 * k_lo)
    slope2 = 1 - z0 + q * ly / (36 * k_lo ** 2 * l_lo)
    least_ell = min(r['ell_min'] for r in allres)
    gate('R1', slope1 < 2 and slope2 < 2 and least_ell >= 1 / 8,
         f'slopes without 6 kappa ell > 3/4 at ell >= 1/8: {slope1} = {float(slope1):.4f} and {slope2} = '
         f'{float(slope2):.4f}, both below 2; least ell at any stage here {least_ell:.5f}')

    dev, kept, lines = 0.0, True, []
    for (nm, cfg, rec), r in zip(LV.CONFIGS, rl):
        dev = max(dev, abs(r['B'] - READ_LOW[nm]))
        if cfg.get('gram', 'paper') == 'paper':
            kept &= abs(r['B'] - rec[0]) < 2e-6
        if READ_LOW[nm] < rec[0] - 1e-6:
            lines.append(f'{nm} {rec[0]:.7f} -> {r["B"]:.7f} (ell {r["v"][2]:.5f}, walls {", ".join(r["walls"])})')
    gate('L1', dev < 2e-6 and kept, f'the reading with the release\'s low side: fifteen configurations within '
                                    f'{dev:.1e} of the records; the eight with the Gram term unchanged; '
                                    + '; '.join(lines))

    dev0 = max(abs(r['B'] - NO_LOW[nm][0]) for nm, r in zip(names, nl0))
    dev1 = max(abs(r['B'] - NO_LOW[nm][1]) for nm, r in zip(names, nl1))
    s0r, s1r = nl0[names.index("Sang's inputs")], nl1[names.index("Sang's inputs")]
    gate('L2', dev0 < 2e-6 and dev1 < 2e-6,
         f'the low side removed: fifteen configurations within {dev0:.1e} (ell >= 1/6) and {dev1:.1e} (the reading) of '
         f'the records; Sang\'s inputs {s0r["B"]:.7f} (walls {", ".join(s0r["walls"])}) and {s1r["B"]:.7f} '
         f'(walls {", ".join(s1r["walls"])}, ell {s1r["v"][2]:.5f})')

    k = len(CURVE)
    flat, fall, allr = cv[:k], cv[k:2 * k], cv[2 * k]
    ok = (all(abs(r['B'] - 0.8745077) < 2e-6 for r in flat)
          and all(abs(r['B'] - CURVE[s]) < 2e-6 for r, s in zip(fall, sorted(CURVE)))
          and abs(hi - S_STAR) < 1e-5 and abs(star['B'] - 0.87) < 1e-9 and star['v'][2] < 1 / 6
          and set(star['walls']) == {'E', 'low side', 'principal edge'} and abs(allr['B'] - READ_CURVE[1]) < 2e-6)
    gate('L3', ok, f'Sang\'s inputs, low side lowered by s = 1/500, 1/250, 1/200, 3/500: with ell >= 1/6 ' +
         ', '.join(f'{r["B"]:.7f}' for r in flat) + '; under the reading ' +
         ', '.join(f'{r["B"]:.7f}' for r in fall) + f'; the edge 0.87 first at s* = {hi:.6f}, ell {star["v"][2]:.5f}, '
         f'walls {", ".join(star["walls"])}; with all readings, s = 3/250: {allr["B"]:.7f}')

    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
