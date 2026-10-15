"""The high side's lower end in ell, after re-reading the release's statements (README round 502).

Round 501 read Sang's lower end ell >= 1/6 as the low side's range and dropped it with 6 kappa ell > 3/4. The release's
lemmas that Sang cites were not re-read for ell < 1/6. README round 502 re-reads their statements: none of those Sang
imports for his high side bounds the prime length below beyond ell >= 0. It also re-reads Sang's high side (arXiv
2610.15291, v5).
Its conditions that bound ell below are four. The supply ell/d > 1/5 of his row count (line 807) and his short gate,
with ell/(h + zeta) > 21/100 (lines 997, 1150), stay. 6 kappa ell > 3/4 (line 1148) and l_y < 1/2 (line 1151) serve
one slope bound, "above by 2" (lines 1314-1318); on his geometry (lines 498-503) l_y < 1/2 is ell > b. This script
drops l_y < 1/2 as well and computes where ell then stops.

The model is lowerend.py's: offslice.py's on Sang's slice, with the crossing cost on the first branch only
(crossing.py), the low side lowered by s where stated, and levers.py's levers, bootstrap and least stage. Every number
here is a statement about this exponent system, not a theorem.

Gates (exit status 1 if any fails):
  F1  in exact arithmetic on Sang's geometry l_x = (1-b-ell)/2, l_y = (1+b-ell)/2, h = (1+b+3 ell)/2, at every point
      of a grid of rationals 0 <= b <= 1/5, 1/10 <= ell <= 1/5: ell/h - 1/5 = (7 ell - 1 - b)/(5 (1+b+3 ell)),
      ell/h - 21/100 = (137 ell - 21 (1+b))/(100 (1+b+3 ell)) and 1/2 - l_y = (ell - b)/2. So on his slice the supply
      is ell > (1+b)/7, his 21/100 is ell > 21 (1+b)/137, and l_y < 1/2 is ell > b
  F2  round 501's reading with l_y < 1/2 also dropped. The fifteen configurations with the release's low side and
      with it removed, Sang's inputs at the five points of lowerend.py's L3, and Sang's inputs + all readings at
      s = 3/500, 1/125, 1/100, 3/250, 2/125 and 1/50: each boundary within 1e-9 of the reading with the row kept.
      The kept reading agrees with lowerend.py's records within 2e-6
  F3  at every stage of every run in F2, Sang's two slope bounds 1 - z0 + q/(12 kappa) and
      1 - z0 + q l_y/(36 kappa^2 ell), with the stage's own kappa, l_y and ell (q = 5/12, R <= 1), are below 2; the
      largest is 0.7265. In exact arithmetic, at ell >= 1/8, kappa >= 13/18 and l_y < 1 (on the slice l_x > ell
      gives l_y < 1 - 2 ell), the second is below 7077/8450 and the first at most 1841/2600
  F4  with the low side removed, under the reading, everything's optimum sits on the supply: ell = 1/7 with b = 0,
      with l_y < 1/2 kept and dropped (within 1e-6), below the principal edge. 1/7 is the least ell at any stage of
      F2, which F1's floor (1+b)/7 bounds below. Sang's inputs stop at the edge 0.87 in both runs, where ell is not
      unique: the solver's optimum has ell = 21/137 with the row kept and 0.1592 with it dropped
"""
import sys
from fractions import Fraction as Fr
from concurrent.futures import ProcessPoolExecutor
import offslice as O
import levers as LV
import lowerend as LE


class Reading(LE.Reading):
    """lowerend.Reading, with Sang's l_y < 1/2 dropped as well when drop_ly is set."""

    def __init__(self, kappa, drop_ly=False, **kw):
        self.drop_ly = drop_ly
        super().__init__(kappa, **kw)

    def fixed_rows(self):
        rows = super().fixed_rows()
        return [x for x in rows if not (self.drop_ly and x[0] == 'ly<1/2')]


def run(args):
    """levers.py's bootstrap and least stage on Sang's slice, with every stage's optimum returned."""
    cfg, s, drop_ly = args
    kappa, fp = 3 / 4, []
    for _ in range(O.STAGES):
        if kappa < 13 / 18:
            break
        o = Reading(kappa, drop_ly=drop_ly, read=True, s=s, mode='slice', **cfg)
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
    return dict(B=sol['v'][3], v=sol['v'], walls=sorted(o.walls(sol)),
                stages=[(k, x['v'][1], x['v'][2]) for k, x, _ in fp])


ALL_CURVE = {0.006: 0.8702645, 0.008: 0.8687363, 0.010: 0.8672309, 0.012: 0.8657514, 0.016: 0.8628871,
             0.020: 0.8612453}   # Sang's inputs + all readings under the reading, low side lowered by s
SLOPE_MAX = 0.7265


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    ok, npts = True, 0
    for bi in range(0, 21):
        for li in range(10, 21):
            b, ell = Fr(bi, 100), Fr(li, 100)
            lx, ly, h = (1 - b - ell) / 2, (1 + b - ell) / 2, (1 + b + 3 * ell) / 2
            ok &= h == 1 - lx + ell == ly + 2 * ell
            ok &= ell / h - Fr(1, 5) == (7 * ell - 1 - b) / (5 * (1 + b + 3 * ell))
            ok &= ell / h - Fr(21, 100) == (137 * ell - 21 * (1 + b)) / (100 * (1 + b + 3 * ell))
            ok &= Fr(1, 2) - ly == (ell - b) / 2
            ok &= (ell / h > Fr(1, 5)) == (ell > (1 + b) / 7) and (ell / h > Fr(21, 100)) == (ell > 21 * (1 + b) / 137)
            ok &= (ly < Fr(1, 2)) == (ell > b)
            npts += 1
    gate('F1', ok, f'on Sang\'s geometry at {npts} rational points: the supply ell/h > 1/5 is ell > (1+b)/7, '
                   f'ell/h > 21/100 is ell > 21(1+b)/137, l_y < 1/2 is ell > b; at b = 0 the supply gives '
                   f'{Fr(1, 7)} and 21/100 gives {Fr(21, 137)} = {21 / 137:.6f}')

    names = [nm for nm, _, _ in LV.CONFIGS]
    cfgs = [cfg for _, cfg, _ in LV.CONFIGS]
    sang = cfgs[names.index("Sang's inputs")]
    allr = cfgs[names.index("Sang's inputs + all readings")]
    pts = ([(c, 0.0) for c in cfgs] + [(c, 10.0) for c in cfgs] + [(sang, s) for s in sorted(LE.CURVE)]
           + [(sang, LE.S_STAR)] + [(allr, s) for s in sorted(ALL_CURVE)])
    jobs = [(c, s, d) for c, s in pts for d in (False, True)]
    with ProcessPoolExecutor(max_workers=4) as ex:
        res = list(ex.map(run, jobs))
    kept, drop = res[0::2], res[1::2]
    n, k = len(cfgs), len(LE.CURVE)

    moved = max(abs(a['B'] - b['B']) for a, b in zip(kept, drop))
    rec = ([LE.READ_LOW[nm] for nm in names] + [LE.NO_LOW[nm][1] for nm in names]
           + [LE.CURVE[s] for s in sorted(LE.CURVE)] + [0.87] + [ALL_CURVE[s] for s in sorted(ALL_CURVE)])
    dev = max(abs(a['B'] - r) for a, r in zip(kept, rec))
    gate('F2', moved < 1e-9 and dev < 2e-6,
         f'l_y < 1/2 dropped as well: {len(kept)} boundaries move by at most {moved:.1e}; the kept reading within '
         f'{dev:.1e} of lowerend.py\'s records; Sang\'s inputs + all readings, low side lowered by s = '
         + ', '.join(f'{s:g}: {a["B"]:.7f}' for s, a in zip(sorted(ALL_CURVE), kept[2 * n + k + 1:])))

    q, z0 = Fr(5, 12), Fr(17, 50)
    worst = max(max(float(1 - z0 + q / (12 * Fr(kap))), float(1 - z0 + q * Fr(ly) / (36 * Fr(kap) ** 2 * Fr(ell))))
                for r in kept + drop for kap, ly, ell in r['stages'])
    e1 = 1 - z0 + q / (12 * Fr(13, 18))
    e2 = 1 - z0 + q * 1 / (36 * Fr(13, 18) ** 2 * Fr(1, 8))
    gate('F3', worst < 2 and abs(worst - SLOPE_MAX) < 1e-4 and e2 == Fr(7077, 8450) and e1 == Fr(1841, 2600),
         f'at every stage of F2 Sang\'s two slope bounds, with the stage\'s own kappa, l_y and ell, are below 2 '
         f'(largest {worst:.4f}); at ell >= 1/8, kappa >= 13/18 and l_y < 1 they are at most {e1} = {float(e1):.4f} '
         f'and below {e2} = {float(e2):.4f}')

    i_ev, i_sg = n + names.index('everything'), n + names.index("Sang's inputs")
    least = min(ell for r in kept + drop for _, _, ell in r['stages'])
    b_of = lambda r: r['v'][1] - r['v'][0]
    ok = (all(abs(r[i_ev]['v'][2] - 1 / 7) < 1e-6 and abs(b_of(r[i_ev])) < 1e-6 for r in (kept, drop))
          and kept[i_ev]['B'] < 0.87 - 1e-3 and abs(least - 1 / 7) < 1e-6
          and all(abs(r[i_sg]['B'] - 0.87) < 1e-9 for r in (kept, drop)))
    ev, sk, sd = drop[i_ev], kept[i_sg], drop[i_sg]
    gate('F4', ok, f'low side removed, under the reading: everything {ev["B"]:.7f} at ell {ev["v"][2]:.6f}, '
                   f'b {b_of(ev):.1e} (walls {", ".join(ev["walls"])}), with l_y < 1/2 kept and dropped; least ell '
                   f'at any stage {least:.6f}; Sang\'s inputs stop at the edge {sk["B"]:.7f}, the solver\'s optimum '
                   f'at ell {sk["v"][2]:.6f} kept and {sd["v"][2]:.6f} dropped')

    print(f'{fails} gate(s) failed' if fails else 'all gates pass')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
