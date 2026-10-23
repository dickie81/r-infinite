"""k_decimals.py: the decimals of `K` on the three Linnik surfaces (SIEVE-ROUTE.md, external/pnt/README.md and the
pilot's README.md), against the exact totals they display (round 633; review of round 631, finding F-B), and the cells
of SIEVE-ROUTE.md's replay table (§23) against `route_limits.jsonl` (round 634; review of round 633, F1).

The class in its form for totals (rounds 584, 585, 587, 632 and 633 found instances of it; rounds 628 and 629 found it
in floors, which this script does not read): a certificate's total below `K`, or the sum of its parts' bounds below
`K`, bounds the loss from above, so a decimal of `K` that displays one is at least its exact value: rounded up, or
written "below `X`" with `X` at least the value. A failing total, above `K`, certifies nothing, and its decimal is
outside the class.

Every decimal `d` written as digits followed by `K`, `·K` or a space and `K` (`K` not followed by a letter, a digit or
`_`) in the live text (struck text `~~…~~` and quotations "…" removed) must be classified in `DECIMALS`: either the
name of an exact value in `EXACT`, which `d` must not undercut, or the reason it lies outside the class (a failing
total, above `K`; a threshold; a float quoted from a review's output; another `K`). Classification is by the string
`d`, not by its site: a new site that writes a classified string for another quantity is checked against the string's
quantity. An unclassified decimal fails the check, so a new string must be classified when it is written.

The replay table's cells are `total/K` to the places shown, rounded to the nearest: each must equal that rounding of
its `route_limits.jsonl` row (curve, `L`, window and `n`), and lie below `1` exactly when the row's total is below `K`.
The table must yield `TABLE_CELLS` cells, so a row the pattern stops reading fails the check.

`EXACT` names where each exact value (a numerator over `K = 2⁶⁰`) comes from: `route_limits.jsonl`'s row or the sum
of the Lean part files' bounds, read on every run (each pattern must match its recorded numbers of files and bounds),
or a grid's total by `route_limits.replay`, stored here because a replay takes up to minutes; `--recompute` replays
the grids and compares with the stored totals. Since round 709 also a grid's refined total, by
`refine_k2_probe.replay2`, stored the same way: on the grid of `SieveGrid225R.lean` it equals `SieveCert2Defs.total2`
(the scratch mirror of the Lean definitions, `scratchpad/r705/mirror2.py`, round 709's record); `--recompute` replays
it too. (Round 711: the probe's refined total may lie below `total2`, the unsafe direction for this check, so since
round 711 the `refined` kind replays `replay2`'s fifth value, the total by the certificate's own decisions, which is
`total2`'s rule; review B of round 709, O1.)

Not read: figures without `K` other than the table's cells, and spellings of a decimal of `K` other than the three
above; the pre-landing self-review covers them.

Usage: k_decimals.py [--recompute]. Exit status 0 when every decimal is classified and none undercuts its value, and
every table cell matches.
"""
import glob, json, os, re, sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
PILOT = os.path.join(HERE, '..', '..')
FILES = ('frontier/linnik/SIEVE-ROUTE.md', 'external/pnt/README.md', 'README.md')
K = 2 ** 60

# name: how its exact value (numerator over K) is found. ('grid', W1, W2, D, n, NUM): route_limits.replay on
# [W1/D, W2/D] with n cells gives NUM (stored, a replay taking up to minutes; --recompute replays it);
# ('refined', W1, W2, D, n, NUM): the same with refine_k2_probe.replay2's refined total by the certificate's own
# decisions, its fifth value (round 709; the fifth value since round 711);
# ('jsonl', curve, L, n): route_limits.jsonl's row; ('lean', patterns): the sum of the part files' bounds.
EXACT = {
    'g7c 9/4 n=400': ('grid', 41191, 48127, 100000, 400, 1140480798652974258),
    'gU 229/100 n=150': ('grid', 40011, 47579, 100000, 150, 1082756119687641850),
    'gU 229/100 n=200': ('grid', 40011, 47579, 100000, 200, 1035048944461701456),
    'gU 2285/1000 n=250': ('grid', 40302, 47464, 100000, 250, 1139467503837147158),
    'grid231 n=200 [4070, 4803]': ('grid', 4070, 4803, 10000, 200, 1089813094299946542),
    'grid230 n=100': ('grid', 3944, 4780, 10000, 100, 956276356674239363),
    'grid232 n=150': ('grid', 4045, 4825, 10000, 150, 980881133367270040),
    'grid227 n=100': ('grid', 4048, 4858, 10000, 100, 973313265243829043),
    'grid226 n=100': ('grid', 4075, 4835, 10000, 100, 1143523799390085445),
    'grid226 n=150': ('grid', 4075, 4835, 10000, 150, 1030211209703059457),
    'grid226 n=180': ('grid', 4075, 4835, 10000, 180, 1001097708779863196),
    'grid226 n=200': ('grid', 4075, 4835, 10000, 200, 977548402391414719),
    'grid 2.256 n=200 [4086, 4826]': ('grid', 4086, 4826, 10000, 200, 1054772424499152438),
    'grid 2.256 n=300 [4086, 4826]': ('grid', 4086, 4826, 10000, 300, 1002803219224850644),
    'grid 2295/1000 n=150 [39719, 47693]': ('grid', 39719, 47693, 100000, 150, 965694177947636179),
    'grid 2255/1000 n=200 [40905, 48242]': ('grid', 40905, 48242, 100000, 200, 1073298964573591545),
    'grid 2255/1000 n=200 [4091, 4824]': ('grid', 4091, 4824, 10000, 200, 1079022260061433519),
    'g7c 9/4 n=600': ('jsonl', 'g7c', '9/4', 600),
    'g7c 9/4 n=800': ('jsonl', 'g7c', '9/4', 800),
    'g7c 2249/1000 n=600': ('jsonl', 'g7c', '2249/1000', 600),
    'g7c 2249/1000 n=800': ('jsonl', 'g7c', '2249/1000', 800),
    'gU 2285/1000 n=300': ('jsonl', 'gU', '457/200', 300),
    'gU 2285/1000 n=400': ('jsonl', 'gU', '457/200', 400),
    'gU 2285/1000 n=600': ('jsonl', 'gU', '457/200', 600),
    'gU 2282/1000 n=600': ('jsonl', 'gU', '1141/500', 600),
    'gU 22825/10000 n=600': ('jsonl', 'gU', '913/400', 600),
    'SieveCert232 bounds': ('lean', ['SieveCert232.lean'], 1, 25),
    'SieveCert226 bounds': ('lean', ['SieveCert226P[0-9].lean'], 5, 49),
    'SieveCert229U bounds': ('lean', ['SieveCert229UP[0-9].lean'], 5, 21),
    'SieveCert225C bounds': ('lean', ['SieveCert225CP*.lean'], 167, 1374),
    'SieveCert2285U bounds': ('lean', ['SieveCert2285UP*.lean'], 28, 252),
    'g7c 9/4 n=200 refined': ('refined', 41191, 48127, 100000, 200, 1120675002519785844),
    'SieveCert225R bounds': ('lean', ['SieveCert225RP*.lean'], 27, 117),
}

FAIL_TOTAL = 'a failing total, above K'
DECIMALS = {
    # displays of exact totals and sums below K
    '0.98921': 'g7c 9/4 n=400', '0.9893': 'g7c 9/4 n=400', '0.96517': 'g7c 9/4 n=600',
    '0.95022': 'g7c 9/4 n=800', '0.99499': 'g7c 2249/1000 n=600', '0.98139': 'g7c 2249/1000 n=800',
    '0.93915': 'gU 229/100 n=150', '0.9392': 'gU 229/100 n=150', '0.89777': 'gU 229/100 n=200',
    '0.98834': 'gU 2285/1000 n=250', '0.96309': 'gU 2285/1000 n=300', '0.94152': 'gU 2285/1000 n=400',
    '0.92022': 'gU 2285/1000 n=600', '0.99177': 'gU 2282/1000 n=600', '0.98057': 'gU 22825/10000 n=600',
    '0.9453': 'grid231 n=200 [4070, 4803]', '0.82944': 'grid230 n=100', '0.85078': 'grid232 n=150',
    '0.84422': 'grid227 n=100', '0.9919': 'grid226 n=100', '0.8936': 'grid226 n=150', '0.8684': 'grid226 n=180',
    '0.84789': 'grid226 n=200', '0.8478880813': 'grid226 n=200', '0.9149': 'grid 2.256 n=200 [4086, 4826]',
    '0.8698': 'grid 2.256 n=300 [4086, 4826]', '0.8517': 'SieveCert232 bounds', '0.84874': 'SieveCert226 bounds',
    '0.94009': 'SieveCert229U bounds', '0.99020': 'SieveCert225C bounds', '0.98932': 'SieveCert2285U bounds',
    '0.8377': 'grid 2295/1000 n=150 [39719, 47693]', '0.9310': 'grid 2255/1000 n=200 [40905, 48242]',
    '0.931': 'grid 2255/1000 n=200 [40905, 48242]', '0.936': 'grid 2255/1000 n=200 [4091, 4824]',
    '0.8442146854': 'grid227 n=100', '0.97204': 'g7c 9/4 n=200 refined', '0.97301': 'SieveCert225R bounds',
    # outside the class
    '1.0769': FAIL_TOTAL, '1.0213': FAIL_TOTAL, '1.02125': FAIL_TOTAL, '1.0051': FAIL_TOTAL, '1.0248': FAIL_TOTAL,
    '4.23': FAIL_TOTAL, '4.05': FAIL_TOTAL, '4.23434': FAIL_TOTAL, '4.04821': FAIL_TOTAL, '2.37': FAIL_TOTAL,
    '1.10': FAIL_TOTAL, '1.16366': FAIL_TOTAL, '1.0782': FAIL_TOTAL, '1.0231': FAIL_TOTAL, '1.07689': FAIL_TOTAL,
    '0.88': 'the threshold of the landings before round 619',
    '0.9400803710196427': "round 624's record of its reviewer's float, as printed",
    '0.299': "another K, a function (the README's section on T1ca.lean)",
    '0.174': "another K, a function (the README's section on T1ca.lean)",
}


def live(line):
    """The line without struck text and without quotations (pairs of straight double quotes)."""
    line = re.sub(r'~~.*?~~', '', line)
    return re.sub(r'"[^"]*"', '', line)


def value(name, replay=False):
    """The exact value of `EXACT[name]`, a numerator over `K`: a grid's stored total or refined total (replayed if
    `replay`), the jsonl row's total or the part files' bounds summed."""
    how = EXACT[name]
    if how[0] in ('grid', 'refined'):
        if not replay:
            return how[5]
        sys.path.insert(0, HERE)
        import route_limits as RL
        W1, W2, D, n = how[1:5]
        U1, U2 = (W1 * RL.DEN + D - 1) // D, W2 * RL.DEN // D
        if how[0] == 'refined':
            import refine_k2_probe as RK
            return RK.replay2(U1, U2, n)[4]
        return RL.replay(U1, U2, n)[0]
    if how[0] == 'jsonl':
        for r in map(json.loads, open(os.path.join(HERE, 'route_limits.jsonl'))):
            if (r['curve'], r['L'], r['n']) == how[1:] and 'total' in r:
                return r['total']
        raise KeyError(name)
    lits, files = [], []
    for pat in how[1]:
        for p in sorted(glob.glob(os.path.join(PILOT, 'external', 'pnt', pat))):
            files.append(p)
            lits += [int(x) for x in RE_BOUND.findall(open(p, encoding='utf-8').read())]
    if (len(files), len(lits)) != how[2:]:
        raise ValueError(f'{name}: {len(files)} files and {len(lits)} bounds, {how[2]} and {how[3]} recorded')
    return sum(lits)


RE_BOUND = re.compile(r'^theorem rows\w*_\d+ : rowsJ?2? [^≤]*≤ (\d+) :=', re.M)
RE_DEC = re.compile(r'(?<![\d.])(\d+\.\d+)(?:K|·K| K)(?![A-Za-z0-9_])')

TABLE_FILE = 'frontier/linnik/SIEVE-ROUTE.md'
TABLE_ROW = re.compile(r'\| `(\w+)` \| `([\d/]+)` \| `\[(\d+), (\d+)\]` \| (.*?) \| `[\d.]+` \| `[\d.]+` \|$')
TABLE_CELLS = 37


def census():
    """Every decimal of `K` in the live text: (failures, rows of (file, line, decimal, name or None))."""
    bad, rows, vals = [], [], {}
    for f in FILES:
        for i, line in enumerate(open(os.path.join(PILOT, f), encoding='utf-8'), 1):
            for m in RE_DEC.finditer(live(line)):
                d = m.group(1)
                c = DECIMALS.get(d)
                rows.append((f, i, d, c if c in EXACT else None))
                if c is None:
                    bad.append(f'{f}:{i}: {d}K is not classified')
                elif c in EXACT:
                    try:
                        v = Fr(vals.setdefault(c, value(c)), K)
                    except ValueError as e:
                        bad.append(f'{f}:{i}: {d}K: {e}')
                        continue
                    if Fr(d) < v:
                        bad.append(f'{f}:{i}: {d}K undercuts {c} = {float(v):.10f}K')
    return bad, rows


def table():
    """§23's replay table: each cell `n: d` must be its jsonl row's `total/K` rounded to the nearest at `d`'s places,
    and below `1` exactly when the total is below `K`. (failures, number of cells read)."""
    jl = [r for r in map(json.loads, open(os.path.join(HERE, 'route_limits.jsonl'))) if 'total' in r]
    bad, cells = [], 0
    for i, line in enumerate(open(os.path.join(PILOT, TABLE_FILE), encoding='utf-8'), 1):
        m = TABLE_ROW.fullmatch(line.rstrip('\n'))
        if not m:
            continue
        curve, L, W = m.group(1), Fr(m.group(2)), (int(m.group(3)), int(m.group(4)))
        for c in re.finditer(r'(\d+): `(\d+\.\d+)`', m.group(5)):
            cells += 1
            n, d = int(c.group(1)), c.group(2)
            hit = [r for r in jl if (r['curve'], Fr(r['L']), r['n'], (r['W1'], r['W2'])) == (curve, L, n, W)]
            if len(hit) != 1:
                bad.append(f'{TABLE_FILE}:{i}: {len(hit)} jsonl rows for {curve} {L} n={n} {W}')
                continue
            v, p = Fr(hit[0]['total'], K), 10 ** len(d.split('.')[1])
            if Fr(d) != Fr(round(v * p), p):
                bad.append(f'{TABLE_FILE}:{i}: n={n}: {d} is not total/K = {float(v):.10f} rounded to the nearest')
            if (Fr(d) < 1) != (v < 1):
                bad.append(f'{TABLE_FILE}:{i}: n={n}: {d} and total/K = {float(v):.10f} on two sides of 1')
    if cells != TABLE_CELLS:
        bad.append(f'{TABLE_FILE}: {cells} table cells read, {TABLE_CELLS} recorded')
    return bad, cells


def recompute():
    """Replays each grid of `EXACT` and compares with its stored total or refined total."""
    bad = []
    for name, how in EXACT.items():
        if how[0] in ('grid', 'refined'):
            got = value(name, replay=True)
            print(f'{name}: {got} {"=" if got == how[5] else "!="} the stored {how[5]}', flush=True)
            if got != how[5]:
                bad.append(name)
    return bad


if __name__ == '__main__':
    bad, rows = census()
    inside = [r for r in rows if r[3]]
    unc = sum(1 for b in bad if b.endswith('is not classified'))
    print(f'{len(rows)} decimals of K on {len(FILES)} files: {len(inside)} display exact totals or sums below K, '
          f'{len(rows) - len(inside) - unc} outside the class, {unc} not classified')
    tbad, cells = table()
    print(f'{cells} cells of the replay table against route_limits.jsonl')
    bad += tbad
    for b in bad:
        print('FAIL', b)
    if '--recompute' in sys.argv:
        rb = recompute()
        for b in rb:
            print('FAIL table', b)
        bad += rb
    print('PASS' if not bad else f'{len(bad)} FAILED')
    sys.exit(1 if bad else 0)
