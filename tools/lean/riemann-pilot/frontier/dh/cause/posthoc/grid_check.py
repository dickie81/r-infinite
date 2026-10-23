#!/usr/bin/env python3
"""Post-hoc: a grid-convergence check of euler_zeros.py's counts.  The winding euler_zeros.py reports is a sum of
principal argument increments around a closed sampled polygon, so it is an integer (to rounding) whatever the
sampling: its distance from an integer is not a check.  What can fail is a missed turn inside one step.  This script
recounts chunks with the step halved (dt = 0.005, dsigma = 0.001; the refinement rule unchanged) and compares every
count with the committed chunk (posthoc/chunks/), printing MATCH or DIFF per chunk and a final verdict line.
Usage: grid_check.py T1 T2 [T1 T2 ...]"""
import sys, json, os, importlib.util
H = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('ez', os.path.join(H, 'euler_zeros.py'))
ez = importlib.util.module_from_spec(spec); spec.loader.exec_module(ez)
ez.DT, ez.DS = 0.005, 0.001
args = [float(x) for x in sys.argv[1:]]
bad = 0
for T1, T2 in zip(args[::2], args[1::2]):
    ref = json.load(open(os.path.join(H, 'chunks', f'ez_{T1:.0f}_{T2:.0f}.json')))
    diffs = []
    for row in ref['rows']:
        res, stats = ez.count(T1, T2, row['sigma0'])
        old = {x['X']: x['N'] for x in row['res']}; new = {x['X']: x['N'] for x in res}
        diffs += [(row['sigma0'], X, old[X], new[X]) for X in old if old[X] != new[X]]
    bad += len(diffs)
    print(f'({T1:.0f}, {T2:.0f}]: ' + ('MATCH (every sigma0 and X)' if not diffs else 'DIFF ' + str(diffs)), flush=True)
print('grid check: ' + ('all counts unchanged at half the step' if bad == 0 else f'{bad} counts changed'))
