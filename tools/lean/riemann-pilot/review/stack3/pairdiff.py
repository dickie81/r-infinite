"""Stack review 3 (STRUCTURAL-REVIEW.md §9.7): for each line `label|file:a-b|file:c-d|renames|renames` of the pairs
file, the number of nonblank lines of the two ranges (whitespace collapsed, optional `x=>y;…` renamings applied)
that match. Usage, from tools/lean/riemann-pilot: python3 review/stack3/pairdiff.py review/stack3/pairs.txt
"""
import difflib, os, sys, re
R = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) + '/'
def rng(spec):
    f, r = spec.rsplit(':', 1); a, b = map(int, r.split('-'))
    L = open(R + f, encoding='utf-8').read().split('\n')[a-1:b]
    return [re.sub(r'\s+', ' ', l.strip()) for l in L if l.strip()]
def ren(lines, pairs):
    out = []
    for l in lines:
        for x, y in pairs: l = l.replace(x, y)
        out.append(l)
    return out
for line in open(sys.argv[1], encoding='utf-8'):
    line = line.strip()
    if not line or line.startswith('#'): continue
    parts = line.split('|')
    label, A, B = parts[0], parts[1], parts[2]
    rA = [tuple(p.split('=>')) for p in parts[3].split(';')] if len(parts) > 3 and parts[3] else []
    rB = [tuple(p.split('=>')) for p in parts[4].split(';')] if len(parts) > 4 and parts[4] else []
    a, b = ren(rng(A), rA), ren(rng(B), rB)
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    same = sum(bl.size for bl in sm.get_matching_blocks())
    print(f'{label}: {len(a)} vs {len(b)} nonblank lines; {same} identical after normalization'
          + (' and renaming' if rA or rB else ''))
