"""Stack review 3 (STRUCTURAL-REVIEW.md §9.7). Usage: python3 review/stack3/exclusive_reach.py deps.jsonl review/stack3/branches.json.
Exclusive reach: for each named root set, B = the own constants reachable from the roots, and the exclusive part
B minus everything reachable from the #print axioms targets outside B (in-file lines plus the pnt/zeta23 build.sh
lists), so a printed helper used only inside B counts as exclusive. Lines are estimated per declaration, from its
declaration line to the next declaration, `#print` line or `end`."""
import collections, json, os, re, sys, functools
R = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LAYERS = [('src', 'src'), ('dh', 'external/dh'), ('pnt', 'external/pnt'), ('zeta23', 'external/zeta23')]
AUX = re.compile(r'^(eq_\d+|eq_def|match_\d+|proof_\d+|_proof_\d+|_lambda_\d+|_sunfold|_unary|_mutual|_private|'
                 r'_cstage\d|spec_\d+|_closed|_aux_\d+|_auxLemma\.\d+|injEq|inj|sizeOf_spec|noConfusion|'
                 r'noConfusionType|recOn|casesOn|rec|below|brecOn|binductionOn|ibelow|mk|ctorIdx)$')
mods, rows = {}, []
for line in open(sys.argv[1], encoding='utf-8'):
    o = json.loads(line)
    if 'imports' in o: mods[o['module']] = o['imports']
    elif 'dupof' in o: pass
    else: rows.append(o)
layer, src = {}, {}
for m in mods:
    layer[m] = 'upstream'
    for lay, d in LAYERS:
        if os.path.exists(f'{R}/{d}/{m}.lean'): layer[m], src[m] = lay, f'{d}/{m}.lean'
own = {m for m in mods if layer[m] != 'upstream'}
defmods = collections.defaultdict(set)
for o in rows: defmods[o['name']].add(o['module'])
@functools.lru_cache(None)
def closure(m):
    s = {m}
    for i in mods.get(m, []):
        if i in mods: s |= closure(i)
    return frozenset(s)
def parent(n):
    out = []
    for p in n.split('.'):
        if p.startswith('_') or AUX.match(p): break
        out.append(p)
    return '.'.join(out) if out else n
def resolve(dep, user):
    ms = defmods.get(dep, set())
    if len(ms) == 1: return (parent(dep), next(iter(ms)))
    inside = sorted(m for m in ms if m in closure(user))
    return (parent(dep), inside[0]) if inside else None
def home(o):
    p = parent(o['name']); ms = defmods.get(p)
    if ms and o['module'] not in ms:
        inside = sorted(m for m in ms if m in closure(o['module']))
        if inside: return (p, inside[0])
    return (p, o['module'])
edges = collections.defaultdict(set)
for o in rows:
    u = home(o)
    for d in set(o['tdeps']) | set(o['vdeps']):
        t = resolve(d, o['module'])
        if t and t != u: edges[u].add(t)
targets = set()
for m in sorted(own):
    for line in open(f'{R}/{src[m]}', encoding='utf-8'):
        mm = re.match(r'^#print axioms\s+(\S+)', line)
        if not mm: continue
        nm = mm.group(1)
        cands = [nm] if nm in defmods else [o['name'] for o in rows if o['module'] in closure(m) and o['name'].endswith('.' + nm)]
        for c in cands:
            r = resolve(c, m)
            if r: targets.add(r)
for bf in ['external/pnt/build.sh', 'external/zeta23/build.sh']:
    for line in open(f'{R}/{bf}', encoding='utf-8'):
        mm = re.match(r'^#print axioms\s+(\S+)', line)
        if mm and mm.group(1) in defmods:
            for m in defmods[mm.group(1)]: targets.add((parent(mm.group(1)), m))
def reach(roots):
    seen, st = set(), list(roots)
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(edges.get(x, ()))
    return seen
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+([^\s:({\[]+)')
spans = {}
def file_spans(m):
    if m in spans: return spans[m]
    lines = open(f'{R}/{src[m]}', encoding='utf-8').read().split('\n')
    starts = [(i, DECL.match(l).group(1)) for i, l in enumerate(lines) if DECL.match(l)]
    res = {}
    for k, (i, n) in enumerate(starts):
        j = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        # stop at #print lines or `end` of namespace
        for jj in range(i + 1, j):
            if lines[jj].startswith('#print') or lines[jj].startswith('end '):
                j = jj; break
        res.setdefault(n.split('.')[-1], []).append((i + 1, j))
    spans[m] = res
    return res
sets = json.load(open(sys.argv[2]))
for label, roots in sets.items():
    rs = set()
    for r in roots:
        hits = [t for t in targets if t[0] == r or t[0].endswith('.' + r)] or \
               [(parent(n), m) for n in defmods if (n == r or n.endswith('.' + r)) for m in defmods[n]]
        rs |= set(hits)
    B = reach(rs)
    others = reach(targets - B)
    excl = sorted(x for x in B if x not in others and x[1] in own)
    tot, per = 0, collections.Counter()
    for n, m in excl:
        sp = file_spans(m).get(n.split('.')[-1], [])
        if sp:
            a, b = sp[0]; tot += b - a; per[m] += b - a
    print(f'{label}: roots {len(rs)}, exclusive constants {len(excl)}, ~{tot} lines', dict(per))
