"""Stack review 3 (STRUCTURAL-REVIEW.md §9.7). Usage: python3 review/stack3/printed_unused.py deps.jsonl out.json (deps.jsonl from census.py's usage line).
Printed targets with no users: own constants named by a #print axioms line (in-file or build.sh) that no other
own constant uses (aux names folded into parents, as census.py). Prints per module."""
import collections, json, os, re, sys, functools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
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
        if os.path.exists(f'{R}/{d}/{m}.lean'):
            layer[m], src[m] = lay, f'{d}/{m}.lean'
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
users = collections.defaultdict(set)
for o in rows:
    u = home(o)
    for d in set(o['tdeps']) | set(o['vdeps']):
        t = resolve(d, o['module'])
        if t and t != u: users[t].add(u)
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
unused = sorted(t for t in targets if t[1] in own and not users.get(t))
json.dump([list(t) for t in unused], open(sys.argv[2], 'w'))
by = collections.Counter(m for _, m in unused)
print('printed targets', len(targets), 'own printed with no users', len(unused))
for m, c in by.most_common(30): print(' ', m, c)
