"""Stack review 3: censuses over the olean dump of OleanDeps.lean (STRUCTURAL-REVIEW.md §9).

Usage, from tools/lean/riemann-pilot after all four builds:
  find build -name '*.olean' | sed 's|^build/||; s|\\.olean$||; s|/|.|g' | sort > mods.txt
  (cd $MATHLIB && LEAN_PATH="$(lake env printenv LEAN_PATH):<pilot>/build" lean --run <pilot>/review/stack3/OleanDeps.lean <pilot>/mods.txt deps.jsonl)
  python3 review/stack3/census.py deps.jsonl

Prints: the module and constant counts; the reachability census (own constants, auxiliary names folded into
their parents, reachable from a `#print axioms` target: the in-file lines of every own module plus the final
checks of external/pnt/build.sh and external/zeta23/build.sh); the unreachable constants per module, with
notation, `congr_simp`, `match_` and private auxiliaries filtered out; and the groups of own declarations with
alpha-equivalent statements (and equal values, for definitions) under two or more names; and the imports of own
modules from whose exclusive closure (the modules no other import of the module brings) nothing is used.
"""
import collections
import functools
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
R = os.path.dirname(os.path.dirname(HERE))
LAYERS = [('src', 'src'), ('dh', 'external/dh'), ('pnt', 'external/pnt'), ('zeta23', 'external/zeta23')]
AUX = re.compile(r'^(eq_\d+|eq_def|match_\d+|proof_\d+|_proof_\d+|_lambda_\d+|_sunfold|_unary|_mutual|_private|'
                 r'_cstage\d|spec_\d+|_closed|_aux_\d+|_auxLemma\.\d+|injEq|inj|sizeOf_spec|noConfusion|'
                 r'noConfusionType|recOn|casesOn|rec|below|brecOn|binductionOn|ibelow|mk|ctorIdx)$')
JUNK = re.compile(r'(_private|congr_simp|match_\d|splitter|_aux_|mellintransform|termζ|unexpand)')
DUPJUNK = re.compile(r'(_private|congr_simp|match_\d|splitter|_aux_|\.eq_\d+$|\.eq_def$|_proof_|\._|instDecidable|'
                     r'\.inj|\.injEq|sizeOf_spec|_sunfold|_unfold)')


def main(path):
    mods, rows, dups = {}, [], []
    for line in open(path, encoding='utf-8'):
        o = json.loads(line)
        if 'imports' in o:
            mods[o['module']] = o['imports']
        elif 'dupof' in o:
            dups.append(o['dupof'])
        else:
            rows.append(o)
    layer, src = {}, {}
    for m in mods:
        layer[m] = 'upstream'
        for lay, d in LAYERS:
            if os.path.exists(f'{R}/{d}/{m}.lean'):
                layer[m], src[m] = lay, f'{d}/{m}.lean'
    own = {m for m in mods if layer[m] != 'upstream'}
    print('modules', len(mods), dict(collections.Counter(layer.values())), 'constants', len(rows))
    defmods = collections.defaultdict(set)
    for o in rows:
        defmods[o['name']].add(o['module'])

    @functools.lru_cache(None)
    def closure(m):
        s = {m}
        for i in mods.get(m, []):
            if i in mods:
                s |= closure(i)
        return frozenset(s)

    def parent(n):
        out = []
        for p in n.split('.'):
            if p.startswith('_') or AUX.match(p):
                break
            out.append(p)
        return '.'.join(out) if out else n

    def resolve(dep, user):
        ms = defmods.get(dep, set())
        if len(ms) == 1:
            return (parent(dep), next(iter(ms)))
        inside = sorted(m for m in ms if m in closure(user))
        return (parent(dep), inside[0]) if inside else None

    def home(o):
        p = parent(o['name'])
        ms = defmods.get(p)
        if ms and o['module'] not in ms:
            inside = sorted(m for m in ms if m in closure(o['module']))
            if inside:
                return (p, inside[0])
        return (p, o['module'])

    edges, nodes = collections.defaultdict(set), set()
    for o in rows:
        u = home(o)
        nodes.add(u)
        for d in set(o['tdeps']) | set(o['vdeps']):
            t = resolve(d, o['module'])
            if t and t != u:
                edges[u].add(t)
    users = collections.defaultdict(set)
    for u, ts in edges.items():
        for t in ts:
            users[t].add(u)
    targets, unres = [], []
    for m in sorted(own):
        for line in open(f'{R}/{src[m]}', encoding='utf-8'):
            mm = re.match(r'^#print axioms\s+(\S+)', line)
            if not mm:
                continue
            nm = mm.group(1)
            cands = [nm] if nm in defmods else [o['name'] for o in rows if o['module'] in closure(m)
                                                 and o['name'].endswith('.' + nm)]
            if not cands:
                unres.append((m, nm))
            for c in cands:
                r = resolve(c, m)
                if r:
                    targets.append(r)
    for bf in ['external/pnt/build.sh', 'external/zeta23/build.sh']:
        for line in open(f'{R}/{bf}', encoding='utf-8'):
            mm = re.match(r'^#print axioms\s+(\S+)', line)
            if mm:
                if mm.group(1) in defmods:
                    targets += [(parent(mm.group(1)), m) for m in defmods[mm.group(1)]]
                else:
                    unres.append((bf, mm.group(1)))
    reach, stack = set(), list(set(targets))
    while stack:
        x = stack.pop()
        if x not in reach:
            reach.add(x)
            stack.extend(edges.get(x, ()))
    own_nodes = {n for n in nodes if n[1] in own}
    dead = sorted(n for n in own_nodes if n not in reach)
    real = [n for n in dead if not JUNK.search(n[0])]
    print('targets', len(targets), 'unresolved', unres)
    print('own nodes', len(own_nodes), 'unreachable', len(dead), 'after filtering artefacts', len(real))
    by = collections.defaultdict(list)
    for n, m in real:
        by[m].append(n + ('' if not users.get((n, m)) else '*'))
    print('unreachable by module (* = has users, all of them unreachable too):')
    for m in sorted(by, key=lambda m: (-len(by[m]), m)):
        print(f'  {m} ({len(by[m])}): ' + ', '.join(by[m]))
    imports = collections.defaultdict(set)
    for o in rows:
        for d in set(o['tdeps']) | set(o['vdeps']):
            imports[o['module']] |= defmods.get(d, set())
    unused = []
    for m in sorted(own):
        imps = [i for i in mods[m] if i in mods]
        for i in imps:
            others = set()
            for j in imps:
                if j != i:
                    others |= closure(j)
            only = closure(i) - others
            if not imports[m] & only:
                unused.append((m, i, len(only)))
    print(f'imports that bring nothing used: {len(unused)}; of them bringing modules of their own:')
    for m, i, n in sorted(unused, key=lambda x: -x[2]):
        if n:
            print(f'  {m} -> {i}: {n}')
    # downstream: with the import removed, does every own module still reach every module whose constants it uses?
    used_in = collections.defaultdict(set)
    for o in rows:
        for d in set(o['tdeps']) | set(o['vdeps']):
            ms = defmods.get(d, set())
            ins = [dm for dm in ms if dm in closure(o['module'])]
            used_in[o['module']] |= set(ins if ins else ms)
    print('removals whose downstream uses all stay reachable:')
    for m, i, n in sorted(unused, key=lambda x: -x[2]):
        if not n:
            continue
        graph = {k: [j for j in v if not (k == m and j == i)] for k, v in mods.items()}

        @functools.lru_cache(None)
        def cl2(x, graph=graph):
            out = {x}
            for j in graph.get(x, []):
                if j in graph:
                    out |= cl2(j)
            return frozenset(out)
        broken = sorted(d for d in own if used_in[d] - cl2(d))
        print(f'  {m} -> {i}: ' + ('ok' if not broken else f'{len(broken)} downstream lose a used module ({", ".join(broken[:4])}...)'))
    groups = []
    for g in dups:
        items = [tuple(x.rsplit(' @ ', 1)) for x in g]
        items = [(n, m) for n, m in items if not DUPJUNK.search(n)]
        if len(items) < 2 or {layer.get(m) for _, m in items} == {'upstream'}:
            continue
        if len({n for n, _ in items}) == 1:
            continue
        groups.append(sorted(items, key=lambda x: x[1]))
    gen = [g for g in groups if all('.lgB_' in n for n, _ in g)]
    rest = [g for g in groups if g not in gen]
    print(f'duplicate groups (own, two or more names): {len(groups)}; generated lgB_n log bounds: {len(gen)}')
    for g in sorted(rest):
        print('  ' + ' = '.join(f'{n} @{m}' for n, m in g))


if __name__ == '__main__':
    main(sys.argv[1])
