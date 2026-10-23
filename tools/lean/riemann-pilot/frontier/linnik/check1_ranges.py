"""check1_ranges.py: the line ranges of a round's Check-1 record against the Lean statements they cite (round 712;
review A of round 711, F7, the third finding of its class after review D of round 709, F5, and review A of round 709,
F3: ranges that omitted a statement's conclusion, or followed a numbering from before the round's own edits).

The record is the block of the pilot's README.md from the line "**Check 1**" of the round's entry to the next line
that opens "**Check". In each of its bullets, a run of names in backticks followed by a parenthesized list of line
numbers and ranges, as `bound2`, `cand` and `cost` followed by (83–86, 117–123), cites those names at those lines:
the lines listed must cover, together, the statement of every name of the run that resolves to a declaration of
`external/pnt/*.lean`. A name resolves in the bullet's current file, the last `….lean` named in backticks before it
or the module of the last dotted name `Module.decl` whose `Module.lean` exists, and otherwise in the one file that
declares it. The statement of a theorem or lemma runs from its keyword's line to the line of its `:=`; of a
definition, structure, class, instance or inductive type, from its keyword's line to the last line before a blank
line or a line opening a new command at the margin.

Not read: names that resolve to no declaration or to several (printed as unchecked, for the self-review), lines cited
without a run of names in backticks before them (a file's header), and citations outside the Check-1 block.

Usage: check1_ranges.py ROUND [--rev REV] | --self-test. With `--rev`, the README and the Lean files are read at that
commit, as the record speaks of its own commit; otherwise from the working tree, where a new entry is checked before
its commit. Exit status 0 when every resolved name is covered.
"""
import glob
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PILOT = os.path.normpath(os.path.join(HERE, '..', '..'))
REL = 'tools/lean/riemann-pilot/'

KIND = r"(theorem|lemma|def|abbrev|structure|class|instance|inductive)"
MODS = r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
RANGES = r"\((\d+(?:[–-]\d+)?(?:,\s*\d+(?:[–-]\d+)?)*)\)"
RUN = re.compile(r"((?:`[^`]+`(?:'s)?(?:,\s*|,?\s+and\s+|\s+)?)+)" + RANGES)


def read(rel, rev):
    if rev:
        return subprocess.run(['git', '-C', PILOT, 'show', f'{rev}:{REL}{rel}'], capture_output=True, text=True,
                              check=True).stdout
    return open(os.path.join(PILOT, rel), encoding='utf-8').read()


def lean_files(rev):
    if rev:
        out = subprocess.run(['git', '-C', PILOT, 'ls-tree', '--full-tree', '--name-only', rev, REL + 'external/pnt/'],
                             capture_output=True, text=True, check=True).stdout.split()
        names = [os.path.basename(p) for p in out if p.endswith('.lean')]
    else:
        names = [os.path.basename(p) for p in glob.glob(os.path.join(PILOT, 'external', 'pnt', '*.lean'))]
    return {n: read('external/pnt/' + n, rev) for n in sorted(names)}


def span(lines, i, kind):
    """The statement's lines (1-based, inclusive) of the declaration whose keyword is on line index `i`."""
    if kind in ('theorem', 'lemma'):
        for j in range(i, len(lines)):
            if ':=' in lines[j]:
                return i + 1, j + 1
        return i + 1, i + 1
    j = i
    while j + 1 < len(lines) and lines[j + 1].strip() and lines[j + 1][:1] in (' ', '\t', '|'):
        j += 1
    return i + 1, j + 1


def resolve(name, cur, files):
    """(file, (first, last)) for a name, or a string saying why it is unchecked."""
    last = name.split('.')[-1]
    pat = re.compile(r"^(?:@\[[^\]]*\]\s*)?" + MODS + KIND + r"\s+(?:[\w'.]*\.)?" + re.escape(last) + r"(?![\w'.])",
                     re.M)
    mod = name.split('.')[0] + '.lean' if '.' in name else None
    first = [f for f in (mod, cur) if f in files][:1]
    for group in (first, list(files)):
        hits = []
        for f in group:
            s = files[f]
            for m in pat.finditer(s):
                lines = s.split('\n')
                i = s.count('\n', 0, m.start())
                hits.append((f, span(lines, i, m.group(1))))
        if len(hits) == 1:
            return hits[0]
        if len(hits) > 1:
            return f'ambiguous ({len(hits)} declarations)'
    return 'no declaration'


def block(readme, rnd):
    m = re.search(r'^## Round ' + str(rnd) + r'\b.*?$', readme, re.M)
    if not m:
        raise SystemExit(f'no entry for round {rnd}')
    nxt = re.search(r'^## Round \d+', readme[m.end():], re.M)
    entry = readme[m.end():m.end() + nxt.start()] if nxt else readme[m.end():]
    b = re.search(r'^\*\*Check 1\*\*.*?(?=^\*\*Check)', entry, re.M | re.S)
    if not b:
        raise SystemExit(f'no Check-1 block in round {rnd}')
    return b.group(0)


def check(text, files):
    bad, rows = 0, []
    for bullet in [ln for ln in text.split('\n') if ln.startswith('- ')]:
        bullet = re.sub(r'~~.*?~~', '', bullet)
        cur, pos = None, 0
        for m in RUN.finditer(bullet):
            for t in re.findall(r'`([^`]+)`', bullet[pos:m.start()]):
                cur = _context(t, files, cur)
            names = re.findall(r'`([^`]+)`', m.group(1))
            covered = set()
            for a, b in (r.split('–') if '–' in r else r.split('-') if '-' in r else (r, r)
                         for r in re.split(r',\s*', m.group(2))):
                covered.update(range(int(a), int(b) + 1))
            for t in names:
                ctx = _context(t, files, cur)
                if t.endswith('.lean') or not re.fullmatch(r"[A-Za-z_][\w'.₀-₉]*", t):
                    cur = ctx
                    continue
                r = resolve(t, cur, files)
                cur = ctx
                if isinstance(r, str):
                    rows.append(f'  unchecked `{t}`: {r}')
                    continue
                f, (lo, hi) = r
                miss = [x for x in range(lo, hi + 1) if x not in covered]
                if miss:
                    bad += 1
                    rows.append(f'  MISS `{t}` ({f} {lo}–{hi}) cited ({m.group(2)}): lines {miss} not covered')
                else:
                    rows.append(f'  ok `{t}` ({f} {lo}–{hi}) cited ({m.group(2)})')
            pos = m.end()
    return bad, rows


def _context(t, files, cur):
    if t.endswith('.lean') and t in files:
        return t
    if '.' in t and t.split('.')[0] + '.lean' in files:
        return t.split('.')[0] + '.lean'
    return cur


def self_test():
    """Plants a record citing a theorem at its full statement and at its statement less its last line; the second
    must be reported on its own MISS line."""
    files = lean_files(None)
    f, (lo, hi) = resolve('SieveExact.chainT0_bound', None, files)
    assert hi > lo, (f, lo, hi)
    good = f'- in `{f}`, `chainT0_bound` ({lo}–{hi}).'
    short = f'- in `{f}`, `chainT0_bound` ({lo}–{hi - 1}).'
    b1, r1 = check(good, files)
    b2, r2 = check(short, files)
    print('\n'.join(r1 + r2))
    ok = b1 == 0 and b2 == 1 and any(x.startswith('  MISS `chainT0_bound`') for x in r2)
    print('SELF-TEST', 'CAUGHT' if ok else 'NOT CAUGHT')
    return 0 if ok else 1


def main():
    if '--self-test' in sys.argv:
        return self_test()
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    rev = sys.argv[sys.argv.index('--rev') + 1] if '--rev' in sys.argv else None
    if rev:
        args.remove(rev)
    rnd = int(args[0])
    files = lean_files(rev)
    bad, rows = check(block(read('README.md', rev), rnd), files)
    print(f'round {rnd}' + (f' at {rev}' if rev else ' (working tree)') + ':')
    print('\n'.join(rows))
    n_ok = sum(r.startswith('  ok') for r in rows)
    n_un = sum(r.startswith('  unchecked') for r in rows)
    print(f'{n_ok} covered, {bad} not covered, {n_un} unchecked')
    print('CHECK1_RANGES', 'PASS' if bad == 0 else f'FAIL ({bad})')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
