"""doc_checks.py: three checks of how the pilot's prose states the Lean theorems, for the defect classes that reviews
found more than once (round 711; reviews A, C and D of round 709). Each check reads the live text (struck text
`~~…~~` and quotations "…" removed from markdown) and compares a census of its hits with the baseline
`doc_checks_base.json`, written when the check was adopted, so that the existing hits are recorded rather than
rewritten; a hit beyond the baseline fails.

* `exists_C` (the class of review B of round 700, F6, and review A of round 709, F1): on the living surfaces
  (`external/pnt/README.md`, `SIEVE-ROUTE.md` and `CGL-LEAN.md`), a sentence that asserts a constant `C` (there is or
  there are `C`) and has `q` in a code span must bind `q` itself, by the span `q ≥ 1` in backticks, or by every or
  for before a code span opening with `q`: where a section's preamble fixes `q`, the sentence otherwise lets `C`
  depend on `q`, which makes a bound over all characters mod `q` trivial. Sentences end at a period or semicolon
  followed by a space. The baseline holds none.
* `qge1` (round 695's review A, F5; round 701's O2; review C of round 709, F5): a docstring of a theorem or lemma with
  `[NeZero q]` in scope (its signature, or a `variable` of an enclosing section, namespace or the file) must contain
  the span `` `q ≥ 1` ``. Read on `external/pnt/*.lean`; the baseline holds the docstrings that lacked it at
  adoption, by file and declaration (review A of round 709, O1, gave the forms: modifiers before `theorem`, a named
  binder `[hq : NeZero q]`, and `q ≥ 1` only inside a longer span such as `2q ≥ 1`).
* `hyps` (the partial-hypothesis-list class: round 604's finding 2, round 667's B F1, round 693; in round 709
  reviews B F1, C F1–F2 and D F1–F2): for each explicit binder `(h : T)` of a theorem or lemma whose type `T` names a
  predicate of the stack (a `def` of type `Bool` or `Prop`, or a `structure` or `class` in `Prop`, defined in
  `external/pnt/*.lean`), the prose that describes the declaration must name the predicate or one of its aliases
  (`ALIAS`): its docstring, and every line of the four markdown surfaces (the three above and the pilot's README.md)
  that cites it, as the head of a bullet (`- `X`, `Y`: …`) or in a parenthetical list of names after the text that
  describes them (`(`X`, `Y` and `Z`)`). A cited name is a declaration when it is one's full name or ends one's full
  name after a dot; a short name with several declarations takes the predicates they share. Instance binders `[…]`
  are not read: the files state them in their preambles.

Not read: other spellings (a constant named otherwise than `C`; a quantifier written in words), hypotheses whose
types name no predicate (`a ≤ b`, `0 ≤ L`), and names in running text outside the two citing forms, such as a list
of the theorems that set an option. The census is a lower bound on the class: a hit is a missing name, not a verified
defect, and a line that names the predicate need not state it as a hypothesis.

Usage: doc_checks.py [--write-baseline]. Exit status 0 when no check has a hit beyond its baseline.
"""
import collections
import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PILOT = os.path.normpath(os.path.join(HERE, '..', '..'))
BASE = os.path.join(HERE, 'doc_checks_base.json')
LIVING = ('external/pnt/README.md', 'frontier/linnik/SIEVE-ROUTE.md', 'frontier/linnik/CGL-LEAN.md')
SURFACES = LIVING + ('README.md',)

# Aliases: words that name a predicate in prose. Matched as substrings, ignoring case; the name itself always counts.
ALIAS = {
    'TypeIIAt': ['type ii'], 'Leaves': ['leaves', 'leaf'], 'KLeaves': ['kept leaves', 'kept part'],
    'cand': ['candidate'], 'dec': ['decomposed', 'dropped'], 'inW': ['window'], 'InC': ['cell'],
    'EvGe': ['eventually at least'], 'EvLe': ['eventually at most'], 'LargeQ': ['large'],
    'CGLDensity': ['density'], 'CharDensity': ['density'], 'Fits': ['fit'], 'ThrOK': ['threshold'],
}

DECL = re.compile(r"/--((?:(?!-/).)*?)-/\s*\n(?:@\[[^\]]*\]\s*\n)?((?:(?:private|protected|noncomputable|nonrec)\s+)*)"
                  r"(theorem|lemma)\s+(\S+)(.*?):=", re.S)
NZ = re.compile(r"\[(?:\w+\s*:\s*)?NeZero q\]")
BINDER = re.compile(r"\((\w[\w' ]*?)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)")
QTOK = re.compile(r"(?<![A-Za-z_\\])q(?![a-z_₀-₉′'])")


def live(line):
    """The line without struck text and without quotations (pairs of straight double quotes)."""
    line = re.sub(r'~~.*?~~', '', line)
    return re.sub(r'"[^"]*"', '', line)


def lean_sources():
    return {os.path.basename(p): open(p, encoding='utf-8').read()
            for p in sorted(glob.glob(os.path.join(PILOT, 'external', 'pnt', '*.lean')))}


def predicates(src):
    pred = set()
    for s in src.values():
        defs = r"^(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z_][\w']*)[^\n]*?:\s*(?:Bool|Prop)\s*:="
        for m in re.finditer(defs, s, re.M):
            pred.add(m.group(1))
        for m in re.finditer(r"^(?:structure|class)\s+([A-Za-z_][\w']*)[^\n]*:\s*Prop\b", s, re.M):
            pred.add(m.group(1))
    return {p for p in pred if len(p) > 2}


def scope_vars(before):
    """The `variable` text in scope at the end of `before`: those of the file and of each enclosing section or
    namespace, with their continuation lines."""
    scope, cont = [[]], False
    for ln in before.split('\n'):
        if re.match(r'(section|namespace)\b', ln):
            scope.append([])
            cont = False
        elif (ln == 'end' or ln.startswith('end ')) and len(scope) > 1:
            scope.pop()
            cont = False
        elif ln.startswith('variable'):
            scope[-1].append(ln)
            cont = True
        elif cont and ln.startswith('    '):
            scope[-1].append(ln)
        else:
            cont = False
    return ' '.join(' '.join(v) for v in scope)


def full_names(s):
    """Each declaration's position and full name (namespaces opened by `namespace` and closed by `end`)."""
    out, ns, pos = {}, [], 0
    for ln in s.split('\n'):
        m = re.match(r'namespace\s+(\S+)', ln)
        if m:
            ns.append(m.group(1))
        elif re.match(r'end\s+(\S+)\s*$', ln) and ns and ln.split()[1] == ns[-1]:
            ns.pop()
        m = re.match(r"(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma)\s+(\S+)", ln)
        if m:
            out[pos] = '.'.join(ns + [m.group(1)])
        pos += len(ln) + 1
    return out


NAMES = r"`[A-Za-z_][\w.'₀-₉]*`(?:(?:,\s*|,?\s+(?:and|or)\s+)`[A-Za-z_][\w.'₀-₉]*`)*"


def cited(text):
    """The names a line describes: those of a bullet's head (`- `X`, `Y`: …`) and of a parenthetical citation
    (`… (`X`, `Y` and `Z`)`), which follows the text describing them."""
    out = set()
    m = re.match(r"\s*(?:[-*]|\d+\.)\s+(" + NAMES + r")[^:`]{0,40}:", text)
    groups = [m.group(1)] if m else []
    groups += re.findall(r"\((" + NAMES + r")\)", text)
    for g in groups:
        out.update(re.findall(r"`([^`]+)`", g))
    return out


def mentions(text, p):
    if re.search(r"(?<![\w'])" + re.escape(p) + r"(?![\w'])", text):
        return True
    low = text.lower()
    return any(a in low for a in ALIAS.get(p, []))


def census():
    src = lean_sources()
    pred = predicates(src)
    hits = {'exists_C': collections.Counter(), 'qge1': collections.Counter(), 'hyps': collections.Counter()}
    decl_preds = collections.defaultdict(list)   # short name and full name -> list of predicate sets
    for f, s in src.items():
        names = full_names(s)
        for m in DECL.finditer(s):
            doc, _, _, name, sig = m.groups()
            start = s.rfind('\n', 0, m.start(4)) + 1
            full = names.get(start, name)
            ps = set()
            for b in BINDER.finditer(sig):
                for p in pred:
                    if re.search(r"(?<![\w'])(?:\w+\.)?" + re.escape(p) + r"(?![\w'])", b.group(2)):
                        ps.add(p)
            for p in sorted(ps):
                if not mentions(doc, p):
                    hits['hyps'][f'{f}:{full}:{p}'] += 1
            parts = full.split('.')
            for key in {'.'.join(parts[i:]) for i in range(len(parts))}:
                decl_preds[key].append(ps)
            if (NZ.search(sig) or NZ.search(scope_vars(s[:m.start()]))) and '`q ≥ 1`' not in doc:
                hits['qge1'][f'{f}:{full}'] += 1
    for rel in SURFACES:
        for line in open(os.path.join(PILOT, rel), encoding='utf-8').read().split('\n'):
            text = live(line)
            if rel in LIVING:
                for sent in re.split(r'(?<=[.;])\s', text):
                    if re.search(r'there (?:is|are) `C', sent):
                        spans = re.findall(r'`([^`]*)`', sent)
                        if any(QTOK.search(x) for x in spans) and not re.search(r'`q ≥ 1`|every `q|for `q', sent):
                            hits['exists_C'][f'{rel}:{sent[:100]}'] += 1
            for tok in cited(text):
                sets = decl_preds.get(tok)
                if not sets:
                    continue
                for p in sorted(set.intersection(*sets)):
                    if not mentions(text, p):
                        hits['hyps'][f'{rel}:{tok}:{p}'] += 1
    return hits


def main():
    hits = census()
    if '--write-baseline' in sys.argv:
        json.dump({k: dict(sorted(v.items())) for k, v in hits.items()}, open(BASE, 'w', encoding='utf-8'), indent=0,
                  ensure_ascii=False)
        print('baseline written:', ', '.join(f'{k} {sum(v.values())}' for k, v in hits.items()))
        return 0
    base = json.load(open(BASE, encoding='utf-8'))
    bad = 0
    for k, v in hits.items():
        b = base.get(k, {})
        new = {key: n - b.get(key, 0) for key, n in v.items() if n > b.get(key, 0)}
        gone = sum(max(0, n - v.get(key, 0)) for key, n in b.items())
        print(f'{k}: {sum(v.values())} hits, baseline {sum(b.values())}; beyond the baseline {sum(new.values())}; '
              f'fixed since the baseline {gone}')
        for key in sorted(new):
            print(f'  NEW {k}: {key}')
        bad += sum(new.values())
    print('DOC_CHECKS', 'PASS' if bad == 0 else f'FAIL ({bad})')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
