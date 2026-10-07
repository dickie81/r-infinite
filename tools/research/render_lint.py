#!/usr/bin/env python3
"""The render lint for the markdown paper surfaces (owner's residual
sweep, round 395; CLAUDE.md "Proportionate checking" item 5: a defect
class found twice gets a cheap automated check).

Rounds 389-393 found delimiters that GitHub does not render as written
(F390-1, A562 O-1, A563 F391-2) by hand; this script renders each
surface with cmark-gfm -- the renderer behind GitHub's markdown, whose
HTML for this paper matched GitHub's own API rendering at 2b76ff1 and
49ab366 (the round-395 reviewers compared the visible text and the
em/strong/del/code markers) -- and fails on nine defect classes, each
decidable from the rendering:

  L1 single-tilde strike: GitHub parses ONE tilde as a strike
     delimiter too, so two approximation signs ("~9.3 ... ~20%") can
     strike everything between them. The surface must render
     identically with CMARK_OPT_STRIKETHROUGH_DOUBLE_TILDE (only "~~"
     strikes); every <del> the default rendering adds is reported.
  L2 literal "~~" left in the rendered text: a strike whose delimiters
     failed the flanking rules (e.g. "here~~;").
  L3 literal "**" left in the rendered text: a bold that failed to
     close.
  L4 emphasis opened inside a word: an <em>/<strong>/<del> whose
     opening delimiter follows a letter or digit -- in this paper that
     is a variable's star ("d*₁", "2x*−2") or a strike glued to a word,
     never intended markup.
  L5 a backslash consumed by markdown: a backslash before ASCII
     punctuation outside code, other than the escapes the surfaces use
     on purpose (* _ ~ ` | and the backslash itself) -- e.g. a quoted
     LaTeX "\\!", "\\(" or "\\#" renders without its backslash.
  L6 a variable's star acting as an emphasis delimiter: every
     unescaped single star that follows a one-letter variable (a
     letter, optionally subscripted or primed, not itself preceded by
     a letter or an apostrophe: "ℓ*", "N*", "d*₁", "2x*") is escaped
     in a copy of its paragraph, and the rendering must not change;
     each star whose escape alone changes it is reported.
  L7 a stray star: an unescaped "*" left literal in the rendered text
     whose preceding character is not a letter, digit, subscript,
     superscript or prime -- the residue of an italic closed early
     ("*(note: f(x)* is real)*" leaves ")*") or of an opener that never
     closed. A literal star meant as text is written "\\*".
  L8 a literal backtick in the rendered text outside code: an unpaired
     backtick string (a quoted LaTeX ``open quote) that also stops a
     later code span from forming. Write it "\\`".
  L9 underscore emphasis: the surfaces never use "_" for emphasis, so
     escaping every unescaped "_" outside code, paragraph by paragraph,
     must not change the rendering ("|x|_p" opens an italic that a
     later "x_ " closes; the paper's 1bo(i) italicised half a
     paragraph this way).

Scope, stated: L1-L9 detect markup that does not render as written,
under cmark-gfm's server-side HTML. Not seen: a star after a
multi-letter token that closes an italic early while the stray it
leaves follows a letter; a quoted LaTeX escape of one of the allowed
characters ("\\_", "\\*", "\\~", "\\|"), which renders without its
backslash; and GitHub's client-side typesetting of "$...$" math, which
the server HTML does not carry. Those stay with the pre-landing
self-review. Code spans and code blocks are exempt (backtick strings
matched as maximal runs, never across a blank line). The per-item
tests of L6 and L9 render one paragraph at a time: cmark-gfm's process
grows by megabytes per whole-paper render (round 395 O2).

The script runs its own sabotage cases first (one per class, plus a
clean case that must pass) and fails if any rule misses its case, so
a rule that cannot fail cannot pass silently. Census line:
"render lint: <k> surfaces, <n> defects; probes <p>/<p> as expected".
Exit 0 iff no defects and every probe as expected; exit 2 if cmark-gfm
is missing (pip install -r tools/requirements.txt). Run by
run_tower.py as a precheck on every invocation.
"""
import html
import os
import re
import sys

try:
    import cmarkgfm
    from cmarkgfm.cmark import Options
except ImportError:
    print("render lint: cmarkgfm is not installed "
          "(pip install -r tools/requirements.txt)", flush=True)
    sys.exit(2)

ROOT = os.path.normpath(os.path.join(os.path.dirname(
    os.path.abspath(__file__)), "..", ".."))
SURFACES = ("riemann-indistinguishability.md",
            "cascade-riemann-formulation.md")
ALLOWED_ESCAPES = set("*_~`|\\")
OPT = Options.CMARK_OPT_UNSAFE
OPT_DT = OPT | Options.CMARK_OPT_STRIKETHROUGH_DOUBLE_TILDE
_SUBS = "₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₔₕₖₗₘₙₚₛₜ′'"
_SUPS = "⁰¹²³⁴⁵⁶⁷⁸⁹ⁿⁱ⁺⁻"


def _render(src, opt):
    return cmarkgfm.github_flavored_markdown_to_html(src, options=opt)


def _drop_code_html(h):
    h = re.sub(r"<pre.*?</pre>", " ", h, flags=re.S)
    return re.sub(r"<code>.*?</code>", " ", h, flags=re.S)


def _text(h):
    return html.unescape(re.sub(r"<[^>]+>", "", h))


# fenced blocks, then inline code spans -- backtick strings are
# maximal runs closed by a run of the same length, and a span never
# crosses a blank line (a paragraph boundary), so an unpaired
# backtick cannot mask the rest of the document; an escaped backtick
# opens nothing
_CODE = re.compile(r"^(```|~~~).*?^\1"
                   r"|(?<![`\\])(`+)(?!`)(?:(?!\n[ \t]*\n)[^\x00])+?(?<!`)\2(?!`)",
                   flags=re.S | re.M)


def _code_mask(src):
    mask = [False] * len(src)
    for m in _CODE.finditer(src):
        for k in range(m.start(), m.end()):
            mask[k] = True
    return mask


def _drop_code_src(src):
    mask = _code_mask(src)
    return "".join(" " if mask[k] else c for k, c in enumerate(src))


def _snip(s, n=90):
    s = re.sub(r"\s+", " ", s).strip()
    return s if len(s) <= n else s[:n] + " ..."


def _paragraphs(src):
    """(offset, text) of each blank-line-separated block."""
    return [(m.start(), m.group(0))
            for m in re.finditer(r"(?:[^\n]|\n(?![ \t]*\n))+", src)]


def _escaped(src, k):
    """True if src[k] is preceded by an odd run of backslashes."""
    n, j = 0, k - 1
    while j >= 0 and src[j] == "\\":
        n += 1
        j -= 1
    return n % 2 == 1


def lint(src):
    """Return a list of (rule, message) defects for one surface."""
    out = []
    gh = _render(src, OPT)
    dt = _render(src, OPT_DT)
    # L1: <del> spans present only under single-tilde parsing
    if gh != dt:
        dels_gh = re.findall(r"<del>(.*?)</del>", gh, flags=re.S)
        dels_dt = re.findall(r"<del>(.*?)</del>", dt, flags=re.S)
        pool = list(dels_dt)
        extra = []
        for d in dels_gh:
            if d in pool:
                pool.remove(d)
            else:
                extra.append(_snip(_text(d)))
        for d in extra or ["(renderings differ; no strike-span diff found)"]:
            out.append(("L1", "single-tilde strike over: " + d))
    body = _drop_code_html(gh)
    txt = _text(body)
    # L2, L3: literal delimiters left in the rendered text
    for rule, pat in (("L2", "~~"), ("L3", "**")):
        for m in re.finditer(re.escape(pat), txt):
            out.append((rule, f"literal {pat!r} at: "
                        + _snip(txt[max(0, m.start() - 60):m.start() + 30])))
    # L4: emphasis or strike opened inside a word
    for m in re.finditer(r"<(em|strong|del)>", body):
        prev = _text(body[max(0, m.start() - 80):m.start()])
        if prev and prev[-1].isalnum():
            j = body.find(f"</{m.group(1)}>", m.end())
            out.append(("L4", f"<{m.group(1)}> opened after "
                        f"{prev[-1]!r}: ..." + _snip(prev[-30:], 30)
                        + "[" + _snip(_text(body[m.end():j]), 50) + "]"))
    mask = _code_mask(src)
    # L5: a backslash markdown consumes, outside code
    for m in re.finditer(r"\\([!-/:-@\[-`{-~])", _drop_code_src(src)):
        if m.group(1) not in ALLOWED_ESCAPES and not _escaped(src, m.start()):
            ln = src.count("\n", 0, m.start()) + 1
            out.append(("L5", f"line {ln}: backslash consumed before "
                        f"{m.group(1)!r}"))
    # L6 / L9: per paragraph, escaping the candidates must not change
    # the rendering; per-item tests only inside a paragraph that changed
    stars = set(_variable_stars(src, mask))
    for off, para in _paragraphs(src):
        cands = {"L6": [k for k in range(len(para)) if off + k in stars],
                 "L9": [k for k, c in enumerate(para)
                        if c == "_" and not mask[off + k]
                        and not _escaped(para, k)]}
        base = None
        for rule, ks in cands.items():
            if not ks:
                continue
            base = base or _render(para, OPT)
            esc = list(para)
            for k in ks:
                esc[k] = "\\" + para[k]
            if _render("".join(esc), OPT) == base:
                continue
            for k in ks:
                if _render(para[:k] + "\\" + para[k:], OPT) != base:
                    ln = src.count("\n", 0, off + k) + 1
                    what = ("variable star acts as a delimiter"
                            if rule == "L6" else
                            "underscore acts as an emphasis delimiter")
                    out.append((rule, f"line {ln}: {what}: ..." + _snip(
                        para[max(0, k - 40):k + 20], 70)))
    # L7, L8: stray literal stars and backticks (escaped ones swapped
    # for an escaped sentinel of the same punctuation class, so only
    # unescaped ones can render as "*" or "`")
    sent = []
    k = 0
    while k < len(src):
        if (src[k] == "\\" and k + 1 < len(src) and src[k + 1] in "*`"
                and not mask[k] and not _escaped(src, k)):
            sent.append("\\@")
            k += 2
            continue
        sent.append(src[k])
        k += 1
    stxt = _text(_drop_code_html(_render("".join(sent), OPT)))
    for m in re.finditer(r"\*", stxt):
        prev = stxt[m.start() - 1] if m.start() else ""
        if not (prev.isalnum() or prev in _SUBS or prev in _SUPS):
            out.append(("L7", "stray '*' after " + repr(prev) + ": "
                        + _snip(stxt[max(0, m.start() - 50):m.start() + 20])))
    for m in re.finditer("`", stxt):
        out.append(("L8", "literal backtick at: "
                    + _snip(stxt[max(0, m.start() - 50):m.start() + 30])))
    return out


def _variable_stars(src, code=None):
    """Offsets of unescaped single stars that follow a one-letter
    variable (a letter, optionally subscripted or primed, not itself
    preceded by a letter or an apostrophe), outside code."""
    code = code if code is not None else _code_mask(src)
    out = []
    for m in re.finditer(r"(?<![\\*])\*(?!\*)", src):
        i = m.start()
        if code[i]:
            continue
        j = i - 1
        while j >= 0 and src[j] in _SUBS:
            j -= 1
        if j < 0 or not src[j].isalpha():
            continue
        if j > 0 and (src[j - 1].isalpha() or src[j - 1] in "'’"):
            continue
        out.append(i)
    return out


# the sabotage cases: each rule must fire on its own case, and the
# clean case must pass (a rule that cannot fail is a finding)
PROBES = (
    ("L1", "about ~9.3 layers, and here~ it ends\n"),
    ("L2", "x ~~carry errors at ~6 decades per level~~ (struck)\n"),
    ("L3", "a **bold that never closes\n"),
    ("L4", "the d*₁ = 19.73, while 27.73 = d*₁ + 8\n"),
    ("L5", "the formula \\psi\\!\\left(x\\right)\n"),
    ("L6", "*(round 224: the crossover ℓ* = 0.456 is sub-spacing)*\n"),
    ("L7", "*(note: the conjugate f(x)* is real, see 1aa)* rest\n"),
    ("L8", "a quoted ``open quote'' and then `code.py` here\n"),
    ("L9", "the norm |x|_p^s and the tail x_ here\n"),
    (None, "~~struck~~ *em* **strong** x\\* ≈ 9.3, \\~9, τ* = 2, "
           "a_k and `a*b ~c~` \\`\\`q''\n"),
)


def probes():
    good = 0
    for rule, src in PROBES:
        got = {r for r, _ in lint(src)}
        if (rule is None and not got) or (rule is not None and rule in got):
            good += 1
        else:
            print(f"  PROBE UNEXPECTED: rule {rule} on {src!r} -> "
                  f"{sorted(got)}", flush=True)
    return good


def main():
    good = probes()
    total = 0
    for s in SURFACES:
        p = os.path.join(ROOT, s)
        defects = lint(open(p, encoding="utf-8").read())
        total += len(defects)
        for rule, msg in defects:
            print(f"  {s}: {rule} {msg}", flush=True)
    print(f"render lint: {len(SURFACES)} surfaces, {total} defects; "
          f"probes {good}/{len(PROBES)} as expected", flush=True)
    sys.exit(0 if total == 0 and good == len(PROBES) else 1)


if __name__ == "__main__":
    main()
