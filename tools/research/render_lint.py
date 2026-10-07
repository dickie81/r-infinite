#!/usr/bin/env python3
"""The render lint for the markdown paper surfaces (owner's residual
sweep, round 395; CLAUDE.md "Proportionate checking" item 5: a defect
class found twice gets a cheap automated check).

Rounds 389-393 found delimiters that GitHub does not render as written
(F390-1, A562 O-1, A563 F391-2) by hand; this script renders each
surface with cmark-gfm -- the renderer behind GitHub's markdown, whose
HTML for this paper matched GitHub's own API rendering in the
<del> census at 2b76ff1 (183 = 183) -- and fails on five defect
classes, each decidable from the rendering:

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
     on purpose (* _ ~ ` | [ ] # < > ( ) and the backslash itself) --
     e.g. a quoted LaTeX "\\!" renders as "!".
  L6 a variable's star acting as an emphasis delimiter: every
     unescaped single star that follows a one-letter variable (a
     letter, optionally subscripted or primed, not itself preceded by
     a letter or an apostrophe: "ℓ*", "N*", "d*₁", "2x*") is escaped
     in a copy, and the rendering must not change; each star whose
     escape alone changes it is reported. This catches the star that
     closes an intended italic early ("*(... ℓ* = 0.456 ... ≥ 1)*"
     rendered half-italic with a dangling "*") as well as the pairs
     L4 sees.

Scope, stated: L1-L6 detect markup that does not render as written.
A star after a multi-letter token ("aim*") is outside L6's variable
rule and stays with the pre-landing self-review. Code spans and code
blocks are exempt (backtick strings matched as maximal runs, never
across a blank line).

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
ALLOWED_ESCAPES = set("*_~`|[]#<>()\\")
OPT = Options.CMARK_OPT_UNSAFE
OPT_DT = OPT | Options.CMARK_OPT_STRIKETHROUGH_DOUBLE_TILDE


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
# backtick cannot mask the rest of the document
_CODE = re.compile(r"^(```|~~~).*?^\1"
                   r"|(?<!`)(`+)(?!`)(?:(?!\n[ \t]*\n)[^\x00])+?(?<!`)\2(?!`)",
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
                extra.append(d)
        for d in extra or ["(renderings differ; no <del> diff found)"]:
            out.append(("L1", "single-tilde strike over: "
                        + _snip(_text(d))))
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
    # L5: a backslash markdown consumes, outside code
    for m in re.finditer(r"\\([!-/:-@\[-`{-~])", _drop_code_src(src)):
        if m.group(1) not in ALLOWED_ESCAPES:
            out.append(("L5", f"backslash consumed before "
                        f"{m.group(1)!r}"))
    # L6: a variable's star acting as an emphasis delimiter -- escape
    # every star that follows a one-letter variable (ℓ*, N*, d*₁, x*)
    # and require the rendering to be unchanged
    stars = _variable_stars(src)
    if stars:
        esc = list(src)
        for i in stars:
            esc[i] = "\\*"
        if _render("".join(esc), OPT) != gh:
            for i in stars:
                one = src[:i] + "\\*" + src[i + 1:]
                if _render(one, OPT) != gh:
                    ln = src.count("\n", 0, i) + 1
                    out.append(("L6", f"line {ln}: variable star acts "
                                "as a delimiter: ..." + _snip(
                                    src[max(0, i - 40):i + 20], 70)))
    return out


_SUBS = "₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₔₕₖₗₘₙₚₛₜ′'"


def _variable_stars(src):
    """Offsets of unescaped single stars that follow a one-letter
    variable (a letter, optionally subscripted or primed, not itself
    preceded by a letter), outside code."""
    code = _code_mask(src)
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
    (None, "~~struck~~ *em* **strong** x\\* ≈ 9.3, \\~9, τ* = 2 and "
           "`a*b ~c~`\n"),
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
