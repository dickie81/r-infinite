#!/usr/bin/env python3
"""The render lint for the markdown paper surfaces (owner's residual
sweep, round 395; CLAUDE.md "Proportionate checking" item 5: a defect
class found twice gets a cheap automated check).

Rounds 389-393 found delimiters that GitHub does not render as written
(F390-1, A562 O-1, A563 F391-2) by hand; this script renders each
surface with cmark-gfm -- the renderer behind GitHub's markdown, whose
HTML for this paper matched GitHub's own API rendering at 2b76ff1 and
49ab366 (the round-395 reviewers compared the visible text and the
em/strong/del/code markers) -- and fails on twenty-one defect classes,
each decidable from the rendering:

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
  L10 a block with no blank line before it, decided from the
     source-positioned rendering: a list, blockquote, heading,
     thematic break, code block or table whose first line directly
     follows a non-blank line (blockquote markers aside) -- a
     hard-wrapped line that begins with "+ ", "1) ", "> ", "***" or
     "~~~" (round 396: nine such lines dropped their operators from
     formulas in 1bf-1ca; round 397 F397-A1/B2 decided it from the
     rendering). Re-wrap an accidental one; give an intended one,
     nested or not, a blank line before it (a nested list made loose
     by this is the price; the surfaces nest none).
  L11 a setext heading: a heading whose source line does not begin
     with "#" (a stray "===" or "---" under a line of text).
  L12 a hard line break (<br>): a trailing backslash or two trailing
     spaces; the surfaces never break lines inside a paragraph.
  L13 raw HTML of any kind, inline or block, tag or comment: every
     "raw HTML omitted" in cmark-gfm's safe rendering ("a<b and c>d"
     renders "ad"; "2<p and q>3" and a line beginning "<p " too --
     round 397 F397-A2/B2: the round-396 form exempted tag names
     markdown also produces).
  L14 an indented code block: a <pre> whose source line is not a
     fence.
  L15 a run of two or more backticks outside a fence: the surfaces
     use none, and a LaTeX ``open quote is one -- two of them in a
     paragraph form a code span that swallows the text between,
     code spans included (round 396 F396-A2; round 397 F397-A2;
     round 398 F398-A1/B3: the round-397 form required the span to
     hold no backtick, so a code span between the quotes hid it).
     Write "\\`\\`".
  L16 a line that continues a block it does not belong to (lazy
     continuation): a line inside a blockquote that does not begin
     with ">" (after any list markers), a line inside a list item that
     is neither indented nor an item (quote markers aside; a list
     inside an indented quote is not checked, round 401 F401-A2), and
     a table line that does not
     begin and end with "|" or has another count of unescaped "|" than
     the header -- prose absorbed as a row, prose whose "|x|" and a
     following "-|-" made a table, or an unescaped "|x|" that splits
     a cell (round 398 F398-A2: a marker written directly under a
     quote, a table or a list joined it; round 399 F399-A2, its in-paper
     case IP3, added the end and the cell count).
  L17 the text is not what the source says: the letters and digits of
     the source, in order (an ordered item's number, which L20 checks,
     and the first word of a rendered fence's info string, which cmark
     keeps as its language, aside -- round 400 F400-A2), must be exactly
     those of the rendering, and the rendering may hold no element
     outside the allowlist of block and inline elements, a superset
     of what the surfaces render: paragraphs, emphasis, strikes, code
     and code blocks, lists, quotes, headings, rules, tables and line
     breaks (round 401 F401-A3/C1: the surfaces render no code block,
     line break or heading below h3; round 400 F400-B10: not
     "plain markdown's elements" -- strikes and tables are GFM's, and
     CommonMark's own links and images are outside it, as are an
     autolink, a task checkbox and a footnote). A
     character reference, a link's target, a link reference
     definition, a task box and a footnote each fail it (round 398
     F398-A2/B3, the third round to find such a class: one invariant
     in place of further rules).
  L18 a top-level block with no blank line after it (round 398
     F398-A2/B3; a rule of its own since round 399, F399-A4/B4, so a
     probe pins it alone).
  L19 a paragraph with no source position: the table under it
     absorbed it (round 398 F398-A2/B3; its own rule since round 399).
  L20 an ordered list item whose rendered number differs from its
     source number -- an item inserted or deleted without
     renumbering, so a cross-reference by number points elsewhere
     (round 399 F399-A2).
  L21 a table delimiter row of two or more cells ("|---|---|") that no
     rendered table holds: the table did not form -- an unescaped "|x|"
     in its header, or a
     header and delimiter row of different widths -- and the whole table
     rendered as one paragraph of bars and dashes (round 400 F400-A1).

Scope, stated: L1-L21 detect markup that does not render as written,
under cmark-gfm's server-side HTML with GitHub's footnotes. The "Not
seen" list below is what the reviews of rounds 395-401 found and the
rules do not catch; it is the survey's record, not a proof that
nothing else exists. Not seen: a star after a multi-letter token that
closes an italic early while the stray it leaves follows a letter; a
quoted LaTeX escape of one of the allowed characters ("\\_", "\\*",
"\\~", "\\|", "\\`" and the backslash itself), which renders without its
backslash; a pair of LaTeX single open-quotes ("`a' ... `b'"), which
forms an ordinary one-backtick code span; inside a list, a wrapped
line that begins with the item's own marker, which renders as a
sibling item; an unescaped "|" inside a table cell that splits it
while the row keeps the header's cell count; a "|"-led line that ends
with "|" and has the header's cell count, written directly under a
table, which joins it as a row; an accidental fence whose opening
line holds one word (a struck "~~~0.3%~~" alone at a paragraph start),
which renders the rest of its container as code with every letter
kept, and the line on which a container closes an unclosed fence,
which the code mask also covers (round 401 F401-A1); a lazy line of a
list inside an indented quote (F401-A2); a one-column table that did
not form (F401-A5/B8/C9); and GitHub's client-side typesetting
of "$...$" math,
which the server HTML does not carry. Those stay with the pre-landing
self-review. Code spans (backtick strings matched as maximal runs,
never across a blank line) and the lines the renderer put in a <pre>
(round 400 F400-A2) are exempt from L5-L9; an indented code block is
itself a defect (L14). The per-item
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
from html.parser import HTMLParser

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
# GitHub renders footnotes (round 398: without the option a footnote
# rendered as plain text here and L17 could not see it)
OPT = Options.CMARK_OPT_UNSAFE | Options.CMARK_OPT_FOOTNOTES
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


# code blocks are the lines the renderer itself put in a <pre> (round
# 400 F400-A2: the lint's own fence pairing differed from cmark's and
# masked text the renderer dropped); inline code spans are backtick
# strings matched as maximal runs closed by a run of the same length,
# never across a blank line (a paragraph boundary) or into a code
# block, so an unpaired backtick cannot mask the rest of the document;
# an escaped backtick opens nothing
_SPAN = re.compile(r"(?<![`\\])(`+)(?!`)(?:(?!\n[ \t]*\n)[^\x00])+?(?<!`)\1(?!`)",
                   flags=re.S)
_PRE_MEMO = {}


def _pre_lines(src):
    """The source lines of every code block the renderer produced, and
    the first line of each (sourcepos), memoized per source."""
    if src not in _PRE_MEMO:
        if len(_PRE_MEMO) > 64:
            _PRE_MEMO.clear()
        h = _render(src, OPT | Options.CMARK_OPT_SOURCEPOS)
        lines, starts = set(), set()
        for m in re.finditer(r'<pre[^>]*data-sourcepos="(\d+):\d+-(\d+):(\d+)"',
                             h):
            a, b, c = int(m.group(1)), int(m.group(2)), int(m.group(3))
            if c == 0 and b > a:
                b -= 1
            lines.update(range(a, b + 1))
            starts.add(a)
        _PRE_MEMO[src] = (frozenset(lines), frozenset(starts))
    return _PRE_MEMO[src]


def _fence_mask(src):
    lines = _pre_lines(src)[0]
    mask, ln = [], 1
    for c in src:
        mask.append(ln in lines)
        if c == "\n":
            ln += 1
    return mask


def _code_mask(src):
    mask = _fence_mask(src)
    blanked = "".join(" " if mask[k] and c != "\n" else c
                      for k, c in enumerate(src))
    for m in _SPAN.finditer(blanked):
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
    # L15: any unescaped run of two or more backticks outside a fence
    # (round 398 F398-A1/B3: the round-397 form, "no backtick inside",
    # was silent when a code span sat between two LaTeX open-quotes)
    fence = _fence_mask(src)
    for m in re.finditer(r"(?<![`\\])``+", src):
        if not fence[m.start()]:
            ln = src.count("\n", 0, m.start()) + 1
            out.append(("L15", f"line {ln}: a run of {len(m.group(0))} "
                        "backticks (a LaTeX ``open quote?)"))
    out += _block_defects(src, gh)
    return out


_QUOTE_PREFIX = re.compile(r"^\s*(?:>\s?)*")
_RAW_HTML = "<!-- raw HTML omitted -->"
# a list item's later line, quote markers first removed: indented, or an
# item of its own (round 399 F399-A3/B5: a quoted list's indented line)
_ITEM_LINE = re.compile(r"\s|\s*(?:[-*+]|\d+[.)])(?:\s|$)")
_QUOTE_MARKS = re.compile(r"^\s*(?:>\s?)+")
# quote markers and list markers, in any order (round 400 F400-A4: a
# quote, table or heading opening a list item)
_BLOCK_PREFIX = re.compile(r"^(?:\s*(?:>\s?|(?:[-*+]|\d+[.)])\s+))*\s*")
_DELIM_ROW = re.compile(r"^\|?\s*:?-+:?\s*(?:\|\s*:?-+:?\s*)+\|?\s*$")
_FENCE_OPEN = re.compile(r"^(\s*(?:>\s?)*\s*(?:(?:[-*+]|\d+[.)])\s+)*"
                         r"(?:`{3,}|~{3,}))(.*)$")
# the allowlist: block and inline elements, a superset of what the
# surfaces render (paragraphs, emphasis, strike, code and code blocks,
# lists, quotes, headings, rules, tables, line breaks); anything else
# in the rendering (a link,
# autolink, image, task checkbox, footnote) is a construct they never
# use on purpose (L17)
_USED_TAGS = {"p", "em", "strong", "del", "code", "pre", "ul", "ol", "li",
              "blockquote", "h1", "h2", "h3", "h4", "h5", "h6", "hr",
              "table", "thead", "tbody", "tr", "th", "td", "br"}
_BLOCK_TAGS = {"p", "ul", "ol", "li", "blockquote", "h1", "h2", "h3", "h4",
               "h5", "h6", "hr", "pre", "table"}


class _Blocks(HTMLParser):
    """Every block element of the source-positioned rendering: tag,
    first and last source line (a trailing blank line excluded), the
    raw position, and its depth among block elements."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack, self.els = [], []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag not in _BLOCK_TAGS or "data-sourcepos" not in a:
            return
        m = re.match(r"(\d+):(\d+)-(\d+):(\d+)", a["data-sourcepos"])
        sl, _sc, el, ec = map(int, m.groups())
        if ec == 0 and el > sl:
            el -= 1
        e = {"tag": tag, "s": sl, "e": el, "raw": a["data-sourcepos"],
             "depth": len(self.stack)}
        if tag == "ol":
            e["next"] = int(a.get("start") or 1)
        if tag == "li" and self.stack and self.stack[-1]["tag"] == "ol":
            e["num"] = self.stack[-1]["next"]
            self.stack[-1]["next"] += 1
        self.els.append(e)
        if tag != "hr":
            self.stack.append(e)

    def handle_endtag(self, tag):
        if tag in _BLOCK_TAGS and self.stack and self.stack[-1]["tag"] == tag:
            self.stack.pop()


def _block_defects(src, gh):
    """L10-L14 and L16-L20 from the source-positioned rendering."""
    out = []
    lines = src.split("\n")
    h = _render(src, OPT | Options.CMARK_OPT_SOURCEPOS)
    h_nocode = _drop_code_html(h)
    tree = _Blocks()
    tree.feed(h)

    def blank(i):
        return (i < 1 or i > len(lines)
                or not _QUOTE_PREFIX.sub("", lines[i - 1]).strip())

    for e in tree.els:
        t, s0, e0 = e["tag"], e["s"], e["e"]
        if e["raw"].startswith("0:0"):
            out.append(("L19", f"<{t}> has no source position: a paragraph "
                        "absorbed by the block that follows it"))
            continue
        if t == "li":
            # L16: a list item's later lines are indented or begin an item
            for i in range(s0 + 1, e0 + 1):
                raw = lines[i - 1]
                if not raw.strip() or raw[:1] in " \t":
                    continue        # indented: inside the item
                ln = _QUOTE_MARKS.sub("", raw)     # a list inside a quote
                if not _ITEM_LINE.match(ln):
                    out.append(("L16", f"line {i}: lazy continuation into a "
                                "list item: " + _snip(lines[i - 1], 50)))
            # L20: an ordered item renders the number its source gives
            m = re.match(r"\s*(?:>\s?)*\s*(\d+)[.)]", lines[s0 - 1])
            if "num" in e and m and int(m.group(1)) != e["num"]:
                out.append(("L20", f"line {s0}: the item renders as "
                            f"{e['num']} but its source says {m.group(1)}"))
            continue
        # L10: a blank line before every block other than a paragraph;
        # L18: a blank line after every top-level block (a top-level
        # paragraph's line before is the line after the block above it)
        if t != "p" and not blank(s0 - 1):
            out.append(("L10", f"line {s0}: <{t}> has no blank line before "
                        "it: ..." + _snip(lines[s0 - 2][-40:], 40) + " | "
                        + _snip(lines[s0 - 1][:40], 40)))
        if e["depth"] == 0 and not blank(e0 + 1):
            out.append(("L18", f"line {e0}: <{t}> has no blank line after "
                        "it: ..." + _snip(lines[e0 - 1][-40:], 40) + " | "
                        + _snip(lines[e0][:40], 40)))
        # L16: every line of a blockquote begins with ">", every line of
        # a table with "|"
        if t == "blockquote":
            for i in range(s0, e0 + 1):
                if lines[i - 1].strip() and not re.match(
                        r"(?:\s*(?:[-*+]|\d+[.)])\s+)*\s*>", lines[i - 1]):
                    out.append(("L16", f"line {i}: lazy continuation into a "
                                "blockquote: " + _snip(lines[i - 1], 50)))
        if t == "table":
            # every line begins and ends with "|" and has the header's
            # cell count (round 399 F399-A2/B6: an unescaped "|x|" in a
            # cell splits it; a "|"-led line under a table joins it)
            cells = None
            for i in range(s0, e0 + 1):
                ln = _BLOCK_PREFIX.sub("", lines[i - 1]).strip()
                n = len(re.findall(r"(?<!\\)(?:\\\\)*\|", ln))
                cells = n if cells is None else cells
                if not (ln.startswith("|") and ln.endswith("|")) \
                        or n != cells:
                    out.append(("L16", f"line {i}: a table line that does not "
                                "begin and end with '|' or has another cell "
                                "count than the header: "
                                + _snip(lines[i - 1], 50)))
        body = _BLOCK_PREFIX.sub("", lines[s0 - 1])
        if t[0] == "h" and t != "hr" and not body.startswith("#"):
            out.append(("L11", f"line {s0}: setext heading: "
                        + _snip(lines[s0 - 1], 60)))
        if t == "pre" and not body.startswith(("```", "~~~")):
            out.append(("L14", f"line {s0}: indented code block"))
    # L21: a delimiter row that no rendered table holds -- a table that
    # did not form (round 400 F400-A1: an unescaped "|x|" in the header,
    # or a header and delimiter row of different widths, turns the whole
    # table into one paragraph of bars and dashes)
    spans = [(e["s"], e["e"]) for e in tree.els if e["tag"] == "table"]
    code_lines = _pre_lines(src)[0]
    for i, raw in enumerate(lines, 1):
        if i in code_lines or not _DELIM_ROW.match(
                _BLOCK_PREFIX.sub("", raw).strip()):
            continue
        if not any(a <= i <= b for a, b in spans):
            out.append(("L21", f"line {i}: a table delimiter row that no "
                        "table holds (the table did not form): "
                        + _snip(raw, 50)))
    for m in re.finditer(r"<br\s*/?>", h_nocode):
        out.append(("L12", "hard line break at: " + _snip(
            _text(h_nocode[max(0, m.start() - 80):m.start()]), 60)))
    safe = _render(src, Options.CMARK_OPT_FOOTNOTES)
    for m in re.finditer(re.escape(_RAW_HTML), safe):
        out.append(("L13", "raw HTML at: ..." + _snip(
            _text(safe[max(0, m.start() - 80):m.start()])[-50:], 50)))
    # L17: the letters and digits survive rendering, in order (an
    # ordered item's number aside), and no element appears that the
    # surfaces never use
    items = {e["s"] for e in tree.els if e["tag"] == "li"}
    pre_starts = _pre_lines(src)[1]

    def norm(i, ln):
        # an ordered item's number (L20 checks it) and the first word
        # of a rendered fence's info string (cmark keeps it as the
        # language; round 399 F399-A3/B5) are not rendered as text --
        # the rest of an info string is dropped, so it stays in the
        # comparison (round 400 F400-A2: a stray "~~~" at a paragraph
        # start swallows its line into an info string)
        if i + 1 in items:
            ln = re.sub(r"^(\s*(?:>\s?)*\s*)\d+[.)]", r"\1", ln)
        if i + 1 in pre_starts:
            m = _FENCE_OPEN.match(ln)
            if m:
                ln = m.group(1) + " " + " ".join(m.group(2).split()[1:])
        return ln
    src2 = "\n".join(norm(i, ln) for i, ln in enumerate(lines))
    a = "".join(c for c in src2 if c.isalnum())
    b = "".join(c for c in _text(gh) if c.isalnum())
    if a != b:
        k = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y),
                 min(len(a), len(b)))
        out.append(("L17", "text changed by the rendering at: ..."
                    + a[max(0, k - 30):k + 20] + " -> ..."
                    + b[max(0, k - 30):k + 20]))
    for t in sorted(set(re.findall(r"<([a-zA-Z][a-zA-Z0-9]*)", gh))
                    - _USED_TAGS):
        out.append(("L17", f"an element the surfaces never use: <{t}>"))
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
    ("L10", "the sum S(T) = arg ζ(½\n+ iT) up to a remainder\n"),
    ("L10", "text line one\n|x| + y is the norm\n+ iT) continues it\n"),
    ("L10", "> a quoted sum ζ(½\n> + iT) continues it\n"),
    ("L10", "a wrapped product\n***\n"),
    ("L10", "a strike that wraps\n~~~230~~ and more\n\nnext\n"),
    ("L11", "a stray rule under text\n===\n"),
    ("L12", "a line ending in a backslash\\\nand the next\n"),
    ("L13", "the order a<b and c>d holds\n"),
    ("L13", "for q<p and p>3 we sum\n"),
    ("L13", "a <!-- hidden --> c\n"),
    ("L13", "the bound holds\n<p ≤ x for every prime\n"),
    ("L14", "para\n\n    an indented line\n"),
    ("L15", "the ``one period'' and the ``other'' here\n"),
    ("L15", "says ``one period'' (gated in `x.py`), and ``the other''\n"),
    ("L19", "intro text\n| a | b |\n|---|---|\n| 1 | 2 |\n"),
    ("L18", "# a heading\ntext right under it\n"),
    ("L18", ">\n# a heading\n"),
    ("L19", "\n|---|---|\n| a | b |\n|---|---|\n"),
    ("L20", "1. one\n2. two\n4. four\n"),
    ("L16", "| a | b |\n|---|---|\n| 1 | 2 |\n|x| + y\n"),
    ("L16", "| a | b | c |\n|---|---|---|\n| norm of |x| | 5 | ok |\n"),
    ("L16", "| p | q | note |\n|---|---|---|\n| 7 | ab is |small| —\n"),
    ("L16", "| a | b | c |\n|---|---|---|\nx | y | z | |\n"),
    ("L21", "| a | b |\n|---|---|---|\n| 1 | 2 |\n"),
    ("L17", "~~~4 supports~~ five supports are certified\n"),
    ("L16", "> a quoted line\n*(a marker)*\n"),
    ("L16", "| a | b |\n|---|---|\n| 1 | 2 |\n*(a marker)*\n"),
    ("L16", "1. item one\na lazy line\n"),
    ("L16", "|x| + y is the norm\n-|-\n"),
    ("L17", "the letter &#x3B1; here\n"),
    ("L17", "see [0, 1](x) here\n"),
    ("L17", "text\n\n[a]: b\n"),
    ("L17", "see <https://ab.cd/ef> here\n"),
    ("L17", "- [x] done\n"),
    ("L17", "a claim[^1] here\n\n[^1]: the note\n"),
    (None, "para one\n\n> quote\n\n| a |\n|---|\n| 1 |\n\n1. one\n"
           "2. two\n\n- x\n- y\n\n> # quoted heading\n\n   ```\n"
           "   a fenced line\n   ```\n\n> 1. a quoted item\n>    continued\n"
           "\n```python\nprint(1)\n```\n\n1. # a heading in an item\n\n"
           "- ```\n  code line\n  ```\n\n1. an item\n\n   > a quote in it\n\n"
           "- | a | b |\n  |---|---|\n  | 1 | 2 |\n\n~~~\n```python\nx = 1\n```\n"
           "~~~\n\n1. > a quoted line\n   > its second line\n"),
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
