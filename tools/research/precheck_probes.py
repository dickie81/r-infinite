#!/usr/bin/env python3
"""THE PRECHECK PROBE SUITE (committed round 277, F276-3: "N probes
green" was a session run with no committed artifact). Executes the
driver's precheck definitions (run_tower.py split at the scan loop,
so no tower is launched) and runs every sabotage / clean case
against _precheck_file on scratch files. Each case states its
expected verdict; the suite exits 1 on any unexpected one and
prints the census. Cases carry the round that introduced them.

Not in any member's reach (nothing imports or names this file),
so running or editing it rotates no cache key.
"""
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
sys.path.insert(0, HERE)

_src = open(os.path.join(HERE, "run_tower.py"), encoding="utf-8").read()
_defs = _src.split("\n_scan = set()")[0]
_ns = {"__name__": "driver_defs",
       "__file__": os.path.join(HERE, "run_tower.py")}
exec(compile(_defs, "run_tower_defs", "exec"), _ns)
_pf = _ns["_precheck_file"]

IMP = "import paper_needles\n"
DECL = 'PAPER_NEEDLES = [{"g": "g1", "s": "anchor", "form": "plain"}]\n'
GATE = 'ok, _ = paper_needles.verify(PAPER_NEEDLES, g="g1")\n'
PATH = ('import sys, os\nsys.path.insert(0, os.path.join('
        'os.path.dirname(__file__), "..", ".."))\n')

# (name, body, expect_flagged)
CASES = [
    # clean controls
    ("control_clean", IMP + DECL + GATE
     + 'ok2 = paper_needles.needle(PAPER_NEEDLES, "anchor", "plain")\n',
     False),
    ("r275_declared_loop", IMP + DECL + GATE
     + 'for d in paper_needles.declared(PAPER_NEEDLES):\n'
       '    print(d["s"])\n', False),
    ("r274_code_swap_textfree", IMP + DECL + GATE
     + "def gate(l, ok): pass\ndef _r(l, ok): pass\n"
       "gate.__code__ = _r.__code__\n", True),   # dunder now flags (F)
    ("r275_cross_module_textfree", IMP + DECL + GATE
     + "import cascade_floor_theory\nx = cascade_floor_theory.ok\n",
     False),
    ("local_import_ok", DECL + "def f():\n    import paper_needles\n"
     "    return paper_needles.verify(PAPER_NEEDLES)\n", False),
    ("init_name_dunders_ok", IMP + DECL + GATE
     + "class K:\n    def __init__(s): super().__init__()\n"
       "n = K.__name__\n", False),
    # (A) paper-naming constants
    ("A_filename_constant", IMP + DECL + GATE
     + 'p = open("../../riemann-indistinguishability.md").read()\n', True),
    ("A_filename_in_join", IMP + DECL + GATE
     + 'import os\np = os.path.join("x", "riemann-indistinguishability.md")\n',
     True),
    ("A_implicit_concat", IMP + DECL + GATE
     + 'p = "riemann-" "indistinguishability.md"\n', True),
    # (A2) module-naming constants (round 277)
    ("A2_dunder_import", 'm = __import__("paper_needles")\n'
     't = open(m.PAPER_PATH).read()\n', True),
    ("A2_sys_modules", IMP + DECL + GATE
     + 'import sys\nm = sys.modules["paper_needles"]\n', True),
    ("A2_importlib", 'import importlib\n'
     'm = importlib.import_module("paper_needles")\n', True),
    # (B) module binding and use
    ("B_import_alias", "import paper_needles as pn\n" + DECL
     + "ok, _ = pn.verify(PAPER_NEEDLES)\n", True),
    ("B_from_import", "from paper_needles import PAPER_PATH\n" + IMP + DECL
     + GATE, True),
    ("B_internal_attr", IMP + DECL + GATE
     + "t = open(paper_needles.PAPER_PATH).read()\n", True),
    ("B_check_attr", IMP + DECL
     + 'ok, _ = paper_needles.check(PAPER_NEEDLES, "x")\n', True),
    ("B_forms_launder", IMP + DECL
     + 'mirror = paper_needles.forms("x")["raw"]\n', True),
    ("B_bare_name", IMP + DECL + GATE + "m = vars(paper_needles)\n", True),
    ("B_rebind", IMP + DECL + GATE + "paper_needles = None\n", True),
    ("B_param_shadow", IMP + DECL
     + "def f(paper_needles):\n    return paper_needles.verify(PAPER_NEEDLES)\n",
     True),
    ("B_local_alias_import", DECL + "def f():\n    import paper_needles as q\n"
     "    return q.verify(PAPER_NEEDLES)\n", True),
    # (B) round-277 F276-1: function-object and import spellings
    ("B_globals_chain", IMP + DECL + GATE
     + 't = paper_needles.verify.__globals__["_TEXTCACHE"]\n', True),
    ("B_needle_globals_path", IMP + DECL
     + 't = open(paper_needles.needle.__globals__["PAPER_PATH"]).read()\n',
     True),
    ("B_attr_as_value", IMP + DECL + "f = paper_needles.verify\n"
     "ok, _ = f(PAPER_NEEDLES)\n", True),
    ("B_from_package_alias", PATH
     + "from tools.research import paper_needles as pn\n"
       "t = open(pn.PAPER_PATH).read()\n", True),
    ("B_from_package_plain", PATH
     + "from tools.research import paper_needles\n" + DECL + GATE, True),
    ("B_dotted_import", PATH + "import tools.research.paper_needles\n"
     "t = open(tools.research.paper_needles.PAPER_PATH).read()\n", True),
    ("B_from_research", PATH + "from research import paper_needles as pn\n"
     "t = open(pn.PAPER_PATH).read()\n", True),
    ("B_from_dotted_module", PATH
     + "from tools.research.paper_needles import PAPER_PATH\n", True),
    ("B_via_member_namespace", IMP + DECL + GATE
     + "import cascade_floor_theory\n"
       "t = open(cascade_floor_theory.paper_needles.PAPER_PATH).read()\n",
     True),
    ("B_from_member", "from cascade_floor_theory import paper_needles\n"
     + DECL + GATE, True),
    ("B_star_import", "from cascade_floor_theory import *\n" + DECL + GATE,
     True),
    # (F) introspection dunders (round 277)
    ("F_class_chain", IMP + DECL + GATE
     + "c = ().__class__.__base__.__subclasses__()\n", True),
    ("F_dict", IMP + DECL + GATE + "d = paper_needles.__dict__\n", True),
    ("F_code_filename", IMP + DECL + GATE
     + "p = paper_needles.declared.__code__.co_filename\n", True),
    # (C) the declaration
    ("C_append", IMP + DECL
     + 'PAPER_NEEDLES.append({"s": "secret", "form": "raw"})\n' + GATE, True),
    ("C_augassign", IMP + DECL
     + 'PAPER_NEEDLES += [{"s": "secret", "form": "raw"}]\n' + GATE, True),
    ("C_subscript_store", IMP + DECL + 'PAPER_NEEDLES[0]["s"] = "secret"\n'
     + GATE, True),
    ("C_alias", IMP + DECL + "D = PAPER_NEEDLES\n" + GATE, True),
    ("C_comprehension", IMP + DECL
     + "ok, _ = paper_needles.verify([d for d in PAPER_NEEDLES])\n", True),
    ("C_for_loop", IMP + DECL + 'for d in PAPER_NEEDLES:\n    d["s"] = "x"\n'
     + GATE, True),
    ("C_list_append_fn", IMP + DECL
     + 'list.append(PAPER_NEEDLES, {"s": "secret", "form": "raw"})\n'
     + GATE, True),
    ("C_two_decls", IMP + DECL + DECL + GATE, True),
    ("C_computed_decl", IMP
     + 'PAPER_NEEDLES = [{"s": "a" + "b", "form": "raw"}]\n' + GATE, True),
    ("C_invalid_entry", IMP + 'PAPER_NEEDLES = [{"s": "a", "form": "bogus"}]\n'
     + GATE, True),
    # (D) call shapes
    ("D_needle_undeclared", IMP + DECL
     + 'ok = paper_needles.needle(PAPER_NEEDLES, "secret", "raw")\n', True),
    ("D_needle_nonconst", IMP + DECL
     + 's = "anchor"\nok = paper_needles.needle(PAPER_NEEDLES, s, "plain")\n',
     True),
    ("D_verify_kw", IMP + DECL
     + 'ok, _ = paper_needles.verify(PAPER_NEEDLES, g="g1", seq=False)\n',
     True),
    ("D_verify_extra_pos", IMP + DECL
     + 'ok, _ = paper_needles.verify(PAPER_NEEDLES, "g1")\n', True),
    ("D_declared_kw", IMP + DECL
     + "x = paper_needles.declared(PAPER_NEEDLES, deep=False)\n", True),
    # (E) declaration required
    ("E_no_decl", IMP + 'ok, _ = paper_needles.verify([{"s": "x", "form": "raw"}])\n',
     True),
]


def main():
    bad = 0
    with tempfile.TemporaryDirectory(prefix="precheck_probes_") as td:
        for name, body, expect in CASES:
            path = os.path.join(td, name + ".py")
            with open(path, "w", encoding="utf-8") as f:
                f.write(body)
            out, _ = _pf(path)
            flagged = bool(out)
            status = "ok" if flagged == expect else "UNEXPECTED"
            if status != "ok":
                bad += 1
            tail = out[0].split(": ", 1)[-1][-64:] if out else ""
            print(f"  {name:28s} flagged={flagged!s:5} expect={expect!s:5} "
                  f"{status}  {tail}", flush=True)
    n = len(CASES)
    print(f"precheck probes: {n} cases, {n - bad} as expected, "
          f"{bad} unexpected", flush=True)
    if bad:
        print("PRECHECK PROBES FAIL", flush=True)
        sys.exit(1)
    print("PRECHECK PROBES PASS", flush=True)


if __name__ == "__main__":
    main()
