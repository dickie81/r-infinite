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
    # (G) stores on imported modules (round 278, F277-1 H1/H2 and the
    #     child-process spawn's dependencies)
    ("G_mp_dps_ok", IMP + DECL + GATE
     + "import mpmath\nfrom mpmath import mp, iv\nmp.dps = 50\nmp.prec = 100\n"
       "iv.prec = 53\n", False),
    ("G_re_sub_hook", "import re\nre.sub = lambda *a, **k: ''\n" + IMP + DECL
     + GATE, True),
    ("G_builtins_open_hook", "import builtins\nbuiltins.open = print\n" + IMP
     + DECL + GATE, True),          # also clause H (import builtins)
    ("G_sys_executable", "import sys\nsys.executable = './fake'\n" + IMP + DECL
     + GATE, True),
    ("G_subprocess_run", "import subprocess\nsubprocess.run = None\n" + IMP
     + DECL + GATE, True),
    ("G_os_environ_store", "import os\nos.environ['PYTHONPATH'] = '.'\n" + IMP
     + DECL + GATE, True),
    ("G_del_attr", "import re\ndel re.sub\n" + IMP + DECL + GATE, True),
    ("G_module_alias", "import re\nM = re\nM.sub = None\n" + IMP + DECL + GATE,
     True),
    ("G_setattr_call", "import re\nsetattr(re, 'sub', None)\n" + IMP + DECL
     + GATE, True),                 # clause H (setattr)
    # (H) interpreter hooks and namespace enumeration (round 278)
    ("H_settrace", "import sys\nsys.settrace(lambda *a: None)\n" + IMP + DECL
     + GATE, True),
    ("H_setprofile", "import sys\nsys.setprofile(lambda *a: None)\n" + IMP
     + DECL + GATE, True),
    ("H_audithook", "import sys\nsys.addaudithook(lambda *a: None)\n" + IMP
     + DECL + GATE, True),
    ("H_sys_modules_enum", "import sys\n" + IMP + DECL + GATE
     + "m = [v for v in sys.modules.values() if hasattr(v, 'PAPER_PATH')]\n",
     True),
    ("H_globals_enum", IMP + DECL + GATE
     + "m = [v for v in globals().values() if hasattr(v, 'PAPER_PATH')]\n",
     True),
    ("H_gc_enum", "import gc\n" + IMP + DECL + GATE
     + "o = [x for x in gc.get_objects() if isinstance(x, dict)]\n", True),
    ("H_inspect", "import inspect\n" + IMP + DECL + GATE, True),
    ("H_ctypes", "import ctypes\n" + IMP + DECL + GATE, True),
    ("H_importlib", "import importlib\n" + IMP + DECL + GATE, True),
    ("H_exec", IMP + DECL + GATE + "exec('x = 1')\n", True),
    ("H_dunder_import_ok", IMP + DECL + GATE
     + "k = __import__('ckpt_key')\n", False),   # committed spelling
    ("H_sys_executable_load_ok", "import sys, subprocess\n" + IMP + DECL + GATE
     + "r = subprocess.run([sys.executable, '--version'])\n", False),
    # (G) binding forms that hand over the module OBJECT (round 279, F278-1)
    ("G_param_store", "import subprocess\ndef _f(m):\n    m.run = None\n"
     "_f(subprocess)\n" + IMP + DECL + GATE, True),
    ("G_tuple_store", "import sys\n(sys,)[0].executable = '/tmp/fake'\n" + IMP
     + DECL + GATE, True),
    ("G_loop_store", "import re\nfor m in [re]:\n    m.sub = None\n" + IMP + DECL
     + GATE, True),
    ("G_walrus_alias", "import sys\nif (m := sys):\n    m.executable = 'x'\n"
     + IMP + DECL + GATE, True),
    ("G_unpack_alias", "import sys, re\na, b = sys, re\na.executable = 'x'\n"
     + IMP + DECL + GATE, True),
    ("G_or_alias", "import sys\nm = None or sys\nm.executable = 'x'\n" + IMP
     + DECL + GATE, True),
    ("G_next_iter", "import sys\nnext(iter([sys])).executable = 'x'\n" + IMP
     + DECL + GATE, True),
    ("G_dash_c", "import sys, subprocess\n" + IMP + DECL + GATE
     + "subprocess.run([sys.executable, '-c', 'pass'])\n", True),
    ("G_dps_nonmp_root", "import sys\nsys.dps = 1\n" + IMP + DECL + GATE, True),
    ("G_module_attr_call_ok", "import subprocess, sys\n" + IMP + DECL + GATE
     + "subprocess.run([sys.executable, '--version'])\n"
       "x = sys.argv[0]\n", False),
    # (I) introspection dunders as string constants (round 278, F277-3)
    ("I_getattr_globals", IMP + DECL + GATE
     + "g = getattr(print, '__globals__', None)\n", True),
    ("I_main_ok", IMP + DECL + GATE + "if __name__ == '__main__':\n    pass\n",
     False),
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
