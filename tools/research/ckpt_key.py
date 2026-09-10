#!/usr/bin/env python3
"""Content-addressed compute checkpoints (owner-commissioned, A341).

key(script_path, params) = sha256(script bytes + canonical params JSON).
Checkpoint filenames embed the first 12 hex chars, so state is reused
ONLY when both the producing code and its inputs are byte-identical:
any edit -- including a sabotage probe's mangle -- changes the key and
forces recomputation. Each checkpoint stores its full provenance.

Reuse is always printed ("REUSED <key12>" / "RECOMPUTED"); setting
CASCADE_COMPUTE=fresh ignores existing state entirely.

Executable-content keying (owner's decision, round 245): code_sha /
code_key hash the docstring-stripped AST of a .py file (comments and
formatting never reach the AST), so prose-only edits no longer rotate
keys and force recomputes, while ANY executable edit -- including a
probe's mangle, since string literals inside executable statements
are AST constants -- still self-invalidates. The original byte-exact
key() remains for callers that want it (the tower members keep it).
"""
import hashlib, json, os

CKDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "checkpoints")

def key(script_path, params):
    h = hashlib.sha256()
    h.update(open(script_path, "rb").read())
    h.update(json.dumps(params, sort_keys=True).encode())
    return h.hexdigest()

# Pure-print stripping (owner's decision, round 282: "abort and fix
# the process" -- a safe-direction edit to five instruments' print
# lines had rotated every interval key and owed a two-hour
# recompute). A bare statement `print(...)` is dropped from the
# executable-content hash when its whole argument subtree contains
# no construct that can write state through a name it does not own:
# no assignment expression, await, yield, lambda, starred argument, or
# `file=` keyword; no keyword argument on an inner call; and every
# call inside it is to a name or attribute on the read-only
# formatting whitelist below. This is a syntactic rule, not a
# semantic proof (round 282 F282-2): a stripped print may still
# CONSUME an iterator bound to a name (`print(list(it))`) or read the
# clock; the standing census of the keyed closures finds no such
# site, and a print over an iterator is not a certified-state edit
# unless the computation later consumes the same iterator.
# Anything else -- a print whose argument calls a function outside
# the whitelist, a print that writes to a file, a print hidden in a
# larger statement -- stays in the hash exactly as before, so a
# probe's mangle cannot ride inside a print. The legacy hash
# (docstring-stripped only) remains available as
# code_sha(path, strip_prints=False); run_tower's member reach key
# keeps it, so a print edit in a member's reach still re-verifies the
# member live (cheap) while the producers' compute state survives.
PRINT_CALL_NAMES = frozenset((
    "print", "_fdir", "float", "int", "str", "repr", "len", "abs",
    "max", "min", "round", "format", "sum", "sorted", "bool", "list",
    "tuple", "dict", "hex", "type", "range", "enumerate", "zip"))
PRINT_CALL_ATTRS = frozenset((
    "upper", "lower", "mid", "rad", "str", "get", "keys", "values",
    "items", "format", "join", "strip", "rstrip", "lstrip", "hexdigest",
    "basename", "isoformat", "strftime", "time", "count", "index",
    "replace", "ljust", "rjust", "hex", "startswith", "endswith",
    "split", "real", "imag", "tolist", "sum", "max", "min", "mean"))
PRINT_KEYWORDS = frozenset(("flush", "sep", "end"))

def _is_pure_print(stmt):
    import ast
    if not (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)):
        return False
    call = stmt.value
    if not (isinstance(call.func, ast.Name) and call.func.id == "print"):
        return False
    for kw in call.keywords:
        if kw.arg is None or kw.arg not in PRINT_KEYWORDS:
            return False
    for node in ast.walk(call):
        if isinstance(node, (ast.NamedExpr, ast.Await, ast.Yield,
                             ast.YieldFrom, ast.Lambda, ast.Starred)):
            return False
        if isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Name):
                if f.id not in PRINT_CALL_NAMES:
                    return False
            elif isinstance(f, ast.Attribute):
                if f.attr not in PRINT_CALL_ATTRS:
                    return False
            else:
                return False
            # no keyword arguments on any inner call: a whitelisted
            # higher-order builtin (max/min/sorted/sum) could otherwise
            # smuggle a callable through key=/default= without a Call node
            if node is not call and node.keywords:
                return False
    return True

def _stripped_tree(data, strip_prints):
    import ast
    tree = ast.parse(data)
    for node in ast.walk(tree):
        body = getattr(node, "body", None)
        if (isinstance(body, list) and body
                and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)):
            body = node.body = body[1:]
        if strip_prints:
            for attr in ("body", "orelse", "finalbody"):
                lst = getattr(node, attr, None)
                if isinstance(lst, list) and lst and isinstance(lst[0], ast.stmt):
                    setattr(node, attr, [s for s in lst if not _is_pure_print(s)])
    return tree

def code_sha_src(data, path=".py", strip_prints=True):
    """The executable-content hash of source bytes (see code_sha)."""
    if not path.endswith(".py"):
        return hashlib.sha256(data).hexdigest()
    import ast
    return hashlib.sha256(ast.dump(_stripped_tree(data, strip_prints)).encode()).hexdigest()

def code_sha(path, strip_prints=True):
    """sha256 of the executable content: the docstring-stripped,
    pure-print-stripped AST dump for .py files (strip_prints=False:
    docstrings only -- the round-245 hash), raw bytes for anything else."""
    return code_sha_src(open(path, "rb").read(), path, strip_prints)

def code_key(script_path, params):
    h = hashlib.sha256()
    h.update(code_sha(script_path).encode())
    h.update(json.dumps(params, sort_keys=True).encode())
    return h.hexdigest()

def path(name, script_path, params):
    return os.path.join(CKDIR, f"{name}_{key(script_path, params)[:12]}.json")

# round-260 F260-2: the key is captured ONCE, at load time, and
# reused by the matching save -- save() previously recomputed the
# key from the on-disk file AT SAVE TIME, so an instrument edited
# while its own run was in flight saved state under a key pairing
# the NEW code's hash with the OLD run's params: a checkpoint
# whose stored provenance no honest run can produce (two such
# misattributed states were found and removed at the sweep; the
# reviewer proved no unsound-REUSE path exists -- the keyfile's
# own sha inside params["deps"] makes a contaminated key
# uncollidable with any self-consistent one -- so the defect was
# provenance-only). The memo is per (name, params); a save with
# no prior load still computes its own key.
_KEY_MEMO = {}

def _memo_id(name, params):
    return name + "|" + json.dumps(params, sort_keys=True)

def _script_sha(script_path, kfun):
    # round-261 F261-5: the stored "script_sha256" field was
    # kfun(path, {}) -- a key, not a sha. It is now the honest
    # per-kfun script hash (nothing consumes the field; the
    # historical files keep their old values as history).
    if kfun is code_key:
        return code_sha(script_path)
    return hashlib.sha256(open(script_path, "rb").read()).hexdigest()

def load(name, script_path, params, kfun=None):
    kfun = kfun or key
    k = kfun(script_path, params)
    _KEY_MEMO[_memo_id(name, params)] = (k, _script_sha(script_path, kfun))
    if os.environ.get("CASCADE_COMPUTE") == "fresh":
        print(f"  ckpt [{name}]: FRESH mode -- ignoring any existing state", flush=True)
        return None
    p = os.path.join(CKDIR, f"{name}_{k[:12]}.json")
    try:
        st = json.load(open(p))
        print(f"  ckpt [{name}]: REUSED {os.path.basename(p)} "
              f"(script+inputs match)", flush=True)
        return st["state"]
    except Exception:
        print(f"  ckpt [{name}]: RECOMPUTING (no matching checkpoint)", flush=True)
        return None

def save(name, script_path, params, state, kfun=None):
    kfun = kfun or key
    memo = _KEY_MEMO.get(_memo_id(name, params))
    if memo is None:
        memo = (kfun(script_path, params),
                _script_sha(script_path, kfun))
    k, ssha = memo
    p = os.path.join(CKDIR, f"{name}_{k[:12]}.json")
    json.dump({"script_sha256": ssha,
               "key": k,
               "params": params, "state": state}, open(p, "w"), indent=0)
    return p


def local_imports(fn, here):
    """Local-module imports of fn (files existing in `here`),
    from the AST -- conditional and function-local imports
    included. Hoisted from the temple instrument round 252 so
    every oneprime DEPS dict can compute its closure."""
    import ast as _ast
    out = set()
    tree = _ast.parse(open(os.path.join(here, fn)).read())
    for node in _ast.walk(tree):
        if isinstance(node, _ast.ImportFrom) and node.module:
            if os.path.exists(os.path.join(here,
                                           node.module + ".py")):
                out.add(node.module + ".py")
        elif isinstance(node, _ast.Import):
            for a in node.names:
                if os.path.exists(os.path.join(here,
                                               a.name + ".py")):
                    out.add(a.name + ".py")
    return out


def producer_closure(roots, here):
    """COMPUTED transitive import closure of the root producer
    files (round-250 F250-1 for the temple; extended to the
    sibling instruments round 252, reviewer-3 F4). ckpt_key.py
    itself is excluded by the arc's convention: no instrument
    keys the keying machinery."""
    closure = set(roots)
    frontier = set(roots)
    while frontier:
        nxt = set()
        for f in frontier:
            nxt |= local_imports(f, here) - closure
        closure |= nxt
        frontier = nxt
    closure.discard("ckpt_key.py")
    return closure
