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

def code_sha(path):
    """sha256 of the executable content: the docstring-stripped AST
    dump for .py files, raw bytes for anything else."""
    data = open(path, "rb").read()
    if not path.endswith(".py"):
        return hashlib.sha256(data).hexdigest()
    import ast
    tree = ast.parse(data)
    for node in ast.walk(tree):
        body = getattr(node, "body", None)
        if (isinstance(body, list) and body
                and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)):
            node.body = body[1:]
    return hashlib.sha256(ast.dump(tree).encode()).hexdigest()

def code_key(script_path, params):
    h = hashlib.sha256()
    h.update(code_sha(script_path).encode())
    h.update(json.dumps(params, sort_keys=True).encode())
    return h.hexdigest()

def path(name, script_path, params):
    return os.path.join(CKDIR, f"{name}_{key(script_path, params)[:12]}.json")

def load(name, script_path, params, kfun=None):
    kfun = kfun or key
    if os.environ.get("CASCADE_COMPUTE") == "fresh":
        print(f"  ckpt [{name}]: FRESH mode -- ignoring any existing state", flush=True)
        return None
    p = os.path.join(CKDIR, f"{name}_{kfun(script_path, params)[:12]}.json")
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
    p = os.path.join(CKDIR, f"{name}_{kfun(script_path, params)[:12]}.json")
    json.dump({"script_sha256": kfun(script_path, {}),
               "key": kfun(script_path, params),
               "params": params, "state": state}, open(p, "w"), indent=0)
    return p
