#!/usr/bin/env python3
"""Content-addressed compute checkpoints (owner-commissioned, A341).

key(script_path, params) = sha256(script bytes + canonical params JSON).
Checkpoint filenames embed the first 12 hex chars, so state is reused
ONLY when both the producing code and its inputs are byte-identical:
any edit -- including a sabotage probe's mangle -- changes the key and
forces recomputation. Each checkpoint stores its full provenance.

Reuse is always printed ("REUSED <key12>" / "RECOMPUTED"); setting
CASCADE_COMPUTE=fresh ignores existing state entirely.
"""
import hashlib, json, os

CKDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "checkpoints")

def key(script_path, params):
    h = hashlib.sha256()
    h.update(open(script_path, "rb").read())
    h.update(json.dumps(params, sort_keys=True).encode())
    return h.hexdigest()

def path(name, script_path, params):
    return os.path.join(CKDIR, f"{name}_{key(script_path, params)[:12]}.json")

def load(name, script_path, params):
    if os.environ.get("CASCADE_COMPUTE") == "fresh":
        print(f"  ckpt [{name}]: FRESH mode -- ignoring any existing state", flush=True)
        return None
    p = path(name, script_path, params)
    try:
        st = json.load(open(p))
        print(f"  ckpt [{name}]: REUSED {os.path.basename(p)} "
              f"(script+inputs match)", flush=True)
        return st["state"]
    except Exception:
        print(f"  ckpt [{name}]: RECOMPUTING (no matching checkpoint)", flush=True)
        return None

def save(name, script_path, params, state):
    p = path(name, script_path, params)
    json.dump({"script_sha256": key(script_path, {}),
               "key": key(script_path, params),
               "params": params, "state": state}, open(p, "w"), indent=0)
    return p
