#!/usr/bin/env python3
"""Provenance-verified checkpoint migration to the print-insensitive
executable-content hash (owner's decision, round 282: "abort and fix
the process").

WHY. ckpt_key.code_sha now drops pure `print(...)` statements from the
executable-content hash, so a print edit no longer rotates a
producer's key. Every checkpoint on disk was filed under the OLD hash
(docstring-stripped only). Rather than recompute hours of certified
state whose producing code differs from today's only in print lines,
this tool re-files each checkpoint under its new key -- but ONLY when
the chain of custody is proved from the checkpoint's own stored
provenance:

  1. RESOLVE. Every entry of params["deps"] ({file: hash}) and the
     stored script_sha256 must resolve, under the OLD hash, to a
     concrete historical version of that file in this repository's
     git history (committed blobs only; F282-3). A hash that resolves to no
     version is unverifiable and the checkpoint is left alone.
  2. RECOMPUTE THE OLD KEY. With the producer identified (the dep
     whose old hash equals script_sha256), the stored key must equal
     the old keying function applied to that historical producer and
     the stored params (code_key: sha256(old_sha + params);
     byte key: sha256(bytes + params)). A mismatch: left alone.
  3. EQUIVALENCE. For every dep file, the NEW hash of the resolved
     historical version must equal the NEW hash of the file as it is
     on disk now -- i.e. the code that produced the state and the
     code that will consume it differ at most in docstrings, comments,
     formatting, and pure print statements. Any other difference:
     left alone (an honest recompute is owed).
  4. RE-FILE. The state is written unchanged under the new key with
     params["deps"] rehashed, script_sha256 rehashed, and a
     "migrated" record (source file, old key, resolved blobs, the
     rule), so a reviewer can re-run every check from the record.

Usage: ckpt_migrate.py [--apply]     (default: dry run, census only)
Files it never touches: checkpoints without {script_sha256, key,
params.deps}; byte-keyed checkpoints whose deps were byte hashes
(their keys do not change); anything failing 1-3.
"""
import hashlib, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key

CKDIR = ckpt_key.CKDIR
REPO = subprocess.check_output(["git", "-C", HERE, "rev-parse", "--show-toplevel"],
                               text=True).strip()
RELDIR = os.path.relpath(HERE, REPO)

_versions = {}      # file -> {old_sha: (blob, src)}, plus byte shas


def _history(fn):
    """All distinct COMMITTED historical blobs of tools/research/fn (git
    rev-list --full-history over HEAD: every commit that touched the path
    on any ancestry line, no simplification); never the working tree
    (round 282 F282-3; docstring aligned round 283 F283-2; --full-history
    round 284 F284-6)."""
    if fn in _versions:
        return _versions[fn]
    rel = os.path.join(RELDIR, fn)
    # --full-history (round 284 F284-6): no history simplification, so a
    # version that lived only on a side branch of a TREESAME merge resolves
    commits = subprocess.check_output(
        ["git", "-C", REPO, "rev-list", "--full-history", "HEAD", "--", rel], text=True).split()
    blobs = {}
    for c in commits:
        try:
            b = subprocess.check_output(["git", "-C", REPO, "rev-parse", f"{c}:{rel}"],
                                        text=True, stderr=subprocess.DEVNULL).strip()
        except subprocess.CalledProcessError:
            continue
        if b and b not in blobs:
            blobs[b] = subprocess.check_output(["git", "-C", REPO, "cat-file", "-p", b])
    table = {}
    for b, src in blobs.items():
        table[ckpt_key.code_sha_src(src, fn, strip_prints=False)] = ("old", b, src)
        table[hashlib.sha256(src).hexdigest()] = ("bytes", b, src)
    # (round 282 F282-3: no working-tree fallback -- a state whose producing
    # code is not in git could not be re-verified later; commit first)
    _versions[fn] = table
    return table


_uses = {}
def _uses_ckpt_key(fn):
    if fn not in _uses:
        try:
            _uses[fn] = b"ckpt_key" in open(os.path.join(HERE, fn), "rb").read()
        except OSError:
            _uses[fn] = False
    return _uses[fn]


def _name_of(basename):
    m = re.match(r"^(.*)_([0-9a-f]{12})\.json$", basename)
    return m.group(1) if m else None


def plan(basename):
    """Returns (status, detail, newfile_or_None, record_or_None)."""
    p = os.path.join(CKDIR, basename)
    try:
        d = json.load(open(p))
    except Exception as e:
        return ("skip", f"unreadable ({e})", None, None)
    if isinstance(d, dict) and "migrated" in d:
        return ("skip", "already a migrated file (its provenance is its migrated record)", None, None)
    if not (isinstance(d, dict) and {"script_sha256", "key", "params", "state"} <= set(d)
            and isinstance(d["params"], dict) and isinstance(d["params"].get("deps"), dict)):
        return ("skip", "no keyed provenance", None, None)
    name = _name_of(basename)
    if name is None or d["key"][:12] != basename[-17:-5]:
        return ("skip", "filename/key mismatch", None, None)
    params = d["params"]; deps = params["deps"]
    # 1. resolve every dep
    resolved = {}
    for fn, h in deps.items():
        if not fn.endswith(".py") or "/" in fn:
            return ("skip", f"non-local dep {fn}", None, None)
        tab = _history(fn)
        if h not in tab:
            return ("unverifiable", f"dep {fn} hash {h[:12]} matches no historical version", None, None)
        resolved[fn] = tab[h]
    kinds = {v[0] for v in resolved.values()}
    if kinds == {"bytes"}:
        return ("unchanged", "byte-hashed deps (key does not depend on code_sha)", None, None)
    if kinds != {"old"}:
        return ("unverifiable", f"mixed dep hash kinds {kinds}", None, None)
    # producer = the dep whose old hash is the stored script_sha256; some
    # instruments list only their imports in DEPS (not themselves), so fall
    # back to a search of every local keyed instrument's history for that hash
    # Checkpoints written before round 261 (F261-5) stored code_key(path, {})
    # -- sha256(old_sha + "{}") -- in script_sha256 instead of the sha; both
    # spellings are accepted, and the stored KEY is always recomputed from the
    # resolved producer's own old hash (step 2), never from this field.
    def _matches(old_sha):
        return (old_sha == d["script_sha256"]
                or hashlib.sha256(old_sha.encode() + b"{}").hexdigest() == d["script_sha256"])
    prods = [fn for fn, h in deps.items() if _matches(h)]
    if not prods:
        for fn in sorted(os.listdir(HERE)):
            if fn.endswith(".py") and fn not in deps and _uses_ckpt_key(fn):
                tab = _history(fn)
                hits = [h for h, v in tab.items() if v[0] == "old" and _matches(h)]
                if hits:
                    prods.append(fn)
                    resolved[fn] = tab[hits[0]]
                    resolved_prod_sha = hits[0]
    if len(prods) != 1:
        return ("unverifiable", f"producer not identified ({len(prods)} candidates)", None, None)
    prod = prods[0]
    kind, blob, src = resolved[prod]
    prod_old_sha = deps[prod] if prod in deps else resolved_prod_sha
    # 2. recompute the old key from the resolved producer's old hash
    pj = json.dumps(params, sort_keys=True).encode()
    k_code = hashlib.sha256(prod_old_sha.encode() + pj).hexdigest()
    if k_code != d["key"]:
        return ("unverifiable", "stored key != code_key(old producer sha, params)", None, None)
    # 3. equivalence under the NEW hash for every dep
    newdeps = {}
    for fn, (kind, blob, hist_src) in resolved.items():
        cur = os.path.join(HERE, fn)
        if not os.path.exists(cur):
            return ("blocked", f"dep {fn} absent from the working tree", None, None)
        h_hist = ckpt_key.code_sha_src(hist_src, fn, strip_prints=True)
        h_cur = ckpt_key.code_sha(cur, strip_prints=True)
        if h_hist != h_cur:
            return ("blocked", f"dep {fn}: historical and current code differ beyond prints/prose", None, None)
        if fn in deps:                      # params keep exactly the producer's own dep set
            newdeps[fn] = h_cur
    newparams = dict(params); newparams["deps"] = newdeps
    new_ssha = ckpt_key.code_sha(os.path.join(HERE, prod), strip_prints=True)
    newkey = hashlib.sha256(new_ssha.encode() + json.dumps(newparams, sort_keys=True).encode()).hexdigest()
    if newkey == d["key"]:
        return ("unchanged", "new key equals old key", None, None)
    newfile = f"{name}_{newkey[:12]}.json"
    rec = {"script_sha256": new_ssha, "key": newkey, "params": newparams, "state": d["state"],
           "migrated": {"from_file": basename, "from_key": d["key"], "from_script_sha256": d["script_sha256"],
                        "resolved_blobs": {fn: v[1] for fn, v in resolved.items()},
                        "rule": "round 282: every dep's historical version (resolved from the stored old "
                                "hash) has the same print-insensitive executable-content hash as the "
                                "working-tree file; the old key recomputes from the stored provenance"}}
    return ("migrate", f"{prod} -> {newfile}", newfile, rec)


def main(apply):
    census = {}
    for bn in sorted(os.listdir(CKDIR)):
        if not bn.endswith(".json"):
            continue
        status, detail, newfile, rec = plan(bn)
        census.setdefault(status, []).append((bn, detail))
        if status == "migrate":
            target = os.path.join(CKDIR, newfile)
            if os.path.exists(target):
                census.setdefault("exists", []).append((bn, newfile))
            elif apply:
                json.dump(rec, open(target, "w"), indent=0)
        if status in ("migrate", "blocked", "unverifiable", "exists"):
            print(f"  {status:12s} {bn}: {detail}", flush=True)
    print("census: " + ", ".join(f"{k} {len(v)}" for k, v in sorted(census.items())) +
          ("  [APPLIED]" if apply else "  [dry run]"), flush=True)
    return census


if __name__ == "__main__":
    main(apply="--apply" in sys.argv[1:])
