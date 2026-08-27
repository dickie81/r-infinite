#!/usr/bin/env python3
"""Shared cache for verified zeta-zero ordinates (round 252,
owner-commissioned pace retrofit): several tower members pull the
same zeros from mpmath.zetazero on every run; the member that
motivated this cache ran ~105 min in-tower under BLAS
contention (round-253 F253-4: the pull-phase share of that was
never separately measured -- the standalone pulls measure
~0.1 s/zero; the cache removes the repeated work either way). The ordinates are mathematical constants, so the
cache is keyed by (dps, count) only; TRUST IS NOT STORED: on
every cache hit the first and last ordinates are recomputed LIVE
at the same dps and must match the cached values exactly
(mpmath is deterministic and json round-trips float64 exactly,
so equality is exact; any mismatch -- corruption, a different
mpmath -- falls through to a full recompute and rewrite). COVERAGE,
stated honestly (round 253, F253-2): the anchors and the count
check catch gross corruption -- wrong length, shifted or
perturbed endpoints, a swapped dps block; a SUB-WINDOW interior
perturbation is NOT detected by the anchors, and the consumers'
own gates give only partial interior coverage (heatflow's diss
pin is a 1e-3-absolute functional of all 60 ordinates and its
gap pins hold 5e-5; fluctuation's g1 pins duplicate the anchors;
prolate's identity windows tolerate small interior shifts) --
adequate for these members' float-grade windows, and no more is
claimed.
Committed under checkpoints/ like every compute checkpoint."""
import json, os

from mpmath import mp, zetazero

HERE = os.path.dirname(os.path.abspath(__file__))
CPATH = os.path.join(HERE, "checkpoints", "zeta_zeros_cache.json")


def zeros_im(count, dps):
    """The imaginary parts of zeta zeros 1..count at mp.dps=dps,
    as a list of float64 (the same float(zetazero(k).imag) pull
    the members previously made inline)."""
    key = f"dps{dps}_{count}"
    cache = {}
    if os.path.exists(CPATH):
        try:
            cache = json.load(open(CPATH, encoding="utf-8"))
        except Exception:
            cache = {}
    mp.dps = dps
    z = cache.get(key)
    if isinstance(z, list) and len(z) == count:
        if (z[0] == float(zetazero(1).imag)
                and z[-1] == float(zetazero(count).imag)):
            print(f"  zeros cache: {key} hit, live anchors "
                  f"verified", flush=True)
            return list(z)
        print(f"  zeros cache: {key} ANCHOR MISMATCH -- "
              f"recomputing", flush=True)
    print(f"  zeros cache: {key} computing live...", flush=True)
    z = [float(zetazero(k).imag) for k in range(1, count + 1)]
    cache[key] = z
    os.makedirs(os.path.dirname(CPATH), exist_ok=True)
    json.dump(cache, open(CPATH, "w", encoding="utf-8"))
    return list(z)
