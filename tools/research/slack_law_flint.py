#!/usr/bin/env python3
"""The zero side of the explicit formula at large support: lambda_1(delta)
by flint's eigensolver, with a Rayleigh-quotient ball (Theorem 1bm's
substrate; Addenda 438-442).

THE OBJECT. For a real probe g of fixed parity on [-a, a] (delta = 2a)
with ghat(r) = int g e^{irt} dt, the zero side of the explicit formula is
Q(g) = sum_gamma |ghat(gamma)|^2 over the zeros 1/2 + i gamma, and
lambda_1(delta) = min_{||g|| = 1} Q(g). THE MODEL COMPUTED: the Gram
Z_jk = 2 sum_{gamma <= gamma_N} ghat_j ghat_k over the first N listed
zeros plus the smooth density (1/2pi) log(r/2pi) beyond the last one
(log-spaced Gauss-Legendre panels to 200 gamma_N), in the orthonormal
Legendre basis of the parity, ghat_n(r) = sqrt((2n+1)/2a) a 2 i^n j_n(ar),
truncated at nmax = 2(2 a T0/pi + EXTRA) with T0 = 2 pi e^delta the
horizon. Every Gram entry is a ball (python-flint/ARB) at `prec` bits;
the eigenvalue is flint's approximate eigensolver's smallest eigenvalue
of the midpoint matrix, and the RAYLEIGH QUOTIENT of the returned vector
is evaluated in balls -- a rigorous UPPER BOUND on the truncated model's
lambda_1 (the minimum over the Legendre subspace), certified to the
ball's radius. What is not certified: the truncations (basis, list,
tail quadrature), each measured by paired cells (EXTRA 35/80/120 at
delta 2; 120/300 at delta 3.5; NZ 700/2000 at 3.5; 1000/2000 at 3.75;
TAIL 16x50 / 64x200 at delta 3).

PRECISION. The Legendre-basis Bessel evaluations lose ~n/2 nats at order
n ~ argument, so prec must exceed ~0.75 nmax bits plus the digits wanted;
the Rayleigh ball printed is the check (a radius comparable to lambda_1
means the run is under-precise -- the 512-bit delta = 3 entry of Addendum
438's first table failed this way).

Environment (CLI): EXTRA (default 35), NZ (zeros used; default the whole
list), ZERO_CHUNK (zeros per Gram block, default 1000), TAIL_PANELS /
TAIL_PTS (defaults 50 / 16), CASCADE_ZEROS (zero list; default
checkpoints/zeta_zeros_2000.json for the CLI).
Usage: slack_law_flint.py <prec> <parity> delta [delta ...]
       slack_law_flint.py cells [cell ...]      (the keyed producer)

KEYED PRODUCER (the 1bm landing): run(cell) computes the named cell on
the 6700-zero list (checkpoints/zeta_zeros_6700.json, whose sha256 is in
the key) at its executable-content key: REUSED from checkpoints/ when the
producing code and inputs match, else recomputed and saved.
"""
import sys, os, json, math, time, hashlib
from flint import arb, acb, arb_mat, acb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
ZFILE_6700 = os.path.join(HERE, "checkpoints", "zeta_zeros_6700.json")
ZFILE_CLI = os.environ.get("CASCADE_ZEROS", os.path.join(HERE, "checkpoints", "zeta_zeros_2000.json"))

def load_zeros(path):
    return [float(z) for z in json.load(open(path))]

def gl(n):
    out = [arb.legendre_p_root(n, k, weight=True) for k in range(n)]
    return [r for r, w in out], [w for r, w in out]

def gram(delta, parity, zeros, nmax_extra=35, tail_panels=50, tail_pts=16, chunk=1000):
    a = arb(delta)/2
    zs = [arb(z) for z in zeros]
    T0 = 2*arb.pi()*arb(delta).exp()
    nmax = 2*(int(float((2*a*T0/arb.pi()).mid())) + nmax_extra)
    ns = list(range(0 if parity == "even" else 1, nmax, 2)); m = len(ns)
    gmax = zs[-1]
    edges = [gmax*(arb(200)**(arb(i)/tail_panels)) for i in range(tail_panels + 1)]
    xg, wg = gl(tail_pts)
    rs = []; ws = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        for xx, ww in zip(xg, wg):
            rs.append((hi - lo)/2*xx + (hi + lo)/2); ws.append((hi - lo)/2*ww)
    dens = [(r/(2*arb.pi())).log()/(2*arb.pi()) for r in rs]
    fac = [(arb(2*n + 1)/(2*a)).sqrt()*a*2 for n in ns]
    sgn = [1 if n % 4 in (0, 1) else -1 for n in ns]
    half = arb(1)/2; pi2 = (arb.pi()/2)
    def jn(n, x):
        x = a*x
        return (pi2/x).sqrt()*x.bessel_j(arb(n) + half)
    # accumulate Z = 2 (Gz Gz^T + Gt Gt^T) in chunks of zeros: memory O(m * chunk), not O(m * nz)
    Z = arb_mat(m, m)
    for c0 in range(0, len(zs), chunk):
        blk = zs[c0:c0 + chunk]; Gz = arb_mat(m, len(blk))
        for i, n in enumerate(ns):
            for k, z in enumerate(blk):
                Gz[i, k] = sgn[i]*fac[i]*jn(n, z)
        Z += 2*(Gz*Gz.transpose())
    Gt = arb_mat(m, len(rs))
    for i, n in enumerate(ns):
        for k, r in enumerate(rs):
            Gt[i, k] = sgn[i]*fac[i]*jn(n, r)*(ws[k]*dens[k]).sqrt()
    Z += 2*(Gt*Gt.transpose())
    return Z, m

def lam1(delta, parity, prec, zeros, extra=35, tail_panels=50, tail_pts=16, chunk=1000):
    """(eigenvalue midpoint, Rayleigh ball, m, gram seconds, eig seconds) at `prec` bits."""
    with ctx.workprec(prec):      # precision by context manager, never a store (clause G)
        t0 = time.time()
        Z, m = gram(delta, parity, zeros, extra, tail_panels, tail_pts, chunk)
        t1 = time.time()
        Zc = acb_mat(Z.mid())
        E, R = Zc.eig(right=True, algorithm="approx")
        k0 = min(range(m), key=lambda i: E[i].real.mid())
        v = arb_mat(m, 1)
        for i in range(m): v[i, 0] = R[i, k0].real.mid()
        num = (v.transpose()*Z*v)[0, 0]; den = (v.transpose()*v)[0, 0]
        rq = num/den
        t2 = time.time()
        return E[k0].real.mid(), rq, m, t1 - t0, t2 - t1

# ------------------------------------------------ keyed producer (the 1bm landing)
sys.path.insert(0, HERE)
import ckpt_key

DEPS_SL = {f: ckpt_key.code_sha(os.path.join(HERE, f)) for f in sorted(
    ckpt_key.producer_closure(("slack_law_flint.py",), HERE))}
KEYFILE = os.path.join(HERE, "slack_law_flint.py")

# the cells: (delta, prec, extra); all even, all on the 6700-zero list, tail 16 x 50
CELLS = {
    "d1.0":      dict(delta=1.0,        prec=320,  extra=120),
    "d1.38":     dict(delta=1.3828125,  prec=320,  extra=120),
    "d2.0":      dict(delta=2.0,        prec=800,  extra=120),
    "d2.0_e35":  dict(delta=2.0,        prec=800,  extra=35),
    "d2.0_e80":  dict(delta=2.0,        prec=800,  extra=80),
    "d2.3":      dict(delta=2.3,        prec=800,  extra=120),
    "d2.6":      dict(delta=2.6,        prec=1400, extra=120),
    "d3.0":      dict(delta=3.0,        prec=1400, extra=120),
    "d3.5":      dict(delta=3.5,        prec=1400, extra=120),
    "d3.5_e300": dict(delta=3.5,        prec=1400, extra=300),
}

def _zeros_sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()

def run(cell):
    cfg = CELLS[cell]
    zsha = _zeros_sha(ZFILE_6700)
    params = {"deps": DEPS_SL, "cell": cell, "delta": cfg["delta"], "parity": "even",
              "prec": cfg["prec"], "extra": cfg["extra"], "zeros_sha256": zsha,
              "tail_panels": 50, "tail_pts": 16, "round": 1}
    name = f"slack_law_{cell}"
    st = ckpt_key.load(name, KEYFILE, params, kfun=ckpt_key.code_key)
    if st is not None:
        return st
    zeros = load_zeros(ZFILE_6700)
    lam, rq, m, tg, te = lam1(cfg["delta"], "even", cfg["prec"], zeros, cfg["extra"])
    with ctx.workprec(cfg["prec"]):
        st = {"cell": cell, "delta": cfg["delta"], "parity": "even", "prec": cfg["prec"],
              "extra": cfg["extra"], "nz": len(zeros), "gmax": zeros[-1], "m": m,
              "zeros_sha256": zsha, "tail_panels": 50, "tail_pts": 16,
              "eig_mid": lam.str(40, radius=False),
              "rq_mid": rq.mid().str(40, radius=False), "rq_rad": float(rq.rad().str(5, radius=False)),
              "rq_upper": rq.upper().str(40, radius=False),
              "ln_rq_upper": float(rq.upper().log()),
              "ln_eig": float(lam.log()),
              "gram_s": tg, "eig_s": te,
              "verdict": "COMPUTED (two-sided model value; the Rayleigh ball is a rigorous upper bound on the truncated model's lambda_1)"}
    ckpt_key.save(name, KEYFILE, params, st, kfun=ckpt_key.code_key)
    return st

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "cells":
        for cell in (sys.argv[2:] or list(CELLS)):
            st = run(cell)
            print(f"{cell:10s} delta {st['delta']:<9} ln lambda_1 (eig) {st['ln_eig']:10.3f}  Rayleigh upper ln {st['ln_rq_upper']:10.3f}  radius {st['rq_rad']:.2e}  m {st['m']} nz {st['nz']} gram {st['gram_s']:.0f}s eig {st['eig_s']:.0f}s", flush=True)
        sys.exit(0)
    prec = int(sys.argv[1]); parity = sys.argv[2]; extra = int(os.environ.get("EXTRA", "35"))
    zeros = load_zeros(ZFILE_CLI)
    nz = int(os.environ.get("NZ", str(len(zeros)))); zeros = zeros[:nz]
    tp = int(os.environ.get("TAIL_PANELS", "50")); tq = int(os.environ.get("TAIL_PTS", "16")); ch = int(os.environ.get("ZERO_CHUNK", "1000"))
    for d in [float(s) for s in sys.argv[3:]]:
        lam, rq, m, tg, te = lam1(d, parity, prec, zeros, extra, tp, tq, ch)
        ed = math.exp(d); ln = float(lam.log())
        print(f"{d:8.4f} {parity} lambda_1 {lam.str(8, radius=False)} (Rayleigh {rq.str(8)}) ln {ln:10.3f} ln/e^d {ln/ed:8.4f} ln/(d e^d) {ln/(d*ed):8.4f} | m {m} | zeros {nz} to {zeros[-1]:.0f} | gram {tg:.0f}s eig {te:.0f}s", flush=True)
