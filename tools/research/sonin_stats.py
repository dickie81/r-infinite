#!/usr/bin/env python3
"""1bd harvest battery: compare an outside-instrument spectrum to the
banked quadruple. Per parity (the lam = sqrt2 identity makes EACH
parity's counting match the zeros' counting):
  (1) count of s <= 240 (banked 103; zeros below 240: 102),
  (2) c0 from fitting count(E) = (E/pi)(log(E/2pi) - 1 + c0) + 2 lam^2
      to the harvested s = 2E ladder (banked: 0.6772 vs log2 at sqrt2),
  (3) sequential displacement |s_n - g_n| in mean-spacing units
      (banked Delta = 0.510) and rms after affine calibration
      (banked 0.32),
  (4) unfolded increment fluctuation: sd of (N(s_{n+1}) - N(s_n) - 1)
      (banked 0.012 for W_sa vs 0.350 for zeros) and the correlation
      of s-increments with zero-increments (banked +0.0032).
Usage: sonin_stats.py <even.json> <odd.json>
"""
import numpy as np, math, json, sys, os
CKDIR = "/home/user/r-infinite/tools/research/checkpoints"
LOG2 = math.log(2)


def zeros_to(T=260.0):
    ck = os.path.join(CKDIR, "zeros260.json")
    if os.path.exists(ck):
        return np.array(json.load(open(ck)))
    from mpmath import mp, zetazero
    mp.dps = 13
    zs = []
    k = 1
    while True:
        z = float(zetazero(k).imag)
        if z > T:
            break
        zs.append(z)
        k += 1
    json.dump(zs, open(ck, "w"))
    return np.array(zs)


def Nsmooth(s, lam):
    E = s/2.0
    return E/math.pi*(np.log(E/(2*math.pi)) - 1 + LOG2) + 2*lam*lam


def analyze(tag, s, g, lam):
    s = np.asarray(s)
    s = s[(s > 5) & (s <= 240)]
    print(f"\n== {tag}: count s<=240 = {len(s)} (banked 103; zeros {len(g)})")
    E = s/2.0
    # c0 fit: n_index = (E/pi)(log(E/2pi) - 1) + (E/pi) c0 + 2 lam^2
    n = np.arange(1, len(s) + 1) - 0.5
    base = E/math.pi*(np.log(E/(2*math.pi)) - 1) + 2*lam*lam
    c0 = np.sum((n - base)*E/math.pi)/np.sum((E/math.pi)**2)
    resid = n - base - E/math.pi*c0
    print(f"   c0 fit = {c0:.4f} vs log2 = {LOG2:.4f} "
          f"(banked 0.6772); fit rms {np.sqrt(np.mean(resid**2)):.3f}")
    m = min(len(s), len(g))
    sp = np.mean(np.diff(g[:m]))
    d = (s[:m] - g[:m])/sp
    print(f"   sequential |s_n - g_n|: mean {np.mean(np.abs(d)):.3f} "
          f"spacings (banked Delta = 0.510)")
    a, b = np.polyfit(g[:m], s[:m], 1)
    cal = s[:m] - (a*g[:m] + b)
    print(f"   affine cal (a={a:.4f}, b={b:+.2f}): rms {np.sqrt(np.mean(cal**2)):.3f}"
          f" (banked 0.32)")
    u = Nsmooth(s, lam)
    inc = np.diff(u) - 1
    gN = g/(2*math.pi)*np.log(g/(2*math.pi)) - g/(2*math.pi) + 7.0/8
    gi = np.diff(gN) - 1
    print(f"   increment sd: instrument {np.std(inc):.3f} (banked 0.012) "
          f"vs zeros {np.std(gi):.3f} (banked 0.350)")
    k = min(len(inc), len(gi))
    if k > 3:
        c = np.corrcoef(inc[:k], gi[:k])[0, 1]
        print(f"   corr(instrument inc, zero inc) = {c:+.4f} (banked +0.0032)")


if __name__ == "__main__":
    ev = json.load(open(sys.argv[1]))
    od = json.load(open(sys.argv[2]))
    de = int(sys.argv[3]) if len(sys.argv) > 3 else 0   # leading suspects to drop
    do = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    lam = ev["lam"]
    g = zeros_to(260.0)
    g = g[g <= 240]
    analyze(f"even (K={ev['K']}, X={ev['X']:g}, drop {de})", ev["s"][de:], g, lam)
    analyze(f"odd  (K={od['K']}, X={od['X']:g}, drop {do})", od["s"][do:], g, lam)
