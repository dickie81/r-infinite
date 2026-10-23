"""Twisted energies on the Farey points (README round 564; SEVEN-THIRDS.md section 32).

Notation of farey_coherence_probe.py: q prime, L = q - 1, the generic lines m of the box, B_m(x) = (m1 x + m3)/m2,
R0 = R with R0(1) = 0, and X'(x) = sum_m (R0(B_m(x)/x) conj R0(B_m(x)) - conj R(x)).  Characters are indexed by Z/L.

The centred indicator w = 1_W - |W|/L has transform R0, and
r_w(phi) = sum_chi w(chi) w(phi chi) = |W intersect phi W| - |W|^2/L.
With c_x(psi) = sum_chi w(chi) w(conj(psi) chi) conj(chi(x)), T_psi(x) = sum_m psi(B_m(x)) (psi(0) = 0) and
Z(x) = #{m : B_m(x) = 0}, exactly

    X'(x) + e(x) = sum_{psi != 1} c_x(psi) T_psi(x),   e(x) = |box| conj R(x) - c_x(1)(|box| - Z(x)),

where c_x(1) = (1 - 2|W|/L) conj R(x), plus |W|^2/L at x = 1.  Round 563 wrote this with the indicator of W in place of
w; that form holds for the sums built from R, not R0, and only up to Z(x) conj R(x).  Cauchy-Schwarz over psi gives

    |X'(x) + e(x)|^2 <= (E_x - |c_x(1)|^2) omega(x),   E_x = sum_phi r_w(phi)^2 phi(x),

where E_x = (1/L) sum_z |R0(z)|^2 |R0(x/z)|^2, omega(x) = sum_{psi != 1} |T_psi(x)|^2 = L sum_{t != 0} nu_x(t)^2 -
(|box| - Z(x))^2 and nu_x(t) = #{m : B_m(x) = t}.
E_1 = (kappa - 1)|W|^4/L, and |E_x| <= E_1.  S(phi) = sum_x omega(x) phi(x) over the points x != 1 of height <= 30.

  (E1) At q = 10007, at six points x and for the three sets, the expansion holds to 1e-6 relative, and so does round
       563's form for the sums built from R, up to Z(x) conj R(x); for the kappa <= 1.25 set, round 563's form misses
       X'(x) by more than a tenth of |X'(x)| at x = 1 and 2.
  (E2) E_x against its definition at x = 2 and 3, and E_1 = (kappa - 1)|W|^4/L, to 1e-8 relative.
  (E3) The Cauchy-Schwarz inequality at every point of height <= 30, for the three sets at q = 10007 and 100003.
  (E4) The collision count: sum_t nu_x(t)^2 <= 128 M^4 (1 + log M)/h at every point of height h <= 2M.
  (E5) sum_x E_x omega(x) = sum_phi r_w(phi)^2 S_1(phi) over the points of height <= 30, with S_1 = S + omega(1).
  (E6) For the G1 and kappa <= 1.25 sets, the 1% of characters with the largest |S(phi)| carry more than three
       quarters of sum_{phi != 1} r_w(phi)^2 S(phi) and less than 15% of sum_{phi != 1} r_w(phi)^2; for the random
       sets that sum is below 1% of r_w(1)^2 S(1).
  (E7) For the kappa <= 1.25 sets, the points of height <= q^{1/8} carry less than a quarter of ||X'||^2 and those of
       height <= 4M more than four fifths; the first share falls from q = 10007 to 100003.
  Printed, not gated: the ratio of sum |X'|^2 to the summed bound over the points of height <= 30, which is what
  Cauchy-Schwarz loses there, and the shares of (E7) for the random sets.
Mutations, each of which must fail a gate: (m1) round 563's form in place of the expansion in (E1); (m2) E_1 with kappa
in place of kappa - 1; (m3) the bound of (E3) with E_x replaced by its phi = 1 term; (m4) the random set in place of
the kappa <= 1.25 set in (E6).

Scope.  These are measurements, at two values of q, of sets that two search methods find.  The identities and the
inequality hold for every W.  The bound they give on the points of height <= q^{1/8} is proved in SEVEN-THIRDS.md
section 32 and its exponents are checked by idea_register.py (R29), not here.
"""
import sys

import numpy as np

from energy_frontier import frontier
from farey_coherence_probe import heights, r_of
from gram_probe import QS, Gram
from line_sums import dlog_table
from low_energy_probe import Lines

HCUT = 30
MUTS = ("m1", "m2", "m3", "m4")


def corr(a, b):
    """corr(a, b)[s] = sum_k a(k) conj(b(k - s)) on Z/L."""
    return np.fft.ifft(np.fft.fft(a) * np.conj(np.fft.fft(b)))


def expansion(S, dl, inv, box, ind, R, R0, x):
    """Relative errors of the expansion, of round 563's form for the R-sums, and round 563's miss of X'(x)."""
    q, L, W = S.q, S.L, S.R
    nb, eps = len(box), W / L
    w = ind - eps
    B = (box[:, 0] * x + box[:, 2]) % q * inv[box[:, 1]] % q
    Z = (B == 0).sum()
    Xp = (R0[B * inv[x] % q] * np.conj(R0[B])).sum() - nb * np.conj(R[x])
    XR = (R[B * inv[x] % q] * np.conj(R[B])).sum() - nb * np.conj(R[x])
    hist = np.zeros(L)
    np.add.at(hist, dl[B[B != 0]], 1)
    T = np.fft.ifft(hist) * L
    ph = np.exp(-2j * np.pi * np.arange(L) * dl[x] / L)
    cw, c = corr(w * ph, w), corr(ind * ph, ind)
    cw1 = (1 - 2 * eps) * np.conj(R[x]) + (eps ** 2 * L if x == 1 else 0)
    e = nb * np.conj(R[x]) - cw1 * (nb - Z)
    scale = abs(Xp) + nb * W
    return (abs((cw[1:] * T[1:]).sum() - Xp - e) / scale, abs((c[1:] * T[1:]).sum() - XR - Z * np.conj(R[x])) / scale,
            abs((c[1:] * T[1:]).sum() - Xp) / scale, abs((c[1:] * T[1:]).sum() - Xp) / abs(Xp))


def measure(q):
    dl = dlog_table(q)
    S = Gram(q, dl=dl)
    lines = Lines(S, dl)
    inv = lines.inv
    box = np.array([m for m in lines.box if m[0] != 0 and m[2] != 0], dtype=np.int64)
    nb, L, W, M = len(box), S.L, S.R, S.M
    eps = W / L
    v, K = S.alternate()
    best, _ = frontier(S, steps=150)
    rng = np.random.default_rng(37)
    sets = {"G1": K, "kappa<=1.25": best[1.25][1], "random": rng.choice(np.arange(1, L), W, replace=False)}
    ht = heights(q, max(HCUT, int(4 * M) + 1))
    pts = np.nonzero(ht <= HCUT)[0]
    pts = pts[pts > 0]
    hp = ht[pts]
    Bs = (np.outer(pts, box[:, 0]) + box[:, 2]) % q * inv[box[:, 1]] % q
    Z = (Bs == 0).sum(axis=1)
    nu2 = np.array([(np.bincount(B[B != 0]).astype(np.float64) ** 2).sum() for B in Bs])
    omega = L * nu2 - (nb - Z) ** 2.0
    small = hp <= 2 * M
    coll = nu2[small] * hp[small] / (M ** 4 * (1 + np.log(M)))
    out = {"q": q, "M": M, "box": nb, "W": W, "npts": len(pts), "coll": float(coll.max()), "sets": {}}
    xs = lines.x
    hx = ht[xs]
    for name, KK in sets.items():
        ind = np.zeros(L)
        ind[KK] = 1
        r = np.rint(np.fft.ifft(np.abs(np.fft.fft(ind)) ** 2).real)
        kappa = (r ** 2).sum() / (W ** 4 / L)
        rw = r - W ** 2 / L
        Ew = (np.fft.ifft(rw ** 2) * L).real
        R = r_of(S, dl, KK)
        R0 = R.copy()
        R0[1] = 0
        F0 = np.abs(R0) ** 2
        z = np.arange(1, q)
        rec = {"kappa": kappa,
               "E_def": max(abs(Ew[dl[x0]] - (F0[z] * F0[x0 * inv[z] % q]).sum() / L) / Ew[0] for x0 in (2, 3)),
               "E1": abs(Ew[0] - (kappa - 1) * W ** 4 / L) / (W ** 4 / L),
               "E1_m2": abs(Ew[0] - kappa * W ** 4 / L) / (W ** 4 / L)}
        if q == QS[0]:
            errs = [expansion(S, dl, inv, box, ind, R, R0, x)
                    for x in (1, 2, 3 * inv[2] % q, 5, 1234, 7 * inv[5] % q)]
            rec["id"] = max(e[0] for e in errs)
            rec["id_R"] = max(e[1] for e in errs)
            rec["id_m1"] = max(e[2] for e in errs)
            rec["miss"] = min(errs[0][3], errs[1][3])
        X = (R0[Bs * inv[pts][:, None] % q] * np.conj(R0[Bs])).sum(axis=1) - nb * np.conj(R[pts])
        cw1 = (1 - 2 * eps) * np.conj(R[pts]) + np.where(pts == 1, eps ** 2 * L, 0)
        lhs = np.abs(X + nb * np.conj(R[pts]) - cw1 * (nb - Z)) ** 2
        ewx = Ew[dl[pts]]
        bound = (ewx - np.abs(cw1) ** 2) * omega
        bound_m3 = (rw[0] ** 2 - np.abs(cw1) ** 2) * omega
        tol = 1e-9 * bound.max()
        rec["cs"] = bool((lhs <= bound + tol).all())
        rec["cs_m3"] = bool((lhs <= bound_m3 + tol).all())
        rec["tight"] = (np.abs(X) ** 2).sum() / bound.sum()
        wgt = np.zeros(L)
        np.add.at(wgt, dl[pts], omega)
        S1 = (np.fft.ifft(wgt) * L).real
        tot = (ewx * omega).sum()
        rec["split"] = abs(tot - (rw ** 2 * S1).sum()) / tot
        one = int(np.nonzero(pts == 1)[0][0])
        Sx = S1 - omega[one]
        osc = (rw[1:] ** 2 * Sx[1:]).sum()
        top = np.argsort(-np.abs(Sx[1:]))[: L // 100] + 1
        rec["top_share"] = (rw[top] ** 2 * Sx[top]).sum() / osc
        rec["top_mass"] = (rw[top] ** 2).sum() / (rw[1:] ** 2).sum()
        rec["osc_rel"] = osc / (rw[0] ** 2 * Sx[0])
        if name != "G1":
            Xf = np.zeros(q - 1, complex)
            xinv = inv[xs]
            for m1, m2, m3 in box:
                B = (m1 * xs + m3) % q * inv[m2] % q
                Xf += R0[B * xinv % q] * np.conj(R0[B])
            a2 = np.abs(Xf - nb * np.conj(R[xs])) ** 2
            rec["theta"] = a2.sum() / (nb ** 2 * q * W ** 2)
            rec["share8"] = a2[hx <= q ** 0.125].sum() / a2.sum()
            rec["share4M"] = a2[hx <= 4 * M].sum() / a2.sum()
        out["sets"][name] = rec
    return out


def gate(ms, mut=None):
    ok = True
    for m in ms:
        ok &= m["coll"] <= 128
        for name, s in m["sets"].items():
            ok &= s["E_def"] <= 1e-8 and s["split"] <= 1e-9
            ok &= (s["E1_m2"] if mut == "m2" else s["E1"]) <= 1e-8
            ok &= s["cs_m3"] if mut == "m3" else s["cs"]
            if "id" in s:
                ok &= (s["id_m1"] if mut == "m1" else s["id"]) <= 1e-6 and s["id_R"] <= 1e-6
            if name == "random":
                ok &= abs(s["osc_rel"]) < 0.01
            else:
                src = m["sets"]["random"] if (mut == "m4" and name == "kappa<=1.25") else s
                ok &= src["top_share"] > 0.75 and src["top_mass"] < 0.15
        lo = m["sets"]["kappa<=1.25"]
        ok &= lo["share8"] < 0.25 and lo["share4M"] > 0.8
        if "miss" in lo:
            ok &= lo["miss"] > 0.1
    ok &= len(ms) == 2 and ms[1]["sets"]["kappa<=1.25"]["share8"] < ms[0]["sets"]["kappa<=1.25"]["share8"]
    return bool(ok)


def main():
    ms = []
    for q in QS[:2]:
        m = measure(q)
        ms.append(m)
        print(f"q={q} M={m['M']:.2f} |W|={m['W']} generic lines={m['box']} points of height <= {HCUT}: {m['npts']}; "
              f"max over h <= 2M of h sum nu^2/(M^4 (1 + log M)) = {m['coll']:.2f} (bound 128)", flush=True)
        for name, s in m["sets"].items():
            line = (f"  {name:12s} kappa = {s['kappa']:.4f}; E_x and E_1 identities {s['E_def']:.1e}, {s['E1']:.1e}; "
                    f"Cauchy-Schwarz {'holds' if s['cs'] else 'FAILS'} (sum |X'|^2/bound = {s['tight']:.4f}); "
                    f"top 1% of |S|: {s['top_share']:+.3f} of the phi != 1 sum, {s['top_mass']:.4f} of the r_w^2 mass; "
                    f"phi != 1 sum / phi = 1 term = {s['osc_rel']:+.4f}")
            if "id" in s:
                line += (f"; expansion {s['id']:.1e}, round 563's form for the R-sums {s['id_R']:.1e}, "
                         f"round 563's form against X' {s['id_m1']:.1e}")
            if "theta" in s:
                line += (f"; theta' = {s['theta']:.5f}, share at height <= q^(1/8): {s['share8']:.3f}, "
                         f"<= 4M: {s['share4M']:.3f}")
            print(line, flush=True)
    ok = gate(ms)
    caught = {mu: not gate(ms, mu) for mu in MUTS}
    print(f"gates {'pass' if ok else 'FAIL'}; mutations: "
          + ", ".join(f"{k} {'caught' if v else 'NOT CAUGHT'}" for k, v in caught.items()))
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
