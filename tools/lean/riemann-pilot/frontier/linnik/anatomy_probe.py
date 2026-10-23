"""Anatomy of the critical eigenvalue, and progressions of characters in large-values sets (README round 554;
SEVEN-THIRDS.md section 22).

Notation as in gram_probe.py: L = q - 1, chi_k(g^j) = e(kj/L), weight w = sin^2 on [N, 2N], |W| = R = q^{2/3},
N = q^{7/9}, M = q/N, kappa = L E(W)/R^4 >= 1.  For a set W of exponents, lambda is the top eigenvalue of the Gram
matrix G_W: the restricted large-sieve constant of W on [N, 2N].  With x the top unit eigenvector,
V(n) = sum_{k in W} x_k chi_k(n) and a(n) = w(n) V(n), the transform of a is lambda x on W, so
lambda^2 = sum_b R(b) rho(b), where R(b) = sum_{k in W} chi_k(b) and rho(b) = sum_n conj(a(bn)) a(n).  The term
b = 1 is |W| ||a||^2.  The height H(b) is the least max(t, |s|) with b = s/t mod q, 1 <= t.

  (A1) Exact exponent arithmetic at sigma = 5/7 (exponents of q).
       - The large sieve, Delta <= N + q, gives |W| <= q N/V^2 = q^{2/3} at V = N^{5/7}; Chen-Gupta-Li's S_3 bound,
         read as Delta - N <~ q^{2/3}|W|^{1/2}, is q at |W| = q^{2/3}.
       - Unit columns u_k = sqrt(w) chi_k/(sum w)^{1/2}: coherence about sqrt(q)/N (Polya-Vinogradov), so
         Gershgorin gives |W| sqrt(q)/N = q^{7/18}, above the trivial M = q^{2/9}; |W| = q^{2/3} lies beyond the
         square-root bottleneck N/sqrt(q) = q^{5/18}.
       - The flat route: flat constant at most c_w M^{1/2} Theta, so Delta <= q^{1-delta} needs Theta <= q^{1/9}, and
         a progression of length l in W forces Theta^2 >= l/3 - l^2/(4L): no progression longer than q^{2/9}.
       - Progressions in large-values sets: the chirp construction reaches N/(sqrt(q) log q), exponent 5/18 > 2/9;
         the Fejer bound l <~ N^2/V^2 = q^{4/9} holds since V^2 = q^{10/9} exceeds q log^3 q; at l = q^{5/18},
         l sqrt(q) = N, so the progression's own Delta is O(N) up to logarithms.
       - The integer-relation bound |W| (kappa - 1)^{1/4} h^{1/2} at h = q^{1/2} is q^{11/12}, and q exactly at the
         largest energy, kappa = L/|W| = q^{1/3}.
       - The closed form E(A, B) = l(l^2 + 2)/12 for the two halves of a progression of even length l, by brute
         force for l <= 200.
  (A2) The integer-relation bound, numerically.  For coprime (s, t) != (1, 1) with s, t <= h = floor(q^{0.4}), the
       map (s, t) -> s/t mod q is injective (h^2 < q) and misses 1, so sum |R(s/t)|^4 <= sum_{b != 1} |R(b)|^4 =
       R^4 (kappa - 1).  The integer part I_h = sum_{(s,t)} R(s/t) c(s,t), c(s,t) = sum_j conj(a(sj)) a(tj), then
       obeys |I_h| <= R (kappa - 1)^{1/4} h^{1/2} D_h ||a||^2 (Hoelder with 4 and 4/3), where D_h is the largest
       number of divisors s <= h of an n in [N, 2N].  Gates: injectivity, the fourth-moment inequality and the bound,
       for every set of (A4) at every q.
  (A3) A progression of characters in a large-values set.  Sharp interval I = [N, 2N], theta_n = ind(n)/L,
       phi a smooth bump with support in [1/8, 7/8] equal to 1 on [3/16, 13/16], and the chirp
       b_n = phi(theta_n) e(-l theta_n^2/2), |b_n| <= 1.  Then B(j) = sum_n b_n chi_j(n) = sum_h c_j(h) T(h), with
       c_j(h) the Fourier coefficients of phi(theta) e(j theta - l theta^2/2) and T(h) = sum_{n in I} chi_h(n);
       the main term is |I| c_j(0), of size |I|/sqrt(l) for l/4 <= j <= 3l/4 (stationary phase), and
       |T(h)| <= sqrt(q) log q otherwise.  At q = 10007, 100003 and 1000003, with V = N^{5/7}:
       - at l = floor((|I|/(2V))^2), every j in [l/4, 3l/4] has |B(j)| >= V and |B(j) - |I| c_j(0)| <= |I||c_j(0)|/2,
         with c_j(0) by quadrature;
       - the largest l on a grid for which the whole window [l/4, 3l/4] is in {|B| >= V} is at least N^2/(10 V^2);
       - the window P at that l has Delta(P, I) <= 3|I| (the top eigenvalue of its sharp Gram matrix);
       - at q >= 100003, Theta^2 of P's two halves, (E(A, B) - |A|^2|B|^2/L)/(|A||B|), exceeds q^{2/9}, so (A1)'s
         flat condition with Theta = q^{1/9} already fails for this large-values set (constants and logarithms
         aside, which a finite q cannot separate).
  (A4) Anatomy of lambda for four sets at q = 10007, 100003 and 1000003: energy_frontier.py's best sets with
       kappa <= 1.25 and kappa <= 2, gram_probe.py's (G1) set, and a random set.  Gates:
       - the decomposition: |sum_b R(b) rho(b) - lambda^2| <= 1e-6 lambda^2;
       - the integer share I_h/lambda^2 is at most 0.01 for the frontier and (G1) sets;
       - for the kappa <= 1.25 set, lambda/L and the share of lambda^2 from heights at most q^{0.4} both fall with q,
         and the share from b with |R(b)| >= 0.3|W| is at most 0.02 at q >= 100003;
       - for the random set, the share from b != 1 with |R(b)| >= 0.1|W| is at most 0.01 at q >= 100003.
Mutations: (m1) the construction's length read as N/V, exponent 2/9, for which (A1)'s comparison with the flat
threshold must fail; (m2) the pairs of (A2) without coprimality, for which injectivity must fail; (m3) the chirp
removed in (A3), b_n = phi(theta_n), for which the window gate must fail at some q; (m4) the (G1) set in place of
the kappa <= 1.25 set in (A4)'s alignment gate, which must fail.

Scope.  (A1) is arithmetic; its closed-form row is an identity, so a pass shows only correct transcription.  (A2)
checks one inequality on the sets measured.  (A3) measures one construction at three q; the asymptotic statements
(the construction's length N/(sqrt(q) log q), the Fejer bound) are proved in SEVEN-THIRDS.md section 22, not
here.  (A4) measures the sets two search methods find; it bounds nothing over all sets of size q^{2/3}.
"""
from fractions import Fraction as Fr
from math import gcd

import numpy as np

from energy_frontier import frontier
from gram_probe import QS, Gram
from line_sums import dlog_table

HEX = 0.4


def a1(mut=None):
    n, w, s = Fr(7, 9), Fr(2, 3), Fr(5, 7)
    v, m = s * n, 1 - n
    ok = 1 + n - 2 * v == w and Fr(2, 3) + w / 2 == 1
    ok &= w + Fr(1, 2) - n == Fr(7, 18) > m and n - Fr(1, 2) == Fr(5, 18) < w
    theta = 1 - n - m / 2
    ok &= theta == Fr(1, 9) and 2 * theta == Fr(2, 9)
    ap = n - Fr(1, 2) if mut != "m1" else n - v
    ok &= ap > 2 * theta and 2 * n - 2 * v == Fr(4, 9) > ap and 2 * v > 1
    ok &= Fr(5, 18) + Fr(1, 2) == n
    ok &= w + Fr(1, 4) == Fr(11, 12) < 1 and w + Fr(1, 4) + (1 - w) / 4 == 1
    for ell in range(2, 201, 2):
        h = ell // 2
        r = np.zeros(2 * ell, dtype=np.int64)
        for x in range(h):
            for y in range(h, ell):
                r[y - x] += 1
        ok &= int((r ** 2).sum()) == ell * (ell * ell + 2) // 12
    print(f"(A1) exponents: flat threshold q^{theta} (progressions up to q^{2 * theta}); construction q^{ap}; "
          f"Fejer limit q^{2 * n - 2 * v}; integer bound q^{w + Fr(1, 4)}: {'pass' if ok else 'FAIL'}")
    return ok


def heights(q):
    H = np.full(q, q, dtype=np.int64)
    b = np.arange(q, dtype=np.int64)
    for t in range(1, int(np.sqrt(q)) + 2):
        s = (b * t) % q
        s = np.where(s > q // 2, q - s, s)
        H = np.minimum(H, np.maximum(t, s))
    return H


def top_vec(S, K):
    Ks = np.sort(np.asarray(K))
    if len(Ks) <= 3000:
        mu, U = np.linalg.eigh(S.Kt[(Ks[None, :] - Ks[:, None]) % S.L])
        v = np.zeros(S.L, complex)
        v[Ks] = U[:, -1]
        return v, mu[-1]
    from scipy.sparse.linalg import LinearOperator, eigsh

    def mv(x):
        z = np.zeros(S.L, complex)
        z[Ks] = x.ravel()
        return S.G(z)[Ks]
    mu, U = eigsh(LinearOperator((len(Ks), len(Ks)), matvec=mv, dtype=complex), k=1, which="LA", tol=1e-10,
                  maxiter=5000)
    v = np.zeros(S.L, complex)
    v[Ks] = U[:, 0]
    return v, mu[0]


def pairs(h, mut=None):
    return [(s, t) for s in range(1, h + 1) for t in range(1, h + 1)
            if (s, t) != (1, 1) and (gcd(s, t) == 1 or mut == "m2")]


def injective(q, h, mut=None):
    res = [s * pow(t, -1, q) % q for s, t in pairs(h, mut)]
    return len(set(res)) == len(res) and 1 not in res


def anatomy(S, K, dl, Hb, pw, Dh):
    q, L, N = S.q, S.L, S.N
    v, lam = top_vec(S, K)
    V = L * np.fft.ifft(v)
    a = np.zeros(L, complex)
    a[S.idx] = S.w * V[S.idx]
    ind = np.zeros(L)
    ind[K] = 1
    R = L * np.fft.ifft(ind)
    rho = np.conj(np.fft.ifft(np.abs(np.fft.fft(a)) ** 2))
    c = (R * rho).real
    tot = c.sum()
    out = {"lam/L": lam / L, "decomp": abs(tot - lam ** 2) / lam ** 2, "diag": c[0] / tot}
    Hbeta, absR, R0 = Hb[pw], np.abs(R), len(K)
    for ex in (0.2, 0.3, 0.4):
        out[f"H<=q^{ex}"] = c[Hbeta <= q ** ex].sum() / tot
    off = np.arange(L) != 0
    for tau in (0.3, 0.1, 0.03):
        out[f"|R|>={tau}"] = c[(absR >= tau * R0) & off].sum() / tot
    h = int(q ** HEX)
    av = np.zeros(2 * N + 2, complex)
    nn = np.arange(N, 2 * N + 1)
    av[nn] = a[dl[nn]]
    Ih, s4, c2 = 0.0, 0.0, 0.0
    for s_, t_ in pairs(h):
        lo, hi = -(-N // min(s_, t_)), (2 * N) // max(s_, t_)
        if hi < lo:
            continue
        j = np.arange(lo, hi + 1)
        cst = np.vdot(av[s_ * j], av[t_ * j])
        Rv = R[dl[s_ * pow(t_, -1, q) % q]]
        Ih += (Rv * cst).real
        s4 += abs(Rv) ** 4
        c2 += abs(cst) ** 2
    kap = S.energy(K) * L / R0 ** 4
    na2 = (np.abs(a) ** 2).sum()
    bound = R0 * max(kap - 1, 0.0) ** 0.25 * h ** 0.5 * Dh * na2
    out.update({"kappa": kap, "int": Ih / tot, "int/bound": abs(Ih) / bound,
                "s4ok": s4 <= R0 ** 4 * (kap - 1) * (1 + 1e-9) + 1e-6})
    return out


def bump(x):
    def sm(u):
        u = np.clip(u, 0, 1)
        e1 = np.where(u > 0, np.exp(-1 / np.maximum(u, 1e-300)), 0.0)
        e2 = np.where(u < 1, np.exp(-1 / np.maximum(1 - u, 1e-300)), 0.0)
        return e1 / (e1 + e2)
    return sm((x - 1 / 8) * 16) * sm((7 / 8 - x) * 16)


def window(ell):
    return np.arange(int(np.ceil(ell / 4)), int(np.floor(3 * ell / 4)) + 1)


def chirp_B(S, dl, ell, mut=None):
    """B(j) = sum_{n in [N, 2N]} b_n chi_j(n) for every exponent j."""
    n = np.arange(S.N, 2 * S.N + 1)
    th = dl[n] / S.L
    f = np.zeros(S.L, complex)
    np.add.at(f, dl[n], bump(th) * (np.exp(-1j * np.pi * ell * th ** 2) if mut != "m3" else 1.0))
    return S.L * np.fft.ifft(f)


def main_terms(nI, ell, js, mut=None):
    """|I| c_j(0), c_j(0) the integral of phi(x) e(jx - l x^2/2) over [0, 1], by the midpoint rule."""
    x = (np.arange(1 << 16) + 0.5) / (1 << 16)
    g = bump(x) * (np.exp(-1j * np.pi * ell * x ** 2) if mut != "m3" else 1.0)
    return nI * np.array([np.mean(g * np.exp(2j * np.pi * j * x)) for j in js])


def a3(S, dl, mut=None):
    N, nI = S.N, S.N + 1
    Vt = N ** (5 / 7)
    ell = int((nI / (2 * Vt)) ** 2)
    js = window(ell)
    B, main = chirp_B(S, dl, ell, mut)[js], main_terms(nI, ell, js, mut)
    ok = bool((np.abs(B) >= Vt).all() and (np.abs(B - main) <= np.abs(main) / 2).all())
    best = 0
    for e in sorted(set(int(x) for x in np.geomspace(4, 4 * (N / Vt) ** 2, 40))):
        if (np.abs(chirp_B(S, dl, e, mut)[window(e)]) >= Vt).all():
            best = e
    out = {"l": ell, "window ok": ok, "best l": best, "N^2/V^2": (N / Vt) ** 2}
    if best:
        jg = window(best)
        T = Gram(S.q, kind="sharp", dl=dl).Kt[(jg[None, :] - jg[:, None]) % S.L]
        out["Delta(P)/|I|"] = np.linalg.eigvalsh(T)[-1] / nI
        out["Theta^2"] = theta2(len(jg), S.L)
    return out


def theta2(lw, L):
    """(E(A, B) - |A|^2|B|^2/L)/(|A||B|) for the two halves A, B of a progression of length lw in Z/L."""
    a, b = lw // 2, lw - lw // 2
    r = np.zeros(lw + 1, dtype=np.int64)
    for x in range(a):
        r[a - x:lw - x] += 1
    return (int((r ** 2).sum()) - a * a * b * b / L) / (a * b)


def main():
    ok = a1()
    caught = {"m1": not a1("m1"), "m2": False, "m3": False, "m4": False}
    rng = np.random.default_rng(54)
    trend = {"lam": [], "h04": []}
    for q in QS:
        dl = dlog_table(q)
        S = Gram(q, dl=dl)
        h = int(q ** HEX)
        inj = injective(q, h)
        caught["m2"] |= not injective(q, h, "m2")
        ok &= inj
        r3 = a3(S, dl)
        r3m = a3(S, dl, "m3")
        caught["m3"] |= not r3m["window ok"]
        ok &= r3["window ok"] and r3["best l"] >= r3["N^2/V^2"] / 10 and r3.get("Delta(P)/|I|", np.inf) <= 3
        if q != QS[0]:
            ok &= r3.get("Theta^2", 0) > q ** (2 / 9)
        print(f"(A3) q={q}: l={r3['l']} window {'in' if r3['window ok'] else 'NOT in'} the large-values set; "
              f"largest l on the grid {r3['best l']} against N^2/V^2 = {r3['N^2/V^2']:.1f}; "
              f"Delta(P)/|I| = {r3.get('Delta(P)/|I|', float('nan')):.3f}; "
              f"Theta^2 of its window {r3.get('Theta^2', float('nan')):.2f} against q^(2/9) = {q ** (2 / 9):.2f}; "
              f"chirp removed: largest l {r3m['best l']}, window {'in' if r3m['window ok'] else 'not in'}")
        Hb = heights(q)
        nn = np.arange(S.N, 2 * S.N + 1)
        Dh = int(sum((nn % d == 0).astype(np.int64) for d in range(1, h + 1)).max())
        g = int(np.argmax(dl == 1))
        pw = np.ones(S.L, dtype=np.int64)
        for j in range(1, S.L):
            pw[j] = pw[j - 1] * g % q
        best, _ = frontier(S, steps=150)
        _, K1 = S.alternate()
        sets = {"kappa<=1.25": best[1.25][1], "kappa<=2": best[2.0][1], "G1": K1,
                "random": rng.choice(np.arange(1, S.L), S.R, replace=False)}
        print(f"(A2) q={q}: h = {h}, D_h = {Dh}, pairs injective and missing 1: {inj}")
        res = {}
        for name, K in sets.items():
            o = anatomy(S, K, dl, Hb, pw, Dh)
            res[name] = o
            print(f"(A4) q={q} {name:11s} kappa={o['kappa']:.2f} lam/L={o['lam/L']:.4f} diag={o['diag']:.4f} "
                  f"H<=q^0.2,0.3,0.4: {o['H<=q^0.2']:.3f} {o['H<=q^0.3']:.3f} {o['H<=q^0.4']:.3f}; "
                  f"|R|>=0.3,0.1,0.03|W|: {o['|R|>=0.3']:.3f} {o['|R|>=0.1']:.3f} {o['|R|>=0.03']:.3f}; "
                  f"integer share {o['int']:.5f} (|I_h|/bound {o['int/bound']:.2e}); decomp err {o['decomp']:.1e}")
            ok &= o["decomp"] <= 1e-6 and o["s4ok"] and o["int/bound"] <= 1
            if name != "random":
                ok &= abs(o["int"]) <= 0.01
        trend["lam"].append(res["kappa<=1.25"]["lam/L"])
        trend["h04"].append(res["kappa<=1.25"]["H<=q^0.4"])
        if q != QS[0]:
            ok &= res["random"]["|R|>=0.1"] <= 0.01
            ok &= res["kappa<=1.25"]["|R|>=0.3"] <= 0.02
            caught["m4"] |= not (res["G1"]["|R|>=0.3"] <= 0.02)
    ok &= trend["lam"][0] > trend["lam"][1] > trend["lam"][2] and trend["h04"][0] > trend["h04"][1] > trend["h04"][2]
    print(f"gates {'pass' if ok else 'FAIL'}; mutations: " +
          ", ".join(f"{k} {'caught' if v else 'NOT CAUGHT'}" for k, v in caught.items()))
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
