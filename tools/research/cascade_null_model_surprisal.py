#!/usr/bin/env python3
"""
Adversarial null model for the cascade's numerical closures: how many bits
of surprisal does each headline match carry once the size of the cascade's
own expression pool (the "trials") is priced in?

MOTIVATION
==========
CLAUDE.md ("What NOT to Argue" #2) demands that the numerology question be
engaged quantitatively.  This script inverts that challenge into a
computable statistic.  Instead of asking "is there another combination?"
(there always is, at some complexity), it asks: under a formalised grammar
of cascade-native expressions, what is the probability that SOME expression
matches each observable at least as well as the published one?  The
negative log2 of that probability is the closure's surprisal in bits.
Matches carrying ~0 bits are uninformative regardless of how impressive
the percentage looks; matches carrying many bits survive look-elsewhere
and are genuine anomalies.

The machinery calibrates itself on pseudo-targets (random numbers the
cascade makes no claim about): the fraction of arbitrary targets matched
at 1% / 0.1% by the grammar is the empirical false-positive rate.

PARTS
=====
  A. Multiplicative grammar pool G: products of <=3 cascade atoms with
     integer exponents in {-2,-1,1,2}.  Atoms: small integers and their
     square roots, pi, sqrt(pi), e, the layer quantities R(d), N(d)=
     sqrt(pi) R(d), alpha(d), Omega(d), p(d) at cascade-relevant d, and
     the descent propagators exp(Phi(a..b)) the series actually uses.
     Deliberately GENEROUS: every published closure formula lives in (or
     below) this grammar, most at complexity <= 3.
  B. Headline-target audit: local expression density, nearest grammar
     expressions, and surprisal of each published match.
  C. Pseudo-target calibration (false-positive baseline) at complexity
     <=2 and <=3.
  D. Additive grammar check for 1/alpha_em (the published formula is a
     3-term sum).
  E. Correction-family audit: the alpha(d*)/chi^k grid vs the nine needed
     shifts; per-observable surprisal; reuse-pair bonuses; Monte-Carlo
     look-elsewhere for the scan over candidate observables (Part IVb:
     "a systematic search of all Standard Model precision observables").
  F. Variant-space audit of the m_mu/m_e leading formula.
  G. The 120-decade hierarchy over candidate canonical constants K.

Runtime ~2 min, memory ~1 GB peak.  Results print to stdout.

HONESTY NOTES
=============
- Part E's null draws needed shifts log-uniform over the family span:
  favourable to the cascade in assuming every scanned observable had a
  closable residual, unfavourable in ignoring that leading residuals
  cluster mid-span.  Sensitivity to the scan size T is reported.
- The grammar is a model of the cascade's expression language, not THE
  language; densities at complexity levels 1-3 let the reader pick their
  own prior.
- Nothing here proves a match is a coincidence.  It prices what the match
  is worth if it is not one.
"""

import math
import sys
import os
from collections import defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import R, alpha, Omega, p  # noqa: E402

PI = math.pi
SQRTPI = math.sqrt(PI)
E = math.e
CHI = 2.0

rng = np.random.default_rng(20260718)


def Nl(d):
    """Cascade lapse N(d) = sqrt(pi) * R(d)  (Part 0 / Part II usage)."""
    return SQRTPI * R(d)


def Phi(a, b):
    """Cascade potential sum_{d=a}^{b} p(d)."""
    return sum(p(d) for d in range(a, b + 1))


def log10_Omega(d):
    """log10 of the d-sphere area, safe for large d."""
    return (math.log10(2.0) + (d + 1) / 2.0 * math.log10(PI)
            - math.lgamma((d + 1) / 2.0) / math.log(10.0))


# ======================================================================
# Part A: the multiplicative grammar pool
# ======================================================================

def build_atoms():
    atoms = [("1", 1.0),
             ("2", 2.0), ("3", 3.0), ("5", 5.0), ("7", 7.0),
             ("sqrt2", math.sqrt(2)), ("sqrt3", math.sqrt(3)),
             ("sqrt5", math.sqrt(5)), ("sqrt7", math.sqrt(7)),
             ("pi", PI), ("sqrtpi", SQRTPI), ("e", E)]
    DIMS = [2, 3, 4, 5, 7, 11, 12, 13, 14, 19, 21]
    for d in DIMS:
        atoms.append((f"R({d})", R(d)))
        atoms.append((f"N({d})", Nl(d)))
        atoms.append((f"alpha({d})", alpha(d)))
        atoms.append((f"Omega({d})", Omega(d)))
    for d in [7, 11, 12, 13, 14, 19, 21]:      # p(d) > 0 only
        atoms.append((f"p({d})", p(d)))
    # descent propagators the series actually uses (generous: cost 1)
    for (a, b) in [(5, 12), (5, 13), (5, 14), (6, 13), (13, 21), (14, 21)]:
        atoms.append((f"exp(Phi({a}..{b}))", math.exp(Phi(a, b))))
    return atoms


EXPONENTS = [-2, -1, 1, 2]


def build_pool(atoms):
    """Return (powered atoms, unique sorted logs at complexity 1, 2, 3)."""
    names = [n for n, _ in atoms]
    logs = np.array([math.log(v) for _, v in atoms])
    L1_logs, L1_names = [], []
    for i, ln in enumerate(logs):
        for e_ in EXPONENTS:
            L1_logs.append(e_ * ln)
            L1_names.append(names[i] if e_ == 1 else f"{names[i]}^{e_}")
    L1 = np.array(L1_logs)
    S2 = (L1[:, None] + L1[None, :]).ravel()
    n1 = len(L1)
    S3 = np.empty(len(S2) * n1, dtype=np.float64)
    idx = 0
    step = max(1, 4_000_000 // n1)
    for start in range(0, len(S2), step):
        block = S2[start:start + step]
        out = (block[:, None] + L1[None, :]).ravel()
        S3[idx:idx + len(out)] = out
        idx += len(out)
    S3 = S3[:idx]

    def uniq(a):
        a = a[np.isfinite(a)]
        a = a[np.abs(a) < math.log(1e8)]
        return np.unique(np.round(a, 9))

    return (L1, L1_names), uniq(L1), uniq(S2), uniq(S3)


def local_density(U, target, halfwidth=0.35):
    lt = math.log(target)
    lo = np.searchsorted(U, lt - halfwidth)
    hi = np.searchsorted(U, lt + halfwidth)
    return (hi - lo) / (2 * halfwidth)


def build_named_pairs(L1pack):
    (L1, L1_names) = L1pack
    logs, names = [], []
    n = len(L1)
    for i in range(n):
        for j in range(i, n):
            logs.append(L1[i] + L1[j])
            names.append(f"{L1_names[i]}*{L1_names[j]}")
    logs = np.array(logs)
    order = np.argsort(logs)
    return logs[order], [names[k] for k in order]


def nearest_named(L1pack, named_pairs, target, topk=3):
    """Best complexity<=3 named expressions: powered atom x named pair."""
    (L1, L1_names) = L1pack
    lt = math.log(target)
    pair_logs, pair_names = named_pairs
    best = []
    for a_log, a_name in zip(L1, L1_names):
        resid = lt - a_log
        j = np.searchsorted(pair_logs, resid)
        for jj in (j - 1, j):
            if 0 <= jj < len(pair_logs):
                d = abs(pair_logs[jj] + a_log - lt)
                best.append((d, f"{a_name} * {pair_names[jj]}"))
    best.sort(key=lambda t: t[0])
    out, seen = [], set()
    for d, nm in best:
        key = round(d, 12)
        if key in seen:
            continue
        seen.add(key)
        out.append((d, nm))
        if len(out) == topk:
            break
    return out


# ======================================================================
# Parts B and C
# ======================================================================

TARGETS = [
    # (name, observed value, cascade claimed relative deviation, formula)
    ("Omega_Lambda",  0.6847,            0.0044,  "(pi-1)/pi   [additive]"),
    ("Omega_m",       0.315,             0.0105,  "1/pi"),
    ("m_H/m_W",       125.25 / 80.377,   0.0080,  "pi/2"),
    ("m_K/m_pi",      493.677 / 139.570, 0.00045, "5/sqrt2"),
    ("m_eta'/m_eta",  957.78 / 547.86,   0.00103, "7/4"),
    ("f_pi/m_pi",     0.6597,            0.0106,  "2/3"),
    ("m_pi/Lambda",   0.6646,            0.0031,  "2/3"),
    ("m_mu/m_e",      206.76828,         0.0013,  "exp(Phi(13->21))*2sqrtpi"),
    ("1/alpha_em",    137.035999,        5.7e-5,  "1/a13+pi/a14+6pi [additive]"),
]


def part_BC(U1, U2, U3, L1pack, named_pairs):
    print("=" * 78)
    print("PART B: headline-target audit (multiplicative grammar)")
    print("=" * 78)
    print(f"pool sizes (unique values, |log|<ln 1e8):  "
          f"C<=1: {len(U1):,}   C<=2: {len(U2):,}   C<=3: {len(U3):,}")
    print()
    print(f"{'target':<14}{'value':>10}  {'dev%':>7}  "
          f"{'rho(C2)':>8}{'rho(C3)':>10}  {'P(C2)':>7}{'P(C3)':>7}  "
          f"{'bits(C2)':>9}{'bits(C3)':>9}")
    rows = []
    for name, val, tol, formula in TARGETS:
        r2 = local_density(U2, val)
        r3 = local_density(U3, val)
        p2 = min(1.0, 1 - math.exp(-r2 * 2 * tol))
        p3 = min(1.0, 1 - math.exp(-r3 * 2 * tol))
        b2 = -math.log2(p2) if p2 > 0 else float("inf")
        b3 = -math.log2(p3) if p3 > 0 else float("inf")
        rows.append((name, val, tol, formula))
        print(f"{name:<14}{val:>10.5f}  {100*tol:>6.3f}%  "
              f"{r2:>8.0f}{r3:>10.0f}  {p2:>7.3f}{p3:>7.3f}  "
              f"{b2:>9.2f}{b3:>9.2f}")
    print()
    print("nearest complexity<=3 pool expressions per target:")
    for name, val, tol, formula in rows:
        near = nearest_named(L1pack, named_pairs, val)
        alts = ";  ".join(f"{nm} ({100*d:.4f}%)" for d, nm in near)
        print(f"  {name:<14} claimed: {formula} ({100*tol:.3f}%)")
        print(f"  {'':<14} pool:    {alts}")
    print()

    print("=" * 78)
    print("PART C: pseudo-target calibration (false-positive baseline)")
    print("=" * 78)
    M = 2000
    pseudo = np.exp(rng.uniform(math.log(0.5), math.log(250.0), M))

    def nearest_dists(U):
        out = np.empty(M)
        for i, t in enumerate(pseudo):
            lt = math.log(t)
            j = np.searchsorted(U, lt)
            cand = [abs(U[jj] - lt) for jj in (j - 1, j) if 0 <= jj < len(U)]
            out[i] = min(cand)
        return out

    for label, U in (("C<=2", U2), ("C<=3", U3)):
        d = nearest_dists(U)
        qs = ", ".join(f"p{q}={100*np.percentile(d,q):.4f}%"
                       for q in (50, 90, 99))
        fr = ", ".join(f"{100*float(np.mean(d<=t)):.1f}% within {100*t:g}%"
                       for t in (0.01, 0.001, 0.0001))
        print(f"  {label}: nearest-match dev {qs}")
        print(f"  {label}: random targets matched: {fr}")
    print()


# ======================================================================
# Part D: additive grammar for 1/alpha_em
# ======================================================================

def part_D(U2):
    print("=" * 78)
    print("PART D: additive grammar check for 1/alpha_em = 137.035999")
    print("=" * 78)
    target = 137.035999
    tol_pub = target * 5.7e-5              # the cascade's achieved 0.0057%
    sub = np.exp(U2[(U2 > math.log(1e-3)) & (U2 < math.log(500.0))])
    sub = np.sort(sub)
    print(f"  additive sub-pool: {len(sub):,} unique complexity<=2 values "
          f"in [1e-3, 500]")

    def count_two_sums(t, delta):
        n = 0
        for a in sub:
            if a >= t:
                break
            lo = np.searchsorted(sub, t - a - delta)
            hi = np.searchsorted(sub, t - a + delta)
            n += int(hi - lo)
        return n

    n_pub = count_two_sums(target, tol_pub)
    n_win = count_two_sums(target, target * 0.02)
    rho = n_win / (2 * 0.02)               # per relative unit
    p_two = min(1.0, 1 - math.exp(-rho * 2 * 5.7e-5))
    print(f"  2-term sums a+b within the published 0.0057%: {n_pub:,}")
    print(f"  local 2-sum density: {rho:,.0f} per unit relative width")
    print(f"  P(some 2-term sum matches this well) ~ {p_two:.4f}  ->  "
          f"bits: {-math.log2(p_two) if 0 < p_two < 1 else 0.0:.2f}")
    print("  (the published formula is a THREE-term sum; the 3-term pool is")
    print("   strictly denser, so its bits are <= the 2-term bits: ~0)")
    print()


# ======================================================================
# Part E: correction-family audit
# ======================================================================

def p_any(sig, grid, L):
    """P(some grid member within sig of a log-uniform needed shift)."""
    return min(1.0, sum(2 * sig / (g * L) for g in grid))


def p_specific(sig, member, L):
    """P(needed shift within sig of one designated member)."""
    return min(1.0, 2 * sig / (member * L))


def part_E():
    print("=" * 78)
    print("PART E: alpha(d*)/chi^k correction-family audit")
    print("=" * 78)
    grid = np.array(sorted(alpha(d) / CHI**k
                           for d in (5, 7, 14, 19) for k in (1, 2, 3, 4)))
    span_lo, span_hi = grid.min() / 1.5, grid.max() * 1.5
    L = math.log(span_hi / span_lo)
    print("  grid ({} members x sign): {}".format(
        len(grid), ", ".join(f"{g:.5f}" for g in grid)))
    print(f"  null span for needed shifts: [{span_lo:.5f}, {span_hi:.5f}]"
          f"  (ln-width {L:.2f})")

    a_s_lead = alpha(12) * math.exp(Phi(5, 12))
    mtmu_lead = math.exp(Phi(6, 13)) * 2 * SQRTPI
    s2w_lead = R(14)**2 / (PI * R(13)**2 + R(14)**2)
    thC_lead = math.degrees(math.atan(
        math.tan(math.acos(Nl(13) / Nl(12))) * math.exp(-p(13) / 2)))
    bs_lead = mtmu_lead * E
    # (name, |needed shift|, sigma in shift units, designated member)
    obs = [
        ("alpha_s",    abs(math.log(0.1179 / a_s_lead)),
         0.0009 / 0.1179,   alpha(14) / 2),
        ("m_tau/m_mu", abs(math.log(16.81703 / mtmu_lead)),
         0.00114 / 16.81703, alpha(14) / 2),
        ("m_tau abs",  abs(math.log(1776.86 / 1754.20)),
         0.12 / 1776.86,    alpha(19) / 2),
        ("ell_A",      abs(math.log(301.6 / (301.44 / math.exp(alpha(19) / 2)))),
         0.09 / 301.6,      alpha(19) / 2),
        ("sin2thW",    abs(math.log(0.23121 / s2w_lead)),
         0.00004 / 0.23121, alpha(5) / 8),
        ("Omega_m",    abs(math.log(0.315 * PI)),
         0.007 / 0.315,     alpha(5) / 8),
        ("theta_C",    abs(math.log(13.04 / thC_lead)),
         0.05 / 13.04,      alpha(7) / 4),
        ("b/s",        abs(math.log(44.75 / bs_lead)),
         0.005,             alpha(7) / 16),
        ("theta_23",   abs(math.log(2.38 / 2.39020)),
         0.06 / 2.38,       alpha(7) / 16),
    ]
    print()
    print(f"{'observable':<12}{'|needed|':>10}{'sigma':>10}{'member':>10}"
          f"{'|diff|/sig':>11}{'P(any)':>9}{'bits':>7}")
    total_bits = 0.0
    for name, need, sig, member in obs:
        pa = p_any(sig, grid, L)
        bits = -math.log2(pa) if pa < 1 else 0.0
        total_bits += bits
        print(f"{name:<12}{need:>10.5f}{sig:>10.5f}{member:>10.5f}"
              f"{abs(need-member)/sig:>11.2f}{pa:>9.3f}{bits:>7.2f}")
    print(f"  naive independent-product surprisal: {total_bits:.1f} bits")

    print()
    print("  reuse pairs (same member closes both):")
    pairs = [("alpha_s", "m_tau/m_mu"), ("m_tau abs", "ell_A"),
             ("sin2thW", "Omega_m")]
    d = {name: (need, sig, mem) for name, need, sig, mem in obs}
    reuse_bits = 0.0
    for a, b in pairs:
        need_b, sig_b, mem = d[b]
        extra = min(1.0, p_specific(sig_b, mem, L) / p_any(sig_b, grid, L))
        bits = -math.log2(extra) if extra < 1 else 0.0
        reuse_bits += bits
        print(f"    {a:<11}+ {b:<11} P(same member|matched)={extra:.4f}"
              f"   extra bits: {bits:.2f}")
    print(f"  reuse bonus total: {reuse_bits:.1f} bits")
    S_obs = total_bits + reuse_bits
    print(f"  AS-PRESENTED TOTAL (no look-elsewhere): {S_obs:.1f} bits")

    print()
    print("  Monte-Carlo look-elsewhere (needed shifts log-uniform on span;")
    print("  T scanned observables: the 9 real sigmas always included, extra")
    print("  candidates draw sigma log-uniform in [5e-5, 2e-2]; MC scoring")
    print("  mirrors the real scoring incl. same-member credits):")
    sig_real = [sig for _, _, sig, _ in obs]

    def run_mc(T, n_mc=40_000):
        count = 0
        stats = np.empty(n_mc)
        gl = grid
        for it in range(n_mc):
            n_extra = T - len(sig_real)
            sigs = sig_real + list(np.exp(rng.uniform(
                math.log(5e-5), math.log(2e-2), n_extra)))
            needs = np.exp(rng.uniform(math.log(span_lo), math.log(span_hi),
                                       T))
            S = 0.0
            members = defaultdict(list)
            for s_, nd in zip(sigs, needs):
                dif = np.abs(gl - nd)
                j = int(np.argmin(dif))
                if dif[j] <= s_:
                    pa = p_any(s_, gl, L)
                    S += -math.log2(pa) if pa < 1 else 0.0
                    members[j].append(s_)
            # same-member credits, scored exactly like the real pairs
            for j, sig_list in members.items():
                if len(sig_list) > 1:
                    sig_list.sort(reverse=True)     # first = primary
                    for s_ in sig_list[1:]:
                        extra = min(1.0, p_specific(s_, gl[j], L)
                                    / p_any(s_, gl, L))
                        S += -math.log2(extra) if extra < 1 else 0.0
            stats[it] = S
            if S >= S_obs:
                count += 1
        ple = max(count, 0.5) / n_mc
        return stats, ple, count

    for T in (9, 20, 40):
        stats, ple, count = run_mc(T)
        note = "" if count else " (0 hits; upper bound)"
        print(f"    T={T:>3}: null S 50/95/99.9%: "
              f"{np.percentile(stats,50):5.1f} /{np.percentile(stats,95):5.1f}"
              f" /{np.percentile(stats,99.9):5.1f}   "
              f"P(S>=S_obs={S_obs:.0f}) ~ {ple:.1e} -> "
              f"{-math.log2(ple):.1f} bits{note}")
    print()


# ======================================================================
# Part F: m_mu/m_e leading-formula variant space
# ======================================================================

def part_F():
    print("=" * 78)
    print("PART F: m_mu/m_e leading-formula variant space")
    print("=" * 78)
    target = 206.76828
    factors = [("1", 1.0), ("2", 2.0), ("sqrtpi", SQRTPI),
               ("2sqrtpi", 2 * SQRTPI), ("pi", PI), ("2pi", 2 * PI),
               ("4pi", 4 * PI), ("e", E), ("4sqrtpi", 4 * SQRTPI),
               ("sqrt2pi", math.sqrt(2 * PI))]
    variants = []
    for L_ in (7, 8, 9):
        for a in range(5, 15):
            b = a + L_ - 1
            if b > 22:
                continue
            base = math.exp(Phi(a, b))
            for fn, fv in factors:
                variants.append((f"exp(Phi({a}..{b}))*{fn}", base * fv))
    vals = np.array([v for _, v in variants])
    devs = np.abs(vals / target - 1)
    n_13 = int(np.sum(devs <= 0.0013))
    n_1 = int(np.sum(devs <= 0.01))
    in_win = int(np.sum(np.abs(np.log(vals / target)) < math.log(2.0)))
    rho_v = in_win / (2 * math.log(2.0))
    p_hit = min(1.0, 1 - math.exp(-rho_v * 2 * 0.0013))
    print(f"  variants enumerated: {len(variants)} (spans of length 7/8/9 "
          f"anchored d=5..14, x {len(factors)} topological prefactors)")
    print(f"  variants within 0.13% of observed: {n_13}   within 1%: {n_1}")
    print(f"  local variant density near target: {rho_v:.1f} per ln")
    print(f"  P(>=1 variant within 0.13%) ~ {p_hit:.3f}  ->  "
          f"{-math.log2(p_hit):.1f} bits")
    best = sorted(zip(devs, [n for n, _ in variants]))[:4]
    for d_, n_ in best:
        print(f"    {n_:<26} dev {100*d_:.3f}%")
    print()


# ======================================================================
# Part G: the 120-decade hierarchy
# ======================================================================

def part_G(U2):
    print("=" * 78)
    print("PART G: the 120-decade hierarchy under candidate constants K")
    print("=" * 78)
    target_dec = 120.146          # -log10(7.15e-121), Planck 2018

    def dec_for_K(K):
        """-log10( (18/pi^3) Omega(d1) Omega(d2) ) for (c1,c2)=(ln K, K)."""
        c1, c2 = math.log(K), K
        if c1 <= p(7):
            return None

        def solve(c):
            lo, hi = 7.0, 50000.0
            for _ in range(200):
                mid = (lo + hi) / 2
                if p(mid) < c:
                    lo = mid
                else:
                    hi = mid
            return lo
        d1 = int(solve(c1))
        d2 = int(solve(c2))
        return -(math.log10(18 / PI**3) + log10_Omega(d1) + log10_Omega(d2))

    Ks = np.exp(U2[(U2 > math.log(1.06)) & (U2 < math.log(3.5))])
    decs = np.array([d_ for d_ in (dec_for_K(float(K)) for K in Ks)
                     if d_ is not None])
    print(f"  candidate constants K (complexity<=2 pool, 1.06<K<=3.5): "
          f"{len(decs):,}")
    print(f"  decade outputs span: {decs.min():.0f} .. {decs.max():.0f}")
    for w in (0.5, 1.0):
        h = int(np.sum(np.abs(decs - target_dec) <= w))
        frac = h / len(decs)
        print(f"  fraction landing within +-{w} decade of 120.15: "
              f"{100*frac:.2f}%  ({h} hits)  -> "
              f"{-math.log2(max(frac, 1e-9)):.1f} bits IF K were a free draw")
    print(f"  the cascade's K = sqrt(pi): decades = "
          f"{dec_for_K(SQRTPI):.3f}  (observed 120.146)")
    Kc = np.exp(rng.uniform(math.log(1.06), math.log(3.5), 4000))
    decs_c = np.array([d_ for d_ in (dec_for_K(float(k)) for k in Kc)
                       if d_ is not None])
    frac_c = float(np.mean(np.abs(decs_c - target_dec) <= 0.5))
    print(f"  continuous log-uniform K null: P(within +-0.5 decade) = "
          f"{100*frac_c:.2f}%  -> {-math.log2(max(frac_c, 1e-9)):.1f} bits")
    print("  (subtract ~2 bits for the choice among admissible constructions:")
    print("   the papers exhibit at least p=c1, p=c2, argmax V, argmax Omega)")
    print()


def main():
    atoms = build_atoms()
    L1pack, U1, U2, U3 = build_pool(atoms)
    named_pairs = build_named_pairs(L1pack)
    part_BC(U1, U2, U3, L1pack, named_pairs)
    part_D(U2)
    part_E()
    part_F()
    part_G(U2)
    print("done.")


if __name__ == "__main__":
    main()
