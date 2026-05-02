#!/usr/bin/env python3
"""
Systematic search over Bott-averaging schemes for cascade lepton mass residuals.

Search dimensions:
  - Window width: 2, 3, 4, 5, 6, 7 layers
  - Window position: forward, centered, mixed
  - Weight function: uniform, Omega(d), R(d), alpha(d), N(d), 1/Omega(d), p(d)
  - Hybrid (different scheme per generation based on growth/descent)
  - Cascade primitive averaged: Phi(d), N(d), R(d), p(d)

Goal: minimize joint relative error in (tau, mu, e) corrections vs required.

Required corrections:
  tau (d_g=5):  +1.25%  (cascade leading is LOW)
  mu  (d_g=13): -0.47%  (cascade leading is HIGH)
  e   (d_g=21): -0.58%  (cascade leading is HIGH)
"""

from __future__ import annotations
import math
from itertools import product
from scipy.special import digamma, gamma


def p_d(d): return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)
def Phi_d(d, d_min=4):
    if d <= d_min: return 0.0
    return sum(p_d(dprime) for dprime in range(d_min + 1, d + 1))
def Omega_d(d): return 2 * math.pi ** (d / 2) / gamma(d / 2)
def R_d(d): return math.exp(math.lgamma(d / 2 + 1) - math.lgamma((d + 3) / 2))
def alpha_d(d): return R_d(d) ** 2 / 4
def N_d(d): return math.sqrt(math.pi) * math.exp(math.lgamma((d + 1) / 2) - math.lgamma((d + 2) / 2))


WEIGHT_FNS = {
    "uniform": lambda d: 1.0,
    "Omega": Omega_d,
    "R": R_d,
    "alpha": alpha_d,
    "N": N_d,
    "1/Omega": lambda d: 1 / Omega_d(d),
    "p": lambda d: max(abs(p_d(d)), 1e-6),
    "Omega^2": lambda d: Omega_d(d) ** 2,
    "Omega/R": lambda d: Omega_d(d) / R_d(d),
}

OBSERVER = 4
GENERATIONS = {1: 21, 2: 13, 3: 5}
N_D_COUNT = {1: 3, 2: 2, 3: 1}
TWO_SQRT_PI = 2 * math.sqrt(math.pi)
REQUIRED = {"tau": 1.25, "mu": -0.47, "e": -0.58}


def get_window(d_g, width, offset, exclude_below_observer=True):
    """Window: [d_g + offset - width//2, d_g + offset + (width-1)//2 + 1)
    But exclude any d <= OBSERVER."""
    start = d_g + offset - width // 2
    end = start + width
    return [d for d in range(start, end) if d > OBSERVER]


def averaged_correction(d_g, window, weight_fn, primitive_fn=Phi_d):
    """Compute correction = exp(-(<F> - F(d_g))) - 1 in percent.

    primitive_fn(d) is the cascade quantity averaged.
    For Phi: cascade mass is exp(-Phi); correction = exp(-(<Phi> - Phi(d_g))) - 1.
    """
    if not window:
        return 0.0
    weights = [weight_fn(d) for d in window]
    wsum = sum(weights)
    avg = sum(w * primitive_fn(d) for w, d in zip(weights, window)) / wsum
    pt = primitive_fn(d_g)
    return (math.exp(-(avg - pt)) - 1) * 100


def joint_error(corrections):
    """Sum of squared relative errors vs required corrections."""
    err = 0
    for label, corr in corrections.items():
        req = REQUIRED[label]
        err += ((corr - req) / req) ** 2
    return math.sqrt(err)


def evaluate_scheme(width_g, offset_g, width_d, offset_d, weight_name, hybrid=True):
    """Evaluate scheme: width_g/offset_g for growth gen (tau, d=5),
    width_d/offset_d for descent gens (mu d=13, e d=21).
    If hybrid=False, use width_g/offset_g for all."""
    weight_fn = WEIGHT_FNS[weight_name]
    corrections = {}
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        if hybrid and gen in [1, 2]:
            window = get_window(d_g, width_d, offset_d)
        else:
            window = get_window(d_g, width_g, offset_g)
        corrections[label] = averaged_correction(d_g, window, weight_fn)
    return corrections


def main():
    print("=" * 78)
    print("Systematic search for best Bott-averaging scheme")
    print("=" * 78)
    print()
    print("Required corrections: tau +1.25%, mu -0.47%, e -0.58%")
    print()

    # Search parameters
    widths = [2, 3, 4, 5, 6, 7]
    offsets_g = [0, 1]  # for growth gen tau, can only go forward (offset 0 = start at d_g)
    offsets_d = [-2, -1, 0, 1]
    weight_names = list(WEIGHT_FNS.keys())

    # Phase 1: NON-HYBRID search (single scheme for all 3)
    print("=" * 78)
    print("PHASE 1: Non-hybrid (same window/weight for all 3 generations)")
    print("=" * 78)
    print()
    results = []
    for width in widths:
        for offset in offsets_d:  # can be negative
            for weight in weight_names:
                corrs = evaluate_scheme(width, offset, width, offset, weight, hybrid=False)
                err = joint_error(corrs)
                results.append((err, width, offset, weight, corrs))
    results.sort()
    print(f"  Top 10 non-hybrid schemes (sorted by joint error):")
    print(f"  {'rank':>4} {'err':>8} {'width':>5} {'offset':>6} {'weight':>10} {'tau':>10} {'mu':>10} {'e':>10}")
    for i, (err, w, o, wt, c) in enumerate(results[:10]):
        print(f"  {i+1:>4} {err:>8.3f} {w:>5} {o:>+6} {wt:>10} {c['tau']:>+9.3f}% {c['mu']:>+9.3f}% {c['e']:>+9.3f}%")
    print()

    # Phase 2: HYBRID search (different scheme for growth vs descent)
    print("=" * 78)
    print("PHASE 2: Hybrid (forward for growth, varied for descent)")
    print("=" * 78)
    print()
    hybrid_results = []
    # Growth (tau): only positive offsets (can't go below observer)
    for wg in [2, 3]:
        for og in [0, 1]:  # window starts at d_g (offset 0) or d_g+1
            for wd in widths:
                for od in offsets_d:
                    for weight in weight_names:
                        corrs = evaluate_scheme(wg, og, wd, od, weight, hybrid=True)
                        err = joint_error(corrs)
                        hybrid_results.append((err, wg, og, wd, od, weight, corrs))
    hybrid_results.sort()
    print(f"  Top 15 hybrid schemes (sorted by joint error):")
    print(f"  {'rank':>4} {'err':>8} {'wg':>3} {'og':>3} {'wd':>3} {'od':>3} {'weight':>10} {'tau':>10} {'mu':>10} {'e':>10}")
    for i, (err, wg, og, wd, od, wt, c) in enumerate(hybrid_results[:15]):
        print(f"  {i+1:>4} {err:>8.3f} {wg:>3} {og:>+3d} {wd:>3} {od:>+3d} {wt:>10} {c['tau']:>+9.3f}% {c['mu']:>+9.3f}% {c['e']:>+9.3f}%")
    print()

    # Phase 3: per-generation independent search
    print("=" * 78)
    print("PHASE 3: Independent per-generation search (best scheme for each)")
    print("=" * 78)
    print()
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        req = REQUIRED[label]
        per_gen_results = []
        for width in widths:
            for offset in [-3, -2, -1, 0, 1, 2]:
                for weight in weight_names:
                    window = get_window(d_g, width, offset)
                    if not window:
                        continue
                    weight_fn = WEIGHT_FNS[weight]
                    corr = averaged_correction(d_g, window, weight_fn)
                    err = abs((corr - req) / req)
                    per_gen_results.append((err, width, offset, weight, corr, window))
        per_gen_results.sort()
        print(f"  {label} (d_g={d_g}, required {req:+.2f}%): best 5 schemes")
        print(f"    {'rank':>4} {'rel err':>8} {'width':>5} {'offset':>6} {'weight':>10} {'corr':>10} {'window':>15}")
        for i, (err, w, o, wt, c, win) in enumerate(per_gen_results[:5]):
            win_str = f"[{win[0]}..{win[-1]}]" if len(win) > 1 else str(win)
            print(f"    {i+1:>4} {err*100:>7.2f}% {w:>5} {o:>+6} {wt:>10} {c:>+9.3f}% {win_str:>15}")
        print()

    # Phase 4: combine the best per-generation choices
    print("=" * 78)
    print("PHASE 4: COMBINE per-generation best schemes")
    print("=" * 78)
    print()
    print("  Best independent scheme per generation (potentially different per gen):")
    best_per_gen = {}
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        req = REQUIRED[label]
        per_gen_results = []
        for width in widths:
            for offset in [-3, -2, -1, 0, 1, 2]:
                for weight in weight_names:
                    window = get_window(d_g, width, offset)
                    if not window:
                        continue
                    weight_fn = WEIGHT_FNS[weight]
                    corr = averaged_correction(d_g, window, weight_fn)
                    err = abs((corr - req) / req)
                    per_gen_results.append((err, width, offset, weight, corr, window))
        per_gen_results.sort()
        best = per_gen_results[0]
        best_per_gen[label] = best
        win_str = f"[{best[5][0]}..{best[5][-1]}]"
        print(f"  {label}: width={best[1]}, offset={best[2]:+d}, weight={best[3]}, corr={best[4]:+.3f}% (req {req:+.2f}%), rel err={best[0]*100:.1f}%, window={win_str}")
    print()

    # Phase 5: TRUE FULL HYBRID search
    # Each generation has INDEPENDENT (width, offset, weight)
    # Joint error = sqrt(sum of per-gen rel err squared)
    print("=" * 78)
    print("PHASE 5: TRUE FULL HYBRID -- independent (width, offset, weight) per gen")
    print("=" * 78)
    print()
    print("  Each generation independently picks its best scheme.")
    print("  The structural cost: cascade has generation-specific averaging rules.")
    print("  But this represents the cascade's BEST POSSIBLE residual closure")
    print("  under the Bott-averaging hypothesis.")
    print()

    # Per-generation best (more comprehensive search)
    per_gen_top = {}
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        req = REQUIRED[label]
        results_pg = []
        for width in widths:
            for offset in [-3, -2, -1, 0, 1, 2, 3]:
                for weight in weight_names:
                    window = get_window(d_g, width, offset)
                    if not window or len(window) < 2:
                        continue
                    weight_fn = WEIGHT_FNS[weight]
                    corr = averaged_correction(d_g, window, weight_fn)
                    err = abs((corr - req) / req)
                    results_pg.append((err, width, offset, weight, corr, window))
        results_pg.sort()
        per_gen_top[label] = results_pg[:5]

    print(f"  Top 5 per generation (independent search):")
    print()
    for label in ["tau", "mu", "e"]:
        print(f"  {label} (req {REQUIRED[label]:+.2f}%):")
        for i, (err, w, o, wt, c, win) in enumerate(per_gen_top[label][:5]):
            win_str = f"[{win[0]}..{win[-1]}]"
            print(f"    {i+1}. width={w}, offset={o:+d}, weight={wt:>10}, "
                  f"corr={c:>+7.3f}%, rel err={err*100:>5.1f}%, window={win_str}")
        print()

    # Joint best: combine each gen's top picks
    best_tau = per_gen_top["tau"][0]
    best_mu = per_gen_top["mu"][0]
    best_e = per_gen_top["e"][0]

    print("  TRUE FULL HYBRID best:")
    print(f"    tau: width={best_tau[1]}, offset={best_tau[2]:+d}, weight={best_tau[3]}, corr={best_tau[4]:+.3f}%  (rel err {best_tau[0]*100:.1f}%)")
    print(f"    mu:  width={best_mu[1]}, offset={best_mu[2]:+d}, weight={best_mu[3]}, corr={best_mu[4]:+.3f}%  (rel err {best_mu[0]*100:.1f}%)")
    print(f"    e:   width={best_e[1]}, offset={best_e[2]:+d}, weight={best_e[3]}, corr={best_e[4]:+.3f}%  (rel err {best_e[0]*100:.1f}%)")
    joint_err_full = math.sqrt(best_tau[0]**2 + best_mu[0]**2 + best_e[0]**2)
    print(f"    JOINT relative error: {joint_err_full:.3f}")
    print()

    # Same weight scan but with independent (w, o) per gen
    print("=" * 78)
    print("PHASE 6: SAME WEIGHT, independent (width, offset) per gen")
    print("=" * 78)
    print()
    print("  Test if a single GLOBAL weight function with per-gen window choice")
    print("  is enough to combat all three residuals.  Saves a 'cascade rule'.")
    print()
    same_weight_results = []
    for weight in weight_names:
        weight_fn = WEIGHT_FNS[weight]
        # For each generation, find best (width, offset) given this weight
        best_per_gen_this_weight = {}
        for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
            d_g = GENERATIONS[gen]
            req = REQUIRED[label]
            results_pg = []
            for width in widths:
                for offset in [-3, -2, -1, 0, 1, 2]:
                    window = get_window(d_g, width, offset)
                    if not window or len(window) < 2:
                        continue
                    corr = averaged_correction(d_g, window, weight_fn)
                    err = abs((corr - req) / req)
                    results_pg.append((err, width, offset, corr, window))
            results_pg.sort()
            best_per_gen_this_weight[label] = results_pg[0] if results_pg else None
        if all(best_per_gen_this_weight[l] is not None for l in ["tau", "mu", "e"]):
            joint = math.sqrt(sum(best_per_gen_this_weight[l][0]**2 for l in ["tau", "mu", "e"]))
            same_weight_results.append((joint, weight, best_per_gen_this_weight))
    same_weight_results.sort()
    print(f"  Top 5 single-weight schemes (with per-gen window):")
    print(f"  {'rank':>4} {'joint err':>10} {'weight':>10} {'tau (w,o,err)':>20} {'mu (w,o,err)':>20} {'e (w,o,err)':>20}")
    for i, (joint, weight, picks) in enumerate(same_weight_results[:5]):
        tau_p = picks["tau"]
        mu_p = picks["mu"]
        e_p = picks["e"]
        print(f"  {i+1:>4} {joint:>10.3f} {weight:>10} "
              f"({tau_p[1]},{tau_p[2]:+d},{tau_p[0]*100:.1f}%) "
              f"({mu_p[1]},{mu_p[2]:+d},{mu_p[0]*100:.1f}%) "
              f"({e_p[1]},{e_p[2]:+d},{e_p[0]*100:.1f}%)")
    print()

    print("=" * 78)
    print("CONCLUSION")
    print("=" * 78)
    print()
    print(f"  TRUE FULL HYBRID joint error: {joint_err_full:.3f}")
    print()
    print(f"  Compared to:")
    print(f"    Best non-hybrid (Phase 1):       1.275")
    print(f"    Best partial-hybrid (Phase 2):   1.275 (essentially same)")
    print(f"    True full hybrid (Phase 5):      {joint_err_full:.3f}")
    print()
    print(f"  Improvement from partial to full hybrid: {1.275 - joint_err_full:.3f}")
    print()


if __name__ == "__main__":
    main()
