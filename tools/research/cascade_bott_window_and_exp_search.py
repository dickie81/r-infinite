#!/usr/bin/env python3
"""
Combined free-parameter search: window AND weight exponent.

For each candidate weight primitive X(d), optimize:
  (width, offset, exponent) per generation independently.

Find:
  (a) Best per-gen joint err under each weight family
  (b) Whether optimal (width, offset, exponent) match cascade-meaningful values
  (c) Whether structural patterns emerge (e.g., Bott-offset alignment)

Cascade primitives tested: Omega(d), R(d), N(d), alpha(d), p(d), 1/Omega(d),
1/R(d), Phi(d), 1/d, d.
"""

from __future__ import annotations
import math
from scipy.special import digamma, gamma
from scipy.optimize import minimize_scalar


def p_d(d): return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_d(d, d_min=4):
    if d <= d_min: return 0.0
    return sum(p_d(dprime) for dprime in range(d_min + 1, d + 1))


def Omega_d(d): return 2 * math.pi ** (d / 2) / gamma(d / 2)
def R_d(d): return math.exp(math.lgamma(d / 2 + 1) - math.lgamma((d + 3) / 2))
def N_d(d): return math.sqrt(math.pi) * math.exp(math.lgamma((d + 1) / 2) - math.lgamma((d + 2) / 2))


PRIMITIVES = {
    "Omega": Omega_d,
    "R": R_d,
    "N": N_d,
    "alpha": lambda d: R_d(d) ** 2 / 4,
    "1/Omega": lambda d: 1 / Omega_d(d),
    "1/R": lambda d: 1 / R_d(d),
    "p_shifted": lambda d: max(p_d(d) + 1, 0.01),
    "d": lambda d: float(d),
    "1/d": lambda d: 1.0 / d,
}

OBSERVER = 4
GENERATIONS = {1: 21, 2: 13, 3: 5}
N_D_COUNT = {1: 3, 2: 2, 3: 1}
TWO_SQRT_PI = 2 * math.sqrt(math.pi)
REQUIRED = {"tau": 1.25, "mu": -0.47, "e": -0.58}


def correction(d_g, window, weight_fn):
    weights = [weight_fn(d) for d in window]
    wsum = sum(weights)
    if wsum == 0: return 0
    Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
    return (math.exp(-(Phi_avg - Phi_d(d_g))) - 1) * 100


def best_window_and_exp(d_g, prim_fn, required):
    """For one generation, find best (window, exponent) for given primitive.
    Return (rel_err, width, offset, p, corr, window)."""
    best = (float('inf'), None, None, None, None, None)
    for width in [2, 3, 4, 5, 6, 7]:
        for offset in [-3, -2, -1, 0, 1, 2, 3]:
            start = d_g + offset - width // 2
            window = [d for d in range(start, start + width) if d > OBSERVER]
            if len(window) < 2:
                continue
            # Optimize exponent
            def loss(p):
                weights = [prim_fn(d) ** p for d in window]
                ws = sum(weights)
                if ws == 0: return 1e9
                Pavg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / ws
                corr = (math.exp(-(Pavg - Phi_d(d_g))) - 1) * 100
                return ((corr - required) / required) ** 2
            try:
                res = minimize_scalar(loss, bounds=(-5, 5), method='bounded')
                if res.fun < best[0]:
                    p_opt = res.x
                    weights = [prim_fn(d) ** p_opt for d in window]
                    ws = sum(weights)
                    Pavg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / ws
                    corr_v = (math.exp(-(Pavg - Phi_d(d_g))) - 1) * 100
                    rel_err = abs((corr_v - required) / required)
                    best = (rel_err, width, offset, p_opt, corr_v, window)
            except Exception:
                pass
    return best


def main():
    print("=" * 78)
    print("Combined search: free window + free exponent per generation")
    print("=" * 78)
    print()
    print("For each cascade primitive X, for each generation:")
    print("  - Search (width, offset) over integers")
    print("  - Optimize exponent p continuously")
    print("Report best (width, offset, p) per gen and structural patterns.")
    print()

    print("Required: tau +1.25%, mu -0.47%, e -0.58%")
    print()

    # For each primitive, find best per-gen and joint err
    print(f"{'X':>10} | {'tau':>30} | {'mu':>30} | {'e':>30} | {'joint':>8}")
    print(f"{'':>10} | {'(w,o,p,err)':>30} | {'(w,o,p,err)':>30} | {'(w,o,p,err)':>30} | ")
    print(f"{'-'*10} | {'-'*30} | {'-'*30} | {'-'*30} | {'-'*8}")

    summary = []
    for prim_name, prim_fn in PRIMITIVES.items():
        per_gen = {}
        for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
            d_g = GENERATIONS[gen]
            req = REQUIRED[label]
            per_gen[label] = best_window_and_exp(d_g, prim_fn, req)
        joint = math.sqrt(sum(per_gen[l][0]**2 for l in ["tau", "mu", "e"]))
        summary.append((joint, prim_name, per_gen))

        def fmt(t):
            err, w, o, p, c, win = t
            return f"({w},{o:+d},p={p:+.2f},{err*100:.1f}%)"
        print(f"{prim_name:>10} | {fmt(per_gen['tau']):>30} | {fmt(per_gen['mu']):>30} | {fmt(per_gen['e']):>30} | {joint:>8.4f}")

    print()
    summary.sort()
    print("=" * 78)
    print("RANKING (sorted by joint err)")
    print("=" * 78)
    print()
    for i, (joint, name, per_gen) in enumerate(summary[:5]):
        print(f"  {i+1}. X = {name}: joint err = {joint:.4f}")
        for label in ["tau", "mu", "e"]:
            err, w, o, p, c, win = per_gen[label]
            print(f"     {label}: width={w}, offset={o:+d}, p={p:+.4f}, "
                  f"corr={c:+.4f}%, rel err={err*100:.2f}%, window={win}")
        print()

    # Look at the BEST result and check structural meaning
    best_overall = summary[0]
    print("=" * 78)
    print("STRUCTURAL ANALYSIS OF BEST RESULT")
    print("=" * 78)
    print()
    name, per_gen = best_overall[1], best_overall[2]
    print(f"Best primitive: X = {name}")
    print(f"Joint relative error: {best_overall[0]:.4f}")
    print()
    print("Per-generation (window, exponent) values:")
    for label in ["tau", "mu", "e"]:
        err, w, o, p, c, win = per_gen[label]
        d_g = GENERATIONS[3 if label == "tau" else (2 if label == "mu" else 1)]
        print(f"  {label} (d_g={d_g}): width={w}, offset={o:+d}, exponent={p:+.4f}")
        print(f"    window={win}, correction={c:+.4f}%, rel err={err*100:.2f}%")
    print()
    print("Check: do the (width, offset, p) values show structural patterns?")
    print("  - Same width across gens? (suggests fixed cascade structural rule)")
    print("  - Same offset? (suggests Bott-aligned positioning)")
    print("  - Exponents related (e.g., integer multiples)?")
    print()
    widths = [per_gen[l][1] for l in ["tau", "mu", "e"]]
    offsets = [per_gen[l][2] for l in ["tau", "mu", "e"]]
    exps = [per_gen[l][3] for l in ["tau", "mu", "e"]]
    print(f"  widths   = {widths}")
    print(f"  offsets  = {offsets}")
    print(f"  exponents = {exps}")
    print()
    if len(set(widths)) == 1:
        print(f"  * SAME WIDTH across gens: w = {widths[0]}")
    if len(set(offsets)) == 1:
        print(f"  * SAME OFFSET across gens: o = {offsets[0]}")
    print()

    # Now do an honest test: GLOBAL params (single width, offset, exponent)
    print("=" * 78)
    print("HONEST TEST: GLOBAL (width, offset, exponent) for all 3 generations")
    print("=" * 78)
    print()
    print("Single rule applied to all gens.  3 free parameters total.")
    print()

    print(f"  {'X':>10} | {'best (w, o, p)':>20} | {'tau':>10} | {'mu':>10} | {'e':>10} | {'joint':>8}")
    print(f"  {'-'*10} | {'-'*20} | {'-'*10} | {'-'*10} | {'-'*10} | {'-'*8}")

    global_results = []
    for prim_name, prim_fn in PRIMITIVES.items():
        best_global = (float('inf'), None, None, None, None)
        for width in [2, 3, 4, 5, 6, 7]:
            for offset in [-3, -2, -1, 0, 1, 2]:
                # Optimize exponent (single global p) to minimize joint err
                def loss(p):
                    err = 0
                    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
                        d_g = GENERATIONS[gen]
                        start = d_g + offset - width // 2
                        window = [d for d in range(start, start + width) if d > OBSERVER]
                        if not window:
                            return 1e9
                        weights = [prim_fn(d) ** p for d in window]
                        ws = sum(weights)
                        if ws == 0: return 1e9
                        Pavg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / ws
                        corr = (math.exp(-(Pavg - Phi_d(d_g))) - 1) * 100
                        req = REQUIRED[label]
                        err += ((corr - req) / req) ** 2
                    return err
                try:
                    res = minimize_scalar(loss, bounds=(-5, 5), method='bounded')
                    if res.fun < best_global[0]:
                        # Compute corrections
                        corrs = {}
                        for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
                            d_g = GENERATIONS[gen]
                            start = d_g + offset - width // 2
                            window = [d for d in range(start, start + width) if d > OBSERVER]
                            weights = [prim_fn(d) ** res.x for d in window]
                            ws = sum(weights)
                            Pavg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / ws
                            corrs[label] = (math.exp(-(Pavg - Phi_d(d_g))) - 1) * 100
                        best_global = (res.fun, width, offset, res.x, corrs)
                except Exception:
                    pass
        joint = math.sqrt(best_global[0])
        global_results.append((joint, prim_name, best_global))
        w, o, p, corrs = best_global[1], best_global[2], best_global[3], best_global[4]
        print(f"  {prim_name:>10} | (w={w},o={o:+d},p={p:+.3f}) | {corrs['tau']:>+9.3f}% | {corrs['mu']:>+9.3f}% | {corrs['e']:>+9.3f}% | {joint:>8.3f}")

    print()
    global_results.sort()
    print("=" * 78)
    print("GLOBAL-PARAM RANKING")
    print("=" * 78)
    print()
    for i, (joint, name, (loss_val, w, o, p, corrs)) in enumerate(global_results[:5]):
        print(f"  {i+1}. X = {name}: width={w}, offset={o:+d}, p={p:+.4f}, joint err = {joint:.4f}")
        for label in ["tau", "mu", "e"]:
            req = REQUIRED[label]
            corr = corrs[label]
            err = abs((corr - req) / req)
            print(f"     {label}: corr = {corr:+.4f}% vs req {req:+.2f}%, rel err = {err*100:.2f}%")
        print()


if __name__ == "__main__":
    main()
