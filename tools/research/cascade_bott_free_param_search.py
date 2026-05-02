#!/usr/bin/env python3
"""
Free-parameter weight search for Bott averaging: let weights float over a
parametric family w(d) = Omega(d)^a * R(d)^b * N(d)^c.

Strategy:
  - Single GLOBAL weight function (one rule for all generations)
  - Use structural-hybrid window (forward-2 growth, centered-3 descent)
  - Optimize (a, b, c) to minimize joint residual error
  - Check if optimal (a, b, c) lands at integer / cascade-meaningful values

If optimal (a, b, c) match specific cascade primitives, this could be a
parameter-free closure (the form is fixed by cascade structure, only the
exponents are continuous).
"""

from __future__ import annotations
import math
from scipy.special import digamma, gamma
from scipy.optimize import minimize


def p_d(d): return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_d(d, d_min=4):
    if d <= d_min: return 0.0
    return sum(p_d(dprime) for dprime in range(d_min + 1, d + 1))


def Omega_d(d): return 2 * math.pi ** (d / 2) / gamma(d / 2)
def R_d(d): return math.exp(math.lgamma(d / 2 + 1) - math.lgamma((d + 3) / 2))
def N_d(d): return math.sqrt(math.pi) * math.exp(math.lgamma((d + 1) / 2) - math.lgamma((d + 2) / 2))


GENERATIONS = {1: 21, 2: 13, 3: 5}
N_D_COUNT = {1: 3, 2: 2, 3: 1}
TWO_SQRT_PI = 2 * math.sqrt(math.pi)
REQUIRED = {"tau": 1.25, "mu": -0.47, "e": -0.58}
OBSERVER = 4


def get_window(d_g):
    """Structural hybrid: forward-2 in growth, centered-3 in descent."""
    if p_d(d_g) < 0:  # growth
        return [d_g, d_g + 1]
    else:  # descent
        return [d_g - 1, d_g, d_g + 1]


def correction(d_g, weight_params):
    """Compute correction in % using parametric weight family.
    weight_params: (a, b, c) for w(d) = Omega(d)^a * R(d)^b * N(d)^c
    """
    a, b, c = weight_params
    window = get_window(d_g)
    weights = [Omega_d(d) ** a * R_d(d) ** b * N_d(d) ** c for d in window]
    wsum = sum(weights)
    Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
    Phi_pt = Phi_d(d_g)
    return (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100


def joint_loss(params):
    """Sum of squared relative errors (to be minimized)."""
    err = 0
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        corr = correction(d_g, params)
        req = REQUIRED[label]
        err += ((corr - req) / req) ** 2
    return err


def main():
    print("=" * 78)
    print("Free-parameter weight search: w(d) = Omega(d)^a * R(d)^b * N(d)^c")
    print("=" * 78)
    print()
    print("Single global weight function for all 3 generations.")
    print("Structural-hybrid window: forward-2 in growth, centered-3 in descent.")
    print("Free parameters: (a, b, c) -- 3 continuous.")
    print()

    # First scan a coarse grid
    print("STEP 1: coarse grid scan over (a, b, c) in [-3, +3]")
    print("-" * 78)
    best = (float('inf'), None, None)
    grid_size = 7
    for ia in range(-3, 4):
        for ib in range(-3, 4):
            for ic in range(-3, 4):
                params = (ia, ib, ic)
                try:
                    loss = joint_loss(params)
                    if loss < best[0]:
                        best = (loss, params, None)
                except Exception:
                    pass
    print(f"  Best integer (a, b, c) = {best[1]}  loss = {best[0]:.4f}")
    a, b, c = best[1]
    print(f"  Corresponds to weight: Omega^{a} * R^{b} * N^{c}")
    print()

    # Numerical minimization
    print("STEP 2: continuous minimization starting from coarse best")
    print("-" * 78)
    result = minimize(joint_loss, x0=list(best[1]), method='Nelder-Mead',
                      options={'xatol': 1e-4, 'fatol': 1e-6})
    a_opt, b_opt, c_opt = result.x
    print(f"  Optimal (a, b, c) = ({a_opt:.4f}, {b_opt:.4f}, {c_opt:.4f})")
    print(f"  Loss = {result.fun:.6f}")
    print(f"  sqrt(loss) = {math.sqrt(result.fun):.4f}  (joint relative error)")
    print()

    # Show predictions at optimum
    print("  Corrections at optimum:")
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        corr = correction(d_g, result.x)
        req = REQUIRED[label]
        print(f"    {label:>5} (d_g={d_g}): {corr:+.4f}%  vs req {req:+.2f}%  rel err {abs((corr-req)/req)*100:.2f}%")
    print()

    # Step 3: 2-parameter restrictions (set c=0)
    print("STEP 3: 2-parameter restriction: w(d) = Omega^a * R^b (c=0)")
    print("-" * 78)
    def loss_2param(p): return joint_loss((p[0], p[1], 0))
    # Coarse scan
    best2 = (float('inf'), None)
    for ia in range(-4, 5):
        for ib in range(-4, 5):
            try:
                loss = loss_2param([ia, ib])
                if loss < best2[0]:
                    best2 = (loss, (ia, ib))
            except Exception:
                pass
    print(f"  Best integer (a, b) = {best2[1]}  loss = {best2[0]:.4f}")
    res2 = minimize(loss_2param, x0=list(best2[1]), method='Nelder-Mead')
    print(f"  Optimal continuous (a, b) = ({res2.x[0]:.4f}, {res2.x[1]:.4f})")
    print(f"  Loss = {res2.fun:.6f}")
    a2, b2 = res2.x
    print(f"  Corrections at optimum:")
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        corr = correction(d_g, (a2, b2, 0))
        req = REQUIRED[label]
        print(f"    {label:>5}: {corr:+.4f}%  vs req {req:+.2f}%  rel err {abs((corr-req)/req)*100:.2f}%")
    print()

    # Step 4: 1-parameter restriction (just Omega^a)
    print("STEP 4: 1-parameter restriction: w(d) = Omega^a (b=c=0)")
    print("-" * 78)
    def loss_1param(p): return joint_loss((p[0], 0, 0))
    best1 = (float('inf'), None)
    for ia in [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6]:
        loss = loss_1param([ia])
        if loss < best1[0]:
            best1 = (loss, ia)
    print(f"  Best integer a = {best1[1]}  loss = {best1[0]:.4f}")
    res1 = minimize(loss_1param, x0=[best1[1]], method='Nelder-Mead')
    print(f"  Optimal continuous a = {res1.x[0]:.4f}")
    print(f"  Loss = {res1.fun:.6f}")
    print(f"  Corrections:")
    for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        corr = correction(d_g, (res1.x[0], 0, 0))
        req = REQUIRED[label]
        print(f"    {label:>5}: {corr:+.4f}%  vs req {req:+.2f}%  rel err {abs((corr-req)/req)*100:.2f}%")
    print()

    # Step 5: scan single-parameter exponents finer
    print("STEP 5: fine scan w(d) = Omega^a, a in [-1, 4]")
    print("-" * 78)
    print(f"  {'a':>6} {'tau':>10} {'mu':>10} {'e':>10} {'joint':>8}")
    for a_step in [int(round(x * 10)) / 10 for x in [-1, -0.5, 0, 0.5, 1, 1.5, 2, 2.5, 3, 3.5, 4]]:
        corrs = {}
        for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
            d_g = GENERATIONS[gen]
            corrs[label] = correction(d_g, (a_step, 0, 0))
        joint = math.sqrt(sum(((corrs[l] - REQUIRED[l]) / REQUIRED[l]) ** 2 for l in REQUIRED))
        print(f"  {a_step:>6.1f} {corrs['tau']:>+9.3f}% {corrs['mu']:>+9.3f}% {corrs['e']:>+9.3f}% {joint:>8.3f}")
    print()

    # Step 6: now FREE the window also, see what window optimum is
    print("STEP 6: free up width and offset for descent gens (per gen)")
    print("-" * 78)
    print("  Use Omega-weight optimum from Step 4 as global weight.")
    a_global = res1.x[0]
    print(f"  Fixed a = {a_global:.4f}")
    print()
    print(f"  For each (mu, e), scan width and offset to find best.  Tau fixed forward [5,6].")
    print()
    print(f"  {'gen':>4} {'best width':>10} {'best offset':>11} {'corr':>10} {'rel err':>10}")
    for gen, label in [(2, "mu"), (1, "e")]:
        d_g = GENERATIONS[gen]
        req = REQUIRED[label]
        best_pg = (float('inf'), None, None, None)
        for width in range(2, 8):
            for offset in [-3, -2, -1, 0, 1, 2]:
                start = d_g + offset - width // 2
                window = [d for d in range(start, start + width) if d > OBSERVER]
                if len(window) < 2:
                    continue
                weights = [Omega_d(d) ** a_global for d in window]
                wsum = sum(weights)
                Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
                corr = (math.exp(-(Phi_avg - Phi_d(d_g))) - 1) * 100
                rel_err = abs((corr - req) / req)
                if rel_err < best_pg[0]:
                    best_pg = (rel_err, width, offset, corr)
        print(f"  {label:>4} {best_pg[1]:>10} {best_pg[2]:>+11d} {best_pg[3]:>+9.3f}% {best_pg[0]*100:>9.2f}%")
    print()


def extended_scan():
    """Test 1-parameter family w(d) = X(d)^p for X in {R, Omega, N, alpha, p}.
    For each X, find optimal p and check residuals.
    """
    print("=" * 78)
    print("STEP 7: 1-parameter X^p families, optimized p per primitive X")
    print("=" * 78)
    print()

    primitives = {
        "R": R_d,
        "Omega": Omega_d,
        "N": N_d,
        "p": lambda d: max(p_d(d) + 1, 0.01),  # shift to positive
        "alpha": lambda d: R_d(d) ** 2 / 4,
        "Phi+1": lambda d: Phi_d(d) + 2,  # shift to positive
        "1/d": lambda d: 1.0 / d,
        "d": lambda d: float(d),
    }

    print(f"  {'X':>10} {'optimal p':>11} {'tau err':>10} {'mu err':>10} {'e err':>10} {'joint':>8}")
    for name, prim_fn in primitives.items():
        def loss(p):
            err = 0
            for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
                d_g = GENERATIONS[gen]
                window = get_window(d_g)
                weights = [prim_fn(d) ** p[0] for d in window]
                wsum = sum(weights)
                Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
                corr = (math.exp(-(Phi_avg - Phi_d(d_g))) - 1) * 100
                req = REQUIRED[label]
                err += ((corr - req) / req) ** 2
            return err

        # Coarse scan first
        best_p = (float('inf'), None)
        for p in [-3, -2.5, -2, -1.5, -1, -0.5, 0, 0.5, 1, 1.5, 2, 2.5, 3, 4, 5]:
            try:
                l = loss([p])
                if l < best_p[0]:
                    best_p = (l, p)
            except (OverflowError, ValueError):
                pass

        # Refine
        try:
            res = minimize(loss, x0=[best_p[1]], method='Nelder-Mead', options={'xatol': 1e-5})
            opt_p = res.x[0]
            opt_loss = res.fun
        except Exception:
            opt_p = best_p[1]
            opt_loss = best_p[0]

        # Compute corrections at optimum
        corrs = {}
        for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
            d_g = GENERATIONS[gen]
            window = get_window(d_g)
            weights = [prim_fn(d) ** opt_p for d in window]
            wsum = sum(weights)
            Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
            corrs[label] = (math.exp(-(Phi_avg - Phi_d(d_g))) - 1) * 100
        errs = [abs((corrs[l] - REQUIRED[l]) / REQUIRED[l]) * 100 for l in ["tau", "mu", "e"]]
        joint = math.sqrt(sum((errs[i] / 100) ** 2 for i in range(3)))
        print(f"  {name:>10} {opt_p:>11.4f} {errs[0]:>9.2f}% {errs[1]:>9.2f}% {errs[2]:>9.2f}% {joint:>8.4f}")
    print()

    # Special: check if p ≈ 1.23 has cascade meaning
    print("=" * 78)
    print("STEP 8: structural interpretation of optimal R^p (p ≈ 1.23)")
    print("=" * 78)
    print()
    print("  Test specific cascade-meaningful candidate exponents for R:")
    print()
    candidates = [
        ("1.0 (pure R)", 1.0),
        ("5/4 (=1.25)", 1.25),
        ("4/3 (≈1.33)", 4/3),
        ("12/π² (≈1.215)", 12 / math.pi ** 2),
        ("π/e (≈1.156)", math.pi / math.e),
        ("ln(π)/(ln(2)) (≈1.652)", math.log(math.pi) / math.log(2)),
        ("3/(2+√π) (≈0.797)", 3 / (2 + math.sqrt(math.pi))),
        ("(2π)/(2π-1) (≈1.190)", (2 * math.pi) / (2 * math.pi - 1)),
        ("optimal continuous", 1.229),
    ]
    print(f"  {'candidate':>30} {'p value':>10} {'tau err':>10} {'mu err':>10} {'e err':>10} {'joint':>8}")
    for name, p in candidates:
        corrs = {}
        for gen, label in [(3, "tau"), (2, "mu"), (1, "e")]:
            d_g = GENERATIONS[gen]
            window = get_window(d_g)
            weights = [R_d(d) ** p for d in window]
            wsum = sum(weights)
            Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
            corrs[label] = (math.exp(-(Phi_avg - Phi_d(d_g))) - 1) * 100
        errs = [abs((corrs[l] - REQUIRED[l]) / REQUIRED[l]) * 100 for l in ["tau", "mu", "e"]]
        joint = math.sqrt(sum((e / 100) ** 2 for e in errs))
        print(f"  {name:>30} {p:>10.4f} {errs[0]:>9.2f}% {errs[1]:>9.2f}% {errs[2]:>9.2f}% {joint:>8.4f}")
    print()


if __name__ == "__main__":
    main()
    extended_scan()
