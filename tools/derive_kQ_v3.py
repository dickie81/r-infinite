#!/usr/bin/env python3
"""
Derive the second-order (observer-dependent) correction to k_Q.

First-order (Theorem 15.9): delta_Q/Q_0 = sum_adj(1 - C^2) [universal]

Second-order hypothesis: the observable's non-uniform sensitivity profile
projects onto the subdominant eigenvector v_2, adding a correction
proportional to (alpha_2/alpha_1)^2 * lambda_2.

For a uniform sensitivity, alpha_2 = 0 and the first-order formula is exact.
For a non-uniform sensitivity, the correction is enhanced.

The complete formula would be:
  delta_Q/Q_0 = sum_adj(1-C^2) * [1 + eta]

where eta is the second-order observer-dependent factor.
"""

import numpy as np
from scipy.special import beta, psi as digamma

pi = np.pi


def correlation_matrix(dims):
    n = len(dims)
    C = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            G_ij = beta(0.5, (dims[i] + dims[j]) / 2.0 + 1.0)
            G_ii = beta(0.5, dims[i] + 1.0)
            G_jj = beta(0.5, dims[j] + 1.0)
            C[i, j] = G_ij / np.sqrt(G_ii * G_jj)
    return C


def overlap_deficit_sum(dims):
    total = 0.0
    for i in range(len(dims) - 1):
        d = dims[i]
        G_dd = beta(0.5, d + 1.0)
        G_d1d1 = beta(0.5, d + 2.0)
        G_dd1 = beta(0.5, (2*d + 1)/2.0 + 1.0)
        C_adj = G_dd1 / np.sqrt(G_dd * G_d1d1)
        total += 1.0 - C_adj**2
    return total


def sensitivity_p(dims):
    """p(d) = (1/2)*psi((d+1)/2) - (1/2)*ln(pi)"""
    return np.array([0.5 * digamma((d+1)/2.0) - 0.5*np.log(pi) for d in dims])


# === Test cases ===
cases = [
    ("alpha_s",    list(range(5, 13)),  0.1159,  0.1179,  sensitivity_p),
    ("ell_A",      list(range(5, 13)),  297.6,   301.6,   None),  # uniform
    ("m_tau/m_mu", list(range(6, 14)),  16.53,   16.82,   sensitivity_p),
]


print("=" * 80)
print("SECOND-ORDER (OBSERVER-DEPENDENT) CORRECTION")
print("=" * 80)

for name, dims, Q0, Q_obs, sens_fn in cases:
    n = len(dims)
    C = correlation_matrix(dims)

    # Eigendecomposition
    eigenvalues, eigenvectors = np.linalg.eigh(C)
    idx = np.argsort(eigenvalues)[::-1]
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]

    lambda_1 = eigenvalues[0]
    lambda_2 = eigenvalues[1]
    eps = 1.0 - lambda_1 / n

    v_1 = eigenvectors[:, 0]
    v_2 = eigenvectors[:, 1]
    if v_2[-1] < 0:
        v_2 = -v_2

    u = np.ones(n) / np.sqrt(n)

    # Sensitivity profile
    if sens_fn is not None:
        w = sens_fn(dims)
    else:
        w = np.ones(n)  # uniform for ell_A

    w_norm = w / np.linalg.norm(w)

    # Projections
    alpha_1 = np.dot(w_norm, v_1)
    alpha_2 = np.dot(w_norm, v_2)
    alpha_u = np.dot(w_norm, u)

    # Observed correction
    delta_obs = Q_obs / Q0 - 1.0
    sum_adj = overlap_deficit_sum(dims)
    ratio = delta_obs / sum_adj  # should be 1 + eta

    print(f"\n--- {name} (d={dims[0]}--{dims[-1]}) ---")
    print(f"  lambda_1 = {lambda_1:.6f}, lambda_2 = {lambda_2:.6f}")
    print(f"  epsilon = {eps:.6f}")
    print(f"  sum_adj(1-C^2) = {sum_adj:.6f}")
    print(f"  delta_obs = {delta_obs:.6f}")
    print(f"  Ratio (= 1 + eta) = {ratio:.4f}")
    print(f"  eta (observed) = {ratio - 1:.4f}")
    print(f"  alpha_1 = {alpha_1:.5f}, alpha_2 = {alpha_2:.5f}")
    print(f"  alpha_2/alpha_1 = {alpha_2/alpha_1:.5f}")
    print(f"  (alpha_2/alpha_1)^2 = {(alpha_2/alpha_1)**2:.5f}")
    print(f"  lambda_2/lambda_1 = {lambda_2/lambda_1:.6f}")

    # Test various formulas for eta
    formulas = {
        "(a2/a1)^2": (alpha_2/alpha_1)**2,
        "(a2/a1)^2 * lam2/lam1": (alpha_2/alpha_1)**2 * lambda_2/lambda_1,
        "(a2/a1)^2 * n*lam2/lam1": (alpha_2/alpha_1)**2 * n*lambda_2/lambda_1,
        "(a2/au)^2 * lam2/lam1": (alpha_2/alpha_u)**2 * lambda_2/lambda_1 if abs(alpha_u) > 1e-10 else 0,
        "a2^2 * lam2 / (a1^2 * lam1)": alpha_2**2 * lambda_2 / (alpha_1**2 * lambda_1),
        "sum(w_i^2 * v2_i^2) * lam2": np.sum(w_norm**2 * v_2**2) * lambda_2,
    }

    print(f"\n  {'Formula':<40s}  {'Predicted eta':>13s}  {'Observed eta':>12s}  {'Dev':>8s}")
    print(f"  {'-'*78}")
    for fname, fval in formulas.items():
        dev = fval - (ratio - 1)
        print(f"  {fname:<40s}  {fval:13.5f}  {ratio-1:12.5f}  {dev:+8.5f}")


# === The formula that works? ===
print(f"\n{'='*80}")
print("TESTING: eta = (alpha_2/alpha_1)^2 * lambda_2 / eps")
print(f"{'='*80}")

print(f"\n{'Observable':<14s}  {'eta_pred':>10s}  {'eta_obs':>10s}  {'Dev':>8s}  "
      f"{'Q_corr':>10s}  {'Q_obs':>10s}  {'Final dev':>10s}")
print("-" * 80)

for name, dims, Q0, Q_obs, sens_fn in cases:
    n = len(dims)
    C = correlation_matrix(dims)
    eigenvalues, eigenvectors = np.linalg.eigh(C)
    idx = np.argsort(eigenvalues)[::-1]
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]

    lambda_1, lambda_2 = eigenvalues[0], eigenvalues[1]
    eps = 1.0 - lambda_1/n
    v_1, v_2 = eigenvectors[:, 0], eigenvectors[:, 1]

    if sens_fn is not None:
        w = sens_fn(dims)
    else:
        w = np.ones(n)
    w_norm = w / np.linalg.norm(w)

    alpha_1 = np.dot(w_norm, v_1)
    alpha_2 = np.dot(w_norm, v_2)

    sum_adj = overlap_deficit_sum(dims)
    delta_obs = Q_obs / Q0 - 1.0
    eta_obs = delta_obs / sum_adj - 1.0

    # Test formula
    eta_pred = (alpha_2/alpha_1)**2 * lambda_2 / eps
    Q_corr = Q0 * (1.0 + sum_adj * (1.0 + eta_pred))
    final_dev = (Q_corr - Q_obs) / Q_obs * 100

    print(f"{name:<14s}  {eta_pred:10.5f}  {eta_obs:10.5f}  "
          f"{eta_pred-eta_obs:+8.5f}  {Q_corr:10.4f}  {Q_obs:10.4f}  {final_dev:+9.2f}%")


# === Broader search: try many formulas ===
print(f"\n{'='*80}")
print("SYSTEMATIC FORMULA SEARCH")
print(f"{'='*80}")

# Collect (eta_obs, alpha_1, alpha_2, lambda_1, lambda_2, eps, n) for each case
data = []
for name, dims, Q0, Q_obs, sens_fn in cases:
    n = len(dims)
    C = correlation_matrix(dims)
    eigenvalues, eigenvectors = np.linalg.eigh(C)
    idx = np.argsort(eigenvalues)[::-1]
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]

    lam1, lam2 = eigenvalues[0], eigenvalues[1]
    eps = 1.0 - lam1/n
    v1, v2 = eigenvectors[:, 0], eigenvectors[:, 1]

    if sens_fn is not None:
        w = sens_fn(dims)
    else:
        w = np.ones(n)
    wn = w / np.linalg.norm(w)

    a1 = np.dot(wn, v1)
    a2 = np.dot(wn, v2)

    sum_adj = overlap_deficit_sum(dims)
    delta_obs = Q_obs / Q0 - 1.0
    eta_obs = delta_obs / sum_adj - 1.0

    data.append({
        'name': name, 'n': n, 'a1': a1, 'a2': a2,
        'lam1': lam1, 'lam2': lam2, 'eps': eps,
        'eta_obs': eta_obs, 'sum_adj': sum_adj,
        'delta_obs': delta_obs, 'Q0': Q0, 'Q_obs': Q_obs,
    })

# Try many formulas of the form eta = f(a1, a2, lam1, lam2, eps, n)
formulas = [
    ("(a2/a1)^2", lambda d: (d['a2']/d['a1'])**2),
    ("(a2/a1)^2 * lam2/eps", lambda d: (d['a2']/d['a1'])**2 * d['lam2']/d['eps']),
    ("(a2/a1)^2 * lam2/(n*eps)", lambda d: (d['a2']/d['a1'])**2 * d['lam2']/(d['n']*d['eps'])),
    ("(a2/a1)^2 * lam2/lam1", lambda d: (d['a2']/d['a1'])**2 * d['lam2']/d['lam1']),
    ("a2^2 * lam2", lambda d: d['a2']**2 * d['lam2']),
    ("a2^2 * lam2 / eps", lambda d: d['a2']**2 * d['lam2'] / d['eps']),
    ("a2^2 / a1^2", lambda d: d['a2']**2 / d['a1']**2),
    ("a2^2 * n / a1^2", lambda d: d['a2']**2 * d['n'] / d['a1']**2),
    ("|a2/a1|", lambda d: abs(d['a2']/d['a1'])),
    ("(a2/a1)^2 * 2", lambda d: (d['a2']/d['a1'])**2 * 2),
    ("(a2/a1)^2 * lam2^2/eps^2", lambda d: (d['a2']/d['a1'])**2 * d['lam2']**2/d['eps']**2),
]

print(f"\n{'Formula':<35s}  ", end="")
for d in data:
    print(f"  {d['name']:>12s}", end="")
print(f"  {'RMS':>8s}")
print("-" * 90)

for fname, ffn in formulas:
    vals = [ffn(d) for d in data]
    residuals = [v - d['eta_obs'] for v, d in zip(vals, data)]
    rms = np.sqrt(np.mean(np.array(residuals)**2))
    print(f"{fname:<35s}  ", end="")
    for v, d in zip(vals, data):
        print(f"  {v:12.5f}", end="")
    print(f"  {rms:8.5f}")

print(f"\n{'(observed eta)':<35s}  ", end="")
for d in data:
    print(f"  {d['eta_obs']:12.5f}", end="")
print()

# Best formula? Compute final corrected predictions
print(f"\n{'='*80}")
print("BEST CANDIDATE AND FINAL PREDICTIONS")
print(f"{'='*80}")

# Find the formula with lowest RMS
best_name = None
best_rms = 1e10
best_fn = None
for fname, ffn in formulas:
    vals = [ffn(d) for d in data]
    residuals = [v - d['eta_obs'] for v, d in zip(vals, data)]
    rms = np.sqrt(np.mean(np.array(residuals)**2))
    if rms < best_rms:
        best_rms = rms
        best_name = fname
        best_fn = ffn

print(f"\nBest formula: eta = {best_name} (RMS = {best_rms:.5f})")

print(f"\n{'Observable':<14s}  {'Leading':>10s}  {'1st order':>10s}  "
      f"{'2nd order':>10s}  {'Observed':>10s}  {'Dev(1st)':>9s}  {'Dev(2nd)':>9s}")
print("-" * 80)

for d in data:
    eta = best_fn(d)
    Q_1st = d['Q0'] * (1.0 + d['sum_adj'])
    Q_2nd = d['Q0'] * (1.0 + d['sum_adj'] * (1.0 + eta))
    dev_1st = (Q_1st - d['Q_obs']) / d['Q_obs'] * 100
    dev_2nd = (Q_2nd - d['Q_obs']) / d['Q_obs'] * 100
    print(f"{d['name']:<14s}  {d['Q0']:10.4f}  {Q_1st:10.4f}  "
          f"{Q_2nd:10.4f}  {d['Q_obs']:10.4f}  {dev_1st:+8.2f}%  {dev_2nd:+8.2f}%")
