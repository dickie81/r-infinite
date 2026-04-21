#!/usr/bin/env python3
"""
Compute the cumulative geometric decoherence over the full cascade descent.

Three computations:
1. Per-step overlap deficit 1 - C²_{d,d+1} from exact Beta functions
2. Cumulative sum over full descent d=5 to d=217
3. Eigenvalue deficit for the full 213-layer path
4. Comparison to 1/(8d²) asymptotic

The overlap deficit at each step IS the decoherence: it measures the fraction
of the cascade integrand's content that changes when descending one level.
"""

import numpy as np
from scipy.special import beta as B_func
from scipy.special import gammaln


def C_adj(d):
    """Exact correlation between adjacent layer integrands d and d+1.

    C_{d,d+1} = B(1/2, (d+d+1)/2 + 1) / sqrt(B(1/2, d+1) * B(1/2, d+2))
              = B(1/2, d + 3/2) / sqrt(B(1/2, d+1) * B(1/2, d+2))
    """
    G_dd = B_func(0.5, d + 1.0)
    G_d1d1 = B_func(0.5, d + 2.0)
    G_dd1 = B_func(0.5, d + 1.5)
    return G_dd1 / np.sqrt(G_dd * G_d1d1)


def overlap_deficit(d):
    """1 - C²_{d,d+1}: the per-step decoherence."""
    c = C_adj(d)
    return 1.0 - c * c


def R_eff(d):
    """Compactification radius at dimension d."""
    return 1.0 / np.sqrt(d + 3)


print("=" * 72)
print("CASCADE GEOMETRIC DECOHERENCE — FULL COMPUTATION")
print("=" * 72)

# ──────────────────────────────────────────────────────────────────────
# 1. Per-step overlap deficit
# ──────────────────────────────────────────────────────────────────────
print("\n1. PER-STEP OVERLAP DEFICIT (1 - C²)")
print("-" * 60)
print(f"{'d':>5}  {'1-C² (exact)':>14}  {'1/(8d²)':>14}  {'ratio':>8}  {'R_eff⁴/8':>12}")
print("-" * 60)

deficits = {}
for d in [4, 5, 6, 7, 10, 12, 13, 19, 50, 100, 217]:
    od = overlap_deficit(d)
    asymp = 1.0 / (8.0 * d * d)
    r4 = R_eff(d)**4 / 8.0
    deficits[d] = od
    print(f"{d:>5}  {od:>14.8f}  {asymp:>14.8f}  {od/asymp:>8.4f}  {r4:>12.8f}")

# ──────────────────────────────────────────────────────────────────────
# 2. Cumulative sum over full descent
# ──────────────────────────────────────────────────────────────────────
print("\n\n2. CUMULATIVE DECOHERENCE OVER CASCADE DESCENT")
print("-" * 60)

# Sum of adjacent overlap deficits from d_start to d_end-1
# (each step goes from d to d-1, so integrating out direction at d)
paths = [
    ("d=5 to d=12 (n=8)", 5, 12),
    ("d=5 to d=19 (to d₁)", 5, 19),
    ("d=5 to d=50", 5, 50),
    ("d=5 to d=100", 5, 100),
    ("d=5 to d=217 (full)", 5, 217),
    ("d=4 to d=217 (with obs)", 4, 217),
]

for label, d_start, d_end in paths:
    cum = sum(overlap_deficit(d) for d in range(d_start, d_end))
    n_steps = d_end - d_start
    print(f"  {label:>30s}: Σ(1-C²) = {cum:.6f}  ({cum*100:.3f}%)  [{n_steps} steps]")

# ──────────────────────────────────────────────────────────────────────
# 3. Detailed cumulative profile
# ──────────────────────────────────────────────────────────────────────
print("\n\n3. CUMULATIVE DECOHERENCE PROFILE")
print("-" * 60)
print(f"{'d_end':>6}  {'Σ(1-C²) from d=5':>18}  {'% of total':>12}  {'1-Σ (coherence)':>16}")
print("-" * 60)

total_full = sum(overlap_deficit(d) for d in range(5, 217))
cumulative = 0.0
checkpoints = [6, 7, 8, 10, 12, 13, 14, 19, 21, 30, 50, 100, 150, 200, 217]

for d in range(5, 217):
    cumulative += overlap_deficit(d)
    if d + 1 in checkpoints:
        pct = 100.0 * cumulative / total_full
        print(f"{d+1:>6}  {cumulative:>18.8f}  {pct:>11.2f}%  {1-cumulative:>16.8f}")

print(f"\n  Total Σ(1-C²) from d=5 to d=216: {total_full:.8f}")
print(f"  Total as percentage: {total_full*100:.4f}%")
print(f"  Residual coherence: {1-total_full:.8f} = {(1-total_full)*100:.4f}%")

# ──────────────────────────────────────────────────────────────────────
# 4. Comparison: exact vs asymptotic 1/(8d²)
# ──────────────────────────────────────────────────────────────────────
print("\n\n4. ASYMPTOTIC COMPARISON")
print("-" * 60)

exact_sum = sum(overlap_deficit(d) for d in range(5, 217))
asymp_sum = sum(1.0/(8.0*d*d) for d in range(5, 217))
print(f"  Exact Σ(1-C²):     {exact_sum:.8f}")
print(f"  Asymptotic Σ1/(8d²): {asymp_sum:.8f}")
print(f"  Ratio:               {exact_sum/asymp_sum:.6f}")

# Analytic asymptotic: (1/8)(π²/6 - Σ_{d=1}^{4} 1/d²)
partial = sum(1.0/d**2 for d in range(1, 5))
analytic = (np.pi**2/6.0 - partial) / 8.0
print(f"  Analytic (1/8)(π²/6 - H₄²): {analytic:.8f}")

# ──────────────────────────────────────────────────────────────────────
# 5. Full Gram eigenvalue computation for the complete path
# ──────────────────────────────────────────────────────────────────────
print("\n\n5. GRAM EIGENVALUE STRUCTURE")
print("-" * 60)

def gram_entry(d_i, d_j):
    """G_{ij} = B(1/2, (d_i+d_j)/2 + 1)"""
    return B_func(0.5, (d_i + d_j) / 2.0 + 1.0)

def correlation_entry(d_i, d_j):
    """C_{ij} = G_{ij} / sqrt(G_{ii} G_{jj})"""
    return gram_entry(d_i, d_j) / np.sqrt(gram_entry(d_i, d_i) * gram_entry(d_j, d_j))

# Short paths first (these are tractable with numpy)
for label, dims in [
    ("d=5-12 (n=8)", list(range(5, 13))),
    ("d=5-19 (n=15)", list(range(5, 20))),
    ("d=5-30 (n=26)", list(range(5, 31))),
]:
    n = len(dims)
    C = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            C[i, j] = correlation_entry(dims[i], dims[j])

    eigenvalues = np.sort(np.linalg.eigvalsh(C))[::-1]
    eps = 1.0 - eigenvalues[0] / n

    print(f"\n  {label}:")
    print(f"    λ₁/n = {eigenvalues[0]/n:.8f},  ε = {eps:.6f} ({eps*100:.3f}%)")
    print(f"    λ₂/n = {eigenvalues[1]/n:.8f}")
    if n > 2:
        print(f"    λ₃/n = {eigenvalues[2]/n:.8f}")

    # Perturbation theory check
    eps_pert = 2.0 / (n * n) * sum(1 - C[i, j] for i in range(n) for j in range(i + 1, n))
    print(f"    ε (perturbation): {eps_pert:.6f}")

# ──────────────────────────────────────────────────────────────────────
# 6. Full path d=5-217 (n=213) — perturbation theory only
# ──────────────────────────────────────────────────────────────────────
print("\n\n6. FULL PATH d=5-217 (n=213)")
print("-" * 60)
print("  (Full eigenvalue computation for 213×213 matrix)")

dims_full = list(range(5, 218))
n_full = len(dims_full)
C_full = np.zeros((n_full, n_full))
for i in range(n_full):
    for j in range(i, n_full):
        c = correlation_entry(dims_full[i], dims_full[j])
        C_full[i, j] = c
        C_full[j, i] = c

eigenvalues_full = np.sort(np.linalg.eigvalsh(C_full))[::-1]
eps_full = 1.0 - eigenvalues_full[0] / n_full

print(f"  λ₁ = {eigenvalues_full[0]:.6f},  λ₁/n = {eigenvalues_full[0]/n_full:.8f}")
print(f"  ε = 1 - λ₁/n = {eps_full:.8f} ({eps_full*100:.4f}%)")
print(f"  λ₂ = {eigenvalues_full[1]:.6f},  λ₂/n = {eigenvalues_full[1]/n_full:.8f}")
print(f"  λ₃ = {eigenvalues_full[2]:.6f},  λ₃/n = {eigenvalues_full[2]/n_full:.8f}")
print(f"  λ₄ = {eigenvalues_full[3]:.6f},  λ₄/n = {eigenvalues_full[3]/n_full:.8f}")
print(f"  Σλ = {sum(eigenvalues_full):.6f}  (should be {n_full})")

# Adjacent sum
adj_sum = sum(overlap_deficit(d) for d in range(5, 217))
print(f"\n  Σ(1-C²_adj) = {adj_sum:.8f}")
print(f"  ε (eigenvalue) = {eps_full:.8f}")
print(f"  Ratio Σ/ε = {adj_sum/eps_full:.4f}")

# ──────────────────────────────────────────────────────────────────────
# 7. Decoherence factor for specific angular separations
# ──────────────────────────────────────────────────────────────────────
print("\n\n7. DECOHERENCE FACTOR FOR PHYSICAL SEPARATIONS")
print("-" * 60)
print("  Using D = exp(-Δθ² × Σ(d+3)/4) for democratic separation")
print("  (separation distributed equally among all 217 directions)")

# Weighted sum for democratic case
weighted_sum = sum((d + 3.0) / (4.0 * 217.0) for d in range(5, 218))
print(f"\n  Weighted decoherence rate = Σ(d+3)/(4×217) = {weighted_sum:.4f}")

for delta_theta_deg in [0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 30.0, 90.0]:
    delta_theta = np.radians(delta_theta_deg)
    D = np.exp(-delta_theta**2 * weighted_sum)
    print(f"  Δθ = {delta_theta_deg:>5.1f}°: D = {D:.6f}  (coherence {D*100:.2f}%)")

# ──────────────────────────────────────────────────────────────────────
# 8. Key result: what fraction of coherence survives the full descent?
# ──────────────────────────────────────────────────────────────────────
print("\n\n8. KEY RESULT: COHERENCE SURVIVAL")
print("=" * 60)
print(f"  Total adjacent overlap deficit:  {adj_sum:.6f}  ({adj_sum*100:.3f}%)")
print(f"  Eigenvalue deficit (full path):  {eps_full:.6f}  ({eps_full*100:.3f}%)")
print(f"  Dominant eigenvalue λ₁/n:        {eigenvalues_full[0]/n_full:.6f}")
print(f"  Cascade coherence:               {1-eps_full:.6f}  ({(1-eps_full)*100:.3f}%)")
print(f"\n  The cascade retains {(1-eps_full)*100:.2f}% coherence over 213 steps.")
print(f"  The 'lost' {eps_full*100:.2f}% is the inter-layer coupling that")
print(f"  drives the descent corrections in the Part 0 Supplement.")
print(f"\n  Per-step decoherence at observer (d=4): {overlap_deficit(4):.6f}")
print(f"  Per-step decoherence at d₁=19:          {overlap_deficit(19):.6f}")
print(f"  Per-step decoherence at d₂=217:         {overlap_deficit(217):.8f}")
