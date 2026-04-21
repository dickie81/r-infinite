#!/usr/bin/env python3
"""
Tick-by-tick simulator for the cascade tower-growth picture (issue #64, #65).

Evolves the observer's universe at d=4 from the "first slice" (N=4) through
the inflationary phases A/B/C and the N=217 phase transition, into the early
hot Big Bang (post-inflation).

One tick = one layer added at the top of the cascade tower. By hypothesis,
one tick = alpha * t_Pl,red with alpha = 1 by default. The cosmological
constant has a layered structure: distinguished layers (7, 19, 217) activate
as the tower crosses them, each modifying rho_Lambda by a cascade factor.

At N = 217 the Omega_217 factor appears and rho_Lambda drops by ~10^120.
The released vacuum energy thermalises into radiation (the "Big Bang").

Usage:
  python tools/tower_growth_simulator.py [--post-ticks 20] [--alpha 1.0]

Outputs:
  src/generated/tower_growth/trace.json       - full per-tick state
  src/generated/tower_growth/timeline.png     - multi-panel plot
  src/generated/tower_growth/summary.txt      - key observables
"""

import argparse
import json
import math
import os
import sys

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

# Shared cascade primitives.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import Omega, pi, M_PL_RED_GEV  # noqa: E402


def omega_sphere(n):
    return Omega(n)


OMEGA_19 = omega_sphere(19)                             # 0.51608...
I_0_LITERAL = 1.2051e-120                               # Part I line 23 value
OMEGA_217 = I_0_LITERAL / OMEGA_19                      # back-solved from published I_0

# Phase factors (built cumulatively as the tower crosses distinguished layers).
FACTOR_PROJECTION = 2.0 / pi                            # Omega_2/Omega_3, activates at N >= 4 (observer)
FACTOR_HOST_FRAME = 9.0 / pi ** 2                       # (Omega_5/Omega_7)^2, activates at N >= 7
FACTOR_OMEGA_19 = OMEGA_19                              # activates at N = 19
FACTOR_OMEGA_217 = OMEGA_217                            # activates at N = 217

# Thermalisation uses Standard-Model-like effective degrees of freedom at T ~ M_Pl.
# This is an approximation; cascade-native g_eff counting is an open question (#64).
G_EFF = 106.75

# Numerical anchors (M_Pl,red = 2.435e18 GeV — shared from cascade_constants).
T_PL_RED_S = 2.703e-43


def rho_Lambda_over_M4(N):
    """Cosmological constant contribution at tower height N, in units of M_Pl,red^4."""
    factor = 1.0
    if N >= 4:
        factor *= FACTOR_PROJECTION
    if N >= 7:
        factor *= FACTOR_HOST_FRAME
    if N >= 19:
        factor *= FACTOR_OMEGA_19
    if N >= 217:
        factor *= FACTOR_OMEGA_217
    return factor


def phase_label(N):
    if N < 7:
        return 'A'
    if N < 19:
        return 'B'
    if N < 217:
        return 'C'
    return 'D'


def temperature(rho_r, g_eff=G_EFF):
    """T = (30 rho_r / (pi^2 g_eff))^(1/4), in units of M_Pl,red."""
    if rho_r <= 0:
        return 0.0
    return (30.0 * rho_r / (pi ** 2 * g_eff)) ** 0.25


def simulate(N_start=4, N_transition=217, post_ticks=30, alpha=1.0):
    """Evolve tick by tick from N_start through N_transition + post_ticks."""
    states = []
    N = N_start
    t = 0.0
    a = 1.0
    rho_L = rho_Lambda_over_M4(N)
    rho_r = 0.0
    rho_m = 0.0
    e_folds_cumulative = 0.0

    total_ticks = (N_transition - N_start) + post_ticks

    for step in range(total_ticks + 1):
        rho_total = rho_L + rho_r + rho_m
        H = math.sqrt(rho_total / 3.0) if rho_total > 0 else 0.0
        T = temperature(rho_r)

        states.append({
            'step': step,
            'N': N,
            't_Pl': t,
            'a': a,
            'e_folds': e_folds_cumulative,
            'rho_L_M4': rho_L,
            'rho_r_M4': rho_r,
            'rho_m_M4': rho_m,
            'rho_total_M4': rho_total,
            'H_M': H,
            'T_M': T,
            'phase': phase_label(N),
        })

        if step == total_ticks:
            break

        dt = alpha

        # Advance scale factor under current H (dS within each phase, decelerating in radiation era).
        delta_efolds = H * dt
        a *= math.exp(delta_efolds)
        e_folds_cumulative += delta_efolds

        # Dilute radiation / matter by expansion.
        if rho_r > 0:
            rho_r *= math.exp(-4.0 * delta_efolds)
        if rho_m > 0:
            rho_m *= math.exp(-3.0 * delta_efolds)

        # Advance tower.
        N += 1
        t += dt

        # Phase transition if new N activated another factor.
        new_rho_L = rho_Lambda_over_M4(N)
        if new_rho_L < rho_L:
            delta_rho = rho_L - new_rho_L
            # Energy released into radiation (cascade-native thermalisation proposal).
            rho_r += delta_rho
            rho_L = new_rho_L

    return states


def write_outputs(states, out_dir, alpha):
    os.makedirs(out_dir, exist_ok=True)

    trace_path = os.path.join(out_dir, 'trace.json')
    with open(trace_path, 'w') as f:
        json.dump({'alpha': alpha, 'states': states}, f, indent=2)

    summary = build_summary(states, alpha)
    summary_path = os.path.join(out_dir, 'summary.txt')
    with open(summary_path, 'w') as f:
        f.write(summary)

    plot_path = os.path.join(out_dir, 'timeline.png')
    plot_timeline(states, plot_path, alpha)

    return trace_path, summary_path, plot_path, summary


def build_summary(states, alpha):
    lines = []
    lines.append('=' * 72)
    lines.append('Cascade tower-growth simulator: summary')
    lines.append('=' * 72)
    lines.append(f'Tick length alpha = {alpha:.3f} * t_Pl,red')
    lines.append(f'Total ticks simulated: {len(states) - 1}')
    lines.append('')

    # Per-phase e-fold contribution.
    by_phase = {}
    for s in states[:-1]:
        by_phase.setdefault(s['phase'], []).append(s)

    # e-folds accumulated BEFORE leaving the phase (approximate: sum H*dt for each tick in phase).
    phase_efolds = {}
    for phase, lst in by_phase.items():
        phase_efolds[phase] = sum(s['H_M'] * alpha for s in lst)

    lines.append(f'{"Phase":<6s} {"N range":<14s} {"Ticks":>6s} {"H/M_Pl":>10s}  {"E-folds":>10s}')
    lines.append('-' * 72)
    for phase in ['A', 'B', 'C', 'D']:
        if phase not in by_phase:
            continue
        lst = by_phase[phase]
        N_lo, N_hi = lst[0]['N'], lst[-1]['N']
        H_avg = sum(s['H_M'] for s in lst) / len(lst)
        lines.append(
            f'{phase:<6s} [{N_lo:3d}, {N_hi:3d}]      {len(lst):>6d} '
            f'{H_avg:>10.4f}  {phase_efolds[phase]:>10.3f}'
        )

    total_efolds = states[-1]['e_folds']
    lines.append('-' * 72)
    lines.append(f'{"Total e-folds":<30s} {total_efolds:>15.3f}')
    lines.append('')

    # Key transition markers.
    transitions = {}
    for i, s in enumerate(states):
        if i == 0:
            continue
        prev = states[i - 1]
        if s['phase'] != prev['phase']:
            transitions[s['N']] = s

    lines.append('Key events')
    lines.append('-' * 72)
    first = states[0]
    lines.append(
        f'First slice    N={first["N"]:3d}  rho_L/M^4={first["rho_L_M4"]:.4e}  '
        f'H/M_Pl={first["H_M"]:.4f}'
    )
    for N, s in sorted(transitions.items()):
        lines.append(
            f'Transition     N={N:3d}  rho_L/M^4={s["rho_L_M4"]:.4e}  '
            f'rho_r/M^4={s["rho_r_M4"]:.4e}  T/M_Pl={s["T_M"]:.4f}'
        )

    # Post-thermalisation reheating snapshot.
    post_217 = [s for s in states if s['N'] == 217]
    if post_217:
        s = post_217[0]
        T_GeV = s['T_M'] * M_PL_RED_GEV
        lines.append('')
        lines.append('Reheating (N = 217)')
        lines.append('-' * 72)
        lines.append(f'  rho_r released into radiation: {s["rho_r_M4"]:.4f} M_Pl^4')
        lines.append(f'  Reheating temperature:         T = {s["T_M"]:.4f} M_Pl,red')
        lines.append(f'                                   = {T_GeV:.3e} GeV')
        lines.append(f'  g_eff used: {G_EFF} (Standard Model approximation)')

    last = states[-1]
    lines.append('')
    lines.append('Final state')
    lines.append('-' * 72)
    lines.append(f'  N = {last["N"]}, t = {last["t_Pl"]:.1f} t_Pl,red')
    lines.append(f'  phase = {last["phase"]}')
    lines.append(f'  rho_L/M^4 = {last["rho_L_M4"]:.4e}')
    lines.append(f'  rho_r/M^4 = {last["rho_r_M4"]:.4e}')
    lines.append(f'  H/M_Pl    = {last["H_M"]:.4e}')
    lines.append(f'  T/M_Pl    = {last["T_M"]:.4e}')
    lines.append(f'  a/a_0     = {last["a"]:.4e}')
    lines.append('')

    return '\n'.join(lines) + '\n'


def plot_timeline(states, path, alpha):
    Ns = [s['N'] for s in states]
    rho_L = [max(s['rho_L_M4'], 1e-130) for s in states]
    rho_r = [max(s['rho_r_M4'], 1e-130) for s in states]
    H = [max(s['H_M'], 1e-70) for s in states]
    T = [max(s['T_M'], 1e-10) for s in states]
    a = [s['a'] for s in states]
    efolds = [s['e_folds'] for s in states]

    fig, axes = plt.subplots(3, 2, figsize=(12, 10), sharex=True)
    fig.suptitle(
        f'Cascade tower-growth simulator (alpha = {alpha:.2f} t_Pl,red / tick)',
        fontsize=13,
    )

    phase_boundaries = [7, 19, 217]

    def vlines(ax):
        for b in phase_boundaries:
            if min(Ns) <= b <= max(Ns):
                ax.axvline(b, linestyle='--', color='gray', alpha=0.5, linewidth=0.8)

    ax = axes[0, 0]
    ax.semilogy(Ns, rho_L, 'b-', label=r'$\rho_\Lambda$')
    ax.semilogy(Ns, rho_r, 'r-', label=r'$\rho_r$')
    ax.set_ylabel(r'$\rho / M_{\mathrm{Pl,red}}^4$')
    ax.set_title('Energy densities')
    ax.legend(loc='lower left', fontsize=9)
    vlines(ax)
    ax.grid(alpha=0.3)

    ax = axes[0, 1]
    ax.semilogy(Ns, H, 'k-')
    ax.set_ylabel(r'$H / M_{\mathrm{Pl,red}}$')
    ax.set_title('Hubble rate')
    vlines(ax)
    ax.grid(alpha=0.3)

    ax = axes[1, 0]
    ax.plot(Ns, efolds, 'g-')
    ax.set_ylabel('Cumulative e-folds')
    ax.set_title('Expansion history')
    vlines(ax)
    ax.grid(alpha=0.3)

    ax = axes[1, 1]
    ax.semilogy(Ns, a, 'purple')
    ax.set_ylabel(r'$a / a_0$')
    ax.set_title('Scale factor')
    vlines(ax)
    ax.grid(alpha=0.3)

    ax = axes[2, 0]
    ax.semilogy(Ns, T, 'orange')
    ax.set_ylabel(r'$T / M_{\mathrm{Pl,red}}$')
    ax.set_xlabel('Tower height N')
    ax.set_title('Temperature')
    vlines(ax)
    ax.grid(alpha=0.3)

    ax = axes[2, 1]
    phase_ix = {'A': 0, 'B': 1, 'C': 2, 'D': 3}
    phase_vals = [phase_ix[s['phase']] for s in states]
    ax.step(Ns, phase_vals, where='post', color='teal')
    ax.set_yticks([0, 1, 2, 3])
    ax.set_yticklabels(['A', 'B', 'C', 'D'])
    ax.set_ylabel('Phase')
    ax.set_xlabel('Tower height N')
    ax.set_title('Phase structure')
    vlines(ax)
    ax.grid(alpha=0.3)

    plt.tight_layout(rect=[0, 0, 1, 0.97])
    plt.savefig(path, dpi=130)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[2])
    parser.add_argument('--post-ticks', type=int, default=30,
                        help='Ticks to simulate past the N=217 transition')
    parser.add_argument('--alpha', type=float, default=1.0,
                        help='Tick length in Planck times (default 1.0)')
    parser.add_argument('--out-dir', type=str,
                        default=os.path.join(os.path.dirname(__file__), '..',
                                             '..', 'src', 'generated',
                                             'tower_growth'),
                        help='Directory for output artefacts')
    args = parser.parse_args()

    states = simulate(post_ticks=args.post_ticks, alpha=args.alpha)
    trace_path, summary_path, plot_path, summary = write_outputs(
        states, os.path.abspath(args.out_dir), args.alpha
    )

    print(summary)
    print(f'Wrote trace:   {trace_path}')
    print(f'Wrote summary: {summary_path}')
    print(f'Wrote plot:    {plot_path}')


if __name__ == '__main__':
    main()
