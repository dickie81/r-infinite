#!/usr/bin/env python3
"""
Plot DESI DR2 BAO redshift vs distance.

Distance ladders shown:
  - D_M(z): transverse comoving distance [Mpc]
  - D_H(z) = c/H(z): Hubble distance     [Mpc]
  - D_V(z) = (z D_H D_M^2)^{1/3}         [Mpc]

DESI DR2 reports each measurement as a ratio to the sound horizon r_d.
We multiply by r_d (cascade or Planck) to recover absolute Mpc, then
plot redshift on the y-axis and distance on the x-axis with the cascade
and Planck cosmology curves overlaid.

Output: tools/research/desi_redshift_distance.png (and .pdf)
"""

import os
import sys

import numpy as np
import matplotlib.pyplot as plt
from scipy import integrate

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import (  # noqa: E402
    H0, Omega_m, Omega_b, Omega_r, Omega_Lambda, c_km_s,
)

# Cascade cosmology -----------------------------------------------------
H0_cas = H0
Om_cas = Omega_m
Or_cas = Omega_r
OL_cas = Omega_Lambda
Ob_cas = Omega_b

# E&H98 r_d for cascade parameters (matches generate_bao_table.py)
h_cas = H0_cas / 100.0
omega_m_cas = Om_cas * h_cas ** 2
omega_b_cas = Ob_cas * h_cas ** 2
rd_cas = 147.60 * (omega_m_cas / 0.1432) ** (-0.255) \
    * (omega_b_cas / 0.02237) ** (-0.127)

# Planck baseline -------------------------------------------------------
H0_pl = 67.4
Om_pl = 0.315
Or_pl = 9.15e-5
OL_pl = 1.0 - Om_pl - Or_pl
rd_pl = 147.60

# DESI DR2 (z, type, value/r_d, sigma/r_d) ------------------------------
desi_data = [
    (0.295, "D_V",  7.930, 0.150),
    (0.510, "D_M", 13.650, 0.200),
    (0.510, "D_H", 20.890, 0.490),
    (0.706, "D_M", 16.970, 0.240),
    (0.706, "D_H", 20.270, 0.470),
    (0.934, "D_M", 21.790, 0.240),
    (0.934, "D_H", 17.730, 0.300),
    (1.321, "D_M", 27.680, 0.500),
    (1.321, "D_H", 13.850, 0.340),
    (1.484, "D_M", 30.420, 0.660),
    (1.484, "D_H", 13.240, 0.450),
    (2.330, "D_M", 39.200, 0.560),
    (2.330, "D_H",  8.540, 0.140),
]


def cosmology(H0_val, Om, Or, OL):
    def H(z):
        return H0_val * np.sqrt(Or * (1 + z) ** 4 + Om * (1 + z) ** 3 + OL)

    def D_M(z):
        z = np.atleast_1d(z).astype(float)
        out = np.empty_like(z)
        for i, zi in enumerate(z):
            out[i], _ = integrate.quad(lambda zp: c_km_s / H(zp), 0.0, zi)
        return out if out.size > 1 else float(out[0])

    def D_H(z):
        return c_km_s / H(np.asarray(z, dtype=float))

    def D_V(z):
        z = np.asarray(z, dtype=float)
        return (z * D_H(z) * D_M(z) ** 2) ** (1.0 / 3.0)

    return H, D_M, D_H, D_V


_, DM_c, DH_c, DV_c = cosmology(H0_cas, Om_cas, Or_cas, OL_cas)
_, DM_p, DH_p, DV_p = cosmology(H0_pl, Om_pl, Or_pl, OL_pl)


# Convert DESI ratios to Mpc using *cascade* r_d (the cascade's own ruler)
# and store separately for D_M, D_H, D_V channels.
def split_channels(r_d):
    out = {"D_M": [], "D_H": [], "D_V": []}
    for z, typ, ratio, sig in desi_data:
        out[typ].append((z, ratio * r_d, sig * r_d))
    return {k: np.array(v).T for k, v in out.items() if v}


desi_cas = split_channels(rd_cas)
desi_pl = split_channels(rd_pl)

# Plot ------------------------------------------------------------------
z_grid = np.linspace(0.01, 2.5, 200)
DM_curve_c = DM_c(z_grid)
DH_curve_c = DH_c(z_grid)
DV_curve_c = DV_c(z_grid)
DM_curve_p = DM_p(z_grid)
DH_curve_p = DH_p(z_grid)
DV_curve_p = DV_p(z_grid)

fig, ax = plt.subplots(figsize=(8.5, 6.0))

# Cascade curves (solid)
ax.plot(DM_curve_c, z_grid, color="C0", lw=2.0,
        label=r"Cascade $D_M(z)$ ($H_0=66.78$, $\Omega_m=1/\pi$)")
ax.plot(DH_curve_c, z_grid, color="C1", lw=2.0,
        label=r"Cascade $D_H(z)=c/H(z)$")
ax.plot(DV_curve_c, z_grid, color="C2", lw=2.0,
        label=r"Cascade $D_V(z)$")

# Planck curves (dashed)
ax.plot(DM_curve_p, z_grid, color="C0", lw=1.2, ls="--", alpha=0.7,
        label=r"Planck $D_M(z)$ ($H_0=67.4$, $\Omega_m=0.315$)")
ax.plot(DH_curve_p, z_grid, color="C1", lw=1.2, ls="--", alpha=0.7,
        label=r"Planck $D_H(z)$")
ax.plot(DV_curve_p, z_grid, color="C2", lw=1.2, ls="--", alpha=0.7,
        label=r"Planck $D_V(z)$")

# DESI DR2 data, scaled by cascade r_d
for typ, color, marker in [("D_M", "C0", "o"),
                           ("D_H", "C1", "s"),
                           ("D_V", "C2", "^")]:
    if typ not in desi_cas:
        continue
    z_arr, d_arr, e_arr = desi_cas[typ]
    ax.errorbar(d_arr, z_arr, xerr=e_arr,
                fmt=marker, color=color, mfc="white", mec=color,
                ms=7, mew=1.6, elinewidth=1.4, capsize=3,
                label=f"DESI DR2 {typ} (× cascade $r_d$)")

ax.set_xlabel("Distance [Mpc]")
ax.set_ylabel("Redshift $z$")
ax.set_title("DESI DR2 BAO: redshift vs distance "
             "(cascade vs Planck $\\Lambda$CDM)")
ax.set_xlim(0, 7500)
ax.set_ylim(0, 2.5)
ax.grid(True, alpha=0.3)
ax.legend(loc="lower right", fontsize=8, framealpha=0.9)

fig.tight_layout()

out_dir = os.path.dirname(os.path.abspath(__file__))
png_path = os.path.join(out_dir, "desi_redshift_distance.png")
pdf_path = os.path.join(out_dir, "desi_redshift_distance.pdf")
fig.savefig(png_path, dpi=150)
fig.savefig(pdf_path)

print(f"Cascade r_d = {rd_cas:.3f} Mpc")
print(f"Planck  r_d = {rd_pl:.3f} Mpc")
print("DESI DR2 points (cascade-scaled):")
for typ in ("D_M", "D_H", "D_V"):
    if typ not in desi_cas:
        continue
    z_arr, d_arr, e_arr = desi_cas[typ]
    for z, d, e in zip(z_arr, d_arr, e_arr):
        print(f"  z = {z:.3f}   {typ} = {d:7.1f} +- {e:5.1f} Mpc")
print(f"\nWrote {png_path}")
print(f"Wrote {pdf_path}")
