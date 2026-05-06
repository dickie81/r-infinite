"""
Plot the surface area Omega_d = 2 pi^((d+1)/2) / Gamma((d+1)/2)
of the unit d-sphere S^d, for d = 0, 1, ..., 217.

Convention follows tools/cascade_constants.py: d is the manifold
dimension of S^d (so S^0 = two points, S^2 = ordinary 2-sphere).

Why d = 0..217?
  - The peak of Omega_d (over integer d) sits at d = 6.
  - d = 217 is the cascade-invariant frontier where the running
    product Phi(d) reaches the ~10^-120 cosmological-constant scale
    (Part 0, Part I).  Plotting up to d = 217 shows that Omega_d
    itself crosses 10^-120 at the same dimensional scale.

Output:
  src/generated/sphere_area/sphere_surface_area.png
  src/generated/sphere_area/values.txt
"""

import os
import sys

# Allow running from anywhere within the repo.
_HERE = os.path.dirname(os.path.abspath(__file__))
_TOOLS = os.path.dirname(_HERE)
_REPO = os.path.dirname(_TOOLS)
sys.path.insert(0, _TOOLS)

import matplotlib.pyplot as plt
from mpmath import log10, mp

from cascade_constants import mp as cmp  # arbitrary-precision backend

mp.dps = 80

D_MAX = 217
ds = list(range(0, D_MAX + 1))

omega = [cmp.Omega(d) for d in ds]
log_omega = [float(log10(v)) for v in omega]
omega_float = [float(v) for v in omega]

peak_d = max(ds, key=lambda d: omega_float[d])

out_dir = os.path.join(_REPO, "src", "generated", "sphere_area")
os.makedirs(out_dir, exist_ok=True)

values_path = os.path.join(out_dir, "values.txt")
with open(values_path, "w") as f:
    f.write("# Surface area of S^d for d = 0..{}\n".format(D_MAX))
    f.write("# Omega_d = 2 pi^((d+1)/2) / Gamma((d+1)/2)\n")
    f.write("# columns: d, Omega_d, log10(Omega_d)\n")
    for d, v, lv in zip(ds, omega, log_omega):
        f.write("{:3d}  {:.12e}  {:+.6f}\n".format(d, float(v), lv))

fig, axes = plt.subplots(1, 2, figsize=(13, 5))

ax = axes[0]
ax.plot(ds, omega_float, lw=1.4, color="#1f77b4")
ax.axvline(peak_d, color="grey", ls="--", lw=0.8, alpha=0.7,
           label="peak at $d = {}$".format(peak_d))
ax.set_xlabel("sphere dimension $d$ (manifold dim of $S^d$)")
ax.set_ylabel(r"$\Omega_d = 2\pi^{(d+1)/2}/\Gamma((d+1)/2)$")
ax.set_title("Linear scale (only the early bump is visible)")
ax.set_xlim(0, D_MAX)
ax.legend()
ax.grid(alpha=0.3)

ax = axes[1]
ax.plot(ds, log_omega, lw=1.4, color="#d62728")
ax.axvline(peak_d, color="grey", ls="--", lw=0.8, alpha=0.7,
           label="peak at $d = {}$".format(peak_d))
for d_mark in (4, 7, 12, 24, 56, D_MAX):
    if d_mark <= D_MAX:
        ax.plot(d_mark, log_omega[d_mark], "ko", ms=4)
        ax.annotate("d={}".format(d_mark),
                    (d_mark, log_omega[d_mark]),
                    xytext=(4, 4), textcoords="offset points", fontsize=8)
ax.set_xlabel("sphere dimension $d$")
ax.set_ylabel(r"$\log_{10}\,\Omega_d$")
ax.set_title(r"Log scale: super-exponential decay from $\Gamma(d/2)$")
ax.set_xlim(0, D_MAX)
ax.legend()
ax.grid(alpha=0.3)

fig.suptitle(r"Surface area of $S^d$ for $d = 0,\ldots," + str(D_MAX) + r"$",
             y=1.02)
fig.tight_layout()

png_path = os.path.join(out_dir, "sphere_surface_area.png")
fig.savefig(png_path, dpi=140, bbox_inches="tight")

print("peak at d = {}: Omega = {:.6f}".format(peak_d, omega_float[peak_d]))
print("Omega(0)   = {:.6e}".format(omega_float[0]))
print("Omega(50)  = {:.6e}".format(omega_float[50]))
print("Omega(100) = {:.6e}".format(omega_float[100]))
print("Omega({})  = {:.6e}".format(D_MAX, omega_float[D_MAX]))
print("\nwrote:")
print("  " + png_path)
print("  " + values_path)
