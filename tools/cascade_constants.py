"""
Cascade constants — single source of truth for numerical primitives
reused across the tools in this folder.

Every quantity here is a function of the Gamma function and pi
(Part 0, Theorem 3.1: pi is the cascade's unique dimensionless constant).
No physical input beyond the identification hypothesis.

Two numerical backends are exposed:
    - scipy / numpy  (default; double precision)
    - mpmath         (arbitrary precision, opt-in)

Both produce identical values at double precision.  Tools that require
arbitrary precision (e.g. verify_continuous_boundary) should import from
the `mp` namespace below; all other tools use the plain numpy-backed
functions.

Usage
-----
    from cascade_constants import R, alpha, Omega, N_lapse, p
    from cascade_constants import D_V, D_0, D_GW, D_1, D_2
    from cascade_constants import Omega_m, Omega_b, Omega_r, Omega_Lambda, H0
    from cascade_constants import mp   # arbitrary-precision analogues

When a script is moved into a subfolder of tools/, add this to the top:

    import sys, os
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from cascade_constants import R, alpha, ...
"""

import math

import numpy as np
from scipy.special import beta as _beta, gamma as _gamma, psi as _digamma


# ──────────────────────────────────────────────────────────────────────
# Gamma-function primitives  (numpy / scipy backend)
# ──────────────────────────────────────────────────────────────────────

pi = math.pi


def R(d):
    """Slicing recurrence coefficient R(d) = Gamma((d+1)/2) / Gamma((d+2)/2).

    Part 0 §3.  Appears in every closure in the series.
    """
    return _gamma((d + 1) / 2.0) / _gamma((d + 2) / 2.0)


def alpha(d):
    """Cascade gauge coupling at layer d: alpha(d) = R(d)^2 / 4.

    Part IVa §4 (gauge coupling as N(d)^2 / Omega_2 = R(d)^2 / 4).
    """
    return R(d) ** 2 / 4.0


def Omega(d):
    """Surface area of S^d: Omega_d = 2 pi^((d+1)/2) / Gamma((d+1)/2)."""
    return 2.0 * pi ** ((d + 1) / 2.0) / _gamma((d + 1) / 2.0)


def V_ball(d):
    """Volume of unit d-ball: V_d = pi^(d/2) / Gamma(d/2 + 1)."""
    return pi ** (d / 2.0) / _gamma(d / 2.0 + 1.0)


def N_lapse(d):
    """Cascade slicing integrand at layer d: N_lapse(d) = integral_{-1}^{1}
    (1 - x^2)^{d/2} dx = B(1/2, d/2 + 1) = sqrt(pi) * R(d+1).

    CONVENTION NOTE.  Two N-conventions appear in the papers; they are
    related by a one-step shift.

      (a) "Integrand-at-layer-d" convention (this function).
          N_lapse(d) = int (1-x^2)^{d/2} dx = V_{d+1}/V_d.
          Numerically N_lapse(0) = 2, N_lapse(4) = 16/15.
          Used in Part IVb Corollary 2.3 (N(0) = 2) and in the
          derivation derive_2sqrtpi_no_dirac.py.

      (b) "V_d/V_{d-1}" convention (paper's majority usage).
          N_paper(d) = sqrt(pi) * R(d) = int (1-x^2)^{(d-1)/2} dx.
          Numerically N_paper(1) = 2, N_paper(4) = 3 pi / 8.
          Used in Part 0 §3, Part I, Part II §7.2, Part IVb Theorem 2.2
          ("the cascade lapse at layer d factorises as
          N(d) = sqrt(pi) R(d)"), Part V.

    Convention (a) is the code default.  Convention (b) can be obtained
    as `sqrt(pi) * R(d)`.  The alpha(d) function below uses the SAME-INDEX
    identity alpha(d) = (sqrt(pi) R(d))^2 / (4 pi) = R(d)^2 / 4, i.e.,
    convention (b).  Therefore alpha(d) is NOT equal to
    N_lapse(d)^2 / (4 pi) at the same index d; it equals
    N_lapse(d-1)^2 / (4 pi) = (sqrt(pi) R(d))^2 / (4 pi).

    Tools that need the paper's convention-(b) lapse should use
    `np.sqrt(pi) * R(d)` directly.
    """
    return _beta(0.5, d / 2.0 + 1.0)


def p(d):
    """Cascade decay rate p(d) = (1/2) psi((d+1)/2) - (1/2) ln pi.

    Part 0 §3.  Critical points of p(d) define the four distinguished
    layers {d_V, d_0, d_1, d_2} = {5, 7, 19, 217}.
    """
    return 0.5 * _digamma((d + 1) / 2.0) - 0.5 * math.log(pi)


# ──────────────────────────────────────────────────────────────────────
# Distinguished layers  (Part 0 Theorem 7.1 + Part IVa)
# ──────────────────────────────────────────────────────────────────────

D_V = 5       # volume maximum               (Part 0, d_V)
D_0 = 7       # area maximum                 (Part 0, d_0)
D_GW = 14     # gauge-window boundary        (Part IVa)
D_1 = 19      # first threshold  p(d_1) = c_1 = (1/2) ln pi
D_2 = 217     # Planck sink      p(d_2) = c_2 = sqrt(pi)

NON_SINK_DISTINGUISHED = frozenset({D_V, D_0, D_GW, D_1})


# ──────────────────────────────────────────────────────────────────────
# Cosmological parameters at d=4 observer (Option A, Part I corrected)
# ──────────────────────────────────────────────────────────────────────
#
# All density fractions are functions of pi alone.  H0 is derived from
# the Friedmann equation at d=4 with rho_Lambda/M_Pl,red^4 = (2/pi) I
# (Part I Theorem 3.1), where (2/pi) is the observer's cube-sphere bridge
# at the spatial dimension d=3.  See Part V Theorem 6.1.

H0 = 66.78                             # km/s/Mpc
h = H0 / 100.0

Omega_m = 1.0 / pi                     # 0.31831
Omega_b = 1.0 / (2.0 * pi ** 2)        # 0.05066
Omega_r = 1.0 / (4.0 * pi ** 7)        # 8.277e-5
Omega_Lambda = (pi - 1.0) / pi         # 0.68169

# Subleading Bott-partition value for Omega_m (used in BAO fits where
# the full three-generation partition of 1/pi is needed).
Omega_m_bott = 0.31150

# Physical constants used across tools
c_km_s = 299792.458                    # speed of light, km/s
M_PL_RED_GEV = 2.435e18                # reduced Planck mass, GeV
N_eff = 3.044                          # effective neutrino species (Planck convention)


# ──────────────────────────────────────────────────────────────────────
# Arbitrary-precision backend  (mpmath)
# ──────────────────────────────────────────────────────────────────────
#
# Exposed as `cascade_constants.mp` to avoid shadowing the numpy-backed
# primitives.  Scripts that need >15 digits (Part 0 invariants, Dirac
# spectral zeta) should do:
#
#     from cascade_constants import mp
#     R_d = mp.R(d)
#     p_d = mp.p(d)
#
# and set mpmath.mp.dps to the desired precision before calling.

class _MPBackend:
    """Arbitrary-precision analogues of R, alpha, Omega, N_lapse, p."""

    def __init__(self):
        import mpmath as _mp
        self._mp = _mp

    @property
    def pi(self):
        return self._mp.pi

    def R(self, d):
        _mp = self._mp
        return _mp.gamma(_mp.mpf(d + 1) / 2) / _mp.gamma(_mp.mpf(d + 2) / 2)

    def alpha(self, d):
        return self.R(d) ** 2 / 4

    def Omega(self, d):
        _mp = self._mp
        return 2 * _mp.power(_mp.pi, _mp.mpf(d + 1) / 2) / _mp.gamma(
            _mp.mpf(d + 1) / 2
        )

    def V_ball(self, d):
        _mp = self._mp
        return _mp.power(_mp.pi, _mp.mpf(d) / 2) / _mp.gamma(
            _mp.mpf(d) / 2 + 1
        )

    def N_lapse(self, d):
        """Integrand-at-layer-d lapse: N(d) = B(1/2, d/2 + 1) via
        Gamma-function identity.  See top-level N_lapse docstring for
        the two-convention note; this uses convention (a) (V_{d+1}/V_d).
        For the paper's convention (b) (V_d/V_{d-1}), use
        self.sqrt_pi * self.R(d).
        """
        _mp = self._mp
        return (
            _mp.gamma(_mp.mpf(1) / 2)
            * _mp.gamma(_mp.mpf(d) / 2 + 1)
            / _mp.gamma(_mp.mpf(d) / 2 + _mp.mpf(3) / 2)
        )

    def p(self, d):
        _mp = self._mp
        x = (_mp.mpf(d) + 1) / 2
        return (_mp.digamma(x) - _mp.log(_mp.pi)) / 2


try:
    mp = _MPBackend()
except ImportError:                    # pragma: no cover
    mp = None                          # mpmath not installed; mp backend unavailable
