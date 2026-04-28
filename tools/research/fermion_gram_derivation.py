#!/usr/bin/env python3
"""
Structural derivation of chirality-halved Gram from cascade fermion lapse.

Setup
-----
Part IVb asserts (pending action-principle derivation, oq:fermion-cascade-action)
that the cascade fermion propagator on even-sphere layers S^{2n} is R(d)/chi
rather than the scalar propagator R(d).  The chi=2 halving comes from the
chirality factorisation theorem (Part IVb Theorem 4.8) applied to the
hairy-ball obstruction at even-sphere layers.

Conjecture
----------
For a CASCADE FERMION FIELD whose layer integrand on even-sphere layers
carries the propagator R(d)/chi, the appropriate Gram inner product is
   <psi_d, psi_d'>_fermion  =  ?
and the resulting Gram correction is
   G_fermion = G_scalar / chi
where G_scalar is the standard adjacent-pair Gram sum.

Two natural ansatzes for the fermion integrand
----------------------------------------------
(A) Half-power scalar: psi_d(x) = (1 - x^2)^{d/(2 chi)} = (1-x^2)^{d/4} for chi=2
    Motivation: the "square root" of the scalar field's contribution, matching
    the propagator-norm-squared identity (R(d)/chi)^2 = R(d)^2/chi^2.
    Note: this differs from R(d)/chi by a factor of chi, not square-rooted.

(B) Lapse-rescaled scalar: psi_d(x) = (1 - x^2)^{d/2} / sqrt(chi)
    Motivation: chi enters as an OVERALL rescaling, not as power.

(C) sqrt-N-N scaling: psi_d(x) = (1 - x^2)^{d/2}, but with the inner product
    rescaled by 1/chi.  Motivation: the chirality factor enters in the
    measure, not the integrand.

For each ansatz, compute:
  - Gram inner products (analytical or numerical)
  - Per-step correlation 1 - C^2_{d,d+1}^{fermion}
  - Path sum G_fermion across cascade-physics paths
  - Test: does G_fermion = G_scalar / chi exactly?

If one ansatz matches, that's the structural cascade fermion compliance.
"""

from __future__ import annotations

import math
import sys

import mpmath as mp  # type: ignore[import-not-found]

mp.mp.dps = 50

CHI = 2  # chirality factor for even-sphere layers


def beta_mp(a: mp.mpf, b: mp.mpf) -> mp.mpf:
    """Beta function B(a, b) in mpmath."""
    return mp.gamma(a) * mp.gamma(b) / mp.gamma(a + b)


def gram_scalar(d_i: float, d_j: float) -> mp.mpf:
    """Scalar Gram entry: int (1-x^2)^{(d_i + d_j)/2} dx = B(1/2, (d_i+d_j)/2 + 1)."""
    return beta_mp(mp.mpf(1) / 2, mp.mpf(d_i + d_j) / 2 + 1)


def gram_ansatz_A(d_i: float, d_j: float) -> mp.mpf:
    """Ansatz A: fermion integrand psi_d = (1-x^2)^{d/(2 chi)}.

    inner product: int (1-x^2)^{(d_i+d_j)/(2 chi)} dx = B(1/2, (d_i+d_j)/(2 chi) + 1).
    """
    return beta_mp(mp.mpf(1) / 2, mp.mpf(d_i + d_j) / (2 * CHI) + 1)


def gram_ansatz_B(d_i: float, d_j: float) -> mp.mpf:
    """Ansatz B: psi_d = scalar/sqrt(chi).  Inner product = scalar/chi (constant rescale)."""
    return gram_scalar(d_i, d_j) / CHI


def C_squared(gram_func, d_i: float, d_j: float) -> mp.mpf:
    """Normalised correlation C^2_{ij} = G_{ij}^2 / (G_{ii} G_{jj})."""
    G_ij = gram_func(d_i, d_j)
    G_ii = gram_func(d_i, d_i)
    G_jj = gram_func(d_j, d_j)
    return G_ij ** 2 / (G_ii * G_jj)


def gram_sum(gram_func, d_start: int, d_end: int) -> mp.mpf:
    """Sum_{d=d_start..d_end-1} (1 - C^2_{d, d+1}) for the given Gram functional."""
    return sum(
        mp.mpf(1) - C_squared(gram_func, d, d + 1)
        for d in range(d_start, d_end)
    )


def main() -> int:
    print("=" * 78)
    print("CASCADE FERMION GRAM: STRUCTURAL DERIVATION OF CHI-HALVED CORRECTION")
    print("=" * 78)
    print()
    print("Conjecture: there exists a cascade fermion Gram functional <,>_fermion")
    print("whose path-distributed correction G_fermion equals G_scalar / chi.")
    print()

    # ---------------------------------------------------------------
    # Note: Ansatz B (constant rescaling) leaves C^2 unchanged because:
    #   C^2 = G_ij^2 / (G_ii G_jj)
    # rescaling G by const drops out.  So 1 - C^2 = scalar value -> G_fermion = G_scalar.
    # That's NOT what we want.  Discard B.
    # ---------------------------------------------------------------
    print("Ansatz B (scalar/sqrt(chi) rescaling) is trivially the same as scalar:")
    print("constant rescaling cancels in C^2 = G_ij^2/(G_ii G_jj).  Discarded.")
    print()

    # ---------------------------------------------------------------
    # Test Ansatz A: psi_d(x) = (1 - x^2)^{d/(2 chi)}
    # ---------------------------------------------------------------
    print("-" * 78)
    print("ANSATZ A: psi_d(x) = (1 - x^2)^{d/(2 chi)}")
    print("-" * 78)
    print("Direct power-rescaling: integrand exponent halved (chi=2).")
    print()
    print(f"{'(d, d+1)':>12} {'1-C^2 scalar':>16} {'1-C^2 ansatz A':>18} "
          f"{'ratio (A/scalar)':>18} {'expected: 1/chi':>16}")
    print("-" * 78)
    for d in [5, 6, 14, 15, 19, 20, 50]:
        cs_scalar = mp.mpf(1) - C_squared(gram_scalar, d, d + 1)
        cs_A = mp.mpf(1) - C_squared(gram_ansatz_A, d, d + 1)
        ratio = cs_A / cs_scalar if cs_scalar != 0 else mp.mpf("nan")
        print(
            f"{f'({d},{d+1})':>12} {mp.nstr(cs_scalar, 8):>16} {mp.nstr(cs_A, 8):>18} "
            f"{mp.nstr(ratio, 8):>18} {1.0/CHI:>16.6f}"
        )
    print()

    # Path sums
    print(f"{'path':>20} {'G_scalar':>16} {'G_ansatz_A':>16} {'A/scalar':>14} {'G_scalar/chi':>14}")
    print("-" * 80)
    paths = [
        ("alpha_s (5..12)", 5, 12),
        ("m_tau/m_mu (6..13)", 6, 13),
        ("m_mu/m_e (14..21)", 14, 21),
        ("rho_Lambda (5..216)", 5, 216),
    ]
    for name, d0, d1 in paths:
        G_s = gram_sum(gram_scalar, d0, d1)
        G_A = gram_sum(gram_ansatz_A, d0, d1)
        ratio = G_A / G_s
        G_s_over_chi = G_s / CHI
        print(
            f"{name:>20} {mp.nstr(G_s, 8):>16} {mp.nstr(G_A, 8):>16} "
            f"{mp.nstr(ratio, 8):>14} {mp.nstr(G_s_over_chi, 8):>14}"
        )
    print()

    # ---------------------------------------------------------------
    # Test Ansatz A more carefully: per-step ratio asymptotic
    # ---------------------------------------------------------------
    print("-" * 78)
    print("Per-step asymptotic for Ansatz A: 1 - C^2_{d,d+1}^A vs 1/(8 d_eff^2)")
    print("-" * 78)
    print("If psi has integrand (1-x^2)^{d/(2chi)}, the EFFECTIVE d for the")
    print("scalar formula is d/chi (the integrand has half the cascade depth).")
    print("So expect 1 - C^2_A ~ 1/(8(d/chi)^2) = chi^2 / (8 d^2) = chi^2 * (1-C^2_scalar)")
    print("at leading order -- which is OPPOSITE to what we want.")
    print()
    for d in [10, 50, 100, 500]:
        cs_scalar = float(mp.mpf(1) - C_squared(gram_scalar, d, d + 1))
        cs_A = float(mp.mpf(1) - C_squared(gram_ansatz_A, d, d + 1))
        ratio = cs_A / cs_scalar
        # Expected at leading 1/d^2: ratio = chi^2 (since d_eff = d/chi)
        print(f"  d={d:>4}: 1-C^2 scalar = {cs_scalar:.4e}, 1-C^2 A = {cs_A:.4e}, "
              f"ratio = {ratio:.4f}, chi^2 = {CHI**2}")
    print()
    print("Ansatz A gives ratio ~ chi^2, not 1/chi.  WRONG DIRECTION.")
    print("This rules out the simple half-power integrand as the fermion field.")
    print()

    # ---------------------------------------------------------------
    # New ansatz: cascade fermion as DOUBLE-POWER scalar
    # If the fermion has propagator R(d)/chi and the SCALAR has R(d), then the
    # fermion's "natural d" is 2d (double the cascade depth) -- because R(d)/chi
    # scales like sqrt(2/(d+1))/2, and R(2d) ~ sqrt(2/(2d+1)) ~ R(d)/sqrt(2)
    # -- not quite chi-halved.  Try integrand (1-x^2)^{chi*d/2}.
    # ---------------------------------------------------------------
    def gram_ansatz_D(d_i: float, d_j: float) -> mp.mpf:
        """Ansatz D: psi_d(x) = (1 - x^2)^{chi*d/2}."""
        return beta_mp(mp.mpf(1) / 2, mp.mpf(d_i + d_j) * CHI / 2 + 1)

    print("-" * 78)
    print("ANSATZ D: psi_d(x) = (1 - x^2)^{chi*d/2}  (DOUBLE the scalar exponent)")
    print("-" * 78)
    print("Motivation: if fermion lapse is R(d)/chi ~ sqrt(2/(d+1))/chi, then in")
    print("scalar-equivalent form the fermion is at EFFECTIVE d_eff = chi*d.")
    print(f"Expected at leading 1/d^2: 1 - C^2_D ~ 1/(8(chi*d)^2) = (1/chi^2) * (1-C^2_scalar)")
    print(f"vs what we want: 1/chi * (1-C^2_scalar)")
    print()
    for d in [10, 50, 100, 500]:
        cs_scalar = float(mp.mpf(1) - C_squared(gram_scalar, d, d + 1))
        cs_D = float(mp.mpf(1) - C_squared(gram_ansatz_D, d, d + 1))
        ratio = cs_D / cs_scalar
        print(f"  d={d:>4}: 1-C^2 scalar = {cs_scalar:.4e}, 1-C^2 D = {cs_D:.4e}, "
              f"ratio = {ratio:.6f}, 1/chi^2 = {1/CHI**2}, 1/chi = {1/CHI}")
    print()
    print("Ansatz D gives ratio ~ 1/chi^2, not 1/chi.  Closer but still wrong.")
    print()

    # ---------------------------------------------------------------
    # Honest assessment so far
    # ---------------------------------------------------------------
    print("=" * 78)
    print("INTERIM CONCLUSION")
    print("=" * 78)
    print()
    print("Neither half-power (Ansatz A) nor double-power (Ansatz D) gives the")
    print("conjectured G_fermion = G_scalar / chi structure.")
    print()
    print("  Ansatz A: 1 - C^2_A / (1 - C^2_scalar) -> chi^2  (WRONG sign in exponent)")
    print("  Ansatz D: 1 - C^2_D / (1 - C^2_scalar) -> 1/chi^2  (still SQUARED, not halved)")
    print()
    print("The ratio chi^a in the per-step deficit comes from EFFECTIVE-d scaling:")
    print("  if psi has integrand exponent k*d, then 1 - C^2 ~ 1/(8(k*d)^2) = (1/k^2)/(8d^2)")
    print("So no power-law integrand modification gives a 1/chi (not 1/chi^2) factor.")
    print()
    print("This strongly suggests: the chirality halving for path-distributed")
    print("corrections is NOT a property of a fermion FIELD's Gram matrix in the")
    print("naive integrand sense.  It must come from an EXTRA structural mechanism")
    print("specific to the d-source coincidence in m_mu/m_e.")
    print()
    print("Next direction: look at where the chi factor lives in Part IVb's marginal")
    print("Green's function identity (G(d_obs, d*) - G(d_obs, d*+1) = alpha(d*) for")
    print("scalar; alpha(d*)/chi for fermion).  The chi enters via the BOUNDARY")
    print("(spectral) reading at the source layer, not via the bulk integrand.")
    print()
    print("Implication: the chi-halved Gram for m_mu/m_e is a BOUNDARY effect at")
    print("d=14 (the U(1) source layer), not a bulk fermion-integrand effect.")
    print("The path d=14..21 starts AT the source layer, so the boundary chi-factor")
    print("is in the path itself, contributing to the path-distributed correction.")
    return 0


if __name__ == "__main__":
    sys.exit(main())


# ============================================================================
# OPTION B FOLLOW-UP: Theorem 4.8 (Part IVb chirality factorisation) reading
# ============================================================================
"""
Reading Theorem 4.8 directly: G_Q(d, d^*) = G(d, d^*)/chi^k for a k-mode
observable, with G the scalar Green's function of the cascade action's
discrete Laplacian (compliance alpha = R^2/4).

The chirality halving in Theorem 4.8 comes from EQUAL SPLITTING of a scalar
perturbation across two chirality basins at even-sphere layers (component A
of the proof).  This applies to a SINGLE PERTURBATION at a SOURCE LAYER d*
and gives delta phi_+ = delta phi_- = delta phi / chi.

For Theorem 4.8 to hold, the fermion Green's function at source d* equals
the scalar response divided by chi.  Since the discrete Laplacian Green's
function decays like the compliance, this requires:
   alpha_f(d^*) = alpha(d^*) / chi.
Equivalently: log alpha_f = log alpha - log chi (ADDITIVE shift in log space).

For path-distributed Gram correction (Cor 14.4 + k-step generalisation):
   G_path = sum_d (1 - C^2_{d, d+1}) ~ -(1/2) sum_d Delta^2 log alpha |_{2d+2}

For G_path^fermion = G_path^scalar / chi we'd need:
   Delta^2 log alpha_f = Delta^2 log alpha / chi
which requires log alpha_f = (log alpha) / chi (MULTIPLICATIVE rescaling).

These two conditions are MATHEMATICALLY INCOMPATIBLE:
- Additive log-shift (Theorem 4.8) preserves Delta^2 log alpha (constants
  drop in the second difference). So fermion path correction = scalar.
- Multiplicative log-rescaling gives wrong single-source response: alpha_f
  at d^* would be alpha(d^*)^{1/chi}, not alpha(d^*) / chi.

Conclusion: there is NO unified cascade fermion compliance function whose
single-source Green's function reproduces alpha(d^*)/chi (Theorem 4.8) AND
whose path-distributed correction is G_scalar/chi.  These are structurally
distinct phenomena.

Implication for m_mu/m_e:
The empirical match G_scalar/chi ~ residual_{m_mu/m_e} (within ~3%) is NOT
a consequence of a unified fermion compliance.  It is one of:
  (i) Coincidence (the 3% slop is consistent with a near-miss).
  (ii) A boundary effect at the source layer d^*=14 not captured by either
       Theorem 4.8 or the bulk Gram-Laplacian -- a separate mechanism.
  (iii) A position-dependent or higher-rank cascade correction structure
       beyond the single-compliance scalar action.

The structural derivation push (option B) terminates here without closure.
The Part 4b oq:mu-e-residual remains open, with the chirality-halved Gram
formulation now classified as 'cannot arise from unified fermion compliance'.
"""
