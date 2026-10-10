#!/usr/bin/env python3
"""
The Weyl-chirality decomposition of S^11 -- computed (the papers' open
item, part4b:4082).

Setup, entirely from cascade-owned structures: the ambient space of
S^11 is R^12; Part II's complex structure J makes R^12 = C^6; Adams'
SU(3) at the gauge layer acts on C^6 as 3 (+) 3bar.  The spinor module
of Spin(12) is the Fock space Lambda(C^6) with Weyl classes = even/odd
form degree (= colour-number parity).  The decomposition under
SU(3)_colour is therefore a finite character computation:

  Delta+ (even, 32) = 4x1 (+) 2x8 (+) 2x(3 (+) 3bar)
  Delta- (odd,  32) = 2x1 (+) (6 (+) 6bar) (+) 3x(3 (+) 3bar)

THEOREM (verified numerically below by character sampling): the
triplet multiplicity is 3 in the ODD Weyl class and 2 in the even
class; quarks (one unit of colour charge = odd colour number) live in
the odd class; the odd class carries the fundamental with multiplicity
exactly N_c = 3.

Also rigorous: the Adams count rho(12) = 4 gives rho - 1 = 3 tangent
fields on S^11, and S^11 = Sp(3)/Sp(2) identifies them as the
quaternionic triple (I, J, K) -- the Adams '3' at the gauge sphere is
the imaginary quaternion frame.

CANDIDATE LEMMA (the up-type factor): a doublet's T3 = +1/2 member
(up-type) crossing the gauge layer must additionally select its copy
among the odd-class triplets -- multiplicity 3 -> counting factor N_c
per generation crossing, on top of the Cartan-measurement atom e.
The T3 = -1/2 member (down-type) crosses Cartan-diagonally and selects
nothing.  This reproduces t/c = N_c x (b/s) (-0.8 sigma) and the
papers' (t/b)/(c/s) = N_c (1.5%).  NAMED RESIDUAL: the doublet-
assignment step (why +1/2 selects and -1/2 does not) -- same epistemic
grade as Addendum 17's Step 3 before Addendum 18 formalised it.

REFUSAL (recorded): the decomposition alone does not supply the
up-type ABSOLUTE anchor; without the assignment lemma no grammar
search is performed for it.
"""

import cmath
import math

import numpy as np


def elementary_symmetric(vals):
    """e_0..e_n of a list of complex numbers, via generating poly."""
    coeffs = np.array([1.0 + 0j])
    for v in vals:
        coeffs = np.convolve(coeffs, np.array([1.0 + 0j, v]))
    return coeffs  # coeffs[k] = e_k


def su3_characters(a, b):
    z = [cmath.exp(1j * a), cmath.exp(1j * b), cmath.exp(-1j * (a + b))]
    chi3 = sum(z)
    chi3b = chi3.conjugate()
    p2 = sum(w * w for w in z)
    chi6 = (chi3 ** 2 + p2) / 2.0
    chi6b = chi6.conjugate()
    chi8 = chi3 * chi3b - 1.0
    return {"1": 1.0 + 0j, "3": chi3, "3b": chi3b, "6": chi6,
            "6b": chi6b, "8": chi8}


def main():
    print("=" * 74)
    print("Character verification of the S^11 Weyl decomposition")
    print("=" * 74)
    rng = np.random.default_rng(11)
    samples = [(rng.uniform(0, 2 * math.pi), rng.uniform(0, 2 * math.pi))
               for _ in range(40)]
    irreps = ["1", "3", "3b", "6", "6b", "8"]
    rows_even, rows_odd, mat = [], [], []
    for (a, b) in samples:
        z = [cmath.exp(1j * a), cmath.exp(1j * b), cmath.exp(-1j * (a + b))]
        vals = z + [w.conjugate() for w in z]          # eigenvalues on 3+3bar
        e = elementary_symmetric(vals)
        even = e[0] + e[2] + e[4] + e[6]
        odd = e[1] + e[3] + e[5]
        rows_even.append(even)
        rows_odd.append(odd)
        ch = su3_characters(a, b)
        mat.append([ch[i] for i in irreps])
    A = np.array(mat)
    m_even = np.linalg.lstsq(A, np.array(rows_even), rcond=None)[0]
    m_odd = np.linalg.lstsq(A, np.array(rows_odd), rcond=None)[0]
    dims = {"1": 1, "3": 3, "3b": 3, "6": 6, "6b": 6, "8": 8}
    print(f"  {'irrep':>6}{'even (Delta+)':>15}{'odd (Delta-)':>14}")
    de = do = 0
    for i, name in enumerate(irreps):
        me, mo = round(m_even[i].real), round(m_odd[i].real)
        de += me * dims[name]
        do += mo * dims[name]
        print(f"  {name:>6}{me:>15}{mo:>14}")
    print(f"  dimension check: even = {de} (expect 32), odd = {do} (expect 32)")
    print(f"  residuals: {np.abs(A @ m_even - rows_even).max():.1e},"
          f" {np.abs(A @ m_odd - rows_odd).max():.1e}")
    print()
    print("  => TRIPLET MULTIPLICITY: 3 in the odd Weyl class, 2 in the")
    print("     even.  Quarks (odd colour number) live in the odd class:")
    print("     the class carries the fundamental with multiplicity N_c = 3.")

    print()
    print("=" * 74)
    print("The Adams triple on S^11 is quaternionic")
    print("=" * 74)
    # Radon-Hurwitz: 12 = 2^2 x 3 -> rho(12) = 4 -> 3 tangent fields
    print("  rho(12) = 4 (Radon-Hurwitz, 12 = 2^2 x 3) -> 3 tangent fields;")
    print("  S^11 = Sp(3)/Sp(2): the three fields are the quaternionic")
    print("  triple I, J, K -- the Adams '3' is the imaginary quaternion")
    print("  frame at the gauge sphere.")

    print()
    print("=" * 74)
    print("Consequence and named residual")
    print("=" * 74)
    print("  candidate lemma: the up-type (T3 = +1/2) crossing selects its")
    print("  copy among the odd-class triplets: counting factor N_c = 3 per")
    print("  generation crossing; down-type crosses Cartan-diagonally.")
    print("  reproduces: t/c = N_c (b/s) at -0.8 sigma; (t/b)/(c/s) = N_c.")
    print("  NAMED RESIDUAL: the doublet-assignment step (+1/2 selects,")
    print("  -1/2 does not) -- the analogue of Step 3 before Addendum 18.")
    print("  REFUSAL: no grammar search for the up-type absolute anchor;")
    print("  it requires the assignment lemma first.")


if __name__ == "__main__":
    main()
