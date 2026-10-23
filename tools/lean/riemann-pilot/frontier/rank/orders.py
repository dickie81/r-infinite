"""Order-N twisted families: extraction exponent, dual Gauss-sum order, carrier degree, and the
exponent left by a model of the dual step.  Exact rational arithmetic.

Extraction (round 288's argument with N-th powers in place of sixth powers).  If the order-N
family A_Z(u) = sum_n mu(n) (u/n)_N W(N(n)/Z) satisfies MeanSquare(sigma), i.e.
sum_{N(u) <= Z^{1+sigma}} |A_Z(u)|^2 << Z^{2+sigma+eps}, then averaging over the N-th powers
u = b^N with N(b) <= Y = Z^{(1+sigma)/N} and Cauchy-Schwarz give the smoothed Moebius sum
<< Z^{1+sigma/2}/Y^{1/2}, hence a zero-free half-plane Re s > theta_N(sigma),
    theta_N(sigma) = (2N - 1 + (N - 1) sigma) / (2N)          (N = 6: (11 + 5 sigma)/12, round 288).

Dual coefficient (identities.py).  mu(n) G(chi_n) = (Hecke) * (unit fixed by n mod 4 or 8) * G(chi_n rho_n)
with rho = chi^{N/2} quadratic, i.e. the dual Gauss sum has order N' = ord(chi rho):
    N' = N/2 (N = 2 mod 4),  N (4 | N),  2N (N odd, over a field with 2N-th roots of unity);
for N = 2 the "Gauss sum" is trivial and the dual coefficient is mu itself.

Carrier.  The theta function on the N'-fold cover of GL_{N'-1} (Kazhdan-Patterson: unique Whittaker
model for n = r + 1 on certain covers), whose first-row coefficients at squarefree indices are N'-th
order Gauss sums for N' = 3 (Patterson) and N' = 4 (Friedberg-Ginzburg, arXiv:1403.3929, Section 5).
Its degree is d = N' - 1.  For N = 3 a second carrier is the Rankin-Selberg product of two cubic
theta functions (mu G_3 = alpha conj(G_3)^2), of degree 4.

Model of the dual step (the companion's DualMeanSquare at B = F = 1: rows k with N(k) <= H = X^{1-sigma},
columns n ~ X, target X^2).  A summation formula of degree d at modulus k turns a column sum into
X / H^{d/2} times a dual sum of length L = H^d / X; the large sieve over the H rows then bounds the
dual sums' mean square by H L + L^{2 - eta} (eta = 0: the generic (H + L) L, sharp for general
coefficients; eta > 0 is a saving on its L^2 term).
The rows' total is X H + X^2 H^{-d} L^{2 - eta}, within X^2 iff H^{d(1 - eta)} X^eta <= X^2, i.e.
    sigma >= sigma_min(d, eta) = 1 - (2 - eta) / (d (1 - eta)).
This is a model of one step: it leaves out the companion's induction on row lengths and transfer
estimates, any structure of the dual beyond the sieve, and carriers not listed here.

Gates (exit status 1 if any fails):
  O1  theta_6(sigma) = (11 + 5 sigma)/12 and theta_N(0) = 1 - 1/(2N)
  O2  below 7/8: sigma* = 1/2 (N = 2), 1/8 (N = 3), none for N >= 4 (theta_4(0) = 7/8 exactly);
      below Sang's 0.8748867: sigma* = 0.49955 (N = 2), 0.124660 (N = 3), none for N >= 4
  O3  dual orders N' = 1, 6, 4, 10, 3, 8, 5, 12 for N = 2, 3, 4, 5, 6, 8, 10, 12; N' = 3 only at N = 6
  O4  model at eta = 0: N = 6 gives 11/12; N = 4 (d = 3) and N = 3 (d = 4) give exactly 1; every other
      listed (N, d) gives more than 1
  O5  savings: N = 4 needs eta > 0 for any theta < 1 and reaches 7/8 at eta = 1/2, never below;
      N = 3 with d = 4 goes below 7/8 iff eta > 3/5, and reaches 5/6 at eta = 1

The cubic family's dual as a cubic large sieve (CUBIC.md).  With coefficients mu(n) G_3(n), norm^2 ~ Z, rows
N(k) <= H = Z^{1-sigma}, the target Z^2 asks for an operator norm <= Z.  Heath-Brown's H + Z + (HZ)^{2/3} gives it iff
H <= Z^{1/2}.  The (HZ)^{2/3} term is the cubic theta component c conj(G_3(k)) N(k)^{-1/6} m(k; Z) at the largest
mass m ~ Z^{5/6}; with the Moebius weight the mass is the Moebius sum m ~ Z^{theta_0 - 1/6} under an input
zero-free half-plane Re s > theta_0, and the component's total is H^{2/3} Z^{2 theta_0 - 1/3}.
  O6  a saving Z^{-delta} on the (HZ)^{2/3} term gives sigma_min = max(0, 1/2 - 3 delta/2) and
      theta_3 = max(5/6, 1 - delta/2): below 7/8 iff delta > 1/4, below Sang's record iff delta > 0.2502266,
      at 11/12 iff delta >= 1/6
  O7  the fixed point: the component is within Z^2 iff sigma >= 3 theta_0 - 5/2, and theta_3 at that sigma is
      max(theta_0, 5/6) exactly, for theta_0 = 5/6, 0.8748867, 7/8, 9/10, 11/12, 1 and a grid of 200 rationals
  O8  the component's exponent at theta_0 = 1 equals Heath-Brown's term's, (2/3)(2 - sigma) + 1, for all sigma, and a
      saving delta on that term is the component at theta_0 = 1 - delta/2 (O6 and O7 agree)
"""
import sys
from fractions import Fraction as Fr

RECORD = Fr(8748867, 10_000_000)          # Sang, arXiv:2610.15291 (on the release's analytic inputs)
SEVEN_EIGHTHS = Fr(7, 8)
ORDERS = (2, 3, 4, 5, 6, 8, 10, 12)


def theta(N, sigma):
    return (2 * N - 1 + (N - 1) * Fr(sigma)) / Fr(2 * N)


def sigma_to_beat(N, target):
    """sup of sigma >= 0 with theta_N(sigma) < target, or None if theta_N(0) >= target."""
    s = (2 * N * target - (2 * N - 1)) / Fr(N - 1)
    return s if s > 0 else None


def dual_order(N):
    if N == 2:
        return 1
    if N % 2 == 1:
        return 2 * N
    return N // 2 if N % 4 == 2 else N


def carriers(N):
    """degrees of the carriers recorded for the order-N family's dual."""
    Nd = dual_order(N)
    if Nd == 1:
        return []
    ds = [Nd - 1]
    if N == 3:
        ds = [4] + ds                       # Rankin-Selberg of two cubic thetas, then GL_5
    return ds


def sigma_min(d, eta=Fr(0)):
    if d <= 2:
        return Fr(0)
    return max(Fr(0), 1 - (2 - Fr(eta)) / (d * (1 - Fr(eta))))


def theta_model(N, d, eta=Fr(0)):
    return theta(N, sigma_min(d, eta))


def eta_to_beat(N, d, target):
    """least eta with theta_model(N, d, eta) < target (strict), or None if no eta < 1 works."""
    s = sigma_to_beat(N, target)
    if s is None:
        return None
    c = (1 - s) * d
    if c <= 2:
        return Fr(0)
    return (c - 2) / (c - 1)


def sieve_sigma(delta):
    """least sigma >= 0 with (HZ)^{2/3} Z^{-delta} <= Z at H = Z^{1-sigma}."""
    return max(Fr(0), Fr(1, 2) - Fr(3, 2) * Fr(delta))


def component_sigma(theta0):
    """least sigma >= 0 with H^{2/3} Z^{2 theta0 - 1/3} <= Z^2 at H = Z^{1-sigma}."""
    return max(Fr(0), 3 * Fr(theta0) - Fr(5, 2))


def component_exponent(theta0, sigma):
    return Fr(2, 3) * (1 - Fr(sigma)) + 2 * Fr(theta0) - Fr(1, 3)


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f"[{'PASS' if ok else 'FAIL'}] {name}: {msg}")
        fails += 0 if ok else 1

    print(f"{'N':>3} {'theta_N(0)':>10} {'sigma<7/8':>9} {'sigma<0.8748867':>15} {'N_dual':>6} {'d':>3}"
          f" {'theta (model, eta=0)':>22} {'eta for <7/8':>12}")
    for N in ORDERS:
        s1, s2 = sigma_to_beat(N, SEVEN_EIGHTHS), sigma_to_beat(N, RECORD)
        ds = carriers(N) or [None]
        for d in ds:
            if d is None:
                th, eta = 'circular (dual is mu)', '-'
            else:
                th = f'{float(theta_model(N, d)):.4f} (sigma={sigma_min(d)})'
                e = eta_to_beat(N, d, SEVEN_EIGHTHS)
                eta = '-' if e is None else str(e)
            print(f"{N:>3} {float(theta(N, 0)):>10.4f} {str(s1) if s1 else '-':>9} "
                  f"{(f'{float(s2):.6f}') if s2 else '-':>15} {dual_order(N):>6} {str(d):>3} {th:>22} {eta:>12}")

    ok = all(theta(6, s) == (11 + 5 * Fr(s)) / 12 for s in (0, Fr(1, 20), Fr(1, 10), 1)) and \
        all(theta(N, 0) == 1 - Fr(1, 2 * N) for N in ORDERS)
    gate('O1', ok, 'theta_6(sigma) = (11 + 5 sigma)/12; theta_N(0) = 1 - 1/(2N)')

    s78 = {N: sigma_to_beat(N, SEVEN_EIGHTHS) for N in ORDERS}
    srec = {N: sigma_to_beat(N, RECORD) for N in ORDERS}
    ok = s78[2] == Fr(1, 2) and s78[3] == Fr(1, 8) and all(s78[N] is None for N in ORDERS if N >= 4) \
        and theta(4, 0) == SEVEN_EIGHTHS and abs(float(srec[2]) - 0.49955) < 1e-5 \
        and abs(float(srec[3]) - 0.124660) < 1e-6 and all(srec[N] is None for N in ORDERS if N >= 4)
    gate('O2', ok, f'sigma* below 7/8: {[(N, str(s78[N])) for N in ORDERS if s78[N]]}; '
                   f'below the record: {[(N, round(float(srec[N]), 6)) for N in ORDERS if srec[N]]}')

    want = {2: 1, 3: 6, 4: 4, 5: 10, 6: 3, 8: 8, 10: 5, 12: 12}
    ok = all(dual_order(N) == want[N] for N in ORDERS) and [N for N in ORDERS if dual_order(N) == 3] == [6]
    gate('O3', ok, f'dual orders {[(N, dual_order(N)) for N in ORDERS]}')

    vals = {(N, d): theta_model(N, d) for N in ORDERS for d in carriers(N)}
    ok = vals[(6, 2)] == Fr(11, 12) and vals[(4, 3)] == 1 and vals[(3, 4)] == 1 and \
        all(v > 1 for k, v in vals.items() if k not in ((6, 2), (4, 3), (3, 4)))
    gate('O4', ok, 'model, eta = 0: ' + ', '.join(f'N={N} d={d}: {v}' for (N, d), v in vals.items()))

    ok = theta_model(4, 3, Fr(1, 1000)) < 1 and theta_model(4, 3, Fr(1, 2)) == SEVEN_EIGHTHS and \
        all(theta_model(4, 3, Fr(k, 100)) >= SEVEN_EIGHTHS for k in range(0, 100)) and \
        eta_to_beat(3, 4, SEVEN_EIGHTHS) == Fr(3, 5) and theta_model(3, 4, Fr(3, 5)) == SEVEN_EIGHTHS and \
        theta_model(3, 4, Fr(61, 100)) < SEVEN_EIGHTHS and theta(3, 0) == Fr(5, 6)
    gate('O5', ok, 'N = 4: eta > 0 needed, 7/8 at eta = 1/2 and never below; '
                   f'N = 3 (d = 4): below 7/8 iff eta > {eta_to_beat(3, 4, SEVEN_EIGHTHS)}; 5/6 at eta -> 1')

    th = {Fr(d, 1000): theta(3, sieve_sigma(Fr(d, 1000))) for d in range(0, 401)}
    ok = all(v == max(Fr(5, 6), 1 - d / 2) for d, v in th.items()) and \
        all((v < SEVEN_EIGHTHS) == (d > Fr(1, 4)) for d, v in th.items()) and \
        all((v < RECORD) == (d > Fr(2502266, 10_000_000)) for d, v in th.items()) and \
        theta(3, sieve_sigma(Fr(1, 6))) == Fr(11, 12) and sieve_sigma(0) == Fr(1, 2)
    gate('O6', ok, 'theta_3 = max(5/6, 1 - delta/2); below 7/8 iff delta > 1/4; below the record iff delta > '
                   f'{float(2 * (1 - RECORD)):.7f}; 11/12 at delta = 1/6')

    grid = [Fr(5, 6), RECORD, SEVEN_EIGHTHS, Fr(9, 10), Fr(11, 12), Fr(1)] + \
        [Fr(5, 6) + Fr(k, 1200) for k in range(0, 201)]
    ok = all(theta(3, component_sigma(t)) == max(t, Fr(5, 6)) for t in grid) and \
        all(component_exponent(t, component_sigma(t)) <= 2 for t in grid if t >= Fr(5, 6)) and \
        all(component_exponent(t, component_sigma(t) - Fr(1, 10 ** 6)) > 2 for t in grid if t > Fr(5, 6))
    gate('O7', ok, f'output theta_3 = input theta_0 on {len(grid)} values in [5/6, 1]; e.g. theta_0 = 0.8748867 -> sigma >= '
                   f'{float(component_sigma(RECORD)):.7f}, theta_3 = {float(theta(3, component_sigma(RECORD))):.7f}')

    sig = [Fr(k, 100) for k in range(0, 101)]
    ok = all(component_exponent(1, x) == Fr(2, 3) * (2 - x) + 1 for x in sig) and \
        component_sigma(1) == Fr(1, 2) == sieve_sigma(0) and \
        all(component_sigma(1 - Fr(d, 1000) / 2) == sieve_sigma(Fr(d, 1000)) for d in range(0, 401))
    gate('O8', ok, "theta_0 = 1 gives Heath-Brown's exponent (2/3)(2 - sigma) + 1 and sigma >= 1/2; "
                   'saving delta = input theta_0 = 1 - delta/2')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
