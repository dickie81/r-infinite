"""Exact-arithmetic checks for the ideas register IDEAS.md (README round 546).

Each check gates a quantitative closure marked [R*] in IDEAS.md.  Exponents are powers of q (prime) with
T = q^{o(1)}, as in `seven_thirds.py`.  sigma = 5/7 is the critical abscissa, and t = (7/3)(1 - 5/7) = 2/3 is the
count a density exponent 7/3 allows there.

Checks.
  (R1) A1, Selberg's method in the form N(sigma) << q^{1 - (2 sigma - 1) theta}.  The density exponent
       f(sigma, theta) = (1 - (2 sigma - 1) theta)/(1 - sigma) has f(5/7, 1/2) = 11/4 and f(5/7, 7/9) = 7/3, and on
       a rational grid of theta in [0, 1], with 7/9 included, f(5/7, theta) < 7/3 exactly when theta > 7/9.
  (R2) D2, D3.  Chen-Gupta-Li's subdivided term q q1^{1/3} T N^{2 - 4 sigma}, with the modulus q^{1 + eta},
       q1 = q and T = q^tau, has q-exponent 4/3 + eta + tau before the factor N^{2 - 4 sigma}.  At N = q^{7/9} and
       sigma = 5/7 the term is q^{2/3 + eta + tau}: equal to q^{2/3} at eta = tau = 0 and above it at every other
       point of a grid with eta, tau >= 0.
  (R3) B6.  The large-values Burgess form |W| <~ N^{2r - 1} q^{1 + 1/r} V^{-2r - 1} at N = q^{7/18} and
       V = N^{5/7} has q-exponent (2r - 6)/9 + 1 + 1/r, which exceeds 1 for r = 1, ..., 10; for r >= 3 both
       (2r - 6)/9 >= 0 and 1/r > 0.  The derivation's choice A = V q^{-1/r} is at least 1 only for r >= 18/5.
  (R4) C3.  An amplifier of length q^lam built from q^rho characters has an off-diagonal of random size
       q^{(rho + lam)/2} against the diagonal q^lam.  On a grid, with rho = 2/3, the off-diagonal is the smaller
       exactly when lam > rho.
  (R5) B6.  Burgess's bound N^{1 - 1/r} q^{(r + 1)/(4r^2)} lies below N^{5/7} exactly when N > q^{c_r}, with
       c_r = ((r + 1)/(4r^2))/(1/r - 2/7), for r = 1, 2, 3: c_1 = 7/10 (Polya-Vinogradov), c_2 = 7/8 and
       c_3 = 7/3 > 1.  For r = 4, ..., 10, 1/r < 2/7 and the bound is never below N^{5/7}.
  (R6) B13.  A large set of size K at V = N^sigma needs a top eigenvalue K N^{2 sigma - 1} of the off-diagonal
       Gram matrix E.  With ||E||_F^2 = K^2 N, at most N^{3 - 4 sigma} eigenvalues can have that size.  At
       sigma = 5/7 that is N^{1/7}: q^{1/9} at N = q^{7/9} and q^{1/18} at N = q^{7/18}.
  (R7) Core 2 and C7.  At N = q^{7/18}: q N^3 = q^{13/6} and N^6 = q^{7/3}.  On a grid, 13/6 + theta' < 7/3
       exactly when theta' < 1/6.  Zacharias's saving eta = 1/14 - 3 theta/7 is 11/448 at theta = 7/64.
  (R8) C8.  SIX(delta) counts products of three numbers of size q^{7/18}, so X = q^{7/6}.  For k = 3,
       7/6 < 2 = k - 1 and 7/6 < 5/2 = k - 1/2.
  (R9) B5, B8.  In `seven_thirds.py`'s model at sigma = 5/7:
       - Huxley's good set is {7/6} at t = 2/3 and is empty at the grid points t < 2/3;
       - Huxley's second line 1 + l(4 - 6 sigma) has slope -2/7, above the mean value theorem's -3/7, so on a
         grid of t its good set lies inside the mean value theorem's;
       - the mean value theorem's good set at t = 2/3 is [7/9, 7/6];
       - Halasz-Montgomery with off-diagonal entries N^{1/12} q^{5/12} needs l >= 35/29, and 35/29 > 7/6.
  (R10) B14.  Large-values theorems from the Analytic Number Theory Exponent Database (chapters 7 and 10, as
       downloaded on 2026-10-18; README round 546 quotes them), with T replaced by the conductor q, so that
       F(l) = l LV(sigma, 1/l).  The barrier at sigma = 5/7 is the block set B = {7/18, 7/9} u [7/6, oo) of
       `seven_thirds.py`, where a family certifies nothing below 7/3 unless F < 2/3 somewhere.
       (R10a) The mean value theorem (7.9) and Huxley (7.12) give `seven_thirds.py`'s MVT and HUX exactly, on a
              grid of (s, l).
       (R10b) F >= 2/3 at l = 7/18, at l = 7/9 and on a grid of l >= 7/6, wherever the theorem applies, for each
              of: Heath-Brown (7.14); the preliminary Heath-Brown bound (7.13) fed with any rho <= tau; Jutila (7.16)
              for k = 1, ..., 12; the exponent-pair bound (7.11) at seven exponent pairs; Guth-Maynard's (10.28) for
              k = 1, ..., 12; Bourgain's simplified bound (10.30) for every alpha_1, alpha_2 >= 0; the rows of
              Bourgain's optimized table (10.31) whose region contains the point; and Kerr's Theorem 5 (10.32) for
              every admissible alpha, where its condition forces alpha > 0 (tau >= 8 sigma - 5).  On the grid of
              l >= 7/6 the database's lower bound min(2 - 2 sigma, tau) (its Lemma 7.5) gives F >= 2/3 by itself.  At
              every exponent pair tested, (7.11)'s slope exceeds the mean value theorem's by (ell - 3/7)/k > 0.
       (R10c) Guth-Maynard's Theorem 1.1 (10.27) gives F(7/9) = 29/45 < 2/3; its proof subdivides to tau = 6/5.
       (R10d) Its unsubdivided companion (10.28) at l = 7/9: the term 2 - 4 sigma + (4/3) tau gives exactly 2/3 and
              equals `seven_thirds.py`'s P31 term c + l(2 - 4s) at c = 4/3; the other seven terms are below 2/3 for
              k = 1, ..., 5; and the term (4 - 6 sigma) k/(k + 1) + k tau/(k + 1) is at least 2/3 for k = 6, ..., 12.
              So the least value over k = 1, ..., 12 is exactly 2/3, from Chen-Gupta-Li's third term.
  (R11) A2.  The power-sum bounds that the database's Table 11.2 gives with a range.  Ford's 58.05 (1 - sigma)^{1/2},
       stated for 1/2 <= sigma <= 1, gives more than 31 at sigma = 5/7 (exactly: 58.05^2 (2/7) > 31^2 > (7/3)^2).
       Heath-Brown's 6.42 (1 - sigma)^{1/2} and Pintz's 3 sqrt(2) (1 - sigma)^{1/2} + 18 (1 - sigma) are stated for
       sigma >= 9/10 and sigma >= 17/18, above 5/7.
  (R12) Cores 3 and 4 against zeta.  The database's moment exponents M(1/2, A) (its chapter 9) and its large-values
       bound from exponent pairs (its Lemma 8.11), for the t-aspect analogues:
       (R12a) Lemma 9.4 (M(1/2, 4) = 1) and Theorem 9.7 (M(1/2, 12) <= 2), interpolated by Lemma 9.2(ii) (a(M(1/a) - 1)
              convex in a), give M(1/2, A) <= 1/2 + A/8 on 4 <= A <= 12; at A = 6 that is 5/4, a sixth moment with
              loss 1/4 > 1/6.
       (R12b) The count of 1-spaced t in [T, 2T] with |zeta(1/2 + it)| >= T^{1/12} is at most T^{M(1/2, A) - A/12}.
              On 4 <= A <= 12 the interpolated bound gives 1/2 + A/24, least (2/3) at A = 4.  Theorem 9.10's thirteen
              linear pieces, from A = 866/65 on, each have slope above 1/12 and give more than 2/3 at both ends (the
              last piece at its left end), and its form for 12 < A <= 12 + 86/65 gives at least 1.
       (R12c) Theorem 9.8's proof bounds the count at height V by T^{o(1)} (T V^{-6} + T^5 V^{-32}); at V = T^{1/12} the
              second term is T^{7/3}.
       (R12d) A dyadic piece of length N = T^{1/tau} (tau >= 2) is large at sigma = 1/2 + tau/12.  Lemma 8.11 with an
              exponent pair (k, ell), k > 0, gives LV_zeta/tau = max(1/2, (4k + 4 ell - 1)/(6k)), which exceeds 2/3 by
              (4 ell - 1)/(6k) > 0; checked at the seven exponent pairs of (R10) and tau = 2, ..., 12.
  (R13) C7 and C9 (README round 547).
       (R13a) A fourth moment twisted by |M_X|^4, sharp for X^2 <= q^{1/4} (x <= 1/8), gives the class-II line
              1 - 4y(sigma - 1/2), without FMx's 2x.  At sigma = 5/7 it is at most 2/3 exactly when y >= 7/18, and for
              x <= 1/8 the blocks [x, y] then contain 7/18, a point of the barrier.
       (R13b) Core 4 through the approximate functional equation.  A piece of length M = q^m is large at
              M^{1/2} q^a.  Its cube's mean value counts such characters by (q + M^3) q^{-6a}, below q^{1 - 4a} exactly
              when m < (1 + 2a)/3; that is 7/18 at a = 1/12, above 1/4.
       (R13c) At M = q^{1/2} and a = 1/12 the square has length q and value q^{2/3}: there the density term and the
              mean value theorem's second term both equal 2/3.  Unsquared (tau = 2, sigma = 2/3) a count below q^{2/3}
              needs LV < 4/3; the mean value theorem gives 5/3, Huxley 2 and Guth-Maynard's Theorem 1.1 26/15.
  (R14) B15 and C10, two routes to SIX(delta) at N = q^{7/18} (README round 548).
       (R14a) Sum |D|^6 <= max |D|^2 Sum |D|^4 <= max |D|^2 (q + N^2) N^2 is below q^{-delta} N^6 exactly when
              max |D| < q^{5/18 - delta/2}.  Burgess's exponent (1 - 1/r)(7/18) + (r + 1)/(4r^2) is least at r = 4,
              71/192, above 5/18 for r = 1, ..., 12; Polya-Vinogradov's is 1/2.  The Lindelof exponent 7/36 is below 5/18.
       (R14b) Equidistribution in every class mod q with a saving q^{-delta'} gives Sum_{chi != chi_0} |D|^6
              <= q^2 (X/q)^2 q^{-2 delta'} = N^6 q^{-2 delta'}, X = N^3 = q^{7/6}: level of distribution 6/7.
              Fouvry-Kowalski-Michel's levels for d_3, 1/2 + 1/46 (prime moduli) and 1/2 + 1/34 (averaged), are below.
  (R15) A1, C11 and C12 (README round 549).
       (R15a) Bourgain-Garaev-Konyagin-Shparlinski's Theorem 19 has e_3 = max(3^2 - 2*3 - 2, 3^2 - 3*3 + 4) = 4 and
              bounds K_3 by (h^3/p^{3/4} + 1) h^{3+o(1)}; at h = q^{7/18} that is q^{19/12}, above the expected q^{4/3}.
       (R15b) A sixth moment averaged over the moduli q <= Q, at most Q^{2+o(1)}, bounds one modulus's sixth moment by
              q^{2+o(1)}: loss 1, against the Weyl bound's 1/3 and the needed 1/6.
       (R15c) The explicit formula with support s, if every zero off the line contributed positively, would give
              A1's exponent at theta = s/2: (1 - (2 sigma - 1) s/2)/(1 - sigma), which is 2 at s = 2 for every sigma.
  (R16) B13 with Heath-Brown's double-sum bound (README round 551).  The bound
       sum_{r,s <= R} |sum_{n <= N} alpha_n chi_r(n) conj(chi_s(n))|^2 <= (N^2 R + N R^2 + N R^{5/4} q^{1/2}) q^{o(1)}
       has its last two terms equal exactly at R = q^{2/3} (exponents n + 4/3 both), and the third below the second
       for R above q^{2/3} on a grid.  The first term, the diagonal's N^2 R, is below N R^2 at R = q^{2/3} for the
       length q^{7/18} and above it for the length q^{7/9}: the bound gives ||E||_F^2 <~ N R^2 only when R >= N.
       Halasz-Montgomery with ||E||_op <= ||E||_F then gives R V^2 <= N^2 + N^{3/2} R, so R <= 2 N^2/V^2 once
       V^2 > 2 N^{3/2}: sigma > 3/4, and 10/7 < 3/2 at sigma = 5/7.
  (R17) Round 552's entries.
       (R17a) A1 at theta = 51/101, the twist length of Bui-Pratt-Robles-Zaharescu's asymptotic: Selberg's exponent
              is 277/101 > 7/3.  At theta = 7/9 it is exactly 7/3.
       (R17b) C14.  With the twist S(chi)^2 of length q^{2 nu}, nu = 7/18, a twisted second moment
              sum_chi |L(1/2 + it, chi)|^2 |S(chi)|^4 << q^{1 + eta} N^2 counts |S| >= N^{5/7} (so |L| >= q^{1/12},
              and N^{5/7 - 1/2} = q^{1/12}) by q^{1/2 + eta}: below q^{2/3} iff eta < 1/6.  The large sieve gives
              eta = 1/2 + 2 nu - 1 = 5/18, a gap of 1/9; the twist length 7/9 exceeds 51/101.  Through Mellin the same
              bound gives sum |S|^6 << q^{1 + eta} N^3, which at eta = 1/6 is q^{7/3} = N^6: SIX's threshold.
       (R17c) E2's levels for S_3 at the critical point (|W| = q^{2/3}, N = q^{7/9}): discarding the Jacobi phases,
              N^{3/2} q^2 = q^{19/6} (seven_thirds.py (P)); Chen-Gupta-Li's q^2 |W|^{3/2} = q^3; independent random
              phases on the q^2 pairs, N^{3/2} q = q^{13/6}.
       (R17d) E4.  The dual of the smooth sum at N = q^{7/18} has length M = q^{11/18} and threshold
              q^{1/2} N^{-2/7} = q^{7/18}.  The mean value theorem for its fourth power, (q + M^2) M^2, gives q^{8/9};
              Poisson's isometry, sum_{chi != chi_0} |D|^4 = (q/N^2)^2 sum |S|^4 = q^{3 - 2 nu}, gives q^{2/3}.
  (R18) E2's net-state note (README round 553).  For fixed chi_2 and m, the Jacobi sums in S_3 form a weighted bilinear
       sum over the product set (W conj chi_2) x (chi_2 conj W), with |W| = q^{2/3} on each side, inside the range
       |X| > q^{1/2 + eps} of Xi's equidistribution theorem.  Parseval saves (|X||Y|/q)^{1/2} = q^{1/6} over the
       trivial bound.  Summed over chi_2 in W and the M = q/N values of m with that bound, S_3 << N q |W|^2,
       which at N = q^{7/9} is q^{28/9} > q^3.
  (R19) Round 554's entries, at sigma = 5/7, N = q^{7/9}, |W| = q^{2/3}, V = N^{5/7} and M = q/N.
       (R19a) B10.  The large sieve gives |W| <= q N/V^2 = q^{2/3}; Chen-Gupta-Li's S_3 bound, read as
              Delta - N <~ q^{2/3}|W|^{1/2}, is q at |W| = q^{2/3}.  Gershgorin with the coherence sqrt(q)/N gives
              |W| sqrt(q)/N = q^{7/18} > M = q^{2/9}, and |W| exceeds the square-root bottleneck N/sqrt(q) = q^{5/18}.
       (R19b) B16.  The flat route needs Theta <= q^{1 - 7/9 - 1/9} = q^{1/9}, hence no progression longer than q^{2/9}.
              The chirp's progression has length N/(sqrt(q) log q), exponent 5/18 > 2/9, and l sqrt(q) = N there; the
              Fejer bound's limit is N^2/V^2 = q^{4/9}, valid since V^2 = q^{10/9} exceeds q.  The halves of a progression
              of even length l <= 60 have E(A, B) = l(l^2 + 2)/12, by brute force.
       (R19c) B17.  The integer-relation bound |W| (kappa - 1)^{1/4} h^{1/2} at h = q^{1/2} is q^{11/12} < q, and q
              exactly at the largest energy kappa = L/|W| = q^{1/3}.
  (R20) Round 555's entries.
       (R20a) B18, the excess-energy lemma, at the critical block N0 = q^{7/18} with |W| = q^{2/3} and V0 = N0^{5/7}.
              (2 N0)^2 < q, since 7/9 < 1.  The floor N0^{8 sigma - 6} has exponent -1/9, against the least value
              q^{-1/3} that kappa - 1 takes for any W of size q^{2/3}: a factor q^{2/9}.  The excess
              (kappa - 1)|W|^4/L then has exponent 14/9, which is Proposition 10.2's first term |W| N^{4 - 4 sigma} at
              N = N0^2.  On a grid of (sigma, nu, w) the two exponents 4w - 1 + nu(8 sigma - 6) and
              w + 2 nu(4 - 4 sigma) agree exactly when 3w = 1 + nu(14 - 16 sigma).  The Cauchy-Schwarz form
              |W|^2 V0^4/N0^2 has exponent 5/3, against the random level N0^2 |W| at 13/9.  The height thresholds:
              V0^2/N0 = N0^{3/7} is q^{1/6}; the Hoelder form's (V0^2/N0)^2 at kappa = q^{o(1)} is q^{1/3}, below
              the block's largest height exponent 7/18.
       (R20b) B19, the Gauss-sum transfer.  At length N = q^l, the threshold V^2 = q^{1/3} N, i.e.
              sigma(l) = 1/2 + 1/(6l), makes the mean value theorem's (q + N)N/V^2 exactly q^{2/3} for every l < 1, and
              sigma(7/9) = 5/7.  A bound ||T'_W|| <= q^{1 - delta} gives |W| <= (N + q^{1 - delta})/q^{1/3}, below
              q^{2/3 - delta/2} for l <= 1 - delta; the density hypothesis value N^{2 - 2 sigma(l)} = q^{l - 1/3} reaches
              q^{2/3 - delta} at l = 1 - delta.  A random set has ||T'_W||/L about 2 alpha^{1/2}, alpha = |W|/L, which
              is q^{-1/6} at |W| = q^{2/3}; the annihilator of a subgroup of order q^{1/3} has |W| = q^{2/3} and the
              largest energy, kappa = |H| = q^{1/3}.
  (R21) Round 556's entries, at the critical block N0 = q^{7/18}, |W| = q^{2/3}, V0 = N0^{5/7}, and its square.
       (R21a) B20.  A large-values set of the square needs the top eigenvalue |W| V0^4/N0^2 = q of the Hadamard square
              G o G of the block's Gram matrix; Schur's bound N0 lambda(G) then needs lambda(G) >= q^{11/18}.  The block's
              own large values need |W| V0^2/N0 = q^{5/6}, and 11/18 < 5/6 < 1.
       (R21b) B21.  The large-spectrum bound kappa >= delta^4 N0, with delta = V0/N0 = q^{-1/9}, has exponent -1/18 < 0.
       (R21c) B22.  Lemma 10.5 at the block: its diagonal N0 |W|^3/V0^2 has exponent 11/6, a factor q^{1/6} above the
              least energy |W|^4/L at 5/3.  At the square the diagonal |W|^3 N^{1 - 2 sigma} is exactly 5/3.
       (R21d) B23.  Without slack the self-consistent bound X <= (N^{2 - 2 sigma}|W|^{1/2})^2 gives the excess exponent
              14/9, B18's floor.  With |W| = q^{2/3 - d} on a grid of d in [0, 1/3]: the slack exponent 5/3 - 3d exceeds
              the floor 14/9 - 4d (the constant-factor slack at d = 0 included), and the off-diagonal term 14/9 - d
              meets the floor only at d = 0.
  (R22) Round 557's entries.
       (R22a) B25.  The free-probability (tree) part of the 2k-th moment of the Gauss-sum matrix gives
              ||T'_W|| <= q^{1/2}|W|^{(k+1)/(2k)}: exponent 1 at k = 2, 17/18 at k = 3, and 5/6 in the limit.  At
              k = 3 a large-values set at the critical point has |W| <= q^{11/18}, and the self-consistent bound is
              q^{1/2}.  The six-cycle's tree part q^3|W|^4 has exponent 17/3; the flat bound q q^4 |W|^3 exceeds it
              by q^{4/3}, and square-root cancellation (exponent 5) would suffice.  On the four-cycle, Cauchy-Schwarz
              and Hoelder both give exponent 10/3, above the tree part's 3.
       (R22b) B26.  The interval's multiplicative k-energy N^k/q (normalized) has exponent 7k/9 - 1, at least the
              (k - 1)/3 that spectral concentration on |W| = q^{2/3} forces, for k = 2, ..., 12; they meet at
              k = 3/2.  A support of size s needs structure beyond wrapping only for s < q^{(k+2)/(3k)}, which is
              q^{2/3} at k = 2.
       (R22c) D4.  The critical zeros, q^{2/3} of them at beta = 5/7, contribute q^{2/3} x^{5/7}, which is x at
              x = q^{7/3}; at x = q^{7/3 - delta} the twisted sum needs a saving q^{2 delta/7} (checked at
              delta = 1/10).

Scope.  This checks arithmetic only.  It does not check the analysis behind any closure, nor that a transplanted
t-aspect theorem holds over the characters mod q.  To show the checks can fail, the script runs thirty-three mutations, at
least one aimed at each check, and requires each mutation to fail at least one check.
"""
from fractions import Fraction as F

import seven_thirds as st

S57 = F(5, 7)
T23 = F(2, 3)


def grid(a, b, n):
    return [a + (b - a) * F(i, n) for i in range(n + 1)]


# (R1) Selberg's method.
def selberg(s, theta, mut=None):
    if mut == "Selberg's mollifier exponent doubled":
        theta = 2 * theta
    return (1 - (2 * s - 1) * theta) / (1 - s)


def check_R1(mut=None):
    fails = []
    if selberg(S57, F(1, 2), mut) != F(11, 4):
        fails.append(f"R1: f(5/7, 1/2) = {selberg(S57, F(1, 2), mut)}, not 11/4")
    if selberg(S57, F(7, 9), mut) != F(7, 3):
        fails.append(f"R1: f(5/7, 7/9) = {selberg(S57, F(7, 9), mut)}, not 7/3")
    for th in sorted(set(grid(F(0), F(1), 180) + [F(7, 9)])):
        if (selberg(S57, th, mut) < F(7, 3)) != (th > F(7, 9)):
            fails.append(f"R1: theta = {th}")
    return fails


# (R2) The auxiliary modulus and a larger T.
def cgl_sub_exponent(eta, tau, mut=None):
    q1 = eta if mut == "the subdivision modulus q1 read as r" else F(1)
    return (1 + eta) + q1 / 3 + tau


def check_R2(mut=None):
    fails = []
    crit = F(7, 9) * (2 - 4 * S57)
    for eta in grid(F(0), F(1, 4), 25):
        for tau in grid(F(0), F(1, 4), 25):
            e = cgl_sub_exponent(eta, tau, mut)
            if e != F(4, 3) + eta + tau:
                fails.append(f"R2: exponent at eta = {eta}, tau = {tau}")
            v = e + crit
            if v != F(2, 3) + eta + tau:
                fails.append(f"R2: critical value at eta = {eta}, tau = {tau}")
            if (v > T23) != (eta > 0 or tau > 0) or (v == T23) != (eta == 0 and tau == 0):
                fails.append(f"R2: comparison at eta = {eta}, tau = {tau}")
    return fails


# (R3) Burgess summed over the characters.
def burgess_lv_exponent(r, mut=None):
    n, v = F(7, 18), F(7, 18) * S57
    e = (2 * r - 1) * n + 1 + F(1, r) - (2 * r + 1) * v
    if mut == "the Burgess form loses its q^{1/r}":
        e -= F(1, r)
    return e


def check_R3(mut=None):
    fails = []
    for r in range(1, 11):
        e = burgess_lv_exponent(r, mut)
        if e != F(2 * r - 6, 9) + 1 + F(1, r):
            fails.append(f"R3: closed form at r = {r}")
        if not e > 1:
            fails.append(f"R3: exponent {e} <= 1 at r = {r}")
        if r >= 3 and not (F(2 * r - 6, 9) >= 0 and F(1, r) > 0):
            fails.append(f"R3: sign split at r = {r}")
        if (F(7, 18) * S57 - F(1, r) >= 0) != (r >= F(18, 5)):
            fails.append(f"R3: A >= 1 at r = {r}")
    return fails


# (R4) Amplification.
def check_R4(mut=None):
    fails = []
    rho = T23
    for lam in grid(F(0), F(2), 120):
        off = rho + lam / 2 if mut == "the amplifier's off-diagonal without the square root on R" else (rho + lam) / 2
        if (off < lam) != (lam > rho):
            fails.append(f"R4: lam = {lam}")
    return fails


# (R5) Pointwise Burgess thresholds at V = N^{5/7}.
def check_R5(mut=None):
    fails = []
    want = {1: F(7, 10), 2: F(7, 8), 3: F(7, 3)}
    for r in range(1, 11):
        a, b = F(r + 1, 4 * r * r), F(1, r) - (1 - S57)
        if mut == "Burgess's q-exponent read as (r + 1)/(4r)":
            a = F(r + 1, 4 * r)
        if r <= 3:
            c = a / b
            if c != want[r]:
                fails.append(f"R5: c_{r} = {c}, not {want[r]}")
            for nu in grid(F(0), F(3), 150):
                if ((1 - F(1, r)) * nu + a < S57 * nu) != (nu > c):
                    fails.append(f"R5: r = {r}, nu = {nu}")
        else:
            if not b < 0:
                fails.append(f"R5: 1/r - 2/7 = {b} at r = {r}")
            if any((1 - F(1, r)) * nu + a < S57 * nu for nu in grid(F(0), F(3), 150)):
                fails.append(f"R5: bound below N^(5/7) at r = {r}")
    if not want[3] > 1:
        fails.append("R5: c_3 <= 1")
    return fails


# (R6) Frobenius room.
def frobenius_room(s, mut=None):
    """log_N of ||E||_F^2 / lam^2 with ||E||_F^2 = K^2 N and lam = K N^{2s-1} (the K's cancel)."""
    r = 1 - 2 * (2 * s - 1)
    if mut == "the room counted with the norm, not its square":
        r = r / 2
    return r


def check_R6(mut=None):
    fails = []
    room = frobenius_room(S57, mut)
    if room != 3 - 4 * S57 or room != F(1, 7):
        fails.append(f"R6: room exponent {room}")
    if F(7, 9) * room != F(1, 9):
        fails.append(f"R6: long room q^{F(7, 9) * room}")
    if F(7, 18) * room != F(1, 18):
        fails.append(f"R6: short room q^{F(7, 18) * room}")
    return fails


# (R7) The sixth-moment loss and Zacharias's saving.
def check_R7(mut=None):
    fails = []
    n = F(7, 20) if mut == "the critical block read as q^{7/20}" else F(7, 18)
    if 1 + 3 * n != F(13, 6) or 6 * n != F(7, 3):
        fails.append("R7: diagonal or off-diagonal exponent")
    for th in grid(F(0), F(1, 2), 150):
        if (F(13, 6) + th < F(7, 3)) != (th < F(1, 6)):
            fails.append(f"R7: theta' = {th}")
    if F(1, 14) - 3 * F(7, 64) / 7 != F(11, 448):
        fails.append("R7: Zacharias eta")
    return fails


# (R8) d_3 in progressions.
def check_R8(mut=None):
    c, k = (2 if mut == "X counted with two factors" else 3) * F(7, 18), 3
    fails = []
    if c != F(7, 6):
        fails.append(f"R8: X = q^{c}")
    if not (c < k - 1 and c < k - F(1, 2)):
        fails.append("R8: ranges")
    return fails


# (R9) Huxley and Halasz-Montgomery at sigma = 5/7.
def hux_interval(s, t, mut=None):
    if mut == "Huxley's slope read as the mean value theorem's":
        return st.good_interval("MVT", s, t)
    return st.good_interval("HUX", s, t)


def check_R9(mut=None):
    fails = []
    if hux_interval(S57, T23, mut) != (F(7, 6), F(7, 6)):
        fails.append(f"R9: Huxley's good set at t = 2/3 is {hux_interval(S57, T23, mut)}")
    for t in grid(F(1, 3), T23, 60)[:-1]:
        if hux_interval(S57, t, mut) is not None:
            fails.append(f"R9: Huxley's good set nonempty at t = {t}")
    if not 4 - 6 * S57 > 1 - 2 * S57:
        fails.append("R9: slopes")
    for t in grid(F(1, 2), F(1), 100):
        h, m = hux_interval(S57, t, mut), st.good_interval("MVT", S57, t)
        if h is not None and not (m is not None and m[0] <= h[0] and h[1] <= m[1]):
            fails.append(f"R9: Huxley's good set not inside the mean value theorem's at t = {t}")
    if st.good_interval("MVT", S57, T23) != (F(7, 9), F(7, 6)):
        fails.append("R9: the mean value theorem's window")
    l_hp = F(5, 12) / (2 * S57 - 1 - F(1, 12))
    if l_hp != F(35, 29) or not l_hp > F(7, 6):
        fails.append(f"R9: half-plane threshold {l_hp}")
    return fails


# (R10) Large-values theorems of the exponent database, transplanted.
def lv_mvt(s, tau):
    return max(2 - 2 * s, 1 + tau - 2 * s)                                 # Theorem 7.9


def lv_hux(s, tau):
    return max(2 - 2 * s, 4 + tau - 6 * s)                                 # Theorem 7.12


def lv_hb(s, tau):
    return max(2 - 2 * s, 10 + tau - 13 * s)                               # Theorem 7.14


def lv_hb_pre(s, tau, rho):
    return max(2 - 2 * s, F(11, 12) * rho + F(3, 2) + tau / 6 - 2 * s)    # Theorem 7.13, given LV <= rho


def lv_jutila(s, tau, k):
    return max(2 - 2 * s, tau + (4 - F(2, k)) - (6 - F(2, k)) * s, tau + (6 - 8 * s) * k)   # Theorem 7.16


def lv_ep(s, tau, k, ell):
    return max(2 - 2 * s, 2 - 2 * s + tau - (2 * s + k - ell - 1) / k)     # Corollary 7.11


def lv_gm(s, tau, mut=None):
    third = tau + F(12, 5) - 4 * s
    if mut == "Guth-Maynard's third term loses its tau":
        third = F(12, 5) - 4 * s
    return max(2 - 2 * s, F(18, 5) - 4 * s, third)                         # Theorem 10.27


def gm2_terms(s, tau, k):
    """The eight terms of Theorem 10.28 (10), for 1/2 < s < 1 and tau >= 1."""
    return [2 - 2 * s, 5 - 6 * s,
            (4 - 6 * s) * F(k, k + 1) + F(k, k + 1) * tau,
            (5 - 6 * s) * F(4 * k, 4 * k + 3) + F(2, 4 * k + 3) * tau,
            2 - 4 * s + F(4, 3) * tau, 3 - 4 * s + tau / 2,
            F(9, 2) - 7 * s + tau, (72 - 112 * s) / 19 + F(18, 19) * tau]


def bourgain_simplified_floor(s, tau):
    """A lower bound for Corollary 10.30's right side over all alpha_1, alpha_2 >= 0, or None outside its
    hypothesis (rho <= min(1, 4 - 2 tau) must allow some rho >= 0).  The last two terms alone give it:
    min over a >= 0 of max(c1 - 2a, c2 + 4a)."""
    if 4 - 2 * tau < 0:
        return None
    c1 = tau + 12 - 16 * s
    c2 = 2 + max(F(1), 2 * tau - 2) - 4 * s
    return (2 * c1 + c2) / 3 if c1 >= c2 else c2


# Table 10.1: (rho_0, region) with each region a list of affine forms that must be >= 0.
BOURGAIN_ROWS = [
    (lambda s, u: F(16, 3) - F(20, 3) * s + u / 3,
     [lambda s, u: -1 + u, lambda s, u: 10 - 14 * s + u, lambda s, u: 4 + 4 * s - 5 * u,
      lambda s, u: -11 + 16 * s - u]),
    (lambda s, u: 5 - 7 * s + F(3, 4) * u,
     [lambda s, u: 8 - 8 * s - u, lambda s, u: -16 + 20 * s + u / 3, lambda s, u: -6 + 10 * s - F(7, 6) * u,
      lambda s, u: -4 - 4 * s + 5 * u]),
    (lambda s, u: 3 - 5 * s + u,
     [lambda s, u: -8 + 8 * s + u, lambda s, u: 2 - 6 * s + 2 * u, lambda s, u: -10 + 14 * s - F(2, 3) * u,
      lambda s, u: 6 - 2 * s - 2 * u]),
    (lambda s, u: -4 * s + 2 * u,
     [lambda s, u: -6 + 2 * s + 2 * u, lambda s, u: -12 + 12 * s + u, lambda s, u: 1 - s]),
    (lambda s, u: 8 - 12 * s + F(4, 3) * u,
     [lambda s, u: 15 - 21 * s + u, lambda s, u: 12 - 12 * s - u, lambda s, u: -F(3, 2) + u,
      lambda s, u: 6 - 10 * s + F(7, 6) * u]),
    (lambda s, u: 2 - 2 * s,
     [lambda s, u: 1 - s, lambda s, u: -10 + 14 * s - u, lambda s, u: -1 + u, lambda s, u: -2 + 6 * s - 2 * u]),
    (lambda s, u: 9 - 12 * s + F(2, 3) * u,
     [lambda s, u: F(3, 2) - u, lambda s, u: -F(1, 2) + s, lambda s, u: -1 + u, lambda s, u: 11 - 16 * s + u,
      lambda s, u: 16 - 20 * s - u / 3]),
]


def bourgain_rows(s, tau):
    """rho_0 of each row of Table 10.1 whose region contains (s, tau); the table is for tau >= 1."""
    if tau < 1:
        return []
    return [r(s, tau) for r, region in BOURGAIN_ROWS if all(g(s, tau) >= 0 for g in region)]


def kerr5_floor(s, tau):
    """Kerr's Theorem 5 needs -alpha < -tau + 8s - 5, so its first term 2 - 2s + alpha exceeds 7 + tau - 10s.
    None outside 1/2 < s <= 1, 0 <= tau <= 3/2, and None for tau < 8s - 5: there the transcribed condition admits
    alpha < 0, and the bound would fall below the database's lower bound min(2 - 2s, tau) (its Lemma 7.5)."""
    if not (F(1, 2) < s <= 1 and 0 <= tau <= F(3, 2)) or tau < 8 * s - 5:
        return None
    return 2 - 2 * s + (tau - 8 * s + 5)


EXPONENT_PAIRS = [(F(1, 2), F(1, 2)), (F(1, 6), F(2, 3)), (F(1, 14), F(11, 14)), (F(2, 7), F(4, 7)),
                  (F(1, 30), F(13, 15)), (F(11, 30), F(8, 15)), (F(13, 84) + F(1, 10**6), F(55, 84) + F(1, 10**6))]


def transplant(lv, l, mut=None):
    """F(l) = l LV(sigma, 1/l): T replaced by the conductor Q = N^{1/l}."""
    v = lv(1 / l)
    if v is None:
        return None
    return v if mut == "the transplant drops the factor l" else l * v


def B_points():
    return [F(7, 18), F(7, 9)] + [F(7, 6) + F(i, 6) for i in range(0, 25)]


def check_R10(mut=None):
    fails, info = [], {}
    s = S57
    # (R10a)
    for s0 in grid(F(1, 2), F(11, 12), 20):
        for l in grid(F(1, 20), F(3), 59):
            if transplant(lambda u: lv_mvt(s0, u), l, mut) != st.F_at("MVT", s0, l):
                fails.append(f"R10a: MVT at s = {s0}, l = {l}")
            if transplant(lambda u: lv_hux(s0, u), l, mut) != st.F_at("HUX", s0, l):
                fails.append(f"R10a: HUX at s = {s0}, l = {l}")
    # (R10b)
    for l in B_points()[2:]:                   # the tail: the database's lower bound min(2 - 2s, tau) (Lemma 7.5)
        if not min(2 * l * (1 - s), F(1)) >= T23:
            fails.append(f"R10b: Lemma 7.5's floor below 2/3 at l = {l}")
    shapes = {"Heath-Brown (7.14)": [lambda u: lv_hb(s, u)]}
    shapes["Jutila (7.16)"] = [lambda u, k=k: lv_jutila(s, u, k) for k in range(1, 13)]
    shapes["exponent pairs (7.11)"] = [lambda u, k=k, e=e: lv_ep(s, u, k, e) for k, e in EXPONENT_PAIRS]
    shapes["Guth-Maynard (10.28)"] = [lambda u, k=k: (max(gm2_terms(s, u, k)) if u >= 1 else None)
                                      for k in range(1, 13)]
    shapes["Bourgain (10.30) floor"] = [lambda u: bourgain_simplified_floor(s, u)]
    shapes["Bourgain (10.31) rows"] = [lambda u: (min(bourgain_rows(s, u)) if bourgain_rows(s, u) else None)]
    shapes["Kerr Thm 5 (10.32) floor"] = [lambda u: kerr5_floor(s, u)]
    for name, lvs in shapes.items():
        used = 0
        for lv in lvs:
            for l in B_points():
                v = transplant(lv, l, mut)
                if v is None:
                    continue
                used += 1
                if v < T23:
                    fails.append(f"R10b: {name} gives F({l}) = {v} < 2/3")
        if used == 0:
            fails.append(f"R10b: {name} applies at no point of B")
        info[name] = used
    for l in B_points():                       # Theorem 7.13, fed with any valid rho <= tau
        tau = 1 / l
        if not F(18) + 2 * tau - 24 * s > tau:
            fails.append(f"R10b: Heath-Brown (7.13) could improve at l = {l}")
        if transplant(lambda u: lv_hb_pre(s, u, u), l, mut) < T23:
            fails.append(f"R10b: Heath-Brown (7.13) at rho = tau, l = {l}")
    for k, e in EXPONENT_PAIRS:
        slope = 2 - 2 * s - (2 * s + k - e - 1) / k              # F = 1 + slope * l
        if slope - (1 - 2 * s) != (e - (2 * s - 1)) / k or not slope > 1 - 2 * s:
            fails.append(f"R10b: exponent pair ({k}, {e}) slope")
    # (R10c)
    gm = transplant(lambda u: lv_gm(s, u, mut), F(7, 9), mut)
    info["Guth-Maynard (10.27) F(7/9)"] = gm
    if gm != F(29, 45) or not gm < T23:
        fails.append(f"R10c: Guth-Maynard (10.27) F(7/9) = {gm}")
    # (R10d)
    l = F(7, 9)
    tau = 1 / l
    best = None
    for k in range(1, 13):
        terms = [l * x for x in gm2_terms(s, tau, k)]
        if terms[4] != T23:
            fails.append(f"R10d: the 4/3-term is {terms[4]} at k = {k}")
        if terms[4] != st.terms("P31", s)[1][2][0] + st.terms("P31", s)[1][2][1] * l:
            fails.append("R10d: the 4/3-term differs from P31's third term")
        others = terms[:4] + terms[5:]
        if k <= 5 and not all(x < T23 for x in others):
            fails.append(f"R10d: another term reaches 2/3 at k = {k}")
        if k >= 6 and not terms[2] >= T23:
            fails.append(f"R10d: the k-term is below 2/3 at k = {k}")
        m = max(terms)
        best = m if best is None else min(best, m)
    info["Guth-Maynard (10.28) min over k of F(7/9)"] = best
    if best != T23:
        fails.append(f"R10d: least value {best}")
    return fails, info


# (R11) Power sums.
def check_R11(mut=None):
    fails = []
    c = F(405, 100) if mut == "Ford's constant read as 4.05" else F(5805, 100)
    if not (c * c * (1 - S57) > 31 * 31 > F(7, 3) ** 2):
        fails.append(f"R11: Ford's bound at 5/7 is not above 31 (C = {c})")
    if not (F(9, 10) > S57 and F(17, 18) > S57):
        fails.append("R11: ranges")
    return fails


# (R12) Cores 3 and 4 against zeta.
GM_PIECES = [   # Theorem 9.10: (slope, intercept, left end) of M(1/2, A) <= slope A + intercept
    (F(16, 114), F(35, 114), F(866, 65)),
    (F(176677, 1246476), F(358428, 1246476), F(14)),
    (F(779, 5422), F(1398, 5422), F(122304, 7955)),
    (F(3 * 1661, 34532), F(3 * 2856, 34532), F(910020, 58699)),
    (F(405277, 2800950), F(677194, 2800950), F(9604, 593)),
    (F(40726597, 280113282), F(64268678, 280113282), F(629068, 35731)),
    (F(3 * 46, 926), F(3 * 49, 926), F(13789, 709)),
    (F(3475, 23168), F(3236, 23168), F(204580, 10333)),
    (F(7 * 39945, 1857036), F(7 * 33704, 1857036), F(4252, 195)),
    (F(37, 244), F(24, 244), F(812348, 30267)),
    (F(31, 196), F(-24, 196), F(440, 13)),
    (F(7 * 31519, 1385180), F(-7 * 33704, 1385180), F(203087, 4742)),
    (F(13, 84), 1 - F(13 * 6, 84), F(3516129, 65729)),
]


def interp_moment(A, mut=None):
    """M(1/2, A) <= 1/2 + A/8 on [4, 12], from M(1/2, 4) = 1 and M(1/2, 12) <= 2."""
    hi = F(5, 2) if mut == "the twelfth moment read as T^{5/2}" else F(2)
    return 1 + (hi - 1) * (A - 4) / 8


def check_R12(mut=None):
    fails = []
    a = F(1, 12)
    # (R12a)
    for A in grid(F(4), F(12), 80):
        if interp_moment(A, mut) != F(1, 2) + A / 8:
            fails.append(f"R12a: interpolation at A = {A}")
    if interp_moment(F(6), mut) != F(5, 4) or not interp_moment(F(6), mut) - 1 > F(1, 6):
        fails.append("R12a: the sixth moment")
    # (R12b)
    vals = [interp_moment(A, mut) - a * A for A in grid(F(4), F(12), 80)]
    if min(vals) != F(2, 3) or vals[0] != F(2, 3) or not all(v > F(2, 3) for v in vals[1:]):
        fails.append(f"R12b: interpolated count, least {min(vals)}")
    ends = [p[2] for p in GM_PIECES[1:]] + [None]
    for (sl, ic, lo), hi in zip(GM_PIECES, ends):
        if not sl > a:
            fails.append(f"R12b: slope {sl} at A >= {lo}")
        for A in ([lo] if hi is None else [lo, hi]):
            if not sl * A + ic - a * A > F(2, 3):
                fails.append(f"R12b: Theorem 9.10 at A = {A}")
    for d in grid(F(0), F(86, 65), 40)[1:]:
        if not 2 + d / 8 - a * (12 + d) >= 1:
            fails.append(f"R12b: the 12 + delta form at delta = {d}")
    # (R12c)
    if 5 - 32 * a != F(7, 3):
        fails.append("R12c: second term")
    # (R12d)
    for k, e in EXPONENT_PAIRS:
        for tau in range(2, 13):
            s0 = F(1, 2) + a * tau
            lv = max(tau - 6 * (s0 - F(1, 2)), (k + e) / k * tau - 2 * (1 + 2 * k + 2 * e) / k * (s0 - F(1, 2)))
            r = lv / tau
            if r != max(F(1, 2), (4 * k + 4 * e - 1) / (6 * k)) or r - F(2, 3) != (4 * e - 1) / (6 * k) or not r > F(2, 3):
                fails.append(f"R12d: pair ({k}, {e}), tau = {tau}")
    return fails


# (R13) Twisted fourth moments as class II, and core 4 through the approximate functional equation.
def check_R13(mut=None):
    fails = []
    s, a = S57, F(1, 12)
    slope = 4 * (s - F(1, 2))
    if mut == "the twisted class-II line keeps FMx's 2x":
        line = lambda x, y: 1 + 2 * x - slope * y
    else:
        line = lambda x, y: 1 - slope * y
    for x in grid(F(0), F(1, 8), 16):
        for y in grid(F(0), F(1, 2), 72):
            if (line(x, y) <= T23) != (y >= F(7, 18)):
                fails.append(f"R13a: x = {x}, y = {y}")
            if line(x, y) <= T23 and not (x <= F(7, 18) <= y):
                fails.append(f"R13a: [x, y] misses 7/18 at x = {x}, y = {y}")
    for m in grid(F(0), F(1, 2), 90):
        cube = max(F(1), 3 * m) - 6 * a
        if (cube < 1 - 4 * a) != (m < (1 + 2 * a) / 3):
            fails.append(f"R13b: m = {m}")
    if (1 + 2 * a) / 3 != F(7, 18) or not F(7, 18) > F(1, 4):
        fails.append("R13b: threshold")
    l, sq = F(1, 2), F(1, 2) + 2 * a                     # the square: length q, value q^{1/2 + 2a}
    if sq != T23 or 2 * 1 * (1 - sq) != T23 or 1 + (1 - 2 * sq) != T23:
        fails.append("R13c: the square at length q")
    sig, tau = F(1, 2) + a / l, 1 / l
    if (sig, tau) != (T23, F(2)) or tau * T23 != F(4, 3):
        fails.append("R13c: the unsquared point")
    if (lv_mvt(sig, tau), lv_hux(sig, tau), lv_gm(sig, tau)) != (F(5, 3), F(2), F(26, 15)):
        fails.append(f"R13c: {lv_mvt(sig, tau)}, {lv_hux(sig, tau)}, {lv_gm(sig, tau)}")
    return fails


# (R14) SIX(delta) by a pointwise bound, and by equidistribution in every class.
def check_R14(mut=None):
    fails = []
    n = F(7, 18)
    need = 2 * n - F(1, 2)                                # max |D| <= q^need: N^2 q^{2 need} q = N^6
    if need != F(5, 18) or not need > n / 2:
        fails.append(f"R14a: needed exponent {need}")
    burg = {r: (1 - F(1, r)) * n + F(r + 1, 4 * r * r) for r in range(1, 13)}
    if mut == "Burgess's q-exponent halved":
        burg = {r: (1 - F(1, r)) * n + F(r + 1, 8 * r * r) for r in range(1, 13)}
    best = min(burg.values())
    if best != F(71, 192) or min(burg, key=burg.get) != 4 or not all(v > need for v in burg.values()):
        fails.append(f"R14a: Burgess {best} at r = {min(burg, key=burg.get)}")
    if not (F(1, 2) > need and n / 2 == F(7, 36) and F(7, 36) < need):
        fails.append("R14a: Polya-Vinogradov or Lindelof")
    X = 3 * n
    level = 1 / X
    if X != F(7, 6) or level != F(6, 7):
        fails.append(f"R14b: X = q^{X}, level {level}")
    if not (level > F(1, 2) + F(1, 46) and level > F(1, 2) + F(1, 34)):
        fails.append("R14b: known levels")
    d = F(1, 100)                                         # q^2 (X/q)^2 q^{-2 delta'} in powers of q
    if 2 + 2 * (X - 1) - 2 * d != 6 * n - 2 * d:
        fails.append("R14b: the variance bound")
    return fails


# (R15) Product congruences, averages over moduli, and the explicit formula.
def check_R15(mut=None):
    fails = []
    nu, n = 3, F(7, 18)
    e3 = max(nu * nu - 2 * nu - 2, nu * nu - 3 * nu + 4)
    if mut == "BGKS's e_3 read as 1":
        e3 = 1
    bound = 2 * nu * n - F(nu, e3)
    if e3 != 4 or bound != F(19, 12) or not bound > 6 * n - 1 or 6 * n - 1 != F(4, 3):
        fails.append(f"R15a: e_3 = {e3}, bound q^{bound}")
    loss = F(2) - 1
    if not (loss == 1 and loss > F(1, 3) > F(1, 6)):
        fails.append("R15b")
    for sg in grid(F(1, 2), F(11, 12), 50)[1:]:
        if selberg(sg, F(1), mut) != 2:
            fails.append(f"R15c: sigma = {sg}")
    return fails


# (R16) Heath-Brown's double-sum bound in B13.
def check_R16(mut=None):
    fails = []
    n = F(7, 18)
    third = (lambda r: n + F(5, 4) * r + F(1, 2)) if mut != "Heath-Brown's R^{5/4} read as R^{3/2}" else \
        (lambda r: n + F(3, 2) * r + F(1, 2))
    second = lambda r: n + 2 * r
    if third(T23) != second(T23) or second(T23) != n + F(4, 3):
        fails.append("R16: the two terms at R = q^{2/3}")
    for r in grid(T23, F(1), 30)[1:]:
        if not third(r) < second(r):
            fails.append(f"R16: third term at R = q^{r}")
    first = (lambda m, r: 2 * m + r) if mut != "the diagonal term read as N R" else (lambda m, r: m + r)
    if not (first(n, T23) < n + 2 * T23 and first(2 * n, T23) > 2 * n + 2 * T23):
        fails.append("R16: the diagonal term against N R^2 at R = q^{2/3}")
    if not (2 * S57 < F(3, 2) and F(3, 4) > S57):
        fails.append("R16: the sigma threshold")
    return fails


# (R17) Round 552: A1 at Bui-Pratt-Robles-Zaharescu's length, C14, E2's levels, E4.
def check_R17(mut=None):
    fails = []
    bprz = F(51, 101) if mut != "BPRZ's length read as q^{7/9}" else F(7, 9)
    if not (selberg(S57, bprz, mut) == F(277, 101) and F(277, 101) > F(7, 3) and selberg(S57, F(7, 9)) == F(7, 3)):
        fails.append("R17a: A1 at theta = 51/101")
    nu = F(7, 18)
    twist = 2 * nu if mut != "the twist's length read as q^{7/18}" else nu
    a = nu * (S57 - F(1, 2))
    count = lambda eta: 1 + eta - 2 * a + nu * (2 - 4 * S57)
    eta_ls = F(1, 2) + twist - 1
    if not (a == F(1, 12) and count(F(1, 6)) == T23 and count(eta_ls) > T23 and eta_ls - F(1, 6) == F(1, 9)
            and twist > F(51, 101) and 1 + F(1, 6) + 3 * nu == 6 * nu):
        fails.append("R17b: the twisted second moment with the twist S^2")
    n2, w = 2 * nu, T23
    trivial, cgl, random = F(3, 2) * n2 + 2, 2 + F(3, 2) * w, F(3, 2) * n2 + 1
    if not (trivial == F(19, 6) and cgl == 3 and random == F(13, 6) and random < cgl < trivial
            and all(st.check_P())):
        fails.append("R17c: the levels of S_3")
    mu, h = 1 - nu, F(1, 2) + nu * (S57 - 1)
    if not (h == F(7, 18) and 2 * mu > 1 and 4 * mu - 4 * h == F(8, 9) and (3 - 2 * nu) - 4 * h == T23):
        fails.append("R17d: the dual's fourth moment")
    return fails


# (R18) Round 553: the bilinear Jacobi sums inside S_3.
def check_R18(mut=None):
    fails = []
    w, n2 = T23, F(7, 9)
    if not (w > F(1, 2) and (w + w - 1) / 2 == F(1, 6)):
        fails.append("R18: Parseval's saving on the product set")
    outer = w + (1 - n2) if mut != "the outer sums read as one term" else F(0)
    per = 1 + w + (1 - n2)
    total = 3 * n2 - 2 + outer + per
    if not (total == F(28, 9) and total > 3 and total == n2 + 1 + 2 * w):
        fails.append("R18: the per-(chi_2, m) bound summed over chi_2 and m")
    return fails


# (R19) Round 554: B10 in compressed-sensing terms, the flat route (B16) and integer relations (B17).
def check_R19(mut=None):
    fails = []
    n, w = F(7, 9), T23
    v, m = S57 * n, 1 - n
    if not (1 + n - 2 * v == w and T23 + w / 2 == 1):
        fails.append("R19a: the large sieve and Chen-Gupta-Li's bound at |W| = q^{2/3}")
    if not (w + F(1, 2) - n == F(7, 18) > m and n - F(1, 2) == F(5, 18) < w):
        fails.append("R19a: Gershgorin and the square-root bottleneck")
    theta = 1 - n - m / 2
    ap = n - F(1, 2) if mut != "the construction's length read as N/V" else n - v
    if not (theta == F(1, 9) and ap > 2 * theta and ap + F(1, 2) == n and 2 * n - 2 * v == F(4, 9) > ap
            and 2 * v > 1):
        fails.append("R19b: the flat threshold against the progressions of large-values sets")
    for ell in range(2, 61, 2):
        r = [0] * ell
        for x in range(ell // 2):
            for y in range(ell // 2, ell):
                r[y - x] += 1
        if sum(c * c for c in r) != F(ell * (ell * ell + 2), 12):
            fails.append(f"R19b: E(A, B) at l = {ell}")
    lemma = w + F(1, 4) if mut != "the integer-relation bound's h^{1/2} read as h" else w + F(1, 2)
    if not (lemma == F(11, 12) and lemma < 1 and lemma + (1 - w) / 4 == 1):
        fails.append("R19c: the integer-relation bound")
    return fails


def check_R20(mut=None):
    fails = []
    nu, w = F(7, 18), T23
    v0 = S57 * nu
    if not (2 * nu < 1):
        fails.append("R20a: the block's ratios do not wrap")
    floor = nu * (8 * S57 - 6) if mut != "the excess-energy exponent read as 8 sigma - 7" else nu * (8 * S57 - 7)
    least = 1 - 2 * w
    excess = 4 * w - 1 + floor
    prop = w + 2 * nu * (4 - 4 * S57)
    if not (floor == F(-1, 9) and least == F(-1, 3) and floor - least == F(2, 9) and excess == F(14, 9) == prop):
        fails.append("R20a: the floor, the least energy and Proposition 10.2's first term")
    for s7 in [F(k, 70) for k in range(36, 70)]:
        for nn in [F(k, 36) for k in range(4, 18)]:
            for ww in [F(k, 12) for k in range(4, 12)]:
                lhs = (4 * ww - 1 + nn * (8 * s7 - 6)) == (ww + 2 * nn * (4 - 4 * s7))
                if lhs != (3 * ww == 1 + nn * (14 - 16 * s7)):
                    fails.append(f"R20a: the agreement criterion at ({s7}, {nn}, {ww})")
    cs, rnd = 2 * w + 4 * v0 - 2 * nu, 2 * nu + w
    if not (cs == F(5, 3) and rnd == F(13, 9) and cs - rnd == F(2, 9)):
        fails.append("R20a: the Cauchy-Schwarz form")
    h1 = 2 * v0 - nu
    h2 = 2 * h1 if mut != "the Hoelder height threshold read without its square" else h1
    if not (h1 == F(1, 6) and h2 == F(1, 3) and h2 < nu):
        fails.append("R20a: the height thresholds")
    third = F(1, 3) if mut != "the critical threshold read as V^2 = q^{1/2} N" else F(1, 2)
    for ell in [F(k, 90) for k in range(10, 90)]:
        sig = F(1, 2) + third / (2 * ell)
        if 1 + ell - 2 * ell * sig != T23:
            fails.append(f"R20b: the mean value theorem at l = {ell}")
            break
        if ell * (2 - 2 * sig) != ell - F(1, 3):
            fails.append(f"R20b: the density hypothesis value at l = {ell}")
            break
    if not (F(1, 2) + third / (2 * F(7, 9)) == S57):
        fails.append("R20b: sigma(7/9)")
    for d in [F(k, 100) for k in range(1, 30)]:
        ell = 1 - d
        if not (max(ell, 1 - d) - F(1, 3) <= T23 - d / 2 and ell - F(1, 3) == T23 - d):
            fails.append(f"R20b: the transfer's consequence at delta = {d}")
    if not (F(1, 2) * (w - 1) == F(-1, 6) and 1 - w == F(1, 3)):
        fails.append("R20b: the random calibration and the annihilator")
    return fails


def check_R21(mut=None):
    fails = []
    nu, w = F(7, 18), T23
    v0 = S57 * nu
    sq_need = w + 4 * v0 - 2 * nu
    schur = sq_need - nu
    block_need = w + 2 * v0 - nu if mut != "the block's large-values need read without |W|" else 2 * v0 - nu
    if not (sq_need == 1 and schur == F(11, 18) and block_need == F(5, 6) and schur < block_need < 1):
        fails.append("R21a: Schur's requirement against the block's own")
    dexp = (S57 - 1) * nu
    bourgain = (4 if mut != "the large-spectrum bound's delta^4 read as delta^2" else 2) * dexp + nu
    if not (dexp == F(-1, 9) and bourgain == F(-1, 18) and bourgain < 0):
        fails.append("R21b: the large-spectrum bound at the critical block")
    least = 4 * w - 1
    bdiag = nu + 3 * w - 2 * v0 if mut != "the block's diagonal read without its factor N0" else 3 * w - 2 * v0
    sdiag = 3 * w + 2 * nu * (1 - 2 * S57)
    if not (least == F(5, 3) and bdiag == F(11, 6) and bdiag - least == F(1, 6) and sdiag == least):
        fails.append("R21c: Lemma 10.5's diagonal at the block and at the square")
    n, floor = 2 * nu, least + nu * (8 * S57 - 6)
    wexp = F(1, 2) if mut != "the uniform-spread bound read with |W| in place of |W|^{1/2}" else 1
    pinned = 2 * (n * (2 - 2 * S57) + wexp * w)
    if not (floor == F(14, 9) and floor - least == F(-1, 9) and pinned == floor):
        fails.append("R21d: the excess pinned at Proposition 10.2's first term")
    for d in [F(k, 90) for k in range(0, 31)]:
        slack, fl, off = least + d - 4 * d, floor - 4 * d, n * (4 - 4 * S57) + w - d
        if not (slack > fl and off >= fl and (off == fl) == (d == 0)):
            fails.append(f"R21d: the slack and the floor at |W| = q^(2/3 - {d})")
            break
    return fails


def check_R22(mut=None):
    fails = []
    w, n, v = T23, F(7, 9), F(5, 9)
    if mut != "the tree part's exponent read as (k + 1)/k":
        tree = lambda k: F(1, 2) + w * F(k + 1, 2 * k)
    else:
        tree = lambda k: F(1, 2) + w * F(k + 1, k)
    if not (tree(2) == 1 and tree(3) == F(17, 18) and F(1, 2) + w / 2 == F(5, 6)):
        fails.append("R22a: the free-probability norms q^{1/2}|W|^{(k+1)/(2k)}")
    if not (tree(3) + n - 2 * v == F(11, 18) and 3 * (F(1, 2) + n - 2 * v) == F(1, 2)):
        fails.append("R22a: the critical counts q^{11/18} and q^{1/2}")
    tr3, flat, sqrt = 3 + 4 * w, 1 + 4 + 3 * w, 1 + 2 + 3 * w
    if not (tr3 == F(17, 3) and flat - tr3 == F(4, 3) and sqrt < tr3):
        fails.append("R22a: the six-cycle's tree part, flat bound and square-root bound")
    cs, hoelder, tree4 = 2 + 2 * w, 1 + 1 + 2 * w, 1 + 3 * w
    if not (cs == hoelder == F(10, 3) and tree4 == 3 and cs > tree4):
        fails.append("R22a: Cauchy-Schwarz and Hoelder on the four-cycle")
    for k in range(2, 13):
        wrapped = n * k - 1 if mut != "the interval's k-energy without its wrap" else F(0)
        if not (wrapped >= F(k - 1, 3) and F(k + 2, 3 * k) <= F(2, 3)):
            fails.append(f"R22b: the interval's k-energy at k = {k}")
            break
    if not (n * F(3, 2) - 1 == F(1, 6) == (F(3, 2) - 1) / 3 and F(2 + 2, 3 * 2) == F(2, 3)):
        fails.append("R22b: the crossover k = 3/2 and the sparse threshold at k = 2")
    L0, cnt = F(7, 3), (w if mut != "the critical zeros counted at q^{1/2}" else F(1, 2))
    if not (cnt + S57 * L0 == L0 and cnt + S57 * (L0 - F(1, 10)) - (L0 - F(1, 10)) == F(2, 70)):
        fails.append("R22c: the critical zeros at the Linnik exponent and the saving 2 delta/7")
    return fails


CHECKS = {"R1": check_R1, "R2": check_R2, "R3": check_R3, "R4": check_R4, "R5": check_R5, "R6": check_R6,
          "R7": check_R7, "R8": check_R8, "R9": check_R9, "R11": check_R11, "R12": check_R12,
          "R13": check_R13, "R14": check_R14, "R15": check_R15,
          "R16": check_R16, "R17": check_R17,
          "R18": check_R18, "R19": check_R19, "R20": check_R20, "R21": check_R21, "R22": check_R22}

MUTATIONS = ["Selberg's mollifier exponent doubled", "the subdivision modulus q1 read as r",
             "the Burgess form loses its q^{1/r}", "the amplifier's off-diagonal without the square root on R",
             "Burgess's q-exponent read as (r + 1)/(4r)", "the room counted with the norm, not its square",
             "the critical block read as q^{7/20}", "X counted with two factors",
             "Huxley's slope read as the mean value theorem's", "the transplant drops the factor l",
             "Guth-Maynard's third term loses its tau", "Ford's constant read as 4.05",
             "the twelfth moment read as T^{5/2}", "the twisted class-II line keeps FMx's 2x",
             "Burgess's q-exponent halved", "BGKS's e_3 read as 1", "Heath-Brown's R^{5/4} read as R^{3/2}",
             "the diagonal term read as N R", "BPRZ's length read as q^{7/9}",
             "the twist's length read as q^{7/18}", "the outer sums read as one term",
             "the construction's length read as N/V", "the integer-relation bound's h^{1/2} read as h",
             "the excess-energy exponent read as 8 sigma - 7", "the critical threshold read as V^2 = q^{1/2} N",
             "the Hoelder height threshold read without its square",
             "the block's large-values need read without |W|", "the large-spectrum bound's delta^4 read as delta^2",
             "the block's diagonal read without its factor N0",
             "the uniform-spread bound read with |W| in place of |W|^{1/2}",
             "the tree part's exponent read as (k + 1)/k", "the interval's k-energy without its wrap",
             "the critical zeros counted at q^{1/2}"]


def main(mut=None):
    res = {key: fn(mut) for key, fn in CHECKS.items()}
    res["R10"], info = check_R10(mut)
    return dict(sorted(res.items(), key=lambda kv: int(kv[0][1:]))), info


if __name__ == "__main__":
    res, info = main()
    nfail = 0
    for key, fl in res.items():
        print(f"({key}) {'pass' if not fl else 'FAIL'}")
        for f in fl[:10]:
            print("    ", f)
        nfail += len(fl)
    for name, v in info.items():
        print(f"    {name}: {v}")
    caught = 0
    for name in MUTATIONS:
        r, _ = main(name)
        n = sum(len(v) for v in r.values())
        print(f"mutation '{name}': {n} failing checks, {'caught' if n else 'NOT CAUGHT'}")
        caught += 1 if n else 0
    print(f"{len(MUTATIONS)} mutations, {caught} caught")
    raise SystemExit(1 if nfail or caught < len(MUTATIONS) else 0)
