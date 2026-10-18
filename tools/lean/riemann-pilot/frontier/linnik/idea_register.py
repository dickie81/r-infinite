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
  (R23) Round 558's entries.
       (R23a) B25's marker.  For k = 3, ..., 12 the tree part q^k|W|^{k+1} has exponent (5k + 2)/3, below 2k by
              (k - 2)/3; the flat walk sum has exponent (8k - 3)/3; for a power saving the route needs more than
              (2k - 3)/3 of saving there, against the k - 1 of square-root cancellation.  The share
              (2k - 3)/(3k - 3) is least, 1/2, at k = 3, and below 2/3 throughout; matching the free value at k = 3
              needs 2/3 (the tree part's 14/3 against the flat 6).
       (R23b) B27.  Orthogonality over all pairs of characters (the full bilinear large sieve) gives L^4|W|^2 =
              q^{16/3} for the six-cycle's inner sum, against the q^5 the route needs for a power saving: a gap
              L/|W| = q^{1/3}.  With a factor |W|/L in each variable it would be q^{14/3}, the free value.  Times
              the factor q in front, the full sieve's q^{19/3} is above q^6.  (sixcycle_probe.py checks the
              identity and the bounds.)
  (R24) Round 559's entry, B28 (the gcd dichotomy), at nu = 7/18, sigma = 5/7, |W| = q^{2/3} and gcd cut q^d.
       (R24a) The characters whose large value comes mostly from pairs with gcd > q^d number at most the cube of
              (q^{1/3} N0 + N0^2 q^{-d})/V0^2: exponents 3(1/3 + nu - 2 sigma nu) = 1/2 and
              3(2 nu - 2 sigma nu - d) = 2/3 - 3d, checked for d = 0, 1/36, 1/18.
       (R24b) At |W| = q^{2/3} the large-gcd part's share of |W| V0^2 is at most q^{-1/18} + q^{-d}.
       (R24c) The pairs with gcd <= q^d have the fourth moment of the block itself, exponent
              1 + 2 nu - 4 sigma nu = 2/3 for the count, with a factor log q^d in place of log N0.
  (R25) Round 560's entry, B29 (the sixth moment by the dispersion method), at nu = 7/18.
       (R25a) Main term 6 nu - 1 = 4/3, diagonal 3 nu = 7/6, shifts l up to q^{3 nu - 1} = q^{1/6}; the trivial
              dispersion error (3 nu - 1) + nu - nu + 4 nu = 31/18 exceeds the main term by nu = 7/18.
       (R25b) The bilinear forms must be at most q^{3 nu - delta} = N0^3 q^{-delta} on average, and N0^3 is
              ||alpha|| ||beta|| M^{1/2} with M = N0^2, the sharp single-frequency bound for arbitrary
              coefficients; the balanced savings M^{1/48} and M^{1/12} leave exponents 47/48 and 11/12 above 1/2.
       (R25c) Exponents of distribution: 1/(1 + 1/3) = 3/4 from theta = 1/3, 1/(1 + 1/6) = 6/7 needed, and the
              balanced box side q^{1/(3 theta)}: 7/18 at 6/7, 4/9 at 3/4, 11/24 at 8/11.
  (R26) Round 561's entry, B30 (the trilinear form against Bettin-Chandee's Theorem 1), at nu = 7/18: frequencies
       A = q^{nu + 1/6} = q^{5/9}, M = N = q^{2 nu} = q^{7/9}, theta = q, so theta A = MN and AMN = q^{19/9};
       ||alpha|| ||beta|| = q^{7/9} and ||nu|| = q^{-1/9}.  In the shape ||alpha|| ||beta|| ||nu|| Y: the trivial
       Y = q^{19/18} (the error q^{31/18}), the needed Y < q^{2/3} (the error below q^{4/3}), the single-frequency
       limit Y = q^{7/18}, and Bettin-Chandee's two terms q^{14/15} and q^{23/24}: a saving q^{7/72} against the
       needed q^{7/18} = q^{28/72}.  At a block q^v (v = 1/3, 7/18, 4/9, 1/2): A = q^{4v - 1}, theta A = MN, the
       needed saving q^v, Bettin-Chandee's min(q^{(14v - 3)/20}, q^{v/4}) at most q^{1/8}, and the single-frequency
       limit q^v below the needed q^{3v - 1/2}.
  (R27) Round 562's entry, B31 (Deshouillers-Iwaniec's Theorem 12, as extended by Drappeau's Theorem 2.1, on
       B30's form), at the blocks q^v (v = 1/3, 7/18, 4/9, 1/2): C = D = R = S = q^v, frequencies n = h l q up to
       N = q^{4v} of which q^{4v - 1} occur, and ||b|| = q^{(4v - 1)/2}.  K^2 = max of CS(RS + N)(C + RD),
       C^2 DS ((RS + N)R)^{1/2} and D^2 N R/S is the first, q^{8v}; the bound q^{6v - 1/2} exceeds the trivial
       q^{7v - 1} by q^{1/2 - v}, and with N replaced by the count q^{4v - 1} it is q^{5v - 1/2}, above the main term
       q^{6v - 1} by q^{1/2 - v}.  At v = 7/18: q^{11/6}, q^{31/18}, q^{13/9} and q^{4/3}.
  (R28) Round 563's entry, B32 (the coherence of the small-line sums on the Farey points), at |W| = q^{2/3},
       M = q^{2/9}: the few-characters lemma's factor |W|^2/(Lq) = q^{-2/3}, so a set A of characters carries at most
       |S||A|kappa q^{-2/3} of theta' on a set S of points; the major-arc count q^{1/9 + 16 eta/9} for
       |D_M| >= M^{1 - eta} (k = 4, the largest k with M^k <= q); the Farey heights H <= q^{5/18 - 8 eta/9} on which the
       major arcs carry at most q^{-delta}; the q^{2/3}/H^2 characters needed on F_H (q^{1/6} at H = q^{1/4}); and the
       uniform-bias heuristic q^{-1/9}.
  (R29) Round 564's entry, B33 (twisted energies on the Farey points), at |W| = q^{2/3}, M = q^{2/9}: the collision
       count's L M^4 = q^{17/9}, the normalisation |box|^2 q |W|^2 = q^{11/3} and E_1 = q^{5/3} up to kappa - 1;
       Hoelder with the 2k-th moment of the Farey sums, valid for heights up to q^{1/(2k)}, gives q^{(3 - k)/(9k)}
       (k = 3, ..., 8; q^{-1/36} at k = 4); at height q^{1/8} the phi = 1 term is q^{-23/72} and the trivial bound
       q^{1/72}, which is q^0 at height q^{1/9}; the range stops below M (1/8 < 2/9), and an eighth moment at its
       diagonal size beyond the integer range would carry it to height q^{1/4}.
  (R30) Round 565's marker on B33 (the open range as a large-values count), at |W| = q^{2/3}, M = q^{2/9}: with
       N(lambda) the number of characters phi != 1 with |S~(phi)| >= q^lambda, the condition N <= q^{4/9 - lambda}
       from lambda = 1/9; the 2k-th moment's N <= q^{1 - 2k lambda}, an integer count for heights below q^{1/(2k)},
       meets it from lambda = 5/27 (k = 2), 1/9 (k = 3) and 5/63 < 1/9 (k = 4); the fourth moment is an integer count
       up to height 2M and the sixth is not; at lambda = 1/9 the fourth moment's count q^{5/9} against the needed
       q^{1/3}; the short-sum levels sigma = 3/4 and 11/12 at length q^{2/9}; and 1/8 < 1/(4 sqrt e) < 1/6.
  (R31) Round 566's marker on B30 (Wright's Theorem 2.1 for subdyadic intervals, arXiv:2608.27732), at the blocks
       q^v (v = 1/3, 7/18, 4/9, 1/2) with A = q^{4v - 1} and M = N = q^{2v}: its A^{1/2} term has Bettin-Chandee's
       second exponent A/2 + 7M/8, and its A^{7/20} term is Bettin-Chandee's first less 2 eta/5; the second binds for
       every eta >= 0 (tying the first at v = 1/3, eta = 0), so the saving stays q^{v/4} (q^{7/72} at v = 7/18).
  (R32) Round 567's marker on B33 (block moments of the short sums), at |W| = q^{2/3}: with k the largest integer
       with (2H)^k < q, N(lambda) <= q^{1 - k lambda}; the worst lambda q^{2/(3k)}, where q^{1 - k lambda + lambda}
       meets q^{lambda + 1/3}, gives q^{-1/9 + 2/(3k)} = q^{-(k - 6)/(9k)} of theta' (k = 6, ..., 12; q^{-1/63} at k = 7
       up to height q^{1/7}, q^{-1/36} at k = 8, R29's Hoelder at even k); the half-plane's |S~| <= H^{2 sigma_1 - 1}
       reaches height q^{1/(9(2 sigma_1 - 1))}: q^{2/15} < q^{1/7} at sigma_1 = 11/12, and q^{2/9} at sigma_1 = 3/4.
  (R33) Round 568's marker on B33 (block moments past their integer range), at |W| = q^{2/3}: the large sieve for
       one modulus gives N(lambda) <= q^{max(1, k eta) - k lambda} at height q^eta for every k, so the share of
       theta' is at most q^{min_k (max(1, k eta) - 1/3)/k - 1/9}; at k = 7 past its integer range this is
       q^{eta - 10/63}, below 1 exactly up to height q^{10/63} (a grid on [1/7, 1/6]); it agrees with R32 at heights
       q^{1/8} and q^{1/7} and improves it to q^{eta - 11/72} on (1/8, 23/168); for B32's major arcs the fifth moment
       past the wrap leaves q^{20 eta/9} characters, fewer than the fourth moment's q^{1/9 + 16 eta/9} exactly when
       eta < 1/4, and reaches height q^{1/3 - 10 eta/9}, at least 4M for eta <= 1/10 (the fourth's for eta <= 1/16).
  (R34) Round 569's markers on A2 and B5, at sigma = 5/7: 7/9 = 2(7/18), so a detection range of exponent ratio at
       least 2 meets the barrier (ratios 2 and 5/2 fit nowhere in (7/18, 7/9), 19/10 fits); Turan's range with
       m = n - 1 has ratio (2n - 1)/n < 2; Jensen from the centre 11/12 to the zero 5/7 inside the radius 5/12 gains
       log(35/17) per zero; the fourth moment counts |L| >= q^theta below q^{2/3} only for theta > 1/12 (first grid
       point 101/1200); the loss (16e)^{-n} at n = (1/12) log q/log(35/17) is q^{-0.435...}, and the best count at a
       scale of the good window with the level so reduced is q^{4/7 + 0.87...} > q^{2/3}; Huxley's second term
       q N^{4 - 6 sigma} is q^{7/9} at N = q^{7/9} and q^{8/9} at N = q^{7/18}, and with the half-plane's gain in the
       Gram entries (q^{1/54} and q^{11/216} there) taken squared off the factor q it is q^{20/27} and q^{85/108}.
  (R35) Round 570's marker on B33 (zero density counts the large Farey sums), at |W| = q^{2/3}: a character with
       no zero in Re s >= sigma_1 - eps, |Im s| <= q^eps has |S~_G| <= H^{2 sigma_1 - 1 + o(1)}, so at height q^eta
       the count at q^l is at most q^{2(1 - sigma_1)}, sigma_1 = 1/2 + l/(2 eta), where the density hypothesis
       holds, and q^{1/6} for sigma_1 > 11/12; the share max_l (l - 4/9 + min(that, 1/3)) is 2 eta/3 - 1/9 < 0 on
       a grid of (0, 1/6); it equals R32's (6 - k)/(9k) at eta = 1/k (k = 6, ..., 12), is -1/90 at 3/20 (R33:
       3/20 - 10/63), and binds at sigma_1 = 5/6; seven_thirds.py's detectors certify the density hypothesis on a
       grid of [5/6, 11/12] with the mean value theorem and Huxley's estimate alone, by the detector FMx (the
       fourth moment, no half-plane input), and not at 5/6 - 1/100; there FMx's reach is 1/2, Huxley's good range
       is [a, 1] with a = (2 sigma - 1)/(6 sigma - 4) <= 2/3 = a(5/6), and copies of [2/3, 1] cover (0, 1/2] while
       those of [2/3 + 1/1000, 1] do not; at 5/6 - 1/100 and 5/6 - 1/1000, FMx certifies Huxley's 3/(3 sigma - 1),
       whose count exponent is at most 1/3 + 3 eps there.
  (R36) Round 571's marker on B32 (the diagonal in psi), at |W| = q^{2/3}, M = q^{2/9}: with sum_x |U_psi(x)|^2 of
       size q M^2, the terms psi = psi' carry q^{-1/9} of theta' at every height ((17/8)(kappa + 9) = 17(2 kappa +
       18)/16 for the constant), e(x) carries q^{-4/3} and q^{-13/9}, and with |K| <= q^{1/2} M^2 in every x-sum the
       off-diagonal bounded with absolute values is q^{1/6}, against Cauchy-Schwarz's q^{1/3}; the proportional pairs
       of [-M, M]^2 number at most 16 M^2 (1 + log M) for M <= 30; at q = 211, M = 4 and four even characters,
       sum_x |U_psi(x)|^2 agrees with the pair formula (q - 1 or q times psi-bar(lambda) on proportional pairs,
       -psi(a/a') on the others with a, a' nonzero, 0 on the rest) and is at most qP + Q; core 2's length q^{7/6}
       has c = 7/6, outside (2, 3) and (5/2, 3) and below 4/3.

Scope.  This checks arithmetic only.  It does not check the analysis behind any closure, nor that a transplanted
t-aspect theorem holds over the characters mod q.  To show the checks can fail, the script runs sixty-seven mutations,
at least one aimed at each check, and requires each mutation to fail at least one check.
"""
import cmath
import math
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


def check_R23(mut=None):
    fails = []
    w = T23
    for k in range(3, 13):
        tree = k + w * (k + 1)
        flat = 1 + (2 * k - 2) + w * k if mut != "the flat walk sum without its factor q" else (2 * k - 2) + w * k
        need = flat - 2 * k
        if not (tree == F(5 * k + 2, 3) and 2 * k - tree == F(k - 2, 3) and flat == F(8 * k - 3, 3)
                and need == F(2 * k - 3, 3)):
            fails.append(f"R23a: the k = {k} exponents")
            break
    ratios = {k: F(2 * k - 3, 3 * k - 3) for k in range(3, 13)}
    if not (min(ratios.values()) == F(1, 2) == ratios[3] and ratios[4] == F(5, 9)
            and all(ratios[k] < F(2, 3) for k in ratios)):
        fails.append("R23a: the share of square-root cancellation, least at k = 3")
    if not (F(4, 3) / 2 == F(2, 3) and 2 + w * 4 == F(14, 3)):
        fails.append("R23a: the share the free value needs at k = 3")
    full = 4 + 2 * w if mut != "the bilinear large sieve's L^2 read as L" else 3 + 2 * w
    if not (full == F(16, 3) and full - 5 == 1 - w and full - 2 * (1 - w) == F(14, 3) and 1 + full > 6):
        fails.append("R23b: the bilinear large sieve against the six-cycle's need")
    return fails


def check_R24(mut=None):
    fails = []
    nu, sig, w = F(7, 18), S57, T23
    power = 3 if mut != "the gcd dichotomy's Hoelder read with the square" else 2
    for d in (F(0), F(1, 36), F(1, 18)):
        small = power * (F(1, 3) + nu - 2 * sig * nu)
        large = power * (2 * nu - 2 * sig * nu - d)
        if not (small == F(1, 2) and large == w - 3 * d and (d == 0 or large < w)):
            fails.append(f"R24a: the large-gcd count at d = {d}")
            break
    third = w / 3 if mut != "the large-gcd share without |W|^{-1/3}" else F(0)
    for d in (F(1, 36), F(1, 18)):
        s1 = F(1, 3) + nu - 2 * sig * nu - third
        s2 = 2 * nu - 2 * sig * nu - d - third
        if not (s1 == F(-1, 18) and s2 == -d):
            fails.append(f"R24b: the large-gcd share at d = {d}")
            break
    if not (1 + 2 * nu - 4 * sig * nu == w and (2 * nu) < 1):
        fails.append("R24c: the fourth moment of the pairs with small gcd")
    return fails


def check_R25(mut=None):
    fails = []
    nu = F(7, 18)
    main, diag, shifts = 6 * nu - 1, 3 * nu, 3 * nu - 1
    freq = nu if mut != "the dispersion error without its frequency count" else F(0)
    err = shifts + freq - nu + 4 * nu
    if not (main == F(4, 3) and diag == F(7, 6) and shifts == F(1, 6) and err == F(31, 18) and err - main == nu):
        fails.append("R25a: the dispersion route's main term, diagonal and trivial error")
    need = main - (shifts + nu - nu)
    sharp = 2 * nu + nu
    if not (need == 3 * nu == sharp and 1 - F(1, 48) > F(1, 2) and 1 - F(1, 12) > F(1, 2)):
        fails.append("R25b: the needed bilinear bound against the sharp single-frequency bound")
    if mut != "the exponent of distribution read as 1/(1 - theta)":
        dist = lambda t: 1 / (1 + t)
    else:
        dist = lambda t: 1 / (1 - t)
    side = lambda th: 1 / (3 * th)
    if not (dist(F(1, 3)) == F(3, 4) and dist(F(1, 6)) == F(6, 7) and side(F(6, 7)) == nu
            and side(F(3, 4)) == F(4, 9) and side(F(8, 11)) == F(11, 24) and F(8, 11) < F(6, 7)):
        fails.append("R25c: the exponents of distribution and their box sides")
    return fails


def check_R26(mut=None):
    fails = []
    nu = F(7, 18)
    A, M = nu + F(1, 6), 2 * nu
    amn = A + 2 * M
    ab = 2 * nu if mut != "the coefficient norms without the divisor-type alpha, beta" else F(0)
    nrm = (A - 2 * nu) / 2
    if not (A == F(5, 9) and M == F(7, 9) and 1 + A == 2 * M and amn == F(19, 9) and nrm == F(-1, 9)):
        fails.append("R26: the ranges of the trilinear form")
    triv = amn / 2
    if not (ab + nrm + triv == F(31, 18) and F(4, 3) - ab - nrm == F(2, 3)):
        fails.append("R26: the trivial and needed exponents of Y")
    t1 = amn * F(7, 20) + M / 4
    t2 = amn * F(3, 8) + (A + M) / 8
    if mut == "Bettin-Chandee's second term without its (AN + AM)^{1/8}":
        t2 = amn * F(3, 8)
    bc = max(t1, t2)
    if not (t1 == F(14, 15) and t2 == F(23, 24) and bc == F(23, 24) and triv - bc == F(7, 72)
            and triv - F(2, 3) == F(28, 72) == nu and M / 2 == nu and nu < F(2, 3) < bc):
        fails.append("R26: Bettin-Chandee against the needed saving and the single-frequency limit")
    for v in (F(1, 3), F(7, 18), F(4, 9), F(1, 2)):
        Av, Mv = 4 * v - 1, 2 * v
        need, trivv = 3 * v - F(1, 2), 4 * v - F(1, 2)
        save = min((14 * v - 3) / 20, v / 4)
        if not (1 + Av == 2 * Mv and trivv - need == v and save <= F(1, 8) < v and Mv / 2 == v < need):
            fails.append(f"R26: the block q^{v}")
            break
    return fails


def check_R27(mut=None):
    fails = []

    def k2(C, D, N, R, S):
        t1 = C + S + max(R + S, N) + max(C, R + D)
        if mut == "Theorem 12's first term without its factor (RS + N)":
            t1 = C + S + max(C, R + D)
        t2 = 2 * C + D + S + (max(N, R + S) + R) / 2
        t3 = 2 * D + N + R - S
        return max(t1, t2, t3), t1
    for v in (F(1, 3), F(7, 18), F(4, 9), F(1, 2)):
        C = D = R = S = v
        shifts = 3 * v - 1
        N, supp = v + shifts + 1, v + shifts
        b = supp / 2 if mut != "the norm of b counted over every n up to N" else N / 2
        big, t1 = k2(C, D, N, R, S)
        bound, trivial, main = big / 2 + b, 4 * v + shifts, 6 * v - 1
        big_s, t1_s = k2(C, D, supp, R, S)
        bound_s = big_s / 2 + b
        if not (big == t1 == 8 * v and bound == 6 * v - F(1, 2) and trivial == 7 * v - 1
                and bound - trivial == F(1, 2) - v and big_s == t1_s == 6 * v and bound_s == 5 * v - F(1, 2)
                and bound_s - main == F(1, 2) - v >= 0):
            fails.append(f"R27: the block q^{v}")
            break
    nu = F(7, 18)
    if not (6 * nu - F(1, 2) == F(11, 6) and 7 * nu - 1 == F(31, 18) and 5 * nu - F(1, 2) == F(13, 9)
            and 6 * nu - 1 == F(4, 3)):
        fails.append("R27: the exponents at the critical block")
    return fails


def check_R28(mut=None):
    fails = []
    w, m = F(2, 3), F(2, 9)
    lem = 2 * w - 2 if mut != "the lemma with |A| in place of |A|^{1/2}" else 2 * w - 2 + F(1, 3)
    if not (lem == F(-2, 3) and 1 - 2 * m == F(5, 9)):
        fails.append("R28: the few-characters lemma")
    k = max(j for j in range(1, 10) if j * m <= 1)
    if mut == "the major-arc moment taken past the wrap":
        k += 1
    for eta in (F(0), F(1, 8), F(1, 4)):
        arcs = 1 - k * m + 2 * k * m * eta
        hmax = (-lem - arcs) / 2
        if not (k == 4 and arcs == F(1, 9) + 16 * eta / 9 and hmax == F(5, 18) - 8 * eta / 9 and hmax > 0):
            fails.append(f"R28: the major arcs at eta = {eta}")
            break
    need = lambda h: -lem - 2 * h
    heur = 2 * w - 2 * m - 1
    if not (need(F(1, 4)) == F(1, 6) and need(F(1, 3)) == 0 and heur == F(-1, 9)):
        fails.append("R28: the characters needed on F_H and the uniform-bias heuristic")
    return fails


def check_R29(mut=None):
    fails = []
    w, m = F(2, 3), F(2, 9)
    om = 1 + 4 * m if mut != "the collision count with M^3 in place of M^4" else 1 + 3 * m
    nrm, en = 6 * m + 1 + 2 * w, 4 * w - 1
    rmax = w if mut != "the bound |r_w| <= |W|^2 in place of |W|" else 2 * w
    if not (om == F(17, 9) and nrm == F(11, 3) and en == F(5, 3)):
        fails.append("R29: the collision count, the normalisation and the energy")
    for k in range(3, 9):
        hol = (rmax * F(2, 2 * k - 1) + en) * F(2 * k - 1, 2 * k) + F(1, 2 * k) + om - nrm
        eta = F(1, 2 * k) if mut != "the eighth moment taken past its integer range" else F(1, 2 * k - 2)
        if not (hol == F(3 - k, 9 * k) and 2 * k * eta <= 1):
            fails.append(f"R29: Hoelder with the {2 * k}-th moment")
            break
    one = lambda eta: 2 * w + om + eta - nrm
    triv = lambda eta: en + om + eta - nrm
    if not (one(F(1, 8)) == F(-23, 72) and triv(F(1, 8)) == F(1, 72) and triv(F(1, 9)) == 0 and F(1, 8) < m):
        fails.append("R29: the terms at heights q^{1/8} and q^{1/9}")
    far = m - F(3 - 4, 9 * 4)
    if not (far == F(1, 4) and 2 * w + 1 + 3 * m + 2 * far - nrm < 0):
        fails.append("R29: the range an eighth moment at its diagonal size would reach")
    return fails


def check_R30(mut=None):
    fails = []
    m, start = F(2, 9), F(1, 9)
    need = lambda lam: F(4, 9) - lam if mut != "the needed count without its factor 1/lambda" else F(4, 9)
    per_fraction = 2 if mut != "a Farey fraction counted as one integer" else 1
    valid = lambda k, eta: per_fraction * k * eta < 1
    meet = {}
    for k in (2, 3, 4):
        e = 2 * k if mut != "the fourth moment of S read as the fourth moment of the short sums" else k
        meet[k] = next(F(j, 945) for j in range(1, 946) if 1 - e * F(j, 945) <= need(F(j, 945)))
    if not (meet[2] == F(5, 27) and meet[3] == start and meet[4] == F(5, 63) and meet[4] < start):
        fails.append("R30: where the moments meet the condition")
    if not (valid(2, m) and not valid(3, m) and valid(3, F(1, 6) - F(1, 100)) and valid(4, F(1, 8) - F(1, 100))
            and not valid(4, F(1, 8))):
        fails.append("R30: the integer ranges of the moments")
    if not (1 - 4 * start == F(5, 9) and need(start) == F(1, 3) and (2 * F(3, 4) - 1) * m == start
            and (2 * F(11, 12) - 1) * m == F(5, 27)):
        fails.append("R30: the fourth moment's count at q^{1/9} and the short-sum levels")
    e_lo, e_hi = F(2718, 1000), F(2719, 1000)
    if not (e_lo < 4 and e_hi < 4 and e_lo > F(9, 4)):
        fails.append("R30: 1/8 < 1/(4 sqrt e) < 1/6")
    return fails


def check_R31(mut=None):
    fails = []
    for v in (F(1, 3), F(7, 18), F(4, 9), F(1, 2)):
        A, M = 4 * v - 1, 2 * v
        bc1, bc2 = (A + 2 * M) * F(7, 20) + M / 4, (A + 2 * M) * F(3, 8) + (A + M) / 8
        w2 = A / 2 + M / 2 + 3 * M / 8 if mut != "Wright's A^{1/2} term with N^{1/2} for N^{3/8}" else A / 2 + M
        for eta in (F(0), F(1, 100), F(1, 10)):
            w1 = A * F(7, 20) + 3 * M / 5 + 7 * M / 20 - 2 * eta / 5
            w2e = w2 - 2 * eta / 5 if mut == "Wright's saving X^{-2 eta/5} on the A^{1/2} terms too" else w2
            save = (A + 2 * M) / 2 - max(w1, w2e)
            if not (w2 == bc2 == A / 2 + 7 * M / 8 and w1 == bc1 - 2 * eta / 5 and max(w1, w2e) == w2e
                    and save == v / 4 < v and (w1 == w2e) == (v == F(1, 3) and eta == 0)):
                fails.append(f"R31: Wright's terms at the block q^{v}, eta = {eta}")
                break
        else:
            continue
        break
    if not (F(7, 18) / 4 == F(7, 72)):
        fails.append("R31: the critical block's saving")
    return fails


def check_R32(mut=None):
    fails = []
    for k in range(6, 13):
        reach = F(1, k) if mut != "the block moment's integer range read as (2H)^{2k} < q" else F(1, 2 * k)
        lam = F(2, 3 * k)
        theta = lam + F(1, 3) - F(4, 9) if mut != "the worst level read as q^{2/k}" else F(2, k) + F(1, 3) - F(4, 9)
        if not (1 - k * lam + lam == lam + F(1, 3) and theta == F(-1, 9) + F(2, 3 * k) == F(6 - k, 9 * k)
                and reach == F(1, k)):
            fails.append(f"R32: the block moments at k = {k}")
            break
        if k % 2 == 0 and not (F(3 - k // 2, 9 * (k // 2)) == theta):
            fails.append(f"R32: R29's Hoelder at k = {k}")
            break
    if not (F(6 - 7, 63) == F(-1, 63) and F(6 - 8, 72) == F(-1, 36) and F(1, 8) < F(1, 7) < F(1, 6)):
        fails.append("R32: the new range q^{1/7} and its saving")
    hp = lambda s1: F(1, 9) / (2 * s1 - 1)
    if not (hp(F(11, 12)) == F(2, 15) < F(1, 7) and hp(F(3, 4)) == F(2, 9) and F(5, 6) * F(2, 15) == F(1, 9)):
        fails.append("R32: the half-plane's range")
    return fails


def check_R33(mut=None):
    fails = []

    def share(eta, k):
        span = k * eta if mut != "the large sieve's length (2H)^k read as (2H)^{2k}" else 2 * k * eta
        top = max(F(1), span) if mut != "the large sieve without its q" else span
        return (top - F(1, 3)) / k - F(1, 9)

    best = lambda eta: min(share(eta, k) for k in range(1, 41))
    for eta in (F(1, 7), F(3, 20), F(10, 63)):
        if not (share(eta, 7) == eta - F(10, 63)):
            fails.append(f"R33: the seventh block moment at height q^{eta}")
            break
    lo = [F(1, 7) + (F(10, 63) - F(1, 7)) * F(i, 20) for i in range(20)]
    hi = [F(10, 63) + (F(1, 6) - F(10, 63)) * F(i, 20) for i in range(21)]
    if not (all(best(e) < 0 for e in lo) and all(best(e) == 0 for e in hi)):
        fails.append("R33: the range q^{10/63}")
    if not (best(F(1, 7)) == F(-1, 63) and best(F(1, 8)) == F(-1, 36)
            and best(F(13, 100)) == F(13, 100) - F(11, 72) < F(-1, 63) and F(11, 72) - F(1, 63) == F(23, 168)):
        fails.append("R33: the savings from height q^{1/8} to q^{1/7}")
    m = F(2, 9)
    if mut != "the major-arc moment past the wrap without the large sieve's M^5":
        k5 = lambda eta: max(F(1), 5 * m) - 5 * m + 10 * m * eta
    else:
        k5 = lambda eta: 1 - 5 * m + 10 * m * eta
    k4 = lambda eta: 1 - 4 * m + 8 * m * eta
    reach = lambda arcs: (F(2, 3) - arcs) / 2
    for eta in grid(F(0), F(1, 2), 40):
        if not (k5(eta) == 20 * eta / 9 and reach(k5(eta)) == F(1, 3) - 10 * eta / 9
                and (k5(eta) < k4(eta)) == (eta < F(1, 4)) and (reach(k5(eta)) >= F(2, 9)) == (eta <= F(1, 10))
                and (reach(k4(eta)) >= F(2, 9)) == (eta <= F(1, 16))):
            fails.append(f"R33: B32's major arcs at eta = {eta}")
            break
    return fails


def check_R34(mut=None):
    fails = []
    lo, hi = F(7, 18), F(7, 9) if mut != "the barrier's ratio read as 3/2" else F(7, 12)
    fits = lambda rho: any(lo < l and rho * l < hi for l in grid(lo, hi, 400))
    if not (hi / lo == 2 and not fits(F(2)) and not fits(F(5, 2)) and fits(F(19, 10))):
        fails.append("R34: a detection range of exponent ratio at least 2 meets the barrier")
    if not all(F(2 * n - 1, n) < 2 for n in range(1, 50)):
        fails.append("R34: Turan's range with m = n - 1")
    c0 = F(11, 12) if mut != "Jensen's centre read as 1" else F(1)
    r, big = c0 - F(5, 7), c0 - F(1, 2)
    per = math.log(big / r)
    four = (lambda th: 1 - 4 * th) if mut != "the fourth moment's count read as q^{1 - 2 theta}" else (lambda th: 1 - 2 * th)
    theta = next(F(j, 1200) for j in range(1, 1200) if four(F(j, 1200)) < F(2, 3))
    loss = float(F(1, 12)) * math.log(16 * math.e) / per
    best = min(max(1.0, y) + y * (1 - 10 / 7) + 2 * k * loss
               for k in range(1, 11) for y in [1.0] + [7 / 9 + i * (7 / 6 - 7 / 9) / 100 for i in range(101)])
    if not (r == F(17, 84) and big == F(5, 12) and theta == F(101, 1200) and 0.43 < loss < 0.44
            and abs(best - (4 / 7 + 2 * loss)) < 1e-12 and best > float(F(2, 3))):
        fails.append("R34: Jensen's count, the fourth moment's threshold and Turan's loss")
    hux = lambda ell, c=F(1): c + ell * (4 - 6 * F(5, 7))
    gain = lambda ell: F(1, 2) - (ell / 12 + F(5, 12))
    if not (hux(F(7, 9)) == F(7, 9) and hux(F(7, 18)) == F(8, 9) and gain(F(7, 9)) == F(1, 54)
            and gain(F(7, 18)) == F(11, 216) and hux(F(7, 9), 1 - 2 * gain(F(7, 9))) == F(20, 27)
            and hux(F(7, 18), 1 - 2 * gain(F(7, 18))) == F(85, 108) and F(85, 108) > F(20, 27) > F(2, 3)):
        fails.append("R34: Huxley's second term at the barrier lengths, with the half-plane's gain squared")
    return fails


def check_R35(mut=None):
    fails = []

    def count(l, eta):
        s1 = F(1, 2) + l / (2 * eta) if mut != "the zero-free bound read as H^{sigma_1}" else l / eta
        dens = F(2) if mut != "the density at 5/6 read as 7/3" else F(7, 3)
        return dens * (1 - min(s1, F(11, 12)))

    def share(eta, n=360):
        return max(F(j, n) * eta - F(4, 9) + min(count(F(j, n) * eta, eta), F(1, 3)) for j in range(n + 1))

    for eta in grid(F(1, 60), F(1, 6) - F(1, 600), 24):
        if not (share(eta) == 2 * eta / 3 - F(1, 9) < 0):
            fails.append(f"R35: the share at height q^{eta}")
            break
    if not (all(share(F(1, k)) == F(6 - k, 9 * k) for k in range(6, 13)) and share(F(3, 20)) == F(-1, 90)
            and F(-1, 90) < F(3, 20) - F(10, 63) and F(1, 2) + (F(2, 3) * F(1, 7)) / (2 * F(1, 7)) == F(5, 6)):
        fails.append("R35: agreement with R32 at 1/k, the gain over R33, and the crossing at 5/6")
    low = F(5, 6) if mut != "the density hypothesis claimed from 4/5" else F(4, 5)
    pts = [low + (F(11, 12) - low) * F(i, 12) for i in range(13)]
    if not (all(st.certify(s1, F(2), methods=("MVT", "HUX")) == "FMx" for s1 in pts)
            and st.certify(F(5, 6) - F(1, 100), F(2), methods=("MVT", "HUX")) is None):
        fails.append("R35: the density hypothesis on [5/6, 11/12] from the mean value theorem and Huxley")
    a = lambda s: (2 * s - 1) / (6 * s - 4)
    if not (all(st.good_interval("HUX", s1, 2 * (1 - s1)) == (a(s1), F(1)) and a(s1) <= F(2, 3) for s1 in pts)
            and all(d[2] == F(1, 2) for s1 in pts for d in st.detectors(s1, 2 * (1 - s1)) if d[4] == "FMx")
            and a(F(5, 6)) == F(2, 3) and st.covered([(F(2, 3), F(1))], F(1, 1000), F(1, 2))
            and not st.covered([(F(2, 3) + F(1, 1000), F(1))], F(1, 1000), F(1, 2))):
        fails.append("R35: FMx's reach 1/2 and Huxley's range [a, 1], a <= 2/3")
    for e in (F(1, 100), F(1, 1000)):
        s1 = F(5, 6) - e
        hux = 3 / (3 * s1 - 1)
        if not (st.certify(s1, hux, methods=("MVT", "HUX")) == "FMx" and hux * (1 - s1) <= F(1, 3) + 3 * e):
            fails.append(f"R35: Huxley's exponent at 5/6 - {e}")
    return fails


_U_CACHE = {}


def _u_mean_square(q, M, js):
    """For even characters psi_j mod q: sum_x |U_psi(x)|^2 directly, the same through the pair formula, P, Q."""
    key = (q, M, tuple(js))
    if key not in _U_CACHE:
        g = next(g for g in range(2, q) if all(pow(g, (q - 1) // p, q) != 1 for p in (2, 3, 5, 7) if (q - 1) % p == 0))
        ind, v = [0] * q, 1
        for k in range(q - 1):
            ind[v] = k
            v = v * g % q
        pts = [(a, b) for a in range(-M, M + 1) for b in range(-M, M + 1) if (a, b) != (0, 0)]
        P = sum(1 for p in pts for r in pts if p[0] * r[1] == p[1] * r[0])
        rows = []
        for j in js:
            chi = [0j] + [cmath.exp(2j * math.pi * j * ind[n] / (q - 1)) for n in range(1, q)]
            direct = sum(abs(sum(chi[(a * x + b) % q] for a, b in pts)) ** 2 for x in range(q))
            pairs = 0j
            for a, b in pts:
                for c, d in pts:
                    if a * d == b * c:
                        lam = c * pow(a, -1, q) % q if a else d * pow(b, -1, q) % q
                        pairs += chi[lam].conjugate() * ((q - 1) if a else q)
                    elif a and c:
                        pairs -= chi[a * pow(c, -1, q) % q]
            rows.append((direct, pairs))
        _U_CACHE[key] = (P, len(pts) ** 2 - P, rows)
    return _U_CACHE[key]


def _p_count(M):
    cnt = {}
    for a in range(-M, M + 1):
        for b in range(-M, M + 1):
            if (a, b) != (0, 0):
                g = math.gcd(a, b)
                d = (a // g, b // g)
                d = d if d > (0, 0) else (-d[0], -d[1])
                cnt[d] = cnt.get(d, 0) + 1
    return sum(c * c for c in cnt.values())


def check_R36(mut=None):
    fails = []
    W, M = F(2, 3), F(2, 9)
    u = 1 + 2 * M if mut != "the U mean square read as qM^4" else 1 + 4 * M
    norm = 6 * M + 1 + 2 * W
    diag = u + 2 * M + 4 * W - 1 - norm
    k_off = F(1, 2) + 2 * M if mut != "the off-diagonal's K bound without its square root" else 1 + 2 * M
    off = k_off + M + 4 * W - norm
    if not (diag == 2 * W - 2 * M - 1 == F(-1, 9) and off == F(1, 6) and 1 - 3 * M == F(1, 3)
            and W - 2 == F(-4, 3) and -2 * M - 1 == F(-13, 9)
            and all(F(17 * (2 * k + 18), 16) == F(17, 8) * (k + 9) for k in range(1, 5))):
        fails.append("R36: the diagonal -1/9, the off-diagonal 1/6 with K square-root, CS 1/3, e(x) -4/3 and -13/9")
    if not all(_p_count(m) <= 16 * m * m * (1 + math.log(m)) + 1e-9 for m in range(1, 31)):
        fails.append("R36: the proportional pairs P <= 16 M^2 (1 + log M)")
    q, m = 211, 4
    P, Qn, rows = _u_mean_square(q, m, (2, 6, 10, 42))
    if not (P == _p_count(m) and Qn <= (2 * m + 1) ** 4
            and all(abs(d - p) < 1e-6 * (1 + d) and d <= q * P + Qn for d, p in rows)):
        fails.append("R36: sum_x |U_psi|^2 by the pair formula, and <= qP + Q, at q = 211, M = 4")
    c = F(7, 6) if mut != "the critical length read as q^{13/6}" else F(13, 6)
    if not (not (2 < c < 3) and not (F(5, 2) < c < 3) and c < F(4, 3) and 3 * F(7, 18) == c):
        fails.append("R36: c = 7/6 outside Nguyen's (2, 3), Kowalski-Ricotta's (5/2, 3) and Petrow-Young's c >= 4/3")
    return fails


CHECKS = {"R1": check_R1, "R2": check_R2, "R3": check_R3, "R4": check_R4, "R5": check_R5, "R6": check_R6,
          "R7": check_R7, "R8": check_R8, "R9": check_R9, "R11": check_R11, "R12": check_R12,
          "R13": check_R13, "R14": check_R14, "R15": check_R15,
          "R16": check_R16, "R17": check_R17,
          "R18": check_R18, "R19": check_R19, "R20": check_R20, "R21": check_R21, "R22": check_R22, "R23": check_R23,
          "R24": check_R24, "R25": check_R25, "R26": check_R26, "R27": check_R27, "R28": check_R28,
          "R29": check_R29, "R30": check_R30, "R31": check_R31,
          "R32": check_R32, "R33": check_R33, "R34": check_R34, "R35": check_R35, "R36": check_R36}

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
             "the critical zeros counted at q^{1/2}",
             "the flat walk sum without its factor q", "the bilinear large sieve's L^2 read as L",
             "the gcd dichotomy's Hoelder read with the square", "the large-gcd share without |W|^{-1/3}",
             "the dispersion error without its frequency count", "the exponent of distribution read as 1/(1 - theta)",
             "the coefficient norms without the divisor-type alpha, beta",
             "Bettin-Chandee's second term without its (AN + AM)^{1/8}",
             "Theorem 12's first term without its factor (RS + N)", "the norm of b counted over every n up to N",
             "the lemma with |A| in place of |A|^{1/2}", "the major-arc moment taken past the wrap",
             "the collision count with M^3 in place of M^4", "the bound |r_w| <= |W|^2 in place of |W|",
             "the eighth moment taken past its integer range", "the needed count without its factor 1/lambda",
             "the fourth moment of S read as the fourth moment of the short sums",
             "a Farey fraction counted as one integer", "Wright's saving X^{-2 eta/5} on the A^{1/2} terms too",
             "Wright's A^{1/2} term with N^{1/2} for N^{3/8}",
             "the block moment's integer range read as (2H)^{2k} < q", "the worst level read as q^{2/k}",
             "the large sieve's length (2H)^k read as (2H)^{2k}", "the large sieve without its q",
             "the major-arc moment past the wrap without the large sieve's M^5",
             "the barrier's ratio read as 3/2", "Jensen's centre read as 1",
             "the fourth moment's count read as q^{1 - 2 theta}",
             "the zero-free bound read as H^{sigma_1}", "the density at 5/6 read as 7/3",
             "the density hypothesis claimed from 4/5",
             "the U mean square read as qM^4", "the off-diagonal's K bound without its square root",
             "the critical length read as q^{13/6}"]


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
