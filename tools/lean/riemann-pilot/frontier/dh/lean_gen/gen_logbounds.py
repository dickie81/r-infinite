# Generate DHLogBounds.lean (LogBounds{NMAX}.lean when NMAX ≠ 121): rational two-sided bounds for Real.log n, n = 2..NMAX, chained through
# log(1 + 1/m) = log((m+1)/m) with PsiOmega.Num.log_one_add_inv_bounds (K terms) from Real.log_two_near_10.
from fractions import Fraction as F
import math, sys
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 121
TARGET = F(1, 10**10)
def K_for(m):
    q = F(1, 2*m+1)
    K = 1
    while 2*q**(2*K+1)/(1-q*q) > TARGET: K += 1
    return K
def partial(m, K):
    q = F(1, 2*m+1)
    return sum(F(2, 2*k+1)*q**(2*k+1) for k in range(K)), 2*q**(2*K+1)/(1-q*q)
lines = ['import Mathlib', 'import DHNumerics', '', '/-! # Generated: rational bounds for `Real.log n`, `2 ≤ n ≤ %d` (round 261, certificate stage 3) -/' % NMAX, '',
         'open Real Finset', '', 'namespace PsiOmega.Num', '']
L = {}; U = {}
L[2] = F(287209, 414355) - TARGET; U[2] = F(287209, 414355) + TARGET
def rat(x): return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
lines += [f"theorem log_bound_2 : {rat(L[2])} ≤ Real.log 2 ∧ Real.log 2 ≤ {rat(U[2])} := by",
          "  have h := abs_sub_le_iff.1 Real.log_two_near_10", "  constructor <;> linarith [h.1, h.2]", ""]
for n in range(3, NMAX+1):
    m = n - 1; K = K_for(m); p, tail = partial(m, K)
    L[n] = L[m] + p; U[n] = U[m] + p + tail
    lines += [f"theorem log_bound_{n} : {rat(L[n])} ≤ Real.log {n} ∧ Real.log {n} ≤ {rat(U[n])} := by",
              f"  have hprev := log_bound_{m}",
              f"  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := {m}) (by norm_num) {K}",
              f"  have e : Real.log ({n} : ℝ) = Real.log ({m} : ℝ) + Real.log (1 + (({m} : ℕ) : ℝ)⁻¹) := by",
              f"    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num",
              f"  rw [e]",
              f"  set y := Real.log (1 + (({m} : ℕ) : ℝ)⁻¹) with hy",
              f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs",
              f"  norm_num at hs",
              f"  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]", ""]
lines += ['end PsiOmega.Num', '', f'#print axioms PsiOmega.Num.log_bound_{NMAX}']
open('DHLogBounds.lean' if NMAX == 121 else f'LogBounds{NMAX}.lean', 'w').write('\n'.join(lines) + '\n')
print(f"wrote {NMAX-1} lemmas; log {NMAX} in [{float(L[NMAX]):.12f}, {float(U[NMAX]):.12f}] true {math.log(NMAX):.12f}; K(2)={K_for(2)} K(50)={K_for(50)} K(120)={K_for(120)}")
