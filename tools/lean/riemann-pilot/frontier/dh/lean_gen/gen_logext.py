# Generate DHLogBoundsExt.lean: rational two-sided bounds for Real.log n, 122 <= n <= NMAX, chained upward
# from PsiOmega.Num.log_bound_121 (DHLogBounds, parsed from the source) through
# log(n) = log(n-1) + log(1 + 1/(n-1)) with PsiOmega.Num.log_one_add_inv_bounds (K terms, tail <= 1e-22),
# every bound rounded outward to the grid 1e-30 (the landed DHLogBounds.lean is untouched).
from fractions import Fraction as F
import math, re, sys, os
import mpmath as mp
mp.mp.dps = 50
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 209
HERE = os.path.dirname(os.path.abspath(__file__))
LOGSRC = '/home/user/r-infinite/tools/lean/riemann-pilot/external/dh/DHLogBounds.lean'
src = open(LOGSRC).read()
m = re.search(r"theorem log_bound_121 : \((\d+) / (\d+) : ℝ\) ≤ Real\.log 121 ∧ Real\.log 121 ≤ \((\d+) / (\d+) : ℝ\)", src)
L = {121: F(int(m.group(1)), int(m.group(2)))}; U = {121: F(int(m.group(3)), int(m.group(4)))}
G = 10**30
def rd_lo(x): return F(math.floor(x * G), G)
def rd_hi(x): return F(math.ceil(x * G), G)
def rat(x): return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def K_for(m):
    q = F(1, 2*m+1); K = 1
    while 2*q**(2*K+1)/(1-q*q) > F(1, 10**22): K += 1
    return K
lines = ['import DHLogBounds', '',
  '/-! # Generated (gen_logext.py): rational bounds for `Real.log n`, `122 ≤ n ≤ %d`' % NMAX, '',
  'Chained upward from `PsiOmega.Num.log_bound_121` (`DHLogBounds`) by',
  '`log n = log (n − 1) + log (1 + 1/(n − 1))` with `PsiOmega.Num.log_one_add_inv_bounds` (tail `≤ 10⁻²²`),',
  'every bound rounded outward to the grid `10⁻³⁰`. Used by the zero-location certificates for the zeros',
  'at heights `114`, `166`, `176` (`DHLocate2Base` … `DHLocate4Num`). -/', '',
  'open Real Finset', '', 'namespace PsiOmega.Num', '']
for n in range(122, NMAX + 1):
    mm = n - 1; K = K_for(mm); q = F(1, 2*mm+1)
    p = sum(F(2, 2*k+1)*q**(2*k+1) for k in range(K)); tail = 2*q**(2*K+1)/(1-q*q)
    L[n] = rd_lo(L[mm] + p); U[n] = rd_hi(U[mm] + p + tail)
    assert mp.mpf(L[n].numerator)/L[n].denominator <= mp.log(n) <= mp.mpf(U[n].numerator)/U[n].denominator
    lines += [f"theorem log_bound_{n} : {rat(L[n])} ≤ Real.log {n} ∧ Real.log {n} ≤ {rat(U[n])} := by",
              f"  have hprev := log_bound_{mm}",
              f"  have hs := PsiOmega.Num.log_one_add_inv_bounds (m := {mm}) (by norm_num) {K}",
              f"  have e : Real.log ({n} : ℝ) = Real.log ({mm} : ℝ) + Real.log (1 + (({mm} : ℕ) : ℝ)⁻¹) := by",
              f"    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num",
              f"  rw [e]",
              f"  set y := Real.log (1 + (({mm} : ℕ) : ℝ)⁻¹) with hy",
              f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs",
              f"  norm_num at hs",
              f"  constructor <;> linarith [hprev.1, hprev.2, hs.1, hs.2]", ""]
lines += ['end PsiOmega.Num', '', f'#print axioms PsiOmega.Num.log_bound_{NMAX}']
open(os.path.join(HERE, 'DHLogBoundsExt.lean'), 'w').write('\n'.join(lines) + '\n')
print(f"wrote {NMAX-121} lemmas; width at {NMAX}: {float(U[NMAX]-L[NMAX]):.3e}; K(121)={K_for(121)} K({NMAX-1})={K_for(NMAX-1)}")
