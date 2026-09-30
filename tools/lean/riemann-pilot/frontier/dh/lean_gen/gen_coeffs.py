# Generate Coeffs.lean: rational interval bounds for uR d, dinvR n, fDH n (n ≤ NMAX), following the real
# recursions dinvR_of_two_le / fDH_eq of src/DHPacket.lean with the interval lemma PsiOmega.Num.mul_bounds,
# kappa_bounds (KappaTight.lean) and log_bound_d (LogBounds.lean). Bounds are rounded outward to 10^-14.
from fractions import Fraction as F
import sys, math
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 121
KLO, KHI = F(284079043840412, 10**15), F(284079043840413, 10**15)
ROUND = 10**14
def rd(lo, hi):
    return F(math.floor(lo*ROUND), ROUND), F(math.ceil(hi*ROUND), ROUND)
def rat(x):
    return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def mulb(a, b):
    c = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]
    return min(c), max(c)
def divisors(n): return [d for d in range(1, n+1) if n % d == 0]
# log bounds, recomputed as in gen_logbounds.py
TARGET = F(1, 10**10)
def K_for(m):
    q = F(1, 2*m+1); K = 1
    while 2*q**(2*K+1)/(1-q*q) > TARGET: K += 1
    return K
L = {2: F(287209, 414355) - TARGET}; U = {2: F(287209, 414355) + TARGET}
for n in range(3, NMAX+1):
    m = n-1; K = K_for(m); q = F(1, 2*m+1)
    p = sum(F(2, 2*k+1)*q**(2*k+1) for k in range(K)); tail = 2*q**(2*K+1)/(1-q*q)
    L[n] = L[m] + p; U[n] = U[m] + p + tail
def uval_expr(d):
    r = d % 5
    return {0: "0", 1: "1", 2: "kappa", 3: "-kappa", 4: "-1"}[r]
def u_bounds(d):
    r = d % 5
    return {0: (F(0), F(0)), 1: (F(1), F(1)), 2: (KLO, KHI), 3: (-KHI, -KLO), 4: (F(-1), F(-1))}[r]
lines = ['import Mathlib', 'import DHPacket', 'import DHNumerics', 'import DHLogBounds', '',
         '/-! # Generated: interval bounds for `u(d)`, `dinv(n)`, `c(n)`, `n ≤ %d` (round 261, certificate stage 3) -/' % NMAX, '',
         'open Real Finset', '', 'namespace PsiOmega', '']
# uR value lemmas
for d in range(2, NMAX+1):
    lines += [f"theorem uR_val_{d} : uR {d} = {uval_expr(d)} := by", "  rw [uR_eq]", "  norm_num [uval]", ""]
lines += ["theorem uR_bounds_of_val {d : ℕ} {v lo hi : ℝ} (h : uR d = v) (hv : lo ≤ v ∧ v ≤ hi) : lo ≤ uR d ∧ uR d ≤ hi := by",
          "  rw [h]; exact hv", ""]
def u_bounds_lemma(d):
    r = d % 5; lo, hi = u_bounds(d)
    if r == 2: hv = "kappa_bounds.1.le, kappa_bounds.2.le"
    elif r == 3: hv = "neg_le_neg kappa_bounds.2.le, neg_le_neg kappa_bounds.1.le"
    else: hv = "le_rfl, le_rfl"
    return f"(uR_bounds_of_val uR_val_{d} ⟨{hv.split(', ')[0]}, {hv.split(', ')[1]}⟩)"
DB = {1: (F(1), F(1))}    # dinvR bounds
lines += ["theorem dinvR_bounds_1 : (1 : ℝ) ≤ dinvR 1 ∧ dinvR 1 ≤ 1 := by rw [dinvR_one]; exact ⟨le_rfl, le_rfl⟩", ""]
for n in range(2, NMAX+1):
    ds = divisors(n)
    pairs = [(d, n//d) for d in ds]
    fpairs = [(d, e) for d, e in pairs if d != 1]
    # exact interval of -(Σ uR d * dinvR e)
    tot_lo, tot_hi = F(0), F(0)
    prods = []
    for d, e in fpairs:
        lo, hi = mulb(u_bounds(d), DB[e]); prods.append((lo, hi)); tot_lo += lo; tot_hi += hi
    lo_n, hi_n = rd(-tot_hi, -tot_lo); DB[n] = (lo_n, hi_n)
    setlit = "{" + ", ".join(f"({d}, {e})" for d, e in pairs) + "}"
    out = [f"theorem dinvR_bounds_{n} : {rat(lo_n)} ≤ dinvR {n} ∧ dinvR {n} ≤ {rat(hi_n)} := by",
           f"  rw [dinvR_of_two_le (by norm_num), Finset.sum_filter, show Nat.divisorsAntidiagonal {n} = {setlit} by decide]",
           "  norm_num [Finset.sum_insert]"]
    for i, (d, e) in enumerate(fpairs):
        out += [f"  have hp{i} := PsiOmega.Num.mul_bounds {u_bounds_lemma(d)} dinvR_bounds_{e}",
                f"  norm_num at hp{i}"]
    hyps = ", ".join(f"hp{i}.1, hp{i}.2" for i in range(len(fpairs)))
    out += [f"  constructor <;> linarith [{hyps}]", ""]
    lines += out
# fDH bounds
FB = {}
for n in range(2, NMAX+1):
    ds = divisors(n); pairs = [(d, n//d) for d in ds]
    tot_lo, tot_hi = F(0), F(0)
    terms = []
    for d, e in pairs:
        if d == 1: continue          # log 1 = 0
        ub = u_bounds(d)
        if ub == (F(0), F(0)): continue
        lg = (L[d], U[d])
        p1 = mulb(lg, ub); p2 = mulb(p1, DB[e]); terms.append((d, e)); tot_lo += p2[0]; tot_hi += p2[1]
    lo_n, hi_n = rd(tot_lo, tot_hi); FB[n] = (lo_n, hi_n)
    setlit = "{" + ", ".join(f"({d}, {e})" for d, e in pairs) + "}"
    out = [f"theorem fDH_bounds_{n} : {rat(lo_n)} ≤ fDH {n} ∧ fDH {n} ≤ {rat(hi_n)} := by",
           f"  rw [fDH_eq, show Nat.divisorsAntidiagonal {n} = {setlit} by decide]",
           "  norm_num [Finset.sum_insert, Real.log_one]"]
    # zero-valued uR terms: state them
    for d, e in pairs:
        if d != 1 and u_bounds(d) == (F(0), F(0)):
            out += [f"  rw [uR_val_{d}]"]
    for i, (d, e) in enumerate(terms):
        out += [f"  have hl{i} := PsiOmega.Num.log_bound_{d}",
                f"  have hq{i} := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hl{i} {u_bounds_lemma(d)}) dinvR_bounds_{e}",
                f"  norm_num at hq{i}"]
    hyps = ", ".join(f"hq{i}.1, hq{i}.2" for i in range(len(terms)))
    out += [f"  constructor <;> linarith [{hyps}]" if terms else "  norm_num", ""]
    lines += out
lines += ['end PsiOmega', '', f'#print axioms PsiOmega.dinvR_bounds_{NMAX}', f'#print axioms PsiOmega.fDH_bounds_{NMAX}']
open('DHCoeffs.lean' if NMAX == 121 else f'Coeffs{NMAX}.lean', 'w').write('\n'.join(lines) + '\n')
import mpmath as mp
mp.mp.dps = 30
print(f"wrote n ≤ {NMAX}; dinvR widths max {max(float(DB[n][1]-DB[n][0]) for n in DB):.2e}; fDH widths max {max(float(FB[n][1]-FB[n][0]) for n in FB):.2e}")
print("fDH bounds n=2..8:", [(n, float(FB[n][0]), float(FB[n][1])) for n in range(2, 9)])
