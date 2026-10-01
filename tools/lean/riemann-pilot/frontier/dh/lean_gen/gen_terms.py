# Generate Terms.lean: for each n = 2..121 a lower bound t_n on the prime term
#   T n = fDH n / √n * ((2a − log n)/2 * cos(ω log n) + sin(ω(2a − log n))/(2ω)),  a = 12/5, ω = 169/2,
# and the partial sums Σ_{n ∈ Icc 2 k} T n ≥ P_k, k = 2..121. Inputs: fDH_bounds_n (Coeffs.lean),
# log_bound_n (LogBounds.lean), theta_n_cos/sin and twoOmegaA_cos/sin (TrigBounds.lean), sqrt bounds (here).
from fractions import Fraction as F
import sys, math
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 121
A, OMEGA = F(12, 5), F(169, 2)
ROUND = 10**12
def rd(lo, hi): return F(math.floor(lo*ROUND), ROUND), F(math.ceil(hi*ROUND), ROUND)
def rat(x): return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def mulb(a, b):
    c = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]; return min(c), max(c)
def addb(a, b): return a[0]+b[0], a[1]+b[1]
def scale(c, a): return (c*a[0], c*a[1]) if c >= 0 else (c*a[1], c*a[0])
# --- reproduce the bounds of the other generators exactly ---
import importlib.util, os, subprocess, json
exec(open('gen_coeffs.py').read().split("lines = ['import Mathlib'")[0])   # gives L, U, DB? no: DB computed inside loop below
# recompute DB/FB exactly as gen_coeffs.py
DB = {1: (F(1), F(1))}; FB = {}
KLO, KHI = F(284079043840412, 10**15), F(284079043840413, 10**15)
def rd14(lo, hi): return F(math.floor(lo*10**14), 10**14), F(math.ceil(hi*10**14), 10**14)
for n in range(2, NMAX+1):
    pairs = [(d, n//d) for d in divisors(n)]
    tot_lo, tot_hi = F(0), F(0)
    for d, e in pairs:
        if d == 1: continue
        lo, hi = mulb(u_bounds(d), DB[e]); tot_lo += lo; tot_hi += hi
    DB[n] = rd14(-tot_hi, -tot_lo)
for n in range(2, NMAX+1):
    pairs = [(d, n//d) for d in divisors(n)]
    tot_lo, tot_hi = F(0), F(0)
    for d, e in pairs:
        if d == 1 or u_bounds(d) == (F(0), F(0)): continue
        p2 = mulb(mulb((L[d], U[d]), u_bounds(d)), DB[e]); tot_lo += p2[0]; tot_hi += p2[1]
    FB[n] = rd14(tot_lo, tot_hi)
# trig bounds: reproduce gen_trig.py's numbers by importing its emit machinery? simpler: re-run its core
trig_src = open('gen_trig.py').read()
ns = {}
exec(trig_src.split("lines = ['import Mathlib'")[0], ns)      # defines center_bounds, L, U, etc.
PI_LO, PI_HI = ns['PI_LO'], ns['PI_HI']
def trig_bounds(thlo, thhi):
    thmid = (thlo + thhi)/2
    M = round(float(thmid / (PI_LO + PI_HI) * 4)); q, s = divmod(M, 4)
    pimid = (PI_LO + PI_HI)/2
    xexact = thmid - M*pimid/2; x0 = F(round(xexact * 10**6), 10**6)
    delta = (thhi - thlo)/2 + abs(M)*(PI_HI - PI_LO)/4 + abs(xexact - x0)
    cl, cu, sl, su = ns['center_bounds'](x0)
    crl, cru, srl, sru = cl - delta, cu + delta, sl - delta, su + delta
    if s == 0:   return (crl, cru), (srl, sru)
    elif s == 1: return (-sru, -srl), (crl, cru)
    elif s == 2: return (-cru, -crl), (-sru, -srl)
    else:        return (srl, sru), (-cru, -crl)
C2A, S2A = trig_bounds(F(2028, 5), F(2028, 5))
def sqrt_bounds(n):
    r = F(math.isqrt(n * 10**24), 10**12)   # floor(√n · 1e12)/1e12
    return r, r + F(1, 10**12)
lines = ['import Mathlib', 'import DHPacket', 'import DHNumerics', 'import DHLogBounds', 'import DHTrigBounds', 'import ' + ('DHCoeffs' if NMAX == 121 else f'Coeffs{NMAX}'), '',
         '/-! # Generated: lower bounds for the prime terms and their partial sums (round 261, certificate stage 3) -/', '',
         'open Real Finset', '', 'namespace PsiOmega', '',
         '/-- The prime term of `QDHu_packet_eq` at `(a, ω) = (12/5, 169/2)`. -/',
         'noncomputable def primeTerm (n : ℕ) : ℝ := fDH n / Real.sqrt n * ((2 * (12 / 5) - Real.log n) / 2 * Real.cos (169 / 2 * Real.log n)',
         '    + Real.sin (169 / 2 * (2 * (12 / 5) - Real.log n)) / (2 * (169 / 2)))', '']
TL = {}
for n in range(2, NMAX+1):
    slo, shi = sqrt_bounds(n)
    lines += [f"theorem sqrt_bounds_{n} : {rat(slo)} ≤ Real.sqrt {n} ∧ Real.sqrt {n} ≤ {rat(shi)} := by",
              "  constructor",
              f"  · calc {rat(slo)} = Real.sqrt ({rat(slo)} ^ 2) := (Real.sqrt_sq (by norm_num)).symm",
              f"      _ ≤ Real.sqrt {n} := Real.sqrt_le_sqrt (by norm_num)",
              f"  · calc Real.sqrt {n} ≤ Real.sqrt ({rat(shi)} ^ 2) := Real.sqrt_le_sqrt (by norm_num)",
              f"      _ = {rat(shi)} := Real.sqrt_sq (by norm_num)", ""]
    cb, sb = trig_bounds(OMEGA*L[n], OMEGA*U[n])
    lg = (L[n], U[n]); inv_s = (1/shi, 1/slo)
    # sin(ω(2a − log n)) = sin(2ωa − θ) = sin(2ωa) cos θ − cos(2ωa) sin θ
    sin_term = addb(mulb(S2A, cb), scale(-1, mulb(C2A, sb)))
    lin = (2*A - lg[1], 2*A - lg[0])                 # 2a − log n
    half = scale(F(1, 2), lin)
    br = addb(mulb(half, cb), scale(1/(2*OMEGA), sin_term))
    tot = mulb(mulb(FB[n], inv_s), br)
    tlo, thi = rd(tot[0], tot[1]); TL[n] = tlo
    out = [f"theorem primeTerm_bounds_{n} : {rat(tlo)} ≤ primeTerm {n} ∧ primeTerm {n} ≤ {rat(thi)} := by",
           "  unfold primeTerm",
           "  push_cast",
           f"  have hf := fDH_bounds_{n}", f"  have hl := PsiOmega.Num.log_bound_{n}",
           f"  have hc := PsiOmega.Num.theta_{n}_cos", f"  have hs := PsiOmega.Num.theta_{n}_sin",
           "  have hc2 := PsiOmega.Num.twoOmegaA_cos", "  have hs2 := PsiOmega.Num.twoOmegaA_sin",
           f"  have hq := sqrt_bounds_{n}",
           f"  have hqpos : (0 : ℝ) < Real.sqrt {n} := Real.sqrt_pos.2 (by norm_num)",
           f"  have hinv := PsiOmega.Num.inv_bounds hq (by norm_num)",
           f"  have hsin : Real.sin (169 / 2 * (2 * (12 / 5) - Real.log {n})) = Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log {n}) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log {n}) := by",
           f"    rw [show (169 / 2 : ℝ) * (2 * (12 / 5) - Real.log {n}) = 2028 / 5 - 169 / 2 * Real.log {n} by ring, Real.sin_sub]",
           "  rw [hsin, div_eq_mul_inv (fDH _)]",
           # bound pieces
           "  have p1 := PsiOmega.Num.mul_bounds hs2 hc",
           "  norm_num at p1",
           "  have p2 := PsiOmega.Num.mul_bounds hc2 hs",
           "  norm_num at p2",
           f"  have hlin : {rat(half[0])} ≤ (2 * (12 / 5) - Real.log {n}) / 2 ∧ (2 * (12 / 5) - Real.log {n}) / 2 ≤ {rat(half[1])} := by",
           "    constructor <;> linarith [hl.1, hl.2]",
           "  have p3 := PsiOmega.Num.mul_bounds hlin hc",
           "  norm_num at p3",
           f"  have hbr : {rat(br[0])} ≤ (2 * (12 / 5) - Real.log {n}) / 2 * Real.cos (169 / 2 * Real.log {n}) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log {n}) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log {n})) / (2 * (169 / 2)) ∧ (2 * (12 / 5) - Real.log {n}) / 2 * Real.cos (169 / 2 * Real.log {n}) + (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log {n}) - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log {n})) / (2 * (169 / 2)) ≤ {rat(br[1])} := by",
           "    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]",
           "  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr",
           "  norm_num at p4",
           "  constructor <;> linarith [p4.1, p4.2]", ""]
    lines += out
# partial sums
P = {}
P[2] = TL[2]
lines += [f"theorem partial_2 : {rat(P[2])} ≤ ∑ n ∈ Finset.Icc 2 2, primeTerm n := by",
          "  rw [Finset.Icc_self, Finset.sum_singleton]", "  exact primeTerm_bounds_2.1", ""]
for k in range(3, NMAX+1):
    P[k] = P[k-1] + TL[k]
    lines += [f"theorem partial_{k} : {rat(P[k])} ≤ ∑ n ∈ Finset.Icc 2 {k}, primeTerm n := by",
              f"  rw [show ({k} : ℕ) = {k-1} + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]",
              f"  have h1 := partial_{k-1}", f"  have h2 := primeTerm_bounds_{k}", "  linarith [h1, h2.1]", ""]
lines += ['end PsiOmega', '', f'#print axioms PsiOmega.partial_{NMAX}']
open('DHTerms.lean' if NMAX == 121 else f'Terms{NMAX}.lean', 'w').write('\n'.join(lines) + '\n')
print(f"wrote n ≤ {NMAX}; S ≥ {float(P[NMAX]):.9f}  (true S at 121 = 5.646212136)")
