# Generate DHOddTerms.lean: for each n = 2..121 a lower bound on the prime term of the SINE packet
#   T⁻ n = fDH n / √n * ((2a − log n)/2 * cos(ω log n) − sin(ω(2a − log n))/(2ω)),  a = 12/5, ω = 169/2,
# (the autocorrelation of 1_{[−a,a]}·sin(ω·) at log n: the cosine packet's with the sidelobe sign flipped),
# and the partial sums Σ_{n ∈ Icc 2 k} T⁻ n ≥ P_k, k = 2..121.
# Adapted from gen_terms.py (round 261): the same atoms fDH_bounds_n (DHCoeffs.lean), log_bound_n (DHLogBounds.lean),
# theta_n_cos/sin and twoOmegaA_cos/sin (DHTrigBounds.lean), and sqrt_bounds_n, which is reused from DHTerms.lean
# (not re-emitted). The only change to the arithmetic is the sign of the sin(ω(2a − log n))/(2ω) term.
# The sibling generators gen_coeffs.py and gen_trig.py are read from this script's directory, or from $DH_LEAN_GEN.
from fractions import Fraction as F
import sys, math, os
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 121
A, OMEGA = F(12, 5), F(169, 2)
ROUND = 10**12
def rd(lo, hi): return F(math.floor(lo*ROUND), ROUND), F(math.ceil(hi*ROUND), ROUND)
def rat(x): return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def mulb(a, b):
    c = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]; return min(c), max(c)
def addb(a, b): return a[0]+b[0], a[1]+b[1]
def scale(c, a): return (c*a[0], c*a[1]) if c >= 0 else (c*a[1], c*a[0])
GEN = os.environ.get('DH_LEAN_GEN', os.path.dirname(os.path.abspath(__file__)))
# --- reproduce the bounds of the other generators exactly (as gen_terms.py does) ---
exec(open(os.path.join(GEN, 'gen_coeffs.py')).read().split("lines = ['import Mathlib'")[0])
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
trig_src = open(os.path.join(GEN, 'gen_trig.py')).read()
ns = {}
exec(trig_src.split("lines = ['import Mathlib'")[0], ns)
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
def sqrt_bounds(n):   # must agree with gen_terms.py's sqrt_bounds_n (reused from DHTerms.lean)
    r = F(math.isqrt(n * 10**24), 10**12)
    return r, r + F(1, 10**12)
lines = ['import Mathlib', 'import DHPacket', 'import DHNumerics', 'import DHLogBounds', 'import DHTrigBounds',
         'import ' + ('DHCoeffs' if NMAX == 121 else f'Coeffs{NMAX}'), 'import ' + ('DHTerms' if NMAX == 121 else f'Terms{NMAX}'), '',
         '/-! # Generated (gen_oddterms.py): lower bounds for the prime terms of the sine packet and their partial sums',
         '',
         'The prime term of `QDHu_sinPacket_eq` at `(a, ω) = (12/5, 169/2)`, from the autocorrelation',
         '`f(u) = ½(2a − u)cos(ωu) − sin(ω(2a − u))/(2ω)` of `1_{[−a,a]}·sin(ω·)`. The atoms are those of `DHTerms`',
         '(whose `sqrt_bounds_n` are reused); only the sign of the sidelobe term differs from `primeTerm`. -/', '',
         'open Real Finset', '', 'namespace PsiOmega', '',
         '/-- The prime term of `QDHu_sinPacket_eq` at `(a, ω) = (12/5, 169/2)`. -/',
         'noncomputable def oddTerm (n : ℕ) : ℝ := fDH n / Real.sqrt n * ((2 * (12 / 5) - Real.log n) / 2 * Real.cos (169 / 2 * Real.log n)',
         '    - Real.sin (169 / 2 * (2 * (12 / 5) - Real.log n)) / (2 * (169 / 2)))', '']
TL = {}
for n in range(2, NMAX+1):
    slo, shi = sqrt_bounds(n)
    cb, sb = trig_bounds(OMEGA*L[n], OMEGA*U[n])
    lg = (L[n], U[n]); inv_s = (1/shi, 1/slo)
    # sin(ω(2a − log n)) = sin(2ωa − θ) = sin(2ωa) cos θ − cos(2ωa) sin θ
    sin_term = addb(mulb(S2A, cb), scale(-1, mulb(C2A, sb)))
    lin = (2*A - lg[1], 2*A - lg[0])                 # 2a − log n
    half = scale(F(1, 2), lin)
    br = addb(mulb(half, cb), scale(-1/(2*OMEGA), sin_term))     # the sidelobe enters with a minus sign
    tot = mulb(mulb(FB[n], inv_s), br)
    tlo, thi = rd(tot[0], tot[1]); TL[n] = tlo
    expr = (f"(2 * (12 / 5) - Real.log {n}) / 2 * Real.cos (169 / 2 * Real.log {n}) - (Real.sin (2028 / 5) * Real.cos (169 / 2 * Real.log {n})"
            f" - Real.cos (2028 / 5) * Real.sin (169 / 2 * Real.log {n})) / (2 * (169 / 2))")
    out = [f"theorem oddTerm_bounds_{n} : {rat(tlo)} ≤ oddTerm {n} ∧ oddTerm {n} ≤ {rat(thi)} := by",
           "  unfold oddTerm",
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
           "  have p1 := PsiOmega.Num.mul_bounds hs2 hc",
           "  norm_num at p1",
           "  have p2 := PsiOmega.Num.mul_bounds hc2 hs",
           "  norm_num at p2",
           f"  have hlin : {rat(half[0])} ≤ (2 * (12 / 5) - Real.log {n}) / 2 ∧ (2 * (12 / 5) - Real.log {n}) / 2 ≤ {rat(half[1])} := by",
           "    constructor <;> linarith [hl.1, hl.2]",
           "  have p3 := PsiOmega.Num.mul_bounds hlin hc",
           "  norm_num at p3",
           f"  have hbr : {rat(br[0])} ≤ {expr} ∧ {expr} ≤ {rat(br[1])} := by",
           "    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]",
           "  have p4 := PsiOmega.Num.mul_bounds (PsiOmega.Num.mul_bounds hf hinv) hbr",
           "  norm_num at p4",
           "  constructor <;> linarith [p4.1, p4.2]", ""]
    lines += out
# partial sums
P = {}
P[2] = TL[2]
lines += [f"theorem oddPartial_2 : {rat(P[2])} ≤ ∑ n ∈ Finset.Icc 2 2, oddTerm n := by",
          "  rw [Finset.Icc_self, Finset.sum_singleton]", "  exact oddTerm_bounds_2.1", ""]
for k in range(3, NMAX+1):
    P[k] = P[k-1] + TL[k]
    lines += [f"theorem oddPartial_{k} : {rat(P[k])} ≤ ∑ n ∈ Finset.Icc 2 {k}, oddTerm n := by",
              f"  rw [show ({k} : ℕ) = {k-1} + 1 by norm_num, Finset.sum_Icc_succ_top (by norm_num)]",
              f"  have h1 := oddPartial_{k-1}", f"  have h2 := oddTerm_bounds_{k}", "  linarith [h1, h2.1]", ""]
lines += ['end PsiOmega', '', f'#print axioms PsiOmega.oddPartial_{NMAX}']
open('DHOddTerms.lean' if NMAX == 121 else f'OddTerms{NMAX}.lean', 'w').write('\n'.join(lines) + '\n')
print(f"wrote n ≤ {NMAX}; S⁻ ≥ {float(P[NMAX]):.12f}  = {P[NMAX].numerator}/{P[NMAX].denominator}")
