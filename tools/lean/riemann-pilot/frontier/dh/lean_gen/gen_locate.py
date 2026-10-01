# Generate the stage-3 numerics of the zero-location certificate (DHLocateSkeleton):
#   DHLocateExp.lean   helper lemmas + two-sided bounds for ex(1617/2000, n) = exp(-(1617/2000) log n)
#   DHLocateTrig.lean  two-sided bounds for cC n = cos(t log n), sC n = sin(t log n), t = 856993/10000
#   DHLocateNum.lean   products, block sums, Q-tails, H1 |PRe 20 12| ≤ 1/1000, H2 |PIm 20 12| ≤ 1/1000,
#                      H3 1 ≤ ARe 20 12, and dh_zero_located
# for n ∈ NS = {5m + j : m < 20, j = 1..4} ∪ {101, ..., 104} (n = 1 handled by ex_one/cC_one/sC_one).
# Exact rational arithmetic (fractions.Fraction) throughout; every rounding is outward.
#
# Inputs (all kernel-checked lemmas):
#   log n       PsiOmega.Num.log_bound_n (DHLogBounds; parsed from the source, so the numbers are exactly
#               the lemma's), rounded outward to 1e-15 after scaling.
#   exp(-y)     Real.exp_bound at x = -(y/8), 12 terms (remainder (y/8)^12 · 13/(12!·12)), then
#               exp(-y) = exp(-(y/8))^8 (Real.exp_nat_mul) and pow_le_pow_left₀.
#   cos, sin    gen_trig.py's scheme: θ = r + M·π/2, M = round(θ/(π/2)), |r| ≤ π/4 + δ; r bounded with
#               Real.pi_gt_d20 / Real.pi_lt_d20; cos/sin at a rational centre x₀ (1e-9 grid) by
#               PsiOmega.Num.cos_bounds / sin_bounds (alternating series to degree 12/13), transferred by
#               Real.abs_cos_sub_cos_le / abs_sin_sub_sin_le.
#   κ           PsiOmega.kappa_bounds (15 digits).
#   Q-values    the exact Gaussian rationals inside PRe_20 / PIm_20 / ARe_20 (parsed from the skeleton).
from fractions import Fraction as F
import math, re, sys, os
import mpmath as mp
mp.mp.dps = 60

HERE = os.path.dirname(os.path.abspath(__file__))
PILOT = '/home/user/r-infinite/tools/lean/riemann-pilot'
SKEL = os.path.join(PILOT, 'src', 'DHLocateSkeleton.lean')
LOGSRC = os.path.join(PILOT, 'src', 'DHLogBounds.lean')

SIG = F(1617, 2000)
TT = F(856993, 10000)
D = 10**15                       # rounding grid for every stored bound
PI_LO = F(314159265358979323846, 10**20)   # Real.pi_gt_d20
PI_HI = F(314159265358979323847, 10**20)   # Real.pi_lt_d20
X0_GRID = 10**9

TEST = [int(a) for a in sys.argv[1:]]      # optional: restrict to these n (test mode)

def fm(x): return mp.mpf(x.numerator) / x.denominator
def rd_lo(x, d=D): return F(math.floor(x * d), d)
def rd_hi(x, d=D): return F(math.ceil(x * d), d)
def rat(x):
    return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def mulb(a, b):
    c = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]; return min(c), max(c)
def rdb(b): return rd_lo(b[0]), rd_hi(b[1])
def addb(*bs): return sum(b[0] for b in bs), sum(b[1] for b in bs)
def negb(b): return -b[1], -b[0]

# ---------------------------------------------------------------- log bounds (from the lemma source)
LB = {}
src = open(LOGSRC).read()
for m in re.finditer(r"theorem log_bound_(\d+) : \((\d+) / (\d+) : ℝ\) ≤ Real\.log \d+ ∧ Real\.log \d+ ≤ \((\d+) / (\d+) : ℝ\)", src):
    n = int(m.group(1)); LB[n] = (F(int(m.group(2)), int(m.group(3))), F(int(m.group(4)), int(m.group(5))))
assert all(n in LB for n in range(2, 122)), sorted(LB)[:5]
for n in range(2, 122):
    assert fm(LB[n][0]) <= mp.log(n) <= fm(LB[n][1])
LOGW = max(float(LB[n][1] - LB[n][0]) for n in range(2, 122))

NS = [5*m + j for m in range(20) for j in range(1, 5)] + [101, 102, 103, 104]
NT = [n for n in NS if n != 1]
if TEST: NT = [n for n in NT if n in TEST]

# ---------------------------------------------------------------- exp
EXPC = F(13, math.factorial(12) * 12)
def P12(r): return sum(F((-1)**i) * r**i / math.factorial(i) for i in range(12))
POLY_LEAN = ("1 - {r} + {r} ^ 2 / 2 - {r} ^ 3 / 6 + {r} ^ 4 / 24 - {r} ^ 5 / 120 + {r} ^ 6 / 720 - {r} ^ 7 / 5040"
             " + {r} ^ 8 / 40320 - {r} ^ 9 / 362880 + {r} ^ 10 / 3628800 - {r} ^ 11 / 39916800")
EXB = {}; EXDATA = {}
for n in NT:
    ylo, yhi = rd_lo(SIG * LB[n][0]), rd_hi(SIG * LB[n][1])
    assert 0 <= ylo and yhi <= 8
    r1 = yhi / 8; A = P12(r1) - r1**12 * EXPC; a = rd_lo(A, 10**20); assert a > 0
    elo = rd_lo(a**8)
    r2 = ylo / 8; B = P12(r2) + r2**12 * EXPC; b = rd_hi(B, 10**20)
    ehi = rd_hi(b**8)
    tv = mp.exp(-mp.mpf(1617)/2000 * mp.log(n))
    assert fm(elo) <= tv <= fm(ehi), n
    EXB[n] = (elo, ehi); EXDATA[n] = (ylo, yhi, a, b)

# ---------------------------------------------------------------- trig
def cos_poly(x, N): return sum(F((-1)**i) * x**(2*i) / math.factorial(2*i) for i in range(N))
def sin_poly(x, N): return sum(F((-1)**i) * x**(2*i+1) / math.factorial(2*i+1) for i in range(N))
def center_bounds(x0):
    cl, cu = cos_poly(x0, 6), cos_poly(x0, 7)
    if x0 >= 0: sl, su = sin_poly(x0, 6), sin_poly(x0, 7)
    else: sl, su = -sin_poly(-x0, 7), -sin_poly(-x0, 6)
    return cl, cu, sl, su
CB = {}; SB = {}; TRIGW = {}
trig_lines = []
def emit_trig(name, theta_expr, thlo, thhi, hl_lines):
    thmid = (thlo + thhi) / 2
    pimid = (PI_LO + PI_HI) / 2
    M = round(thmid / (pimid / 2))
    q, s = divmod(M, 4)
    xexact = thmid - M * pimid / 2
    x0 = F(round(xexact * X0_GRID), X0_GRID)
    delta = (thhi - thlo) / 2 + abs(M) * (PI_HI - PI_LO) / 4 + abs(xexact - x0)
    x0s = rat(x0) if x0 >= 0 else f"(-{rat(-x0)})"
    assert abs(x0) + delta <= 1, (name, x0, delta)
    cl, cu, sl, su = center_bounds(x0)
    crl, cru, srl, sru = cl - delta, cu + delta, sl - delta, su + delta
    # outward rounding of the reduced-angle cos/sin bounds
    crl, cru, srl, sru = rd_lo(crl), rd_hi(cru), rd_lo(srl), rd_hi(sru)
    if s == 0:   CL, CU, SL, SU = crl, cru, srl, sru
    elif s == 1: CL, CU, SL, SU = -sru, -srl, crl, cru
    elif s == 2: CL, CU, SL, SU = -cru, -crl, -sru, -srl
    else:        CL, CU, SL, SU = srl, sru, -cru, -crl
    red = f"PsiOmega.Num.redAngle ({theta_expr}) {M}"
    out = []
    out += [f"theorem {name}_r_bounds : {rat(x0 - delta)} ≤ {red} ∧ {red} ≤ {rat(x0 + delta)} := by"]
    out += hl_lines
    out += ["  have hpi1 := Real.pi_gt_d20", "  have hpi2 := Real.pi_lt_d20", "  unfold PsiOmega.Num.redAngle", "  push_cast",
            "  constructor <;> linarith [hl.1, hl.2]", ""]
    shift = {0: "", 1: " + π / 2", 2: " + π", 3: " + π + π / 2"}[s]
    out += [f"theorem {name}_eq : ({theta_expr}) = ({red}{shift}) + (({q} : ℤ) : ℝ) * (2 * π) := by",
            "  unfold PsiOmega.Num.redAngle", "  push_cast", "  ring", ""]
    out += [f"theorem {name}_cos_r : {rat(crl)} ≤ Real.cos ({red}) ∧ Real.cos ({red}) ≤ {rat(cru)} := by",
            f"  have hr := {name}_r_bounds",
            f"  have hc := PsiOmega.Num.cos_bounds (x := {x0s}) (by rw [abs_le]; constructor <;> norm_num)",
            "  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc",
            "  norm_num at hc",
            f"  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le ({red}) {x0s})"]
    if x0 < 0:
        out += ["  rw [Real.cos_neg] at hlip"]
    out += [f"  have hd : |{red} - {x0s}| ≤ {rat(delta)} := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]",
            f"  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg ({red} - {x0s})]", ""]
    if x0 >= 0:
        sin_center = [f"  have hs := PsiOmega.Num.sin_bounds (x := {x0s}) (by norm_num) (by norm_num)",
                      "  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs", "  norm_num at hs"]
    else:
        sin_center = [f"  have hs0 := PsiOmega.Num.sin_bounds (x := {rat(-x0)}) (by norm_num) (by norm_num)",
                      "  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0", "  norm_num at hs0",
                      f"  have hs : -({rat(sin_poly(-x0, 7))}) ≤ Real.sin {x0s} ∧ Real.sin {x0s} ≤ -({rat(sin_poly(-x0, 6))}) := by",
                      "    rw [Real.sin_neg]",
                      "    constructor <;> linarith [hs0.1, hs0.2]"]
    out += [f"theorem {name}_sin_r : {rat(srl)} ≤ Real.sin ({red}) ∧ Real.sin ({red}) ≤ {rat(sru)} := by",
            f"  have hr := {name}_r_bounds"] + sin_center + [
            f"  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le ({red}) {x0s})",
            f"  have hd : |{red} - {x0s}| ≤ {rat(delta)} := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]",
            f"  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg ({red} - {x0s})]", ""]
    cos_rw = {0: "  rw [Real.cos_add_int_mul_two_pi]",
              1: "  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]",
              2: "  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]",
              3: "  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]"}[s]
    sin_rw = {0: "  rw [Real.sin_add_int_mul_two_pi]",
              1: "  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]",
              2: "  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]",
              3: "  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]"}[s]
    out += [f"theorem {name}_cos : {rat(CL)} ≤ Real.cos ({theta_expr}) ∧ Real.cos ({theta_expr}) ≤ {rat(CU)} := by",
            f"  have hc := {name}_cos_r", f"  have hs := {name}_sin_r", f"  rw [{name}_eq]", cos_rw,
            "  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]", ""]
    out += [f"theorem {name}_sin : {rat(SL)} ≤ Real.sin ({theta_expr}) ∧ Real.sin ({theta_expr}) ≤ {rat(SU)} := by",
            f"  have hc := {name}_cos_r", f"  have hs := {name}_sin_r", f"  rw [{name}_eq]", sin_rw,
            "  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]", ""]
    return out, (CL, CU), (SL, SU), (M, x0, delta)

for n in NT:
    thlo, thhi = rd_lo(TT * LB[n][0]), rd_hi(TT * LB[n][1])
    th = f"856993 / 10000 * Real.log {n}"
    out, cb, sb, info = emit_trig(f"thL_{n}", th, thlo, thhi,
        [f"  have hl0 := PsiOmega.Num.log_bound_{n}",
         f"  have hl : {rat(thlo)} ≤ 856993 / 10000 * Real.log {n} ∧ 856993 / 10000 * Real.log {n} ≤ {rat(thhi)} := by",
         "    constructor <;> linarith [hl0.1, hl0.2]"])
    tc = mp.cos(mp.mpf(856993)/10000 * mp.log(n)); ts = mp.sin(mp.mpf(856993)/10000 * mp.log(n))
    assert fm(cb[0]) <= tc <= fm(cb[1]) and fm(sb[0]) <= ts <= fm(sb[1]), n
    out += [f"theorem cCB_{n} : {rat(cb[0])} ≤ cC {n} ∧ cC {n} ≤ {rat(cb[1])} := by",
            "  unfold cC", "  simp only [Nat.cast_ofNat]", f"  exact thL_{n}_cos", "",
            f"theorem sCB_{n} : {rat(sb[0])} ≤ sC {n} ∧ sC {n} ≤ {rat(sb[1])} := by",
            "  unfold sC", "  simp only [Nat.cast_ofNat]", f"  exact thL_{n}_sin", ""]
    trig_lines += out
    CB[n] = cb; SB[n] = sb; TRIGW[n] = info

# ---------------------------------------------------------------- Lean: DHLocateExp.lean
NAMES = ' '.join(['DHLocateExp', 'DHLocateTrig', 'DHLocateNum'])
SUFFIX = '' if not TEST else 'T'
exp_lines = ['import DHLocateSkeleton', '',
  '/-! # Generated (gen_locate.py): two-sided bounds for `ex (1617/2000) n = exp(-(1617/2000) log n)`, `n ∈ NS`',
  '',
  '`log n` from `PsiOmega.Num.log_bound_n`; `exp(-y) = exp(-(y/8))^8` (`Real.exp_nat_mul`) with `exp(-(y/8))` from',
  '`Real.exp_bound` (12 terms). Stage 3 of the zero-location certificate (`DHLocateSkeleton`). -/', '',
  'open Real Finset', '', 'namespace PsiOmega.Locate', '',
  '/-- Interval product with explicit outer bounds; the eight corner checks are numeral comparisons. -/',
  'theorem mul_bounds_of {x y a b c d lo hi : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)',
  '    (h1 : lo ≤ a * c) (h2 : lo ≤ a * d) (h3 : lo ≤ b * c) (h4 : lo ≤ b * d)',
  '    (h5 : a * c ≤ hi) (h6 : a * d ≤ hi) (h7 : b * c ≤ hi) (h8 : b * d ≤ hi) :',
  '    lo ≤ x * y ∧ x * y ≤ hi := by',
  '  have h := PsiOmega.Num.mul_bounds hx hy',
  '  exact ⟨le_trans (le_min (le_min h1 h2) (le_min h3 h4)) h.1,',
  '    le_trans h.2 (max_le (max_le h5 h6) (max_le h7 h8))⟩', '',
  '/-- `exp(-r)` within `r¹²·13/(12!·12)` of its degree-11 Taylor polynomial, `0 ≤ r ≤ 1` (`Real.exp_bound`). -/',
  'theorem exp_neg_poly_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :',
  '    ' + POLY_LEAN.format(r='r') + ' - r ^ 12 * (13 / 5748019200) ≤ Real.exp (-r) ∧',
  '      Real.exp (-r) ≤ ' + POLY_LEAN.format(r='r') + ' + r ^ 12 * (13 / 5748019200) := by',
  '  have hx : |(-r)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hr0]; exact hr1',
  '  have h := Real.exp_bound hx (n := 12) (by norm_num)',
  '  rw [abs_neg, abs_of_nonneg hr0] at h',
  '  have h2 := abs_sub_le_iff.1 h',
  '  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at h2',
  '  norm_num at h2',
  '  constructor <;> nlinarith [h2.1, h2.2]', '',
  '/-- Lower bound for `exp(-q)`, `0 ≤ q ≤ 8`, from the polynomial at `q/8` and the eighth power. -/',
  'theorem exp_neg_ge_of {q a lo : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 8) (ha0 : 0 ≤ a)',
  '    (ha : a ≤ ' + POLY_LEAN.format(r='(q / 8)') + ' - (q / 8) ^ 12 * (13 / 5748019200))',
  '    (hlo : lo ≤ a ^ 8) : lo ≤ Real.exp (-q) := by',
  '  have hb := exp_neg_poly_bounds (r := q / 8) (by positivity) (by linarith)',
  '  have h1 : a ≤ Real.exp (-(q / 8)) := le_trans ha hb.1',
  '  have e : Real.exp (-q) = Real.exp (-(q / 8)) ^ 8 := by',
  '    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring',
  '  rw [e]',
  '  exact le_trans hlo (pow_le_pow_left₀ ha0 h1 8)', '',
  '/-- Upper bound for `exp(-q)`, `0 ≤ q ≤ 8`. -/',
  'theorem exp_neg_le_of {q b hi : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 8)',
  '    (hb : ' + POLY_LEAN.format(r='(q / 8)') + ' + (q / 8) ^ 12 * (13 / 5748019200) ≤ b)',
  '    (hhi : b ^ 8 ≤ hi) : Real.exp (-q) ≤ hi := by',
  '  have hp := exp_neg_poly_bounds (r := q / 8) (by positivity) (by linarith)',
  '  have h1 : Real.exp (-(q / 8)) ≤ b := le_trans hp.2 hb',
  '  have e : Real.exp (-q) = Real.exp (-(q / 8)) ^ 8 := by',
  '    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring',
  '  rw [e]',
  '  exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le h1 8) hhi', '',
  'theorem ex_one : ex (1617 / 2000) 1 = 1 := by simp [ex]', '',
  'theorem cC_one : cC 1 = 1 := by simp [cC]', '',
  'theorem sC_one : sC 1 = 0 := by simp [sC]', '']
for n in NT:
    elo, ehi = EXB[n]; ylo, yhi, a, b = EXDATA[n]
    exp_lines += [
      f"theorem exB_{n} : {rat(elo)} ≤ ex (1617 / 2000) {n} ∧ ex (1617 / 2000) {n} ≤ {rat(ehi)} := by",
      f"  have hl := PsiOmega.Num.log_bound_{n}",
      f"  have hlo := exp_neg_ge_of (q := {rat(yhi)}) (a := {rat(a)}) (lo := {rat(elo)}) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)",
      f"  have hhi := exp_neg_le_of (q := {rat(ylo)}) (b := {rat(b)}) (hi := {rat(ehi)}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)",
      "  unfold ex", "  simp only [Nat.cast_ofNat]", "  constructor",
      "  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))",
      "  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi", ""]
exp_lines += ['end PsiOmega.Locate', '', f'#print axioms PsiOmega.Locate.exB_{NT[-1]}']

trig_hdr = ['import DHLocateExp' + SUFFIX, '',
  '/-! # Generated (gen_locate.py): bounds for `cC n = cos(t log n)`, `sC n = sin(t log n)`, `t = 856993/10000`, `n ∈ NS`',
  '',
  'Reduction `θ = r + M·π/2` with `Real.pi_gt_d20`/`Real.pi_lt_d20`; `cos`, `sin` at a rational centre by',
  '`PsiOmega.Num.cos_bounds`/`sin_bounds`, transferred by `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`. -/', '',
  'open Real Finset', '', 'namespace PsiOmega.Locate', '']
trig_all = trig_hdr + trig_lines + ['end PsiOmega.Locate', '', f'#print axioms PsiOmega.Locate.cCB_{NT[-1]}', f'#print axioms PsiOmega.Locate.sCB_{NT[-1]}']

open(os.path.join(HERE, 'DHLocateExp' + SUFFIX + '.lean'), 'w').write('\n'.join(exp_lines) + '\n')
open(os.path.join(HERE, 'DHLocateTrig' + SUFFIX + '.lean'), 'w').write('\n'.join(trig_all) + '\n')

# ---------------------------------------------------------------- report atoms
print(f"log widths max {LOGW:.3e}")
ew = [float(EXB[n][1] - EXB[n][0]) for n in NT]
cw = [float(CB[n][1] - CB[n][0]) for n in NT]; sw = [float(SB[n][1] - SB[n][0]) for n in NT]
print(f"ex widths max {max(ew):.3e}; cos widths max {max(cw):.3e}; sin widths max {max(sw):.3e}; M max {max(abs(TRIGW[n][0]) for n in NT)}")

# ---------------------------------------------------------------- Q literals (from the skeleton)
sk = open(SKEL).read()
QT = {}   # QT[(kind, j, part)] = (text, Fraction), kind ∈ {'Q','Qd'}, part ∈ {'re','im'}
for kind, fn in (('Q', 'QEM'), ('Qd', 'QEMd')):
    for j in range(1, 5):
        m = re.search(rf"theorem {fn}_cLoc_{j} : \({fn} 12 \(20 \+ {j} / 5\) cLoc\)\.re = \((-?\d+) / (\d+) : ℝ\) ∧\s*\({fn} 12 \(20 \+ {j} / 5\) cLoc\)\.im = \((-?\d+) / (\d+) : ℝ\)", sk)
        assert m, (kind, j)
        QT[(kind, j, 're')] = (f"({m.group(1)} / {m.group(2)} : ℝ)", F(int(m.group(1)), int(m.group(2))))
        QT[(kind, j, 'im')] = (f"({m.group(3)} / {m.group(4)} : ℝ)", F(int(m.group(3)), int(m.group(4))))
# the literals must occur verbatim in the three substituted statements
for key, (t, v) in QT.items():
    assert t in sk, key

KLO, KHI = F(284079043840412, 10**15), F(284079043840413, 10**15)
KB = (KLO, KHI)
num = ['import DHLocateTrig' + SUFFIX, '',
  '/-! # Generated (gen_locate.py): the interval evaluation of `PRe 20 12`, `PIm 20 12`, `ARe 20 12`',
  '',
  'Stage 3 of the zero-location certificate: the three open inequalities of `DHLocateSkeleton`',
  '(`H1`, `H2`, `H3`) from the atom bounds of `DHLocateExp` / `DHLocateTrig`, `κ` (`PsiOmega.kappa_bounds`)',
  'and `log n` (`PsiOmega.Num.log_bound_n`), by interval products (`mul_bounds_of`) and block sums; then',
  '`dh_zero_located` = `dh_zero_near_of_center'' H1 H2 H3`. -/', '',
  'open Real Finset', '', 'namespace PsiOmega.Locate', '',
  'theorem kappaB : (284079043840412 / 1000000000000000 : ℝ) ≤ kappa ∧ kappa ≤ (284079043840413 / 1000000000000000 : ℝ) := by',
  '  have h := PsiOmega.kappa_bounds', '  constructor <;> linarith [h.1, h.2]', '']
NB = 8
def mb(h1, h2): return f"mul_bounds_of {h1} {h2}" + " (by norm_num)" * NB
BND = {}   # name -> (lo, hi)
def lemma(name, expr, b, proof_lines):
    BND[name] = b
    num.append(f"theorem {name} : {rat(b[0])} ≤ {expr} ∧ {expr} ≤ {rat(b[1])} := by")
    num.extend(proof_lines); num.append('')
LG = {}
EXPR = {}
for n in NT:
    e = f"ex (1617 / 2000) {n}"
    LG[n] = (rd_lo(LB[n][0]), rd_hi(LB[n][1]))
    lemma(f"lgB_{n}", f"Real.log {n}", LG[n], [f"  have h := PsiOmega.Num.log_bound_{n}", "  constructor <;> linarith [h.1, h.2]"])
    if n > 100: continue
    j = n % 5
    for tag, at, B in (('C', 'cC', CB[n]), ('S', 'sC', SB[n])):
        ex_ = f"{e} * {at} {n}"
        b = rdb(mulb(EXB[n], B)); lemma(f"e{tag}_{n}", ex_, b, [f"  exact {mb(f'exB_{n}', f'{at}B_{n}')}"])
        EXPR[f"e{tag}_{n}"] = ex_
        if j in (2, 3):
            kx = f"kappa * ({ex_})"
            lemma(f"ke{tag}_{n}", kx, rdb(mulb(KB, b)), [f"  exact {mb('kappaB', f'e{tag}_{n}')}"])
            EXPR[f"ke{tag}_{n}"] = kx
    lx = f"Real.log {n} * ({e} * cC {n})"
    b = rdb(mulb(LG[n], BND[f"eC_{n}"])); lemma(f"leC_{n}", lx, b, [f"  exact {mb(f'lgB_{n}', f'eC_{n}')}"])
    EXPR[f"leC_{n}"] = lx
    if j in (2, 3):
        kx = f"kappa * ({lx})"
        lemma(f"kleC_{n}", kx, rdb(mulb(KB, b)), [f"  exact {mb('kappaB', f'leC_{n}')}"])
        EXPR[f"kleC_{n}"] = kx

# ---- blocks of the m-sums
def block_terms(kind, m):
    """the four summand terms (expr, bounds, sign) of block m, kind ∈ {'P','I','A'}"""
    out = []
    for j in (1, 2, 3, 4):
        n = 5*m + j
        sign = 1 if j in (1, 2) else -1
        at = 'sC' if kind == 'I' else 'cC'
        if n == 1:
            ex_ = {'P': "ex (1617 / 2000) 1 * cC 1", 'I': "ex (1617 / 2000) 1 * sC 1",
                   'A': "Real.log 1 * (ex (1617 / 2000) 1 * cC 1)"}[kind]
            val = {'P': F(1), 'I': F(0), 'A': F(0)}[kind]
            out.append((ex_, (val, val), sign, None)); continue
        base = {'P': f"eC_{n}", 'I': f"eS_{n}", 'A': f"leC_{n}"}[kind]
        name = ('k' + base) if j in (2, 3) else base
        if kind == 'A' and j in (2, 3): name = f"kleC_{n}"
        out.append((EXPR[name], BND[name], sign, name))
    return out
BLK = {}
have_all = all(n in NT for n in NS if n != 1)
if have_all:
    for kind, pre in (('P', 'PReB'), ('I', 'PImB'), ('A', 'AReB')):
        for m in range(20):
            terms = block_terms(kind, m)
            expr = terms[0][0]
            for (ex_, b, sg, nm) in terms[1:]:
                expr += (" + " if sg > 0 else " - ") + ex_
            lo = sum(b[0] if sg > 0 else -b[1] for (_, b, sg, _) in terms)
            hi = sum(b[1] if sg > 0 else -b[0] for (_, b, sg, _) in terms)
            pl = []
            hs = []
            for i, (ex_, b, sg, nm) in enumerate(terms):
                if nm is None:
                    pl.append(f"  have h{i} : {ex_} = {rat(b[0])} := by " +
                              {'P': "rw [ex_one, cC_one]; norm_num", 'I': "rw [sC_one]; norm_num",
                               'A': "rw [Real.log_one]; norm_num"}[kind])
                    hs.append(f"h{i}")
                else:
                    pl.append(f"  have h{i} := {nm}"); hs += [f"h{i}.1", f"h{i}.2"]
            pl.append(f"  constructor <;> linarith [{', '.join(hs)}]")
            lemma(f"{pre}_{m}", expr, (lo, hi), pl)
            BLK[(kind, m)] = (lo, hi)

# ---- the Q-tails
def tail_inner(kind, j):
    N = 100 + j
    Qr, Qi = QT[('Q', j, 're')], QT[('Q', j, 'im')]
    if kind == 'P':
        return f"cC {N} * {Qr[0]} + sC {N} * {Qi[0]}"
    if kind == 'I':
        return f"cC {N} * {Qi[0]} - sC {N} * {Qr[0]}"
    Dr, Di = QT[('Qd', j, 're')], QT[('Qd', j, 'im')]
    return f"cC {N} * ({Dr[0]} - Real.log {N} * {Qr[0]}) + sC {N} * ({Di[0]} - Real.log {N} * {Qi[0]})"
def scaleb(c, b): return (c*b[0], c*b[1]) if c >= 0 else (c*b[1], c*b[0])
TAIL = {}
if have_all or all(N in NT for N in (101, 102, 103, 104)):
    for kind, pre in (('P', 'PReT'), ('I', 'PImT'), ('A', 'AReT')):
        for j in (1, 2, 3, 4):
            N = 100 + j
            Qr, Qi = QT[('Q', j, 're')][1], QT[('Q', j, 'im')][1]
            inner = tail_inner(kind, j)
            pl = [f"  have hc := cCB_{N}", f"  have hs := sCB_{N}"]
            if kind == 'P':
                ib = addb(scaleb(Qr, CB[N]), scaleb(Qi, SB[N]))
            elif kind == 'I':
                ib = addb(scaleb(Qi, CB[N]), negb(scaleb(Qr, SB[N])))
            else:
                Dr, Di = QT[('Qd', j, 're')][1], QT[('Qd', j, 'im')][1]
                v1 = rdb(addb((Dr, Dr), negb(scaleb(Qr, LG[N]))))
                v2 = rdb(addb((Di, Di), negb(scaleb(Qi, LG[N]))))
                Dr_t, Di_t = QT[('Qd', j, 're')][0], QT[('Qd', j, 'im')][0]
                Qr_t, Qi_t = QT[('Q', j, 're')][0], QT[('Q', j, 'im')][0]
                p1 = rdb(mulb(CB[N], v1)); p2 = rdb(mulb(SB[N], v2))
                pl += [f"  have hl := lgB_{N}",
                       f"  have hv1 : {rat(v1[0])} ≤ {Dr_t} - Real.log {N} * {Qr_t} ∧ {Dr_t} - Real.log {N} * {Qr_t} ≤ {rat(v1[1])} := by",
                       "    constructor <;> linarith [hl.1, hl.2]",
                       f"  have hv2 : {rat(v2[0])} ≤ {Di_t} - Real.log {N} * {Qi_t} ∧ {Di_t} - Real.log {N} * {Qi_t} ≤ {rat(v2[1])} := by",
                       "    constructor <;> linarith [hl.1, hl.2]",
                       f"  have hp1 : {rat(p1[0])} ≤ cC {N} * ({Dr_t} - Real.log {N} * {Qr_t}) ∧ cC {N} * ({Dr_t} - Real.log {N} * {Qr_t}) ≤ {rat(p1[1])} :=",
                       f"    {mb('hc', 'hv1')}",
                       f"  have hp2 : {rat(p2[0])} ≤ sC {N} * ({Di_t} - Real.log {N} * {Qi_t}) ∧ sC {N} * ({Di_t} - Real.log {N} * {Qi_t}) ≤ {rat(p2[1])} :=",
                       f"    {mb('hs', 'hv2')}"]
                ib = addb(p1, p2)
            ib = rdb(ib)
            hint = "hp1.1, hp1.2, hp2.1, hp2.2" if kind == 'A' else "hc.1, hc.2, hs.1, hs.2"
            pl += [f"  have hin : {rat(ib[0])} ≤ {inner} ∧ {inner} ≤ {rat(ib[1])} := by",
                   f"    constructor <;> linarith [{hint}]"]
            tb = rdb(mulb(EXB[N], ib))
            texpr = f"ex (1617 / 2000) {N} * ({inner})"
            pl += [f"  have he : {rat(tb[0])} ≤ {texpr} ∧ {texpr} ≤ {rat(tb[1])} :=",
                   f"    {mb(f'exB_{N}', 'hin')}"]
            if j in (2, 3):
                kb = rdb(mulb(KB, tb))
                pl += [f"  exact {mb('kappaB', 'he')}"]
                lemma(f"{pre}_{j}", f"kappa * ({texpr})", kb, pl)
                TAIL[(kind, j)] = kb
            else:
                pl += ["  exact he"]
                lemma(f"{pre}_{j}", texpr, tb, pl)
                TAIL[(kind, j)] = tb

# ---- the three inequalities and the located zero
RES = {}
if have_all:
    simpPI = "  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]"
    simpA = "  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]"
    for kind, pre, tpre, H, sgn in (('P', 'PReB', 'PReT', 'H1', 1), ('I', 'PImB', 'PImT', 'H2', -1), ('A', 'AReB', 'AReT', 'H3', -1)):
        s_lo = sum(BLK[(kind, m)][0] for m in range(20)); s_hi = sum(BLK[(kind, m)][1] for m in range(20))
        if sgn < 0: s_lo, s_hi = -s_hi, -s_lo
        t = [TAIL[(kind, j)] for j in (1, 2, 3, 4)]
        t_lo = t[0][0] + t[1][0] - t[2][1] - t[3][1]; t_hi = t[0][1] + t[1][1] - t[2][0] - t[3][0]
        RES[kind] = (s_lo + t_lo, s_hi + t_hi)
        lo, hi = RES[kind]
        hs = []
        pl = []
        for m in range(20):
            pl.append(f"  have b{m} := {pre}_{m}"); hs += [f"b{m}.1", f"b{m}.2"]
        for j in (1, 2, 3, 4):
            pl.append(f"  have t{j} := {tpre}_{j}"); hs += [f"t{j}.1", f"t{j}.2"]
        unf = {'P': 'PRe_20', 'I': 'PIm_20', 'A': 'ARe_20'}[kind]
        q = {'P': 'PRe', 'I': 'PIm', 'A': 'ARe'}[kind]
        what = {'P': 'Re fEM(c)', 'I': 'Im fEM(c)', 'A': 'Re fEM′(c)'}[kind]
        CH = os.environ.get('COUNT_HB', '') == '1'
        for side, rel in (('ge', f"{rat(lo)} ≤ {q} 20 12"), ('le', f"{q} 20 12 ≤ {rat(hi)}")):
            if CH: num += ["#count_heartbeats in"]
            num += [f"/-- {'Lower' if side == 'ge' else 'Upper'} end of the enclosure of `{what}`. -/"]
            num += [f"theorem {q}_20_{side} : {rel} := by",
                    f"  rw [{unf}]", simpA if kind == 'A' else simpPI] + pl + [f"  linarith [{', '.join(hs)}]", ""]
        num += [f"/-- **The enclosure of `{what}`**: `{q} 20 12 ∈ [{float(lo):.10e}, {float(hi):.10e}]` (width `{float(hi - lo):.2e}`). -/",
                f"theorem {q}_20_mem : {rat(lo)} ≤ {q} 20 12 ∧ {q} 20 12 ≤ {rat(hi)} := ⟨{q}_20_ge, {q}_20_le⟩", ""]
        if kind in ('P', 'I'):
            assert -F(1, 1000) <= lo and hi <= F(1, 1000), (kind, RES[kind])
            num += [f"/-- Open inequality `{H}` of `DHLocateSkeleton`. -/",
                    f"theorem {H} : |{q} 20 12| ≤ 1 / 1000 := by",
                    f"  have h := {q}_20_mem", "  rw [abs_le]", "  constructor <;> linarith [h.1, h.2]", ""]
        else:
            assert 1 <= lo, RES[kind]
            num += [f"/-- Open inequality `{H}` of `DHLocateSkeleton`. -/",
                    f"theorem {H} : 1 ≤ ARe 20 12 := by",
                    f"  have h := {q}_20_mem", "  linarith [h.1]", ""]
    num += ["/-- **A kernel-checked zero of the Davenport–Heilbronn function off the critical line**: within `1/100` of",
            "`c = cLoc = 1617/2000 + (856993/10000) i` (`dh_zero_near_of_center'` with its three open inequalities",
            "discharged). -/",
            "theorem dh_zero_located : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cLoc‖ < 1 / 100 :=",
            "  dh_zero_near_of_center' H1 H2 H3", "",
            "/-- The located zero in coordinates: `0.7985 < Re ρ < 0.8185` (so `Re ρ > 1/2`: off the critical line)",
            "and `85.6893 < Im ρ < 85.7093`. -/",
            "theorem dh_zero_located_box : ∃ ρ : ℂ, dh ρ = 0 ∧ 1597 / 2000 < ρ.re ∧ ρ.re < 1637 / 2000 ∧",
            "    856893 / 10000 < ρ.im ∧ ρ.im < 857093 / 10000 := by",
            "  obtain ⟨ρ, h0, hρ⟩ := dh_zero_located",
            "  have hre := abs_lt.1 ((Complex.abs_re_le_norm (ρ - cLoc)).trans_lt hρ)",
            "  have him := abs_lt.1 ((Complex.abs_im_le_norm (ρ - cLoc)).trans_lt hρ)",
            "  rw [Complex.sub_re, cLoc_re] at hre",
            "  rw [Complex.sub_im, cLoc_im] at him",
            "  exact ⟨ρ, h0, by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩", ""]
    num += ['end PsiOmega.Locate', '',
            '#print axioms PsiOmega.Locate.PRe_20_mem', '#print axioms PsiOmega.Locate.PIm_20_mem', '#print axioms PsiOmega.Locate.ARe_20_mem',
            '#print axioms PsiOmega.Locate.H1', '#print axioms PsiOmega.Locate.H2', '#print axioms PsiOmega.Locate.H3',
            '#print axioms PsiOmega.Locate.dh_zero_located', '#print axioms PsiOmega.Locate.dh_zero_located_box']
else:
    num += ['end PsiOmega.Locate']
open(os.path.join(HERE, 'DHLocateNum' + SUFFIX + '.lean'), 'w').write('\n'.join(num) + '\n')
if RES:
    for k, v in RES.items():
        print(f"{k}: [{float(v[0]):.10e}, {float(v[1]):.10e}]  width {float(v[1]-v[0]):.3e}")

# ---------------------------------------------------------------- error budget report
if RES and os.environ.get('BUDGET', '') == '1':
    W = lambda b: float(b[1] - b[0])
    main = [n for n in NT if n < 100]
    print("atom widths (absolute, full interval):")
    print(f"  log n (rounded) max {max(W(LG[n]) for n in NT):.3e}")
    print(f"  ex    max {max(W(EXB[n]) for n in NT):.3e}  mean {sum(W(EXB[n]) for n in NT)/len(NT):.3e}")
    print(f"  cC    max {max(W(CB[n]) for n in NT):.3e}  mean {sum(W(CB[n]) for n in NT)/len(NT):.3e}")
    print(f"  sC    max {max(W(SB[n]) for n in NT):.3e}  mean {sum(W(SB[n]) for n in NT)/len(NT):.3e}")
    print(f"  kappa {float(KHI-KLO):.1e}")
    dl = [float(TRIGW[n][2]) for n in NT]
    print(f"  reduced-angle half-width delta max {max(dl):.3e} (theta from log: {max(float(TT*(LB[n][1]-LB[n][0])/2) for n in NT):.3e}; pi_d20 x M/4: {max(abs(TRIGW[n][0]) for n in NT)*1e-20/4:.1e})")
    print("product-term widths:")
    for nm in ('eC', 'eS', 'leC'):
        ws = [W(BND[f'{nm}_{n}']) for n in main]
        print(f"  {nm:4s} max {max(ws):.3e} sum {sum(ws):.3e}")
    for kind in 'PIA':
        bw = sum(W(BLK[(kind, m)]) for m in range(20)); tw = sum(W(TAIL[(kind, j)]) for j in (1, 2, 3, 4))
        print(f"  {kind}: m-sum blocks total width {bw:.3e}, Q-tails total width {tw:.3e}, enclosure width {W(RES[kind]):.3e}")
    true = {'P': mp.mpf('-3.2265086264189e-5'), 'I': mp.mpf('-5.4359577231286e-5'), 'A': mp.mpf('1.2323333731546')}
    for kind in 'PIA':
        lo, hi = RES[kind]
        print(f"  {kind}: [{float(lo):.10e}, {float(hi):.10e}] contains skeleton value {float(true[kind]):.10e}: {fm(lo) <= true[kind] <= fm(hi)}")
    print(f"  H1 slack used: {max(abs(float(RES['P'][0])), abs(float(RES['P'][1]))):.3e} of 1e-3;  H2: {max(abs(float(RES['I'][0])), abs(float(RES['I'][1]))):.3e} of 1e-3;  H3: lower end {float(RES['A'][0]):.7f} >= 1")
