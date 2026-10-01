# gen_locate_zero.py — the zero-location certificate of DHLocateSkeleton for a further zero of dh.
#
# usage: python3 gen_locate_zero.py TAG            (TAG ∈ CONFIG; writes DHLocate{TAG}{Base,Exp,Trig[,Trig2…],Num}.lean)
#        BUDGET=1 python3 gen_locate_zero.py TAG   (also prints the budget report)
#
# Given a rational centre c = σ + it (grid 1e-5), M, K = 12, the radius r and the Cauchy radius R, emits
#   DHLocate{TAG}Base.lean  the centre-specific lemmas of the skeleton, instantiated through DHLocateGen:
#                           the centre, the Euler–Maclaurin box constants (B, 5^{-σ₀}, (M + j/5)^{1-σ₀-24}) and
#                           the EM error on the ball; QsupR/Gsup on the box of closedBall c (r + R) and the
#                           Cauchy bound; the termwise D2sum; the exact Gaussian rationals (s)_n(c), (s)_n'(c),
#                           Q_{M+j/5}(c), Q'_{M+j/5}(c); the substituted forms of PReG/PImG/AReG; the ladder.
#   DHLocate{TAG}Exp.lean   two-sided bounds for ex σ n = exp(-σ log n), n ∈ NS
#   DHLocate{TAG}Trig.lean  two-sided bounds for cCG c n = cos(t log n), sCG c n = sin(t log n), n ∈ NS
#                           (split over DHLocate{TAG}Trig.lean, DHLocate{TAG}Trig2.lean, … when CONFIG sets tsplit)
#   DHLocate{TAG}Num.lean   interval products, block sums, Q-tails, H1–H3, dh_zero_located, the box,
#                           and the top-level PsiOmega.Locate.dh_zero_located_{TAG}, dh_zero_located_box_{TAG}
# Every number is an exact rational (fractions.Fraction); every rounding is outward; every budget inequality
# is asserted here before it is emitted (and re-checked by the kernel).
from fractions import Fraction as F
from math import factorial, floor, ceil
import math, re, sys, os
import mpmath as mp
mp.mp.dps = 60

HERE = os.path.dirname(os.path.abspath(__file__))
PILOT = '/home/user/r-infinite/tools/lean/riemann-pilot'
LOGSRCS = [os.path.join(PILOT, 'src', 'DHLogBounds.lean'), os.path.join(PILOT, 'src', 'DHLogBoundsExt.lean')]

# ------------------------------------------------------------------ configuration
# centres: the refined zeros (mpmath findroot on f = dh/a(1), 40 digits) rounded to the grid 1e-5
CONFIG = {
  '2': dict(sn=65083,  tn=11416334, r=F(1, 200), M=28, R=F(2, 5),  rho='0.65083008060973708 + 114.16334273075698 i'),
  '3': dict(sn=57436,  tn=16647931, r=F(1, 500), M=41, R=F(7, 20), rho='0.57435605045080599 + 166.47930591316816 i', tsplit=2, hbA=1000000),
  '4': dict(sn=72426,  tn=17670246, r=F(1, 150), M=41, R=F(7, 20), rho='0.72425769462680978 + 176.70246124285583 i', tsplit=2, hbA=1000000),
}
# tsplit: the trig bounds are written to tsplit files DHLocate{TAG}Trig.lean, DHLocate{TAG}Trig2.lean, ... (each a
# contiguous range of n, each importing the previous), so that no single file compiles for much over ~6 minutes.
# hbA: maxHeartbeats for the two enclosure theorems of Re fEM'(c) (AReG_ge, AReG_le): their final linarith over
# 2M + 8 block/tail bounds needs ~334000 heartbeats at M = 41 (measured with #count_heartbeats on zero 3).
TAG = sys.argv[1]
cfg = CONFIG[TAG]
G5 = 100000
SIG = F(cfg['sn'], G5); TT = F(cfg['tn'], G5)
SIG_T = f"{cfg['sn']} / {G5}"; TT_T = f"{cfg['tn']} / {G5}"
r = cfg['r']; M = cfg['M']; K = 12; R = cfg['R']
NS_ = f"PsiOmega.Locate.Z{TAG}"
D = 10**15
PI_LO = F(314159265358979323846, 10**20)
PI_HI = F(314159265358979323847, 10**20)
X0_GRID = 10**9
KLO, KHI = F(284079043840412, 10**15), F(284079043840413, 10**15)
KB = (KLO, KHI); KU = F(28408, 100000)
Bn = {2:F(1,6),4:F(-1,30),6:F(1,42),8:F(-1,30),10:F(5,66),12:F(-691,2730),14:F(7,6),16:F(-3617,510),
      18:F(43867,798),20:F(-174611,330),22:F(854513,138),24:F(-236364091,2730)}

def fm(x): return mp.mpf(x.numerator) / x.denominator
def rd_lo(x, d=D): return F(floor(x * d), d)
def rd_hi(x, d=D): return F(ceil(x * d), d)
def rat(x):
    x = F(x)
    return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def ratp(x):   # bare a / b (for places where a type ascription is not wanted)
    x = F(x)
    return f"{x.numerator} / {x.denominator}" if x.denominator != 1 else f"{x.numerator}"
def roundup(x, sig=6):
    x = F(x); assert x > 0
    e = int(mp.floor(mp.log10(fm(x))))
    scale = F(10)**(e - sig + 1)
    q = x / scale
    return (q.numerator // q.denominator + (1 if q.numerator % q.denominator else 0)) * scale
def rounddown(x, sig=6):
    x = F(x); assert x > 0
    e = int(mp.floor(mp.log10(fm(x))))
    scale = F(10)**(e - sig + 1)
    q = x / scale
    return (q.numerator // q.denominator) * scale
def mulb(a, b):
    c = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]; return min(c), max(c)
def rdb(b): return rd_lo(b[0]), rd_hi(b[1])
def addb(*bs): return sum(b[0] for b in bs), sum(b[1] for b in bs)
def negb(b): return -b[1], -b[0]
def scaleb(c, b): return (c*b[0], c*b[1]) if c >= 0 else (c*b[1], c*b[0])
U = {1: 1, 2: KHI, 3: KHI, 4: 1}     # |u(j)| upper bounds for budgets

# ------------------------------------------------------------------ log bounds (parsed from the lemma sources)
LB = {}
for path in LOGSRCS:
    src = open(path).read()
    for m in re.finditer(r"theorem log_bound_(\d+) : \((\d+) / (\d+) : ℝ\) ≤ Real\.log \d+ ∧ Real\.log \d+ ≤ \((\d+) / (\d+) : ℝ\)", src):
        n = int(m.group(1)); LB[n] = (F(int(m.group(2)), int(m.group(3))), F(int(m.group(4)), int(m.group(5))))
NMAXN = 5*M + 4
assert all(n in LB for n in range(2, NMAXN + 1)), "log bounds missing"
for n in range(2, NMAXN + 1):
    assert fm(LB[n][0]) <= mp.log(n) <= fm(LB[n][1])
LOGW = max(float(LB[n][1] - LB[n][0]) for n in range(2, NMAXN + 1))

NS = [5*m + j for m in range(M) for j in range(1, 5)] + [5*M + j for j in range(1, 5)]
NT = [n for n in NS if n != 1]

# ------------------------------------------------------------------ the true values (mpmath), for the budget
s5 = mp.sqrt(5)
kap = 2*mp.sin(mp.pi/5)/(s5 + 2*mp.sin(2*mp.pi/5))
uu = {0: 0, 1: 1, 2: kap, 3: -kap, 4: -1}
cc = mp.mpc(fm(SIG), fm(TT))
def f_true(s):
    return 5**(-s)*(mp.zeta(s, mp.mpf(1)/5) + kap*mp.zeta(s, mp.mpf(2)/5) - kap*mp.zeta(s, mp.mpf(3)/5) - mp.zeta(s, mp.mpf(4)/5))
def fd_true(s):
    t = (mp.zeta(s, mp.mpf(1)/5, 1) + kap*mp.zeta(s, mp.mpf(2)/5, 1) - kap*mp.zeta(s, mp.mpf(3)/5, 1) - mp.zeta(s, mp.mpf(4)/5, 1))
    return 5**(-s)*t - mp.log(5)*f_true(s)
F_C = f_true(cc); FD_C = fd_true(cc)

# ------------------------------------------------------------------ exact (s)_n, (s)_n', Q, Q' at c
P = [(F(1), F(0))]; PD = [(F(0), F(0))]
for n in range(2*K - 1):
    a, b = P[n]; da, db = PD[n]
    cr, ci = SIG + n, TT
    P.append((a*cr - b*ci, a*ci + b*cr))
    PD.append((da*cr - db*ci + a, da*ci + db*cr + b))
QV = {}
for j in range(1, 5):
    x = M + F(j, 5)
    a = SIG - 1; b = TT; nsq = a*a + b*b
    qr = x*a/nsq + F(1, 2); qi = -x*b/nsq
    dr = -x*(a*a - b*b)/nsq**2; di = x*2*a*b/nsq**2
    for k in range(K):
        co = Bn[2*k+2]/factorial(2*k+2)/x**(2*k+1)
        qr += co*P[2*k+1][0]; qi += co*P[2*k+1][1]
        dr += co*PD[2*k+1][0]; di += co*PD[2*k+1][1]
    QV[j] = (qr, qi, dr, di)
# the approximant at c, exactly in the Q-part and by mpmath in the Dirichlet part: a check of the formulas
def fEM_mp():
    s = cc; tot = 0; totd = 0
    for n in range(1, 5*M):
        tot += uu[n % 5] * mp.power(n, -s); totd += -mp.log(n) * uu[n % 5] * mp.power(n, -s)
    for j in range(1, 5):
        N = 5*M + j; Q = mp.mpc(fm(QV[j][0]), fm(QV[j][1])); Qd = mp.mpc(fm(QV[j][2]), fm(QV[j][3]))
        tot += uu[j] * mp.power(N, -s) * Q; totd += uu[j] * mp.power(N, -s) * (Qd - mp.log(N) * Q)
    return tot, totd
FEM_C, FEMD_C = fEM_mp()

# ------------------------------------------------------------------ the Euler–Maclaurin box constants
s0 = SIG - r; s1 = SIG + r; tau = TT + r
prod = F(1)
for i in range(2*K): prod *= (s1 + i)**2 + tau**2
B = roundup(F(int(mp.ceil(mp.sqrt(fm(prod))))), 3)
assert B*B >= prod
# 5^{-s0} <= y5 via exponent p/q <= s0
q5 = 200; p5 = floor(s0 * q5); assert F(p5, q5) <= s0
y5 = roundup(F(str(mp.nstr(mp.power(5, -mp.mpf(p5)/q5), 30))), 5)
assert F(5)**p5 * y5**q5 >= 1
# (M + j/5)^{-(23 + s0)} <= y_j via 23 + p/q, q = 100
qx = 100; px = floor(s0 * qx); assert F(px, qx) <= s0
EX = 2*K - 1 + s0     # 23 + s0 (the exponent 1 - s0 - 24 = -EX)
yx = {}; Yx = {}
for j in range(1, 5):
    xj = M + F(j, 5)
    v = mp.power(fm(xj), -(mp.mpf(2*K - 1) + mp.mpf(px)/qx))
    yj = roundup(F(str(mp.nstr(v, 30))), 5)
    Yj = yj * xj**(2*K - 1)
    assert xj**px * Yj**qx >= 1
    yx[j] = yj; Yx[j] = Yj
CPI = F(1) / (3 * 2**24 * F(3141592, 1000000)**22)
e0_exact = y5 * (CPI * B / (s0 + 2*K - 1) * (yx[1] + KU*yx[2] + KU*yx[3] + yx[4]))
e0 = roundup(e0_exact, 3)

# ------------------------------------------------------------------ G sup on the box of closedBall c (r + R)
rR = r + R
g0 = SIG - rR; g1 = SIG + rR; gt = TT + rR; gt0 = TT - rR
assert g0 > 0
def QsupR(x):
    tot = x/gt0 + F(1, 2)
    for k in range(K):
        n = 2*k+1
        S = F(1)
        for i in range(n): S *= gt + (g1 + i)**2/(2*gt)
        tot += abs(Bn[2*k+2])/factorial(2*k+2) * S / x**n
    return tot
qg = {}
for j in range(1, 5): qg[j] = roundup(QsupR(M + F(j, 5)), 4)
qe = 200; pe = floor(g0 * qe); assert F(pe, qe) <= g0
ye = {}
for j in range(1, 5):
    N = 5*M + j
    yj = roundup(F(str(mp.nstr(mp.power(N, -mp.mpf(pe)/qe), 30))), 5)
    assert F(N)**pe * yj**qe >= 1
    ye[j] = yj
Gc = roundup(ye[1]*qg[1] + KU*(ye[2]*qg[2]) + KU*(ye[3]*qg[3]) + ye[4]*qg[4], 4)

# ------------------------------------------------------------------ D2sum(σd, M), σd = σ − r
sd = s0
qd = 200; pd = floor(sd * qd); assert F(pd, qd) <= sd
D2 = {}
d2tot = F(0)
for n in range(2, 5*M):
    if n % 5 == 0: continue
    hi = rd_hi(LB[n][1], 10**12)
    y = roundup(F(str(mp.nstr(mp.power(n, -mp.mpf(pd)/qd), 30))), 6)
    assert F(n)**pd * y**qd >= 1
    c = roundup(hi**2 * y, 6)
    D2[n] = (hi, y, c)
    d2tot += (1 if n % 5 in (1, 4) else KU) * c
d2 = roundup(d2tot, 4)
m2 = d2 + 2*Gc/R**2

# ------------------------------------------------------------------ the margin and the tolerances
ARE = mp.re(FEMD_C)
assert ARE > 0
arlo = rounddown(F(str(mp.nstr(ARE, 20))) - F(1, 100), 2)
slack = arlo*r - m2*r**2 - 2*e0
assert slack > 0, ("margin fails", float(slack))
tol = rounddown(slack / 5, 1)      # |PReG|, |PImG| ≤ tol each: 2(2 tol + e0) ≤ arlo r − m2 r² − slack/5
assert 2*(tol + tol + e0) < arlo*r - m2*r**2
assert abs(mp.re(FEM_C)) < fm(tol) / 4 and abs(mp.im(FEM_C)) < fm(tol) / 4

if os.environ.get('BUDGET', '') == '1' or True:
    print(f"=== zero {TAG}: rho = {cfg['rho']}")
    print(f"  c = {SIG_T} + ({TT_T}) i = {float(SIG):.5f} + {float(TT):.5f} i;  M = {M}, K = {K}, r = {ratp(r)}, R = {ratp(R)}")
    print(f"  f(c) = {mp.nstr(F_C, 6)}  (fEM(c) = {mp.nstr(FEM_C, 6)});  f'(c) = {mp.nstr(FD_C, 8)}  (fEM'(c) = {mp.nstr(FEMD_C, 8)})")
    print(f"  EM box: s0 = {ratp(s0)}, s1 = {ratp(s1)}, tau = {ratp(tau)}; B = {float(B):.3e} (sqrt prod = {float(mp.sqrt(fm(prod))):.4e});"
          f" 5^-s0 <= {float(y5):.5f}; x_j^-(23+s0) <= {[f'{float(yx[j]):.4e}' for j in range(1,5)]}")
    print(f"  e0 (per unit a(1)) <= {float(e0):.3e}  (exact rational {float(e0_exact):.4e})")
    print(f"  G box: s0' = {ratp(g0)}, s1' = {ratp(g1)}, tau' = {ratp(gt)}, tau0' = {ratp(gt0)};  QsupR <= {[float(qg[j]) for j in range(1,5)]};"
          f" N^-s0' <= {[float(ye[j]) for j in range(1,5)]};  Gsup <= C = {float(Gc)};  2C/R^2 = {float(2*Gc/R**2):.4f}")
    true_d2 = sum(abs(uu[n % 5]) * mp.log(n)**2 * mp.power(n, -fm(sd)) for n in range(2, 5*M))
    print(f"  D2sum({ratp(sd)}, {M}) <= d2 = {float(d2)}  (true {mp.nstr(true_d2, 6)}; exponent {pd}/{qd})")
    print(f"  m2 = d2 + 2C/R^2 = {float(m2):.4f};  ar = {float(arlo)} (Re fEM'(c) = {mp.nstr(ARE, 8)})")
    print(f"  margin: ar r - m2 r^2 = {float(arlo*r - m2*r**2):.4e};  2 e0 = {float(2*e0):.2e};  slack = {float(slack):.4e};"
          f"  tolerance |PRe|, |PIm| <= {float(tol):.1e} (true |Re fEM(c)| = {mp.nstr(abs(mp.re(FEM_C)), 3)}, |Im| = {mp.nstr(abs(mp.im(FEM_C)), 3)})")

# ------------------------------------------------------------------ Lean text helpers
EXS = f"ex ({SIG_T})"            # the atom ex σ n
def exn(n): return f"{EXS} {n}"
def cCn(n): return f"cCG cZ {n}"
def sCn(n): return f"sCG cZ {n}"
TH = lambda n: f"{TT_T} * Real.log {n}"
X = lambda j: f"{M} + {j} / 5"     # the x of Q_x as it appears after Nat.cast_ofNat
HDR = ['open Complex Metric', 'open scoped Nat', '', 'noncomputable section', '', f'namespace {NS_}', '']

# ================================================================== Base file
base = ['import DHLocateGen', 'import DHLogBoundsExt', '',
  f'/-!',
  f'# A zero of `dh` within `{ratp(r)}` of `c = {SIG_T} + ({TT_T}) i`: the certificate instance (generated)',
  '',
  f'Generated by `gen_locate_zero.py {TAG}`: the centre-specific lemmas of `DHLocateSkeleton`, instantiated through',
  f'the centre-parametric layer `DHLocateGen`, for the zero `ρ ≈ {cfg["rho"]}`.',
  f'Approximant `dhEM {M} 12 = a(1)·fEM {M} 12`; radius `r = {ratp(r)}`; Cauchy radius `R = {ratp(R)}`.',
  '',
  f'* Euler–Maclaurin error on `closedBall cZ r`: `‖dh − dhEM‖ ≤ ‖a(1)‖·{float(e0):.3e}` (box',
  f'  `{ratp(s0)} ≤ Re ≤ {ratp(s1)}`, `|Im| ≤ {ratp(tau)}`, `B = {B}`).',
  f'* `‖DEM″ + GEM″‖ ≤ m₂ = {ratp(m2)} ≈ {float(m2):.3f}` on the ball: `D2sum({ratp(sd)}, {M}) ≤ {ratp(d2)}` termwise',
  f'  and `‖GEM‖ ≤ {ratp(Gc)}` on the box of `closedBall cZ ({ratp(rR)})` (Cauchy, `2C/R² = {float(2*Gc/R**2):.4f}`).',
  f'* Exact `(s)_n(c)`, `(s)′_n(c)` (`n ≤ 23`) and `Q_{{{M}+j/5}}(c)`, `Q′_{{{M}+j/5}}(c)`.',
  f"* The ladder `dh_zero_near_of_center'`: `|PReG cZ {M} 12| ≤ {ratp(tol)}`, `|PImG cZ {M} 12| ≤ {ratp(tol)}`,",
  f'  `{ratp(arlo)} ≤ AReG cZ {M} 12` give the zero (margin `2(2·{float(tol):.1e} + {float(e0):.2e}) <'
  f' {float(arlo)}·r − m₂ r² = {float(arlo*r - m2*r**2):.4e}`).',
  '-/', ''] + HDR
base += [f'/-- The centre `c = {SIG_T} + ({TT_T}) i`. -/',
  f'def cZ : ℂ := {SIG_T} + {TT_T} * I', '',
  f'theorem cZ_re : cZ.re = {SIG_T} := by simp [cZ]', '',
  f'theorem cZ_im : cZ.im = {TT_T} := by simp [cZ]', '']
# --- EM box constants
base += ['/-! ## 1. The Euler–Maclaurin error on the ball -/', '',
  f'theorem five_rpow_le : (5 : ℝ) ^ (-({ratp(s0)} : ℝ)) ≤ {rat(y5)} := by',
  f'  calc (5 : ℝ) ^ (-({ratp(s0)} : ℝ)) ≤ (5 : ℝ) ^ (-(({p5} : ℕ) : ℝ) / (({q5} : ℕ) : ℝ)) :=',
  '        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)',
  f'    _ = (5 : ℝ) ^ (-((({p5} : ℕ) : ℝ) / (({q5} : ℕ) : ℝ))) := by rw [neg_div]',
  f'    _ ≤ {rat(y5)} := rpow_neg_div_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)', '']
for j in range(1, 5):
    xj = M + F(j, 5)
    base += [f'theorem x{j}_rpow_le : ({ratp(xj)} : ℝ) ^ (-({ratp(EX)} : ℝ)) ≤ {rat(yx[j])} := by',
      f'  calc ({ratp(xj)} : ℝ) ^ (-({ratp(EX)} : ℝ))',
      f'        ≤ ({ratp(xj)} : ℝ) ^ (-(((23 : ℕ) : ℝ) + (({px} : ℕ) : ℝ) / (({qx} : ℕ) : ℝ))) :=',
      '        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)',
      f'    _ ≤ (({ratp(xj)} : ℝ) ^ 23)⁻¹ * ({rat(yx[j])} * ({ratp(xj)} : ℝ) ^ 23) :=',
      f'        rpow_neg_add_div_le (by norm_num) (by norm_num) 23 (by norm_num) (by norm_num)',
      '    _ = _ := by field_simp', '',
      f'theorem hy{j} : ((({M} : ℕ) : ℝ) + {j} / 5) ^ (1 - ({ratp(s0)} : ℝ) - 2 * 12) ≤ {rat(yx[j])} := by',
      f'  have e1 : (({M} : ℕ) : ℝ) + {j} / 5 = {ratp(xj)} := by norm_num',
      f'  have e2 : (1 - ({ratp(s0)} : ℝ) - 2 * 12) = -({ratp(EX)} : ℝ) := by norm_num',
      f'  rw [e1, e2]', f'  exact x{j}_rpow_le', '']
base += [f'theorem prod_box_le : ∏ i ∈ Finset.range (2 * 12), ((({ratp(s1)} : ℝ) + i) ^ 2 + ({ratp(tau)} : ℝ) ^ 2)',
  f'    ≤ ({rat(B)}) ^ 2 := by',
  '  simp only [Finset.prod_range_succ, Finset.prod_range_zero]; norm_num', '',
  f'/-- **The Euler–Maclaurin error on the ball**, normalised: `‖dh z − dhEM {M} 12 z‖ ≤ ‖a(1)‖·{ratp(e0)}`. -/',
  f'theorem norm_dh_sub_dhEM_le_ball {{z : ℂ}} (hz : z ∈ closedBall cZ {rat(r)}) :',
  f'    ‖dh z - dhEM {M} 12 z‖ ≤ ‖aDH chi5 1‖ * {rat(e0)} :=',
  f'  norm_dh_sub_dhEM_le_ballG (c := cZ) (r := {rat(r)}) (σ₀ := {rat(s0)}) (σ₁ := {rat(s1)}) (τ := {rat(tau)})',
  f'    (B := {rat(B)}) (M := {M}) (by norm_num) (by norm_num) (by norm_num) (by rw [cZ_re]; norm_num)',
  f'    (by rw [cZ_re]; norm_num) (by rw [cZ_im]; norm_num) (by rw [cZ_im]; norm_num) prod_box_le five_rpow_le',
  '    hy1 hy2 hy3 hy4 (by norm_num) hz', '']
# --- G sup and Cauchy
QBARGS = f"({rat(g1)}) ({rat(gt)}) ({rat(gt0)})"
base += [f'/-! ## 2. `G″` on the ball: Cauchy on circles of radius `{ratp(R)}`, `‖GEM‖ ≤ {ratp(Gc)}` on the box of `closedBall cZ ({ratp(rR)})` -/', '',
  'theorem QsupR_ball_le :']
for j in range(1, 5):
    base += [f'    QsupR 12 ({X(j)}) {QBARGS} ≤ {rat(qg[j])}' + (' ∧' if j < 4 else ' := by')]
base += ['  refine ⟨?_, ?_, ?_, ?_⟩ <;>',
  '  · simp only [QsupR, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,',
  '      Finset.prod_range_zero, Nat.reduceMul, Nat.reduceAdd, bernoulli_2_eq, bernoulli_4_eq,',
  '      bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq,',
  '      bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq]',
  '    norm_num [Nat.factorial]', '',
  f'theorem Gsup_ball_le : Gsup {M} 12 ({rat(g0)}) {QBARGS} ≤ {rat(Gc)} := by',
  '  obtain ⟨q1, q2, q3, q4⟩ := QsupR_ball_le']
for j in range(1, 5):
    base += [f'  have r{j} := QsupB_le_QsupR 12 (x := {X(j)}) (σ₁ := {rat(g1)}) (τ := {rat(gt)})',
             f'    (τ₀ := {rat(gt0)}) (by norm_num) (by norm_num)']
for j in range(1, 5):
    base += [f'  have e{j} : ex ({rat(g0)}) {5*M+j} ≤ {rat(ye[j])} :=',
             f'    ex_le_of (p := {pe}) (q := {qe}) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)']
base += ['  have hk := kappa_le', '  have hk0 := kappa_pos.le',
  f'  have hq0 : ∀ j : ℕ, 0 ≤ QsupB 12 ({M} + j / 5) {QBARGS} := by',
  '    intro j', '    unfold QsupB', '    positivity',
  '  have p1 := hq0 1', '  have p2 := hq0 2', '  have p3 := hq0 3', '  have p4 := hq0 4']
for j in range(1, 5):
    base += [f'  have x{j} : 0 ≤ ex ({rat(g0)}) {5*M+j} := (Real.exp_pos _).le']
base += ['  unfold Gsup', '  push_cast at p1 p2 p3 p4 ⊢',
  f'  refine le_trans ?_ (show ({rat(ye[1])} * {rat(qg[1])} + 28408 / 100000 * ({rat(ye[2])} * {rat(qg[2])}) +',
  f'      28408 / 100000 * ({rat(ye[3])} * {rat(qg[3])}) + {rat(ye[4])} * {rat(qg[4])} : ℝ) ≤ {rat(Gc)}',
  '      by norm_num)', '  gcongr',
  '  · exact r1.trans q1', '  · exact r2.trans q2', '  · exact r3.trans q3', '  · exact r4.trans q4', '']
# --- D2 terms
base += [f'/-! ## 3. The termwise sum `D2sum({ratp(sd)}, {M}) ≤ {ratp(d2)}`', '',
  f'Per term `log² n · n^{{-σd}} ≤ (log n)_hi² · y_n`, `(log n)_hi` from `log_bound_n` (`DHLogBounds`, `DHLogBoundsExt`),',
  f'`n^{{-σd}} ≤ n^{{-{pd}/{qd}}} ≤ y_n` (`ex_le_of`). -/', '']
for n in sorted(D2):
    hi, y, c = D2[n]
    base += [f'theorem D2t_{n} : Real.log {n} ^ 2 * ex ({ratp(sd)}) {n} ≤ {rat(c)} := by',
      f'  have hl : Real.log (({n} : ℕ) : ℝ) ≤ {rat(hi)} := by',
      f'    have h := (PsiOmega.Num.log_bound_{n}).2', '    push_cast', '    linarith',
      f'  have h := D2term_leG (n := {n}) (σ := {rat(sd)}) (hi := {rat(hi)}) (y := {rat(y)}) (c := {rat(c)}) (by norm_num) hl',
      f'    (ex_le_of (p := {pd}) (q := {qd}) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))',
      '    (by norm_num)', '  exact_mod_cast h', '']
hyps = []
for n in sorted(D2):
    if n % 5 in (1, 4): hyps.append(f"D2t_{n}")
    else: hyps.append(f"mul_le_mul hk D2t_{n} (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by norm_num)")
base += ['set_option maxRecDepth 20000 in', f'/-- **`D2sum({ratp(sd)}, {M}) ≤ {ratp(d2)}`**. -/',
  f'theorem D2sum_le : D2sum ({ratp(sd)}) {M} ≤ {rat(d2)} := by',
  '  have hk := kappa_le', '  unfold D2sum',
  '  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat,',
  '    Nat.cast_one, Real.log_one]', '  norm_num only',
  '  linarith [' + ',\n    '.join(hyps) + ']', '',
  f'/-- **The second-derivative bound on the ball**: `‖DEM″ + GEM″‖ ≤ {ratp(m2)}` on `closedBall cZ {ratp(r)}`. -/',
  f'theorem m2_ball {{z : ℂ}} (hz : z ∈ closedBall cZ {rat(r)}) :',
  f'    ‖DEMk 2 {M} z + deriv (deriv (GEM {M} 12)) z‖ ≤ {rat(m2)} := by',
  f'  have h := norm_deriv2_fEM_ballG {M} 12 (c := cZ) (r := {rat(r)}) (R := {rat(R)}) (σd := {rat(sd)})',
  f'    (σ₀ := {rat(g0)}) (σ₁ := {rat(g1)}) (τ := {rat(gt)}) (τ₀ := {rat(gt0)}) (C := {rat(Gc)}) (d₂ := {rat(d2)})',
  '    (by rw [cZ_re]; norm_num) D2sum_le (by norm_num) (by norm_num) (by norm_num) (by rw [cZ_re]; norm_num)',
  '    (by rw [cZ_re]; norm_num) (by rw [cZ_im]; norm_num) (by rw [cZ_im]; norm_num) Gsup_ball_le hz',
  '  refine h.trans (le_of_eq ?_)', '  norm_num', '']
# --- poch values
base += [f'/-! ## 4. Exact Gaussian-rational values of `(s)_n`, `(s)′_n`, `Q_x`, `Q′_x` at `c`, `x = {M} + j/5` -/', '',
  'theorem poch_c_0 : (HurwitzEM.poch cZ 0).re = (1 : ℝ) ∧ (HurwitzEM.poch cZ 0).im = (0 : ℝ) := by',
  '  simp [HurwitzEM.poch]', '',
  'theorem pochD_c_0 : (pochD cZ 0).re = (0 : ℝ) ∧ (pochD cZ 0).im = (0 : ℝ) := by',
  '  simp [pochD]', '']
for n in range(1, 2*K):
    a, b = P[n]
    base += [f'theorem poch_c_{n} : (HurwitzEM.poch cZ {n}).re = {rat(a)} ∧',
      f'    (HurwitzEM.poch cZ {n}).im = {rat(b)} := by',
      f'  obtain ⟨h1, h2⟩ := poch_c_{n-1}',
      '  rw [HurwitzEM.poch_succ, Complex.mul_re, Complex.mul_im, h1, h2]',
      '  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cZ_re, cZ_im]',
      '  norm_num', '']
for n in range(1, 2*K):
    a, b = PD[n]
    base += [f'theorem pochD_c_{n} : (pochD cZ {n}).re = {rat(a)} ∧',
      f'    (pochD cZ {n}).im = {rat(b)} := by',
      f'  obtain ⟨h1, h2⟩ := pochD_c_{n-1}', f'  obtain ⟨g1, g2⟩ := poch_c_{n-1}',
      '  rw [pochD, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, h1, h2, g1, g2]',
      '  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, cZ_re, cZ_im]',
      '  norm_num', '']
BERN = ('bernoulli_2_eq, bernoulli_4_eq, bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, '
        'bernoulli_14_eq, bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq')
PRW = ', '.join(f'(poch_c_{2*k+1}).1, (poch_c_{2*k+1}).2' for k in range(K))
PDRW = ', '.join(f'(pochD_c_{2*k+1}).1, (pochD_c_{2*k+1}).2' for k in range(K))
for j in range(1, 5):
    qr, qi, dr, di = QV[j]
    base += [f'theorem QEM_c_{j} : (QEM 12 ({X(j)}) cZ).re = {rat(qr)} ∧',
      f'    (QEM 12 ({X(j)}) cZ).im = {rat(qi)} := by',
      '  rw [QEM_eq_real]',
      '  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,',
      '    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]',
      f'  rw [{PRW}]',
      f'  simp only [{BERN}, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,',
      '    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, cZ_re, cZ_im]',
      '  norm_num [Nat.factorial]', '',
      f'theorem QEMd_c_{j} : (QEMd 12 ({X(j)}) cZ).re = {rat(dr)} ∧',
      f'    (QEMd 12 ({X(j)}) cZ).im = {rat(di)} := by',
      '  rw [QEMd_eq_real]',
      '  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,',
      '    Complex.im_ofReal_mul, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]',
      f'  rw [{PDRW}]',
      f'  simp only [{BERN}, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,',
      '    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.neg_re,',
      '    Complex.neg_im, pow_two, Complex.mul_re, Complex.mul_im, cZ_re, cZ_im]',
      '  norm_num [Nat.factorial]', '']
# --- substituted forms
QT = {}
for j in range(1, 5):
    qr, qi, dr, di = QV[j]
    QT[('Q', j, 're')] = (rat(qr), qr); QT[('Q', j, 'im')] = (rat(qi), qi)
    QT[('Qd', j, 're')] = (rat(dr), dr); QT[('Qd', j, 'im')] = (rat(di), di)
def sumpart(kind):
    at = 'sCG' if kind == 'I' else 'cCG'
    if kind in ('P', 'I'):
        body = (f"({EXS} (5 * m + 1) * {at} cZ (5 * m + 1)\n      + kappa * ({EXS} (5 * m + 2) * {at} cZ (5 * m + 2))\n"
                f"      - kappa * ({EXS} (5 * m + 3) * {at} cZ (5 * m + 3))\n      - {EXS} (5 * m + 4) * {at} cZ (5 * m + 4))")
    else:
        body = (f"(Real.log (5 * m + 1 : ℕ) * ({EXS} (5 * m + 1) * {at} cZ (5 * m + 1))\n"
                f"      + kappa * (Real.log (5 * m + 2 : ℕ) * ({EXS} (5 * m + 2) * {at} cZ (5 * m + 2)))\n"
                f"      - kappa * (Real.log (5 * m + 3 : ℕ) * ({EXS} (5 * m + 3) * {at} cZ (5 * m + 3)))\n"
                f"      - Real.log (5 * m + 4 : ℕ) * ({EXS} (5 * m + 4) * {at} cZ (5 * m + 4)))")
    s = f"∑ m ∈ Finset.range {M}, {body}"
    return f"({s})" if kind == 'P' else f"-({s})"
def tail_inner(kind, j):
    N = 5*M + j
    Qr, Qi = QT[('Q', j, 're')][0], QT[('Q', j, 'im')][0]
    if kind == 'P': return f"cCG cZ {N} * {Qr} + sCG cZ {N} * {Qi}"
    if kind == 'I': return f"cCG cZ {N} * {Qi} - sCG cZ {N} * {Qr}"
    Dr, Di = QT[('Qd', j, 're')][0], QT[('Qd', j, 'im')][0]
    return f"cCG cZ {N} * ({Dr} - Real.log {N} * {Qr}) + sCG cZ {N} * ({Di} - Real.log {N} * {Qi})"
def tailpart(kind):
    t = [f"{exn(5*M+j)} * ({tail_inner(kind, j)})" for j in range(1, 5)]
    return f"({t[0]}\n      + kappa * ({t[1]})\n      - kappa * ({t[2]})\n      - {t[3]})"
QRW = ', '.join(f'(QEM_c_{j}).1, (QEM_c_{j}).2' for j in range(1, 5))
QDRW = ', '.join(f'(QEMd_c_{j}).1, (QEMd_c_{j}).2' for j in range(1, 5))
base += [f'/-! ## 5. The three point values with every constant substituted -/', '']
for kind, q, nm in (('P', 'PReG', 'PRe_Z'), ('I', 'PImG', 'PIm_Z'), ('A', 'AReG', 'ARe_Z')):
    base += [f'theorem {nm} : {q} cZ {M} 12 = {sumpart(kind)} +', f'    {tailpart(kind)} := by']
    if kind == 'A':
        base += [f'  simp only [{q}, cZ_re, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, QDG_re, QDG_im]',
                 f'  rw [{QRW}, {QDRW}]', '']
    else:
        base += [f'  simp only [{q}, cZ_re, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat]', f'  rw [{QRW}]', '']
# --- ladder
base += ['/-! ## 6. The ladder -/', '',
  f'/-- **The certificate at `cZ`, ball-uniform inputs discharged**: three point values remain. -/',
  'theorem dh_zero_near_of_center {pr pi ar : ℝ}',
  f'    (hPr : |PReG cZ {M} 12| ≤ pr) (hPi : |PImG cZ {M} 12| ≤ pi) (hAr : ar ≤ |AReG cZ {M} 12|)',
  f'    (hmargin : 2 * (pr + pi + {rat(e0)}) < ar * {rat(r)} - {rat(m2)} * {rat(r)} ^ 2) :',
  f'    ∃ ρ, dh ρ = 0 ∧ ‖ρ - cZ‖ < {rat(r)} :=',
  '  dh_zero_near_of_elementaryG (by norm_num) (by rw [cZ_im]; norm_num) hPr hPi hAr',
  '    (fun _ hz => m2_ball hz) (fun _ hz => norm_dh_sub_dhEM_le_ball hz) hmargin', '',
  f'/-- **The open inputs with fixed tolerances**: `|Re fEM(c)| ≤ {ratp(tol)}`, `|Im fEM(c)| ≤ {ratp(tol)}`,',
  f'`Re fEM′(c) ≥ {ratp(arlo)}` (true values `{mp.nstr(mp.re(FEM_C), 4)}`, `{mp.nstr(mp.im(FEM_C), 4)}`, `{mp.nstr(ARE, 6)}`). -/',
  f"theorem dh_zero_near_of_center' (hPr : |PReG cZ {M} 12| ≤ {rat(tol)}) (hPi : |PImG cZ {M} 12| ≤ {rat(tol)})",
  f'    (hAr : {rat(arlo)} ≤ AReG cZ {M} 12) : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cZ‖ < {rat(r)} :=',
  '  dh_zero_near_of_center hPr hPi (hAr.trans (le_abs_self _)) (by norm_num)', '',
  f'end {NS_}', '']
for nm in ['norm_dh_sub_dhEM_le_ball', 'Gsup_ball_le', 'D2sum_le', 'm2_ball', 'QEM_c_1', 'QEMd_c_4', 'PRe_Z', 'PIm_Z',
           'ARe_Z', 'dh_zero_near_of_center', "dh_zero_near_of_center'"]:
    base.append(f'#print axioms {NS_}.{nm}')

# ================================================================== Exp file (as gen_locate.py)
EXPC = F(13, factorial(12) * 12)
def P12(x): return sum(F((-1)**i) * x**i / factorial(i) for i in range(12))
EXB = {}; EXDATA = {}
for n in NT:
    ylo, yhi = rd_lo(SIG * LB[n][0]), rd_hi(SIG * LB[n][1])
    assert 0 <= ylo and yhi <= 8
    r1 = yhi / 8; A = P12(r1) - r1**12 * EXPC; a = rd_lo(A, 10**20); assert a > 0
    elo = rd_lo(a**8)
    r2 = ylo / 8; Bq = P12(r2) + r2**12 * EXPC; b = rd_hi(Bq, 10**20)
    ehi = rd_hi(b**8)
    tv = mp.exp(-fm(SIG) * mp.log(n))
    assert fm(elo) <= tv <= fm(ehi), n
    EXB[n] = (elo, ehi); EXDATA[n] = (ylo, yhi, a, b)
expf = [f'import DHLocate{TAG}Base', '',
  f'/-! # Generated (`gen_locate_zero.py {TAG}`): two-sided bounds for `ex σ n = exp(-σ log n)`, `σ = {SIG_T}`, `n ∈ NS`', '',
  '`log n` from `PsiOmega.Num.log_bound_n`; `exp(-y) = exp(-(y/8))^8` with `exp(-(y/8))` from `Real.exp_bound`',
  '(`exp_neg_ge_of`, `exp_neg_le_of`, `DHLocateExp`). -/', '', 'open Real Finset', '', f'namespace {NS_}', '']
for n in NT:
    elo, ehi = EXB[n]; ylo, yhi, a, b = EXDATA[n]
    expf += [f"theorem exB_{n} : {rat(elo)} ≤ {exn(n)} ∧ {exn(n)} ≤ {rat(ehi)} := by",
      f"  have hl := PsiOmega.Num.log_bound_{n}",
      f"  have hlo := exp_neg_ge_of (q := {rat(yhi)}) (a := {rat(a)}) (lo := {rat(elo)}) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)",
      f"  have hhi := exp_neg_le_of (q := {rat(ylo)}) (b := {rat(b)}) (hi := {rat(ehi)}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)",
      "  unfold ex", "  simp only [Nat.cast_ofNat]", "  constructor",
      "  · exact le_trans hlo (Real.exp_le_exp.2 (by linarith [hl.1, hl.2]))",
      "  · exact le_trans (Real.exp_le_exp.2 (by linarith [hl.1, hl.2])) hhi", ""]
expf += [f'end {NS_}', '', f'#print axioms {NS_}.exB_{NT[-1]}']

# ================================================================== Trig file (as gen_locate.py)
def cos_poly(x, N): return sum(F((-1)**i) * x**(2*i) / factorial(2*i) for i in range(N))
def sin_poly(x, N): return sum(F((-1)**i) * x**(2*i+1) / factorial(2*i+1) for i in range(N))
def center_bounds(x0):
    cl, cu = cos_poly(x0, 6), cos_poly(x0, 7)
    if x0 >= 0: sl, su = sin_poly(x0, 6), sin_poly(x0, 7)
    else: sl, su = -sin_poly(-x0, 7), -sin_poly(-x0, 6)
    return cl, cu, sl, su
CB = {}; SB = {}; TRIGW = {}
trig_by_n = {}
def emit_trig(name, theta_expr, thlo, thhi, hl_lines):
    thmid = (thlo + thhi) / 2
    pimid = (PI_LO + PI_HI) / 2
    Mq = round(thmid / (pimid / 2))
    q, s = divmod(Mq, 4)
    xexact = thmid - Mq * pimid / 2
    x0 = F(round(xexact * X0_GRID), X0_GRID)
    delta = (thhi - thlo) / 2 + abs(Mq) * (PI_HI - PI_LO) / 4 + abs(xexact - x0)
    x0s = rat(x0) if x0 >= 0 else f"(-{rat(-x0)})"
    assert abs(x0) + delta <= 1, (name, x0, delta)
    cl, cu, sl, su = center_bounds(x0)
    crl, cru, srl, sru = cl - delta, cu + delta, sl - delta, su + delta
    crl, cru, srl, sru = rd_lo(crl), rd_hi(cru), rd_lo(srl), rd_hi(sru)
    if s == 0:   CL, CU, SL, SU = crl, cru, srl, sru
    elif s == 1: CL, CU, SL, SU = -sru, -srl, crl, cru
    elif s == 2: CL, CU, SL, SU = -cru, -crl, -sru, -srl
    else:        CL, CU, SL, SU = srl, sru, -cru, -crl
    red = f"PsiOmega.Num.redAngle ({theta_expr}) {Mq}"
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
    return out, (CL, CU), (SL, SU), (Mq, x0, delta)
for n in NT:
    thlo, thhi = rd_lo(TT * LB[n][0]), rd_hi(TT * LB[n][1])
    th = TH(n)
    out, cb, sb, info = emit_trig(f"thL_{n}", th, thlo, thhi,
        [f"  have hl0 := PsiOmega.Num.log_bound_{n}",
         f"  have hl : {rat(thlo)} ≤ {th} ∧ {th} ≤ {rat(thhi)} := by",
         "    constructor <;> linarith [hl0.1, hl0.2]"])
    tc = mp.cos(fm(TT) * mp.log(n)); ts = mp.sin(fm(TT) * mp.log(n))
    assert fm(cb[0]) <= tc <= fm(cb[1]) and fm(sb[0]) <= ts <= fm(sb[1]), n
    out += [f"theorem cCB_{n} : {rat(cb[0])} ≤ {cCn(n)} ∧ {cCn(n)} ≤ {rat(cb[1])} := by",
            "  unfold cCG", "  rw [cZ_im]", "  simp only [Nat.cast_ofNat]", f"  exact thL_{n}_cos", "",
            f"theorem sCB_{n} : {rat(sb[0])} ≤ {sCn(n)} ∧ {sCn(n)} ≤ {rat(sb[1])} := by",
            "  unfold sCG", "  rw [cZ_im]", "  simp only [Nat.cast_ofNat]", f"  exact thL_{n}_sin", ""]
    trig_by_n[n] = out
    CB[n] = cb; SB[n] = sb; TRIGW[n] = info
TSPLIT = cfg.get('tsplit', 1)
TNAMES = [f'DHLocate{TAG}Trig' + ('' if k == 0 else str(k + 1)) for k in range(TSPLIT)]
TCHUNKS = [NT[k * len(NT) // TSPLIT:(k + 1) * len(NT) // TSPLIT] for k in range(TSPLIT)]
trigfs = []
for k in range(TSPLIT):
    part = '' if TSPLIT == 1 else f' (part {k + 1} of {TSPLIT}: `{TCHUNKS[k][0]} ≤ n ≤ {TCHUNKS[k][-1]}`)'
    trigfs.append([f'import DHLocate{TAG}Exp' if k == 0 else f'import {TNAMES[k - 1]}', '',
      f'/-! # Generated (`gen_locate_zero.py {TAG}`): bounds for `cCG cZ n = cos(t log n)`, `sCG cZ n = sin(t log n)`, `t = {TT_T}`, `n ∈ NS`{part}', '',
      'Reduction `θ = r + M·π/2` with `Real.pi_gt_d20`/`Real.pi_lt_d20`; `cos`, `sin` at a rational centre by',
      '`PsiOmega.Num.cos_bounds`/`sin_bounds`, transferred by `Real.abs_cos_sub_cos_le`/`abs_sin_sub_sin_le`. -/', '',
      'open Real Finset', '', f'namespace {NS_}', ''] + [l for n in TCHUNKS[k] for l in trig_by_n[n]] + [f'end {NS_}', '',
      f'#print axioms {NS_}.cCB_{TCHUNKS[k][-1]}', f'#print axioms {NS_}.sCB_{TCHUNKS[k][-1]}'])

# ================================================================== Num file (as gen_locate.py)
num = [f'import {TNAMES[-1]}', '',
  f'/-! # Generated (`gen_locate_zero.py {TAG}`): the interval evaluation of `PReG cZ {M} 12`, `PImG cZ {M} 12`, `AReG cZ {M} 12`', '',
  f'The three open inequalities of `DHLocate{TAG}Base` (`H1`, `H2`, `H3`) from the atom bounds of `DHLocate{TAG}Exp` /',
  ', '.join(f'`{t}`' for t in TNAMES) + ', `κ` (`PsiOmega.kappa_bounds`) and `log n` (`PsiOmega.Num.log_bound_n`), by interval products',
  "(`mul_bounds_of`) and block sums; then `dh_zero_located` = `dh_zero_near_of_center' H1 H2 H3`. -/", '',
  'open Real Finset', '', f'namespace {NS_}', '']
NB = 8
def mb(h1, h2): return f"mul_bounds_of {h1} {h2}" + " (by norm_num)" * NB
BND = {}
def lemma(name, expr, b, proof_lines):
    BND[name] = b
    num.append(f"theorem {name} : {rat(b[0])} ≤ {expr} ∧ {expr} ≤ {rat(b[1])} := by")
    num.extend(proof_lines); num.append('')
LG = {}; EXPR = {}
for n in NT:
    e = exn(n)
    LG[n] = (rd_lo(LB[n][0]), rd_hi(LB[n][1]))
    lemma(f"lgB_{n}", f"Real.log {n}", LG[n], [f"  have h := PsiOmega.Num.log_bound_{n}", "  constructor <;> linarith [h.1, h.2]"])
    if n > 5*M: continue
    j = n % 5
    for tag, at, Bd, bn in (('C', 'cCG cZ', CB[n], 'cCB'), ('S', 'sCG cZ', SB[n], 'sCB')):
        ex_ = f"{e} * {at} {n}"
        b = rdb(mulb(EXB[n], Bd)); lemma(f"e{tag}_{n}", ex_, b, [f"  exact {mb(f'exB_{n}', f'{bn}_{n}')}"])
        EXPR[f"e{tag}_{n}"] = ex_
        if j in (2, 3):
            kx = f"kappa * ({ex_})"
            lemma(f"ke{tag}_{n}", kx, rdb(mulb(KB, b)), [f"  exact {mb('kappaBG', f'e{tag}_{n}')}"])
            EXPR[f"ke{tag}_{n}"] = kx
    lx = f"Real.log {n} * ({e} * cCG cZ {n})"
    b = rdb(mulb(LG[n], BND[f"eC_{n}"])); lemma(f"leC_{n}", lx, b, [f"  exact {mb(f'lgB_{n}', f'eC_{n}')}"])
    EXPR[f"leC_{n}"] = lx
    if j in (2, 3):
        kx = f"kappa * ({lx})"
        lemma(f"kleC_{n}", kx, rdb(mulb(KB, b)), [f"  exact {mb('kappaBG', f'leC_{n}')}"])
        EXPR[f"kleC_{n}"] = kx
def block_terms(kind, m):
    out = []
    for j in (1, 2, 3, 4):
        n = 5*m + j
        sign = 1 if j in (1, 2) else -1
        at = 'sCG cZ' if kind == 'I' else 'cCG cZ'
        if n == 1:
            ex_ = {'P': f"{exn(1)} * cCG cZ 1", 'I': f"{exn(1)} * sCG cZ 1",
                   'A': f"Real.log 1 * ({exn(1)} * cCG cZ 1)"}[kind]
            val = {'P': F(1), 'I': F(0), 'A': F(0)}[kind]
            out.append((ex_, (val, val), sign, None)); continue
        base_ = {'P': f"eC_{n}", 'I': f"eS_{n}", 'A': f"leC_{n}"}[kind]
        name = ('k' + base_) if j in (2, 3) else base_
        if kind == 'A' and j in (2, 3): name = f"kleC_{n}"
        out.append((EXPR[name], BND[name], sign, name))
    return out
BLK = {}
for kind, pre in (('P', 'PReB'), ('I', 'PImB'), ('A', 'AReB')):
    for m in range(M):
        terms = block_terms(kind, m)
        expr = terms[0][0]
        for (ex_, b, sg, nm) in terms[1:]:
            expr += (" + " if sg > 0 else " - ") + ex_
        lo = sum(b[0] if sg > 0 else -b[1] for (_, b, sg, _) in terms)
        hi = sum(b[1] if sg > 0 else -b[0] for (_, b, sg, _) in terms)
        pl = []; hs = []
        for i, (ex_, b, sg, nm) in enumerate(terms):
            if nm is None:
                pl.append(f"  have h{i} : {ex_} = {rat(b[0])} := by " +
                          {'P': "rw [ex_oneG, cCG_one]; norm_num", 'I': "rw [sCG_one]; norm_num",
                           'A': "rw [Real.log_one]; norm_num"}[kind])
                hs.append(f"h{i}")
            else:
                pl.append(f"  have h{i} := {nm}"); hs += [f"h{i}.1", f"h{i}.2"]
        pl.append(f"  constructor <;> linarith [{', '.join(hs)}]")
        lemma(f"{pre}_{m}", expr, (lo, hi), pl)
        BLK[(kind, m)] = (lo, hi)
TAIL = {}
for kind, pre in (('P', 'PReT'), ('I', 'PImT'), ('A', 'AReT')):
    for j in (1, 2, 3, 4):
        N = 5*M + j
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
                   f"  have hp1 : {rat(p1[0])} ≤ cCG cZ {N} * ({Dr_t} - Real.log {N} * {Qr_t}) ∧ cCG cZ {N} * ({Dr_t} - Real.log {N} * {Qr_t}) ≤ {rat(p1[1])} :=",
                   f"    {mb('hc', 'hv1')}",
                   f"  have hp2 : {rat(p2[0])} ≤ sCG cZ {N} * ({Di_t} - Real.log {N} * {Qi_t}) ∧ sCG cZ {N} * ({Di_t} - Real.log {N} * {Qi_t}) ≤ {rat(p2[1])} :=",
                   f"    {mb('hs', 'hv2')}"]
            ib = addb(p1, p2)
        ib = rdb(ib)
        hint = "hp1.1, hp1.2, hp2.1, hp2.2" if kind == 'A' else "hc.1, hc.2, hs.1, hs.2"
        pl += [f"  have hin : {rat(ib[0])} ≤ {inner} ∧ {inner} ≤ {rat(ib[1])} := by",
               f"    constructor <;> linarith [{hint}]"]
        tb = rdb(mulb(EXB[N], ib))
        texpr = f"{exn(N)} * ({inner})"
        pl += [f"  have he : {rat(tb[0])} ≤ {texpr} ∧ {texpr} ≤ {rat(tb[1])} :=",
               f"    {mb(f'exB_{N}', 'hin')}"]
        if j in (2, 3):
            kb = rdb(mulb(KB, tb))
            pl += [f"  exact {mb('kappaBG', 'he')}"]
            lemma(f"{pre}_{j}", f"kappa * ({texpr})", kb, pl)
            TAIL[(kind, j)] = kb
        else:
            pl += ["  exact he"]
            lemma(f"{pre}_{j}", texpr, tb, pl)
            TAIL[(kind, j)] = tb
RES = {}
simpPI = "  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd]"
simpA = "  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]"
for kind, pre, tpre, H, sgn in (('P', 'PReB', 'PReT', 'H1', 1), ('I', 'PImB', 'PImT', 'H2', -1), ('A', 'AReB', 'AReT', 'H3', -1)):
    s_lo = sum(BLK[(kind, m)][0] for m in range(M)); s_hi = sum(BLK[(kind, m)][1] for m in range(M))
    if sgn < 0: s_lo, s_hi = -s_hi, -s_lo
    t = [TAIL[(kind, j)] for j in (1, 2, 3, 4)]
    t_lo = t[0][0] + t[1][0] - t[2][1] - t[3][1]; t_hi = t[0][1] + t[1][1] - t[2][0] - t[3][0]
    RES[kind] = (s_lo + t_lo, s_hi + t_hi)
    lo, hi = RES[kind]
    hs = []; pl = []
    for m in range(M):
        pl.append(f"  have b{m} := {pre}_{m}"); hs += [f"b{m}.1", f"b{m}.2"]
    for j in (1, 2, 3, 4):
        pl.append(f"  have t{j} := {tpre}_{j}"); hs += [f"t{j}.1", f"t{j}.2"]
    unf = {'P': 'PRe_Z', 'I': 'PIm_Z', 'A': 'ARe_Z'}[kind]
    q = {'P': 'PReG', 'I': 'PImG', 'A': 'AReG'}[kind]
    what = {'P': 'Re fEM(c)', 'I': 'Im fEM(c)', 'A': 'Re fEM′(c)'}[kind]
    for side, rel in (('ge', f"{rat(lo)} ≤ {q} cZ {M} 12"), ('le', f"{q} cZ {M} 12 ≤ {rat(hi)}")):
        if kind == 'A' and cfg.get('hbA'): num += [f"set_option maxHeartbeats {cfg['hbA']} in"]
        num += [f"/-- {'Lower' if side == 'ge' else 'Upper'} end of the enclosure of `{what}`. -/"]
        num += [f"theorem {q}_{side} : {rel} := by",
                f"  rw [{unf}]", simpA if kind == 'A' else simpPI] + pl + [f"  linarith [{', '.join(hs)}]", ""]
    num += [f"/-- **The enclosure of `{what}`**: `{q} cZ {M} 12 ∈ [{float(lo):.10e}, {float(hi):.10e}]` (width `{float(hi - lo):.2e}`). -/",
            f"theorem {q}_mem : {rat(lo)} ≤ {q} cZ {M} 12 ∧ {q} cZ {M} 12 ≤ {rat(hi)} := ⟨{q}_ge, {q}_le⟩", ""]
    if kind in ('P', 'I'):
        assert -tol <= lo and hi <= tol, (kind, [float(v) for v in RES[kind]], float(tol))
        num += [f"/-- Open inequality `{H}` of `DHLocate{TAG}Base`. -/",
                f"theorem {H} : |{q} cZ {M} 12| ≤ {rat(tol)} := by",
                f"  have h := {q}_mem", "  rw [abs_le]", "  constructor <;> linarith [h.1, h.2]", ""]
    else:
        assert arlo <= lo, ([float(v) for v in RES[kind]], float(arlo))
        num += [f"/-- Open inequality `{H}` of `DHLocate{TAG}Base`. -/",
                f"theorem {H} : {rat(arlo)} ≤ AReG cZ {M} 12 := by",
                f"  have h := {q}_mem", "  linarith [h.1]", ""]
lo_re, hi_re = SIG - r, SIG + r; lo_im, hi_im = TT - r, TT + r
num += [f"/-- **The located zero**: within `{ratp(r)}` of `cZ = {SIG_T} + ({TT_T}) i` (`dh_zero_near_of_center'` with",
        "its three open inequalities discharged). -/",
        f"theorem dh_zero_located : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cZ‖ < {rat(r)} :=",
        "  dh_zero_near_of_center' H1 H2 H3", "",
        f"/-- The located zero in coordinates: `{float(lo_re):.5f} < Re ρ < {float(hi_re):.5f}` (off the critical line)",
        f"and `{float(lo_im):.5f} < Im ρ < {float(hi_im):.5f}`. -/",
        f"theorem dh_zero_located_box : ∃ ρ : ℂ, dh ρ = 0 ∧ {ratp(lo_re)} < ρ.re ∧ ρ.re < {ratp(hi_re)} ∧",
        f"    {ratp(lo_im)} < ρ.im ∧ ρ.im < {ratp(hi_im)} := by",
        "  obtain ⟨ρ, h0, hρ⟩ := dh_zero_located",
        "  have hre := abs_lt.1 ((Complex.abs_re_le_norm (ρ - cZ)).trans_lt hρ)",
        "  have him := abs_lt.1 ((Complex.abs_im_le_norm (ρ - cZ)).trans_lt hρ)",
        "  rw [Complex.sub_re, cZ_re] at hre",
        "  rw [Complex.sub_im, cZ_im] at him",
        "  exact ⟨ρ, h0, by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩", "",
        f'end {NS_}', '', 'namespace PsiOmega.Locate', '',
        f"/-- **Zero {TAG}** (`ρ ≈ {cfg['rho']}`): a kernel-checked zero of `dh` within `{ratp(r)}` of",
        f"`{SIG_T} + ({TT_T}) i`. -/",
        f"theorem dh_zero_located_{TAG} : ∃ ρ, dh ρ = 0 ∧ ‖ρ - Z{TAG}.cZ‖ < {rat(r)} := Z{TAG}.dh_zero_located", "",
        f"/-- **Zero {TAG}** in coordinates. -/",
        f"theorem dh_zero_located_box_{TAG} : ∃ ρ : ℂ, dh ρ = 0 ∧ {ratp(lo_re)} < ρ.re ∧ ρ.re < {ratp(hi_re)} ∧",
        f"    {ratp(lo_im)} < ρ.im ∧ ρ.im < {ratp(hi_im)} := Z{TAG}.dh_zero_located_box", "",
        'end PsiOmega.Locate', '']
for nm in ['PReG_mem', 'PImG_mem', 'AReG_mem', 'H1', 'H2', 'H3', 'dh_zero_located', 'dh_zero_located_box']:
    num.append(f'#print axioms {NS_}.{nm}')
num += [f'#print axioms PsiOmega.Locate.dh_zero_located_{TAG}', f'#print axioms PsiOmega.Locate.dh_zero_located_box_{TAG}']

for kind in 'PIA':
    lo, hi = RES[kind]
    print(f"  {kind}: [{float(lo):.10e}, {float(hi):.10e}]  width {float(hi - lo):.3e}")
print(f"  atoms: {len(NT)} values of n (max {max(NT)}); log width max {LOGW:.2e};"
      f" cos width max {max(float(CB[n][1]-CB[n][0]) for n in NT):.2e}; ex width max {max(float(EXB[n][1]-EXB[n][0]) for n in NT):.2e}")

if os.environ.get('WRITE', '1') == '1':
    outs = [(f'DHLocate{TAG}Base', base), (f'DHLocate{TAG}Exp', expf)] + list(zip(TNAMES, trigfs)) + [(f'DHLocate{TAG}Num', num)]
    for stem, lines in outs:
        open(os.path.join(HERE, f'{stem}.lean'), 'w').write('\n'.join(lines) + '\n')
    print("  wrote", ', '.join(f'{stem}.lean' for stem, _ in outs))
