# Generate DHTrigBounds.lean (TrigBounds{NMAX}.lean when NMAX ≠ 121): rational two-sided bounds for cos(θ_n), sin(θ_n), θ_n = (169/2) log n, n = 2..NMAX,
# and for the special angle 2ωa = 2028/5. Method: θ = r + s·π/2 + q·2π with s ∈ {0,1,2,3}, |r| ≤ 0.8;
# r is within δ of a rational centre x₀ (from log_bound_n and pi_gt_d6/pi_lt_d6); cos/sin at x₀ by the
# degree-12 alternating-series bounds (PsiOmega.Num.cos_bounds/sin_bounds), transferred by abs_cos_sub_cos_le.
from fractions import Fraction as F
import math, sys, mpmath as mp
mp.mp.dps = 40
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 121
OMEGA = F(169, 2)
PI_LO, PI_HI = F(3141592, 10**6), F(3141593, 10**6)
def rat(x):
    return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
def fact(k):
    return math.factorial(k)
def cos_poly(x, N):  # Σ_{i<N} (-1)^i x^{2i}/(2i)!
    return sum(F((-1)**i) * x**(2*i) / fact(2*i) for i in range(N))
def sin_poly(x, N):
    return sum(F((-1)**i) * x**(2*i+1) / fact(2*i+1) for i in range(N))
def center_bounds(x0):
    """(cl, cu, sl, su): rational bounds for cos x0, sin x0 at a rational centre with |x0| ≤ 1."""
    cl, cu = cos_poly(x0, 6), cos_poly(x0, 7)
    if x0 >= 0:
        sl, su = sin_poly(x0, 6), sin_poly(x0, 7)
    else:
        sl, su = -sin_poly(-x0, 7), -sin_poly(-x0, 6)
    return cl, cu, sl, su
# log bounds: re-derive exactly as gen_logbounds.py does
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

lines = ['import Mathlib', 'import DHNumerics', 'import DHLogBounds', '',
         '/-! # Generated: rational bounds for `cos(ω log n)`, `sin(ω log n)`, `ω = 169/2`, `2 ≤ n ≤ %d`,' % NMAX,
         'and for `cos(2028/5)`, `sin(2028/5)` (round 261, certificate stage 3) -/', '',
         'open Real Finset', '', 'namespace PsiOmega.Num', '',
         '/-- The reduced angle `θ − M·π/2`. -/',
         'noncomputable def redAngle (θ : ℝ) (M : ℤ) : ℝ := θ - M * (π / 2)', '']
def emit(name, theta_expr, thlo, thhi, hl_lines):
    """theta_expr: Lean expression of θ; thlo/thhi rational bounds on θ; hl_lines: tactic lines proving
    `hl : thlo ≤ θ ∧ θ ≤ thhi` (as list of strings)."""
    thmid = (thlo + thhi)/2
    M = round(float(thmid / (PI_LO + PI_HI) * 4))        # θ ≈ M·π/2
    q, s = divmod(M, 4)
    pimid = (PI_LO + PI_HI)/2
    xexact = thmid - M*pimid/2
    x0 = F(round(xexact * 10**6), 10**6)
    # |r − x0| ≤ (thhi−thlo)/2 + |M|·(PI_HI−PI_LO)/4 + |xexact − x0|
    delta = (thhi - thlo)/2 + abs(M)*(PI_HI - PI_LO)/4 + abs(xexact - x0)
    x0s = rat(x0) if x0 >= 0 else f"(-{rat(-x0)})"
    assert abs(x0) + delta <= 1, (name, x0, delta)
    cl, cu, sl, su = center_bounds(x0)
    # bounds for cos r, sin r: [cl − δ, cu + δ], [sl − δ, su + δ]
    crl, cru, srl, sru = cl - delta, cu + delta, sl - delta, su + delta
    # cos θ, sin θ from s
    if s == 0:   CL, CU, SL, SU = crl, cru, srl, sru
    elif s == 1: CL, CU, SL, SU = -sru, -srl, crl, cru
    elif s == 2: CL, CU, SL, SU = -cru, -crl, -sru, -srl
    else:        CL, CU, SL, SU = srl, sru, -cru, -crl
    out = []
    out += [f"theorem {name}_r_bounds : {rat(x0 - delta)} ≤ redAngle ({theta_expr}) {M} ∧ redAngle ({theta_expr}) {M} ≤ {rat(x0 + delta)} := by"]
    out += hl_lines
    out += ["  have hpi1 := Real.pi_gt_d6", "  have hpi2 := Real.pi_lt_d6", "  unfold redAngle", "  push_cast",
            "  constructor <;> linarith [hl.1, hl.2]", ""]
    shift = {0: "", 1: " + π / 2", 2: " + π", 3: " + π + π / 2"}[s]
    out += [f"theorem {name}_eq : ({theta_expr}) = (redAngle ({theta_expr}) {M}{shift}) + (({q} : ℤ) : ℝ) * (2 * π) := by",
            "  unfold redAngle", "  push_cast", "  ring", ""]
    # cos r and sin r bounds at the centre + Lipschitz
    out += [f"theorem {name}_cos_r : {rat(crl)} ≤ Real.cos (redAngle ({theta_expr}) {M}) ∧ Real.cos (redAngle ({theta_expr}) {M}) ≤ {rat(cru)} := by",
            f"  have hr := {name}_r_bounds",
            f"  have hc := PsiOmega.Num.cos_bounds (x := {x0s}) (by rw [abs_le]; constructor <;> norm_num)",
            "  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc",
            "  norm_num at hc",
            f"  have hlip := abs_le.1 (Real.abs_cos_sub_cos_le (redAngle ({theta_expr}) {M}) {x0s})"]
    if x0 < 0:
        out += ["  rw [Real.cos_neg] at hlip"]
    out += [f"  have hd : |redAngle ({theta_expr}) {M} - {x0s}| ≤ {rat(delta)} := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]",
            "  constructor <;> linarith [hlip.1, hlip.2, hc.1, hc.2, hd, abs_nonneg (redAngle (" + theta_expr + f") {M} - {x0s})]", ""]
    if x0 >= 0:
        sin_center = [f"  have hs := PsiOmega.Num.sin_bounds (x := {x0s}) (by norm_num) (by norm_num)",
                      "  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs", "  norm_num at hs"]
    else:
        sin_center = [f"  have hs0 := PsiOmega.Num.sin_bounds (x := {rat(-x0)}) (by norm_num) (by norm_num)",
                      "  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs0", "  norm_num at hs0",
                      f"  have hs : -({rat(sin_poly(-x0,7))}) ≤ Real.sin {x0s} ∧ Real.sin {x0s} ≤ -({rat(sin_poly(-x0,6))}) := by",
                      f"    rw [Real.sin_neg]",
                      "    constructor <;> linarith [hs0.1, hs0.2]"]
    out += [f"theorem {name}_sin_r : {rat(srl)} ≤ Real.sin (redAngle ({theta_expr}) {M}) ∧ Real.sin (redAngle ({theta_expr}) {M}) ≤ {rat(sru)} := by",
            f"  have hr := {name}_r_bounds"] + sin_center + [
            f"  have hlip := abs_le.1 (Real.abs_sin_sub_sin_le (redAngle ({theta_expr}) {M}) {x0s})",
            f"  have hd : |redAngle ({theta_expr}) {M} - {x0s}| ≤ {rat(delta)} := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]",
            "  constructor <;> linarith [hlip.1, hlip.2, hs.1, hs.2, hd, abs_nonneg (redAngle (" + theta_expr + f") {M} - {x0s})]", ""]
    # cos θ, sin θ
    r = f"redAngle ({theta_expr}) {M}"
    cos_rw = {0: f"  rw [Real.cos_add_int_mul_two_pi]",
              1: f"  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two]",
              2: f"  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi]",
              3: f"  rw [Real.cos_add_int_mul_two_pi, Real.cos_add_pi_div_two, Real.sin_add_pi]"}[s]
    sin_rw = {0: f"  rw [Real.sin_add_int_mul_two_pi]",
              1: f"  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two]",
              2: f"  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi]",
              3: f"  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi]"}[s]
    out += [f"theorem {name}_cos : {rat(CL)} ≤ Real.cos ({theta_expr}) ∧ Real.cos ({theta_expr}) ≤ {rat(CU)} := by",
            f"  have hc := {name}_cos_r", f"  have hs := {name}_sin_r", f"  rw [{name}_eq]", cos_rw,
            "  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]", ""]
    out += [f"theorem {name}_sin : {rat(SL)} ≤ Real.sin ({theta_expr}) ∧ Real.sin ({theta_expr}) ≤ {rat(SU)} := by",
            f"  have hc := {name}_cos_r", f"  have hs := {name}_sin_r", f"  rw [{name}_eq]", sin_rw,
            "  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]", ""]
    # sanity
    tc, ts = mp.cos(mp.mpf(thmid.numerator)/thmid.denominator), mp.sin(mp.mpf(thmid.numerator)/thmid.denominator)
    assert float(CL) <= float(tc) <= float(CU) and float(SL) <= float(ts) <= float(SU), (name, float(CL), float(tc), float(CU))
    return out, float(CU - CL)
widths = []
for n in range(2, NMAX+1):
    th = f"169 / 2 * Real.log {n}"
    out, w = emit(f"theta_{n}", th, OMEGA*L[n], OMEGA*U[n],
                  [f"  have hl0 := log_bound_{n}", f"  have hl : {rat(OMEGA*L[n])} ≤ 169 / 2 * Real.log {n} ∧ 169 / 2 * Real.log {n} ≤ {rat(OMEGA*U[n])} := by",
                   "    constructor <;> linarith [hl0.1, hl0.2]"])
    lines += out; widths.append(w)
out, w = emit("twoOmegaA", "(2028 / 5 : ℝ)", F(2028, 5), F(2028, 5),
              ["  have hl : (2028 / 5 : ℝ) ≤ (2028 / 5 : ℝ) ∧ (2028 / 5 : ℝ) ≤ (2028 / 5 : ℝ) := ⟨le_rfl, le_rfl⟩"])
lines += out
lines += ['end PsiOmega.Num', '', f'#print axioms PsiOmega.Num.theta_{NMAX}_cos', '#print axioms PsiOmega.Num.twoOmegaA_sin']
open('DHTrigBounds.lean' if NMAX == 121 else f'TrigBounds{NMAX}.lean', 'w').write('\n'.join(lines) + '\n')
print(f"wrote {NMAX-1} angles; max interval width {max(widths):.3e}")
