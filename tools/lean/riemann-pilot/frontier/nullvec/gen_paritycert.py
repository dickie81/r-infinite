#!/usr/bin/env python3
"""Round 135: write src/ParityCert.lean from the arb certificates kpar_cert_{even,odd}_A.json.
Usage: gen_paritycert.py EVEN_JSON ODD_JSON CINB_EVEN CINB_ODD
CINB_*: the integer B with B/10^6 <= lowP (sumQ (N+1)) (kernel-checked), so T = 2.780109 + B/10^6."""
import sys, json
from fractions import Fraction
def load(fn): return json.load(open(fn))
E, O = load(sys.argv[1]), load(sys.argv[2])
cinE, cinO = int(sys.argv[3]), int(sys.argv[4])
def frac(s):
    f = Fraction(s); return f"({f.numerator} / {f.denominator} : ℝ)" if f.denominator != 1 else f"({f.numerator} : ℝ)"
def epsq(s): f = Fraction(s); return f"({f.numerator} / {f.denominator} : ℝ)"
def Tval(B): return Fraction("2.780109") + Fraction(B, 10**6)
def klemmas(K, name, b):
    bf = Fraction(b)
    if K == 4:
        assert bf >= Fraction(6, 10) and bf <= Fraction(693147, 10**6)
        lo = f"""theorem hKlo_{name} : Real.log ((4 - 1 : ℕ) : ℝ) ≤ 2 * {frac(b)} := by
  have := log_three_le; norm_num at this ⊢; linarith"""
        hi = f"""theorem hKhi_{name} : 2 * {frac(b)} < Real.log (4 : ℕ) := by
  have := Real.log_two_gt_d9; push_cast; rw [log_four_eq]; norm_num at this ⊢; linarith"""
    elif K == 5:
        assert bf >= Fraction(6932, 10000) and bf < Fraction(8, 10)
        lo = f"""theorem hKlo_{name} : Real.log ((5 - 1 : ℕ) : ℝ) ≤ 2 * {frac(b)} := by
  have := Real.log_two_lt_d9; norm_num; rw [log_four_eq]; norm_num at this ⊢; linarith"""
        hi = f"""theorem hKhi_{name} : 2 * {frac(b)} < Real.log (5 : ℕ) := by
  have := log_five_gt; push_cast; norm_num at this ⊢; linarith"""
    else:
        raise ValueError(K)
    return lo + "\n\n" + hi
def block(C, B, sec):
    name = "E" if sec == "even" else "O"
    N, K, b, eps = C["N"], C["K"], C["a"], C["eps"]
    T = Tval(B); assert Fraction(C["tail_T"]) == T, (C["tail_T"], T)
    lst = ", ".join(C["psiC"][str(m)] for m in range(1, N + 1))
    n = N + 2 if sec == "even" else N + 1
    gram = "gC" if sec == "even" else "gCO"
    sf = "sfunW" if sec == "even" else "sfunO"
    thm = "weilQ_ge_of_certW" if sec == "even" else "weilQodd_ge_of_certW"
    concl = "weilQ a g" if sec == "even" else "weilQg a g"
    probe = "Probe a g" if sec == "even" else "OProbe a g"
    sz = f"{N} + 2" if sec == "even" else f"{N} + 1"
    return f"""
/-! ## The {sec} sector at `a* = {b}`: `N = {N}`, primes `n < {K}`, `ε = {eps}` -/

/-- Certified `ψ̲_m ≤ ψ_m` at `a* = {b}`, `m = 1..{N}` (arb quadrature, `kpar_cert_{sec}_{b}.json`). -/
def psi{name}q : List ℚ := [{lst}]

def psi{name} (k : ℕ) : ℝ := ((psi{name}q.getD (k - 1) 0 : ℚ) : ℝ)

/-- The tail constant: `{float(T):.6f} ≤ Cin({N + 1}π/2)` (the rational chain `cin_of_check`, kernel-checked). -/
theorem cin{name} : {frac(str(T))} ≤ Cin ((({N} + 1 : ℕ) : ℝ) * π / 2) := by
  have h := cin_of_check (N := {N} + 1) (by norm_num) (b := {B} / 10 ^ 6) (by decide +kernel)
  push_cast at h ⊢; linarith

{klemmas(K, name, b)}

def gram{name} : Matrix (Fin ({sz})) (Fin ({sz})) ℝ := Matrix.of fun i j => {gram} {frac(b)} i j

/-- **The {sec} certificate** (checked by `frontier/nullvec/kpar_cert.py cert {sec} {b} {N} {eps}`). -/
def Cert{name} : Prop :=
  (∀ k : ℕ, k < {N} → psi{name} (k + 1) ≤ modeE {frac(b)} ((k : ℤ) + 1)) ∧ gram{name}.PosDef ∧
    {epsq(eps)} ≤ kappaW {frac(b)} {frac(str(T))} {K} ∧
    ((kappaW {frac(b)} {frac(str(T))} {K} - {epsq(eps)}) • gram{name}
      + gram{name} * diagonal (fun i : Fin ({sz}) => {sf} {frac(b)} (tauW {frac(b)} {frac(str(T))} {K}) (wP {frac(b)} {K}) psi{name} i)
        * gram{name}).PosSemidef

/-- **{sec.capitalize()}-sector positivity up to `a* = {b}`**: granted `Cert{name}`, every normalised {sec} probe
at every support `0 < a ≤ {b}` has `Q(g) ≥ {eps}`. -/
theorem weilQ_ge_{name} {{a : ℝ}} (ha : 0 < a) (hab : a ≤ {frac(b)}) (hc : Cert{name}) {{g : ℝ → ℝ}}
    (hp : {probe}) (hn : normSq g = 1) : {epsq(eps)} ≤ {concl} :=
  {thm} (K := {K}) (N := {N}) (by norm_num) (by norm_num) (by norm_num) hKlo_{name} hKhi_{name} cin{name} psi{name}
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 ha hab hp hn
"""
bE, bO = Fraction(E["a"]), Fraction(O["a"])
bmin = min(bE, bO)
src = f"""import Mathlib
import ParityRelax

/-! # Weil positivity in both parity sectors, as far as the relaxation reaches (round 135)

Instances of `weilQ_ge_of_certW` / `weilQodd_ge_of_certW` (ParityRelax.lean), each granted one arb certificate:

* **even sector**: `Q(g) ≥ {E['eps']}` for every normalised even probe at every support `0 < a ≤ {E['a']}`
  (`weilQ_ge_E`), with the primes `n < {E['K']}` and `N = {E['N']}` modes;
* **odd sector**: `Q(g) ≥ {O['eps']}` for every normalised odd probe at every support `0 < a ≤ {O['a']}`
  (`weilQ_ge_O`), with the primes `n < {O['K']}` and `N = {O['N']}` modes;
* **every real `g`**: `Q(g) ≥ min(ε_e, ε_o)‖g‖²` for `0 < a ≤ {bmin}` (`weilQg_ge_both`).
-/

open Real Filter Topology Complex MeasureTheory Set Matrix

noncomputable section

namespace Pilot1ca

theorem log_three_le : Real.log 3 ≤ 1.2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have h2 : (0.2 : ℝ) + 1 ≤ Real.exp 0.2 := Real.add_one_le_exp _
  have : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

theorem log_five_gt : (1.6 : ℝ) < Real.log 5 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have he := Real.exp_one_lt_d9
  have hb := Real.exp_bound (x := 0.6) (by rw [abs_of_pos (by norm_num)]; norm_num) (n := 5) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at hb
  have hb' : Real.exp 0.6 ≤ 1.8223 := by
    have := (abs_le.mp hb).2
    norm_num at this ⊢; linarith
  have : Real.exp 1.6 = Real.exp 1 * Real.exp 0.6 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have h0 : 0 < Real.exp 0.6 := Real.exp_pos _
  norm_num at he
  nlinarith

theorem log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
{block(E, cinE, "even")}
{block(O, cinO, "odd")}
/-- **Weil positivity for every real `g`**, granted both certificates: `Q(g) ≥ min(ε_e, ε_o)‖g‖²` at every support
`0 < a ≤ {bmin}`. -/
theorem weilQg_ge_both {{a : ℝ}} (ha : 0 < a) (hab : a ≤ {frac(str(bmin))}) (hE : CertE) (hO : CertO) {{g : ℝ → ℝ}}
    (hg : SProbe a g) : min {epsq(E['eps'])} {epsq(O['eps'])} * normSq g ≤ weilQg a g :=
  weilQg_ge_min ha (fun _ hp hn => weilQ_ge_E ha (by linarith) hE hp hn)
    (fun _ hp hn => weilQ_ge_O ha (by linarith) hO hp hn) hg

end Pilot1ca

#print axioms Pilot1ca.weilQ_ge_E
#print axioms Pilot1ca.weilQ_ge_O
#print axioms Pilot1ca.weilQg_ge_both
"""
open("../../src/ParityCert.lean", "w").write(src)
print("wrote ParityCert.lean", len(src))
