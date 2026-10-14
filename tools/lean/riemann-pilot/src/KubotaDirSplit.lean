import KubotaLocTable

/-! # The Dirichlet series `D_m` at a primary prime (round 453)

S5f-13 of round 360's plan, part 4. Round 452's next step planned the relations among round 428's Dirichlet
series `D_m(s) = Σ_c S_m(c)·N(c)^{−s}` at a primary prime `p ∤ x`, for `m = δ₃xp^e`. This round proves them,
for `Re s > 2`, with `N = N(p)`, `X = N(p)^{−s}` and `t = (3/p)₃`:

* **The series** (`dirD`, a definition; `dirL_eq`, `cuspSm_of_not_dvd`, `norm_cuspSm_le` and
  **`summable_dirD`**): `|S_m(c)| ≤ 9N(c)`, so `D_m(s)` converges absolutely for `Re s > 2`.
* **The split by the exponent of `p`** (`dirA`, a definition; `normSq_cpow_mul`, `normSq_cpow_pow`,
  `dirA_add_three`, `dirA_mod_three`, **`dirD_split`** and `dirD_split_sum`): with
  `A_a(s) = Σ_{p ∤ c} (c/p)₃^a·S_{δ₃x}(c)·N(c)^{−s}`,
  `D_{δ₃xp^e}(s) = A_{2e}(s) + Σ_{k ≥ 1} t^k·G_k(δ₃xp^e)·X^k·A_{2k+2e}(s)`, for `p ∤ x` a finite sum over
  `k ≤ e + 1`.
* **The Gauss sums modulo `p`** (`gaussP_add_three` and **`gaussP_one_mul_two`**): `γ_{j+3}(x) = γ_j(x)` for
  `j ≥ 1`, and `γ_1(x)·γ_2(x) = N` for `p ∤ x`.
* **The relations** (`cub_three_pow_three`, **`dirD_p5`** and **`dirD_p3`**):
  `D_{δ₃xp⁵} = (1 + N³X³)·D_{δ₃xp²}` and `D_{δ₃xp³} = (1 + N³X³)·D_{δ₃x} − t·X·γ_1(x)·D_{δ₃xp}`.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### The Dirichlet series `D_m(s)` -/

/-- **The Dirichlet series `D_m(s) = Σ_c S_m(c)·N(c)^{−s}`** of round 428's `integral_ebr_eis1_fundP3`. -/
def dirD (m : 𝓞 K) (s : ℂ) : ℂ :=
  ∑' c : 𝓞 K, cuspSm m c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)

/-- Round 450's completed series `dirL x` is `(2π/Γ(s))(2π|δ₃x|/9)^{s−1}·D_{δ₃x}(s)`. -/
theorem dirL_eq (x : 𝓞 K) (s : ℂ) :
    dirL x s = 2 * Real.pi / Complex.Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) *
      dirD (δ3 * x) s :=
  rfl

/-- `S_m(c) = 0` unless `3 ∣ c`: a bottom row `(c, d)` of `Γ_1(3)` has `3 ∣ c`. -/
theorem cuspSm_of_not_dvd (m : 𝓞 K) {c : 𝓞 K} (hc : ¬ (3 : 𝓞 K) ∣ c) : cuspSm m c = 0 := by
  unfold cuspSm
  exact (tsum_congr fun r => ite_eq_right fun h => hc h.2.1).trans tsum_zero

/-- **`|S_m(c)| ≤ 9N(c)`** for `c ≠ 0`: each of the `N(3c)` summands has absolute value at most `1` (round
370's `norm_σO_cub`). -/
theorem norm_cuspSm_le (m : 𝓞 K) {c : 𝓞 K} (hc : c ≠ 0) :
    ‖cuspSm m c‖ ≤ 9 * (absNorm (span {c}) : ℝ) := by
  classical
  have h30 : (3 : 𝓞 K) ≠ 0 := fun h => by
    have := congrArg σO h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have h3c : (3 : 𝓞 K) * c ≠ 0 := mul_ne_zero h30 hc
  have := finite_quot (3 * c) h3c
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * c})
  unfold cuspSm
  rw [tsum_fintype]
  refine le_trans (b := ∑ _r : 𝓞 K ⧸ span {3 * c}, (1 : ℝ))
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)) ?_
  · split_ifs with h
    · rw [norm_mul, norm_σO_cub h.2.2 h.1, norm_ebr, one_mul]
    · rw [norm_zero]; exact zero_le_one
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_quot,
      ← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_three]
    push_cast
    exact le_rfl

/-- **`D_m(s)` converges absolutely for `Re s > 2`** (round 441's `summable_mul_normSq_cpow`). -/
theorem summable_dirD (m : 𝓞 K) {s : ℂ} (hs : 2 < s.re) :
    Summable fun c : 𝓞 K => cuspSm m c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  classical
  have hs0 : -s ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have h := summable_mul_normSq_cpow (f := fun c => if c = 0 then 0 else cuspSm m c / 9) (fun c => ?_) hs
  · refine (h.mul_left 9).congr fun c => ?_
    by_cases hc : c = 0
    · subst hc
      simp [Complex.zero_cpow hs0]
    · simp only [hc, ite_false]
      ring
  · by_cases hc : c = 0
    · simp [hc]
    · simp only [hc, ite_false]
      rw [norm_div, show ‖(9 : ℂ)‖ = 9 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 9)]
      linarith [norm_cuspSm_le m hc]

/-- `N(ab)^{−s} = N(a)^{−s}·N(b)^{−s}`. -/
theorem normSq_cpow_mul (a b : 𝓞 K) (s : ℂ) :
    ((Complex.normSq (σO (a * b)) : ℝ) : ℂ) ^ (-s) =
      ((Complex.normSq (σO a) : ℝ) : ℂ) ^ (-s) * ((Complex.normSq (σO b) : ℝ) : ℂ) ^ (-s) := by
  rw [map_mul, Complex.normSq_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)]

/-- `N(a^k)^{−s} = (N(a)^{−s})^k`. -/
theorem normSq_cpow_pow (a : 𝓞 K) (k : ℕ) (s : ℂ) :
    ((Complex.normSq (σO (a ^ k)) : ℝ) : ℂ) ^ (-s) = (((Complex.normSq (σO a) : ℝ) : ℂ) ^ (-s)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, normSq_cpow_mul, ih, pow_succ]

/-! ### The split by the exponent of `p` -/

/-- **The part of `D_{δ₃x}` prime to `p`, twisted by `(c/p)₃^a`**:
`A_a(s) = Σ_{p ∤ c} (c/p)₃^a·S_{δ₃x}(c)·N(c)^{−s}`. -/
def dirA (p x : 𝓞 K) (a : ℕ) (s : ℂ) : ℂ :=
  ∑' c : {c : 𝓞 K // ¬ p ∣ c}, σO (cub (c : 𝓞 K) (span {p})) ^ a *
    (cuspSm (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s))

/-- `A_a` depends on `a` modulo `3`. -/
theorem dirA_add_three {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) (x : 𝓞 K) (a : ℕ) (s : ℂ) :
    dirA p x (a + 3) s = dirA p x a s := by
  unfold dirA
  refine tsum_congr fun c => ?_
  have h3 : σO (cub (c : 𝓞 K) (span {p})) ^ 3 = 1 := by
    rw [← map_pow, cub_pow_three hpp (isCoprime_of_not_dvd hp c.2), map_one]
  rw [pow_add, h3, mul_one]

/-- `A_a` depends only on `a mod 3`. -/
theorem dirA_mod_three {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) (x : 𝓞 K) (a : ℕ) (s : ℂ) :
    dirA p x a s = dirA p x (a % 3) s := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases lt_or_ge a 3 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
      rw [dirA_add_three hp hpp, ih b (by omega), Nat.add_mod_right]

/-- **`D_{δ₃xp^e}` by the exponent of `p`**: for a primary prime `p` and `Re s > 2`,
`D_{δ₃xp^e}(s) = Σ_k c_k·N(p)^{−ks}·A_{2k+2e}(s)`, with `c_0 = 1` and `c_k = (3/p)₃^k·G_k(δ₃xp^e)` for
`k ≥ 1`. The `c ≠ 0` are the `p^k c′` with `p ∤ c′`, each once (Mathlib's `WfDvdMonoid.max_power_factor`),
and round 451's `cuspSm_mul_pow` and `cuspSm_twist` factor `S_{δ₃xp^e}(p^k c′)`. -/
theorem dirD_split {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) (x : 𝓞 K) (e : ℕ) {s : ℂ}
    (hs : 2 < s.re) :
    dirD (δ3 * (x * p ^ e)) s = ∑' k : ℕ,
      (if k = 0 then 1 else σO (cub 3 (span {p})) ^ k * locG (δ3 * (x * p ^ e)) p k) *
        (((Complex.normSq (σO p) : ℝ) : ℂ) ^ (-s)) ^ k * dirA p x (2 * k + 2 * e) s := by
  classical
  have hp0 := hp.ne_zero
  have hs0 : -s ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  set f : 𝓞 K → ℂ := fun c =>
    cuspSm (δ3 * (x * p ^ e)) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) with hf_def
  have hf : Summable f := summable_dirD _ hs
  set φ : ℕ × {c : 𝓞 K // ¬ p ∣ c} → 𝓞 K := fun kc => p ^ kc.1 * kc.2 with hφ_def
  have key : ∀ {k l : ℕ} {c d : 𝓞 K}, ¬ p ∣ d → p ^ k * c = p ^ l * d → k ≤ l := by
    intro k l c d hd h
    by_contra hlt
    push Not at hlt
    apply hd
    have h' : p ^ l * (p ^ (k - l) * c) = p ^ l * d := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, h]
    rw [← mul_left_cancel₀ (pow_ne_zero l hp0) h']
    exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.sub_ne_zero_of_lt hlt)) c
  have hφ : Function.Injective φ := by
    rintro ⟨k, c, hc⟩ ⟨l, d, hd⟩ h
    simp only [hφ_def] at h
    obtain rfl := le_antisymm (key hd h) (key hc h.symm)
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ (pow_ne_zero k hp0) h))
  have hsupp : Function.support f ⊆ Set.range φ := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hc
      simp only [hf_def, map_zero, Complex.ofReal_zero, Complex.zero_cpow hs0, mul_zero]
    obtain ⟨n, a, ha, rfl⟩ := WfDvdMonoid.max_power_factor hc0 hp.irreducible
    exact ⟨(n, ⟨a, ha⟩), rfl⟩
  have hg : Summable (f ∘ φ) := hf.comp_injective hφ
  unfold dirD
  rw [← hφ.tsum_eq hsupp]
  change ∑' kc, (f ∘ φ) kc = _
  rw [hg.tsum_prod' hg.prod_factor]
  refine tsum_congr fun k => ?_
  unfold dirA
  rw [← tsum_mul_left]
  refine tsum_congr fun ⟨c, hc⟩ => ?_
  show cuspSm (δ3 * (x * p ^ e)) (p ^ k * c) * ((Complex.normSq (σO (p ^ k * c)) : ℝ) : ℂ) ^ (-s) = _
  rw [normSq_cpow_mul, normSq_cpow_pow]
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero p)
  by_cases h3 : (3 : 𝓞 K) ∣ c
  · have htw := cuspSm_twist hpp hc0 h3 (isCoprime_of_not_dvd hp hc).symm e x
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [pow_zero, one_mul, ite_true, htw]
      ring
    · rw [cuspSm_mul_pow hp hpp hk hc0 h3 hc (x * p ^ e), htw, ite_eq_right hk.ne']
      ring
  · have h3' : ¬ (3 : 𝓞 K) ∣ p ^ k * c := fun h =>
      h3 (((isCoprime_three_of_primary hpp).pow_right (n := k)).dvd_of_dvd_mul_left h)
    rw [cuspSm_of_not_dvd _ h3', cuspSm_of_not_dvd _ h3]
    ring

/-- **The split as a finite sum**: for `p ∤ x` the terms with `k ≥ e + 2` vanish (round 452's `locG_high`). -/
theorem dirD_split_sum {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {x : 𝓞 K} (hpx : ¬ p ∣ x) (e : ℕ)
    {s : ℂ} (hs : 2 < s.re) :
    dirD (δ3 * (x * p ^ e)) s = ∑ k ∈ Finset.range (e + 2),
      (if k = 0 then 1 else σO (cub 3 (span {p})) ^ k * locG (δ3 * (x * p ^ e)) p k) *
        ((absNorm (span {p}) : ℂ) ^ (-s)) ^ k * dirA p x ((2 * k + 2 * e) % 3) s := by
  have hN : ((Complex.normSq (σO p) : ℝ) : ℂ) = (absNorm (span {p}) : ℂ) := by
    rw [normSq_σO, Complex.ofReal_natCast]
  rw [dirD_split hp hpp x e hs, hN, tsum_eq_sum (s := Finset.range (e + 2)) fun k hk => ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [dirA_mod_three hp hpp]
  · rw [Finset.mem_range, not_lt] at hk
    rw [ite_eq_right (by omega), locG_high hp hpx hk, mul_zero, zero_mul, zero_mul]

/-! ### The Gauss sums modulo `p` -/

/-- **`γ_{j+3}(h) = γ_j(h)` for `j ≥ 1`**: `(f/p)₃³ = 1` for `p ∤ f` (round 362's `cub_pow_three`), and both
summands are `0` for `p ∣ f`. -/
theorem gaussP_add_three {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) (h : 𝓞 K) {j : ℕ} (hj : 0 < j) :
    gaussP h p (j + 3) = gaussP h p j := by
  unfold gaussP gTerm
  refine tsum_congr fun f => ?_
  by_cases hf : p ∣ repQ p f
  · rw [cub_span_eq_zero hp hf, map_zero, zero_pow (by omega), zero_pow hj.ne']
  · have h3 : σO (cub (repQ p f) (span {p})) ^ 3 = 1 := by
      rw [← map_pow, cub_pow_three hpp (isCoprime_of_not_dvd hp hf), map_one]
    rw [pow_add, h3, mul_one]

/-- **`γ_1(h)·γ_2(h) = N(p)`** for a primary prime `p ∤ h`. `γ_j(h)` is the Gauss sum of `χ^j`, for round
292's cubic character `χ` modulo `p`, with the additive character `f ↦ ψ_p(−fh)`, which is primitive (round
363's `ψQ_isPrimitive_of_ne_zero`); Mathlib's `gaussSum_mul_gaussSum_pow_orderOf_sub_one` gives `χ(−1)·N(p)`,
and `χ(−1) = 1` (round 292's `cubCharC_neg_one`). -/
theorem gaussP_one_mul_two {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {h : 𝓞 K} (hph : ¬ p ∣ h) :
    gaussP h p 1 * gaussP h p 2 = (absNorm (span {p}) : ℂ) := by
  classical
  have hp0 := hp.ne_zero
  have := span_isMaximal_of_prime hp
  have hP3 := three_not_mem_span hp hpp
  have := finite_quot p hp0
  let : Fintype (𝓞 K ⧸ span {p}) := Fintype.ofFinite _
  set χ := cubCharC (span {p}) hP3 with hχ_def
  set ψ := (ψQ p hp0).mulShift (Ideal.Quotient.mk (span {p}) (-h)) with hψ_def
  have hb : Ideal.Quotient.mk (span {p}) (-h) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, dvd_neg]
    exact hph
  have hψ : ψ.IsPrimitive := fun a ha => by
    rw [hψ_def, AddChar.mulShift_mulShift]
    exact ψQ_isPrimitive_of_ne_zero p hp0 (mul_ne_zero hb ha)
  have key := gaussSum_mul_gaussSum_pow_orderOf_sub_one (cubCharC_ne_one (span {p}) hP3) hψ
  rw [← hχ_def, orderOf_cubCharC, hχ_def, cubCharC_neg_one, one_mul] at key
  have hg : ∀ j, 0 < j → gaussP h p j = gaussSum (χ ^ j) ψ := by
    intro j hj
    unfold gaussP gaussSum
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hχf : χ f = σO (cub (repQ p f) (span {p})) := by
      rw [show χ f = χ (Ideal.Quotient.mk _ (repQ p f)) by rw [repQ_mk], cub_prime, chi3_eq hP3]
      rfl
    have hψf : ψ f = ψc p (-repQ p f * h) := by
      rw [show ψ f = ψ (Ideal.Quotient.mk _ (repQ p f)) by rw [repQ_mk], hψ_def, AddChar.mulShift_apply,
        ← map_mul, ψQ_mk]
      congr 1
      ring
    unfold gTerm
    rw [MulChar.pow_apply' χ hj.ne', hχf, hψf, ebr_gTerm]
  rw [hg 1 one_pos, hg 2 two_pos, pow_one, key, card_quot]

/-! ### The relations at `p` -/

/-- `(3/p)₃³ = 1`. -/
theorem cub_three_pow_three {p : 𝓞 K} (hpp : Primary p) : σO (cub 3 (span {p})) ^ 3 = 1 := by
  rw [← map_pow, cub_pow_three hpp (isCoprime_three_of_primary hpp), map_one]

/-- **`D_{δ₃xp⁵} = (1 + N(p)^{3−3s})·D_{δ₃xp²}`** for a primary prime `p ∤ x` and `Re s > 2`, with
`N(p)^{3−3s}` written `N(p)³·(N(p)^{−s})³`, by round 452's table. -/
theorem dirD_p5 {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {x : 𝓞 K} (hpx : ¬ p ∣ x) {s : ℂ}
    (hs : 2 < s.re) :
    dirD (δ3 * (x * p ^ 5)) s =
      (1 + (absNorm (span {p}) : ℂ) ^ 3 * ((absNorm (span {p}) : ℂ) ^ (-s)) ^ 3) *
        dirD (δ3 * (x * p ^ 2)) s := by
  have L1 : locG (δ3 * (x * p ^ 5)) p 1 = 0 := by
    rw [locG_low hp hpp x one_pos (by norm_num), ite_eq_right (by decide)]
  have L2 : locG (δ3 * (x * p ^ 5)) p 2 = 0 := by
    rw [locG_low hp hpp x two_pos (by norm_num), ite_eq_right (by decide)]
  have L3 : locG (δ3 * (x * p ^ 5)) p 3 =
      (absNorm (span {p}) : ℂ) ^ 2 * ((absNorm (span {p}) : ℂ) - 1) := by
    rw [locG_low hp hpp x (by norm_num) (by norm_num), ite_eq_left (by decide)]
  have L4 : locG (δ3 * (x * p ^ 5)) p 4 = 0 := by
    rw [locG_low hp hpp x (by norm_num) (by norm_num), ite_eq_right (by decide)]
  have L5 : locG (δ3 * (x * p ^ 5)) p 5 = 0 := by
    rw [locG_low hp hpp x (by norm_num) (by norm_num), ite_eq_right (by decide)]
  have L6 : locG (δ3 * (x * p ^ 5)) p 6 = -(absNorm (span {p}) : ℂ) ^ 5 :=
    locG_mid_three hp hpp hpx (e := 5) (by decide)
  have M1 : locG (δ3 * (x * p ^ 2)) p 1 = 0 := by
    rw [locG_low hp hpp x one_pos (by norm_num), ite_eq_right (by decide)]
  have M2 : locG (δ3 * (x * p ^ 2)) p 2 = 0 := by
    rw [locG_low hp hpp x two_pos (by norm_num), ite_eq_right (by decide)]
  have M3 : locG (δ3 * (x * p ^ 2)) p 3 = -(absNorm (span {p}) : ℂ) ^ 2 :=
    locG_mid_three hp hpp hpx (e := 2) (by decide)
  have ht := cub_three_pow_three hpp
  rw [dirD_split_sum hp hpp hpx 5 hs, dirD_split_sum hp hpp hpx 2 hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, L1, L2, L3, L4, L5, L6, M1, M2, M3,
    Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, mul_zero, zero_mul,
    add_zero, zero_add, pow_zero, pow_one, one_mul, mul_one]
  set N := (absNorm (span {p}) : ℂ)
  set X := N ^ (-s)
  set t := σO (cub 3 (span {p}))
  linear_combination (dirA p x 1 s * N ^ 3 * X ^ 3 - t ^ 3 * dirA p x 1 s * N ^ 5 * X ^ 6) * ht

/-- **`D_{δ₃xp³} = (1 + N(p)^{3−3s})·D_{δ₃x} − (3/p)₃·N(p)^{−s}·γ_1(x)·D_{δ₃xp}`** for a primary prime `p ∤ x`
and `Re s > 2`, with `N(p)^{3−3s}` written `N(p)³·(N(p)^{−s})³`, by round 452's table and
`γ_1(x)·γ_2(x) = N(p)`. -/
theorem dirD_p3 {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {x : 𝓞 K} (hpx : ¬ p ∣ x) {s : ℂ}
    (hs : 2 < s.re) :
    dirD (δ3 * (x * p ^ 3)) s =
      (1 + (absNorm (span {p}) : ℂ) ^ 3 * ((absNorm (span {p}) : ℂ) ^ (-s)) ^ 3) * dirD (δ3 * x) s -
        σO (cub 3 (span {p})) * (absNorm (span {p}) : ℂ) ^ (-s) * gaussP x p 1 *
          dirD (δ3 * (x * p)) s := by
  have L1 : locG (δ3 * (x * p ^ 3)) p 1 = 0 := by
    rw [locG_low hp hpp x one_pos (by norm_num), ite_eq_right (by decide)]
  have L2 : locG (δ3 * (x * p ^ 3)) p 2 = 0 := by
    rw [locG_low hp hpp x two_pos (by norm_num), ite_eq_right (by decide)]
  have L3 : locG (δ3 * (x * p ^ 3)) p 3 =
      (absNorm (span {p}) : ℂ) ^ 2 * ((absNorm (span {p}) : ℂ) - 1) := by
    rw [locG_low hp hpp x (by norm_num) le_rfl, ite_eq_left (by decide)]
  have L4 : locG (δ3 * (x * p ^ 3)) p 4 = (absNorm (span {p}) : ℂ) ^ 3 * gaussP x p 4 :=
    locG_mid hp x 3
  have G4 : gaussP x p 4 = gaussP x p 1 := gaussP_add_three hp hpp x one_pos
  have Z1 : locG (δ3 * (x * p ^ 0)) p 1 = (absNorm (span {p}) : ℂ) ^ 0 * gaussP x p 1 :=
    locG_mid hp x 0
  have O1 : locG (δ3 * (x * p ^ 1)) p 1 = 0 := by
    rw [locG_low hp hpp x one_pos le_rfl, ite_eq_right (by decide)]
  have O2 : locG (δ3 * (x * p ^ 1)) p 2 = (absNorm (span {p}) : ℂ) ^ 1 * gaussP x p 2 :=
    locG_mid hp x 1
  have hγ := gaussP_one_mul_two hp hpp hpx
  have ht := cub_three_pow_three hpp
  have e0 : dirD (δ3 * x) s = dirD (δ3 * (x * p ^ 0)) s := by rw [pow_zero, mul_one]
  have e1 : dirD (δ3 * (x * p)) s = dirD (δ3 * (x * p ^ 1)) s := by rw [pow_one]
  rw [e0, e1, dirD_split_sum hp hpp hpx 3 hs, dirD_split_sum hp hpp hpx 0 hs,
    dirD_split_sum hp hpp hpx 1 hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd]
  simp only [L1, L2, L3, L4, G4, Z1, O1, O2]
  simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, mul_zero, zero_mul,
    add_zero, zero_add, pow_zero, pow_one, one_mul, mul_one]
  set N := (absNorm (span {p}) : ℂ)
  set X := N ^ (-s)
  set t := σO (cub 3 (span {p}))
  linear_combination (N ^ 2 * (N - 1) * X ^ 3 * dirA p x 0 s + N ^ 2 * X ^ 3 * dirA p x 0 s +
    t * N ^ 3 * gaussP x p 1 * X ^ 4 * dirA p x 2 s) * ht + t ^ 3 * N * X ^ 3 * dirA p x 0 s * hγ

end Eis

end

#print axioms Eis.dirL_eq
#print axioms Eis.cuspSm_of_not_dvd
#print axioms Eis.norm_cuspSm_le
#print axioms Eis.summable_dirD
#print axioms Eis.normSq_cpow_mul
#print axioms Eis.normSq_cpow_pow
#print axioms Eis.dirA_add_three
#print axioms Eis.dirA_mod_three
#print axioms Eis.dirD_split
#print axioms Eis.dirD_split_sum
#print axioms Eis.gaussP_add_three
#print axioms Eis.gaussP_one_mul_two
#print axioms Eis.cub_three_pow_three
#print axioms Eis.dirD_p5
#print axioms Eis.dirD_p3
