/-
# Round 653: the Ramanujan sum's bound and the decay of `J` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li end the proof of Proposition 7.1 with two inputs. For the kernel: "As w(u) is a smooth bump supported on
[1,2], we observe that w(v₁u₃)²w(v₂u₃)²w(u₃)²u₃² vanishes unless v₁, v₂ ∈ [1/2,2]. Furthermore, its jth derivative
with respect to u₃ is bounded by O_j(1). Thus, by repeated integration by parts, the inner integral is
O_ϵ((qT)^{−300}) unless |m₁v₁+m₂v₂+m₃| ≤ (qT)^ϵq/N and v₁, v₂ ∈ [1/2,2]. On the other hand, the inner integral is
O(1) trivially." For the Ramanujan sum: "the fact that |C_q(m)| ≤ (m,q)" (text layer lines 2227–2234; spaces
restored, the exponents and subscripts transcribed). This file proves both inputs, the second in the weaker form
`|C_q(n)| ≤ d(q)(n, q)`, whose extra `d(q)` the factor `(qTN)^ε` of round 639's `CGLS3` absorbs.

Plain statements.
* `norm_Cq_le`: for `q ≥ 1` and `n ∈ ℤ/qℤ`, `|C_q(n)| ≤ d(q)·gcd(n, q)`, with `n` read as its least nonnegative
  residue and round 652's `C_q(n) = Σ_{a∈(ℤ/qℤ)ˣ}e(an/q)`.
* `Jk_decay`: for every `K` there is `C_K` with `(2π|λ|)^K|J(v₁, v₂, λ)| ≤ C_K` for all real `λ` and `|v₁|, |v₂| ≤ 2`,
  where `J` is round 651's kernel; `K = 0` is their "O(1) trivially".
* `Jk_eq_zero_of`: `J(v₁, v₂, λ) = 0` unless `v₁, v₂ ∈ (1/2, 2)`.

The proofs. `C_q(n) = Σ_{0≤a<q, (a,q)=1}e(an/q) = Σ_{d|q}μ(d)Σ_{a<q, d|a}e(an/q) = Σ_{d|q}μ(d)(q/d)[q/d | n]`: Möbius
over the divisors of `q` (round 649's `sum_coprime_eq`, here in `ℂ`) and geometric sums of roots of unity. Each term is
at most `(n, q)` in absolute value, since `q/d | n` and `q/d | q` give `q/d | (n, q)`. For the kernel,
`g_v(u) = u²w(v₁u)²w(v₂u)²w(u)²` is `G(v₁u, v₂u, u)` with `G(a, b, c) = c²w(a)²w(b)²w(c)²`, smooth with compact
support on `ℝ³`. So the `K`-th derivative of `g_v` is that of `G` along `u ↦ (v₁u, v₂u, u)`, at most
`sup‖D^KG‖·‖(v₁, v₂, 1)‖^K ≤ C·2^K`. Integration by parts (round 588's `SieveSmooth.pow_mul_norm_fourier_le`, from
Mathlib's `Real.fourier_iteratedDeriv`) gives `(2π|λ|)^K|J| ≤ ∫|g_v^{(K)}| ≤ C·2^K`, since `g_v^{(K)}` vanishes off
`[1, 2]`.

* `sum_divisors_moebius_C`, `sum_coprime_eq_C`: Möbius over the divisors of `q`, in `ℂ`.
* `sum_range_exp`, `sum_multiples_exp`: the geometric sums (Mathlib's `geom_sum_eq` and `Complex.exp_eq_one_iff`).
* `Cq_eq_range`, `Cq_eq_moebius`, `norm_Cq_le`: the Ramanujan sum.
* `Gk`, `contDiff_Gk`, `Gk_ne_zero`, `hasCompactSupport_Gk`, `exists_bound_Gk`, `Lv`, `Lv_apply`, `norm_Lv_le`,
  `gv_eq_comp`, `iteratedDeriv_gv_eq_zero`, `Jk_decay`: the decay of `J` (Mathlib's
  `ContinuousLinearMap.iteratedFDeriv_comp_right` and `ContinuousMultilinearMap.norm_compContinuousLinearMap_le`).
* `Jk_eq_zero_of`: the support of `J`.

The file imports `LinnikCGLRFact.lean`.
-/

import LinnikCGLRFact

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLRam

open ArithmeticFunction (moebius)
open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLProd LinnikCGLRFact

/-! ### The Ramanujan sum -/

/-- `Σ_{d|n} μ(d) = [n = 1]`, in `ℂ`. -/
lemma sum_divisors_moebius_C (n : ℕ) : ∑ d ∈ n.divisors, (moebius d : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n) (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] at h
  exact h

/-- **Möbius over the divisors of `q`**, in `ℂ`: `Σ_{n∈S, (n,q)=1} f(n) = Σ_{d|q} μ(d) Σ_{n∈S, d|n} f(n)`. -/
lemma sum_coprime_eq_C {q : ℕ} (hq : q ≠ 0) (S : Finset ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ S.filter (fun n => n.Coprime q), f n =
      ∑ d ∈ q.divisors, (moebius d : ℂ) * ∑ n ∈ S.filter (fun n => d ∣ n), f n := by
  classical
  have key : ∀ n, (if n.Coprime q then (1 : ℂ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then (moebius d : ℂ) else 0 := by
    intro n
    have hg : n.gcd q ≠ 0 := Nat.gcd_ne_zero_right hq
    have hdiv : q.divisors.filter (fun d => d ∣ n) = (n.gcd q).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h2, h1⟩, hg⟩
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hq⟩, h1⟩
    rw [← Finset.sum_filter, hdiv, sum_divisors_moebius_C]
  calc ∑ n ∈ S.filter (fun n => n.Coprime q), f n
      = ∑ n ∈ S, f n * (if n.Coprime q then 1 else 0) := by
        rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun n _ => ?_; split_ifs <;> simp
    _ = ∑ n ∈ S, ∑ d ∈ q.divisors, if d ∣ n then (moebius d : ℂ) * f n else 0 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [key n, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        split_ifs <;> ring
    _ = ∑ d ∈ q.divisors, ∑ n ∈ S, if d ∣ n then (moebius d : ℂ) * f n else 0 := Finset.sum_comm
    _ = ∑ d ∈ q.divisors, (moebius d : ℂ) * ∑ n ∈ S.filter (fun n => d ∣ n), f n := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        split_ifs <;> simp

/-- **The geometric sum**: `Σ_{b<M}e(bn/M) = M` if `M | n` and `0` otherwise. -/
lemma sum_range_exp {M : ℕ} (hM : 0 < M) (n : ℕ) :
    ∑ b ∈ Finset.range M, Complex.exp (2 * π * I * ((b * n : ℕ) : ℂ) / M) = if M ∣ n then (M : ℂ) else 0 := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h2 : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : ∀ b : ℕ, Complex.exp (2 * π * I * ((b * n : ℕ) : ℂ) / M) = Complex.exp (2 * π * I * n / M) ^ b := by
    intro b
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  simp only [e]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    have h1 : Complex.exp (2 * π * I * ((M * k : ℕ) : ℂ) / M) = 1 := by
      have e2 : 2 * π * I * ((M * k : ℕ) : ℂ) / M = (k : ℂ) * (2 * π * I) := by push_cast; field_simp
      rw [e2, Complex.exp_nat_mul_two_pi_mul_I]
    rw [h1]; simp
  · have hne : Complex.exp (2 * π * I * n / M) ≠ 1 := by
      intro h1
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h1
      apply h
      have h3 : (n : ℂ) = (k : ℂ) * M := by
        calc (n : ℂ) = (2 * π * I * n / M) * M / (2 * π * I) := by field_simp
          _ = (k * (2 * π * I)) * M / (2 * π * I) := by rw [hk]
          _ = (k : ℂ) * M := by field_simp
      have h4 : (n : ℤ) = k * M := by exact_mod_cast h3
      exact Int.natCast_dvd_natCast.1 ⟨k, by rw [h4]; ring⟩
    rw [geom_sum_eq hne, ← Complex.exp_nat_mul]
    have e3 : (M : ℂ) * (2 * π * I * n / M) = (n : ℂ) * (2 * π * I) := by field_simp
    rw [e3, Complex.exp_nat_mul_two_pi_mul_I]; simp

/-- **The multiples of `d | q` below `q`**: `Σ_{a<q, d|a}e(an/q) = (q/d)[q/d | n]`. -/
lemma sum_multiples_exp {q d : ℕ} (hq : q ≠ 0) (hd : d ∣ q) (n : ℕ) :
    ∑ a ∈ (Finset.range q).filter (fun a => d ∣ a), Complex.exp (2 * π * I * ((a * n : ℕ) : ℂ) / q) =
      if q / d ∣ n then ((q / d : ℕ) : ℂ) else 0 := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hq)
  obtain ⟨M, rfl⟩ := hd
  have hM : 0 < M := Nat.pos_of_ne_zero fun h => hq (by rw [h, mul_zero])
  have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hM0' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [Nat.mul_div_cancel_left M hd0, ← sum_range_exp hM n]
  refine Finset.sum_nbij' (fun a => a / d) (fun b => d * b) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact Nat.div_lt_of_lt_mul ha.1
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨Nat.mul_lt_mul_of_pos_left hb hd0, dvd_mul_right d b⟩
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact Nat.mul_div_cancel' ha.2
  · intro b _
    exact Nat.mul_div_cancel_left b hd0
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨c, rfl⟩ := ha.2
    rw [Nat.mul_div_cancel_left c hd0]
    congr 1
    push_cast
    field_simp

/-- `C_q(n)` as a sum over `0 ≤ a < q` coprime to `q`. -/
lemma Cq_eq_range (q : ℕ) [NeZero q] (n : ZMod q) :
    Cq q n = ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      Complex.exp (2 * π * I * ((a * n.val : ℕ) : ℂ) / q) := by
  classical
  have hψ : ∀ a : ℕ, ZMod.stdAddChar ((a : ZMod q) * n) =
      Complex.exp (2 * π * I * ((a * n.val : ℕ) : ℂ) / q) := by
    intro a
    have h := ZMod.stdAddChar_coe (N := q) ((a * n.val : ℕ) : ℤ)
    rw [Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val] at h
    rw [h]; push_cast; ring_nf
  unfold Cq
  calc ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * n)
      = ∑ u : (ZMod q)ˣ, (fun x : ZMod q => if IsUnit x then ZMod.stdAddChar (x * n) else 0) u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        show _ = if IsUnit (u : ZMod q) then _ else _
        simp [u.isUnit]
    _ = ∑ x : ZMod q, (if IsUnit x then ZMod.stdAddChar (x * n) else 0) :=
        (sum_eq_sum_units (fun x : ZMod q => if IsUnit x then ZMod.stdAddChar (x * n) else 0)
          fun x hx => by simp [hx]).symm
    _ = ∑ a ∈ Finset.range q, (if IsUnit (a : ZMod q) then ZMod.stdAddChar ((a : ZMod q) * n) else 0) := by
        symm
        exact Finset.sum_nbij' (fun a : ℕ => (a : ZMod q)) ZMod.val (fun _ _ => Finset.mem_univ _)
          (fun x _ => Finset.mem_range.2 (ZMod.val_lt x)) (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha))
          (fun x _ => ZMod.natCast_zmod_val x) (fun _ _ => rfl)
    _ = _ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hψ a]
        simp only [ZMod.isUnit_iff_coprime]

/-- **The Ramanujan sum by Möbius**: `C_q(n) = Σ_{d|q}μ(d)(q/d)[q/d | n]`. -/
lemma Cq_eq_moebius (q : ℕ) [NeZero q] (n : ZMod q) :
    Cq q n = ∑ d ∈ q.divisors, (moebius d : ℂ) * if q / d ∣ n.val then ((q / d : ℕ) : ℂ) else 0 := by
  rw [Cq_eq_range, sum_coprime_eq_C (NeZero.ne q)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [sum_multiples_exp (NeZero.ne q) (Nat.dvd_of_mem_divisors hd)]

/-- **The Ramanujan sum's bound**: `|C_q(n)| ≤ d(q)(n, q)`. -/
theorem norm_Cq_le (q : ℕ) [NeZero q] (n : ZMod q) :
    ‖Cq q n‖ ≤ (q.divisors.card : ℝ) * (Nat.gcd n.val q : ℝ) := by
  rw [Cq_eq_moebius]
  have hg : 0 < Nat.gcd n.val q := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne q))
  calc ‖∑ d ∈ q.divisors, (moebius d : ℂ) * (if q / d ∣ n.val then ((q / d : ℕ) : ℂ) else 0)‖
      ≤ ∑ d ∈ q.divisors, ‖(moebius d : ℂ) * (if q / d ∣ n.val then ((q / d : ℕ) : ℂ) else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ q.divisors, (Nat.gcd n.val q : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [norm_mul]
        have hμ : ‖(moebius d : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hb : ‖(if q / d ∣ n.val then ((q / d : ℕ) : ℂ) else 0)‖ ≤ Nat.gcd n.val q := by
          split_ifs with h
          · rw [Complex.norm_natCast]
            exact_mod_cast Nat.le_of_dvd hg (Nat.dvd_gcd h (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
          · simp
        calc ‖(moebius d : ℂ)‖ * ‖(if q / d ∣ n.val then ((q / d : ℕ) : ℂ) else 0)‖
            ≤ 1 * (Nat.gcd n.val q : ℝ) := mul_le_mul hμ hb (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = (q.divisors.card : ℝ) * (Nat.gcd n.val q : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The kernel `J` -/

/-- `G(a, b, c) = c²w(a)²w(b)²w(c)²`, so that `g_v(u) = G(v₁u, v₂u, u)`. -/
def Gk (p : ℝ × ℝ × ℝ) : ℂ := ((p.2.2 ^ 2 * wCGL p.1 ^ 2 * wCGL p.2.1 ^ 2 * wCGL p.2.2 ^ 2 : ℝ) : ℂ)

lemma contDiff_Gk : ContDiff ℝ ∞ Gk := by
  have hw := wCGL_contDiff
  have h : ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ => p.2.2 ^ 2 * wCGL p.1 ^ 2 * wCGL p.2.1 ^ 2 * wCGL p.2.2 ^ 2 := by
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp h

lemma Gk_ne_zero {p : ℝ × ℝ × ℝ} (h : Gk p ≠ 0) : p ∈ Icc (1 : ℝ) 2 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2) := by
  have hw : ∀ x, wCGL x ≠ 0 → x ∈ Icc (1 : ℝ) 2 := fun x hx => by
    obtain ⟨h1, h2⟩ := one_lt_of_wCGL_ne hx; exact ⟨h1.le, h2.le⟩
  have h1 : wCGL p.1 ≠ 0 := fun h0 => h (by simp [Gk, h0])
  have h2 : wCGL p.2.1 ≠ 0 := fun h0 => h (by simp [Gk, h0])
  have h3 : wCGL p.2.2 ≠ 0 := fun h0 => h (by simp [Gk, h0])
  exact ⟨hw _ h1, hw _ h2, hw _ h3⟩

lemma hasCompactSupport_Gk : HasCompactSupport Gk :=
  HasCompactSupport.intro ((isCompact_Icc (a := (1 : ℝ)) (b := 2)).prod
    ((isCompact_Icc (a := (1 : ℝ)) (b := 2)).prod (isCompact_Icc (a := (1 : ℝ)) (b := 2)))) fun p hp => by
      by_contra h; exact hp (Gk_ne_zero h)

lemma exists_bound_Gk (K : ℕ) : ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ K Gk p‖ ≤ C :=
  (contDiff_Gk.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
    (hasCompactSupport_Gk.iteratedFDeriv K)

/-- `u ↦ (v₁u, v₂u, u)`. -/
def Lv (v₁ v₂ : ℝ) : ℝ →L[ℝ] ℝ × ℝ × ℝ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((v₁, v₂, 1) : ℝ × ℝ × ℝ)

lemma Lv_apply (v₁ v₂ u : ℝ) : Lv v₁ v₂ u = (u * v₁, u * v₂, u) := by
  simp [Lv]

lemma norm_Lv_le {v₁ v₂ : ℝ} (h1 : |v₁| ≤ 2) (h2 : |v₂| ≤ 2) : ‖Lv v₁ v₂‖ ≤ 2 := by
  unfold Lv
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
  simp only [Prod.norm_def, Real.norm_eq_abs, abs_one]
  exact max_le h1 (max_le h2 (by norm_num))

lemma gv_eq_comp (v₁ v₂ : ℝ) : (fun u : ℝ => ((gv v₁ v₂ u : ℝ) : ℂ)) = Gk ∘ Lv v₁ v₂ := by
  funext u
  simp only [Function.comp_apply, Lv_apply, Gk, gv]
  rw [mul_comm u v₁, mul_comm u v₂]

/-- The derivatives of `g_v` vanish off `[1, 2]`. -/
lemma iteratedDeriv_gv_eq_zero (v₁ v₂ : ℝ) (n : ℕ) {u : ℝ} (hu : u ∉ Icc (1 : ℝ) 2) :
    iteratedDeriv n (fun u : ℝ => ((gv v₁ v₂ u : ℝ) : ℂ)) u = 0 := by
  have hs : Function.support (fun u : ℝ => ((gv v₁ v₂ u : ℝ) : ℂ)) ⊆ Icc (1 : ℝ) 2 := by
    intro x hx
    rw [gv_eq_comp] at hx
    have h := (Gk_ne_zero hx).2.2
    rwa [Lv_apply] at h
  have ht : tsupport (fun u : ℝ => ((gv v₁ v₂ u : ℝ) : ℂ)) ⊆ Icc (1 : ℝ) 2 := closure_minimal hs isClosed_Icc
  have h0 : iteratedFDeriv ℝ n (fun u : ℝ => ((gv v₁ v₂ u : ℝ) : ℂ)) u = 0 := by
    by_contra h
    exact hu (ht (support_iteratedFDeriv_subset n h))
  rw [iteratedDeriv_eq_iteratedFDeriv, h0]
  rfl

/-- **The decay of `J`**, uniformly for `|v₁|, |v₂| ≤ 2`: for every `K` there is `C` with
`(2π|λ|)^K|J(v₁, v₂, λ)| ≤ C`. -/
theorem Jk_decay (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v₁ v₂ lam : ℝ, |v₁| ≤ 2 → |v₂| ≤ 2 →
    (2 * π * |lam|) ^ K * ‖Jk v₁ v₂ lam‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_Gk K
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C * 2 ^ K, by positivity, fun v₁ v₂ lam h1 h2 => ?_⟩
  set g : ℝ → ℂ := fun u => ((gv v₁ v₂ u : ℝ) : ℂ) with hg
  have hgd : ContDiff ℝ ∞ g := by rw [hg, gv_eq_comp]; exact contDiff_Gk.comp (Lv v₁ v₂).contDiff
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n g) := fun n =>
    (hgd.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (K := Icc (1 : ℝ) 2) isCompact_Icc fun u hu => iteratedDeriv_gv_eq_zero v₁ v₂ n hu)
  have hbd : ∀ u, ‖iteratedDeriv K g u‖ ≤ C * 2 ^ K := by
    intro u
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hg, gv_eq_comp,
      (Lv v₁ v₂).iteratedFDeriv_comp_right contDiff_Gk u (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul (hC _) (pow_le_pow_left₀ (norm_nonneg _) (norm_Lv_le h1 h2) K) (by positivity) hC0
  have hJ : Jk v₁ v₂ lam = 𝓕 g lam := (LinnikCGLProd.fourier_eq g lam).symm
  rw [hJ]
  refine (SieveSmooth.pow_mul_norm_fourier_le (hgd.of_le (by exact_mod_cast le_top)) (fun n _ => hint n) lam).trans ?_
  have e : ∫ x in Icc (1 : ℝ) 2, ‖iteratedDeriv K g x‖ = ∫ x, ‖iteratedDeriv K g x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hg, iteratedDeriv_gv_eq_zero v₁ v₂ K hx, norm_zero]
  rw [← e]
  calc ∫ x in Icc (1 : ℝ) 2, ‖iteratedDeriv K g x‖ ≤ ∫ _ in Icc (1 : ℝ) 2, C * 2 ^ K :=
        setIntegral_mono_on ((hgd.continuous_iteratedDeriv K (by exact_mod_cast le_top)).norm.integrableOn_Icc)
          (integrableOn_const (by simp)) measurableSet_Icc fun x _ => hbd x
    _ = C * 2 ^ K := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]; ring

/-- `J(v₁, v₂, λ) = 0` unless `v₁, v₂ ∈ (1/2, 2)`. -/
lemma Jk_eq_zero_of {v₁ v₂ : ℝ} (h : v₁ ∉ Ioo (1 / 2 : ℝ) 2 ∨ v₂ ∉ Ioo (1 / 2 : ℝ) 2) (lam : ℝ) :
    Jk v₁ v₂ lam = 0 := by
  have hg : ∀ u, gv v₁ v₂ u = 0 := by
    intro u
    unfold gv
    by_cases hu : wCGL u = 0
    · rw [hu]; ring
    obtain ⟨hu1, hu2⟩ := one_lt_of_wCGL_ne hu
    have key : ∀ v : ℝ, v ∉ Ioo (1 / 2 : ℝ) 2 → wCGL (v * u) = 0 := by
      intro v hv
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hv
      refine wCGL_zero ?_
      rcases hv with hv | hv
      · left; nlinarith
      · right; nlinarith
    rcases h with h | h
    · rw [key v₁ h]; ring
    · rw [key v₂ h]; ring
  unfold Jk
  simp [hg]

end LinnikCGLRam

#print axioms LinnikCGLRam.norm_Cq_le
#print axioms LinnikCGLRam.Jk_decay
#print axioms LinnikCGLRam.Jk_eq_zero_of
