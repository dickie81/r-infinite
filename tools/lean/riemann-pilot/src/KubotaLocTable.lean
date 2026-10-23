import KubotaSmFactor

/-! # The local sums `G_k(δ₃hp^e)` (round 452)

S5f-13 of round 360's plan, part 3. Round 451 factored round 428's sums `S_m(p^k c′)` at a primary prime `p`
through the local sum `G_k(m) = Σ_{f mod p^k, p ∤ f} (f/p)₃^k·ĕ((m/9)·(3f/p^k))`. This round computes
`G_k(δ₃hp^e)` for `k ≥ 1`, a primary prime `p` and `p ∤ h`:

* **Sums over `ℤ[ω]/N`** (`tsum_quot_affine'`, `tsum_quot_eq_zero_of_mul`, `tsum_quot_eq_zero_of_add` and
  `tsum_quot_dvd_fiber`): affine changes of variables, the vanishing of a sum that a change of variables
  multiplies by `l ≠ 1`, and the sum modulo `N` of a function periodic modulo `M ∣ N`.
* **The Gauss sums modulo `p`** (`gTerm` and `gaussP`, definitions; `ebr_gTerm`, `gTerm_add` and
  **`gaussP_three`**): `γ_j(h) = Σ_{f mod p} (f/p)₃^j·ĕ((δ₃h/9)·(3f/p))`, and `γ_j(h) = −1` for `3 ∣ j`,
  `j ≥ 1`.
* **The table** (`locTerm_low`, **`locG_low`**, `locTerm_mid`, **`locG_mid`**, `locG_mid_three` and
  **`locG_high`**): for `1 ≤ k ≤ e`, `G_k = N(p)^{k−1}(N(p) − 1)` when `3 ∣ k` and `0` otherwise; for
  `k = e + 1`, `G_k = N(p)^e·γ_{e+1}(h)`, which is `−N(p)^e` when `3 ∣ e + 1`; and `G_k = 0` for `k ≥ e + 2`.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### Sums over `ℤ[ω]/N` -/

/-- **An affine change of variables on `ℤ[ω]/N`** (round 445's `tsum_quot_affine` for any modulus): for `F`
periodic modulo `N` and `u` prime to `N`, `Σ_q F(a + u·q) = Σ_q F(q)`. -/
theorem tsum_quot_affine' {N u : 𝓞 K} (hN : N ≠ 0) (hu : IsCoprime u N) {F : 𝓞 K → ℂ}
    (hF : ∀ y y', N ∣ y - y' → F y = F y') (a : 𝓞 K) :
    ∑' q : 𝓞 K ⧸ span {N}, F (a + u * repQ N q) = ∑' q : 𝓞 K ⧸ span {N}, F (repQ N q) := by
  have := finite_quot N hN
  have := Fintype.ofFinite (𝓞 K ⧸ span {N})
  rw [tsum_fintype, tsum_fintype]
  set e : 𝓞 K ⧸ span {N} → 𝓞 K ⧸ span {N} :=
    fun q => Ideal.Quotient.mk (span {N}) (a + u * repQ N q) with he
  have hinj : Function.Injective e := by
    intro q q' h
    rw [he, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have h' : N ∣ u * (repQ N q - repQ N q') := by
      have : a + u * repQ N q - (a + u * repQ N q') = u * (repQ N q - repQ N q') := by ring
      rwa [this] at h
    have h'' := hu.symm.dvd_of_dvd_mul_left h'
    rw [← repQ_mk N q, ← repQ_mk N q', Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h''
  refine Fintype.sum_bijective e (Finite.injective_iff_bijective.1 hinj) _ _ fun q => ?_
  exact hF _ _ (by
    have := dvd_repQ_sub N (a + u * repQ N q)
    rw [← dvd_neg, neg_sub] at this
    exact this)

/-- **A sum that a dilation multiplies by `l ≠ 1` vanishes**: for `F` periodic modulo `N`, `g` prime to `N`
and `F(gy) = l·F(y)` for every `y`, `Σ_{q mod N} F(q) = 0`. -/
theorem tsum_quot_eq_zero_of_mul {N g : 𝓞 K} (hN : N ≠ 0) (hg : IsCoprime g N) {F : 𝓞 K → ℂ}
    (hF : ∀ y y', N ∣ y - y' → F y = F y') {l : ℂ} (hl : l ≠ 1) (hmul : ∀ y, F (g * y) = l * F y) :
    ∑' q : 𝓞 K ⧸ span {N}, F (repQ N q) = 0 := by
  have h := tsum_quot_affine' hN hg hF 0
  simp only [zero_add, hmul] at h
  rw [tsum_mul_left] at h
  have : (l - 1) * ∑' q : 𝓞 K ⧸ span {N}, F (repQ N q) = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl)

/-- **A sum that a translation multiplies by `l ≠ 1` vanishes**: for `F` periodic modulo `N` and
`F(y + t) = l·F(y)` for every `y`, `Σ_{q mod N} F(q) = 0`. -/
theorem tsum_quot_eq_zero_of_add {N : 𝓞 K} (hN : N ≠ 0) {F : 𝓞 K → ℂ}
    (hF : ∀ y y', N ∣ y - y' → F y = F y') (t : 𝓞 K) {l : ℂ} (hl : l ≠ 1) (hadd : ∀ y, F (y + t) = l * F y) :
    ∑' q : 𝓞 K ⧸ span {N}, F (repQ N q) = 0 := by
  have h := tsum_quot_affine' hN isCoprime_one_left hF t
  simp only [one_mul, add_comm t, hadd] at h
  rw [tsum_mul_left] at h
  have : (l - 1) * ∑' q : 𝓞 K ⧸ span {N}, F (repQ N q) = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl)

open Classical in
/-- **A sum modulo `N` of a function periodic modulo `M ∣ N`**:
`N(M)·Σ_{q mod N} F(q) = N(N)·Σ_{q mod M} F(q)`, with `N(·)` the norm (round 414's `card_fiber_mul` for
the fibres of `ℤ[ω]/N → ℤ[ω]/M`). -/
theorem tsum_quot_dvd_fiber {M N : 𝓞 K} (hM : M ≠ 0) (hN : N ≠ 0) (hMN : M ∣ N) {F : 𝓞 K → ℂ}
    (hF : ∀ y y', M ∣ y - y' → F y = F y') :
    (absNorm (span {M}) : ℂ) * ∑' q : 𝓞 K ⧸ span {N}, F (repQ N q) =
      (absNorm (span {N}) : ℂ) * ∑' q : 𝓞 K ⧸ span {M}, F (repQ M q) := by
  have := finite_quot N hN
  have := Fintype.ofFinite (𝓞 K ⧸ span {N})
  have := finite_quot M hM
  have := Fintype.ofFinite (𝓞 K ⧸ span {M})
  have hle : span {N} ≤ span {M} := span_singleton_le_span_singleton.2 hMN
  set φ := Ideal.Quotient.factor hle with hφ
  have hsurj : Function.Surjective φ := Ideal.Quotient.factor_surjective hle
  have hval : ∀ q, F (repQ N q) = F (repQ M (φ q)) := by
    intro q
    refine hF _ _ ?_
    have h1 : φ q = Ideal.Quotient.mk (span {M}) (repQ N q) := by
      rw [hφ, ← Ideal.Quotient.factor_mk hle (repQ N q), repQ_mk]
    have h2 := dvd_repQ_sub M (repQ N q)
    rw [← h1] at h2
    rw [← dvd_neg, neg_sub]
    exact h2
  have hfib : ∀ r : 𝓞 K ⧸ span {M}, ((Finset.univ.filter fun q => φ q = r).card : ℂ) *
      (absNorm (span {M}) : ℂ) = (absNorm (span {N}) : ℂ) := by
    intro r
    have h := card_fiber_mul φ.toAddMonoidHom hsurj r
    rw [card_quot, card_quot] at h
    exact_mod_cast h
  rw [tsum_fintype, tsum_fintype]
  simp_rw [hval]
  rw [← Finset.sum_fiberwise' Finset.univ φ (fun r => F (repQ M r)), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← hfib r]
  ring

/-! ### The Gauss sums modulo `p` -/

/-- The summand of the Gauss sum modulo `p`: `(f/p)₃^j·ĕ((δ₃h/9)·(3f/p))`. -/
def gTerm (h p : 𝓞 K) (j : ℕ) (f : 𝓞 K) : ℂ :=
  σO (cub f (span {p})) ^ j * ebr (σO (δ3 * h) / 9 * (σO (3 * f) / σO p))

/-- **The Gauss sum modulo `p`**: `γ_j(h) = Σ_{f mod p} (f/p)₃^j·ĕ((δ₃h/9)·(3f/p))`. For a prime `p` and
`j ≥ 1` the class of `0` contributes `0`, since `(0/p)₃ = 0`. -/
def gaussP (h p : 𝓞 K) (j : ℕ) : ℂ := ∑' f : 𝓞 K ⧸ span {p}, gTerm h p j (repQ p f)

/-- The phase of `gTerm` is the additive character `ψ_p(−fh)` (round 363's `ebr_shift`). -/
theorem ebr_gTerm (h p f : 𝓞 K) : ebr (σO (δ3 * h) / 9 * (σO (3 * f) / σO p)) = ψc p (-f * h) := by
  rw [← ebr_shift p (-f) h]
  congr 1
  rw [show (δ3 ^ 2 * -f) = 3 * f by rw [δ3_sq]; ring]
  ring

/-- `gTerm` is periodic modulo `p`. -/
theorem gTerm_add (h : 𝓞 K) {p : 𝓞 K} (hp : p ≠ 0) (j : ℕ) (f u : 𝓞 K) :
    gTerm h p j (f + p * u) = gTerm h p j f := by
  unfold gTerm
  rw [cub_congr (show p ∣ f + p * u - f by rw [add_sub_cancel_left]; exact dvd_mul_right p u)]
  congr 1
  have hσ : σO p ≠ 0 := σO_ne_zero hp
  have e : σO (δ3 * h) / 9 * (σO (3 * (f + p * u)) / σO p) =
      σO (δ3 * h) / 9 * (σO (3 * f) / σO p) + σO (δ3 * h) * σO (3 * u) / 9 := by
    simp only [map_add, map_mul]; field_simp
  rw [e, ebr_add, ebr_period, mul_one]

/-- **`γ_j(h) = −1` for `3 ∣ j`, `j ≥ 1` and `p ∤ h`**: `(f/p)₃^j` is `1` for `p ∤ f` and `0` for `p ∣ f`, and
the additive character sums to `0` over `ℤ[ω]/p` (round 363's `sum_ψc_mul`). -/
theorem gaussP_three {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {h : 𝓞 K} (hph : ¬ p ∣ h) {j : ℕ}
    (hj : 0 < j) (h3 : 3 ∣ j) : gaussP h p j = -1 := by
  classical
  have hp0 := hp.ne_zero
  have := finite_quot p hp0
  have := Fintype.ofFinite (𝓞 K ⧸ span {p})
  have hsym : ∀ f : 𝓞 K ⧸ span {p}, σO (cub (repQ p f) (span {p})) ^ j = if f = 0 then 0 else 1 := by
    intro f
    by_cases hf : f = 0
    · have hd : p ∣ repQ p f := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, repQ_mk, hf]
      rw [ite_eq_left hf, cub_span_eq_zero hp hd, map_zero, zero_pow hj.ne']
    · have hnd : ¬ p ∣ repQ p f := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, repQ_mk]; exact hf
      obtain ⟨i, rfl⟩ := h3
      rw [ite_eq_right hf, ← map_pow, pow_mul, cub_pow_three hpp (isCoprime_of_not_dvd hp hnd), one_pow,
        map_one]
  have hψ := sum_ψc_mul p hp0 (-h)
  have hnz : ¬ Ideal.Quotient.mk (span {p}) (-h) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, dvd_neg]; exact hph
  rw [ite_eq_right hnz] at hψ
  have h0 : ψc p (repQ p 0 * -h) = 1 := by
    have hd : p ∣ repQ p 0 := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, repQ_mk]
    obtain ⟨u, hu⟩ := hd
    rw [hu, mul_assoc, ψc_mul_self p hp0]
  unfold gaussP gTerm
  rw [tsum_fintype]
  simp_rw [hsym, ebr_gTerm]
  have e : ∀ f : 𝓞 K ⧸ span {p}, (if f = 0 then (0 : ℂ) else 1) * ψc p (-repQ p f * h) =
      ψc p (repQ p f * -h) - if f = 0 then 1 else 0 := by
    intro f
    rw [show -repQ p f * h = repQ p f * -h by ring]
    by_cases hf : f = 0
    · rw [ite_eq_left hf, ite_eq_left hf, hf, h0]; ring
    · rw [ite_eq_right hf, ite_eq_right hf]; ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, hψ, Finset.sum_ite_eq' Finset.univ (0 : 𝓞 K ⧸ span {p}),
    ite_eq_left (Finset.mem_univ _)]
  ring

/-! ### The table of `G_k(δ₃hp^e)` -/

/-- **For `1 ≤ k ≤ e` the phase is `1`** (round 428's `ebr_period`), and the local summand is `(f/p)₃^k`,
which is `0` for `p ∣ f`. -/
theorem locTerm_low {p : 𝓞 K} (hp : Prime p) (h : 𝓞 K) {e k : ℕ} (hk : 0 < k) (hke : k ≤ e) (f : 𝓞 K) :
    locTerm (δ3 * (h * p ^ e)) p k f = σO (cub f (span {p})) ^ k := by
  classical
  unfold locTerm
  by_cases hf : p ∣ f
  · rw [ite_eq_left hf, cub_span_eq_zero hp hf, map_zero, zero_pow hk.ne']
  · rw [ite_eq_right hf]
    have hσ : σO (p ^ k) ≠ 0 := σO_ne_zero (pow_ne_zero k hp.ne_zero)
    have e1 : σO (δ3 * (h * p ^ e)) / 9 * (σO (3 * f) / σO (p ^ k)) =
        σO (δ3 * (h * p ^ (e - k))) * σO (3 * f) / 9 := by
      have hpe : p ^ e = p ^ (e - k) * p ^ k := by rw [← pow_add, Nat.sub_add_cancel hke]
      rw [hpe]; simp only [map_mul]; field_simp
    rw [e1, ebr_period, mul_one]

/-- **`G_k(δ₃hp^e)` for `1 ≤ k ≤ e`**: `N(p)^{k−1}(N(p) − 1)` when `3 ∣ k`, and `0` otherwise. The summand is
periodic modulo `p`; modulo `p` it is `1` off `0` when `3 ∣ k`, and otherwise multiplying by a `g` with
`(g/p)₃ ≠ 1` (round 445's `exists_cub_ne_one`) multiplies the sum by `(g/p)₃^k ≠ 1`. -/
theorem locG_low {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) (h : 𝓞 K) {e k : ℕ} (hk : 0 < k) (hke : k ≤ e) :
    locG (δ3 * (h * p ^ e)) p k =
      if 3 ∣ k then (absNorm (span {p}) : ℂ) ^ (k - 1) * ((absNorm (span {p}) : ℂ) - 1) else 0 := by
  classical
  have hp0 := hp.ne_zero
  have := finite_quot p hp0
  have := Fintype.ofFinite (𝓞 K ⧸ span {p})
  have hF : ∀ y y', p ∣ y - y' → σO (cub y (span {p})) ^ k = σO (cub y' (span {p})) ^ k :=
    fun y y' hyy => by rw [cub_congr hyy]
  have hfib := tsum_quot_dvd_fiber hp0 (pow_ne_zero k hp0) (dvd_pow_self p hk.ne') hF
  have hNk : (absNorm (span {p ^ k}) : ℂ) = (absNorm (span {p}) : ℂ) ^ k := by
    rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  have hS : ∑' q : 𝓞 K ⧸ span {p}, σO (cub (repQ p q) (span {p})) ^ k =
      if 3 ∣ k then (absNorm (span {p}) : ℂ) - 1 else 0 := by
    split_ifs with h3
    · have hsym : ∀ q : 𝓞 K ⧸ span {p}, σO (cub (repQ p q) (span {p})) ^ k = 1 - if q = 0 then 1 else 0 := by
        intro q
        by_cases hq : q = 0
        · have hd : p ∣ repQ p q := by
            rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, repQ_mk, hq]
          rw [ite_eq_left hq, cub_span_eq_zero hp hd, map_zero, zero_pow hk.ne', sub_self]
        · have hnd : ¬ p ∣ repQ p q := by
            rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, repQ_mk]; exact hq
          obtain ⟨i, rfl⟩ := h3
          rw [ite_eq_right hq, ← map_pow, pow_mul, cub_pow_three hpp (isCoprime_of_not_dvd hp hnd), one_pow,
            map_one, sub_zero]
      rw [tsum_fintype]
      simp_rw [hsym]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_quot, nsmul_eq_mul, mul_one,
        Finset.sum_ite_eq' Finset.univ (0 : 𝓞 K ⧸ span {p}), ite_eq_left (Finset.mem_univ _)]
    · obtain ⟨g, hg, hg1⟩ := exists_cub_ne_one hp hpp
      refine tsum_quot_eq_zero_of_mul hp0 hg hF (l := σO (cub g (span {p})) ^ k) ?_ fun y => ?_
      · rw [← map_pow]; exact σO_pow_ne_one (cub_pow_three hpp hg) hg1 h3
      · rw [cub_mul_left, map_mul, mul_pow]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  unfold locG
  simp_rw [locTerm_low hp h hk hke]
  rw [hNk, hS] at hfib
  rw [Nat.add_sub_cancel]
  apply mul_left_cancel₀ (absNorm_span_ne_zero hp0)
  rw [hfib]
  split_ifs <;> ring

/-- **For `k = e + 1` the local summand is the summand of the Gauss sum modulo `p`**:
`(f/p)₃^{e+1}·ĕ((δ₃h/9)·(3f/p))`, both `0` for `p ∣ f`. -/
theorem locTerm_mid {p : 𝓞 K} (hp : Prime p) (h : 𝓞 K) (e : ℕ) (f : 𝓞 K) :
    locTerm (δ3 * (h * p ^ e)) p (e + 1) f = gTerm h p (e + 1) f := by
  classical
  unfold locTerm gTerm
  by_cases hf : p ∣ f
  · rw [ite_eq_left hf, cub_span_eq_zero hp hf, map_zero, zero_pow (Nat.succ_ne_zero e), zero_mul]
  · rw [ite_eq_right hf]
    have hσ : σO p ≠ 0 := σO_ne_zero hp.ne_zero
    have e1 : σO (δ3 * (h * p ^ e)) / 9 * (σO (3 * f) / σO (p ^ (e + 1))) =
        σO (δ3 * h) / 9 * (σO (3 * f) / σO p) := by
      simp only [map_mul, map_pow]; field_simp; ring
    rw [e1]

/-- **`G_{e+1}(δ₃hp^e) = N(p)^e·γ_{e+1}(h)`**: the summand is periodic modulo `p`, and each class modulo `p`
has `N(p)^e` classes modulo `p^{e+1}` over it. -/
theorem locG_mid {p : 𝓞 K} (hp : Prime p) (h : 𝓞 K) (e : ℕ) :
    locG (δ3 * (h * p ^ e)) p (e + 1) = (absNorm (span {p}) : ℂ) ^ e * gaussP h p (e + 1) := by
  have hp0 := hp.ne_zero
  have hF : ∀ y y', p ∣ y - y' → gTerm h p (e + 1) y = gTerm h p (e + 1) y' := by
    intro y y' hyy
    obtain ⟨u, hu⟩ := hyy
    rw [show y = y' + p * u by rw [← hu]; ring, gTerm_add h hp0]
  have hfib := tsum_quot_dvd_fiber hp0 (pow_ne_zero (e + 1) hp0) (dvd_pow_self p (Nat.succ_ne_zero e)) hF
  have hNk : (absNorm (span {p ^ (e + 1)}) : ℂ) = (absNorm (span {p}) : ℂ) ^ (e + 1) := by
    rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow]
  unfold locG gaussP
  simp_rw [locTerm_mid hp h e]
  rw [hNk] at hfib
  apply mul_left_cancel₀ (absNorm_span_ne_zero hp0)
  rw [hfib]; ring

/-- **`G_{e+1}(δ₃hp^e) = −N(p)^e` when `3 ∣ e + 1`** and `p ∤ h`. -/
theorem locG_mid_three {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {h : 𝓞 K} (hph : ¬ p ∣ h) {e : ℕ}
    (h3 : 3 ∣ e + 1) : locG (δ3 * (h * p ^ e)) p (e + 1) = -(absNorm (span {p}) : ℂ) ^ e := by
  rw [locG_mid hp h e, gaussP_three hp hpp hph (Nat.succ_pos e) h3, mul_neg_one]

/-- **`G_k(δ₃hp^e) = 0` for `k ≥ e + 2` and `p ∤ h`**: translating `f` by `p^{k−e−1}t` keeps the symbol and
multiplies the phase by `ψ_p(−th)`, which is not `1` for some `t` (round 363's `dvd_of_ψc_mul_eq_one`). -/
theorem locG_high {p : 𝓞 K} (hp : Prime p) {h : 𝓞 K} (hph : ¬ p ∣ h) {e k : ℕ} (hk : e + 2 ≤ k) :
    locG (δ3 * (h * p ^ e)) p k = 0 := by
  classical
  have hp0 := hp.ne_zero
  have hk0 : 0 < k := by omega
  have hσ : σO p ≠ 0 := σO_ne_zero hp0
  obtain ⟨t, ht⟩ : ∃ t, ψc p (-t * h) ≠ 1 := by
    by_contra hall
    push Not at hall
    have hd := dvd_of_ψc_mul_eq_one p (-h) hp0 fun x => by rw [show -h * x = -x * h by ring]; exact hall x
    exact hph (by rwa [dvd_neg] at hd)
  obtain ⟨j, hj⟩ : ∃ j, k = e + 1 + (j + 1) := ⟨k - e - 2, by omega⟩
  unfold locG
  refine tsum_quot_eq_zero_of_add (pow_ne_zero k hp0) (fun y y' hyy => ?_) (p ^ (j + 1) * t) ht fun y => ?_
  · obtain ⟨u, hu⟩ := hyy
    rw [show y = y' + p ^ k * u by rw [← hu]; ring, locTerm_add (h * p ^ e) p hp0 hk0]
  · unfold locTerm
    have hpt : p ∣ p ^ (j + 1) * t := dvd_mul_of_dvd_left (dvd_pow_self p j.succ_ne_zero) t
    by_cases hy : p ∣ y
    · rw [ite_eq_left ((dvd_add_right hy).2 hpt), ite_eq_left hy, mul_zero]
    · rw [ite_eq_right (fun h' => hy ((dvd_add_left hpt).1 h')), ite_eq_right hy,
        cub_congr (show p ∣ y + p ^ (j + 1) * t - y by rw [add_sub_cancel_left]; exact hpt)]
      have e1 : σO (δ3 * (h * p ^ e)) / 9 * (σO (3 * (y + p ^ (j + 1) * t)) / σO (p ^ k)) =
          σO (δ3 * (h * p ^ e)) / 9 * (σO (3 * y) / σO (p ^ k)) + σO (δ3 * h) / 9 * (σO (3 * t) / σO p) := by
        rw [hj]; simp only [map_add, map_mul, map_pow]; field_simp; ring
      rw [e1, ebr_add, ebr_gTerm h p t]; ring

end Eis

end

#print axioms Eis.tsum_quot_affine'
#print axioms Eis.tsum_quot_eq_zero_of_mul
#print axioms Eis.tsum_quot_eq_zero_of_add
#print axioms Eis.tsum_quot_dvd_fiber
#print axioms Eis.ebr_gTerm
#print axioms Eis.gTerm_add
#print axioms Eis.gaussP_three
#print axioms Eis.locTerm_low
#print axioms Eis.locG_low
#print axioms Eis.locTerm_mid
#print axioms Eis.locG_mid
#print axioms Eis.locG_mid_three
#print axioms Eis.locG_high
