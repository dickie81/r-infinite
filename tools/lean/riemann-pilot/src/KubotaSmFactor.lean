import KubotaCoefResidue

/-! # The sums `S_m(c)` at a primary prime (round 451)

S5f-13 of round 360's plan, part 2. Round 450's next step planned the relations among round 430's Dirichlet
series `D_m(s) = Σ_c S_m(c)N(c)^{−s}` at a primary prime `p`, beginning with the factorization of round 428's
sums `S_m(c) = Σ_{d mod 3c} (c/d)₃·ĕ((m/9)(d/c))`, over the `d` with `(c, d)` a bottom row of `Γ_1(3)`. This
round proves the factorization. For `m = δ₃x`, a primary prime `p`, `k ≥ 1`, and `c′ ≠ 0` with `3 ∣ c′` and
`p ∤ c′`:

* **The summand** (`smTerm`, a definition; `cuspSm_eq`, `smTerm_add` and `tsum_quot_eq_sum`): the summand of
  `S_m(c)` is periodic modulo `3c`, and a sum over the classes modulo `N` of a function periodic modulo `N` is
  its sum over any complete residue system.
* **The local sum** (`locTerm` and `locG`, definitions; `locTerm_add`):
  `G_k(m) = Σ_{f mod p^k, p ∤ f} (f/p)₃^k·ĕ((m/9)·(3f/p^k))`, whose summand is periodic modulo `p^k`.
* **The factorization** (`bRow_crt`, `cub_crt` and `smTerm_crt`; **`cuspSm_mul_pow`**):
  `S_m(p^k c′) = (3/p)₃^k·(c′/p)₃^{2k}·G_k(m)·S_m(c′)`. The classes modulo `3p^k c′` are the `3c′f₁ + p^k f₂`
  (round 295's `crt_rep_bijective`); `(p^k c′, 3c′f₁ + p^k f₂)` is a bottom row exactly when `p ∤ f₁` and
  `(c′, f₂)` is one; and the symbol factors by cubic reciprocity (round 290's `cub_recip`) and its periodicity
  (round 382's `cub_add_three_mul`).
* **The twist by `p^e`** (`smTerm_twist`; **`cuspSm_twist`**): `S_{δ₃xp^e}(c′) = (c′/p)₃^{2e}·S_{δ₃x}(c′)` for
  `p` primary and prime to `c′`.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### The summand -/

open Classical in
/-- The summand of round 428's `S_m(c)` at `d`: `(c/d)₃·ĕ((m/9)·(d/c))` when `(c, d)` is a bottom row, and `0`
otherwise. -/
def smTerm (m c d : 𝓞 K) : ℂ :=
  if BRow (c, d) then σO (cub c (span {d})) * ebr (σO m / 9 * (σO d / σO c)) else 0

/-- `S_m(c)` is the sum of its summand over the classes modulo `3c`. -/
theorem cuspSm_eq (m c : 𝓞 K) :
    cuspSm m c = ∑' r : 𝓞 K ⧸ span {3 * c}, smTerm m c (repQ (3 * c) r) := rfl

/-- **The summand is periodic modulo `3c`**, for `m ∈ δ₃ℤ[ω]` (round 389's `bRow_add_iff` and
`cub_add_of_bRow`, round 428's `ebr_period`). -/
theorem smTerm_add (x c d u : 𝓞 K) (hc : c ≠ 0) :
    smTerm (δ3 * x) c (d + 3 * c * u) = smTerm (δ3 * x) c d := by
  classical
  unfold smTerm
  by_cases h : BRow (c, d)
  · have h' : BRow (c, d + 3 * c * u) := (bRow_add_iff u).2 h
    rw [ite_eq_left h', ite_eq_left h, cub_add_of_bRow h u]
    congr 1
    have hσc : σO c ≠ 0 := σO_ne_zero hc
    have e : σO (δ3 * x) / 9 * (σO (d + 3 * c * u) / σO c) =
        σO (δ3 * x) / 9 * (σO d / σO c) + σO (δ3 * x) * σO (3 * u) / 9 := by
      simp only [map_add, map_mul]; field_simp
    rw [e, ebr_add, ebr_period, mul_one]
  · rw [ite_eq_right (mt (bRow_add_iff u).1 h), ite_eq_right h]

/-- **A sum over the classes modulo `N` is the sum over any complete residue system**, for `F` periodic
modulo `N` (as round 295's `gaussTr_eq_sum`). -/
theorem tsum_quot_eq_sum {ι : Type*} [Fintype ι] (N : 𝓞 K) (hN : N ≠ 0) (F : 𝓞 K → ℂ)
    (hF : ∀ z u, F (z + N * u) = F z) (rep : ι → 𝓞 K)
    (hR : Function.Bijective (fun p : ι × 𝓞 K => rep p.1 + N * p.2)) :
    ∑' r : 𝓞 K ⧸ span {N}, F (repQ N r) = ∑ i, F (rep i) := by
  have : Finite (𝓞 K ⧸ span {N}) := finite_quot N hN
  let : Fintype (𝓞 K ⧸ span {N}) := Fintype.ofFinite _
  rw [tsum_fintype]
  symm
  refine Fintype.sum_bijective _ (rep_mk_bijective N rep hR) _ _ fun i => ?_
  exact periodic_congr N F hF (repQ_mk N _).symm

/-! ### The factor at a primary prime -/

open Classical in
/-- The summand of the local sum at `p^k`: `(f/p)₃^k·ĕ((m/9)·(3f/p^k))` for `p ∤ f`, and `0` for `p ∣ f`. -/
def locTerm (m p : 𝓞 K) (k : ℕ) (f : 𝓞 K) : ℂ :=
  if p ∣ f then 0 else σO (cub f (span {p})) ^ k * ebr (σO m / 9 * (σO (3 * f) / σO (p ^ k)))

/-- **The local sum at `p^k`**: `G_k(m) = Σ_{f mod p^k, p ∤ f} (f/p)₃^k·ĕ((m/9)·(3f/p^k))`. -/
def locG (m p : 𝓞 K) (k : ℕ) : ℂ := ∑' f : 𝓞 K ⧸ span {p ^ k}, locTerm m p k (repQ (p ^ k) f)

/-- The local summand is periodic modulo `p^k`, for `k ≥ 1` and `m ∈ δ₃ℤ[ω]`. -/
theorem locTerm_add (x p : 𝓞 K) (hp : p ≠ 0) {k : ℕ} (hk : 0 < k) (f u : 𝓞 K) :
    locTerm (δ3 * x) p k (f + p ^ k * u) = locTerm (δ3 * x) p k f := by
  classical
  unfold locTerm
  have hpk : p ∣ p ^ k * u := dvd_mul_of_dvd_left (dvd_pow_self p hk.ne') u
  by_cases h : p ∣ f
  · rw [ite_eq_left ((dvd_add_right h).2 hpk), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((dvd_add_left hpk).1 h')), ite_eq_right h,
      cub_congr (show p ∣ f + p ^ k * u - f by rw [add_sub_cancel_left]; exact hpk)]
    congr 1
    have hσ : σO (p ^ k) ≠ 0 := σO_ne_zero (pow_ne_zero k hp)
    have e : σO (δ3 * x) / 9 * (σO (3 * (f + p ^ k * u)) / σO (p ^ k)) =
        σO (δ3 * x) / 9 * (σO (3 * f) / σO (p ^ k)) + σO (δ3 * x) * σO (3 * u) / 9 := by
      simp only [map_add, map_mul, map_pow] at hσ ⊢; field_simp
    rw [e, ebr_add, ebr_period, mul_one]

/-- **The bottom rows modulo `3p^k c′`**, through the Chinese remainder theorem: for a primary prime `p`,
`k ≥ 1`, `3 ∣ c′` and `p ∤ c′`, `(p^k c′, 3c′f₁ + p^k f₂)` is a bottom row exactly when `p ∤ f₁` and
`(c′, f₂)` is one. -/
theorem bRow_crt {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {k : ℕ} (hk : 0 < k) {c' : 𝓞 K}
    (h3 : (3 : 𝓞 K) ∣ c') (hpc : ¬ p ∣ c') (f₁ f₂ : 𝓞 K) :
    BRow (p ^ k * c', 3 * c' * f₁ + p ^ k * f₂) ↔ ¬ p ∣ f₁ ∧ BRow (c', f₂) := by
  have hp3 : ¬ p ∣ 3 := fun h => by
    obtain ⟨t, ht⟩ := hpp
    exact hp.not_isUnit (isUnit_of_dvd_one (by
      have : p ∣ p - 3 * t := dvd_sub (dvd_refl p) (dvd_mul_of_dvd_left h t)
      rwa [show p - 3 * t = 1 by linear_combination ht] at this))
  have hprim : Primary (3 * c' * f₁ + p ^ k * f₂) ↔ Primary f₂ := by
    obtain ⟨t, ht⟩ := primary_pow hpp k
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w - c' * f₁ - t * f₂, by linear_combination hw - f₂ * ht⟩
    · rintro ⟨w, hw⟩
      exact ⟨w + c' * f₁ + t * f₂, by linear_combination hw + f₂ * ht⟩
  have hcop2 : IsCoprime c' (3 * c' * f₁ + p ^ k * f₂) ↔ IsCoprime c' f₂ := by
    have hcp : IsCoprime c' (p ^ k) := ((Prime.coprime_iff_not_dvd hp).2 hpc).symm.pow_right
    rw [show 3 * c' * f₁ + p ^ k * f₂ = p ^ k * f₂ + c' * (3 * f₁) by ring,
      IsCoprime.add_mul_left_right_iff, IsCoprime.mul_right_iff]
    exact ⟨fun h => h.2, fun h => ⟨hcp, h⟩⟩
  have hcop1 : IsCoprime (p ^ k) (3 * c' * f₁ + p ^ k * f₂) ↔ ¬ p ∣ f₁ := by
    rw [show 3 * c' * f₁ + p ^ k * f₂ = 3 * c' * f₁ + p ^ k * f₂ from rfl]
    constructor
    · intro h hf
      have h' : IsCoprime p (3 * c' * f₁ + p ^ k * f₂) := h.of_isCoprime_of_dvd_left (dvd_pow_self p hk.ne')
      exact (Prime.coprime_iff_not_dvd hp).1 h'
        (dvd_add (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_left (dvd_pow_self p hk.ne') _))
    · intro hf
      refine IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
      have h1 : p ∣ 3 * c' * f₁ := (dvd_add_left (dvd_mul_of_dvd_left (dvd_pow_self p hk.ne') f₂)).1 h
      rcases hp.dvd_or_dvd h1 with h2 | h2
      · rcases hp.dvd_or_dvd h2 with h3' | h3'
        · exact hp3 h3'
        · exact hpc h3'
      · exact hf h2
  unfold BRow
  simp only
  rw [IsCoprime.mul_left_iff, hcop1, hcop2, hprim]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, -, h4⟩
    exact ⟨⟨h1, h2⟩, dvd_mul_of_dvd_right h3 _, h4⟩

/-- **The symbol at `3c′f₁ + p^k f₂`**: `(p^k c′/d)₃ = (3/p)₃^k·(c′/p)₃^{2k}·(f₁/p)₃^k·(c′/f₂)₃`, by cubic
reciprocity (round 290's `cub_recip`) for `(p/d)₃` and periodicity (round 382's `cub_add_three_mul`) for
`(c′/d)₃`. -/
theorem cub_crt {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {k : ℕ} (hk : 0 < k) {c' : 𝓞 K}
    (h3 : (3 : 𝓞 K) ∣ c') (hpc : ¬ p ∣ c') {f₁ f₂ : 𝓞 K}
    (h : BRow (p ^ k * c', 3 * c' * f₁ + p ^ k * f₂)) :
    cub (p ^ k * c') (span {3 * c' * f₁ + p ^ k * f₂}) =
      cub 3 (span {p}) ^ k * cub c' (span {p}) ^ (2 * k) * cub f₁ (span {p}) ^ k * cub c' (span {f₂}) := by
  obtain ⟨hf₁, hrow⟩ := (bRow_crt hp hpp hk h3 hpc f₁ f₂).1 h
  have hd : Primary (3 * c' * f₁ + p ^ k * f₂) := h.2.2
  have hcop : IsCoprime p (3 * c' * f₁ + p ^ k * f₂) :=
    (IsCoprime.mul_left_iff.1 h.1).1.of_isCoprime_of_dvd_left (dvd_pow_self p hk.ne')
  have hp0 := hp.ne_zero
  have hf₂0 : f₂ ≠ 0 := primary_ne_zero hrow.2.2
  have e1 : cub p (span {3 * c' * f₁ + p ^ k * f₂}) =
      cub 3 (span {p}) * cub c' (span {p}) * cub f₁ (span {p}) := by
    rw [cub_recip hpp hd hcop,
      cub_congr (show p ∣ 3 * c' * f₁ + p ^ k * f₂ - 3 * c' * f₁ by
        rw [add_sub_cancel_left]; exact dvd_mul_of_dvd_left (dvd_pow_self p hk.ne') f₂),
      cub_mul_left, cub_mul_left]
  have hpk : Primary (p ^ k * f₂) := (primary_pow hpp k).mul hrow.2.2
  have hpkc : IsCoprime (p ^ k * f₂) c' :=
    IsCoprime.mul_left (((Prime.coprime_iff_not_dvd hp).2 hpc).pow_left) hrow.1.symm
  have e2 : cub c' (span {3 * c' * f₁ + p ^ k * f₂}) = cub c' (span {p}) ^ k * cub c' (span {f₂}) := by
    rw [show 3 * c' * f₁ + p ^ k * f₂ = p ^ k * f₂ + 3 * c' * f₁ by ring, cub_add_three_mul hpk hpkc h3 f₁,
      cub_mul_span c' (pow_ne_zero k hp0) hf₂0, cub_pow_span c' hp0 k]
  rw [cub_mul_left, cub_pow_left (x := p) hd, e1, e2]
  ring

/-- **The summand at `3c′f₁ + p^k f₂`** factors: `(3/p)₃^k·(c′/p)₃^{2k}` times the local summand at `f₁` times
the summand of `S_m(c′)` at `f₂`. -/
theorem smTerm_crt {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {k : ℕ} (hk : 0 < k) {c' : 𝓞 K}
    (hc' : c' ≠ 0) (h3 : (3 : 𝓞 K) ∣ c') (hpc : ¬ p ∣ c') (x f₁ f₂ : 𝓞 K) :
    smTerm (δ3 * x) (p ^ k * c') (3 * c' * f₁ + p ^ k * f₂) =
      σO (cub 3 (span {p})) ^ k * σO (cub c' (span {p})) ^ (2 * k) * locTerm (δ3 * x) p k f₁ *
        smTerm (δ3 * x) c' f₂ := by
  classical
  have hp0 := hp.ne_zero
  by_cases h : BRow (p ^ k * c', 3 * c' * f₁ + p ^ k * f₂)
  · obtain ⟨hf₁, hrow⟩ := (bRow_crt hp hpp hk h3 hpc f₁ f₂).1 h
    unfold smTerm locTerm
    rw [ite_eq_left h, ite_eq_left hrow, ite_eq_right hf₁, cub_crt hp hpp hk h3 hpc h]
    have hσp : σO (p ^ k) ≠ 0 := σO_ne_zero (pow_ne_zero k hp0)
    have hσc : σO c' ≠ 0 := σO_ne_zero hc'
    have e : σO (δ3 * x) / 9 * (σO (3 * c' * f₁ + p ^ k * f₂) / σO (p ^ k * c')) =
        σO (δ3 * x) / 9 * (σO (3 * f₁) / σO (p ^ k)) + σO (δ3 * x) / 9 * (σO f₂ / σO c') := by
      simp only [map_add, map_mul, map_pow] at hσp ⊢; field_simp
    rw [e, ebr_add]
    simp only [map_mul, map_pow]
    ring
  · have h' : ¬ (¬ p ∣ f₁ ∧ BRow (c', f₂)) := fun h' => h ((bRow_crt hp hpp hk h3 hpc f₁ f₂).2 h')
    unfold smTerm
    rw [ite_eq_right h]
    by_cases hf₁ : p ∣ f₁
    · unfold locTerm; rw [ite_eq_left hf₁]; ring
    · rw [ite_eq_right fun hr => h' ⟨hf₁, hr⟩]; ring

/-- **The factorization of `S_m` at a primary prime**: for `p` a primary prime, `k ≥ 1`, `c′ ≠ 0` with
`3 ∣ c′` and `p ∤ c′`, and `m = δ₃x`, `S_m(p^k c′) = (3/p)₃^k·(c′/p)₃^{2k}·G_k(m)·S_m(c′)` (round 295's
`crt_rep_bijective`). -/
theorem cuspSm_mul_pow {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {k : ℕ} (hk : 0 < k) {c' : 𝓞 K}
    (hc' : c' ≠ 0) (h3 : (3 : 𝓞 K) ∣ c') (hpc : ¬ p ∣ c') (x : 𝓞 K) :
    cuspSm (δ3 * x) (p ^ k * c') =
      σO (cub 3 (span {p})) ^ k * σO (cub c' (span {p})) ^ (2 * k) * locG (δ3 * x) p k *
        cuspSm (δ3 * x) c' := by
  classical
  have hp0 := hp.ne_zero
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp0
  have h30 : (3 : 𝓞 K) ≠ 0 := fun h => by
    have := congrArg σO h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have h3c : (3 : 𝓞 K) * c' ≠ 0 := mul_ne_zero h30 hc'
  have hcop : IsCoprime (p ^ k) (3 * c') := by
    refine IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
    rcases hp.dvd_or_dvd h with h' | h'
    · obtain ⟨t, ht⟩ := hpp
      exact hp.not_isUnit (isUnit_of_dvd_one (by
        have : p ∣ p - 3 * t := dvd_sub (dvd_refl p) (dvd_mul_of_dvd_left h' t)
        rwa [show p - 3 * t = 1 by linear_combination ht] at this))
    · exact hpc h'
  have := finite_quot (p ^ k) hpk
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ k})
  have := finite_quot (3 * c') h3c
  have := Fintype.ofFinite (𝓞 K ⧸ span {3 * c'})
  have hcrt := crt_rep_bijective (p ^ k) (3 * c') hpk h3c hcop (repQ (p ^ k)) (repQ (3 * c'))
    (repQ_bijective _ hpk) (repQ_bijective _ h3c)
  have hN : 3 * (p ^ k * c') = p ^ k * (3 * c') := by ring
  have hR : Function.Bijective (fun q : ((𝓞 K ⧸ span {p ^ k}) × (𝓞 K ⧸ span {3 * c'})) × 𝓞 K =>
      (fun q : (𝓞 K ⧸ span {p ^ k}) × (𝓞 K ⧸ span {3 * c'}) =>
        3 * c' * repQ (p ^ k) q.1 + p ^ k * repQ (3 * c') q.2) q.1 + 3 * (p ^ k * c') * q.2) := by
    rw [hN]; exact hcrt
  have hsum := tsum_quot_eq_sum (3 * (p ^ k * c')) (by rw [hN]; exact mul_ne_zero hpk h3c)
    (smTerm (δ3 * x) (p ^ k * c')) (fun z u => smTerm_add x _ z u (mul_ne_zero hpk hc'))
    (fun q : (𝓞 K ⧸ span {p ^ k}) × (𝓞 K ⧸ span {3 * c'}) =>
      3 * c' * repQ (p ^ k) q.1 + p ^ k * repQ (3 * c') q.2) hR
  rw [cuspSm_eq, hsum, Fintype.sum_prod_type, locG, cuspSm_eq (δ3 * x) c', tsum_fintype, tsum_fintype]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  exact smTerm_crt hp hpp hk hc' h3 hpc x _ _

/-! ### The twist by `p^e` -/

/-- **The summand twisted by `p^e`**: for `πp^e + 3wc′ = 1` with `p` primary, prime to `c′` and `3 ∣ c′`, the
summand of `S_{mp^e}(c′)` at `πf` is `(c′/p)₃^{2e}` times that of `S_m(c′)` at `f`. -/
theorem smTerm_twist {p : 𝓞 K} (hpp : Primary p) {c' : 𝓞 K} (hc' : c' ≠ 0) (h3 : (3 : 𝓞 K) ∣ c')
    (hpc : IsCoprime p c') (e : ℕ) {π w : 𝓞 K} (hπ : π * p ^ e + w * (3 * c') = 1) (x f : 𝓞 K) :
    smTerm (δ3 * (x * p ^ e)) c' (π * f) = σO (cub c' (span {p})) ^ (2 * e) * smTerm (δ3 * x) c' f := by
  classical
  have hπc : IsCoprime π c' := ⟨p ^ e, 3 * w, by linear_combination hπ⟩
  have hπp : Primary π := by
    obtain ⟨t, ht⟩ := primary_pow hpp e
    exact ⟨-(π * t) - w * c', by linear_combination hπ - π * ht⟩
  have hπ0 : π ≠ 0 := primary_ne_zero hπp
  have hrow : BRow (c', π * f) ↔ BRow (c', f) := by
    unfold BRow
    simp only
    rw [IsCoprime.mul_right_iff, primary_mul_iff hπp]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hπc.symm, h.1⟩, h.2⟩⟩
  unfold smTerm
  by_cases h : BRow (c', f)
  · rw [ite_eq_left (hrow.2 h), ite_eq_left h]
    have hf0 : f ≠ 0 := primary_ne_zero h.2.2
    have hcp3 : cub c' (span {p}) ^ 3 = 1 := cub_pow_three hpp hpc.symm
    have hone : cub c' (span {π}) * cub c' (span {p}) ^ e = 1 := by
      rw [← cub_pow_span c' (primary_ne_zero hpp) e,
        ← cub_mul_span c' hπ0 (pow_ne_zero e (primary_ne_zero hpp)),
        show π * p ^ e = 1 + 3 * c' * (-w) by linear_combination hπ,
        cub_add_three_mul ⟨0, by ring⟩ isCoprime_one_left h3, cub_one_right]
    have hπcub : cub c' (span {π}) = cub c' (span {p}) ^ (2 * e) := by
      calc cub c' (span {π}) = cub c' (span {π}) * (cub c' (span {p}) ^ 3) ^ e := by
            rw [hcp3, one_pow, mul_one]
        _ = (cub c' (span {π}) * cub c' (span {p}) ^ e) * cub c' (span {p}) ^ (2 * e) := by ring
        _ = cub c' (span {p}) ^ (2 * e) := by rw [hone, one_mul]
    rw [cub_mul_span c' hπ0 hf0, hπcub]
    have hσc : σO c' ≠ 0 := σO_ne_zero hc'
    have e1 : σO (δ3 * (x * p ^ e)) / 9 * (σO (π * f) / σO c') =
        σO (δ3 * x) / 9 * (σO f / σO c') + σO (δ3 * x) * σO (3 * (-(w * f))) / 9 := by
      have hπ' : σO π * σO p ^ e = 1 - σO w * (3 * σO c') := by
        have := congrArg σO hπ
        simp only [map_add, map_mul, map_pow, map_one, map_ofNat] at this
        linear_combination this
      simp only [map_mul, map_pow, map_neg, map_ofNat]
      field_simp
      linear_combination (σO δ3 * σO x * σO f) * hπ'
    rw [e1, ebr_add, ebr_period, mul_one]
    simp only [map_mul, map_pow]
    ring
  · rw [ite_eq_right (mt hrow.1 h), ite_eq_right h, mul_zero]

/-- **`S_{mp^e}(c′) = (c′/p)₃^{2e}·S_m(c′)`** for `p` primary and prime to `c′`, `c′ ≠ 0` with `3 ∣ c′`, and
`m = δ₃x`: the classes `πf`, with `πp^e ≡ 1 (mod 3c′)`, run over the classes modulo `3c′`. -/
theorem cuspSm_twist {p : 𝓞 K} (hpp : Primary p) {c' : 𝓞 K} (hc' : c' ≠ 0) (h3 : (3 : 𝓞 K) ∣ c')
    (hpc : IsCoprime p c') (e : ℕ) (x : 𝓞 K) :
    cuspSm (δ3 * (x * p ^ e)) c' = σO (cub c' (span {p})) ^ (2 * e) * cuspSm (δ3 * x) c' := by
  classical
  have h30 : (3 : 𝓞 K) ≠ 0 := fun h => by
    have := congrArg σO h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have h3c : (3 : 𝓞 K) * c' ≠ 0 := mul_ne_zero h30 hc'
  have hp3 : IsCoprime p 3 := by
    obtain ⟨t, ht⟩ := hpp
    exact ⟨1, -t, by linear_combination ht⟩
  obtain ⟨π, w, hπ'⟩ := (hp3.mul_right hpc).pow_left (m := e)
  have hπc3 : IsCoprime π (3 * c') := ⟨p ^ e, w, by linear_combination hπ'⟩
  have := finite_quot (3 * c') h3c
  have := Fintype.ofFinite (𝓞 K ⧸ span {3 * c'})
  rw [cuspSm_eq, cuspSm_eq, tsum_fintype, tsum_fintype, Finset.mul_sum]
  set E : 𝓞 K ⧸ span {3 * c'} → 𝓞 K ⧸ span {3 * c'} :=
    fun r => Ideal.Quotient.mk (span {3 * c'}) (π * repQ (3 * c') r) with hE
  have hinj : Function.Injective E := by
    intro r r' h
    rw [hE, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have h' : 3 * c' ∣ π * (repQ (3 * c') r - repQ (3 * c') r') := by
      rw [mul_sub]; exact h
    have h'' := hπc3.symm.dvd_of_dvd_mul_left h'
    rw [← repQ_mk (3 * c') r, ← repQ_mk (3 * c') r', Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h''
  refine (Fintype.sum_bijective E (Finite.injective_iff_bijective.1 hinj) _ _ fun r => ?_).symm
  rw [← smTerm_twist hpp hc' h3 hpc e hπ' x]
  have hper : ∀ z u, smTerm (δ3 * (x * p ^ e)) c' (z + 3 * c' * u) = smTerm (δ3 * (x * p ^ e)) c' z :=
    fun z u => smTerm_add _ c' z u hc'
  obtain ⟨u, hu⟩ := dvd_repQ_sub (3 * c') (π * repQ (3 * c') r)
  rw [show repQ (3 * c') (Ideal.Quotient.mk (span {3 * c'}) (π * repQ (3 * c') r)) =
    π * repQ (3 * c') r + 3 * c' * u by linear_combination hu, hper]

end Eis

end

#print axioms Eis.cuspSm_eq
#print axioms Eis.smTerm_add
#print axioms Eis.tsum_quot_eq_sum
#print axioms Eis.locTerm_add
#print axioms Eis.bRow_crt
#print axioms Eis.cub_crt
#print axioms Eis.smTerm_crt
#print axioms Eis.cuspSm_mul_pow
#print axioms Eis.smTerm_twist
#print axioms Eis.cuspSm_twist
