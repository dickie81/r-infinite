import KubotaCusps

/-! # The multiplier at a cusp (round 369)

S5f-3d, part 1, the fourth part of round 360's S5f-3. The companion paper's (A.10) gives Kubota's
character at `g₁ = gH⁻¹` in three cases, "`(c_0/a)_3(a/r)_3,&3\mid c,`",
"`(-u_0/(a-u_0b_g))_3\,((c_0/u_0)/a)_3(a/r)_3,`" at `v_λ(c) = 1`, and "`(a/c_0)_3(a/r)_3,&(c,\lambda)=1.`",
proved by "`the determinant equation and cubic reciprocity`". This file proves the multiplier in the form
the group identity uses, and the tools for constructing the cusp matrices.

* **`3 ∣ c`** (`kub_of_ne`): `κ(g) = (c/a)₃` by the definition of round 361's `kub`.
* **`v_λ(c) = 1`** (**`kub_lower`**): for `ad − bc = 1` with `a` primary and `9 ∣ b`,
  `κ((a − u₀b, b; c − u₀d, d)) = (c/a)₃` for `u₀ = ±λ`, through `a(c − u₀d) = −u₀ + c(a − u₀b)`,
  `bc ≡ −1 (mod a)`, round 290's `cub_recip` and round 362's `cub_δ3_congr`.
* **`(c, λ) = 1`** (**`kub_inv`**): for `ad − bc = 1` with `c` primary and `9 ∣ d ≠ 0`,
  `κ((−b, a + ub; −d, c + ud)) = (a/c)₃`, through `(d/−bc)₃ = 1` (round 365's `exists_S_decomp`, round
  362's `cub_unit_of_nine` and `cub_δ3_of_nine`, round 364's `cub_two_congr`, and reciprocity at the part
  of `d` prime to `6`).
* **The splitting** (`cub_split_left`, **`σO_cub_prod`**): `(er/a)₃ = (e/a)₃(a/r)₃`, and
  `σ((a/∏_{P∈A}π_P)₃) = ∏_{P∈A}χ_P(a)²`.
* **The fixed factor** (**`cub_S_congr`**): `(uλʲ2ⁱ/a)₃` depends only on `a` modulo `9` and `2`.
* **Tools for the construction** (`isCoprime_δ3_of_primary`, `cub_pow_left`, `theta_add_three`,
  `exists_reduced`, `mod_lam`, `lam_shape`): `θ(z + 3t, v) = θ(z, v)`, lowest terms in the principal ideal
  ring `𝓞`, residues modulo `λ`, and `c ≡ ±λ (mod 3)` at `v_λ(c) = 1`.
-/

open NumberField Ideal UniqueFactorizationMonoid Complex
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- The symmetric form of round 362's `isCoprime_δ3`. -/
theorem isCoprime_δ3_of_primary {a : 𝓞 K} (ha : Primary a) : IsCoprime a δ3 :=
  (isCoprime_δ3 ha).symm

theorem kub_of_ne {γ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (h : γ 1 0 ≠ 0) :
    kub γ = σO (cub (γ 1 0) (span {γ 0 0})) := by
  unfold kub; exact ite_eq_right h

theorem cub_pow_left {x N : 𝓞 K} (hN : Primary N) (n : ℕ) :
    cub (x ^ n) (span {N}) = cub x (span {N}) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, cub_one hN]
  | succ n ih => rw [pow_succ, cub_mul_left, ih, pow_succ]

/-- **The multiplier at `H = (1, 0; ±λ, 1)`** (the companion paper's (A.10), the case `v_λ(c) = 1`):
for `ad − bc = 1` with `a` primary and `9 ∣ b`, `κ((a − u₀b, b; c − u₀d, d)) = (c/a)₃` for `u₀ = ±λ`. -/
theorem kub_lower {a b c d u₀ : 𝓞 K} (hdet : a * d - b * c = 1) (ha : Primary a) (hb : (9 : 𝓞 K) ∣ b)
    (hu : u₀ = δ3 ∨ u₀ = -δ3) (hC : c - u₀ * d ≠ 0) :
    kub !![a - u₀ * b, b; c - u₀ * d, d] = σO (cub c (span {a})) := by
  have e10 : (!![a - u₀ * b, b; c - u₀ * d, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = c - u₀ * d := rfl
  have e00 : (!![a - u₀ * b, b; c - u₀ * d, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0 = a - u₀ * b := rfl
  rw [kub_of_ne (by rw [e10]; exact hC), e10, e00]
  congr 1
  have h3b : (3 : 𝓞 K) ∣ u₀ * b := by
    obtain ⟨k, hk⟩ := hb
    exact ⟨u₀ * 3 * k, by rw [hk]; ring⟩
  have hA : Primary (a - u₀ * b) := by
    obtain ⟨t, ht⟩ := ha
    obtain ⟨k, hk⟩ := h3b
    exact ⟨t - k, by linear_combination ht - hk⟩
  have hA9 : (9 : 𝓞 K) ∣ (a - u₀ * b) - a := by
    obtain ⟨k, hk⟩ := hb
    exact ⟨-(u₀ * k), by rw [hk]; ring⟩
  have hab : IsCoprime a b := ⟨d, -c, by linear_combination hdet⟩
  have hau : IsCoprime a u₀ := by
    rcases hu with rfl | rfl
    · exact isCoprime_δ3_of_primary ha
    · exact (isCoprime_δ3_of_primary ha).neg_right
  have hcop : IsCoprime a (a - u₀ * b) := by
    obtain ⟨x, y, hxy⟩ := hau.mul_right hab
    exact ⟨x + y, -y, by linear_combination hxy⟩
  have hca : IsCoprime c a := ⟨-b, d, by linear_combination hdet⟩
  have hua : IsCoprime (-u₀) a := hau.symm.neg_left
  -- `a·(c − u₀d) = −u₀ + c·(a − u₀b)`
  have key : a * (c - u₀ * d) - -u₀ = (a - u₀ * b) * c := by linear_combination (-u₀) * hdet
  set A' := a - u₀ * b with hA'
  set C' := c - u₀ * d with hC'
  have h1 : cub a (span {A'}) * cub C' (span {A'}) = cub (-u₀) (span {A'}) := by
    rw [← cub_mul_left]; exact cub_congr ⟨c, key⟩
  have h2 : cub a (span {A'}) = cub (-u₀) (span {a}) * cub b (span {a}) := by
    rw [cub_recip ha hA hcop, ← cub_mul_left]
    exact cub_congr ⟨1, by rw [hA']; ring⟩
  have h3 : cub b (span {a}) * cub c (span {a}) = 1 := by
    rw [← cub_mul_left, cub_congr (show a ∣ b * c - (-1) from ⟨d, by linear_combination -hdet⟩),
      cub_neg ha, cub_one ha]
  have h4 : cub (-u₀) (span {A'}) = cub (-u₀) (span {a}) := by
    rcases hu with rfl | rfl
    · rw [cub_neg hA, cub_neg ha]; exact cub_δ3_congr hA ha hA9
    · rw [neg_neg]; exact cub_δ3_congr hA ha hA9
  have hX := cub_ne_zero ha hua
  -- `X·B·W = X`, so `B·W = 1`, and `B·Y = 1`
  have hBW : cub b (span {a}) * cub C' (span {A'}) = 1 := by
    apply mul_left_cancel₀ hX
    rw [mul_one, ← mul_assoc, ← h2, h1, h4]
  calc cub C' (span {A'}) = cub C' (span {A'}) * (cub b (span {a}) * cub c (span {a})) := by
        rw [h3, mul_one]
    _ = (cub b (span {a}) * cub C' (span {A'})) * cub c (span {a}) := by ring
    _ = cub c (span {a}) := by rw [hBW, one_mul]

/-- **The multiplier at `H = (u, −1; 1, 0)`** (the companion paper's (A.10), the case `(c, λ) = 1`): for
`ad − bc = 1` with `c` primary, `9 ∣ d`, `d ≠ 0` and `b ≠ 0`,
`κ((−b, a + ub; −d, c + ud)) = (a/c)₃`. -/
theorem kub_inv {a b c d u : 𝓞 K} (hdet : a * d - b * c = 1) (hc : Primary c) (hd9 : (9 : 𝓞 K) ∣ d)
    (hd0 : d ≠ 0) (hb0 : b ≠ 0) :
    kub !![-b, a + u * b; -d, c + u * d] = σO (cub a (span {c})) := by
  have e10 : (!![-b, a + u * b; -d, c + u * d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = -d := rfl
  have e00 : (!![-b, a + u * b; -d, c + u * d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0 = -b := rfl
  rw [kub_of_ne (by rw [e10]; exact neg_ne_zero.2 hd0), e10, e00]
  congr 1
  have hc0 := primary_ne_zero hc
  -- `N = −bc = 1 − ad ≡ 1 (mod 9)`
  have hN9 : (9 : 𝓞 K) ∣ -b * c - 1 := by
    obtain ⟨k, hk⟩ := hd9
    exact ⟨-(a * k), by linear_combination hdet - a * hk⟩
  have hN := primary_of_nine hN9
  have hb : Primary (-b) := by
    obtain ⟨t, ht⟩ := hc
    obtain ⟨k, hk⟩ := hN9
    exact ⟨b * t + 3 * k, by linear_combination hk + b * ht⟩
  rw [cub_neg hb]
  -- `(d/N)₃ = 1`
  have hdN : cub d (span {-b * c}) = 1 := by
    obtain ⟨ε, s, t, d'', hd''p, -, hdd⟩ := exists_S_decomp _ d rfl hd0
    have hd''d : d'' ∣ d := ⟨ε * δ3 ^ s * 2 ^ t, by rw [hdd]; ring⟩
    have h2 : cub 2 (span {-b * c}) ^ t = 1 := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [pow_zero]
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have h2d : (2 : 𝓞 K) ∣ d := ⟨ε * δ3 ^ s * 2 ^ t' * d'', by rw [hdd, pow_succ]; ring⟩
        have h2N : (2 : 𝓞 K) ∣ -b * c - 1 := by
          obtain ⟨k, hk⟩ := h2d
          exact ⟨-(a * k), by linear_combination hdet - a * hk⟩
        have hcopN : IsCoprime (-b * c) 2 := by
          obtain ⟨k, hk⟩ := h2N
          exact ⟨1, -k, by linear_combination hk⟩
        rw [cub_two_congr hN primary_one hcopN isCoprime_one_left (by simpa using h2N), cub_one_right,
          one_pow]
    have hd'' : cub d'' (span {-b * c}) = 1 := by
      have hcop : IsCoprime d'' (-b * c) := by
        obtain ⟨m, hm⟩ := hd''d
        exact ⟨a * m, 1, by linear_combination hdet - a * hm⟩
      rw [cub_recip hd''p hN hcop, cub_congr (show d'' ∣ -b * c - 1 from
        dvd_trans hd''d ⟨-a, by linear_combination hdet⟩), cub_one hd''p]
    rw [hdd, cub_mul_left, cub_mul_left, cub_mul_left, cub_pow_left hN, cub_pow_left hN,
      cub_unit_of_nine ε hN9, cub_δ3_of_nine hN9, one_pow, one_mul, one_mul, h2, one_mul, hd'']
  have hsplit := cub_mul_span d (neg_ne_zero.2 hb0) hc0
  rw [hdN] at hsplit
  have hdc : cub d (span {c}) * cub a (span {c}) = 1 := by
    rw [← cub_mul_left, cub_congr (show c ∣ d * a - 1 from ⟨b, by linear_combination hdet⟩), cub_one hc]
  calc cub d (span {-b}) = cub d (span {-b}) * (cub d (span {c}) * cub a (span {c})) := by
        rw [hdc, mul_one]
    _ = (cub d (span {-b}) * cub d (span {c})) * cub a (span {c}) := by ring
    _ = cub a (span {c}) := by rw [← hsplit, one_mul]

/-- **The splitting of `(c/a)₃` at `c = e·r`**: `(er/a)₃ = (e/a)₃·(a/r)₃` for `a, r` primary and coprime. -/
theorem cub_split_left {a r : 𝓞 K} (e : 𝓞 K) (ha : Primary a) (hr : Primary r) (har : IsCoprime a r) :
    cub (e * r) (span {a}) = cub e (span {a}) * cub a (span {r}) := by
  rw [cub_mul_left, cub_recip hr ha har.symm]

/-- `σ((a/∏_{P∈A}π_P)₃) = ∏_{P∈A}χ_P(a)²`. -/
theorem σO_cub_prod (a : 𝓞 K) (A : Finset Pr) :
    σO (cub a (span {∏ P ∈ A, πP P})) = ∏ P ∈ A, chiP P.1 a ^ 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, cub_one_right, map_one]
  | insert P A hP ih =>
    rw [Finset.prod_insert hP, Finset.prod_insert hP,
      cub_mul_span a (ne_zero_of_maximal (πP P)) (prod_πP_ne_zero A), map_mul, ih, cub_prime,
      ← chiP_sq (h6Pr P), (πP_spec P).2]

/-- **The supplementary factor is fixed modulo `18`**: `(uλʲ2ⁱ/a)₃ = (uλʲ2ⁱ/a′)₃` for `a, a′` primary
and odd with `a ≡ a′ (mod 9)` and `(mod 2)`. -/
theorem cub_S_congr (u : (𝓞 K)ˣ) (j i : ℕ) {a a' : 𝓞 K} (ha : Primary a) (ha' : Primary a')
    (h2 : IsCoprime a 2) (h2' : IsCoprime a' 2) (h9 : (9 : 𝓞 K) ∣ a - a') (h22 : (2 : 𝓞 K) ∣ a - a') :
    cub ((u : 𝓞 K) * δ3 ^ j * 2 ^ i) (span {a}) = cub ((u : 𝓞 K) * δ3 ^ j * 2 ^ i) (span {a'}) := by
  rw [cub_mul_left, cub_mul_left, cub_mul_left, cub_mul_left, cub_pow_left ha, cub_pow_left ha,
    cub_pow_left ha', cub_pow_left ha', cub_unit_congr u ha ha' (cub_omega_congr ha ha' h9),
    cub_δ3_congr ha ha' h9, cub_two_congr ha ha' h2 h2' h22]

/-- `θ` is invariant under `z ↦ z + 3t`. -/
theorem theta_add_three {θ : ℂ → ℝ → ℂ}
    (hK3 : ∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)
    (t : 𝓞 K) (z : ℂ) {v : ℝ} (hv : 0 < v) : θ (z + σO (3 * t)) v = θ z v := by
  obtain ⟨d1, m1, k1⟩ := upperThree t
  have h := hK3 _ d1 m1 z v hv
  rw [k1, one_mul] at h
  have hmap : (!![1, 3 * t; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO = !![1, σO (3 * t); 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hmap] at h
  unfold atG at h
  rw [uhsAct_transl] at h
  exact h

/-- **Lowest terms** in the principal ideal ring `𝓞`: `x = gx′`, `L = gL′` with `x′, L′` coprime. -/
theorem exists_reduced (x : 𝓞 K) {L : 𝓞 K} (hL : L ≠ 0) :
    ∃ g x' L' : 𝓞 K, g ≠ 0 ∧ x = g * x' ∧ L = g * L' ∧ IsCoprime x' L' := by
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (span {x, L} : Ideal (𝓞 K))).principal
  have hx : x ∈ span ({g} : Set (𝓞 K)) := by
    rw [← Ideal.submodule_span_eq, ← hg]; exact Ideal.subset_span (by simp)
  have hL' : L ∈ span ({g} : Set (𝓞 K)) := by
    rw [← Ideal.submodule_span_eq, ← hg]; exact Ideal.subset_span (by simp)
  have hgm : g ∈ (span {x, L} : Ideal (𝓞 K)) := by
    rw [hg]; exact Submodule.mem_span_singleton_self g
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton.1 hx
  obtain ⟨L', rfl⟩ := Ideal.mem_span_singleton.1 hL'
  have hg0 : g ≠ 0 := fun h => hL (by rw [h, zero_mul])
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 hgm
  refine ⟨g, x', L', hg0, rfl, rfl, α, β, ?_⟩
  apply mul_left_cancel₀ hg0
  linear_combination hαβ

/-- Every element is `≡ 0, 1` or `−1` modulo `λ`. -/
theorem mod_lam (y : 𝓞 K) : δ3 ∣ y ∨ δ3 ∣ y - 1 ∨ δ3 ∣ y + 1 := by
  obtain ⟨m, n, rfl⟩ := exists_coords y
  have hω : (ω : 𝓞 K) - 1 = δ3 * -(ω ^ 2) := by
    unfold δ3; linear_combination ω_sq_add + 2 * ω_cube
  have h2 := δ3_sq
  obtain ⟨q, r, hr, hqr⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2) ∧ m + n = 3 * q + r :=
    ⟨(m + n) / 3, (m + n) % 3, by omega, by omega⟩
  have e : ((m : 𝓞 K) + n * ω) = 3 * q + r + n * (ω - 1) := by
    have : ((m + n : ℤ) : 𝓞 K) = ((3 * q + r : ℤ) : 𝓞 K) := by rw [hqr]
    push_cast at this
    linear_combination this
  rcases hr with rfl | rfl | rfl
  · left
    exact ⟨-δ3 * q + n * -(ω ^ 2), by push_cast at e; linear_combination e + (q : 𝓞 K) * h2 + (n : 𝓞 K) * hω⟩
  · right; left
    exact ⟨-δ3 * q + n * -(ω ^ 2), by push_cast at e; linear_combination e + (q : 𝓞 K) * h2 + (n : 𝓞 K) * hω⟩
  · right; right
    exact ⟨-δ3 * (q + 1) + n * -(ω ^ 2), by
      push_cast at e; linear_combination e + ((q : 𝓞 K) + 1) * h2 + (n : 𝓞 K) * hω⟩

/-- At `v_λ(c) = 1`, `c ≡ ±λ (mod 3)`. -/
theorem lam_shape {c : 𝓞 K} (h1 : δ3 ∣ c) (h2 : ¬ (3 : 𝓞 K) ∣ c) :
    (3 : 𝓞 K) ∣ c - δ3 ∨ (3 : 𝓞 K) ∣ c - -δ3 := by
  obtain ⟨c', rfl⟩ := h1
  have hs := δ3_sq
  rcases mod_lam c' with ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨w, hw⟩
  · exact absurd ⟨-w, by rw [hw]; linear_combination w * hs⟩ h2
  · left; exact ⟨-w, by linear_combination δ3 * hw + w * hs⟩
  · right; exact ⟨-w, by linear_combination δ3 * hw + w * hs⟩

end Eis

end

#print axioms Eis.isCoprime_δ3_of_primary
#print axioms Eis.kub_of_ne
#print axioms Eis.cub_pow_left
#print axioms Eis.kub_lower
#print axioms Eis.kub_inv
#print axioms Eis.cub_split_left
#print axioms Eis.σO_cub_prod
#print axioms Eis.cub_S_congr
#print axioms Eis.theta_add_three
#print axioms Eis.exists_reduced
#print axioms Eis.mod_lam
#print axioms Eis.lam_shape
