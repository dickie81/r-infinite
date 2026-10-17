import KubotaMultiplier

/-! # The cusp data of a group of translates (round 370)

S5f-3d, part 2, the end of S5f-3d. For a group `(h₀, A)` of round 367 the companion paper says to
"`write $z_{\boldsymbol h}=a/c$ in lowest terms,`", notes that "`Changing representatives modulo $p$ changes
$z_{\boldsymbol h}$ by an element of $\lambda^2\OO=3\OO$,`", and then "`the Chinese remainder theorem gives
$\delta'\in\OO$ satisfying the following congruences,`" with "`In each case, put $g_1=gH^{-1}$.`" This file
constructs these data and proves the expansion of every translate of a group at its cusp.

* **A translate through a cusp matrix** (`theta_translate`, `theta_cusp_one`, `theta_cusp_lam`,
  `theta_cusp_inv`): round 368's (A.8), the series at `H` and the cusp shift, with round 369's multiplier,
  in the cases `3 ∣ c`, `v_λ(c) = 1` and `(c, λ) = 1`.
* **The arithmetic of a group** (`rP`, `grpNum`, `grpNum_sub`, `grpNum_mod`, **`trShift_eq`**): with
  `λ²h₀/L = a₀/c₀`, `r = ∏_{P∈A}π_P` and representatives `9x_Ph_P ≡ h_P (mod π_P)`, the translate point
  is `a/c + 3t` with `a = ε·grpNum` and `c = εc₀r`. The numerators of a group agree modulo `9c₀`, and
  `a ≡ s_Ph_P (mod π_P)` with `s_P = εc₀λ²(r/π_P)`.
* **Tools** (`cub_left_congr`, `exists_det_nine_b`, `exists_det_nine_d`, and others): `(e/a)₃` depends only
  on `a` modulo `9` and `e`, and Bézout with `9 ∣ b` or with `9 ∣ δ′`.
* **The cusp data of a group** (**`group_cusp`**): given the data of one of the three cases (the matrix `H`
  with its series, and the class `δ₀` of `δ′` modulo `9εc₀`), every translate is `κ₀∏_Pχ_P(s_Ph_P)²` times
  the series at `H` in the coordinates of (A.9), with the cusp shift as the phase `ψ_{λ³c}(−mδ′)`. Here
  `‖κ₀‖ = 1`, `δ′ ≡ δ₀ (mod 9εc₀)` and `δ′s_Ph_P ≡ 1 (mod π_P)`.
* **The parameters exist** (`group_params`, **`group_cusp_exists`**).
-/

open NumberField Ideal UniqueFactorizationMonoid Complex
open scoped ComplexConjugate

noncomputable section

namespace Eis

theorem nine_eq_δ3_pow : (9 : 𝓞 K) = δ3 ^ 4 := by
  have h := δ3_sq
  calc (9 : 𝓞 K) = (δ3 ^ 2) ^ 2 := by rw [h]; norm_num
    _ = δ3 ^ 4 := by ring

theorem nine_ne_zero' : (9 : 𝓞 K) ≠ 0 := by
  rw [nine_eq_δ3_pow]; exact pow_ne_zero 4 δ3_ne_zero

theorem not_isUnit_nine : ¬ IsUnit (9 : 𝓞 K) := fun h =>
  lam_not_unit (isUnit_of_dvd_unit (dvd_trans lam_dvd_three ⟨3, by norm_num⟩) h)

theorem isCoprime_nine_of_primary {a : 𝓞 K} (ha : Primary a) : IsCoprime a 9 := by
  rw [nine_eq_δ3_pow]; exact (isCoprime_δ3 ha).symm.pow_right

theorem δ3_not_mem (P : Pr) : δ3 ∉ P.1 := fun h => by
  have h3 : (3 : 𝓞 K) ∈ P.1 := by
    have := P.1.mul_mem_left (-δ3) h
    rwa [show -δ3 * δ3 = (3 : 𝓞 K) by linear_combination -δ3_sq] at this
  have h6 : (2 : 𝓞 K) * 3 ∈ P.1 := P.1.mul_mem_left _ h3
  norm_num at h6
  exact P.2.2 h6

theorem not_lam_dvd_of_isCoprime {x : 𝓞 K} (h : IsCoprime x δ3) : ¬ (ω - 1) ∣ x := fun hx =>
  lam_not_unit (h.isUnit_of_dvd' hx lam_dvd_δ3)

theorem norm_σO_cub {x b : 𝓞 K} (hb : Primary b) (hxb : IsCoprime x b) : ‖σO (cub x (span {b}))‖ = 1 := by
  have h : ‖σO (cub x (span {b}))‖ ^ 3 = 1 := by
    rw [← norm_pow, ← map_pow, cub_pow_three hb hxb, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h

/-- **`(e/a)₃` depends only on `a` modulo `9` and `e`**, for `a, a′` primary and prime to `e`. -/
theorem cub_left_congr {e a a' : 𝓞 K} (he : e ≠ 0) (ha : Primary a) (ha' : Primary a')
    (hae : IsCoprime a e) (hae' : IsCoprime a' e) (h9 : (9 : 𝓞 K) ∣ a - a') (he' : e ∣ a - a') :
    cub e (span {a}) = cub e (span {a'}) := by
  obtain ⟨u, s, t, e', he'p, -, hee⟩ := exists_S_decomp _ e rfl he
  have he'd : e' ∣ e := ⟨u * δ3 ^ s * 2 ^ t, by rw [hee]; ring⟩
  have h1 : cub e' (span {a}) = cub e' (span {a'}) := by
    rw [cub_recip he'p ha (hae.symm.of_isCoprime_of_dvd_left he'd),
      cub_recip he'p ha' (hae'.symm.of_isCoprime_of_dvd_left he'd)]
    exact cub_congr (dvd_trans he'd he')
  have h2 : cub 2 (span {a}) ^ t = cub 2 (span {a'}) ^ t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have h2e : (2 : 𝓞 K) ∣ e := ⟨u * δ3 ^ s * 2 ^ t' * e', by rw [hee, pow_succ]; ring⟩
      rw [cub_two_congr ha ha' (hae.of_isCoprime_of_dvd_right h2e) (hae'.of_isCoprime_of_dvd_right h2e)
        (dvd_trans h2e he')]
  simp only [hee, cub_mul_left, cub_pow_left ha, cub_pow_left ha']
  rw [cub_unit_congr u ha ha' (cub_omega_congr ha ha' h9), cub_δ3_congr ha ha' h9, h2, h1]

/-- **Bézout with `9 ∣ b`**: `aδ − bc = 1` with `9 ∣ b` and `c − wδ ≠ 0`. -/
theorem exists_det_nine_b {a c : 𝓞 K} (hac : IsCoprime a (9 * c)) (hc : c ≠ 0) {w : 𝓞 K} (hw : w ≠ 0) :
    ∃ δ b : 𝓞 K, a * δ - b * c = 1 ∧ (9 : 𝓞 K) ∣ b ∧ c - w * δ ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := hac
  by_cases h : c - w * x = 0
  · refine ⟨x + 9 * c, -(9 * (y - a)), by linear_combination hxy, ⟨-(y - a), by ring⟩, fun h' => ?_⟩
    have e : (9 : 𝓞 K) * w * c = 0 := by linear_combination h - h'
    exact mul_ne_zero (mul_ne_zero nine_ne_zero' hw) hc e
  · exact ⟨x, -(9 * y), by linear_combination hxy, ⟨-y, by ring⟩, h⟩

/-- **Bézout with `9 ∣ δ`**: `aδ − bc = 1` with `9 ∣ δ`, `δ ≠ 0` and `b ≠ 0`. -/
theorem exists_det_nine_d {a c : 𝓞 K} (hac : IsCoprime (9 * a) c) :
    ∃ δ b : 𝓞 K, a * δ - b * c = 1 ∧ (9 : 𝓞 K) ∣ δ ∧ δ ≠ 0 ∧ b ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := hac
  by_cases hx : x = 0
  · subst hx
    have hc : c ≠ 0 := by rintro rfl; simp at hxy
    refine ⟨9 * c, 9 * a - y, by linear_combination hxy, ⟨c, rfl⟩, mul_ne_zero nine_ne_zero' hc, fun h => ?_⟩
    exact not_isUnit_nine (IsUnit.of_mul_eq_one (a * c) (by linear_combination hxy + c * h))
  · refine ⟨9 * x, -y, by linear_combination hxy, ⟨x, rfl⟩, mul_ne_zero nine_ne_zero' hx, fun hy => ?_⟩
    exact not_isUnit_nine (IsUnit.of_mul_eq_one (x * a) (by linear_combination hxy + c * hy))

/-- The coordinates of (A.9): `g⁻¹(z + a/c, v) = (−d/c − W, V)`. -/
def cuspW (c : 𝓞 K) (z : ℂ) (v : ℝ) : ℂ := conj z / (σO c ^ 2 * ((Complex.normSq z + v ^ 2 : ℝ) : ℂ))

def cuspV (c : 𝓞 K) (z : ℂ) (v : ℝ) : ℝ := v / (Complex.normSq (σO c) * (Complex.normSq z + v ^ 2))

theorem cuspV_pos {c : 𝓞 K} (hc : c ≠ 0) (z : ℂ) {v : ℝ} (hv : 0 < v) : 0 < cuspV c z v := by
  have hC : σO c ≠ 0 := fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  unfold cuspV
  have := Complex.normSq_nonneg z
  exact div_pos hv (mul_pos (Complex.normSq_pos.2 hC) (by positivity))

/-- **A translate through a cusp matrix**: (A.8), the cusp table's series at `H`, and the cusp shift. -/
theorem theta_translate {θ : ℂ → ℝ → ℂ}
    (hK3 : ∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)
    {H : Matrix (Fin 2) (Fin 2) (𝓞 K)} {cH : ℂ} {dH : 𝓞 K → ℂ}
    (hser : ∀ z v, 0 < v → atG θ (H.map σO) z v = thSer cH dH z v)
    {a b c d : 𝓞 K} (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    {g₁ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hg : !![a, b; c, d] = g₁ * H) (hg₁ : g₁.det = 1)
    (h3 : ModThree g₁) (hH : H.det = 1) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    θ (z + σO a / σO c) v =
      kub g₁ * thSer cH (fun m => dH m * ψc (δ3 ^ 3 * c) (-(m * d))) (-cuspW c z v) (cuspV c z v) := by
  have hV := cuspV_pos hc z hv
  unfold cuspV at hV
  unfold cuspW cuspV
  rw [theta_at_cusp hK3 hdet hc hg hg₁ h3 hH z hv, hser _ _ hV, thSer_cusp_shift]

theorem modThree_of {p q r s : 𝓞 K} (hp : (3 : 𝓞 K) ∣ p - 1) (hq : (3 : 𝓞 K) ∣ q) (hr : (3 : 𝓞 K) ∣ r)
    (hs : (3 : 𝓞 K) ∣ s - 1) : ModThree !![p, q; r, s] := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hp
  · simpa using hq
  · simpa using hr
  · simpa using hs

/-- The case `3 ∣ c`: `H = I`, `κ = (c/a)₃`. -/
theorem theta_cusp_one {θ : ℂ → ℝ → ℂ}
    (hK3 : ∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)
    {cH : ℂ} {dH : 𝓞 K → ℂ}
    (hser : ∀ z v, 0 < v → atG θ ((1 : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) z v = thSer cH dH z v)
    {a b c d : 𝓞 K} (hdet : a * d - b * c = 1) (hc : c ≠ 0) (ha : Primary a) (hb : (3 : 𝓞 K) ∣ b)
    (hc3 : (3 : 𝓞 K) ∣ c) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    θ (z + σO a / σO c) v = σO (cub c (span {a})) *
      thSer cH (fun m => dH m * ψc (δ3 ^ 3 * c) (-(m * d))) (-cuspW c z v) (cuspV c z v) := by
  have e10 : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = c := rfl
  have e00 : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0 = a := rfl
  have hd1 : (3 : 𝓞 K) ∣ d - 1 := by
    obtain ⟨t, ht⟩ := ha
    obtain ⟨k, hk⟩ := hc3
    exact ⟨b * k - t * d, by linear_combination hdet + b * hk - d * ht⟩
  have h3 : ModThree (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) := modThree_of ha hb hc3 hd1
  rw [theta_translate hK3 hser hdet hc (mul_one _).symm (by rw [Matrix.det_fin_two_of]; exact hdet) h3
    Matrix.det_one z hv, kub_of_ne (by rw [e10]; exact hc), e10, e00]

/-- The case `v_λ(c) = 1`: `H = (1, 0; u₀, 1)`, `κ = (c/a)₃`. -/
theorem theta_cusp_lam {θ : ℂ → ℝ → ℂ}
    (hK3 : ∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)
    {u₀ : 𝓞 K} {cH : ℂ} {dH : 𝓞 K → ℂ}
    (hser : ∀ z v, 0 < v → atG θ ((!![1, 0; u₀, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) z v =
      thSer cH dH z v)
    {a b c d : 𝓞 K} (hdet : a * d - b * c = 1) (hc : c ≠ 0) (ha : Primary a) (hb : (9 : 𝓞 K) ∣ b)
    (hu : u₀ = δ3 ∨ u₀ = -δ3) (hcu : (3 : 𝓞 K) ∣ c - u₀) (hC : c - u₀ * d ≠ 0) (z : ℂ) {v : ℝ}
    (hv : 0 < v) :
    θ (z + σO a / σO c) v = σO (cub c (span {a})) *
      thSer cH (fun m => dH m * ψc (δ3 ^ 3 * c) (-(m * d))) (-cuspW c z v) (cuspV c z v) := by
  have hb3 : (3 : 𝓞 K) ∣ b := dvd_trans ⟨3, by norm_num⟩ hb
  have hd1 : (3 : 𝓞 K) ∣ d - 1 := by
    obtain ⟨t, ht⟩ := ha
    obtain ⟨k, hk⟩ := hb3
    exact ⟨k * c - t * d, by linear_combination hdet + c * hk - d * ht⟩
  have hg : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      !![a - u₀ * b, b; c - u₀ * d, d] * !![1, 0; u₀, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hg₁ : (!![a - u₀ * b, b; c - u₀ * d, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet
  have hH : (!![1, 0; u₀, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
    rw [Matrix.det_fin_two_of]; ring
  have h3 : ModThree (!![a - u₀ * b, b; c - u₀ * d, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) := by
    obtain ⟨t, ht⟩ := ha
    obtain ⟨k, hk⟩ := hb3
    obtain ⟨m, hm⟩ := hcu
    obtain ⟨n, hn⟩ := hd1
    exact modThree_of ⟨t - u₀ * k, by linear_combination ht - u₀ * hk⟩ ⟨k, hk⟩
      ⟨m - u₀ * n, by linear_combination hm - u₀ * hn⟩ ⟨n, hn⟩
  rw [theta_translate hK3 hser hdet hc hg hg₁ h3 hH z hv, kub_lower hdet ha hb hu hC]

/-- The case `(c, λ) = 1`: `H = (u, −1; 1, 0)`, `κ = (a/c)₃`. -/
theorem theta_cusp_inv {θ : ℂ → ℝ → ℂ}
    (hK3 : ∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)
    {u : 𝓞 K} {cH : ℂ} {dH : 𝓞 K → ℂ}
    (hser : ∀ z v, 0 < v → atG θ ((!![u, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) z v =
      thSer cH dH z v)
    {a b c d : 𝓞 K} (hdet : a * d - b * c = 1) (hc : Primary c) (hd9 : (9 : 𝓞 K) ∣ d) (hd0 : d ≠ 0)
    (hb0 : b ≠ 0) (hau : (3 : 𝓞 K) ∣ a - u) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    θ (z + σO a / σO c) v = σO (cub a (span {c})) *
      thSer cH (fun m => dH m * ψc (δ3 ^ 3 * c) (-(m * d))) (-cuspW c z v) (cuspV c z v) := by
  have hd3 : (3 : 𝓞 K) ∣ d := dvd_trans ⟨3, by norm_num⟩ hd9
  have hg : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      !![-b, a + u * b; -d, c + u * d] * !![u, -1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hg₁ : (!![-b, a + u * b; -d, c + u * d] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet
  have hH : (!![u, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
    rw [Matrix.det_fin_two_of]; ring
  have h3 : ModThree (!![-b, a + u * b; -d, c + u * d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) := by
    obtain ⟨t, ht⟩ := hc
    obtain ⟨k, hk⟩ := hd3
    obtain ⟨m, hm⟩ := hau
    have hb1 : (3 : 𝓞 K) ∣ -b - 1 := ⟨-(a * k) + b * t, by linear_combination hdet - a * hk + b * ht⟩
    obtain ⟨n, hn⟩ := hb1
    exact modThree_of ⟨n, hn⟩ ⟨m - u * n, by linear_combination hm - u * hn⟩
      ⟨-k, by linear_combination -hk⟩ ⟨t + u * k, by linear_combination ht + u * hk⟩
  have hc0 : c ≠ 0 := primary_ne_zero hc
  rw [theta_translate hK3 hser hdet hc0 hg hg₁ h3 hH z hv, kub_inv hdet hc hd9 hd0 hb0]

/-- The product `r/π_P` of the other primes of `A`. -/
def rP (A : Finset Pr) (P : Pr) : 𝓞 K := ∏ Q ∈ A.erase P, πP Q

theorem mul_rP {A : Finset Pr} {P : Pr} (hP : P ∈ A) : πP P * rP A P = ∏ Q ∈ A, πP Q :=
  Finset.mul_prod_erase A (fun Q => πP Q) hP

theorem rP_not_mem (A : Finset Pr) (P : Pr) : rP A P ∉ P.1 := by
  rw [← isCoprime_πP_iff]
  exact IsCoprime.prod_left fun Q hQ => isCoprime_πP (Finset.ne_of_mem_erase hQ)

theorem πP_dvd_rP {A : Finset Pr} {P Q : Pr} (hP : P ∈ A) (hQP : Q ≠ P) : πP P ∣ rP A Q :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hQP.symm, hP⟩)

theorem πP_dvd_prod {A : Finset Pr} {P : Pr} (hP : P ∈ A) : πP P ∣ ∏ Q ∈ A, πP Q :=
  Finset.dvd_prod_of_mem _ hP

theorem rP_ne_zero (A : Finset Pr) (P : Pr) : rP A P ≠ 0 := fun e =>
  rP_not_mem A P (e ▸ P.1.zero_mem)

/-- **The numerator of a translate**: `a₀r + c₀Σ_{P∈A}λ²(9x_P h_P)(r/π_P)`, with the representatives
`9x_P h_P ≡ h_P (mod π_P)` divisible by `9`. -/
def grpNum (a₀ c₀ : 𝓞 K) (x : Pr → 𝓞 K) (A : Finset Pr) (h : (P : A) → 𝓞 K ⧸ span {πP P.1}) : 𝓞 K :=
  a₀ * ∏ P ∈ A, πP P + c₀ * ∑ P : A, δ3 ^ 2 * (9 * x P.1 * repQ (πP P.1) (h P)) * rP A P.1

/-- The numerators of a group agree modulo `9c₀`. -/
theorem grpNum_sub (a₀ c₀ : 𝓞 K) (x : Pr → 𝓞 K) (A : Finset Pr) (h : (P : A) → 𝓞 K ⧸ span {πP P.1}) :
    9 * c₀ ∣ grpNum a₀ c₀ x A h - a₀ * ∏ P ∈ A, πP P :=
  ⟨∑ P : A, δ3 ^ 2 * (x P.1 * repQ (πP P.1) (h P)) * rP A P.1, by
    unfold grpNum
    rw [add_sub_cancel_left, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ => by ring⟩

/-- The numerator modulo `π_P`: `≡ c₀λ²(r/π_P)h_P`. -/
theorem grpNum_mod (a₀ c₀ : 𝓞 K) {x : Pr → 𝓞 K} {A : Finset Pr} (h : (P : A) → 𝓞 K ⧸ span {πP P.1})
    (P : A) (hx : πP P.1 ∣ 9 * x P.1 - 1) :
    πP P.1 ∣ grpNum a₀ c₀ x A h - c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P) := by
  classical
  unfold grpNum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ P)]
  have h2 : πP P.1 ∣ ∑ Q ∈ Finset.univ.erase P, δ3 ^ 2 * (9 * x Q.1 * repQ (πP Q.1) (h Q)) * rP A Q.1 :=
    Finset.dvd_sum fun Q hQ =>
      Dvd.dvd.mul_left (πP_dvd_rP P.2 (fun e => (Finset.ne_of_mem_erase hQ) (Subtype.ext e))) _
  obtain ⟨k1, hk1⟩ := πP_dvd_prod P.2
  obtain ⟨k2, hk2⟩ := h2
  obtain ⟨k3, hk3⟩ := hx
  refine ⟨a₀ * k1 + c₀ * k2 + c₀ * δ3 ^ 2 * k3 * repQ (πP P.1) (h P) * rP A P.1, ?_⟩
  rw [hk1, hk2]
  linear_combination (c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) * hk3

/-- **A translate point as a fraction**: `z_h = a/c + 3t` with `a = ε·grpNum` and `c = εc₀r`. -/
theorem trShift_eq {L : 𝓞 K} (hL : L ≠ 0) (h₀ : 𝓞 K ⧸ span {L}) (A : Finset Pr)
    (h : (P : A) → 𝓞 K ⧸ span {πP P.1}) {g₀ a₀ c₀ : 𝓞 K} (hg : δ3 ^ 2 * repQ L h₀ = g₀ * a₀)
    (hLg : L = g₀ * c₀) {x : Pr → 𝓞 K} (hx : ∀ P ∈ A, πP P ∣ 9 * x P - 1) (ε : (𝓞 K)ˣ) :
    ∃ t : 𝓞 K, trShift L ⟨(h₀, A), h⟩ =
      σO ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) / σO ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) + σO (3 * t) := by
  classical
  have hσ : ∀ y : 𝓞 K, y ≠ 0 → σO y ≠ 0 := fun y hy e => hy (σO_injective (e.trans (map_zero σO).symm))
  have hc₀ : c₀ ≠ 0 := by rintro rfl; exact hL (by rw [hLg, mul_zero])
  have hg₀ : g₀ ≠ 0 := by rintro rfl; exact hL (by rw [hLg, zero_mul])
  have hr0 := prod_πP_ne_zero A
  have hπ : ∀ P : A, σO (πP P.1) ≠ 0 := fun P => hσ _ (ne_zero_of_maximal _)
  have hr : ∀ P : A, σO (∏ Q ∈ A, πP Q) = σO (πP P.1) * σO (rP A P.1) := fun P => by
    rw [← map_mul, mul_rP P.2]
  have hx' : ∀ P : A, ∃ k, 9 * x P.1 - 1 = πP P.1 * k := fun P => hx P.1 P.2
  choose k hk using hx'
  refine ⟨∑ P : A, repQ (πP P.1) (h P) * k P, ?_⟩
  have e0 : σO (δ3 ^ 2 * repQ L h₀) / σO L = σO a₀ / σO c₀ := by
    rw [hg, hLg, map_mul, map_mul, mul_div_mul_left _ _ (hσ _ hg₀)]
  have eP : ∀ P : A, σO (δ3 ^ 2 * repQ (πP P.1) (h P)) / σO (πP P.1) =
      σO (δ3 ^ 2 * (9 * x P.1 * repQ (πP P.1) (h P))) / σO (πP P.1) +
        σO (3 * (repQ (πP P.1) (h P) * k P)) := by
    intro P
    rw [div_add' _ _ _ (hπ P), div_left_inj' (hπ P), ← map_mul, ← map_add]
    congr 1
    linear_combination (-(δ3 ^ 2 * repQ (πP P.1) (h P))) * hk P +
      (-(repQ (πP P.1) (h P) * k P * πP P.1)) * δ3_sq
  have efr : σO ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) / σO ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) =
      σO a₀ / σO c₀ + ∑ P : A, σO (δ3 ^ 2 * (9 * x P.1 * repQ (πP P.1) (h P))) / σO (πP P.1) := by
    have hS : ∑ P : A, σO (δ3 ^ 2 * (9 * x P.1 * repQ (πP P.1) (h P))) / σO (πP P.1) =
        σO (∑ P : A, δ3 ^ 2 * (9 * x P.1 * repQ (πP P.1) (h P)) * rP A P.1) / σO (∏ Q ∈ A, πP Q) := by
      rw [map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [map_mul _ _ (rP A P.1), hr P, mul_div_mul_right _ _ (hσ _ (rP_ne_zero A P.1))]
    rw [hS, div_add_div _ _ (hσ _ hc₀) (hσ _ hr0),
      show (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P = ε * (c₀ * ∏ P ∈ A, πP P) by ring, map_mul,
      map_mul σO (ε : 𝓞 K), mul_div_mul_left _ _ (hσ _ ε.ne_zero), map_mul σO c₀]
    unfold grpNum
    rw [map_add, map_mul, map_mul]
  show σO (δ3 ^ 2 * repQ L h₀) / σO L + ∑ P : A, σO (δ3 ^ 2 * repQ (πP P.1) (h P)) / σO (πP P.1) = _
  rw [e0, Finset.sum_congr rfl fun P _ => eP P, Finset.sum_add_distrib, efr, ← map_sum, ← Finset.mul_sum]
  ring

theorem isCoprime_of_dvd_sub {a e D : 𝓞 K} (he : IsCoprime e D) (h : D ∣ a - e) : IsCoprime a D := by
  obtain ⟨u, v, huv⟩ := he
  obtain ⟨k, hk⟩ := h
  exact ⟨u, v - u * k, by linear_combination huv + u * hk⟩

theorem not_mem_of_isCoprime_πP {P : Pr} {x : 𝓞 K} (h : IsCoprime x (πP P)) : x ∉ P.1 :=
  (isCoprime_πP_iff P x).1 h

/-- The factor `s_P = εc₀λ²(r/π_P)` is prime to `π_P`. -/
theorem cuspS_not_mem {A : Finset Pr} {c₀ : 𝓞 K} (ε : (𝓞 K)ˣ) {P : Pr} (hc : c₀ ∉ P.1) :
    (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P ∉ P.1 := by
  refine not_mem_of_isCoprime_πP (((((isCoprime_πP_iff P _).2 (unit_not_mem P ε)).mul_left
    ((isCoprime_πP_iff P _).2 hc)).mul_left ((isCoprime_πP_iff P _).2 (δ3_not_mem P)).pow_left).mul_left
    ((isCoprime_πP_iff P _).2 (rP_not_mem A P)))

/-- The facts shared by the three cases, for one translate of a group. -/
theorem group_facts {L : 𝓞 K} (A : Finset Pr) (hA : ∀ P ∈ A, L ∉ P.1) {g₀ a₀ c₀ : 𝓞 K}
    (hLg : L = g₀ * c₀) (hac : IsCoprime a₀ c₀) {x : Pr → 𝓞 K} (hx : ∀ P ∈ A, πP P ∣ 9 * x P - 1)
    (ε : (𝓞 K)ˣ) (h : (P : A) → 𝓞 K ⧸ span {πP P.1}) (hh : ∀ P, h P ≠ 0) :
    9 * ((ε : 𝓞 K) * c₀) ∣ (ε : 𝓞 K) * grpNum a₀ c₀ x A h - (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) ∧
      IsCoprime ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)) ((ε : 𝓞 K) * c₀) ∧
      IsCoprime ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) ((ε : 𝓞 K) * c₀) ∧
      IsCoprime ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) (∏ P ∈ A, πP P) ∧
      ∀ P : A, (ε : 𝓞 K) * grpNum a₀ c₀ x A h -
        (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P) ∈ P.1.1 := by
  have hc₀P : ∀ P ∈ A, c₀ ∉ P.1 := fun P hP hm => hA P hP (by rw [hLg]; exact P.1.mul_mem_left _ hm)
  have hrc : IsCoprime (∏ P ∈ A, πP P) c₀ :=
    IsCoprime.prod_left fun P hP => ((isCoprime_πP_iff P c₀).2 (hc₀P P hP)).symm
  have h1 : 9 * ((ε : 𝓞 K) * c₀) ∣ (ε : 𝓞 K) * grpNum a₀ c₀ x A h - (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) := by
    obtain ⟨k, hk⟩ := grpNum_sub a₀ c₀ x A h
    exact ⟨k, by linear_combination (ε : 𝓞 K) * hk⟩
  have h2 : IsCoprime ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)) ((ε : 𝓞 K) * c₀) :=
    (isCoprime_mul_unit_left ε.isUnit _ _).2 (hac.mul_left hrc)
  have h3 := isCoprime_of_dvd_sub h2 (dvd_trans (dvd_mul_left _ _) h1)
  have hmod : ∀ P : A, (ε : 𝓞 K) * grpNum a₀ c₀ x A h -
      (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P) ∈ P.1.1 := by
    intro P
    obtain ⟨k, hk⟩ := grpNum_mod a₀ c₀ h P (hx P.1 P.2)
    rw [← (πP_spec P.1).2, Ideal.mem_span_singleton]
    exact ⟨(ε : 𝓞 K) * k, by linear_combination (ε : 𝓞 K) * hk⟩
  refine ⟨h1, h2, h3, IsCoprime.prod_right fun P hP => ?_, hmod⟩
  rw [isCoprime_πP_iff]
  intro hm
  have hs := cuspS_not_mem (A := A) ε (hc₀P P hP)
  have hy := repQ_not_mem P (hh ⟨P, hP⟩)
  have := P.1.sub_mem hm (hmod ⟨P, hP⟩)
  rw [sub_sub_cancel] at this
  rcases P.2.1.isPrime.mem_or_mem this with h' | h'
  · exact hs h'
  · exact hy h'

/-- **The cusp data of a group of translates** (S5f-3d): for a group `(h₀, A)` of round 367, with
`λ²h₀/L = a₀/c₀` in lowest terms, representatives `9x_P h_P ≡ h_P (mod π_P)`, a unit `ε`, and the
data of one of the three cases (the matrix `H`, with `θ(Hw)` a theta-type series, and the class `δ₀`
of `δ′` modulo `9εc₀`), every translate is `κ₀∏_Pχ_P(s_Ph_P)²` times the series at `H` in the
coordinates of (A.9), with the cusp shift as a phase. Here `c = εc₀r`, `s_P = εc₀λ²(r/π_P)`,
`δ′ ≡ δ₀ (mod 9εc₀)` and `δ′s_Ph_P ≡ 1 (mod π_P)`. -/
theorem group_cusp {θ : ℂ → ℝ → ℂ}
    (hK3 : ∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)
    {L : 𝓞 K} (hL : L ≠ 0) (h₀ : 𝓞 K ⧸ span {L}) (A : Finset Pr) (hA : ∀ P ∈ A, L ∉ P.1)
    {g₀ a₀ c₀ : 𝓞 K} (hg : δ3 ^ 2 * repQ L h₀ = g₀ * a₀) (hLg : L = g₀ * c₀) (hac : IsCoprime a₀ c₀)
    {x : Pr → 𝓞 K} (hx : ∀ P ∈ A, πP P ∣ 9 * x P - 1) (ε : (𝓞 K)ˣ)
    {H : Matrix (Fin 2) (Fin 2) (𝓞 K)} {cH : ℂ} {dH : 𝓞 K → ℂ}
    (hser : ∀ z v, 0 < v → atG θ (H.map σO) z v = thSer cH dH z v) {δ₀ : 𝓞 K}
    (hcase : (Primary ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)) ∧
        9 * ((ε : 𝓞 K) * c₀) ∣ (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) * δ₀ - 1 ∧
        ((3 ∣ c₀ ∧ H = 1) ∨ ∃ u₀, (u₀ = δ3 ∨ u₀ = -δ3) ∧
          3 ∣ (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P - u₀ ∧ H = !![1, 0; u₀, 1])) ∨
      (Primary ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) ∧ 9 ∣ δ₀ ∧
        (ε : 𝓞 K) * c₀ ∣ (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) * δ₀ - 1 ∧
        ∃ u, 3 ∣ (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) - u ∧ H = !![u, -1; 1, 0])) :
    ∃ κ₀ : ℂ, ‖κ₀‖ = 1 ∧ ∀ h : (P : A) → 𝓞 K ⧸ span {πP P.1}, (∀ P, h P ≠ 0) →
      ∃ δ : 𝓞 K, 9 * ((ε : 𝓞 K) * c₀) ∣ δ - δ₀ ∧
        (∀ P : A, δ * ((ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) - 1 ∈ P.1.1) ∧
        ∀ z (v : ℝ), 0 < v → θ (z + trShift L ⟨(h₀, A), h⟩) v =
          κ₀ * (∏ P : A, chiP P.1.1 ((ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) ^ 2) *
            thSer cH (fun m => dH m * ψc (δ3 ^ 3 * ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P)) (-(m * δ)))
              (-cuspW ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) z v)
              (cuspV ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) z v) := by
  classical
  have hc₀ : c₀ ≠ 0 := by rintro rfl; exact hL (by rw [hLg, mul_zero])
  have hr0 := prod_πP_ne_zero A
  have hD0 : (ε : 𝓞 K) * c₀ ≠ 0 := mul_ne_zero ε.ne_zero hc₀
  have hc0 : (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P ≠ 0 := mul_ne_zero hD0 hr0
  have hrp := primary_prod_πP A
  -- the common steps: the translate point, and the factor `∏_Pχ_P(a)²`
  have hpoint : ∀ h : (P : A) → 𝓞 K ⧸ span {πP P.1}, ∀ z (v : ℝ), 0 < v →
      θ (z + trShift L ⟨(h₀, A), h⟩) v = θ (z + σO ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) /
        σO ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P)) v := by
    intro h z v hv
    obtain ⟨t, ht⟩ := trShift_eq hL h₀ A h hg hLg hx ε
    rw [ht, ← add_assoc, theta_add_three hK3 t _ hv]
  have hchi : ∀ h : (P : A) → 𝓞 K ⧸ span {πP P.1}, (∀ P : A, (ε : 𝓞 K) * grpNum a₀ c₀ x A h -
      (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P) ∈ P.1.1) →
      σO (cub ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) (span {∏ P ∈ A, πP P})) =
        ∏ P : A, chiP P.1.1 ((ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) ^ 2 := by
    intro h hm
    rw [σO_cub_prod, ← Finset.prod_coe_sort A]
    exact Finset.prod_congr rfl fun P _ => by rw [chiP_congr (hm P)]
  have hmodP : ∀ h : (P : A) → 𝓞 K ⧸ span {πP P.1}, ∀ δ b : 𝓞 K,
      (ε : 𝓞 K) * grpNum a₀ c₀ x A h * δ - b * ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) = 1 →
      (∀ P : A, (ε : 𝓞 K) * grpNum a₀ c₀ x A h -
        (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P) ∈ P.1.1) →
      ∀ P : A, δ * ((ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) - 1 ∈ P.1.1 := by
    intro h δ b hdet hm P
    have hcP : (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P ∈ P.1.1 := by
      rw [← (πP_spec P.1).2, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_left (πP_dvd_prod P.2) _
    have e : δ * ((ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) - 1 =
        b * ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) - δ * ((ε : 𝓞 K) * grpNum a₀ c₀ x A h -
          (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) := by
      linear_combination hdet
    rw [e]
    exact P.1.1.sub_mem (P.1.1.mul_mem_left _ hcP) (P.1.1.mul_mem_left _ (hm P))
  rcases hcase with ⟨hprim, hδ₀, hH⟩ | ⟨hprimc, hδ9, hδ₀, u, hu, rfl⟩
  · -- `a` primary: the cases `3 ∣ c` and `v_λ(c) = 1`
    refine ⟨σO (cub ((ε : 𝓞 K) * c₀) (span {(ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)})), norm_σO_cub hprim
      (group_facts A hA hLg hac hx ε (fun P => 1) (fun P => one_ne_zero)).2.1.symm, fun h hh => ?_⟩
    obtain ⟨h1, h2, h3, h4, hm⟩ := group_facts A hA hLg hac hx ε h hh
    have ha : Primary ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) := by
      obtain ⟨t, ht⟩ := hprim
      obtain ⟨k, hk⟩ := h1
      exact ⟨t + 3 * ((ε : 𝓞 K) * c₀) * k, by linear_combination ht + hk⟩
    have hac9 : IsCoprime ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) (9 * ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P)) :=
      (isCoprime_nine_of_primary ha).mul_right (h3.mul_right h4)
    have hw : ∃ w : 𝓞 K, w ≠ 0 ∧ ((3 ∣ c₀ ∧ H = 1) ∨ ((w = δ3 ∨ w = -δ3) ∧
        3 ∣ (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P - w ∧ H = !![1, 0; w, 1])) := by
      rcases hH with hH | ⟨u₀, hu₀, hcu, hH⟩
      · exact ⟨1, one_ne_zero, Or.inl hH⟩
      · refine ⟨u₀, ?_, Or.inr ⟨hu₀, hcu, hH⟩⟩
        rcases hu₀ with rfl | rfl
        · exact δ3_ne_zero
        · exact neg_ne_zero.2 δ3_ne_zero
    obtain ⟨w, hw0, hwH⟩ := hw
    obtain ⟨δ, b, hdet, hb9, hC⟩ := exists_det_nine_b hac9 hc0 hw0
    -- `δ ≡ δ₀ (mod 9εc₀)`
    have hδ : 9 * ((ε : 𝓞 K) * c₀) ∣ δ - δ₀ := by
      have hco : IsCoprime (9 * ((ε : 𝓞 K) * c₀)) ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)) :=
        (isCoprime_nine_of_primary hprim).symm.mul_left h2.symm
      refine hco.dvd_of_dvd_mul_left ?_
      obtain ⟨k1, hk1⟩ := h1
      obtain ⟨k2, hk2⟩ := hδ₀
      obtain ⟨k3, hk3⟩ := hb9
      exact ⟨-(k1 * δ) + k3 * ∏ P ∈ A, πP P - k2, by
        linear_combination -(δ * hk1) - hk2 + hdet + ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) * hk3⟩
    refine ⟨δ, hδ, hmodP h δ b (by linear_combination hdet) hm, fun z v hv => ?_⟩
    have hsplit : σO (cub ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) (span {(ε : 𝓞 K) * grpNum a₀ c₀ x A h})) =
        σO (cub ((ε : 𝓞 K) * c₀) (span {(ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)})) *
          ∏ P : A, chiP P.1.1 ((ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) ^ 2 := by
      rw [cub_split_left _ ha hrp h4, map_mul, hchi h hm,
        cub_left_congr hD0 ha hprim h3 h2 (dvd_trans (dvd_mul_right _ _) h1) (dvd_trans (dvd_mul_left _ _) h1)]
    rw [hpoint h z v hv, ← hsplit]
    rcases hwH with ⟨hc3, rfl⟩ | ⟨hu₀, hcu, rfl⟩
    · exact theta_cusp_one hK3 hser hdet hc0 ha (dvd_trans ⟨3, by norm_num⟩ hb9)
        (Dvd.dvd.mul_right (Dvd.dvd.mul_left hc3 _) _) z hv
    · exact theta_cusp_lam hK3 hser hdet hc0 ha hb9 hu₀ hcu hC z hv
  · -- `c` primary: the case `(c, λ) = 1`
    have hD : Primary ((ε : 𝓞 K) * c₀) := by
      obtain ⟨t, ht⟩ := hprimc
      obtain ⟨k, hk⟩ := hrp
      exact ⟨t - (ε : 𝓞 K) * c₀ * k, by linear_combination ht - (ε : 𝓞 K) * c₀ * hk⟩
    refine ⟨σO (cub ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)) (span {(ε : 𝓞 K) * c₀})), norm_σO_cub hD
      (group_facts A hA hLg hac hx ε (fun P => 1) (fun P => one_ne_zero)).2.1, fun h hh => ?_⟩
    obtain ⟨h1, h2, h3, h4, hm⟩ := group_facts A hA hLg hac hx ε h hh
    have hco : IsCoprime (9 * ((ε : 𝓞 K) * grpNum a₀ c₀ x A h)) ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) :=
      (isCoprime_nine_of_primary hprimc).symm.mul_left (h3.mul_right h4)
    obtain ⟨δ, b, hdet, hδ9', hδ0, hb0⟩ := exists_det_nine_d hco
    have hδ : 9 * ((ε : 𝓞 K) * c₀) ∣ δ - δ₀ := by
      have hDδ : (ε : 𝓞 K) * c₀ ∣ δ - δ₀ := by
        refine h2.symm.dvd_of_dvd_mul_left ?_
        obtain ⟨k1, hk1⟩ := dvd_trans (dvd_mul_left _ _) h1
        obtain ⟨k2, hk2⟩ := hδ₀
        exact ⟨-(k1 * δ) + b * ∏ P ∈ A, πP P - k2, by linear_combination -(δ * hk1) - hk2 + hdet⟩
      exact (isCoprime_nine_of_primary hD).symm.mul_dvd (dvd_sub hδ9' hδ9) hDδ
    refine ⟨δ, hδ, hmodP h δ b (by linear_combination hdet) hm, fun z v hv => ?_⟩
    have hsplit : σO (cub ((ε : 𝓞 K) * grpNum a₀ c₀ x A h) (span {(ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P})) =
        σO (cub ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)) (span {(ε : 𝓞 K) * c₀})) *
          ∏ P : A, chiP P.1.1 ((ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1 * repQ (πP P.1) (h P)) ^ 2 := by
      rw [cub_mul_span _ hD0 hr0, map_mul, hchi h hm, cub_congr (dvd_trans (dvd_mul_left _ _) h1)]
    have hau : (3 : 𝓞 K) ∣ (ε : 𝓞 K) * grpNum a₀ c₀ x A h - u := by
      obtain ⟨k1, hk1⟩ := dvd_trans (⟨3 * ((ε : 𝓞 K) * c₀), by ring⟩ : (3 : 𝓞 K) ∣ 9 * ((ε : 𝓞 K) * c₀)) h1
      obtain ⟨k2, hk2⟩ := hu
      exact ⟨k1 + k2, by linear_combination hk1 + hk2⟩
    rw [hpoint h z v hv, ← hsplit]
    exact theta_cusp_inv hK3 hser hdet hprimc hδ9' hδ0 hb0 hau z hv

/-- An element not divisible by `λ` is prime to `λ`. -/
theorem isCoprime_δ3_of_not_dvd {c : 𝓞 K} (h : ¬ δ3 ∣ c) : IsCoprime c δ3 := by
  rcases mod_lam c with h0 | ⟨k, hk⟩ | ⟨k, hk⟩
  · exact absurd h0 h
  · exact ⟨1, -k, by linear_combination hk⟩
  · exact ⟨-1, k, by linear_combination -hk⟩

theorem isCoprime_three_of_primary {r : 𝓞 K} (hr : Primary r) : IsCoprime (3 : 𝓞 K) r := by
  rw [show (3 : 𝓞 K) = -(δ3 ^ 2) by linear_combination δ3_sq]
  exact (isCoprime_δ3 hr).pow_left.neg_left

/-- `9 ≡ 1/x_P`: every `π_P` has an inverse of `9` modulo it. -/
theorem exists_nine_inv (P : Pr) : ∃ x : 𝓞 K, πP P ∣ 9 * x - 1 := by
  have h9 : (9 : 𝓞 K) ∉ P.1 := by
    rw [nine_eq_δ3_pow]
    exact fun hm => δ3_not_mem P (P.2.1.isPrime.mem_of_pow_mem 4 hm)
  obtain ⟨p, q, hpq⟩ := (isCoprime_πP_iff P 9).2 h9
  exact ⟨p, -q, by linear_combination hpq⟩

/-- **The parameters of a group exist**: lowest terms, the inverses of `9`, the unit `ε`, the case data
`(H, δ₀)`, and the series at `H` from the cusp table. -/
theorem group_params {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (h₀ : 𝓞 K ⧸ span {L}) (A : Finset Pr)
    (hA : ∀ P ∈ A, L ∉ P.1) :
    ∃ (g₀ a₀ c₀ : 𝓞 K) (x : Pr → 𝓞 K) (ε : (𝓞 K)ˣ) (H : Matrix (Fin 2) (Fin 2) (𝓞 K)) (cH : ℂ)
      (dH : 𝓞 K → ℂ) (δ₀ : 𝓞 K),
      δ3 ^ 2 * repQ L h₀ = g₀ * a₀ ∧ L = g₀ * c₀ ∧ IsCoprime a₀ c₀ ∧ (∀ P, πP P ∣ 9 * x P - 1) ∧
      ThetaSupp Kc dH ∧ (∀ z v, 0 < v → atG θ (H.map σO) z v = thSer cH dH z v) ∧
      ((Primary ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)) ∧
        9 * ((ε : 𝓞 K) * c₀) ∣ (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) * δ₀ - 1 ∧
        ((3 ∣ c₀ ∧ H = 1) ∨ ∃ u₀, (u₀ = δ3 ∨ u₀ = -δ3) ∧
          3 ∣ (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P - u₀ ∧ H = !![1, 0; u₀, 1])) ∨
      (Primary ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) ∧ 9 ∣ δ₀ ∧
        (ε : 𝓞 K) * c₀ ∣ (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) * δ₀ - 1 ∧
        ∃ u, 3 ∣ (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) - u ∧ H = !![u, -1; 1, 0])) := by
  classical
  obtain ⟨g₀, a₀, c₀, -, hg, hLg, hac⟩ := exists_reduced (δ3 ^ 2 * repQ L h₀) hL
  choose x hx using exists_nine_inv
  have hc₀P : ∀ P ∈ A, c₀ ∉ P.1 := fun P hP hm => hA P hP (by rw [hLg]; exact P.1.mul_mem_left _ hm)
  have hrc : IsCoprime (∏ P ∈ A, πP P) c₀ :=
    IsCoprime.prod_left fun P hP => ((isCoprime_πP_iff P c₀).2 (hc₀P P hP)).symm
  have hrp := primary_prod_πP A
  have hrδ : IsCoprime (∏ P ∈ A, πP P) δ3 := (isCoprime_δ3 hrp).symm
  -- the series at a matrix `H` of the cusp table
  have hser : ∀ H : Matrix (Fin 2) (Fin 2) (𝓞 K),
      (H = 1 ∨ H = !![1, 0; δ3, 1] ∨ H = !![1, 0; -δ3, 1] ∨ ∃ u, H = !![u, -1; 1, 0]) →
      ∃ (cH : ℂ) (dH : 𝓞 K → ℂ), ThetaSupp Kc dH ∧
        ∀ z v, 0 < v → atG θ (H.map σO) z v = thSer cH dH z v := fun H hH => cusp_table hd H hH
  by_cases hlam : δ3 ∣ c₀
  · -- `a₀r` is prime to `λ`
    have haδ : IsCoprime a₀ δ3 := hac.of_isCoprime_of_dvd_right hlam
    obtain ⟨ε, hε⟩ := exists_primary (not_lam_dvd_of_isCoprime (haδ.mul_left hrδ))
    have hco : IsCoprime ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P)) (9 * ((ε : 𝓞 K) * c₀)) :=
      (isCoprime_nine_of_primary hε).mul_right ((isCoprime_mul_unit_left ε.isUnit _ _).2 (hac.mul_left hrc))
    obtain ⟨p, q, hpq⟩ := hco
    have hδ₀ : 9 * ((ε : 𝓞 K) * c₀) ∣ (ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P) * p - 1 :=
      ⟨-q, by linear_combination hpq⟩
    by_cases h3 : (3 : 𝓞 K) ∣ c₀
    · obtain ⟨cH, dH, hdH, hs⟩ := hser 1 (Or.inl rfl)
      exact ⟨g₀, a₀, c₀, x, ε, 1, cH, dH, p, hg, hLg, hac, hx, hdH, hs,
        Or.inl ⟨hε, hδ₀, Or.inl ⟨h3, rfl⟩⟩⟩
    · have hc3 : ¬ (3 : 𝓞 K) ∣ (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P := by
        intro h
        apply h3
        have h' : (3 : 𝓞 K) ∣ (ε : 𝓞 K) * c₀ := (isCoprime_three_of_primary hrp).dvd_of_dvd_mul_right h
        exact Units.dvd_mul_left.mp h'
      have hclam : δ3 ∣ (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P := Dvd.dvd.mul_right (Dvd.dvd.mul_left hlam _) _
      have hu₀ : ∃ u₀ : 𝓞 K, (u₀ = δ3 ∨ u₀ = -δ3) ∧ (3 : 𝓞 K) ∣ (ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P - u₀ := by
        rcases lam_shape hclam hc3 with h | h
        · exact ⟨δ3, Or.inl rfl, h⟩
        · exact ⟨-δ3, Or.inr rfl, h⟩
      obtain ⟨u₀, hu, hcu⟩ := hu₀
      obtain ⟨cH, dH, hdH, hs⟩ := hser !![1, 0; u₀, 1] (by
        rcases hu with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl)))
      exact ⟨g₀, a₀, c₀, x, ε, !![1, 0; u₀, 1], cH, dH, p, hg, hLg, hac, hx, hdH, hs,
        Or.inl ⟨hε, hδ₀, Or.inr ⟨u₀, hu, hcu, rfl⟩⟩⟩
  · -- `c₀r` is prime to `λ`
    have hcδ := isCoprime_δ3_of_not_dvd hlam
    obtain ⟨ε, hε⟩ := exists_primary (not_lam_dvd_of_isCoprime (hcδ.mul_left hrδ))
    have hε' : Primary ((ε : 𝓞 K) * c₀ * ∏ P ∈ A, πP P) := by rw [mul_assoc]; exact hε
    have hD9 : IsCoprime (9 : 𝓞 K) ((ε : 𝓞 K) * c₀) := by
      rw [nine_eq_δ3_pow]
      exact ((isCoprime_mul_unit_left_right ε.isUnit _ _).2 hcδ.symm).pow_left
    have hco : IsCoprime (9 * ((ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P))) ((ε : 𝓞 K) * c₀) :=
      hD9.mul_left ((isCoprime_mul_unit_left ε.isUnit _ _).2 (hac.mul_left hrc))
    obtain ⟨p, q, hpq⟩ := hco
    obtain ⟨cH, dH, hdH, hs⟩ := hser !![(ε : 𝓞 K) * (a₀ * ∏ P ∈ A, πP P), -1; 1, 0]
      (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
    exact ⟨g₀, a₀, c₀, x, ε, _, cH, dH, 9 * p, hg, hLg, hac, hx, hdH, hs,
      Or.inr ⟨hε', ⟨p, rfl⟩, ⟨-q, by linear_combination hpq⟩, _, by simp, rfl⟩⟩

/-- **The cusp data of a group** (S5f-3d), with the parameters chosen: for a group `(h₀, A)` with the
primes of `A` prime to `L`, there are `D ∣ L`, a unimodular `κ₀`, a series `(c_H, d_H)` under the
support and size condition, a class `δ₀` and factors `s_P ∉ P` such that every translate of the
group is `κ₀∏_Pχ_P(s_Ph_P)²` times the series at `−W` with the phase `ψ_{λ³c}(−mδ′)`, `c = D∏_Pπ_P`,
`δ′ ≡ δ₀ (mod 9D)` and `δ′s_Ph_P ≡ 1 (mod π_P)`. -/
theorem group_cusp_exists {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (h₀ : 𝓞 K ⧸ span {L}) (A : Finset Pr)
    (hA : ∀ P ∈ A, L ∉ P.1) :
    ∃ (D : 𝓞 K) (cH : ℂ) (dH : 𝓞 K → ℂ) (κ₀ : ℂ) (δ₀ : 𝓞 K) (s : Pr → 𝓞 K),
      D ≠ 0 ∧ D ∣ L ∧ ThetaSupp Kc dH ∧ ‖κ₀‖ = 1 ∧ (∀ P ∈ A, s P ∉ P.1) ∧
      ∀ h : (P : A) → 𝓞 K ⧸ span {πP P.1}, (∀ P, h P ≠ 0) →
        ∃ δ : 𝓞 K, 9 * D ∣ δ - δ₀ ∧ (∀ P : A, δ * (s P.1 * repQ (πP P.1) (h P)) - 1 ∈ P.1.1) ∧
          ∀ z (v : ℝ), 0 < v → θ (z + trShift L ⟨(h₀, A), h⟩) v =
            κ₀ * (∏ P : A, chiP P.1.1 (s P.1 * repQ (πP P.1) (h P)) ^ 2) *
              thSer cH (fun m => dH m * ψc (δ3 ^ 3 * (D * ∏ P ∈ A, πP P)) (-(m * δ)))
                (-cuspW (D * ∏ P ∈ A, πP P) z v) (cuspV (D * ∏ P ∈ A, πP P) z v) := by
  obtain ⟨g₀, a₀, c₀, x, ε, H, cH, dH, δ₀, hg, hLg, hac, hx, hdH, hs, hcase⟩ :=
    group_params hd hL h₀ A hA
  have hc₀ : c₀ ≠ 0 := by rintro rfl; exact hL (by rw [hLg, mul_zero])
  obtain ⟨κ₀, hκ, hall⟩ := group_cusp hd.2.2.2.2.2.2.2.2 hL h₀ A hA hg hLg hac (fun P _ => hx P) ε hs hcase
  refine ⟨(ε : 𝓞 K) * c₀, cH, dH, κ₀, δ₀, fun P => (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P,
    mul_ne_zero ε.ne_zero hc₀, ⟨(↑ε⁻¹ : 𝓞 K) * g₀, ?_⟩, hdH, hκ,
    fun P hP => cuspS_not_mem ε (fun hm => hA P hP (by rw [hLg]; exact P.1.mul_mem_left _ hm)), hall⟩
  rw [hLg]
  linear_combination (-(g₀ * c₀)) * ε.mul_inv

end Eis

end

#print axioms Eis.nine_eq_δ3_pow
#print axioms Eis.nine_ne_zero'
#print axioms Eis.not_isUnit_nine
#print axioms Eis.isCoprime_nine_of_primary
#print axioms Eis.δ3_not_mem
#print axioms Eis.not_lam_dvd_of_isCoprime
#print axioms Eis.norm_σO_cub
#print axioms Eis.cub_left_congr
#print axioms Eis.exists_det_nine_b
#print axioms Eis.exists_det_nine_d
#print axioms Eis.cuspV_pos
#print axioms Eis.theta_translate
#print axioms Eis.modThree_of
#print axioms Eis.theta_cusp_one
#print axioms Eis.theta_cusp_lam
#print axioms Eis.theta_cusp_inv
#print axioms Eis.mul_rP
#print axioms Eis.rP_not_mem
#print axioms Eis.πP_dvd_rP
#print axioms Eis.πP_dvd_prod
#print axioms Eis.rP_ne_zero
#print axioms Eis.grpNum_sub
#print axioms Eis.grpNum_mod
#print axioms Eis.trShift_eq
#print axioms Eis.isCoprime_of_dvd_sub
#print axioms Eis.not_mem_of_isCoprime_πP
#print axioms Eis.cuspS_not_mem
#print axioms Eis.group_facts
#print axioms Eis.group_cusp
#print axioms Eis.isCoprime_δ3_of_not_dvd
#print axioms Eis.isCoprime_three_of_primary
#print axioms Eis.exists_nine_inv
#print axioms Eis.group_params
#print axioms Eis.group_cusp_exists
