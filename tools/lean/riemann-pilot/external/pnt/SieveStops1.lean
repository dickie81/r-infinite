/-
# Round 604: a stop's cofactor, and the stops below the window (milestone M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements.

* `sum_cofactor`: for a `p`-rough `W ≤ N₁` with `0 < W`, the multiples `n ∈ (N₁, N₂]` of `W` that are `p`-rough are
  the `Wk` with `k ≥ 2` `p`-rough and `N₁ < Wk ≤ N₂`.
* `stops1_bound`: fix `e₀ > 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `r`
  run over `R`, each `r > 0` with every prime factor at least `z₀` and coefficients `|c_r| ≤ 1`, let `w ≥ q^{e₀}`,
  and let `q^{0.401L} ≤ X` and `Xz₀ ≤ q^{0.485L}`. Then the stops of Buchstab's tree at the threshold `X`
  (`SieveDiff.tree_weighted`), weighted by `c_r` and summed over `r`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.
* `window_bound`: the same with `r` itself in the window, `R ⊆ (P₁, P₂]`, for `S(A_r, z₀) − S(B_r, z₀)/φ(q)`.

`stops1_bound` and `window_bound` were the first case of Proposition 6's proof in `frontier/linnik/SIEVE-ROUTE.md`
§5 (`r ≤ x^{u₁}`). The proof of `linnik_2333` does not use them: `SieveProp6.prop6` runs one tree, at the threshold
`X'` (`SieveStops2`). `sum_cofactor` is used by `SieveStops2` and `SieveChain`.

The proof of the bounds: a stop `W = r∏P·p` lies in `(X, Xz₀]`, inside the lower window; its least prime is `p`
(`minFac_W`), so `W` determines `(r, P, p)` (`filter_W`, `div_W`), and the stop's cofactor is a `p`-rough `k ≥ 2`
(`sum_cofactor`). `SieveTypeIIR.typeII_rough` with `m = W` and `z(m) = minFac m` bounds the sum.

The file imports `SieveDiff.lean` and `SieveTypeIIR.lean`.
-/
import SieveDiff
import SieveTypeIIR

open Real Finset SieveFamily SieveTree

namespace SieveStops1

/-- A multiple of a `p`-rough `W ≤ N₁` in `(N₁, N₂]` is `Wk` with `k ≥ 2`; `n` is `p`-rough iff `k` is. -/
theorem sum_cofactor (f : ℕ → ℂ) {W p N₁ N₂ : ℕ} (hW : 0 < W) (hWN : W ≤ N₁) (hWp : rough p W) :
    ∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0) =
      ∑ k ∈ (Finset.Icc 2 N₂).filter (fun k => (∀ p' < p, p'.Prime → ¬ p' ∣ k) ∧ N₁ < W * k ∧ W * k ≤ N₂),
        f (W * k) := by
  rw [show (∑ n ∈ Finset.Ioc N₁ N₂, f n * (if W ∣ n ∧ rough p n then 1 else 0)) =
      ∑ n ∈ (Finset.Ioc N₁ N₂).filter (fun n => W ∣ n ∧ rough p n), f n by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp]
  refine Finset.sum_nbij' (fun n => n / W) (fun k => W * k) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, ⟨c, rfl⟩, hr⟩ := hn
    rw [Nat.mul_div_cancel_left c hW, Finset.mem_Icc]
    have hc2 : 2 ≤ c := by
      by_contra h
      interval_cases c <;> omega
    refine ⟨⟨hc2, le_trans (Nat.le_mul_of_pos_left c hW) hn2⟩,
      fun p' hp' hpp hpd => hr p' hp' hpp (dvd_mul_of_dvd_right hpd W), hn1, hn2⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hk ⊢
    obtain ⟨-, hr, h1, h2⟩ := hk
    refine ⟨⟨h1, h2⟩, dvd_mul_right W k, fun p' hp' hpp hpd => ?_⟩
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact hWp p' hp' hpp h
    · exact hr p' hp' hpp h
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2.1
  · intro k _
    exact Nat.mul_div_cancel_left k hW
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2.1]

/-! ### A stop determines its tree node -/

section Recover

variable {r p z₀ : ℕ} {P : Finset ℕ}

theorem prime_dvd_W (hp : p.Prime) (hP : P ⊆ primesIco (p + 1) z₀) (hr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ r → z₀ ≤ ℓ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ r * (∏ p' ∈ P, p') * p) : (z₀ ≤ ℓ ∧ ℓ ∣ r) ∨ ℓ ∈ P ∨ ℓ = p := by
  rcases (Nat.Prime.dvd_mul hℓ).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul hℓ).1 h with h' | h'
    · exact Or.inl ⟨hr ℓ hℓ h', h'⟩
    · obtain ⟨ℓ', hℓ', hd'⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 h'
      have hpr := (mem_primesIco.1 (hP hℓ')).2.2
      rw [(Nat.prime_dvd_prime_iff_eq hℓ hpr).1 hd']
      exact Or.inr (Or.inl hℓ')
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h))

theorem minFac_W (hp : p.Prime) (hpz : p < z₀) (hP : P ⊆ primesIco (p + 1) z₀)
    (hr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ r → z₀ ≤ ℓ) : Nat.minFac (r * (∏ p' ∈ P, p') * p) = p := by
  have hW1 : r * (∏ p' ∈ P, p') * p ≠ 1 := by
    intro h
    have := Nat.eq_one_of_mul_eq_one_left h
    exact hp.one_lt.ne' this
  refine le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_left p _)) ?_
  have hmp := Nat.minFac_prime hW1
  rcases prime_dvd_W hp hP hr hmp (Nat.minFac_dvd _) with ⟨h, -⟩ | h | h
  · omega
  · have := (mem_primesIco.1 (hP h)).1; omega
  · omega

theorem filter_W (hp : p.Prime) (hP : P ⊆ primesIco (p + 1) z₀) (hr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ r → z₀ ≤ ℓ) :
    (primesIco (p + 1) z₀).filter (· ∣ r * (∏ p' ∈ P, p') * p) = P := by
  ext ℓ
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hℓ, hd⟩
    obtain ⟨hℓ1, hℓz, hℓp⟩ := mem_primesIco.1 hℓ
    rcases prime_dvd_W hp hP hr hℓp hd with ⟨h, -⟩ | h | h
    · omega
    · exact h
    · omega
  · intro hℓ
    exact ⟨hP hℓ, dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hℓ) r) p⟩

theorem div_W (hp : p.Prime) (hP : ∀ ℓ ∈ P, 0 < ℓ) :
    r * (∏ p' ∈ P, p') * p / ((∏ p' ∈ P, p') * p) = r := by
  rw [mul_assoc]
  exact Nat.mul_div_cancel r (Nat.mul_pos (Finset.prod_pos hP) hp.pos)

end Recover

section Bound

open Classical

/-- **The stops below the window.** Fix `e₀ > 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a`
mod `q`: let `r` run over `R`, each `r > 0` with every prime factor at least `z₀` and coefficients `|c_r| ≤ 1`, let
`w ≥ q^{e₀}`, and let `q^{0.401L} ≤ X` and `Xz₀ ≤ q^{0.485L}`. Then the stops of Buchstab's tree at the threshold `X`
(`SieveDiff.tree_weighted`), weighted by `c_r` and summed over `r`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`. -/
theorem stops1_bound {e₀ : ℝ} (he₀ : 0 < e₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (X w z₀ : ℕ) (R : Finset ℕ) (c : ℕ → ℂ), (∀ r, ‖c r‖ ≤ 1) →
      (∀ r ∈ R, 0 < r ∧ ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p) →
      (q : ℝ) ^ e₀ ≤ w → (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ X →
      ((X * z₀ : ℕ) : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ‖∑ r ∈ R, c r * ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊, dw q a n *
              (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  obtain ⟨δ, hδ, q₁, hq₁⟩ := SieveTypeIIR.typeII_rough he₀
  refine ⟨δ, hδ, max q₁ 2, ?_⟩
  intro q _ hq a ha X w z₀ R c hc hR hw hX hXz
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  set N₁ := ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hN₂
  have hXzN : X * z₀ ≤ N₁ := by
    apply Nat.le_floor
    calc ((X * z₀ : ℕ) : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) := hXz
      _ ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  -- the stops
  set T := (R ×ˢ ((primesIco w z₀).sigma (fun p => (primesIco (p + 1) z₀).powerset))).filter
    (fun t => t.1 * ∏ p' ∈ t.2.2, p' ≤ X ∧ X < t.1 * (∏ p' ∈ t.2.2, p') * t.2.1) with hT
  set Wt : ℕ × (Σ _ : ℕ, Finset ℕ) → ℕ := fun t => t.1 * (∏ p' ∈ t.2.2, p') * t.2.1 with hWt
  set G : ℕ → ℂ := fun W => ∑ k ∈ (Finset.Icc 2 N₂).filter
    (fun k => (∀ p' < Nat.minFac W, p'.Prime → ¬ p' ∣ k) ∧ N₁ < W * k ∧ W * k ≤ N₂), dw q a (W * k) with hG
  have hmemT : ∀ t ∈ T, t.1 ∈ R ∧ t.2.1 ∈ primesIco w z₀ ∧ t.2.2 ⊆ primesIco (t.2.1 + 1) z₀ ∧
      t.1 * ∏ p' ∈ t.2.2, p' ≤ X ∧ X < Wt t := by
    intro t ht
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_sigma, Finset.mem_powerset] at ht
    exact ⟨ht.1.1, ht.1.2.1, ht.1.2.2, ht.2.1, ht.2.2⟩
  have hPpos : ∀ t ∈ T, ∀ ℓ ∈ t.2.2, 0 < ℓ := fun t ht ℓ hℓ =>
    (mem_primesIco.1 ((hmemT t ht).2.2.1 hℓ)).2.2.pos
  have hrec : ∀ t ∈ T, Nat.minFac (Wt t) = t.2.1 ∧
      (primesIco (Nat.minFac (Wt t) + 1) z₀).filter (· ∣ Wt t) = t.2.2 ∧
      Wt t / ((∏ p' ∈ (primesIco (Nat.minFac (Wt t) + 1) z₀).filter (· ∣ Wt t), p') * Nat.minFac (Wt t)) = t.1 := by
    intro t ht
    obtain ⟨hr, hp, hP, -, -⟩ := hmemT t ht
    obtain ⟨-, hpz, hpp⟩ := mem_primesIco.1 hp
    have hmf : Nat.minFac (Wt t) = t.2.1 := minFac_W hpp hpz hP (hR t.1 hr).2
    have hfl : (primesIco (t.2.1 + 1) z₀).filter (· ∣ Wt t) = t.2.2 := filter_W hpp hP (hR t.1 hr).2
    refine ⟨hmf, by rw [hmf]; exact hfl, ?_⟩
    rw [hmf, hfl]
    exact div_W hpp (hPpos t ht)
  -- the inner sums are the cofactor sums
  have hstep1 : (∑ r ∈ R, c r * ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset,
      (-1 : ℂ) ^ (P.card + 1) * (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
        ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0)) =
      ∑ t ∈ T, c t.1 * (-1 : ℂ) ^ (t.2.2.card + 1) * G (Wt t) := by
    rw [hT, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    dsimp only
    split_ifs with h
    · obtain ⟨-, hpz, hpp⟩ := mem_primesIco.1 hp
      have hPs : P ⊆ primesIco (p + 1) z₀ := Finset.mem_powerset.1 hP
      have hr0 := (hR r hr).1
      have hW0 : 0 < r * (∏ p' ∈ P, p') * p :=
        Nat.mul_pos (Nat.mul_pos hr0 (Finset.prod_pos fun ℓ hℓ => (mem_primesIco.1 (hPs hℓ)).2.2.pos)) hpp.pos
      have hWN : r * (∏ p' ∈ P, p') * p ≤ N₁ :=
        le_trans (Nat.mul_le_mul_right p h.1) (le_trans (Nat.mul_le_mul_left X hpz.le) hXzN)
      have hWr : rough p (r * (∏ p' ∈ P, p') * p) := by
        intro ℓ hℓp hℓ hd
        rcases prime_dvd_W hpp hPs (hR r hr).2 hℓ hd with ⟨h', -⟩ | h' | h'
        · omega
        · have := (mem_primesIco.1 (hPs h')).1; omega
        · omega
      rw [sum_cofactor _ hW0 hWN hWr]
      have hmf : Nat.minFac (r * (∏ p' ∈ P, p') * p) = p := minFac_W hpp hpz hPs (hR r hr).2
      simp only [hG, hWt, hmf]
      ring
    · ring
  rw [hstep1]
  -- the coefficients, through the node a stop determines
  set PW : ℕ → Finset ℕ := fun W => (primesIco (Nat.minFac W + 1) z₀).filter (· ∣ W) with hPW
  set acoef : ℕ → ℂ := fun W => c (W / ((∏ p' ∈ PW W, p') * Nat.minFac W)) * (-1 : ℂ) ^ ((PW W).card + 1)
    with hacoef
  have hcoef : ∀ t ∈ T, c t.1 * (-1 : ℂ) ^ (t.2.2.card + 1) = acoef (Wt t) := by
    intro t ht
    obtain ⟨-, h2, h3⟩ := hrec t ht
    simp only [hacoef, hPW]
    rw [h3, h2]
  have hinj : ∀ t ∈ T, ∀ t' ∈ T, Wt t = Wt t' → t = t' := by
    intro t ht t' ht' h
    obtain ⟨h1, h2, h3⟩ := hrec t ht
    obtain ⟨h1', h2', h3'⟩ := hrec t' ht'
    rw [h] at h1 h2 h3
    obtain ⟨r, p, P⟩ := t
    obtain ⟨r', p', P'⟩ := t'
    dsimp only at h1 h2 h3 h1' h2' h3'
    have hp : p = p' := h1.symm.trans h1'
    have hP : P = P' := h2.symm.trans h2'
    have hr : r = r' := h3.symm.trans h3'
    subst hp hP hr
    rfl
  have hinj' : Set.InjOn Wt (T : Set (ℕ × (Σ _ : ℕ, Finset ℕ))) := fun t ht t' ht' h =>
    hinj t (Finset.mem_coe.1 ht) t' (Finset.mem_coe.1 ht') h
  rw [Finset.sum_congr rfl fun t ht => by rw [hcoef t ht], ← Finset.sum_image (f := fun W => acoef W * G W) hinj']
  have hS : T.image Wt ⊆ Finset.Ioc X (X * z₀) := by
    intro W hW
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hW
    obtain ⟨-, hp, -, h1, h2⟩ := hmemT t ht
    obtain ⟨-, hpz, -⟩ := mem_primesIco.1 hp
    exact Finset.mem_Ioc.2 ⟨h2, le_trans (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul_left X hpz.le)⟩
  have ha1 : ∀ W, ‖acoef W‖ ≤ 1 := by
    intro W
    simp only [hacoef, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    exact hc _
  have hz : ∀ W ∈ T.image Wt, (q : ℝ) ^ e₀ ≤ Nat.minFac W := by
    intro W hW
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hW
    rw [(hrec t ht).1]
    obtain ⟨-, hp, -, -, -⟩ := hmemT t ht
    exact le_trans hw (by exact_mod_cast (mem_primesIco.1 hp).1)
  exact hq₁ q hq1 a ha X (X * z₀) (T.image Wt) hS hX hXz acoef ha1 Nat.minFac hz

/-- **The terms inside the window.** Fix `e₀ > 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a`
mod `q`: let `r` run over `R ⊆ (P₁, P₂]`, `q^{0.401L} ≤ P₁`, `P₂ ≤ q^{0.485L}`, with every prime factor of each `r` at
least `z₀ ≥ q^{e₀}` and coefficients `|c_r| ≤ 1`. Then `Σ_r c_r (S(A_r, z₀) − S(B_r, z₀)/φ(q))` is at most
`q^{L−δ}/φ(q)` in absolute value. -/
theorem window_bound {e₀ : ℝ} (he₀ : 0 < e₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (z₀ P₁ P₂ : ℕ) (R : Finset ℕ) (c : ℕ → ℂ), (∀ r, ‖c r‖ ≤ 1) → R ⊆ Finset.Ioc P₁ P₂ →
      (∀ r ∈ R, ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p) → (q : ℝ) ^ e₀ ≤ z₀ →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ‖∑ r ∈ R, c r * ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊,
          dw q a n * (if r ∣ n ∧ rough z₀ n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  obtain ⟨δ, hδ, q₁, hq₁⟩ := SieveTypeIIR.typeII_rough he₀
  refine ⟨δ, hδ, max q₁ 2, ?_⟩
  intro q _ hq a ha z₀ P₁ P₂ R c hc hRS hR hz₀ hP₁ hP₂
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  have hP₂N : P₂ ≤ ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ := by
    apply Nat.le_floor
    exact hP₂.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  have hP₁1 : 1 ≤ P₁ := by
    have : (1 : ℝ) ≤ (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    exact_mod_cast this.trans hP₁
  rw [Finset.sum_congr rfl fun r hr => by
    have hrI := Finset.mem_Ioc.1 (hRS hr)
    rw [sum_cofactor _ (by omega) (le_trans hrI.2 hP₂N) (fun p hp hpp hpd => by
      have := hR r hr p hpp hpd; omega)]]
  exact hq₁ q hq1 a ha P₁ P₂ R hRS hP₁ hP₂ c hc (fun _ => z₀) (fun _ _ => hz₀)

end Bound

end SieveStops1
