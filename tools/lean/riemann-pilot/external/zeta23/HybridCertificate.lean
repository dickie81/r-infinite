import Zeta23.ZeroSide

/-! # The same-space hybrid certificate on zeta23's zero side, with the off-line term displayed (round 276)

zeta23 (Alpöge–Furman) bounds the number of distinct on-line zeros through the rank–trace inequality applied to
A = Σ_z m_z v_z v_zᵀ (`Zeta23.ZeroSide.ZeroBlockData`), in units c > 0 (zeta23 takes c = aL², Â = c⁻¹A, and splits
Â = P_c + Q_c with P_c = c⁻¹·A_on, A_on the on-line part of A, `ZeroBlockData.blockP`/`blockQ`).  This file
proves, for any zero-block data and any c > 0:

* `cert_offline` — the certificate with the off-line pairs written out:
      s₁ + s₂ ≥ 2c⁻¹·Re tr A − ‖c⁻¹A‖²_F + Σ_{z ∈ R} (4c⁻¹ m_z Re β_z − 4),      β_z = v_z · v_z (bilinear),
  where R holds one representative of each off-line pair {ρ, 1 − ρ̄}.  No hypothesis on the vectors beyond the
  `ZeroBlockData` axioms.

and, for the same-space coupling v_z = w_z + (η g_z) u_z (w, u: families of vectors; g: a weight at the zeros, for
instance a continuation of Re(B ζ′); η real):

* `hybrid_cert` — with hypotheses only v = w + (ηg)u and the on-line normalisation Σ_k |w_z k|² ≤ c (the shape of
  zeta23's `hPois`, imposed on the base family w alone):
      s₁ + s₂ ≥ c⁻¹(4 A_w + 2 A_g) − 2 N − ‖c⁻¹A‖²_F + 2c⁻¹ Σ_{z off the line} m_z Re G_z,
      A_w = Re Σ_z m_z (w_z·w_z),  G_z = 2η g_z (w_z·u_z) + η² g_z² (u_z·u_z),  A_g = Re Σ_z m_z G_z.
  A_w, A_g and N are sums over all zeros of the window, and ‖A‖²_F is a function of the entries of A, which are
  such sums.  The last term is the only one that is a sum over the off-line zeros alone.  `hybrid_cert_pairs`
  folds it onto R, as 4c⁻¹ Σ_{z ∈ R} m_z Re G_z, when w is reflection-symmetric.
* `hybrid_cert_of_offline` — the last term replaced by −2c⁻¹E, given the displayed input
      OFF(E): −E ≤ Σ_{z off the line} m_z Re G_z;
  and `hybrid_cert_of_moments`, which splits OFF by order in η into two one-sided inputs,
  −E₁ ≤ 2η Σ_{z off the line} m_z Re(g_z (w_z·u_z)) and −E₂ ≤ Σ_{z off the line} m_z Re(g_z² (u_z·u_z)).
* `hybrid_cert_of_no_offline` — if every zero of the window is on the line, the off-line term is absent.
* `hybrid_cert_eta_zero` — η = 0 gives 4c⁻¹ A_w − 2N − ‖c⁻¹A‖²_F ≤ s₁ + s₂, the inequality of zeta23's
  `Assembly.zeroside_rank_core` (4 tr Â − 2N(I′) − ‖Â‖²_F ≤ r).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Zeta23.ZeroSide
open scoped ComplexOrder BigOperators

namespace HybridCert

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d) (P : D.PairReps)

/-- β_z := v_z · v_z, the bilinear (unconjugated) square norm of the evaluation vector. -/
def β (z : ι) : ℂ := D.v z ⬝ᵥ D.v z

lemma star_dotProduct_star' (x y : d → ℂ) : star x ⬝ᵥ star y = star (x ⬝ᵥ y) := by
  simp [dotProduct, star_sum]

/-- A sum over all points of a σ-conjugation-equivariant function splits into on-line points and pairs:
Re Σ f = Re Σ_{onLine} f + Σ_R 2 Re f. -/
lemma re_sum_split (f : ι → ℂ) (hf : ∀ z, f (D.σ z) = star (f z)) :
    (∑ z, f z).re = (∑ z ∈ D.onLine, f z).re + ∑ z ∈ P.R, 2 * (f z).re := by
  rw [D.sum_split (M := ℂ) P f, Complex.add_re, Complex.re_sum, Complex.re_sum]
  congr 1
  refine sum_congr rfl fun z _ => ?_
  rw [hf z, Complex.add_re, Complex.star_def, Complex.conj_re]; ring

lemma trace_vecMulVec_self (z : ι) : (vecMulVec (D.v z) (D.v z)).trace = β D z := by
  simp [β, trace_vecMulVec]

lemma trace_blockA : D.blockA.trace = ∑ z, (D.m z : ℂ) * β D z := by
  simp only [ZeroBlockData.blockA, trace_sum, trace_smul, smul_eq_mul, trace_vecMulVec_self]

lemma trace_onPart : D.onPart.trace = ∑ z ∈ D.onLine, (D.m z : ℂ) * β D z := by
  simp only [ZeroBlockData.onPart, trace_sum, trace_smul, smul_eq_mul, trace_vecMulVec_self]

lemma β_σ (z : ι) : β D (D.σ z) = star (β D z) := by
  simp only [β, D.v_σ, star_dotProduct_star']

/-- Re tr A = Re tr(on-line part) + Σ_R 2 m_z Re β_z. -/
lemma rtrace_blockA_split :
    rtrace D.blockA = rtrace D.onPart + ∑ z ∈ P.R, 2 * ((D.m z : ℝ) * (β D z).re) := by
  have h := re_sum_split D P (fun z => (D.m z : ℂ) * β D z) (fun z => by
    rw [D.m_σ, β_σ, star_mul', star_natCast])
  simp only [rtrace, RCLike.re_to_complex, trace_blockA, trace_onPart]
  rw [h]; congr 1
  refine sum_congr rfl fun z _ => ?_
  rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]

lemma rtrace_real_smul (r : ℝ) (M : Matrix d d ℂ) : rtrace (((r : ℝ) : ℂ) • M) = r * rtrace M := by
  simp only [rtrace, trace_smul, smul_eq_mul, RCLike.re_to_complex, Complex.re_ofReal_mul]

/-- **The rank–trace certificate in units c** (zeta23's `rank_trace_ineq_two` for P_c = c⁻¹·A_on and
Q_c = c⁻¹·(A − A_on), where A_on = `D.onPart` is the on-line part of A, as in `ZeroBlockData.blockP`/`blockQ`;
zeta23 uses c = aL², Â = c⁻¹A): 4 c⁻¹ Re tr A − 2 c⁻¹ Re tr A_on − 4p − ‖c⁻¹A‖² ≤ s₁ + s₂, with p = #R. -/
theorem cert_general {c : ℝ} (hc : 0 < c) :
    4 * c⁻¹ * rtrace D.blockA - 2 * c⁻¹ * rtrace D.onPart - 4 * (P.p : ℝ)
      - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have h := rank_trace_ineq_two (D.blockP_posSemidef hc) (D.blockQ_isHermitian c)
    (D.rank_blockP_le hc) (D.posIndex_blockQ_le P hc)
  rw [ZeroBlockData.blockP_add_blockQ] at h
  simp only [ZeroBlockData.blockP, ZeroBlockData.blockQ, rtrace_real_smul, rtrace_sub] at h
  linarith

/-- **The certificate with the off-line pairs written out** (no hypothesis on the vectors):
2 c⁻¹ Re tr A − ‖c⁻¹A‖² + Σ_R (4 c⁻¹ m_z Re β_z − 4) ≤ s₁ + s₂. -/
theorem cert_offline {c : ℝ} (hc : 0 < c) :
    2 * c⁻¹ * rtrace D.blockA - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA)
      + ∑ z ∈ P.R, (4 * c⁻¹ * ((D.m z : ℝ) * (β D z).re) - 4) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have h := cert_general D P hc
  have hs := rtrace_blockA_split D P
  have hp : (P.p : ℝ) = ∑ z ∈ P.R, (1 : ℝ) := by simp [ZeroBlockData.PairReps.p]
  have hsum : ∑ z ∈ P.R, (4 * c⁻¹ * ((D.m z : ℝ) * (β D z).re) - 4)
      = 2 * c⁻¹ * ∑ z ∈ P.R, 2 * ((D.m z : ℝ) * (β D z).re) - 4 * ∑ z ∈ P.R, (1 : ℝ) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun z _ => by ring
  rw [hsum]; rw [hp] at h; rw [hs] at h ⊢; linarith

/-! ## The same-space coupling v = w + (η g) u -/

section Hybrid

variable (w u : ι → d → ℂ) (g : ι → ℂ) (η : ℝ)

/-- G_z := 2η g_z (w_z·u_z) + η² g_z² (u_z·u_z): the weight-dependent part of β_z. -/
def G (z : ι) : ℂ := 2 * (η : ℂ) * g z * (w z ⬝ᵥ u z) + (η : ℂ) ^ 2 * g z ^ 2 * (u z ⬝ᵥ u z)

/-- A_w := Re Σ_z m_z (w_z·w_z). -/
def Aw : ℝ := (∑ z, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re

/-- A_g := Re Σ_z m_z G_z. -/
def Ag : ℝ := (∑ z, (D.m z : ℂ) * G w u g η z).re

variable {w u g η}

lemma β_eq (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z) (z : ι) :
    β D z = w z ⬝ᵥ w z + G w u g η z := by
  simp only [β, G, hv, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (u z) (w z)]
  ring

/-- Re(x·x) ≤ Σ_k |x_k|² for every complex vector x (the bilinear square against the Hermitian one). -/
lemma re_dotProduct_self_le (x : d → ℂ) : (x ⬝ᵥ x).re ≤ ∑ k, ‖x k‖ ^ 2 := by
  rw [dotProduct, Complex.re_sum]
  refine sum_le_sum fun k _ => ?_
  rw [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (x k).im]

lemma re_natCast_mul (n : ℕ) (x : ℂ) : ((n : ℂ) * x).re = (n : ℝ) * x.re := by
  rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]

/-- A_g = Re Σ_{on-line} m_z G_z + Σ_{z off the line} m_z Re G_z. -/
lemma Ag_split : Ag D w u g η = (∑ z ∈ D.onLine, (D.m z : ℂ) * G w u g η z).re
    + ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (G w u g η z).re := by
  show (∑ z, (D.m z : ℂ) * G w u g η z).re = _
  rw [← Finset.sum_add_sum_compl D.onLine, Complex.add_re, Complex.re_sum (s := D.onLineᶜ)]
  congr 1
  exact sum_congr rfl fun z _ => re_natCast_mul _ _

/-- **The same-space hybrid certificate** (no RH, no symmetry assumption on w, u, g):
c⁻¹(4 A_w + 2 A_g) − 2N − ‖c⁻¹A‖² + 2c⁻¹ Σ_{z off the line} m_z Re G_z ≤ s₁ + s₂, assuming v = w + (ηg)u and the
on-line normalisation Σ_k |w_z k|² ≤ c (the shape of zeta23's `hPois`, imposed on w alone; zeta23 has c = aL²). -/
theorem hybrid_cert {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - 2 * (D.Ncount : ℝ) - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA)
      + 2 * c⁻¹ * ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (G w u g η z).re ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let P := D.pairRepsOfLinearOrder
  have h := cert_general D P hc
  -- Re tr A = A_w + A_g
  have hA : rtrace D.blockA = Aw D w + Ag D w u g η := by
    simp only [rtrace, RCLike.re_to_complex, trace_blockA, Aw, Ag, β_eq D hv, mul_add, sum_add_distrib,
      Complex.add_re]
  -- Re tr A_on = Re Σ_{on-line} m_z (w_z·w_z) + Re Σ_{on-line} m_z G_z
  have hP : rtrace D.onPart = (∑ z ∈ D.onLine, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re
      + (∑ z ∈ D.onLine, (D.m z : ℂ) * G w u g η z).re := by
    simp only [rtrace, RCLike.re_to_complex, trace_onPart, β_eq D hv, mul_add, sum_add_distrib, Complex.add_re]
  -- Re Σ_{on-line} m_z (w_z·w_z) ≤ c·N_on
  have hPw : (∑ z ∈ D.onLine, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re ≤ c * (D.Non : ℝ) := by
    rw [Complex.re_sum, ZeroBlockData.Non, Nat.cast_sum, mul_sum]
    refine sum_le_sum fun z hz => ?_
    rw [re_natCast_mul]
    have hm : (0 : ℝ) ≤ D.m z := Nat.cast_nonneg _
    calc (D.m z : ℝ) * (w z ⬝ᵥ w z).re ≤ D.m z * c := by
          gcongr; exact (re_dotProduct_self_le _).trans (hPois z hz)
      _ = c * D.m z := mul_comm _ _
  have hPw' : c⁻¹ * (∑ z ∈ D.onLine, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re ≤ (D.Non : ℝ) := by
    calc c⁻¹ * (∑ z ∈ D.onLine, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re ≤ c⁻¹ * (c * (D.Non : ℝ)) :=
          mul_le_mul_of_nonneg_left hPw (inv_nonneg.mpr hc.le)
      _ = D.Non := by field_simp
  have hN' : (D.Non : ℝ) + 2 * (P.p : ℝ) ≤ D.Ncount := by exact_mod_cast D.Non_add_two_p_le_Ncount P
  have e1 : c⁻¹ * (∑ z ∈ D.onLine, (D.m z : ℂ) * G w u g η z).re
      = c⁻¹ * Ag D w u g η - c⁻¹ * ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (G w u g η z).re := by
    rw [Ag_split]; ring
  rw [hA, hP] at h
  nlinarith [hPw', hN', h, e1]

lemma ww_σ (hw : ∀ z, w (D.σ z) = star (w z)) (z : ι) :
    w (D.σ z) ⬝ᵥ w (D.σ z) = star (w z ⬝ᵥ w z) := by
  rw [hw, star_dotProduct_star']

/-- G is σ-equivariant as soon as w is (G = β − w·w, and β is by `ZeroBlockData.v_σ`). -/
lemma G_σ (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z) (hw : ∀ z, w (D.σ z) = star (w z)) (z : ι) :
    G w u g η (D.σ z) = star (G w u g η z) := by
  have e : G w u g η (D.σ z) = β D (D.σ z) - w (D.σ z) ⬝ᵥ w (D.σ z) := by rw [β_eq D hv]; ring
  rw [e, β_σ, ww_σ D hw, β_eq D hv, star_add]; ring

/-- For a σ-equivariant f, the off-line zeros contribute Σ_{z off the line} Re f_z = Σ_{z ∈ R} 2 Re f_z. -/
lemma re_sum_offLine (f : ι → ℂ) (hf : ∀ z, f (D.σ z) = star (f z)) :
    ∑ z ∈ D.onLineᶜ, (f z).re = ∑ z ∈ P.R, 2 * (f z).re := by
  have h := re_sum_split D P f hf
  rw [← Finset.sum_add_sum_compl D.onLine, Complex.add_re, Complex.re_sum (s := D.onLineᶜ)] at h
  linarith

/-- **The certificate on pair representatives**: if w is reflection-symmetric,
c⁻¹(4 A_w + 2 A_g) − 2N − ‖c⁻¹A‖² + 4c⁻¹ Σ_{z ∈ R} m_z Re G_z ≤ s₁ + s₂. -/
theorem hybrid_cert_pairs {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hw : ∀ z, w (D.σ z) = star (w z)) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - 2 * (D.Ncount : ℝ) - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA)
      + 4 * c⁻¹ * ∑ z ∈ P.R, (D.m z : ℝ) * (G w u g η z).re ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have h := hybrid_cert D hc hv hPois
  have hs := re_sum_offLine D P (fun z => (D.m z : ℂ) * G w u g η z) (fun z => by
    rw [D.m_σ, G_σ D hv hw, star_mul', star_natCast])
  simp only [re_natCast_mul] at hs
  rw [hs, ← mul_sum] at h
  linarith

/-- **The certificate with the off-line input displayed**: given OFF(E): −E ≤ Σ_{z off the line} m_z Re G_z,
c⁻¹(4 A_w + 2 A_g − 2E) − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂. -/
theorem hybrid_cert_of_offline {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c)
    {E : ℝ} (hOFF : -E ≤ ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (G w u g η z).re) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - 2 * c⁻¹ * E - 2 * (D.Ncount : ℝ)
      - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have := hybrid_cert D hc hv hPois
  have hκ : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  nlinarith [mul_le_mul_of_nonneg_left hOFF hκ]

/-- **The off-line input split by order in η**: one-sided inputs −E₁ ≤ 2η Σ_{off} m Re(g (w·u)) (first order)
and −E₂ ≤ Σ_{off} m Re(g² (u·u)) (second order) give c⁻¹(4 A_w + 2 A_g − 2E₁ − 2η²E₂) − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂. -/
theorem hybrid_cert_of_moments {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c)
    {E₁ E₂ : ℝ} (h1 : -E₁ ≤ 2 * η * ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (g z * (w z ⬝ᵥ u z)).re)
    (h2 : -E₂ ≤ ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (g z ^ 2 * (u z ⬝ᵥ u z)).re) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - 2 * c⁻¹ * (E₁ + η ^ 2 * E₂)
      - 2 * (D.Ncount : ℝ) - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have hsplit : ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (G w u g η z).re
      = 2 * η * ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (g z * (w z ⬝ᵥ u z)).re
        + η ^ 2 * ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (g z ^ 2 * (u z ⬝ᵥ u z)).re := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun z _ => ?_
    simp only [G, Complex.add_re]
    have e1 : (2 * (η : ℂ) * g z * (w z ⬝ᵥ u z)).re = 2 * η * (g z * (w z ⬝ᵥ u z)).re := by
      rw [show 2 * (η : ℂ) * g z * (w z ⬝ᵥ u z) = ((2 * η : ℝ) : ℂ) * (g z * (w z ⬝ᵥ u z)) by push_cast; ring,
        Complex.re_ofReal_mul]
    have e2 : ((η : ℂ) ^ 2 * g z ^ 2 * (u z ⬝ᵥ u z)).re = η ^ 2 * (g z ^ 2 * (u z ⬝ᵥ u z)).re := by
      rw [show (η : ℂ) ^ 2 * g z ^ 2 * (u z ⬝ᵥ u z) = ((η ^ 2 : ℝ) : ℂ) * (g z ^ 2 * (u z ⬝ᵥ u z)) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [e1, e2]; ring
  have hsecond : -(η ^ 2 * E₂) ≤ η ^ 2 * ∑ z ∈ D.onLineᶜ, (D.m z : ℝ) * (g z ^ 2 * (u z ⬝ᵥ u z)).re := by
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg η); linarith
  exact le_trans (le_of_eq (by ring)) (hybrid_cert_of_offline D hc hv hPois
    (E := E₁ + η ^ 2 * E₂) (by rw [hsplit]; linarith))

/-- **No off-line zeros**: if every zero of the window is on the line, the certificate holds with E = 0:
c⁻¹(4 A_w + 2 A_g) − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂. -/
theorem hybrid_cert_of_no_offline {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c) (hon : ∀ z, D.σ z = z) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - 2 * (D.Ncount : ℝ)
      - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have hempty : D.onLineᶜ = ∅ := by
    ext z; simp [ZeroBlockData.mem_onLine, hon z]
  have := hybrid_cert_of_offline D hc hv hPois (E := 0) (by simp [hempty])
  linarith

/-- **Consistency (η = 0)**: the hybrid certificate reduces to the inequality of zeta23's
`Assembly.zeroside_rank_core`, 4 c⁻¹ A_w − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂. -/
theorem hybrid_cert_eta_zero {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c) :
    4 * c⁻¹ * Aw D w - 2 * (D.Ncount : ℝ) - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have hv' : ∀ z, D.v z = w z + (((0 : ℝ) : ℂ) * (0 : ι → ℂ) z) • w z := fun z => by simp [hv z]
  have := hybrid_cert (g := 0) (u := w) (η := 0) D hc hv' hPois
  simpa [G, Ag] using this

end Hybrid

end HybridCert
