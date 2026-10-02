import Zeta23.ZeroSide

/-! # The same-space hybrid certificate on zeta23's zero side, with the off-line term displayed (round 276)

zeta23 (Alpöge–Furman) bounds the number of distinct on-line zeros through the rank–trace inequality applied to
A = Σ_z m_z v_z v_zᵀ (`Zeta23.ZeroSide.ZeroBlockData`), in units c > 0 (zeta23 takes c = aL², Â = c⁻¹A, and splits
Â = P_c + Q_c with P_c = c⁻¹·(on-line part), `ZeroBlockData.blockP`/`blockQ`).  This file proves, for ANY
zero-block data and any c > 0:

* `cert_offline` — the RH-free certificate with the off-line pairs written out exactly:
      s₁ + s₂ ≥ 2c⁻¹·Re tr A − ‖c⁻¹A‖²_F + Σ_{z ∈ R} (4c⁻¹ m_z Re β_z − 4),      β_z = v_z · v_z (bilinear),
  where R holds one representative of each off-line pair {ρ, 1 − ρ̄}.  No hypothesis on the vectors beyond the
  `ZeroBlockData` axioms.

and, for the same-space coupling v_z = w_z + (η g_z) u_z (w, u: Fourier-class families; g: an analytic weight such as
the reflection-symmetric continuation of Re(B ζ′)/m; η real):

* `hybrid_cert` — using only the on-line normalisation Σ_k |w_z k|² ≤ c (zeta23's `hPois` for the base family) and
  N_on + 2p ≤ N:
      s₁ + s₂ ≥ c⁻¹(4 A_w + 2 A_g) − 2 N − ‖c⁻¹A‖²_F + 4c⁻¹ Σ_{z ∈ R} m_z Re G_z,
      A_w = Re Σ_z m_z (w_z·w_z),  G_z = 2η g_z (w_z·u_z) + η² g_z² (u_z·u_z),  A_g = Re Σ_z m_z G_z.
  Every term except the last is a sum over ALL zeros of a function of the data (what a prime side computes);
  the last is a sum over off-line pairs only.
* `hybrid_cert_of_offline` — the same with the off-line term replaced by a displayed hypothesis
      OFF(E): −E ≤ Σ_{z ∈ R} m_z Re G_z,
  i.e. exactly the input an RH-free proof must supply; and `hybrid_cert_of_moments`, which splits OFF into a
  first-order input |Σ_R m Re(g (w·u))| ≤ E₁ and a second-order input −E₂ ≤ Σ_R m Re(g² (u·u)).
* `hybrid_cert_of_no_offline` — with no off-line zeros in the window the off-line term is absent (E = 0).
* `hybrid_cert_eta_zero` — η = 0 returns AF's assembly 4c⁻¹ A_w − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂ (consistency check).
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

/-- **The rank–trace certificate in units c** (zeta23's `rank_trace_ineq_two` for P_c = c⁻¹·(on-line part),
Q_c = c⁻¹·(A − on-line part), as in `ZeroBlockData.blockP`/`blockQ`; zeta23 uses c = aL², Â = c⁻¹A):
4 c⁻¹ Re tr A − 2 c⁻¹ Re tr P − 4p − ‖c⁻¹A‖² ≤ s₁ + s₂. -/
theorem cert_general {c : ℝ} (hc : 0 < c) :
    4 * c⁻¹ * rtrace D.blockA - 2 * c⁻¹ * rtrace D.onPart - 4 * (P.p : ℝ)
      - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have h := rank_trace_ineq_two (D.blockP_posSemidef hc) (D.blockQ_isHermitian c)
    (D.rank_blockP_le hc) (D.posIndex_blockQ_le P hc)
  rw [ZeroBlockData.blockP_add_blockQ] at h
  simp only [ZeroBlockData.blockP, ZeroBlockData.blockQ, rtrace_real_smul, rtrace_sub] at h
  linarith

/-- **The certificate with the off-line pairs written out** (no hypothesis on the vectors):
2 c⁻¹ Re tr A − ‖c⁻¹A‖² + Σ_R (4 c⁻¹ m_z Re β_z − 4) ≤ s₁ + s₂.  If c⁻¹ β_z = 1 at every off-line point (as for
a Poisson identity Σ_k φ̂(γ − τ_k)² = c that continues analytically to complex γ), each summand is 4(m_z − 1) ≥ 0. -/
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

lemma G_σ (hw : ∀ z, w (D.σ z) = star (w z)) (hu : ∀ z, u (D.σ z) = star (u z))
    (hg : ∀ z, g (D.σ z) = star (g z)) (z : ι) : G w u g η (D.σ z) = star (G w u g η z) := by
  simp only [G, hw, hu, hg, star_dotProduct_star', star_add, star_mul', star_pow, Complex.star_def,
    Complex.conj_ofReal, map_ofNat]

lemma ww_σ (hw : ∀ z, w (D.σ z) = star (w z)) (z : ι) :
    w (D.σ z) ⬝ᵥ w (D.σ z) = star (w z ⬝ᵥ w z) := by
  rw [hw, star_dotProduct_star']

/-- On the line w_z is real, so w_z·w_z = Σ_k |w_z k|². -/
lemma ww_onLine (hw : ∀ z, w (D.σ z) = star (w z)) {z : ι} (hz : D.σ z = z) :
    w z ⬝ᵥ w z = ((∑ k, ‖w z k‖ ^ 2 : ℝ) : ℂ) := by
  have hr : ∀ k, star (w z k) = w z k := fun k => by
    have := congrFun (hw z) k; rw [hz] at this; simpa using this.symm
  push_cast
  refine sum_congr rfl fun k _ => ?_
  have := hr k
  rw [RCLike.star_def] at this
  have h1 : w z k * w z k = (starRingEnd ℂ) (w z k) * w z k := by rw [this]
  rw [h1, RCLike.conj_mul]; rfl

/-- **The same-space hybrid certificate** (RH-free; the off-line pairs enter only through the last term):
c⁻¹(4 A_w + 2 A_g) − 2 N − ‖c⁻¹A‖² + 4 c⁻¹ Σ_R m_z Re G_z ≤ s₁ + s₂, assuming only the on-line
normalisation Σ_k |w_z k|² ≤ c (zeta23's `hPois` for the base family; zeta23 has c = aL²) and the
reflection symmetry of w, u, g. -/
theorem hybrid_cert {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hw : ∀ z, w (D.σ z) = star (w z)) (hu : ∀ z, u (D.σ z) = star (u z))
    (hg : ∀ z, g (D.σ z) = star (g z))
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - 2 * (D.Ncount : ℝ) - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA)
      + 4 * c⁻¹ * ∑ z ∈ P.R, (D.m z : ℝ) * (G w u g η z).re ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have h := cert_general D P hc
  -- Re tr A = A_w + A_g
  have hA : rtrace D.blockA = Aw D w + Ag D w u g η := by
    simp only [rtrace, RCLike.re_to_complex, trace_blockA, Aw, Ag, β_eq D hv, mul_add, sum_add_distrib,
      Complex.add_re]
  -- Re tr P ≤ N_on + A_g − Σ_R 2 m Re G
  have hPw : (∑ z ∈ D.onLine, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re ≤ c * (D.Non : ℝ) := by
    rw [Complex.re_sum, ZeroBlockData.Non, Nat.cast_sum, mul_sum]
    refine sum_le_sum fun z hz => ?_
    rw [ww_onLine D hw ((D.mem_onLine).mp hz), ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    have hm : (0 : ℝ) ≤ D.m z := Nat.cast_nonneg _
    calc (D.m z : ℝ) * ∑ k, ‖w z k‖ ^ 2 ≤ D.m z * c := by gcongr; exact hPois z hz
      _ = c * D.m z := mul_comm _ _
  have hPw' : c⁻¹ * (∑ z ∈ D.onLine, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re ≤ (D.Non : ℝ) := by
    calc c⁻¹ * (∑ z ∈ D.onLine, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re ≤ c⁻¹ * (c * (D.Non : ℝ)) :=
          mul_le_mul_of_nonneg_left hPw (inv_nonneg.mpr hc.le)
      _ = D.Non := by field_simp
  have hG := re_sum_split D P (fun z => (D.m z : ℂ) * G w u g η z) (fun z => by
    rw [D.m_σ, G_σ D hw hu hg, star_mul', star_natCast])
  have hP : rtrace D.onPart = (∑ z ∈ D.onLine, (D.m z : ℂ) * (w z ⬝ᵥ w z)).re
      + (∑ z ∈ D.onLine, (D.m z : ℂ) * G w u g η z).re := by
    simp only [rtrace, RCLike.re_to_complex, trace_onPart, β_eq D hv, mul_add, sum_add_distrib, Complex.add_re]
  have hGre : ∀ z, ((D.m z : ℂ) * G w u g η z).re = (D.m z : ℝ) * (G w u g η z).re := fun z => by
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  simp only [hGre] at hG
  have hN := D.Non_add_two_p_le_Ncount P
  have hN' : (D.Non : ℝ) + 2 * (P.p : ℝ) ≤ D.Ncount := by exact_mod_cast hN
  have h2 : ∑ z ∈ P.R, 2 * ((D.m z : ℝ) * (G w u g η z).re) = 2 * ∑ z ∈ P.R, (D.m z : ℝ) * (G w u g η z).re := by
    rw [mul_sum]
  rw [show (∑ z, (D.m z : ℂ) * G w u g η z).re = Ag D w u g η from rfl] at hG
  rw [h2] at hG
  rw [hA, hP] at h
  have hκ : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  nlinarith [hPw', hN', hG, h]

/-- **The certificate with the off-line input displayed**: given OFF(E): −E ≤ Σ_R m_z Re G_z,
c⁻¹(4 A_w + 2 A_g − 4E) − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂. -/
theorem hybrid_cert_of_offline {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hw : ∀ z, w (D.σ z) = star (w z)) (hu : ∀ z, u (D.σ z) = star (u z))
    (hg : ∀ z, g (D.σ z) = star (g z))
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c)
    {E : ℝ} (hOFF : -E ≤ ∑ z ∈ P.R, (D.m z : ℝ) * (G w u g η z).re) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - 4 * c⁻¹ * E - 2 * (D.Ncount : ℝ)
      - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have := hybrid_cert D P hc hv hw hu hg hPois
  have hκ : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  nlinarith [mul_le_mul_of_nonneg_left hOFF hκ]

/-- **The off-line input split by order in η**: a first-order input |Σ_R m Re(g (w·u))| ≤ E₁ and a
second-order input −E₂ ≤ Σ_R m Re(g² (u·u)) give
c⁻¹(4 A_w + 2 A_g − 8|η|E₁ − 4η²E₂) − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂. -/
theorem hybrid_cert_of_moments {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hw : ∀ z, w (D.σ z) = star (w z)) (hu : ∀ z, u (D.σ z) = star (u z))
    (hg : ∀ z, g (D.σ z) = star (g z))
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c)
    {E₁ E₂ : ℝ} (h1 : |∑ z ∈ P.R, (D.m z : ℝ) * (g z * (w z ⬝ᵥ u z)).re| ≤ E₁)
    (h2 : -E₂ ≤ ∑ z ∈ P.R, (D.m z : ℝ) * (g z ^ 2 * (u z ⬝ᵥ u z)).re) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - c⁻¹ * (8 * |η| * E₁ + 4 * η ^ 2 * E₂)
      - 2 * (D.Ncount : ℝ) - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have hsplit : ∑ z ∈ P.R, (D.m z : ℝ) * (G w u g η z).re
      = 2 * η * ∑ z ∈ P.R, (D.m z : ℝ) * (g z * (w z ⬝ᵥ u z)).re
        + η ^ 2 * ∑ z ∈ P.R, (D.m z : ℝ) * (g z ^ 2 * (u z ⬝ᵥ u z)).re := by
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
  have hfirst : -(2 * |η| * E₁) ≤ 2 * η * ∑ z ∈ P.R, (D.m z : ℝ) * (g z * (w z ⬝ᵥ u z)).re := by
    have := abs_le.mp h1
    have hab := abs_mul (2 * η) (∑ z ∈ P.R, (D.m z : ℝ) * (g z * (w z ⬝ᵥ u z)).re)
    have h0 : |2 * η| = 2 * |η| := by rw [abs_mul]; norm_num
    have : |2 * η * ∑ z ∈ P.R, (D.m z : ℝ) * (g z * (w z ⬝ᵥ u z)).re| ≤ 2 * |η| * E₁ := by
      rw [hab, h0]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith [neg_abs_le (2 * η * ∑ z ∈ P.R, (D.m z : ℝ) * (g z * (w z ⬝ᵥ u z)).re)]
  have hsecond : -(η ^ 2 * E₂) ≤ η ^ 2 * ∑ z ∈ P.R, (D.m z : ℝ) * (g z ^ 2 * (u z ⬝ᵥ u z)).re := by
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg η); linarith
  exact le_trans (le_of_eq (by ring)) (hybrid_cert_of_offline D P hc hv hw hu hg hPois
    (E := 2 * |η| * E₁ + η ^ 2 * E₂) (by rw [hsplit]; linarith))

/-- **No off-line zeros**: if the window has no off-line pair (R = ∅), the certificate holds with E = 0:
c⁻¹(4 A_w + 2 A_g) − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂.  The off-line input is the only place the zeros' positions enter. -/
theorem hybrid_cert_of_no_offline {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z + ((η : ℂ) * g z) • u z)
    (hw : ∀ z, w (D.σ z) = star (w z)) (hu : ∀ z, u (D.σ z) = star (u z))
    (hg : ∀ z, g (D.σ z) = star (g z))
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c) (hR : P.R = ∅) :
    4 * c⁻¹ * Aw D w + 2 * c⁻¹ * Ag D w u g η - 2 * (D.Ncount : ℝ)
      - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have := hybrid_cert_of_offline D P hc hv hw hu hg hPois (E := 0) (by simp [hR])
  linarith

/-- **Consistency (η = 0)**: the hybrid certificate reduces to AF's assembly
4 c⁻¹ A_w − 2N − ‖c⁻¹A‖² ≤ s₁ + s₂. -/
theorem hybrid_cert_eta_zero {c : ℝ} (hc : 0 < c) (hv : ∀ z, D.v z = w z) (hw : ∀ z, w (D.σ z) = star (w z))
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖w z k‖ ^ 2 ≤ c) :
    4 * c⁻¹ * Aw D w - 2 * (D.Ncount : ℝ) - frobSq (((c⁻¹ : ℝ) : ℂ) • D.blockA) ≤ ((D.s₁ + D.s₂ : ℕ) : ℝ) := by
  have hv' : ∀ z, D.v z = w z + (((0 : ℝ) : ℂ) * (0 : ι → ℂ) z) • w z := fun z => by simp [hv z]
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have := hybrid_cert (g := 0) (u := w) (η := 0) D D.pairRepsOfLinearOrder hc hv' hw hw (fun z => by simp) hPois
  simpa [G, Ag] using this

end Hybrid

end HybridCert
