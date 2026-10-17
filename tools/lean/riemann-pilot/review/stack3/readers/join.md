<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

Lens: joins. These are sockets in src/, external/dh/, external/pnt/*.lean and external/zeta23/*.lean that results of rounds 337–495 could fill but do not. The D1 consumers and everything in STRUCTURAL-REVIEW §9 are excluded. Each item is a suggestion for the lead to verify by reading the source.

**Coverage (read-only)**
1. STRUCTURAL-REVIEW.md: lines 77–103 and 174–406 read.
2. README.md: lines 7866–7870, 7895–7915, 8244–8252, 8855–8875, 17312–17483 and 17831–17889 read. The "The next step" paragraphs of rounds 471–495 were read via grep; each is one line.
3. src/ files read in full:
   - HalfPlaneJoinsFinal.lean: 1–117
   - HalfPlaneJoins.lean: 1–114
   - CrossCriteria.lean: 1–145
   - DirichletOmega.lean: 1–168
   - KernelChain.lean: 1–41
4. src/ files read in part:
   - StripConv.lean: 1–110 and 380–470
   - Unconditional.lean: 1–60 and 245–332
   - ZetaInputs.lean: 1–30, 192–198 and 220–264
   - ZetaJoins.lean: 1–140
   - WeilChiCriterion.lean: 1–40, 100–300 and 335–390
   - WeilChi.lean: 1–75
   - WeilTwinGeneral.lean: 1–30, 85–110 and 270–340
   - WeilDedekind.lean: 100–170
   - WeilLandau.lean: 155–193
   - WeilRate.lean: 1–30 plus all declaration statements
   - PsiOmega.lean: 685–720
   - RealDirichlet.lean: 560–700
   - KaiserNine.lean: 1–60
   - KaiserSplit.lean: 1–60
   - BohrJoins.lean: 1–110
   - ShortPrimes.lean: 20–45
   - DensityAsym.lean: 1–35 plus statements
   - HadamardApply.lean: 160–175
   - HurwitzCross.lean: 25–50
   - DetectCore.lean: 20–40
   - MeanSquareZeta.lean: 20–40
   - MeanSquareHigh.lean: 441–447 and 495–543
   - ExplicitBridge.lean: 40–55
   - Exterior.lean: 182–200
   - AngularFamily.lean: 90–105
   - PhiDecay.lean: 1–40 and 530–600
   - KubotaStrip.lean: 1–60 plus statements
   - ThermalJoins.lean: 1–40
   - StripShift.lean: 120–140
   - ZetaDiscs, ZetaDiscsR, JensenAvg, ShellSixthCore, BohrLandauCore and ShellCount: 1–30 each
   - RealCharHalfPlane, DirichletCharHalfPlane and KubotaThetaProof: declaration statements
5. external/pnt/ files:
   - HalfPlanePNT, HalfPlaneFinal, HalfPlaneLindelof, MertensExponent, SquarefreeCount and QuadClassNumber: declaration statements
   - PsiExponent: statements plus 20–32 and 74–94
   - QuadKronecker: statements plus 255–330
   - SmoothPerron: 1–48 plus statements
   - QuadIdeals: 1–60 and 443–504
   - KVBridge 45–70; Landau 335–395; Rung3 15–40; LandauKV 131–137; PNTKV 179–183; ShortKV 48–60
   - TwinKV 1–12 and 456–461; BohrKV 1–28; Domination 1–30 and 120–175
   - build.sh: 1–304
6. external/zeta23/ files:
   - CoImportGamma: 1–31
   - CoImportMV: 1–30 and 80–130
   - CountCompare, ZeroWindow, SlogZeta, Dictionary, HybridCertificate and HybridExamples: 1–25 each
7. external/dh/ files: DHColumn 225–260; DHChannels 130–160 and 240–262; ChiGround 728–800.

**Socket census (step 1, the zero-location sockets only)**
- **Prop displays.** `grep -nE '^\s*(…)(def|abbrev|structure|class) .*: *Prop( |$|:=)'` over the four own layers gives 165 lines. The chain displays are all proved in KubotaThetaProof.lean:46–111 and HalfPlaneJoinsFinal.lean:31. The other named inputs are proved too: `MSPoly`, `EMApprox`, `EMBound`, `DetectHyp`, `XiGrowth`, `ZetaNoZeroInUnitInterval`, `DigammaDiff`, `BinetFormula`.
- **Still open:** the displays of `CrossCriteria` (C), `CoImportMV.GaussIdealCount`, `VdC2Bound`, `VinoBlockSaving`, `DetectHypP` (no consumer), the certificates, and `EnergyGap`/`HypD`/`DFamW`.
- **ζ half-plane hypothesis** (`hzf : ∀ ρ, θ < ρ.re → riemannZeta ρ ≠ 0`):
  - src: `PsiOmega.band_of_zeroFree` (692), `rh_of_zeroFree_half` (701), `BohrJoins.shell_of_zeroFree` (56), `sphere_of_zeroFree_half` (95).
  - pnt: HalfPlanePNT, MertensExponent, SquarefreeCount, HalfPlaneLindelof and DivisorExponent. All have 11/12 and Θ instances in pnt; in src, 11/12 only, via `kubotaTheta`.
- **Band hypothesis** (`∀ s, … → |2 s.re − 1| ≤ σ`): `weil_twins_rate` (WeilLandau:162), `twins_rate` (WeilChiCriterion:195), `twins_rate_chi4` (:365), `QKχ_twins_rate` (WeilTwinGeneral:315), `twins_rate_realRooted` (:94), `Dedekind4.QK_twins_rate` (WeilDedekind:116), `CrossCriteria.LamGradedConverse` (137).
- **Strip-width-½ inputs:** StripConv (`stripSet` 39, `HypConvStrip` 48, theorems 64/100/390/419/437), `KernelChain.rh_of_close_RPhi` (31), `Unconditional.pinned_unconditional` with `hstrip` (258/306) feeding `ZetaInputs.pinned_zeta` (229) and `ZetaJoins.pinned_zeta_zero` (53). PhiDecay/PhiLadder and the Kaiser files also carry it.
- **`hS` on (0,1) or (θ,1):** WeilChiCriterion, WeilChiDensity, WeilTwinGeneral, ChiHalfSharp, CrossCriteria.grh_of_cross, DirichletOmega (85/98/115/159), RealDirichlet:667, dh ChiFirstFailure/ChiGround/DHJoins.

**Candidates**

1. **(A) Twin rate 5/6 for every GoodChar χ with `hS`, not only χ₋₃. Rate 5/6 for every real-rooted base on the ζ side.**
   - Sockets:
     - src/WeilChiCriterion.lean:195 `theorem twins_rate (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) : (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QC χ (l + 1) (twin (box 1) l)) ↔ ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → |2 * s.re - 1| ≤ σ` (under `variable (hG : GoodChar χ) include hG`, lines 30–31)
     - :365 `theorem twins_rate_chi4 {σ : ℝ} (hσ : 0 ≤ σ) :`
     - src/WeilTwinGeneral.lean:315 `theorem QKχ_twins_rate (hG : GoodChar χ) (hS : …)`
     - src/WeilDedekind.lean:116 `theorem QK_twins_rate {σ : ℝ} (hσ : 0 ≤ σ) :`, whose right side is `(∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ) ∧ (∀ s : ℂ, DirichletCharacter.LFunction chi4 s = 0 → 0 < s.re → s.re < 1 → |2 * s.re - 1| ≤ σ)`
     - src/WeilTwinGeneral.lean:94 `theorem twins_rate_realRooted … (hRR : RealRooted b g₀) {σ : ℝ} (hσ : 0 ≤ σ) : (∃ C, … ≤ weilQ (l + b) (twin g₀ l)) ↔ ∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ`
   - Fillers:
     - src/RealCharHalfPlane.lean:354 `theorem LFunction_ne_zero_of_isQuadratic [NeZero q] {χ : DirichletCharacter ℂ q} (hq : χ.IsQuadratic) {s : ℂ} (hs : 11 / 12 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : LFunction χ s ≠ 0`
     - the reflection in `HalfPlaneJoins.chi3_band` (src/HalfPlaneJoins.lean:36–57), whose only χ-specific step is `rw [XiC_even good_chi3]`; `XiC_even` (src/WeilChi.lean:68) is generic under `hG`
     - src/HalfPlaneJoinsFinal.lean:43 `zeta_band_eleven_twelfths`
     - instances: `good_chi4` and `good_chi8` (WeilChiCriterion:346, 348), `good_chi7` (WeilTwinGeneral:195), `hS4` (WeilDedekind:20), `hS7` and `hS8` (WeilTwinGeneral:198, 346)
   - Gap: a χ band lemma (`chi3_band` with `hG` in place of `good_chi3` and the real-character half-plane in place of `ne_zero_of_smoothBound`). The stack has none: `grep … band … theorem` finds only `zeta_band`, `chi3_band` and `band_of_zeroFree` (ζ). After that it is one line per socket.
   - Recorded only as not reached:
     - README.md:8866 (round 279): "- Statements at the level of RH or GRH, characters other than `χ₋₃`, and the real zeros of `L(s, χ₋₃)`, …"
     - README.md:17373 (round 468): "…for other characters, and on the real zeros of `L(s, χ₋₃)` remain as listed."
     - STRUCTURAL-REVIEW.md:188: "(round 468: the uniform rate `5/6` is fed … for `L(s, χ₋₃)` and `ζ·ζ_{ℚ(√−3)}`; per-pole rates are not fed…)"
     - No marker after round 477.
   - Commands:
     - `grep -n 'twins_rate\b\|twins_rate \|QKχ_twins_rate\|twins_rate)' src/*.lean external/*/*.lean`: uses only at HalfPlaneJoins.lean:66 and 73 (χ₋₃) and WeilChiCriterion.lean:368.
     - `grep -rn '5 / 6\|59 / 6\|5 / 12' …`: only HalfPlaneJoinsFinal.
     - `grep -rlw` on `twins_rate_chi4`, `QK_twins_rate` and `twins_rate_realRooted`: each is used only in its own file.
     - `awk 'NR>=17312' README.md | grep 'twins_rate|χ₋₄|chi4…'`: only round 468's χ₋₃ lines.
   - The every-real-character half-plane (round 477) gives rate 5/6 for the twin forms of `L(s,χ₋₄)`, `L(s,χ₋₇)`, `L(s,χ₋₈)`, `ζ·L(χ)` and `ζ_{ℚ(i)}`, and for every real-rooted base. None is stated.

2. **(A) The strip-convergence RH criteria at strip width c ∈ (5/12, ½].**
   - Sockets:
     - src/StripConv.lean:39 `def stripSet : Set ℂ := {z | |z.im| < 1 / 2}`
     - :17 "The threshold `½` is the half-width of the critical strip."
     - :56 `theorem ordinate_mem_strip`
     - :64 `rh_of_strip_cross`, :100 `rh_of_hypConvStrip_top`
     - :390 `hypConvStrip_of_close … (hclose : ∀ b < 1 / 2, Tendsto (fun n => Real.sqrt (2 * a n) * Real.exp (a n * b) * Real.sqrt (normSq fun t => g n t - φ n t)) atTop (𝓝 0))`
     - :419 `rh_of_close_top`, :437 `rh_of_relgap` (`hrel : ∀ b < 1 / 2, …`)
     - src/KernelChain.lean:31 `rh_of_close_RPhi` (`hclose : ∀ b < 1 / 2, …`)
   - Filler: src/HalfPlaneJoinsFinal.lean:43 `zeta_band_eleven_twelfths` and :56 `abs_im_tau_le_five_twelfths (i : ZeroIdx (sqF Xi)) : |(tau i).im| ≤ 5 / 12`. Every ordinate then lies in `|Im z| ≤ 5/12`.
   - Template: external/dh/DHColumn.lean:228 `def stripW (w : ℝ) : Set ℂ := {z | |z.im| < w}`, :233 `HypConvStripDH (a) (g) (w : ℝ)`, :237 `ordinate_mem_stripW`.
   - Gap: restate at width c. Hurwitz needs only an open strip that contains 0 and every ordinate. `kernelApprox_RPhi` is proved on `closedStrip 1`, which contains any strip with c ≤ 1. The closeness hypothesis weakens from every b < ½ to every b < c.
   - Recorded only for dh: README.md:8250 "The pilot's statements pinned at strip width `½` (`rh_of_strip_cross` and its kin) can be instantiated at `dh` only at width `2`…", and §7's round-271 card on `not_hypConvStripDH_of_cross`.
   - Commands:
     - `grep -n 'stripSet\|HypConvStrip\|hypConvStrip_of_close\|KernelApprox\|rh_of_strip_cross' README.md STRUCTURAL-REVIEW.md`: no hit after round 262.
     - `awk 'NR>=17188' README.md | grep '5/12\|width\|threshold'`: no hit on this.
   - The half-plane lets every RH criterion of StripConv and KernelChain take closeness rate e^{−b·a_n} for b < c, with any fixed c > 5/12, in place of b < ½.

3. **(A) The pinning radius with cosh(5a/12).**
   - Sockets:
     - src/Unconditional.lean:263 `(hstrip : ∀ i, |(t i).im| ≤ 1 / 2)` and :267 `(hr : Real.sqrt (Q + (2 * g 0 * Real.cosh (a / 2)) ^ 2 * S) / m ≤ r)`
     - the only use of `hstrip` is :281–283 `have hch : Real.cosh (a * |(t i).im|) ≤ Real.cosh (a / 2)` (grep `hstrip` finds lines 263, 283, 311 and 322 only)
     - src/ZetaInputs.lean:192 `theorem im_ordinate_zeta … ≤ 1 / 2`
     - :229 `pinned_zeta`, which discharges `hstrip` by `im_ordinate_zeta` at :252–254
     - src/ZetaJoins.lean:53 `pinned_zeta_zero`
   - Filler: `zeta_band_eleven_twelfths`.
   - Gap: a width parameter w in `pinned_unconditional`, with B = 2g(0)cosh(aw), and `im_ordinate_zeta` at 5/12. At a = 10, cosh(5) = 74.2 against cosh(25/6) = 32.3.
   - Not recorded: `awk 'NR>=17188' README.md | grep 'pinned\|cosh\|hstrip'` finds nothing relevant.
   - The ζ pinning theorems can use B = 2g(0)cosh(5a/12).

4. **(A) Θ-exact forms of the graded criteria.**
   - Sockets:
     - src/WeilLandau.lean:159–164. Docstring: "The exponential rate at which the twin form can go negative is exactly `2Θ − 1`, `Θ = sup Re ρ`." Statement: `weil_twins_rate {σ} (hσ : 0 ≤ σ) : (∃ C, …) ↔ ∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ`.
     - src/WeilRate.lean:81 `lam_rate … (hlt : σ < |2 * s.re - 1|) (C X : ℝ) : ∃ a, X < a ∧ lam a < -(C * Real.exp (σ * a))`
     - :105 `lam_fails_exponentially (hRH : ¬RiemannHypothesis) : ∃ δ > 0, …`
     - :43 `zeros_of_lam_ge`
     - WeilTwinGeneral.lean:94 `twins_rate_realRooted`
     - BohrJoins.lean:56 `shell_of_zeroFree`
   - Fillers:
     - external/pnt/PsiExponent.lean:31 `noncomputable def Theta : ℝ := sSup zeroReals`
     - :69 `zeta_ne_zero_of_Theta_lt`, :77 `exists_zero_re_gt {ε} (hε : 0 < ε) : ∃ ρ, IsNontrivialZero ρ ∧ Theta - ε < ρ.re`, :64 `half_le_Theta`
     - src/PsiOmega.lean:692 `band_of_zeroFree`
   - Gap: a pnt file importing WeilLandau, WeilRate and BohrJoins together with PsiExponent. TwinKV.lean:2 already imports WeilLandau and BohrKV.lean:2 imports BohrJoins. The proofs are about 15 lines each. For σ ≥ 0: (∃ C, ∀ l ≥ 0, −Ce^{σl} ≤ weilQ …) ↔ 2Θ − 1 ≤ σ; λ₁ fails at every rate σ < 2Θ − 1; the shell at Θ is the thinnest.
   - Recorded only as prose with an informal Θ: README.md:7373, and STRUCTURAL-REVIEW.md:211 "Graded: `weil_twins_rate` — the exponential rate of the negative part is `2Θ − 1`."
   - Commands: `grep -n 'Theta' src/*.lean external/*/*.lean`, filtered of the Kubota and Eisenstein names: no use outside PsiExponent, MertensExponent, HalfPlaneLindelof, DivisorExponent and SquarefreeCount. `grep '2Θ − 1'`: only README 7373, 8022 and STRUCTURAL-REVIEW 122, 211.
   - With `PsiExponent.Theta` defined, "rate = 2Θ − 1" can be a Lean theorem, as can its λ₁ and Bohr-shell companions; none is stated.

5. **(A) Half of the missing Prop ψ(x) − x = Ω±(√x).**
   - Socket: src/CrossCriteria.lean:125 `def PsiOmegaSqrt : Prop := ∃ c > 0, ∀ X : ℝ, (∃ x, X < x ∧ c * x ^ (1 / 2 : ℝ) < Chebyshev.psi x - x) ∧ (∃ x, X < x ∧ Chebyshev.psi x - x < -(c * x ^ (1 / 2 : ℝ)))`.
   - Fillers: external/pnt/PsiExponent.lean:88 `psi_omega_Theta {ε} (hε : 0 < ε) (hεΘ : ε < Theta) (c X : ℝ) : (∃ x, X < x ∧ c * x ^ (Theta - ε) < ψ x - x) ∧ …`, and MertensExponent.lean:270 `rh_iff_Theta_eq_half : RiemannHypothesis ↔ Theta = 1 / 2`.
   - Gap: if RH fails, Θ > ½; take ε = (Θ − ½)/2, c = 1 and X' = max X 1, so x^{1/2} ≤ x^{Θ−ε}. That gives `¬RiemannHypothesis → PsiOmegaSqrt`. The RH case remains.
   - Record: STRUCTURAL-REVIEW.md:272 "Missing: `Ω(x^{1/2})` itself (needs a zero *on* `Re = ½` …)". It does not mention the ¬RH half. `grep 'PsiOmegaSqrt' README.md STRUCTURAL-REVIEW.md` finds only README:141 and STRUCTURAL-REVIEW:31.
   - The missing Prop reduces to RH → PsiOmegaSqrt by a short case split.

6. **(A) `CoImportMV.GaussIdealCount` from the pnt quadratic-field layer.**
   - Socket: external/zeta23/CoImportMV.lean:96–101 "/-- The ideal count of `ℚ(i)` (as `CyclotomicField 4 ℚ`) is the pilot's radial coefficient `r₂(n)/4`. -/ def GaussIdealCount : Prop := ∀ n : ℕ, n ≠ 0 → (((Nat.card {I : Ideal (NumberField.RingOfIntegers (CyclotomicField 4 ℚ)) // Ideal.absNorm I = n} : ℕ) : ℂ) = AngularFamily.angularCoeff 0 n)". It sits in section "(3) missing Props, typechecked". Consumers: :104 `dedekindZeta_eq_angularL (h : GaussIdealCount)` and :109 `dedekindZeta_eq_zeta_mul_L (h : GaussIdealCount)`.
   - Fillers:
     - external/pnt/QuadIdeals.lean:472 `rA_eq {χ : ArithmeticFunction ℤ} (hχ : χ.IsMultiplicative) (hpow …) (htype : ∀ p, p.Prime → (χ p = 1 ∧ Split K p) ∨ (χ p = -1 ∧ Inert K p) ∨ (χ p = 0 ∧ Ramified K p)) : rA K = χ * zeta`
     - QuadKronecker.lean:305 `type_two_three (h23 : d % 4 = 2 ∨ d % 4 = 3) (hd0 : d ≠ 0) {p} (hp : p.Prime) : (jacTop d hd0 (p : ZMod (4 * d.natAbs)) = 1 ∧ QuadIdeals.Split K p) ∨ …`, with context `(hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d) (hK : Module.finrank ℚ K = 2)` at :283
     - QuadKronecker.lean :105 `jacTop_natCast`, :194 `charFun_mult`, :203 `charFun_pow`
     - src/AngularFamily.lean:42 `member_zero_coeff (hn : n ≠ 0) : angularCoeff 0 n = ∑ d ∈ n.divisors, ((ZMod.χ₄ d : ℤ) : ℂ)`
     - Mathlib: `jacobiSym.at_neg_one (hb : Odd b) : J(-1 | b) = χ₄ b` (JacobiSymbol.lean:311) and `IsCyclotomicExtension.finrank` (Cyclotomic/PrimitiveRoots.lean:177)
   - Gap: take d = −1 and s = ζ₄ (s² = −1); finrank = φ(4) = 2; χ = `charFun (jacTop (−1) _)`. Bridge `Nat.card` to `(QuadIdeals.ofNorm n).card`. CoImportMV.lean:1 already imports the pnt module `DetectEM`, and QuadIdeals imports Mathlib only.
   - Not recorded: `grep -rn GaussIdealCount --include=*.md` over the whole repository gives no hits.
   - Rounds 485–487 discharge the display, which makes the two `dedekindZeta` joins unconditional.

7. **(A, PAPER, not short) Subconvexity ζ(½+it) ≪ |t|^{5/24+ε}, which gives `ConvexityBound`.**
   - Sockets: src/CrossCriteria.lean:93 `def ZetaCritBound (c : ℝ) : Prop := ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ c` and :97 `def ConvexityBound : Prop := ∀ ε > 0, ZetaCritBound (1 / 4 + ε)`.
   - Filler: external/pnt/HalfPlaneLindelof.lean:463 `zeta_bound_eleven_twelfths {σ₀ ε} (hσ₀ : 11 / 12 < σ₀) (hε : 0 < ε) : ∃ T C, ∀ σ t, σ₀ ≤ σ → T ≤ |t| → ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ε ∧ …`. So μ(σ) = 0 for σ > 11/12. The functional equation gives μ(1/12) ≤ 5/12, and convexity gives μ(½) ≤ 5/24 = 0.2083 < ¼.
   - Gaps:
     - The size of the factor 2(2π)^{−s}Γ(s)cos(πs/2) on Re s = σ₀, needed for Mathlib's `riemannZeta_one_sub` (RiemannZeta.lean:177). Mathlib's Gamma files give no vertical-line bound. The stack's `Eis.exists_norm_Gamma_le` (KubotaStrip.lean:51, no decay) and `exists_norm_inv_Gamma_le` (:90, e^{π|Im s|}) are too weak.
     - A Phragmén–Lindelöf lemma with linearly interpolated exponents. Mathlib's `PhragmenLindelof.vertical_strip` and `Eis.poly_bound_strip` (KubotaStrip.lean:128) take one bound on both edges. `HalfPlaneLindelof.norm_le_interp` (:42) needs `‖F‖ ≤ A` on the whole rectangle, and with A = C|t| it gives only exponent ½.
   - Not recorded:
     - §6 Lindelöf (line 226): "Nothing: no subconvexity bound of any strength is in the three layers …"
     - §6 Zero density (line 224): "every pointwise bound on `ζ` in the stack is Euler–Maclaurin … or the Vinogradov region near `σ = 1`". This is stale since round 470.
     - §5b:194: "a subconvexity input would lower `A`".
     - README round 470 Check 9(b): "The Lindelöf entry's Missing Prop, on `Re s = ½`, stands."
   - Command: `grep -n '5/24\|subconvex\|ConvexityBound\|ZetaCritBound' README.md STRUCTURAL-REVIEW.md`.
   - Round 470's half-plane Lindelöf bound would give the stack's first subconvex exponent on the critical line. This is the input §5b and §6 name for lowering A.

8. **(A, trivial) Register §6, "Effective/explicit questions": "Missing Prop for any explicit statement: an explicit `A` in `zeroFree_KV` or an explicit `C` in `DensityXi`."**
   - Socket: external/pnt/LandauKV.lean:131 `zeroFree_KV : ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, Real.exp 3 ≤ |t| → 1 - A / (Real.log |t| ^ ((2 : ℝ) / 3) * Real.log (Real.log |t|) ^ ((1 : ℝ) / 3)) ≤ σ → ζ (σ + t * I) ≠ 0`.
   - Filler: src/KubotaThetaProof.lean:105 `ne_zero_of_re_gt_eleven_twelfths`.
   - Gap: arithmetic only. For |t| ≥ e³ the denominator is at least 3^{2/3}(log 3)^{1/3} = 2.146, so A = 1/6 gives 1 − A/(…) ≥ 1 − 0.0777 > 11/12.
   - Not recorded: line 276 has no marker. Its sentence "The stack contains no explicit numerical constant on the analytic side except in the certificate rounds" is also stale since round 484.
   - Side note: the same half-plane statements imply `ShortKV.zeroFreeXi_KV` and `PNTKV.PNT_KV`. With an adjusted constant they also imply `TwinKV.twins_lower_KV_sharp` and `BohrKV.shell_of_KV`.

9. **(F, and B) The λ₁ prefactor join is dominated by `lam_nine`.**
   - Docstring, src/HalfPlaneJoins.lean:18–19: "Unconditionally the exponent is `10a` (`lam_prefactor`), less a Korobov–Vinogradov saving `c·a^{1/3}/(log a)^{1/3}` in `external/pnt` (`lam_prefactor_KV`)."
   - Against it, src/KaiserNine.lean:47 `lam_nine : ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → lam a ≤ K * (a + 1) * Real.exp (9 * a - 4 * π * Real.exp (2 * a))`, from round 220, before round 279.
   - `HalfPlaneJoins.lam_prefactor_eleven_twelfths` (HalfPlaneJoinsFinal.lean:87, exponent 59/6·a) follows from `lam_nine` with the same K. `lam_prefactor_of_smoothBound` (8 + 2θ)·a is never below 9a, since θ ≥ ½ (`HalfPlanePNT.half_le_of_zeroFree`).
   - README.md:17349 (round 468): "`λ₁`: the exponent `10a` … becomes `(59/6)a`, a saving of `e^{a/6}`". README.md:8860 says the same.
   - Precedent: README.md:7868 (round 234), "This bound is weaker than round 220's `KaiserNine.lam_nine` … What round 234 adds is effectivity in principle, and nothing else", and STRUCTURAL-REVIEW F13 (line 140), which covers only the older bounds.
   - The round-468 prefactor is, as a Lean statement, a corollary of round 220's `lam_nine`. The docstring and README compare it with 10a only.

**Checked, no join**
- **`ShortPrimes.ZeroFreeXi α`:** the half-plane gives `ZeroFreeXi 0`, but θ in `short_primes_of_density` depends on A only. Recorded at README:8863.
- **`Rung3.KVInput n₁ 1` for every n₁ > 0:** dischargeable via `HalfPlanePNT.logDeriv_le_of_zeroFree`, but the conclusion is dominated by `psi_isBigO_eleven_twelfths`.
- **`Kaiser.lam_le_split` at Θ:** (8 + 2Θ)a ≥ 9a.
- **`CrossCriteria.NoRealZero` and every `hS` on (0,1) or (θ<½,1):** the half-planes cover only (11/12, 1).
- **`CrossCriteria.LamGradedConverse`:** its antecedent holds at 5/6, but the Prop is the missing implication itself.
- **DHChannels `LFunction_ratio_mul` (h1 h2):** needs s and 1 − s both in the half-plane.
- **Cubic Gauss-sum door:** `SmoothPerron.smoothedSum_eq_verticalIntegral_left` needs L holomorphic with linear growth on Re s ≥ σ'. D_m is continued only near 4/3, in 0 < Im s < π/r, with a pole at 4/3.
- **`KubotaPhi.zetaK_ne_zero` (Re ≥ 1):** the ζ_K half-plane would extend φ to Re s > 35/36, but no consumer needs it.
- **`KubotaCusps.kubotaData_of` and `KubotaTranslates.lemma61_of_kubotaTheta`:** already recorded in README round 468.
- **PhiDecay/PhiLadder `hs … ≤ 1/2`:** the conclusions decay faster than every exponential, so a narrower strip gains nothing.

**Stale register lines met on the way (not joins)**
- §6 RH entry, line 212: "What is proved unconditionally about the rate" omits round 468's 5/6.
- §6 RH entry, line 213: the list of RH equivalents omits `MertensExponent.rh_iff_Theta_eq_half` and `rh_iff_mertens`; `grep rh_iff_mertens STRUCTURAL-REVIEW.md` gives no hits.