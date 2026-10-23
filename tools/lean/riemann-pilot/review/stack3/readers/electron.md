<!-- Stack review 3 reader report: model output, a list of CANDIDATES, not findings. STRUCTURAL-REVIEW.md §9.2 and §9.7 record what the lead verified (Check 3). Scratchpad paths below are the reader's session files, not committed. -->

Running mandatory review protocol. Checks 0–9 active.

COVERAGE (Read tool, end to end)
src/CascadeLepton.lean: lines 1–489 read
src/ChargeLattice.lean: lines 1–139 read
src/DiracSpin.lean: lines 1–134 read
src/DistinguishedDims.lean: lines 1–539 read
src/BinetEnvelope.lean: lines 1–768 read
src/EulerGammaBinet.lean: lines 1–178 read
src/ThermalJoins.lean: lines 1–351 read
src/ThermalZeta.lean: lines 1–729 read
src/BoundaryLabels.lean: lines 1–403 read
src/BesselK.lean: lines 1–149 read
src/UpperHalfSpace.lean: lines 1–218 read
src/HilbertResolvent.lean: lines 1–375 read

I read STRUCTURAL-REVIEW.md lines 322–405 (§9) first. For comparison only, I read parts of these files: BinetProof 1–82 and 336–420; DigammaGauss 1–80 and 278–300; BallTower 125–207; KubotaBall 40–131; KubotaMeasure 215–340; KubotaEnergy 189–240; KubotaResidue 1–64; KubotaCTPrinciple 1–110; KubotaBallOp 1–40; KubotaBesselMellin 1–30 and 95–215; KubotaDerivative 40–70 and 112–145; KubotaThetaSeries 86–112; KubotaTheta 279–300; KubotaMellin 40–62, 136–170 and 226–258; KubotaCoefScalar 30–46; KubotaTranslates 232–246; external/dh/DHConstants.lean 1–40. I also read the Mathlib lines quoted below, from the pinned tree.

Items 1–2 are the classification you asked for of §9.4's existing CascadeLepton/ChargeLattice entry; they are not new findings. None of the other candidates appears in §9 (I checked against lines 322–405).

CANDIDATES

1. (C, classification of §9.4) src/CascadeLepton.lean
Checked: `grep -rn --include=*.lean -w NAME src external` for every declaration in the file. The 13 statements with no #print line and no user outside the group, with their in-file hits:
- diracLayers_29 :54
- dirac_sphere_even :59
- Rc_pos :64 (used at :125, :133)
- Gamma_three_halves :69 (used at :82, :89)
- Rc_one :79 (used at :95)
- Rc_two :86 (used at :100)
- Nc_one :94 (used at :104, :112)
- Nc_two :99 (used at :108)
- Nc_one_eq_integral :103
- Nc_two_eq_integral :107
- two_sqrt_pi_eq :111
- fermion_scalar_ratio :124
- sqrt_alphaC :131
Every hit is in CascadeLepton.lean.

Results that would deserve a #print axioms line:
- `theorem Nc_one : Nc 1 = 2` and `theorem Nc_two : Nc 2 = π / 2`.
  - The section heading `/-! ## The lapse: \`N(0) = π\`, \`N(1) = 2\`, \`N(2) = π/2\` -/` (:62) announces them.
  - Its first member, Nc_zero, is reachable only through the printed Nc_zero_mul_ne (:116, :484).
- `theorem Nc_one_eq_integral : Nc 1 = ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ (0 : ℕ)` and `theorem Nc_two_eq_integral : Nc 2 = ∫ x in (-1 : ℝ)..1, √(1 - x ^ 2)`.
- `theorem two_sqrt_pi_eq : 2 * √π = Nc 1 * Real.Gamma (1 / 2)`. It is the positive half of a contrast whose negative half, `theorem Nc_zero_mul_ne : Nc 0 * Real.Gamma (1 / 2) ≠ 2 * √π`, is printed.
- `theorem fermion_scalar_ratio (d : ℕ) : (Rc d / 2) / Nc d = 1 / (2 * √π)` and `theorem sqrt_alphaC (d : ℕ) : √(alphaC d) = Rc d / 2`. Together they make up the whole of `/-! ## The fermion obstruction factor -/` (:121).
  - The factor appears as a literal in `def leadRatio (a b : ℕ) : ℝ := Real.exp (PhiC b - PhiC a) * (2 * √π)` (:50) and in tauMuShifted (:440).
  - So these two, plus two_sqrt_pi_eq, are the only Lean statements about the factor, and none of them is checked.
- `theorem diracLayers_29 : diracLayers 29 = {5, 13, 21, 29} := by decide` and `theorem dirac_sphere_even {d : ℕ} (h : d % 8 = 5) : Even (d - 1)`. The printed nD_generations (:56) gives only the counts.

Scaffolding:
- Gamma_three_halves (see also 11a).
- Rc_one and Rc_two, which feed only Nc_one and Nc_two.
- Rc_pos, which feeds only the obstruction pair.

Candidate: nine of the 13 are stated results, and the other four are helpers that become reachable once those nine are printed.

2. (C/F, classification of §9.4) src/ChargeLattice.lean
Checked: `grep -rn --include=*.lean -w "hyper\|sm_hypercharges\|quark_charges\|hydrogen_neutral" src external` hits only ChargeLattice (hyper at :75 and :87–89; the others only at their definition lines). `grep -rln "^import ChargeLattice" src external` finds no importer.

- Result, quark_charges (:114):
  `theorem quark_charges : elCharge (1 / 2) (1 / 6) = 2 / 3 ∧ elCharge (-1 / 2) (1 / 6) = -1 / 3 ∧ elCharge 0 (2 / 3) = 2 / 3 ∧ elCharge 0 (-1 / 3) = -1 / 3`
  It is the quark counterpart of the printed electron_charge (:109, :138).
- Result, sm_hypercharges (:86):
  `theorem sm_hypercharges : hyper 1 = 1 / 6 ∧ hyper 4 = 2 / 3 ∧ hyper (-2) = -1 / 3 ∧ hyper (-3) = -1 / 2 ∧ hyper (-6) = -1 ∧ hyper 3 = 1 / 2`
  - This is exactly the content that the docstring of the printed sm_z6Trivial claims: "All pass the `ℤ₆` test, and their hypercharges are `1/6, 2/3, −1/3, −1/2, −1, 1/2`." (:78–79).
  - sm_z6Trivial's statement (:80–82) contains only the six `Z6Trivial` conjuncts (F).
- Scaffolding: `def hyper (q : ℤ) : ℚ := q / 6` (:75), used only by sm_hypercharges.
- hydrogen_neutral (:120), with the docstring at :119:
  `theorem hydrogen_neutral : 2 * (2 / 3 : ℚ) + (-1 / 3) + (-1) = 0 := by norm_num`
  - It mentions no definition from the file.
  - Its docstring, "`2Q_u + Q_d + Q_e = 0`: hydrogen (`uud` plus `e`) is neutral.", ties it to elCharge only in prose (F).
  - The printed anomaly_free (:124–129) is the same kind: literal hypercharges, not `hyper` values.

Candidate: quark_charges and sm_hypercharges are results, `hyper` is scaffolding, and hydrogen_neutral is a numeral check that carries meaning only if it is restated through elCharge.

3. (E, special attention 3) src/BoundaryLabels.lean:344, `set_option maxRecDepth 4000 in`
This is the only override in the 12 files: `grep -n set_option` over all 12 hits only BoundaryLabels:344, and there is no maxHeartbeats anywhere.

What the override covers:
- It sits on (:346–347): `theorem cascadeInv_lattice_bounds : (1.0216e-121 : ℝ) < Part0.cascadeInv 6 20 218 ∧ Part0.cascadeInv 6 20 218 < 1.0218e-121`.
- Its two numeric steps are `simp only [Nat.factorial]; norm_num` (:359, :365) on `(Nat.factorial 20 : ℝ) * (Nat.factorial 218 : ℝ)` and `225 * 2 ^ 232 * (Nat.factorial 10 : ℝ) * (Nat.factorial 109 : ℝ) * 3.141592 ^ 119`.

The same unfolding of large factorials appears elsewhere without an override (`grep -n "Nat.factorial\]"`):
- BoundaryLabels:175 (20!, 10!, 9!)
- BoundaryLabels:192 (218!, 109!, 108!)
- DistinguishedDims:493 and :497 (108!, 9!)

What Mathlib offers at the pin:
- Mathlib/Tactic/NormNum/NatFactorial.lean:15–16: "This is done by reducing each of these to `ascFactorial`, which is computed using a divide and conquer strategy that improves performance and avoids exceeding the recursion depth."
- The extension is `@[nolint unusedHavesSuffices, norm_num Nat.factorial _] def evalNatFactorial` (:66–67).

Only consumer: `grep -w cascadeInv_lattice_bounds` hits :24 (docstring), :346, :374 (paper_over_lattice) and :402.

Candidate:
- The override is a recursion-depth override, not a heartbeat override. Most likely it is needed because `simp only [Nat.factorial]` unfolds 218! into a product 218 levels deep.
- Plain `norm_num`, using Mathlib's factorial extension, is the candidate replacement. I have not built it.
- Separately, paper_over_lattice needs only the ratio I(7,19,217)/I(6,20,218) = (16/(5π))²·20!/(2²⁰·9!·10!)·218!/(2²¹⁸·108!·109!) ≈ 10.756. This follows from Om_six/Om_seven, Om_nineteen/Om_twenty and Om_two_seventeen/Om_two_eighteen, and π¹¹⁷ and π¹¹⁹ cancel in it.

4. (B, special attention 2) EulerGammaBinet and BinetEnvelope both prove the order-1 bounds
- phiB_order_one duplicates the round-406 pair exactly.
  - src/BinetEnvelope.lean:289–290: `theorem phiB_order_one {s : ℝ} (hs : 0 < s) : s / 12 - s ^ 3 / 720 ≤ PilotDigamma.phiB s ∧ PilotDigamma.phiB s ≤ s / 12`
  - It is identical to `⟨le_phiB hs, phiB_le hs⟩`, from src/EulerGammaBinet.lean:47 `theorem le_phiB {s : ℝ} (hs : 0 < s) : s / 12 - s ^ 3 / 720 ≤ phiB s` and :30 `theorem phiB_le {s : ℝ} (hs : 0 < s) : phiB s ≤ s / 12`.
  - Its own docstring (:287–288) names the two lemmas.
- lapR_stirling2's first conjunct duplicates le_lapR exactly.
  - BinetEnvelope:362–364 `lapR_stirling2`, first conjunct: `1 / (12 * x ^ 2) - 1 / (120 * x ^ 4) ≤ Electron.lapR x`.
  - EulerGammaBinet:125: `theorem le_lapR {x : ℝ} (hx : 0 < x) : 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4) ≤ lapR x`.
- The rest of round 406's bounds are K = 1 instances of BinetEnvelope's envelopes.
  - EulerGammaBinet:111 `theorem lapR_le {x : ℝ} (hx : 0 < x) : lapR x ≤ 1 / (12 * x ^ 2)` is `lapR_envelope 1` (BinetEnvelope:187) combined with stirC_zero.
  - phiB_le and le_phiB are `phiB_envelope 1` (:116).
- eulerMascheroni_eq repeats one step inline.
  - EulerGammaBinet:150–164 `eulerMascheroni_eq` takes real parts of digamma_eq_lap at z = 16 inline.
  - BinetEnvelope:218 `theorem rpsi_eq_lapR {x : ℝ} (hx : 0 < x) : PilotDigamma.rpsi x = Real.log x - 1 / (2 * x) - Electron.lapR x` is that same step for every x > 0.
Checked (`grep -w`):
- phiB_order_one: BinetEnvelope :15, :289, :736 only.
- le_phiB: EulerGammaBinet :47, :131; ThermalJoins :107.
- le_lapR: EulerGammaBinet :125, :171.
- lapR_le: EulerGammaBinet :111, :170.
- rpsi_eq_lapR: BinetEnvelope :218, :235, :366, :727.
- Import chain (`grep ^import`): BinetEnvelope → DistinguishedDims → ThermalJoins → CascadeLepton → EulerGammaBinet.
Candidate:
- phiB_order_one and the first conjunct of lapR_stirling2 restate round-406 lemmas word for word.
- The round-406 lemmas are the K = 1 (or x = 16) cases of BinetEnvelope's general theorems.
- The general theorems sit downstream, so they would have to move up the chain to replace the special cases.

5. (B, special attention 2) EulerGammaBinet against BinetProof and DigammaGauss
- integrableOn_exp_mul_phiB is the real case of BinetProof's integrableOn_lap.
  - EulerGammaBinet:74–75: `theorem integrableOn_exp_mul_phiB {x : ℝ} (hx : 0 < x) : IntegrableOn (fun s => Real.exp (-(x * s)) * phiB s) (Ioi 0)`
  - BinetProof:51–52: `theorem integrableOn_lap {z : ℂ} (hz : 0 < z.re) : IntegrableOn (fun s : ℝ => Complex.exp (-(z * s)) * (phiB s : ℂ)) (Ioi 0)`
  - Both proofs use the same domination by ½·e^{−xs} via abs_phiB_le, and EulerGammaBinet imports BinetProof (:2).
- EulerGammaBinet's general-k Γ-integral lemmas contain three older lemmas as special cases.
  - The general lemmas are EulerGammaBinet:85 `theorem integrableOn_pow_mul_exp {x : ℝ} (hx : 0 < x) (k : ℕ) : IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(x * s))) (Ioi 0)` and :92–93 `theorem integral_pow_mul_exp {x : ℝ} (hx : 0 < x) (k : ℕ) : ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(x * s)) = (1 / x) ^ (k + 1) * (k.factorial : ℝ)`.
  - At k = 1 they contain DigammaGauss:284 `theorem integrableOn_mul_exp_neg {c : ℝ} (hc : 0 < c) : IntegrableOn (fun t : ℝ => t * Real.exp (-(c * t))) (Ioi 0)` and :290 `theorem integral_mul_exp_neg {c : ℝ} (hc : 0 < c) : ∫ t in Ioi (0 : ℝ), t * Real.exp (-(c * t)) = 1 / c ^ 2`.
  - At k = 0 they contain BinetProof:63 `theorem integral_exp_neg_mul' {c : ℝ} (hc : 0 < c) : ∫ s in Ioi (0 : ℝ), Real.exp (-(c * s)) = 1 / c`.
  - All five lemmas come from the same Mathlib lemmas.
Checked:
- `grep -rn "integral_rpow_mul_exp_neg_mul_Ioi\|integrableOn_rpow_mul_exp_neg_mul_rpow" src external` hits BinetProof :66, DigammaGauss :286 and :294, EulerGammaBinet :87 and :94, plus Kubota, Eisenstein and DivisorExponent files.
- `grep -w integrableOn_lap` hits BinetProof :51 and :212.
Candidate: EulerGammaBinet re-proves the real case of BinetProof's integrability lemma, and states the general-k Γ integral whose k = 0 and k = 1 cases are three older lemmas upstream.

6. (B) src/ThermalZeta.lean:72–73 against src/BinetProof.lean:340–342
- ThermalZeta: `lemma hasSum_bose {t : ℝ} (ht : 0 < t) : HasSum (fun i : ℕ => Real.exp (-((i : ℝ) + 1) * t)) (bose t)`
- BinetProof: `theorem hasSum_bose {t : ℝ} (ht : 0 < t) : HasSum (fun n : ℕ => Real.exp (-((2 * π * ((n : ℝ) + 1)) * t))) (1 / (Real.exp (2 * π * t) - 1))`
Checked: `grep -w hasSum_bose` hits BinetProof :340, :396 and ThermalZeta :72, :132.
Candidate: BinetProof's lemma is ThermalZeta's at 2πt. Each is proved separately from hasSum_geometric_of_lt_one, and ThermalJoins imports both without relating them.

7. (B) BinetEnvelope, internally and against ThermalZeta
- summable_Zs is the natural-exponent case of ThermalZeta's summable_succ_rpow.
  - BinetEnvelope:57: `theorem summable_Zs {m : ℕ} (hm : 2 ≤ m) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ m)`
  - ThermalZeta:120–121: `lemma summable_succ_rpow {σ : ℝ} (hσ : 1 < σ) : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ σ)`
  - BinetEnvelope imports ThermalZeta.
- Zs_six repeats the proof of Zs_eq_bernoulli at j = 2.
  - BinetEnvelope:256–267: `theorem Zs_six : Zs 6 = π ^ 6 / 945`
  - :297–298: `theorem Zs_eq_bernoulli (j : ℕ) : Zs (2 * j + 2) = (-1) ^ j * 2 ^ (2 * j + 1) * π ^ (2 * j + 2) * bernoulli (2 * j + 2) / (2 * j + 2).factorial`
  - Both proofs are `(hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat …)`, then convert and tsum_eq.
Checked:
- `grep -w summable_Zs`: :57, :75, :718.
- `grep -w summable_succ_rpow`: ThermalZeta :120, :133, :147, :179, :220, :235.
Candidate: one restatement of an imported lemma, and one special case proved separately from its own general form.

8. (B) BinetEnvelope's real Γ_ℝ against Complex.Gammaℝ in ThermalJoins, ThermalZeta and BallTower
- hasDerivAt_log_gammaR against pC_eq_logDeriv.
  - BinetEnvelope:557–558: `theorem hasDerivAt_log_gammaR {s : ℝ} (hs : 0 < s) : HasDerivAt (fun t => Real.log (gammaR t)) (Part0.pR (s - 1)) s`
  - ThermalJoins:177–178: `theorem pC_eq_logDeriv (d : ℕ) : (Electron.pC d : ℂ) = logDeriv Complex.Gammaℝ ((d : ℂ) + 1)`
- gammaR_eq_two_div_OmR against the sphere-area identities.
  - BinetEnvelope:672: `theorem gammaR_eq_two_div_OmR {s : ℝ} (hs : 0 < s) : gammaR s = 2 / Part0.OmR (s - 1)`
  - ThermalZeta:446–447: `theorem gammaR_eq_two_div_sphereArea (n : ℕ) (hn : 1 ≤ n) : Complex.Gammaℝ (n : ℂ) = 2 / (BallTower.sphereArea n : ℂ)`
  - BallTower:187–188: `theorem Gammaℝ_mul_sphereArea (n : ℕ) (hn : 1 ≤ n) : Complex.Gammaℝ (n : ℂ) * (sphereArea n : ℂ) = 2`. Its inner `hreal` (:195–199) is the real identity at integer n.
Checked:
- `grep -rn -w gammaR src external` hits only BinetEnvelope (definition at :551 and its uses) and BoundaryLabels :296, :300.
- `grep -n Gammaℝ` in BinetEnvelope, BoundaryLabels and DistinguishedDims hits nothing.
Candidate: the BinetEnvelope theorems are the all-real-s forms of the integer-n statements about Complex.Gammaℝ, and grep finds no lemma relating BinetEnvelope.gammaR to Complex.Gammaℝ.

9. (B) DistinguishedDims against BinetEnvelope and the dh layer
- The integer thresholds follow from BinetEnvelope's located crossings.
  - The integer statements are DistinguishedDims:346 `theorem threshold_two : Electron.pC 217 < √π ∧ √π < Electron.pC 218`, together with threshold_one (:326), pC_six_neg (:173) and pC_seven_pos (:183).
  - They follow from BinetEnvelope:544–545 `theorem threshold_two_loc : ∃ x ∈ Ioo (217.62665 : ℝ) 217.62675, Part0.pR x = √π ∧ …`, with threshold_one_loc (:538) and zero_loc (:534), plus pR_strictMonoOn (:79) and pR_natCast (:45).
  - DistinguishedDims gets them from exact rational sums (harmonic 108 and a 109-term sum, :356–365). BinetEnvelope gets its located crossings from Stirling plus Taylor bounds (item 15).
- DistinguishedDims' log π bounds are weaker than the dh layer's.
  - DistinguishedDims:156 `theorem log_pi_gt : (1.1447 : ℝ) < Real.log π` and :164 `theorem log_pi_lt : Real.log π < 1.1448`.
  - external/dh/DHConstants.lean:17: `theorem log_pi_bounds : (11447296 : ℝ) / 10 ^ 7 < Real.log π ∧ Real.log π < (11447301 : ℝ) / 10 ^ 7`.
  - src/ is built before external/dh: external/dh/build.sh says "Usage: ./build.sh, after ../../build.sh". So DistinguishedDims cannot import the dh bound.
Checked: `grep -rn "log_pi_gt\|log_pi_lt\|log_pi_bounds\|1\.1447"` hits DistinguishedDims plus DHConstants :17 and :111, DHOddPacket :560 and DHCertificate :48.
Candidate:
- Four headline inequalities are computed twice, by different numerics, in files on the same import chain.
- The log π bounds duplicate a sharper bound that the layer order keeps out of reach.

10. (B) src/BoundaryLabels.lean:81–82 against src/BinetEnvelope.lean:635–637
- BoundaryLabels: `theorem tilt_max {c x0 : ℝ} (hx0 : -1 < x0) (h0 : Part0.pR x0 = c) : ∀ y, -1 < y → y ≠ x0 → tilt c y < tilt c x0`
- BinetEnvelope: `theorem strict_min_of_deriv {f g : ℝ → ℝ} {a x0 : ℝ} (hx0 : a < x0) (hf : ∀ x, a < x → HasDerivAt f (g x) x) (hneg : ∀ x, a < x → x < x0 → g x < 0) (hpos : ∀ x, x0 < x → 0 < g x) : ∀ y, a < y → y ≠ x0 → f x0 < f y`
- At c = 0, tilt_max is the Ω clause of three_landmarks in log form. That clause is `(∀ y, -1 < y → y ≠ x → Part0.OmR y < Part0.OmR x)` (BinetEnvelope:684), and crossings_maximize (BoundaryLabels:255) restates it.
Checked:
- `grep -w strict_min_of_deriv`: BinetEnvelope :635, :696, :704, :711.
- `grep -w tilt_max`: BoundaryLabels :81, :262, :264, :266.
Candidate: tilt_max is strict_min_of_deriv applied with f = −tilt c, g = pR − c and a = −1, using hasDerivAt_tilt and pR_strictMonoOn. BoundaryLabels imports BinetEnvelope.

11. (B) Lemmas that duplicate Mathlib at the pinned commit
a. src/CascadeLepton.lean:69: `theorem Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2`
   - This is Mathlib `lemma Real.Gamma_nat_add_one_add_half (k : ℕ) : Gamma (k + 1 + 1 / 2) = (2 * k + 1 : ℕ)‼ * √π / (2 ^ (k + 1))` at k = 0 (Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:330).
   - The same file already uses the sibling lemma Real.Gamma_nat_add_half (:380, :396).
b. CascadeLepton.lean:257: `theorem exp_nat (n : ℕ) : Real.exp n = Real.exp 1 ^ n`
   - This is the symmetric form of `@[simp] lemma exp_one_pow (n : ℕ) : exp 1 ^ n = exp n` (Analysis/SpecialFunctions/Pow/Real.lean:79).
c. src/ThermalZeta.lean:592–593: `lemma integral_exp_quad {α : ℝ} (hα : 0 < α) (β : ℝ) : ∫ y : ℝ, Real.exp (-α * y ^ 2 + β * y) = √(π / α) * Real.exp (β ^ 2 / (4 * α))`
   - This is the real case of `theorem _root_.integral_cexp_quadratic (hb : b.re < 0) (c d : ℂ) : ∫ x : ℝ, cexp (b * x ^ 2 + c * x + d) = (π / -b) ^ (1 / 2 : ℂ) * cexp (d - c ^ 2 / (4 * b))` (Analysis/SpecialFunctions/Gaussian/FourierTransform.lean:173).
d. ThermalZeta.lean:249–250: `theorem mellin_boltz {s : ℂ} (hs : 0 < s.re) : mellin (fun t => (Real.exp (-t) : ℂ)) s = Complex.Gamma s`
   - This is Complex.Gamma_eq_integral composed with `theorem GammaIntegral_eq_mellin : GammaIntegral = mellin fun x => ↑(Real.exp (-x))` (Analysis/SpecialFunctions/Gamma/Deriv.lean:48).
   - Its proof (:251–253) repeats the unfolding that the Mathlib lemma already does.
e. src/HilbertResolvent.lean:38–39: `theorem im_inner_apply_self {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (x : E) : (⟪A x, x⟫_ℂ).im = 0`
   - This is `hA.isSymmetric.im_inner_apply_self x`, from Mathlib `theorem IsSymmetric.im_inner_apply_self {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) : im ⟪T x, x⟫ = 0 := conj_eq_iff_im.mp <| hT.conj_inner_sym x x` (Analysis/InnerProductSpace/Symmetric.lean:145–147). The proof is the same.
   - Also, isSelfAdjoint_sub_real (:138–144) re-derives `protected lemma IsSelfAdjoint.algebraMap {r : R} (hr : IsSelfAdjoint r) : IsSelfAdjoint (algebraMap R A r)` (Algebra/Star/Module.lean:240). The instance `StarModule 𝕜 (E →L[𝕜] E)` it needs is at Analysis/InnerProductSpace/Adjoint.lean:269.
Checked: grep of the Mathlib tree for each name (lines above). `grep -rn "Gamma (3 / 2)\|Gamma_three_halves" src external` hits only CascadeLepton :69, :82, :89.
Candidate: these five lemmas restate, or re-derive, Mathlib lemmas that exist at the pin.

12. (B, minor) src/DistinguishedDims.lean:224 and :228 against src/BallTower.lean:161–164
- `theorem Om_six : Om 6 = 16 * π ^ 3 / 15` and `theorem Om_seven : Om 7 = π ^ 4 / 3`, both proved by `unfold …sphereArea; rw […]; push_cast; ring`.
- Inside sphereArea_lt_seven (BallTower:158), the local `have e7 : sphereArea 7 = 16 * π ^ 3 / 15` and `have e8 : sphereArea 8 = π ^ 4 / 3` are the same facts with the same proof text.
Checked: read both; `grep -rn "sphereArea [0-9]"` hits BallTower :158–168, DistinguishedDims :221–229 and BoundaryLabels :130–135, :271.

13. (D) CascadeLepton: two pairs of proofs that differ only in their numbers
- PhiC_21_sub_13 (:188–206) and PhiC_13_sub_5 (:209–227).
  - Statements: `theorem PhiC_21_sub_13 : PhiC 21 - PhiC 13 = 3195110257 / 232792560 - 4 * eulerMascheroniConstant - 4 * Real.log 2 - 4 * Real.log π` and `theorem PhiC_13_sub_5 : PhiC 13 - PhiC 5 = 62093 / 5544 - 4 * eulerMascheroniConstant - 4 * Real.log 2 - 4 * Real.log π`.
  - Both run the same 17 lines: PhiC_sub, `show Ioc … = {…} by decide`, seven `Finset.sum_insert (by decide)`, eight pC_even/pC_odd haves, then `simp only [harmonic, …]; push_cast; ring`. Only the layer numbers change.
- Rc_21 (:374–383) and Rc_14 (:390–398) share the skeleton `rw [Rc, h1, h2, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_add_half, hf, hd]`.
Candidate: one lemma for the eight-layer window (8m+5, 8m+13] would give both PhiC values.

14. (D/E) CascadeLepton: leadRatio_13_21_bounds (:285–326) and leadRatio_5_13_bounds (:329–370)
- Statements: `theorem leadRatio_13_21_bounds : (206.4957 : ℝ) < leadRatio 13 21 ∧ leadRatio 13 21 < 206.4959` and `theorem leadRatio_5_13_bounds : (16.52999 : ℝ) < leadRatio 5 13 ∧ leadRatio 5 13 < 16.53001`.
- Both are the same 42-line interval proof: exp_ge_of/exp_le_of, pi_gt_d20/pi_lt_d20, sqrt_pi_gt/lt, two `simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num` blocks, and two gcongr steps for π⁴.
- Only the numerals change: n = 11 vs 8, N = 10 vs 14, the split r, and the targets.
Candidate: one lemma taking q and an enclosure of q − 4γ, applied through leadRatio_closed, would give both.

15. (D/E) BinetEnvelope: six near-generated proofs
- pR_lo0 (:432–444), pR_hi0 (:447–461), pR_lo1 (:464–478), pR_hi1 (:481–497), pR_lo2 (:500–513), pR_hi2 (:516–531).
- All six follow one 13–17-line skeleton:
  - rpsi_le_shift or le_rpsi_shift at y0;
  - log_lt_of_lt_mul_exp or lt_log_of_mul_exp_lt, fed by `lt_mul_exp_of`/`mul_exp_lt_of _ 12 …`;
  - `simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num` on 12-digit decimals raised to powers up to the 11th;
  - an hB bound by norm_num;
  - `unfold Part0.pR; rw [show …]; linarith`.
- They differ only in numerals, the shift N (4 or 0) and P (π or π²).
Candidate: one lemma per direction would replace all six.

16. (D) Three copies of the same log-derivative proof
- Locations:
  - DistinguishedDims:126–152: `theorem hasDerivAt_log_OmR {x : ℝ} (hx : -1 < x) : HasDerivAt (fun y => Real.log (OmR y)) (-pR x) x`
  - BinetEnvelope:557–580: `theorem hasDerivAt_log_gammaR …`
  - BinetEnvelope:583–606: `theorem hasDerivAt_log_ballV {t : ℝ} (ht : -2 < t) : HasDerivAt (fun u => Real.log (ballV u)) (-Part0.pR (t + 1)) t`
- All three run the same 24–27-line skeleton:
  - differentiability of `Real.log ∘ Real.Gamma` via real_ne_neg_nat;
  - the derivative of an affine map, then comp;
  - `.mul_const (Real.log π)`;
  - an eventual equality by filter_upwards through log_mul or log_div and log_rpow;
  - `convert … ; ring`.
- The affine maps are (x+1)/2, s/2 and t/2+1.
Candidate: one lemma for d/dt log(π^{affine}·Γ(affine)^{±1}) would give all three.

17. (D) BoundaryLabels: lattice_one (:213–226) and lattice_two (:229–241)
- Statements: `theorem lattice_one : ∀ d : ℕ, d ≠ 20 → tilt (Real.log π / 2) d < tilt (Real.log π / 2) 20` and `theorem lattice_two : ∀ d : ℕ, d ≠ 218 → tilt √π d < tilt √π 218`.
- The 14-line proofs are identical apart from renamings:
  - 19/20 becomes 217/218;
  - threshold_one_loc becomes threshold_two_loc;
  - step_19_20 becomes step_217_218;
  - `Real.log_mul …, Real.log_sqrt …` becomes `Real.log_mul …, Real.log_exp`.

18. (D, special attention 2, BesselK) The same bound block is written out four times in the Kubota files
- It composes two BesselK lemmas:
  - src/BesselK.lean:90 `theorem norm_besselK_le (ν : ℂ) (x : ℝ) : ‖besselK ν x‖ ≤ (1 / 2) * bkR ν.re x`
  - :119–120 `theorem bkR_le_exp {r x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x) : bkR r x ≤ Real.exp (-(x / 2)) * bkR r (x₀ / 2)`
- The 9–10-line block, in order:
  1. `have hK := norm_besselK_le (1 / 3 : ℂ) (4 * Real.pi * ‖σO m‖ * X / 9)`
  2. `have hre : (1 / 3 : ℂ).re = 1 / 3 := by norm_num` and `rw [hre] at hK`
  3. hx₀, then hxx proved by `rw [div_le_div_iff_of_pos_right (by norm_num)]; … nlinarith`
  4. `have hdecay := bkR_le_exp (r := 1 / 3) hx₀ hxx`
- It appears at:
  - src/KubotaDerivative.lean:119–128
  - src/KubotaThetaSeries.lean:92–101
  - src/KubotaTheta.lean:281–289
  - src/KubotaMellin.lean:139–148
Checked: `grep -rn "norm_besselK_le (1 / 3\|bkR_le_exp (r := 1 / 3)\|have hre : (1 / 3 : ℂ).re = 1 / 3" src` hits exactly these four. KubotaMellin:230–231 starts the same block but uses bkR_third_le instead.
Candidate: one BesselK lemma, ‖besselK ν x‖ ≤ ½·e^{−x/2}·bkR ν.re (x₀/2) for 0 < x₀ ≤ x, would replace the four copies.

19. (A, special attention 2, BesselK) Generic K_ν lemmas live outside BesselK.lean
- These use only BesselK's API, but are defined in Kubota files:
  - src/KubotaDerivative.lean:44: `theorem continuousAt_besselK (ν : ℂ) {x : ℝ} (hx : 0 < x) : ContinuousAt (besselK ν) x`
  - src/KubotaTranslates.lean:237: `theorem besselK_ofReal (r x : ℝ) : besselK (r : ℂ) x = ((1 / 2 * bkR r x : ℝ) : ℂ)`
  - src/KubotaPmTheta.lean:432: `theorem bkR_pos {x : ℝ} (hx : 0 < x) (r : ℝ) : 0 < bkR r x`
- One is stated for ν = 1/3 only.
  - src/KubotaCoefScalar.lean:34: `theorem besselK_third_ne_zero {u : ℝ} (hu : 0 < u) : besselK (1 / 3) u ≠ 0`, proved from besselK_third_ofReal and `bkR_pos hu (1 / 3)`.
  - With besselK_ofReal the same two steps give `besselK (r : ℂ) u ≠ 0` for every real r.
- I found no re-proof of a BesselK lemma.
  - KubotaBesselMellin builds on bkK and besselK (integral_bkK :136, mellin_besselK :207).
  - `grep -n -i "bessel\|bkK" src/KubotaBall.lean` finds nothing.
Checked: `grep -rn "theorem besselK_\|theorem continuousAt_besselK\|theorem bkR_pos\|theorem bkR_third_le" src` hits KubotaDerivative:44, KubotaTranslates:237, KubotaMellin:45 and :346, KubotaCoefScalar:34, KubotaPmTheta:432.

20. (D, special attention 2, UpperHalfSpace) The decomposition proof over uhsAct is written three times
- Locations:
  - src/KubotaMeasure.lean:314–337: `theorem uinv_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : UInv (actP g)`
  - src/KubotaBall.lean:102–128: `theorem pinv_actP … : PInv (actP g)`
  - src/KubotaEnergy.lean:211–234: `theorem conf_actP … : Conf (actP g)`
- The 24-line bodies are identical:
  - `by_cases hc : g 1 0 = 0`;
  - `g = !![g 0 0, 0; 0, (g 0 0)⁻¹] * !![1, g 0 1 / g 0 0; 0, 1]`;
  - `g = !![1, g 0 0 / g 1 0; 0, 1] * !![0, -1; 1, 0] * !![g 1 0, 0; 0, (g 1 0)⁻¹] * !![1, g 1 1 / g 1 0; 0, 1]` with `linear_combination -hdet`;
  - the h1/h2 determinant steps.
  - Only UInv.mul/hmul/Conf.mul and the generator lemma names change.
- One more inline copy: KubotaEnergy:189–195 `theorem actP_E_eq (p : ℂ × ℝ) : actP !![0, -1; 1, 0] p = tauR (psiInv p)` is proved, with the same text, inline in uinv_actP_E (KubotaMeasure:284–291).
- The generator facts sit outside UpperHalfSpace.
  - They are uhsAct_diag, det_transl, det_E and det_diag (KubotaMeasure:229, :293, :296, :299).
  - They belong beside UpperHalfSpace's uhsAct_transl (:189) and uhsAct_inv (:193).
Checked: `grep "g 0 0 / g 1 0; 0, 1\] \* !!\[0, -1; 1, 0\]\|linear_combination -hdet" src` hits KubotaMeasure :325, :328, KubotaEnergy :222, :225 and KubotaBall :116, :119. The other `-hdet` hits are unrelated cub_congr steps.
Candidate: one induction principle would replace the three proofs. It would say that a predicate closed under products of det-1 matrices, and true for translations, diagonals and E, holds for every det-1 matrix.

21. (A, special attention 2, HilbertResolvent)
- KubotaResidue's tendsto_resolvent_curve_ev strictly generalizes HilbertResolvent's tendsto_resolvent_curve.
  - src/KubotaResidue.lean:39–43: `theorem tendsto_resolvent_curve_ev (hA : IsSelfAdjoint A) {l d c : ℝ} … (him : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * ε ≤ (ℓ ε).im) …`
  - src/HilbertResolvent.lean:266–268: `theorem tendsto_resolvent_curve … (him : ∀ ε : ℝ, 0 < ε → c * ε ≤ (ℓ ε).im) …`
  - The generalization sits in a generic `section Curve` (KubotaResidue:32–59) with no Kubota content.
  - The original's only use is in that proof (KubotaResidue:57).
- KubotaCTPrinciple has a generic Hilbert-space section about HilbertResolvent's kerAt.
  - The section is `section Hilbert`, lines 40–102. It contains starProjection_kerAt_mem (:56) and inner_starProjection_kerAt_eq_zero (:96).
  - It also contains `theorem orthogonal_invariant (hA : IsSelfAdjoint A) {S : Submodule ℂ E} (hS : ∀ x ∈ S, A x ∈ S) : ∀ y ∈ Sᗮ, A y ∈ Sᗮ` (:46–47).
  - orthogonal_invariant is Mathlib's `lemma orthogonalComplement_mem_invtSubmodule (hp : p ∈ T.invtSubmodule) : pᗮ ∈ T.invtSubmodule` (namespace LinearMap.IsSymmetric, Analysis/InnerProductSpace/Semisimple.lean:30) with T = A.
- KubotaBallOp has no duplicate.
  - It imports HilbertResolvent (:2) but uses none of its 23 declarations.
  - A per-name grep shows the users are only KubotaGHolo (:33, :34, :666, :672, :680, :689), KubotaResidue and KubotaCTPrinciple.
Candidate: the generic resolvent and kerAt results of rounds 425 and 438 sit in Kubota files, and one of them duplicates Mathlib.

22. (A) src/ChargeLattice.lean: the header's chain is never composed in Lean
- Header (:13–15): "With the sector minima, `Y_H = ½`, and gauge invariance of the lepton Yukawa singlet `L̄He_R`, a nonzero `Y_e` forces `Y_L = −½` and `Y_e = −1` (`lepton_hypercharges`). With `Q = T₃ + Y`, the electron has charge `−1` in both chiralities and the neutrino `0` (`electron_charge`)."
- The three statements it cites:
  - :98–99: `theorem lepton_hypercharges (YL Ye : ℚ) (hL : YL = 1 / 2 ∨ YL = -1 / 2) (hyuk : Ye = YL - 1 / 2) (he : Ye ≠ 0) : YL = -1 / 2 ∧ Ye = -1`
  - :109–110: `theorem electron_charge : elCharge (-1 / 2) (-1 / 2) = -1 ∧ elCharge 0 (-1) = -1 ∧ elCharge (1 / 2) (-1 / 2) = 0`
  - :60 minimal_charge
Candidate:
- electron_charge evaluates elCharge at literal hypercharges, not at lepton_hypercharges' conclusions.
- hL is not derived from `minimal_charge 0 1` through `hyper`.
- So no Lean statement carries the chain from the sector rule to the electron's charge.

23. (A) src/DiracSpin.lean: dirac_square's Clifford hypothesis is never discharged
- The hypothesis is `(hcl : ∀ μ ν, γ μ * γ ν + γ ν * γ μ = 2 * (η μ ν : A))` (:30), and no theorem instantiates it.
- pauli_mul gives it for γ = pauli and η = δ, since ε is antisymmetric: `theorem pauli_mul (i j : Fin 3) : pauli i * pauli j = (if i = j then 1 else 0) + I • ∑ k, (eps i j k : ℂ) • pauli k` (:96–97).
- g_eq_two takes the matching as a scalar hypothesis: `theorem g_eq_two {e m g : ℝ} (he : e ≠ 0) (hm : m ≠ 0) (h : e / (2 * m) = g / 2 * (e / m) * (1 / 2)) : g = 2` (:121–122).
Checked: `grep -rn -w "dirac_square\|pauli_mul\|levi_civita_contract\|g_eq_two" src external` hits only DiracSpin (the definitions and #print lines).
Candidate: the file's pieces are not composed. The header (:17–18) says "this file proves the algebra only", so this is a door, not a mismatch.

24. (A) BinetEnvelope's coefficients are not connected to riemannZeta
- BinetEnvelope defines its own series:
  - :55: `def Zs (m : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ m`
  - :62: `def stirC (j : ℕ) : ℝ := 2 * Zs (2 * j + 2) / (2 * π) ^ (2 * j + 2)`
  - :269 `theorem stirC_zero : stirC 0 = 1 / 12` and :275 `theorem stirC_one : stirC 1 = 1 / 720`
- ThermalJoins states the same coefficients with riemannZeta (:113–115): `theorem highT_coeffs : (1 / 12 : ℂ) = 2 * riemannZeta 2 / (2 * π) ^ 2 ∧ (1 / 720 : ℂ) = 2 * riemannZeta 4 / (2 * π) ^ 4`.
- Mathlib has the bridge material: `theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) : riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k` (NumberTheory/LSeries/RiemannZeta.lean:222).
Checked: `grep -n riemannZeta src/BinetEnvelope.lean` finds nothing, and the Zs series pattern occurs only in BinetEnvelope.
Candidate: no lemma relates Zs to riemannZeta, so highT_coeffs is not obtained as the j = 0, 1 case of stirC_eq_bernoulli.

25. (C) Two helpers whose only use is their own #print line
- src/BoundaryLabels.lean:107–108: `theorem tilt_lattice_max_down {c x0 : ℝ} {m : ℕ} (hx0 : -1 < x0) (h0 : Part0.pR x0 = c) (hlo : (m : ℝ) < x0) (hhi : x0 < m + 1) (hstep : tilt c (m + 1) < tilt c m) : ∀ d : ℕ, d ≠ m → tilt c d < tilt c m`
  - `grep -w` hits :17 (header list), :107 and :384 (#print).
  - The lattice maxima use tilt_lattice_max_up (:222, :237) or Om_lt_six (:208) instead.
- src/ThermalZeta.lean:545: `lemma cycleSign_succ (i : ℕ) : ((cycleSign (i + 1) : ℤ) : ℝ) = (-1) ^ i`
  - `grep -w` hits :545 and :722 (#print).
  - hasSum_fermi and mellin_fermi (:93, :214) use `(-1) ^ i` directly.
  - So the header's "The fermion versions carry the sign `(−1)^{k−1}` of a `k`-cycle (`cycleSign`)" (:19–20) rests only on this unused lemma.

26. (E) Heavy evaluation, not timed, with no override
- DistinguishedDims threshold_two (:346):
  - :356–357: `have hq : harmonic 108 < (526397 / 100000 : ℚ) := by simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num`
  - :364–365: `have hs : (6.65486 : ℝ) < ∑ j ∈ Finset.range 109, 1 / ((j : ℝ) + 1 / 2) := by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num`
  - These are exact 108- and 109-term rational sums, with constants tight to about 10⁻⁶ (H₁₀₈ ≈ 5.263969, Σ ≈ 6.654862).
  - The conclusion needs only H₁₀₈ < 2√π + γ + log π ≈ 5.26685 and Σ > 2√π + 2 log 2 + γ + log π ≈ 6.65315. The statement also follows downstream (item 9).
- DistinguishedDims:492–497 (cascadeInv_bounds: 9!, 108!, 3.141592^117) and BoundaryLabels:190–192 (step_217_218: 218!, 109!, 108! and a 12-term Taylor sum) both unfold factorials with `simp only [… Nat.factorial]` (see item 3).
- src/DiracSpin.lean:98–99, in pauli_mul: `fin_cases i <;> fin_cases j <;> (ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, eps, Matrix.mul_apply, Fin.sum_univ_two])`. That is 36 bare simp calls over Fin 3 sums and eps's if-chains.

27. (F) src/ThermalJoins.lean:11 claims more than the file proves
- Header: "Every statement is an identity between existing definitions."
- Two statements are inequalities:
  - :57: `theorem pressureBoltz_six_lt (hd : 1 ≤ d) (h6 : d ≠ 6) : pressureBoltz 6 1 < pressureBoltz d 1`
  - :105–106: `theorem bose_highT_bounds {s : ℝ} (hs : 0 < s) : 1 / s - 1 / 2 + s / 12 - s ^ 3 / 720 ≤ bose s ∧ bose s ≤ 1 / s - 1 / 2 + s / 12`

28. (F, cosmetic) src/EulerGammaBinet.lean:166 claims one digit too many
- Docstring: "**Euler's constant to seven digits**: `0.57721566 < γ < 0.57721580`." The title at :4 also says "Euler's constant to seven digits".
- Statement (:167–168): `theorem eulerMascheroni_bounds : (0.57721566 : ℝ) < Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant < 0.57721580`
- The interval has width 1.4×10⁻⁷, so it fixes six decimals; the seventh could be 6, 7 or 8.

29. (F, cosmetic) src/BesselK.lean:26 uses the wrong name for the function
- Docstring: "**The Bessel function of the second kind**, `K_ν(x) = ½∫_0^∞ t^{ν−1}e^{−x(t + 1/t)/2} dt`", on (:28) `def besselK (ν : ℂ) (x : ℝ) : ℂ := (1 / 2 : ℂ) * mellin (fun t => (bkK x t : ℂ)) ν`.
- This is the modified Bessel function of the second kind (K_ν). Mathlib's Analysis/SpecialFunctions/Bessel.lean:36–38 lists "Bessel function of the second kind" (Y_ν) under TODO.