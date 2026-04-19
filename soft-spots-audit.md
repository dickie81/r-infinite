# Unacknowledged Soft Spots — Cascade Derivation Chain Audit

Scope: soft spots in the cascade's derivation chain that are **not** flagged by the papers themselves in their "What this paper does/does not do" or "Open questions" sections. Identified via direct re-reading of the load-bearing theorems and proofs; each citation is `file:line`.

Gaps that the papers *do* acknowledge (Gram-matrix second-order correction, variational max-over-min, "observer at $d=4$ is empirical", the $k_Q$ coefficient, the $6\pi$ screening in $\alpha_{\rm em}$, the second $G_d$ route, etc.) are **excluded** from this file by construction.

Coverage: Prelude, Part 0, Part 0 Supplement, Part I, Part II, Part III, Part II=III, Part IVa, Part IVb.

**Status.** 20 of the original 37 soft spots have been closed in hardening commits (SP-1, SP-2, SP-3, SP-4, SP-5, SP-6, SP-8, SP-10, SP-15, SP-19, SP-21, SP-22, SP-23, SP-25, SP-28, SP-29, SP-31, SP-32, SP-33, SP-37). This file now tracks the **17 open items** that remain. Closures are recorded with commit hashes in the "Closed items (reference)" section at the end, for traceability.

**Note on the Prelude.** All Prelude soft spots (SP-1 through SP-4) are closed. The Prelude is an *exploration* of what the true minimum starting point of the cascade might be, not the load-bearing first link in the derivation chain. The series' hypothesis — that $B^\infty$ descended to 4D is indistinguishable from our universe — is stated independently in the cover sheet and does not depend on the Prelude's $0\ne 1 \to B^\infty$ chain.

## Severity scale

- **Exploratory** — occurs in a paper whose function is to probe a minimum starting point, not to prove one. Worth tightening if the paper is later promoted to load-bearing; not blocking downstream hardening.
- **Foundational** — affects whether the cascade starts from "one axiom" as advertised.
- **High** — directly affects a headline numerical claim.
- **Structural** — affects a derivation step whose conclusion is re-used downstream.
- **Minor** — affects presentation or first-order approximation; numerical impact below stated uncertainties.

---

## Part 0

### SP-7. Theorem 8.4 — "scale = ratio, content = product" is rationalised, not forced — **Structural**
`src/cascade-series-part0.tex:574–631`.

Two references can combine as a product (geometric mean); two independent outputs of a multiplicative recurrence are just scalars combinable arbitrarily. Structural stability selects *which* dimensions are scale vs content; it does not select the combining operation for each class. Remark 8.5 denies this is a definition.

---

## Part 0 Supplement

### SP-9. $\Omega_m^{\rm Bott}$ path applied to a ratio-of-sums observable — **Structural**
`src/cascade-series-part0.0.tex:231–239`, cf Part V Theorem 5.10.

Theorem 15.11 proves the correction *"for a multiplicative propagator"* traversing a contiguous path. $\Omega_m^{\rm Bott}$ is a ratio of sums over non-trivial-phase layers, not a multiplicative propagator. The application to $\Omega_m^{\rm Bott}$ is an unstated extension.

---

## Part I

### SP-11. Exponential form $\exp(\sum(1-C^2))$ not derived in the Supplement — **Minor**
`src/cascade-series-part1.tex:437` vs `src/cascade-series-part0.0.tex:214`.

Theorem 15.11 gives $\delta Q/Q_0 = \sum(1-C^2)$ (linear). Part I promotes to $Q = Q_0\cdot\exp(\sum)$. Agreement at $O(10^{-4})$ for the numerical value $\sum=0.02108$, below Planck's $1.9\%$ uncertainty; formally an unstated first-order $\to$ exponential promotion.

### SP-12. "Observer's host at $d_V=5$" — semantic move imported from Cover Sheet — **Structural**
`src/cascade-series-part1.tex:86–103`.

Part 0 identifies $d_V=5$ as the mathematical argmax of $V_d$. The further step "this is the observer's host" is a Part I–specific modelling identification sourced from the cover sheet's thought experiment, not from any theorem. It is what licenses Correction 1's $d_0\to d_V$ frame conversion.

### SP-13. "Free dimension" is physical, not mathematically characterised (Remark 3.1) — **Structural**
`src/cascade-series-part1.tex:175–202`, applied in `:135–141`.

The "3 free dimensions, 1 locked" reading relies on:
1. Time-$=$-slicing-direction (Part II content used in Part I).
2. Per-$S^2$ content density as the native cascade object (Part IVb content used in Part I).
3. An equivocation between "$n$ free dimensions" and "receiving volume $\Omega_n$": had the argument been "4 free dimensions", the boundary $S^3$ (area $\Omega_3$) would still be the natural receiving surface.

### SP-14. Frame-factor squaring inherits orbit-termination $n=2$ — **Structural**
`src/cascade-series-part1.tex:118–120`, ref Part 0 Lemma 8.8 and Theorem 6.5.

$(9/\pi^2)$ follows from two factors of $\Omega_5/\Omega_7$. Two factors because there are two thresholds (orbit termination, Part 0 Theorem 6.5). Orbit termination has its own soft spots (SP-5, SP-7). A third canonical value would upshift $\rho_\Lambda$ by $3/\pi\approx 0.95$ — a ~5% contingency. Part I does not name this sensitivity.

---

## Part II

### SP-16. Identification "$J$ evolves states" is a modelling step — **Structural**
`src/cascade-series-part2.tex:490–507`; downstream at `src/cascade-series-part3.tex:372–385`.

Theorem 6.1 proves a *static* relation: consecutive slicing axes sit at $\pi/2$. Theorem 6.4 constructs a specific SO(2) rotation $J: e_1\mapsto e_2,\,e_2\mapsto -e_1$ in the $e_1$–$e_2$ plane and promotes it to a *dynamical* complex structure on the Hilbert space. Orthogonal axes permit such a rotation to be defined; they do not force it to be the cascade's evolution operator. The paper denies this is an assumption: *"Since $\alpha=\pi/2$ is forced, this complex structure is not introduced as an assumption but derived."*

### SP-17. CHSH bipartition is chosen, not forced — **Structural**
`src/cascade-series-part2.tex:1108–1115`.

The CHSH construction on $S^7$ partitions $\mathbb{C}^4 = \mathbb{C}^2_A\otimes\mathbb{C}^2_B$ by grouping the first two complex coordinates as $A$ and the last two as $B$. This is one of three distinct 2+2 partitions of $\mathbb{C}^4$ (choosing which two of four coordinates go to $A$). The cascade's iterated slicing doesn't single out a bipartition; it's imported by treating "Alice vs Bob" as two observers in a fixed partition. A different choice would give a different entangled state and potentially a different CHSH output. Theorem 10.3 is correct *given* the partition, but the partition isn't cascade-derived.

### SP-18. Schrödinger-equation derivation absorbs the imaginary part of $(N-i)/N^2$ into "lapse normalisation" — **Minor**
`src/cascade-series-part2.tex:647–654`.

The continuum limit replaces the difference equation by $i\,d\psi/dt = \mathcal{H}\psi$ with $\mathcal{H} = (1-N)/N^2$ (real part), declaring *"the imaginary part contributes a decay/growth that is absorbed into the lapse normalisation"*. No explicit normalisation is constructed. The continuum approximation's roughness at the observer's dimension is acknowledged in the following Remark ($N(4)=1.178$ gives $\sim$12% fractional change per step), but the specific imaginary-part absorption is not.

---

## Part III

### SP-20. Corollary 9.4's "third characterisation" uses a specific scale factor $a(t)=\sqrt{1-t^2}$ without deriving it as the Lorentzian scale factor — **Structural**
`src/cascade-series-part3.tex:423–440`.

The corollary computes $R^{(n)} = (n-1)(n-4)/a^4$ on the FRW metric with $a(t)=\sqrt{1-t^2}$ and concludes $R$ vanishes at $n=4$. But $\sqrt{1-t^2}$ is the *Euclidean* cross-section radius of the cascade's slicing. Its reuse as the *Lorentzian* scale factor of a cosmology gives a bounded universe ($a\to 0$ at $t\to\pm 1$ — a bang/crunch). The paper asserts the identification implicitly; the third characterisation therefore inherits the Wick-rotation identification of Theorem 10.2 (SP-21 closure acknowledges the cascade's Euclidean-to-Lorentzian map is Wick rotation, cascade-motivated by the forced precession). SP-20 itself remains: the specific identification of $\sqrt{1-t^2}$ as Lorentzian scale factor uses Wick rotation of the cascade's Euclidean cross-section, which is the correct operation but not separately derived here.

## Part II=III

### SP-24. Theorem 5.1 "No absolute scale" contradicts Part IVb's use of $M_{\rm Pl,red}$ as dimensional input — **Structural**
`src/cascade-series-part2-equals-3.tex:227–232`, cf Part IVb's absolute masses `src/cascade-series-part4b.tex:973`.

The theorem states *"every physical prediction of the cascade series is a dimensionless ratio"* and *"the cascade geometry contains no intrinsic length, time, mass, or energy scale"*. Part IVb's absolute masses ($m_\tau = 1777$ MeV, $m_W = 80.10$ GeV, $v = 240.8$ GeV, etc.) are physical predictions with dimensions, and they use $M_{\rm Pl,red}$ as a dimensionful input (explicitly: Theorem 4.7 writes $v = M_{\rm Pl,red}\cdot\alpha_s\cdot\exp(-\pi/\alpha(5))$). The theorem's universal claim is too strong — it covers dimensionless ratios but not the absolute masses that Part IVb derives.

### SP-26. Theorem 4.1 "double uniqueness" — Gleason and Lovelock's in-domain uniqueness does not imply cross-domain consistency — **Structural**
`src/cascade-series-part2-equals-3.tex:197–215`.

The *reductio* argument: if QM and GR contradicted at $d=4$, one wouldn't be unique in its domain; but both are unique by classical theorems; contradiction. The step "contradictory predictions $\Rightarrow$ one isn't unique" is the load-bearing inference, and it is not justified. Gleason's uniqueness is *within* a Hilbert-space framework; Lovelock's is *within* a 4D Lorentzian-manifold framework. Two theories each unique within its own domain can have conflicting predictions about a *shared* observable (e.g., a quantum gravitational scattering amplitude) without either losing its in-domain uniqueness. The cascade's single-source architecture is plausibly consistent, but the one-line uniqueness argument does not establish it.

---

## Part IVa

### SP-27. Theorem 2.1 "self-dual crossing" at $d=12$ is a 0.225% numerical near-miss, framed as structural; argument explicitly invokes Kaluza–Klein despite the cascade's refusal elsewhere — **Structural** + **Check-7 tension**
`src/cascade-series-part4a.tex:150–180`.

The theorem: $N(12) = 0.70870$ vs. self-dual $1/\sqrt{2} = 0.70711$ — deviation 0.225%. The paper treats this "crossing" as structurally significant ("the crossing therefore falls exactly at the first layer of the second complex spinor window"). But "falls exactly at" is 0.225% off — a near-miss, not an exact coincidence. More importantly, the mechanism invoked is Kaluza–Klein gauge enhancement: *"In Kaluza–Klein compactification on a circle of radius $R$, the low-energy theory contains a $\mathrm{U}(1)$ gauge field … At the self-dual radius … the $\mathrm{U}(1)$ enhances to $\mathrm{SU}(2)$."* The cascade explicitly refuses Kaluza–Klein reduction (Paper I §3.2; Paper II=III §5–6; Paper III §12). Either this is a legitimate exception (the cascade imports a specific KK identity while refusing the procedure), or it is a Check-7 violation. The paper does not flag the tension.

### SP-30. Theorem 4.3 "Three generations" — proof gives "three visible + one suppressed", not "three only" — **Structural**
`src/cascade-series-part4a.tex:541–566`, cf cover sheet paragraph on Gen~0 at $d=29$.

The theorem statement: *"The number of observable fermion generations is exactly three."* The proof concludes: *"Generation 0 ($d=29$) is 9.3 steps past threshold; its amplitude relative to Generation 1 is suppressed by a factor of $\sim 289$, making it **unobservable**."* "Unobservable" $\ne$ "nonexistent". The cover sheet's own text explicitly identifies $d=29$ with a candidate neutrino-mass layer at $\sim 0.5$ eV, and Part IVb Open Question 4 treats $d=29$ as a *partially realised* Gen 0 sourcing neutrino masses. The strong-form theorem (exactly three) is weaker than the proof supports; the correct statement is "exactly three charged fermion generations, with a suppressed fourth Bott layer at $d=29$".

---

## Part IVb

### SP-34. Theorem 2.9's "independent $C$ from $m_\tau$" check is plausibly circular — **Minor**
`src/cascade-series-part4b.tex:283–285`.

The theorem claims self-consistency of $C = \alpha_s/(2\sqrt{\pi}) = 0.0327$ against "independently, from the $\tau$ mass: $C = 0.0324$. Agreement: 1.0%". The "independent" extraction is not spelt out; reverse-engineering the cascade's τ-mass formula would compute $C$ from the *observed* $m_\tau$ combined with the cascade's $v$, $\Phi(5)$, and $(2\sqrt{\pi})^{-2}$ — which uses the same mass-formula structure the coupling is supposed to validate. Without specification, whether this is a genuine cross-check or a consistency tautology is ambiguous.

### SP-35. Theorem 5.1 Cabibbo — the factor 1/2 in $\exp(-p(13)/2)$ is selected by integer-fit, not derived — **Structural**
`src/cascade-series-part4b.tex:1105–1128`.

Remark 5.2 defends the 1/2 factor: *"The only integers consistent with the series' systematic range are tested: $\exp(-p(13)/1)$ gives 11.11° ($-14.8\%$, wrong sign for the systematic); $\exp(-p(13)/3)$ gives 14.47° ($+11.0\%$, outside the systematic range); only $\exp(-p(13)/2)$ gives 13.26° ($+1.7\%$, within range). The factor 2 is predicted by the bilinear structure of the mixing matrix."* The selection procedure — try $\{1,2,3\}$ and pick the one that fits — is a fit, whatever it is called. The rationalisation "bilinear structure of the mixing matrix" is post-hoc: no derivation is supplied showing that mixing matrices force a specific factor of 2 in this exponent. The paper's claim "not fitted" is misleading.

### SP-36. Proposition 4.8 source selection rule — the four observable *types* were defined after observing the seven source assignments; exhaustiveness is trivial on the training set — **Structural**
`src/cascade-series-part4b.tex:695–715`, verification at `:730–760`.

The three physics flags $(P,L,G)$ and the four-type decision procedure are introduced to reproduce the source assignments of the already-closed seven observables. The "verification" (`:730–748`) is not a blind prediction but a re-derivation of the known assignments. The claim *"every Standard Model precision observable is assigned to exactly one type"* is tested only against the seven observables that defined the types. Applied to new observables (e.g., $\alpha_{\rm em}(M_Z)$, $m_W$ absolute, CKM $\theta_{13}$, $\theta_{23}$ — listed in Remark 4.9 *"falsifiable prediction"*), the rule becomes predictive — but those predictions have not been tested. The paper's *"Does not … derive the three flags $(P,L,G)$ themselves from a purely formal cascade object"* acknowledges that flags are physics meta-data, but does not acknowledge the selection-on-training-set structure of the proposition's proof.

## Summary

| ID | Soft spot | Paper | Severity |
|---|---|---|---|
| SP-7 | Scale=ratio, content=product rule | Part 0 | Structural |
| SP-9 | $\Omega_m^{\rm Bott}$ path on ratio-of-sums | Part 0 Supp | Structural |
| **SP-10** | **$\rho_\Lambda$ Gram-path $[5,216]$ unjustified** | Part I | **High** |
| SP-11 | $\exp$ vs linear Gram form | Part I | Minor |
| SP-12 | $d_V=5$ as observer's host | Part I | Structural |
| SP-13 | "Free dimension" is physical | Part I | Structural |
| SP-14 | Frame-squaring inherits $n=2$ | Part I | Structural |
| SP-16 | $J$ evolves states (static→dynamic) | Part II | Structural |
| SP-17 | CHSH bipartition chosen, not forced | Part II | Structural |
| SP-18 | Schrödinger derivation absorbs imaginary part | Part II | Minor |
| SP-20 | Lorentzian scale factor $\sqrt{1-t^2}$ imported | Part III | Structural |
| SP-24 | "No absolute scale" contradicts $M_{\rm Pl,red}$ use | Part II=III | Structural |
| SP-26 | In-domain uniqueness ≠ cross-domain consistency | Part II=III | Structural |
| SP-27 | $d=12$ self-dual crossing is 0.225% near-miss + KK-tension | Part IVa | Structural + Check-7 |
| SP-30 | "Three generations" is "three visible + suppressed 4th" | Part IVa | Structural |
| SP-34 | "Independent $C$ from $m_\tau$" check is ambiguously circular | Part IVb | Minor |
| SP-35 | Cabibbo 1/2 factor is integer-fit among $\{1,2,3\}$ | Part IVb | Structural |
| SP-36 | Source-selection types defined post-hoc from 7 observables | Part IVb | Structural |

## Notes on scope

- This file documents **only** soft spots the papers do not themselves acknowledge. Items already flagged in each paper's "What this paper does not do" or "Open questions" sections (e.g., the observable-dependent $k_Q$ in the Supplement, the variational max-over-min in Part 0, the second $G_d$ route in Part II=III, the absolute-mass dimensional inputs in Part IVb, the thermal-spectrum derivation, the Page curve, the tensor $r$ magnitude) are deliberately excluded.
- **Load-bearing items still open:** none. SP-23 and SP-31 were the two load-bearing items; both now labelled and tracked as Tier-D research problems in their respective papers' own Open-Questions sections (Part~II=III OQ~1; Part~IVb OQ~1).
- **Quantitatively testable items (Tier C):**
  - SP-17 — compute CHSH on the two alternative bipartitions of $\mathbb{C}^4$ and verify whether $2\sqrt{2}$ is robust.
  - SP-36 — blind-test the source-selection rule against $\alpha_{\rm em}(M_Z)$, $m_W$, $m_e/m_\mu$, CKM $\theta_{13}$, $\theta_{23}$ (Remark 4.9's worked candidates) and verify whether the predictions close within experimental precision.
- **Conceptually tightenable items:** SP-26, SP-35, SP-36. Each could be upgraded from "asserted" to "proved/derived" by supplying an explicit theorem. (SP-25 now tracked as Part II=III Open Question 1, cross-linked via `rem:sp25-status`.)

## Closed items (reference)

18 soft spots closed in hardening commits. Commit hashes for traceability:

| ID | Closure summary | Commit |
|---|---|---|
| SP-1 | Logic→geometry translation: acknowledged in Prelude §10 OQ 3 | `5d522c5` |
| SP-2 | Finite→$\aleph_0$: austerity Principle 2.2 clause (i) | `5843dcf`, `b587aac` |
| SP-3 | Binary-test countability: austerity clause (ii) | `5843dcf`, `b587aac` |
| SP-4 | $\mathbb{R}^*$-dilation: austerity clause (iii) + uniqueness argument | `5843dcf`, `b587aac`, `85476dc` |
| SP-5 | Uniqueness-of-$c_1$ proof: exhaustiveness lemma pre-filters candidates by primitivity; `rem:c1-alternatives` shows $R(d_0)$, $\Omega_{d_0-1}/\Omega_{d_0+1}$, Stirling $2\pi e^{2\sqrt{\pi}}$, and $2\sqrt{\pi}$ are Class-4 derived functions failing primitivity | `73cc8f5` |
| SP-6 | Tower-completeness proof: explicit 4-class mechanism enumeration (extrema, monotone zeros, primitive-value crossings, higher-order invariants); `rem:tower-alternatives` rules out self-dual radius $1/\sqrt{2}$ (no integer solution + non-cascade import), $p^{(n)}$ zeros (no zeros), $\Omega_d$ inflections (derived from $d_0$) | `73cc8f5` |
| SP-8 | Theorem 15.7 relabelled first-order; strengthened to upper bound | `2003692` |
| SP-10 | $\rho_\Lambda$ Gram-path $[5,216]$ principled by austerity | `46087ae` |
| SP-15 | Born rule Step 4 rewritten with explicit Cauchy-additivity derivation on the probability simplex; `rem:sp15-status` acknowledges this as the cascade-native frame-function uniqueness (Gleason-equivalent content, $d\geq 3$ condition made structural from observer $d=4$) | `5b3ca7b` |
| SP-19 | Lemma 9.1 added (five named inputs + fallback) | `c4b99e3` |
| SP-21 | Wick rotation acknowledged; remark `rem:wick-rotation-cascade` | `0501f50` |
| SP-22 | Cascade-lapse vs metric-lapse distinction | `49b4908` |
| SP-23 | Theorem 7.1 proof expanded to 3 steps (unit-ball BD derived, area-is-content derived, scale invariance asserted); `rem:sp23-status` + Open Question (content-area-scale-invariance derivation target); stale Paper~I Thm~4.4 ref corrected to Paper~0 Thm~3.1 | `36596ab` |
| SP-25 | Theorem 6.1 reformulated with three-step factorisation (metric derived, state derived, state-metric map asserted); `rem:sp25-status` + Open Question (state-metric-instantiation) identifying two cascade-native routes (state-dependent foliation, stress-energy back-reaction) | `b27dcb9` |
| SP-28 | Generator-count theorem demoted to remark | `daca41b` |
| SP-29 | SU(3) chirality factual fix + CP-phase paragraph | `a4c42f2` |
| SP-31 | Theorem 2.2 step (b) labelled asserted; `rem:sp31-status` + Open Question (cascade-fermion-action derivation target) | `53ab7b7` |
| SP-32 | Mass-formula $n_D+1$ derived | `3472a9e` |
| SP-33 | Obstruction-rule scope articulated; `rem:obstruction-scope` | `8e4805c` |
| SP-37 | $d=14$ hairy-ball attribution corrected + pairing rationalisations tightened | `4a6be53` |

Plus the austerity-as-derivation framing upgrade (`b587aac`) and open-questions cleanup (`ecdb90f`).


## Hardening priorities

Suggested order for the hardening phase, cheapest first.

Tier A (trivial fixes) and Tier B (articulate implicit rules) are complete. Two tiers remain.

### Tier C — Blind-test predictive rules (weeks, high-value)

Each of these either hardens the rule significantly or exposes a defect early. All are testable by computation.

| ID | Test | What it settles |
|---|---|---|
| SP-10 | Compute the Gram sum on paths [19,217], {3,5,6,7,19,217}, and any other plausible ρ_Λ path. Publish which gives the best closure and why. | Whether the -0.07% headline is robust or cherry-picked |
| SP-36 | Blind-test the source-selection rule against α_em(M_Z), m_W absolute, m_e/m_μ, CKM θ_13, θ_23 per Remark 4.9's "falsifiable prediction". Publish the blind predictions *before* checking them. | Whether the three-flag rule is genuinely predictive or trained on the 7-observable set |
| SP-17 | Compute CHSH on alternative bipartitions of ℂ⁴. Expected: Tsirelson bound gives 2√2 for any maximally-entangled bipartition. If it does, the CHSH result is robust; soft spot downgrades to Minor. | Whether the bipartition choice in Part II §10.3 is cosmetic or structural |

### Tier D — Genuine open problems (months, research-scale)

| ID | What's needed | Why it matters |
|---|---|---|
| SP-26, SP-35 | Each could be upgraded from "asserted" to "proved/derived" by supplying an explicit theorem. Individually modest; collectively a review-resistant rewrite of the load-bearing proofs. | Tightens the "forced derivation" framing |

Note: SP-23 and SP-31 are closed by acknowledgement. SP-23: Remark `rem:sp23-status` in Part II=III factorises Theorem 7.1's proof into three ingredients (unit-ball boundary dominance derived; content-equals-area derived; linear content-area scale invariance asserted), with empirical confirmation at $d=3$ (BTZ) and $d=4$ (Schwarzschild), and Part II=III Open Question 1 (`oq:content-area-scale-invariance`) names the cascade-action derivation target. SP-31: Remark `rem:sp31-status` in Part IVb labels the "exactly one factor of $\sqrt{\pi}$" step as asserted, and Part IVb Open Question 1 (`oq:fermion-cascade-action`) names the cascade-fermion-action derivation target. Resolving the underlying research problems — a cascade action on the lattice whose boundary-layer entropy is $A/d$ independent of total area, and a discrete Dirac operator on the cascade lattice whose Green's function on $S^{2n}$ is $R(d)/\chi$ — remains a genuine Tier D workload, now tracked in the papers' own Open Questions rather than in this audit.

### What hardening does *not* require

- Addressing SP-1 through SP-4 while the Prelude remains exploratory. Promote them to priority only if the Prelude is later reframed as load-bearing.
- Resolving the already-acknowledged gaps (k_Q, 6π in α_em, second G_d route, tensor r, source-selection flags as cascade objects). Those are in the papers' own open-questions lists.
