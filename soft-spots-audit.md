# Unacknowledged Soft Spots — Cascade Derivation Chain Audit

Scope: soft spots in the cascade's derivation chain that are **not** flagged by the papers themselves in their "What this paper does/does not do" or "Open questions" sections. Identified via direct re-reading of the load-bearing theorems and proofs; each citation is `file:line`.

Gaps that the papers *do* acknowledge (Gram-matrix second-order correction, variational max-over-min, "observer at $d=4$ is empirical", the $k_Q$ coefficient, the $6\pi$ screening in $\alpha_{\rm em}$, the second $G_d$ route, etc.) are **excluded** from this file by construction.

Coverage: Prelude, Part 0, Part 0 Supplement, Part I, Part II, Part III, Part II=III, Part IVa, Part IVb.

**Status.** 27 of the original 37 soft spots have been closed in hardening commits (SP-1, SP-2, SP-3, SP-4, SP-5, SP-6, SP-8, SP-10, SP-15, SP-18, SP-19, SP-21, SP-22, SP-23, SP-24, SP-25, SP-26, SP-27, SP-28, SP-29, SP-30, SP-31, SP-32, SP-33, SP-34, SP-35, SP-37). This file now tracks the **10 open items** that remain. Closures are recorded with commit hashes in the "Closed items (reference)" section at the end, for traceability.

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

---

## Part III

### SP-20. Corollary 9.4's "third characterisation" uses a specific scale factor $a(t)=\sqrt{1-t^2}$ without deriving it as the Lorentzian scale factor — **Structural**
`src/cascade-series-part3.tex:423–440`.

The corollary computes $R^{(n)} = (n-1)(n-4)/a^4$ on the FRW metric with $a(t)=\sqrt{1-t^2}$ and concludes $R$ vanishes at $n=4$. But $\sqrt{1-t^2}$ is the *Euclidean* cross-section radius of the cascade's slicing. Its reuse as the *Lorentzian* scale factor of a cosmology gives a bounded universe ($a\to 0$ at $t\to\pm 1$ — a bang/crunch). The paper asserts the identification implicitly; the third characterisation therefore inherits the Wick-rotation identification of Theorem 10.2 (SP-21 closure acknowledges the cascade's Euclidean-to-Lorentzian map is Wick rotation, cascade-motivated by the forced precession). SP-20 itself remains: the specific identification of $\sqrt{1-t^2}$ as Lorentzian scale factor uses Wick rotation of the cascade's Euclidean cross-section, which is the correct operation but not separately derived here.

## Part II=III

---

## Part IVa

---

## Part IVb

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
| SP-20 | Lorentzian scale factor $\sqrt{1-t^2}$ imported | Part III | Structural |
| SP-36 | Source-selection types defined post-hoc from 7 observables | Part IVb | Structural |

## Notes on scope

- This file documents **only** soft spots the papers do not themselves acknowledge. Items already flagged in each paper's "What this paper does not do" or "Open questions" sections (e.g., the observable-dependent $k_Q$ in the Supplement, the variational max-over-min in Part 0, the second $G_d$ route in Part II=III, the absolute-mass dimensional inputs in Part IVb, the thermal-spectrum derivation, the Page curve, the tensor $r$ magnitude) are deliberately excluded.
- **Load-bearing items still open:** none. SP-23 and SP-31 were the two load-bearing items; both now labelled and tracked as Tier-D research problems in their respective papers' own Open-Questions sections (Part~II=III OQ~1; Part~IVb OQ~1).
- **Quantitatively testable items (Tier C):**
  - SP-17 — compute CHSH on the two alternative bipartitions of $\mathbb{C}^4$ and verify whether $2\sqrt{2}$ is robust.
  - SP-36 — blind-test the source-selection rule against $\alpha_{\rm em}(M_Z)$, $m_W$, $m_e/m_\mu$, CKM $\theta_{13}$, $\theta_{23}$ (Remark 4.9's worked candidates) and verify whether the predictions close within experimental precision.
- **Conceptually tightenable items:** SP-36. (SP-25 now tracked as Part II=III Open Question 1; SP-35 now tracked as Part IVb Open Question 1, the geometric-mean mixing rule.)

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
| SP-18 | New Lemma `lem:lapse-norm` explicitly constructs the cumulative-lapse normalisation $\tilde\psi_d = \psi_d\prod_{j>d}^D N(j)^{-1}$, showing $\tilde\psi_{d-1} = i\tilde\psi_d$ (pure unit-modulus phase, unitary); Corollary 7.5 proof rewritten to pass through $\tilde\psi$; `rem:sp18-status` factorises the derivation into three statuses (exact discrete propagator derived; unitary reduction derived via Lemma; continuum form $(1-N)/N^2$ an effective description valid for $d\gg 1$) | `93434a0` |
| SP-19 | Lemma 9.1 added (five named inputs + fallback) | `c4b99e3` |
| SP-21 | Wick rotation acknowledged; remark `rem:wick-rotation-cascade` | `0501f50` |
| SP-22 | Cascade-lapse vs metric-lapse distinction | `49b4908` |
| SP-23 | Theorem 7.1 proof expanded to 3 steps (unit-ball BD derived, area-is-content derived, scale invariance asserted); `rem:sp23-status` + Open Question (content-area-scale-invariance derivation target); stale Paper~I Thm~4.4 ref corrected to Paper~0 Thm~3.1 | `36596ab` |
| SP-24 | Reframed as not-a-defect via `rem:sp24-status`: distinguishes cascade-intrinsic (dimensionless, zero empirical input) from empirically-anchored (dimensional, two anchors: $M_{\rm Pl,red}$ and $m_Z$) scales; this is standard physical-theory practice (GR with $G$, QED with $\alpha$), with the cascade reducing the SM's $\sim 22$ dimensional parameters to $2$ | *(this commit)* |
| SP-27 | Theorem 2.1 restated as "near-miss observation" with explicit 0.225% deviation; KK-mechanism paragraph rewritten to separate reference value ($1/\sqrt{2}$ as a name) from KK mechanism (not imported); `rem:sp27-status` with three statuses (derived Gamma value, observed near-miss, not-imported KK mechanism) and Check-7 compliance statement pointing to Adams' theorem as the actual derivation | `79c9372` |
| SP-25 | Theorem 6.1 reformulated with three-step factorisation (metric derived, state derived, state-metric map asserted); `rem:sp25-status` + Open Question (state-metric-instantiation) identifying two cascade-native routes (state-dependent foliation, stress-energy back-reaction) | `b27dcb9` |
| SP-26 | Theorem 4.1 proof rewritten to use single-source argument instead of invalid reductio on in-domain uniqueness; theorem renamed "Gleason + Lovelock + single source = consistency"; `rem:sp26-status` explicitly concedes the QED/EFT-QG counterexample and identifies `thm:single` as the load-bearing input | `1001883` |
| SP-28 | Generator-count theorem demoted to remark | `daca41b` |
| SP-29 | SU(3) chirality factual fix + CP-phase paragraph | `a4c42f2` |
| SP-30 | Theorem 4.3 statement tightened to "exactly three observable charged-fermion generations" with explicit acknowledgment of the suppressed fourth Bott layer at $d=29$; proof reworded to "kills the fourth \emph{charged-fermion} generation" with cross-reference to Part IVb neutrino-mass derivation; `rem:sp30-status` documents the three-status factorisation (three charged gens derived, $d=29$ as cascade primitive derived, neutrino role derived in Part IVb); abstract and summary overreach phrases softened | `2b52a6e` |
| SP-31 | Theorem 2.2 step (b) labelled asserted; `rem:sp31-status` + Open Question (cascade-fermion-action derivation target) | `53ab7b7` |
| SP-32 | Mass-formula $n_D+1$ derived | `3472a9e` |
| SP-33 | Obstruction-rule scope articulated; `rem:obstruction-scope` | `8e4805c` |
| SP-34 | Theorem 2.9 proof extended to spell out Route 2 (inverting the $\tau$-mass formula for $C$) with explicit formula $C_\tau = 2\sqrt{2\pi}\,m_\tau\,e^{\Phi(5)}/v$; new `rem:sp34-status` documents Routes 1 and 2 share no dynamical input (only the Part-0 primitive $2\sqrt{\pi}$), with $v$ and $\Phi(5)$ both cascade-derived quantities without fermion-mass input | `b7ba37b` |
| SP-35 | Cabibbo $1/2$ remark rewritten as three-step factorisation (raw angle derived, descent $\exp(-p(13))$ derived, geometric-mean off-diagonal asserted); `rem:sp35-status` honestly labels the Fritzsch-like ansatz; new Open Question (`oq:mixing-geometric-mean`) names the cascade-action derivation target; `thm:cabibbo-amplitude` and `rem:ckm-hierarchy` labels added | `60392e2` |
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
| — | The conceptually-tightenable cluster is now empty. SP-36 remains in the blind-test Tier C row. | — |

Note: SP-23 and SP-31 are closed by acknowledgement. SP-23: Remark `rem:sp23-status` in Part II=III factorises Theorem 7.1's proof into three ingredients (unit-ball boundary dominance derived; content-equals-area derived; linear content-area scale invariance asserted), with empirical confirmation at $d=3$ (BTZ) and $d=4$ (Schwarzschild), and Part II=III Open Question 1 (`oq:content-area-scale-invariance`) names the cascade-action derivation target. SP-31: Remark `rem:sp31-status` in Part IVb labels the "exactly one factor of $\sqrt{\pi}$" step as asserted, and Part IVb Open Question 1 (`oq:fermion-cascade-action`) names the cascade-fermion-action derivation target. Resolving the underlying research problems — a cascade action on the lattice whose boundary-layer entropy is $A/d$ independent of total area, and a discrete Dirac operator on the cascade lattice whose Green's function on $S^{2n}$ is $R(d)/\chi$ — remains a genuine Tier D workload, now tracked in the papers' own Open Questions rather than in this audit.

### What hardening does *not* require

- Addressing SP-1 through SP-4 while the Prelude remains exploratory. Promote them to priority only if the Prelude is later reframed as load-bearing.
- Resolving the already-acknowledged gaps (k_Q, 6π in α_em, second G_d route, tensor r, source-selection flags as cascade objects). Those are in the papers' own open-questions lists.
