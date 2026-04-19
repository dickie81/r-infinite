# Unacknowledged Soft Spots — Cascade Derivation Chain Audit

Scope: soft spots in the cascade's derivation chain that are **not** flagged by the papers themselves in their "What this paper does/does not do" or "Open questions" sections. Identified via direct re-reading of the load-bearing theorems and proofs; each citation is `file:line`.

Gaps that the papers *do* acknowledge (Gram-matrix second-order correction, variational max-over-min, "observer at $d=4$ is empirical", the $k_Q$ coefficient, the $6\pi$ screening in $\alpha_{\rm em}$, the second $G_d$ route, etc.) are **excluded** from this file by construction.

Coverage: Prelude, Part 0, Part 0 Supplement, Part I, Part II, Part III, Part II=III, Part IVa, Part IVb.

**Important context on the Prelude.** The Prelude is an *exploration* of what the true minimum starting point of the cascade might be. It is not the load-bearing first link in the derivation chain. The series' hypothesis — that $B^\infty$ descended to 4D is indistinguishable from our universe — is stated independently in the cover sheet and does not depend on the Prelude's $0\ne 1 \to B^\infty$ chain. Prelude soft spots (SP-1 through SP-4) are accordingly classified **Exploratory** rather than Foundational: they are looseness in an exploratory paper, not gaps in the cascade's load-bearing chain. They become Foundational only if the Prelude is promoted from exploration to load-bearing first link.

## Severity scale

- **Exploratory** — occurs in a paper whose function is to probe a minimum starting point, not to prove one. Worth tightening if the paper is later promoted to load-bearing; not blocking downstream hardening.
- **Foundational** — affects whether the cascade starts from "one axiom" as advertised.
- **High** — directly affects a headline numerical claim.
- **Structural** — affects a derivation step whose conclusion is re-used downstream.
- **Minor** — affects presentation or first-order approximation; numerical impact below stated uncertainties.

---

## Prelude

### SP-1. Logic-to-geometry translation (Theorem 3.1) — **Exploratory** — ✅ **FIXED (acknowledged as open in Prelude §10 OQ 3)**
`src/cascade-series-prelude.tex:110–115`, discussion at `:102–108`.

The theorem's premise is "unit vectors representing two fully distinguishable states — states sharing no common component under any linear operation on $V$". That premise is already the geometric form of the conclusion. The theorem proves geometric no-common-component $\Rightarrow$ zero inner product rigorously; it does not prove that logical $0\ne 1$ $\Rightarrow$ geometric no-common-component. The paper denies this is an assumption ("not an additional assumption; it is a translation of the same fact into geometric language").

### SP-2. Finite $\to \aleph_0$ jump is parameter-economic, not mathematical (Theorem 4.1, step 2) — **Exploratory** — ✅ **FIXED (austerity axiom declared)**
`src/cascade-series-prelude.tex:157–168`.

*"Refusing it would be [an additional assumption]"* — philosophical, not proved. $\aleph_0$ is itself a specific cardinal; the step privileges it over all finite cardinals by appealing to the Prelude §1 principle that a theory of everything cannot have inputs. That principle is assumed, not derived from $0\ne 1$.

### SP-3. "Countable rather than uncountable" presumes binary-test distinctions (Theorem 4.1, step 3) — **Exploratory** — ✅ **FIXED (austerity axiom declared)**
`src/cascade-series-prelude.tex:170–179`.

*"Each distinction is a single bit: a binary test 'is the state $e_i$ or not?'"* — introduced here for the first time. Uncountable distinction is excluded "by the same parameter-economy principle that excludes finite $n$", chaining two unacknowledged assumptions.

### SP-4. $\mathbb{R}^*$-dilation invariance introduced as a new symmetry (§5) — **Exploratory** — ✅ **FIXED (austerity principle + ℝ* uniqueness argument)**
`src/cascade-series-prelude.tex:186–203`.

The absence of an external ruler does not force invariance under $\mathbb{R}^*$-dilation specifically (vs conformal group, vs discrete scale invariance, vs $\mathbb{C}^*$). The paper asserts $\mathbb{P}\mathcal{H}$ is "the unique quotient" without proving uniqueness over alternative symmetry groups.

---

## Part 0

### SP-5. Theorem 6.2 — "four information classes" enumeration not shown to be exhaustive — **Structural**
`src/cascade-series-part0.tex:240–281`.

The uniqueness-of-$c_1$ proof checks four candidate classes. Other natural scalars derivable from the zero — $R(d_0)$, $\Omega_{d_0-1}/\Omega_{d_0+1}$, the Stirling parameter $2\pi e^{2\sqrt{\pi}}$ that appears in Theorem 9.1, or $2\sqrt{\pi}$ (itself a downstream primitive in Part IVb) — are not considered.

### SP-6. Theorem 7.1 ("Tower completeness") asserts exhaustiveness but only rules out $d=6$ — **Structural**
`src/cascade-series-part0.tex:417–435`.

The claim "no other cascade quantity selects a dimension" is stated without enumerating candidates. Inflection points of $\Omega_d$, zeros of higher derivatives of $p$, and **the self-dual radius $R(d)=1/\sqrt{2}$ which Part IVa Theorem 2.1 identifies at $d=12$ as structurally significant** are not considered. Part IVa's downstream use of a self-dual crossing shows the Gamma-function framework already contains a candidate fifth dimension that Part 0 misses.

### SP-7. Theorem 8.4 — "scale = ratio, content = product" is rationalised, not forced — **Structural**
`src/cascade-series-part0.tex:574–631`.

Two references can combine as a product (geometric mean); two independent outputs of a multiplicative recurrence are just scalars combinable arbitrarily. Structural stability selects *which* dimensions are scale vs content; it does not select the combining operation for each class. Remark 8.5 denies this is a definition.

---

## Part 0 Supplement

### SP-8. Theorem 15.7 stated as equality, is first-order perturbative — **Minor** — ✅ **FIXED**
`src/cascade-series-part0.0.tex:153–166`; numerical residual `:168` (0.17%).

The formula $\lambda_1 = n - \langle u|D|u\rangle$ is first-order around the rank-1 matrix $J$; the theorem statement uses `=`. The verification residual (0.17%) shows the formula is approximate. The first-order label is inside the proof but not the theorem statement.

### SP-9. $\Omega_m^{\rm Bott}$ path applied to a ratio-of-sums observable — **Structural**
`src/cascade-series-part0.0.tex:231–239`, cf Part V Theorem 5.10.

Theorem 15.11 proves the correction *"for a multiplicative propagator"* traversing a contiguous path. $\Omega_m^{\rm Bott}$ is a ratio of sums over non-trivial-phase layers, not a multiplicative propagator. The application to $\Omega_m^{\rm Bott}$ is an unstated extension.

---

## Part I

### SP-10. Gram-correction path $[5,216]$ imported without derivation — **High** (load-bearing)
`src/cascade-series-part1.tex:434–440`.

The equation at line 437 uses $\sum_{d=5}^{216}(1-C^2_{d,d+1})$ (numerical value $0.02108$ imported from the Supplement's $\Omega_m^{\rm Bott}$ row). $\rho_\Lambda$'s formula $(18/\pi^3)\Omega_{19}\Omega_{217}$ traverses the dimensions $\{3, 5, 7, 19, 217\}$ via the unified-descent theorem, not the contiguous layers $[5, 216]$. Alternative paths $[19, 217]$ or the unified-descent skeleton would give different residuals. **The headline $-0.07\%$ closure depends on this unjustified path choice.**

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

### SP-15. Theorem 5.2 Born rule — "Step 4" is Gleason-lite under the banner of concentration of measure — **Structural**
`src/cascade-series-part2.tex:400–416`, cf `:428–436`.

Step 4 of the Born-rule proof ends with: *"concentration of measure forces this partition to be the unique assignment consistent with additivity across orthogonal axes. For $k$ orthogonal axes … by Parseval's identity on $S^{d-1}$. No other function of $\theta$ satisfies this constraint for all $k$ and all orientations simultaneously."* This is Gleason's own uniqueness argument (frame functions on a Hilbert space) recast in geometric language. §5.3 *"What the cascade adds to Gleason"* then treats Gleason as a downstream check — but Step 4 already used Gleason-shaped reasoning to pin $\cos^2\theta$. Pythagoras and Parseval give additivity; they do not, on their own, select $\cos^2$ over other analytic functions satisfying the same constraint for all $k$ — that selection is Gleason's content. Not flagged as such.

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

### SP-19. Lemma 9.2 identifies the cascade's Hilbert space with "the spinor representation space of Spin(1,d−1)" without justification — **Structural** (load-bearing on the $d=4$ derivation) — ✅ **FIXED (upgraded to Lemma with named inputs; Option B)**
`src/cascade-series-part3.tex:372–385`.

The lemma opens: *"For the cascade's state space (carrying $J$ with $J^2=-\mathrm{Id}$) **to serve as** the spinor representation space of $\mathrm{Spin}(1,d-1)$…"*. The "to serve as" is the whole game. Part II's Hilbert space is $S^{d-1}$ geometry from orthogonality; it does not come with a Spin-group action. Imposing one requires (a) choosing $d$, (b) identifying the Hilbert space with an irreducible spinor representation. Condition (C1) in Theorem 9.3's $d=4$ intersection then rules out $d$-values by Clifford classification. **Without this identification step, (C1) isn't even a well-posed condition on $d$.** The paper treats the identification as implicit.

### SP-20. Corollary 9.4's "third characterisation" uses a specific scale factor $a(t)=\sqrt{1-t^2}$ without deriving it as the Lorentzian scale factor — **Structural**
`src/cascade-series-part3.tex:423–440`.

The corollary computes $R^{(n)} = (n-1)(n-4)/a^4$ on the FRW metric with $a(t)=\sqrt{1-t^2}$ and concludes $R$ vanishes at $n=4$. But $\sqrt{1-t^2}$ is the *Euclidean* cross-section radius of the cascade's slicing. Its reuse as the *Lorentzian* scale factor of a cosmology gives a bounded universe ($a\to 0$ at $t\to\pm 1$ — a bang/crunch). The paper asserts the identification implicitly; the third characterisation therefore inherits the Wick-rotation-in-disguise of Theorem 10.2 (see SP-21).

### SP-21. Theorem 10.2 proof conflates "Lorentzian signature" with "oscillatory unitary evolution" — **Structural**
`src/cascade-series-part3.tex:488–499`; remark at `:501–507`.

The proof's opening: *"Lorentzian signature means $g_{tt}<0$. This is equivalent, **by definition**, to time evolution being generated by a self-adjoint Hamiltonian with real eigenvalues, giving unitary oscillatory evolution $e^{-iHt}$."* This equivalence is not a definition — metric signature is a property of the metric tensor, independent of whether a Hamiltonian exists. In standard QFT they are *correlated* through Wick rotation, but not definitionally equivalent. The immediately-following remark then says the connection is "not through analytic continuation of the metric" — but the sign flip from the Euclidean $+dt^2$ to the Lorentzian $-dt^2$ is exactly the analytic continuation operation, by another name. Flagged internally as "not Wick rotation", but the derivation *is* Wick rotation installed by fiat.

### SP-22. §4.4 asserts unit lapse $g_{tt}=-1$ while §4.2 gives cascade lapse $N(4)=3\pi/8$ — **Structural**
`src/cascade-series-part3.tex:210–216`, cf `:196–200`.

The "4D projected metric" is written as $ds^2_{\rm 4D} = -dt^2 + a(t)^2\,d\sigma_3^2$ — unit lapse. The lapse function of the cascade is introduced two subsections earlier as $N(d) = \sqrt{\pi}\cdot R(d)$, with $N(4) = 3\pi/8 \approx 1.178$. The reconciliation — whether the 4D effective metric uses unit lapse or the cascade lapse — is not addressed inside Part III. Part V Theorem 6.1 later retracts a "lapse-corrected Friedmann" derivation, which suggests the issue was recognised downstream, but Part III itself does not flag the tension.

---

## Part II=III

### SP-23. Theorem 7.1 conflates "boundary dominance of the unit ball" with "black-hole horizon entropy-area law" — **Structural**
`src/cascade-series-part2-equals-3.tex:286–299`.

The one-line proof: *"Boundary dominance: $\Omega_{d-1}/V_d = d$. Therefore $V_d = \Omega_{d-1}/d$. A horizon of area $A$ is a boundary. Its interior content is $V = A/d$."* The identity is a *unit-ball* fact. For a ball of radius $r$, $V/A = r/d$, not $1/d$ — the factor $1/d$ only recovers for $r=1$. Applying it to a physical black hole horizon (Schwarzschild: $r=2M$) silently sets $r=1$ in Planck units and equates "cascade content behind horizon" with the unit-ball interior volume. The match to Bekenstein–Hawking $S=A/4$ works *because* entropy is dimensionless in Planck-area units, but the identification "content = $V$ of unit ball at horizon dimension" is a modelling choice, not forced by boundary dominance alone.

### SP-24. Theorem 5.1 "No absolute scale" contradicts Part IVb's use of $M_{\rm Pl,red}$ as dimensional input — **Structural**
`src/cascade-series-part2-equals-3.tex:227–232`, cf Part IVb's absolute masses `src/cascade-series-part4b.tex:973`.

The theorem states *"every physical prediction of the cascade series is a dimensionless ratio"* and *"the cascade geometry contains no intrinsic length, time, mass, or energy scale"*. Part IVb's absolute masses ($m_\tau = 1777$ MeV, $m_W = 80.10$ GeV, $v = 240.8$ GeV, etc.) are physical predictions with dimensions, and they use $M_{\rm Pl,red}$ as a dimensionful input (explicitly: Theorem 4.7 writes $v = M_{\rm Pl,red}\cdot\alpha_s\cdot\exp(-\pi/\alpha(5))$). The theorem's universal claim is too strong — it covers dimensionless ratios but not the absolute masses that Part IVb derives.

### SP-25. Theorem 6.1 "different states produce different metrics" lacks a concrete instantiation — **Structural**
`src/cascade-series-part2-equals-3.tex:253–268`.

Paper III's cascade metric $-dt^2 + a(t)^2\,d\sigma_3^2$ is a *single* FRW background, the same for all cascade states on $S^{d-1}$. Theorem 6.1 asserts "different states produce different metrics; superpositions of states produce superpositions of metrics" — but no construction shows two distinct states $|\Psi_1\rangle,|\Psi_2\rangle \in S^{d-1}$ giving rise to two distinct 4D metrics. (The paper's "Does not" list at `:585–599` flags that the explicit Hilbert space of metric superpositions is not constructed, which is adjacent; it does not flag that the theorem's key premise — states determining metrics — is itself asserted, not demonstrated.)

### SP-26. Theorem 4.1 "double uniqueness" — Gleason and Lovelock's in-domain uniqueness does not imply cross-domain consistency — **Structural**
`src/cascade-series-part2-equals-3.tex:197–215`.

The *reductio* argument: if QM and GR contradicted at $d=4$, one wouldn't be unique in its domain; but both are unique by classical theorems; contradiction. The step "contradictory predictions $\Rightarrow$ one isn't unique" is the load-bearing inference, and it is not justified. Gleason's uniqueness is *within* a Hilbert-space framework; Lovelock's is *within* a 4D Lorentzian-manifold framework. Two theories each unique within its own domain can have conflicting predictions about a *shared* observable (e.g., a quantum gravitational scattering amplitude) without either losing its in-domain uniqueness. The cascade's single-source architecture is plausibly consistent, but the one-line uniqueness argument does not establish it.

---

## Part IVa

### SP-27. Theorem 2.1 "self-dual crossing" at $d=12$ is a 0.225% numerical near-miss, framed as structural; argument explicitly invokes Kaluza–Klein despite the cascade's refusal elsewhere — **Structural** + **Check-7 tension**
`src/cascade-series-part4a.tex:150–180`.

The theorem: $N(12) = 0.70870$ vs. self-dual $1/\sqrt{2} = 0.70711$ — deviation 0.225%. The paper treats this "crossing" as structurally significant ("the crossing therefore falls exactly at the first layer of the second complex spinor window"). But "falls exactly at" is 0.225% off — a near-miss, not an exact coincidence. More importantly, the mechanism invoked is Kaluza–Klein gauge enhancement: *"In Kaluza–Klein compactification on a circle of radius $R$, the low-energy theory contains a $\mathrm{U}(1)$ gauge field … At the self-dual radius … the $\mathrm{U}(1)$ enhances to $\mathrm{SU}(2)$."* The cascade explicitly refuses Kaluza–Klein reduction (Paper I §3.2; Paper II=III §5–6; Paper III §12). Either this is a legitimate exception (the cascade imports a specific KK identity while refusing the procedure), or it is a Check-7 violation. The paper does not flag the tension.

### SP-28. Theorem 2.7 "generator count $12 = 8+3+1$" and "rank $= 4$" are numerical matches presented as structural — **Minor** — ✅ **FIXED**
`src/cascade-series-part4a.tex:214–223`.

The layers strictly between $d_0=7$ and $d_1=19$ number $19-7-1=11$; the paper says "exactly 12" using inclusive/exclusive of different endpoints. The decomposition $12 = 8+3+1 = \dim(\mathrm{SU}(3))+\dim(\mathrm{SU}(2))+\dim(\mathrm{U}(1))$ is arithmetic, not structural: the 8+3+1 split comes from Adams' theorem applied to layers 12, 13, 14 (proved separately), not from the 12-layer count. Similarly, "total rank $=2+1+1=4=$ observer's spacetime dimension" is a numerical coincidence — the cascade's rank-theory doesn't independently derive that the gauge-window's Lie-algebra rank should equal $d=4$. Both are retrospective observations, not load-bearing derivations, but they are presented in the main argument as structural confirmations.

### SP-29. "SU(3) couples chirally" is factually incorrect — **Minor** (factual) — ✅ **FIXED**
`src/cascade-series-part4a.tex:202–205`. Fix applied in commit: see Fixes Applied section below.

The paper's rationalisation of the Weyl–Dirac–Weyl assignment read: *"$\mathrm{SU}(3)$ and $\mathrm{U}(1)$ couple chirally to fermions, while $\mathrm{SU}(2)$ couples only to left-handed fermions (vector-like pre-breaking, chiral after breaking)."* QCD ($\mathrm{SU}(3)$ colour) is vectorial in the Standard Model — left- and right-handed quarks carry equal colour charge; $\mathrm{SU}(3)$ does not couple chirally. The assignment of Weyl-phase layers ($d=12$, $d=14$) to $\mathrm{SU}(3)$ and $\mathrm{U}(1)$ via "chiral coupling" was therefore based on a mis-statement of Standard Model physics. The numerical identification $d=12 \to \mathrm{SU}(3)$, $d=14 \to \mathrm{U}(1)$ remains defensible via Adams (SP-27 aside); the chirality-matching argument used to motivate the assignment has been replaced.

### SP-30. Theorem 4.3 "Three generations" — proof gives "three visible + one suppressed", not "three only" — **Structural**
`src/cascade-series-part4a.tex:541–566`, cf cover sheet paragraph on Gen~0 at $d=29$.

The theorem statement: *"The number of observable fermion generations is exactly three."* The proof concludes: *"Generation 0 ($d=29$) is 9.3 steps past threshold; its amplitude relative to Generation 1 is suppressed by a factor of $\sim 289$, making it **unobservable**."* "Unobservable" $\ne$ "nonexistent". The cover sheet's own text explicitly identifies $d=29$ with a candidate neutrino-mass layer at $\sim 0.5$ eV, and Part IVb Open Question 4 treats $d=29$ as a *partially realised* Gen 0 sourcing neutrino masses. The strong-form theorem (exactly three) is weaker than the proof supports; the correct statement is "exactly three charged fermion generations, with a suppressed fourth Bott layer at $d=29$".

---

## Part IVb

### SP-31. Theorem 2.2 proof (b) — "obstruction consumes $\sqrt{\pi}$" is physics-intuition dressed as mathematical derivation — **Structural, load-bearing on every fermion mass**
`src/cascade-series-part4b.tex:105–136`.

The proof's step (b) argues: *"A fermion (spinor) couples to the tangent frame through the spin connection. The global obstruction of the tangent frame means the fermion cannot access the full angular measure of the quarter-turn. The quarter-turn constant $\sqrt{\pi}$ is consumed by the obstruction."* This is qualitative physics reasoning, not a computation that derives $N_f(d) = R(d)/\chi$ from an action or measure. The paper supplies two independent constants ($\chi=2$ from chirality, $\sqrt{\pi}$ from the slicing) and combines them via "the obstruction consumes exactly one factor of $\sqrt{\pi}$" — but the "exactly one" is asserted, not computed. The parallel derivation via Corollary 2.3 (the cascade-primitive identity $2\sqrt{\pi} = N(0)\cdot\Gamma(\tfrac{1}{2})$) identifies the numerical factor post-hoc but does not derive the obstruction mechanism.

### SP-32. Theorem 2.7 mass formula uses $(2\sqrt{\pi})^{-(n_D+1)}$; the "+1" observer toll is asserted, not derived — **Structural**
`src/cascade-series-part4b.tex:287–299`.

Remark 2.10 *(observer's obstruction)*: *"The observer pays this toll to see the gauge window, then pays it again at each Dirac layer between the gauge window and the generation layer. The total obstruction count in the mass formula is $n_D + 1$."* The "+1" representing the observer's universal-coupling toll is introduced separately from the $n_D$ count (Dirac layers on the fermion's path). The two contributions are stitched together without a unified derivation from a single action or propagator computation — the bookkeeping is structural (obstruction counting) but the specific "$n_D + 1$" exponent is assembled from two independently-argued components.

### SP-33. α_s's descent formula does not pick up obstruction factors from $d=5$, though the descent path crosses it — **Structural** — ✅ **FIXED (obstruction-rule scope articulated + consistent across all three gauge couplings)**
`src/cascade-series-part4b.tex:423–427`, cf obstruction rule `src/cascade-series-part4b.tex:838–852`.

$\alpha_s(M_Z) = \alpha(12)\cdot\exp(\Phi(12\to 4))$ has the cascade descent from $d=12$ down to $d=4$, which passes through $d=5$ (a Dirac layer). The Weinberg-angle derivation (Theorem 4.9) asserts *"a field passing through a Dirac layer encounters the topological obstruction"*, giving $\mathrm{U}(1)$'s coupling a $1/\sqrt{\pi}$ factor for crossing $d=13$. By the same rule, $\mathrm{SU}(3)$'s coupling should pick up $1/\sqrt{\pi}$ for crossing $d=5$ — but the α_s formula does not include this factor (including it would give $\alpha_s \approx 0.065$, far off from 0.118). The apparent resolution is a rule like "obstruction applies only when crossing *broken-symmetry* Dirac layers, not *generation* Dirac layers"; this distinction is not stated anywhere in Part IVb.

### SP-34. Theorem 2.9's "independent $C$ from $m_\tau$" check is plausibly circular — **Minor**
`src/cascade-series-part4b.tex:283–285`.

The theorem claims self-consistency of $C = \alpha_s/(2\sqrt{\pi}) = 0.0327$ against "independently, from the $\tau$ mass: $C = 0.0324$. Agreement: 1.0%". The "independent" extraction is not spelt out; reverse-engineering the cascade's τ-mass formula would compute $C$ from the *observed* $m_\tau$ combined with the cascade's $v$, $\Phi(5)$, and $(2\sqrt{\pi})^{-2}$ — which uses the same mass-formula structure the coupling is supposed to validate. Without specification, whether this is a genuine cross-check or a consistency tautology is ambiguous.

### SP-35. Theorem 5.1 Cabibbo — the factor 1/2 in $\exp(-p(13)/2)$ is selected by integer-fit, not derived — **Structural**
`src/cascade-series-part4b.tex:1105–1128`.

Remark 5.2 defends the 1/2 factor: *"The only integers consistent with the series' systematic range are tested: $\exp(-p(13)/1)$ gives 11.11° ($-14.8\%$, wrong sign for the systematic); $\exp(-p(13)/3)$ gives 14.47° ($+11.0\%$, outside the systematic range); only $\exp(-p(13)/2)$ gives 13.26° ($+1.7\%$, within range). The factor 2 is predicted by the bilinear structure of the mixing matrix."* The selection procedure — try $\{1,2,3\}$ and pick the one that fits — is a fit, whatever it is called. The rationalisation "bilinear structure of the mixing matrix" is post-hoc: no derivation is supplied showing that mixing matrices force a specific factor of 2 in this exponent. The paper's claim "not fitted" is misleading.

### SP-36. Proposition 4.8 source selection rule — the four observable *types* were defined after observing the seven source assignments; exhaustiveness is trivial on the training set — **Structural**
`src/cascade-series-part4b.tex:695–715`, verification at `:730–760`.

The three physics flags $(P,L,G)$ and the four-type decision procedure are introduced to reproduce the source assignments of the already-closed seven observables. The "verification" (`:730–748`) is not a blind prediction but a re-derivation of the known assignments. The claim *"every Standard Model precision observable is assigned to exactly one type"* is tested only against the seven observables that defined the types. Applied to new observables (e.g., $\alpha_{\rm em}(M_Z)$, $m_W$ absolute, CKM $\theta_{13}$, $\theta_{23}$ — listed in Remark 4.9 *"falsifiable prediction"*), the rule becomes predictive — but those predictions have not been tested. The paper's *"Does not … derive the three flags $(P,L,G)$ themselves from a purely formal cascade object"* acknowledges that flags are physics meta-data, but does not acknowledge the selection-on-training-set structure of the proposition's proof.

### SP-37. "Why the specific pairings type↦d$^*$" rationalisations include a factually wrong statement — **Minor** (factual) — ✅ **FIXED**
`src/cascade-series-part4b.tex:766–774`.

The rationalisation for Gauge→$d_{\rm gw}=14$ reads: *"$d=14$ … the $\mathrm{U}(1)$ hypercharge layer, the highest of the window and **the only one carrying a hairy-ball obstruction** that produces the universal $2\sqrt\pi$ factor."* But $d=14$ is a Weyl layer on the *odd*-dimensional sphere $S^{13}$ — no hairy-ball obstruction. The hairy-ball obstruction lives at $d=13$ (Dirac, on $S^{12}$). What the rationalisation presumably intends is that $d=14$'s coupling picks up the $2\sqrt{\pi}$ factor *by crossing* $d=13$, not by carrying an obstruction itself. As stated, the claim misidentifies which layer carries the obstruction.

---

## Summary

| ID | Soft spot | Paper | Severity |
|---|---|---|---|
| ~~SP-1~~ | ~~Logic→geometry translation~~ | Prelude | ✅ Fixed (acknowledged in Prelude §10 OQ 3) |
| ~~SP-2~~ | ~~Finite→$\aleph_0$ parameter economy~~ | Prelude | ✅ Fixed (austerity clause (i)) |
| ~~SP-3~~ | ~~Binary-test countability~~ | Prelude | ✅ Fixed (austerity clause (ii)) |
| ~~SP-4~~ | ~~$\mathbb{R}^*$-dilation as new symmetry~~ | Prelude | ✅ Fixed (austerity clause (iii)) |
| SP-5 | $c_1$ uniqueness four-class exhaustiveness | Part 0 | Structural |
| SP-6 | Tower completeness misses self-dual radius | Part 0 | Structural |
| SP-7 | Scale=ratio, content=product rule | Part 0 | Structural |
| ~~SP-8~~ | ~~First-order $\epsilon$ stated as equality~~ | Part 0 Supp | ✅ Fixed |
| SP-9 | $\Omega_m^{\rm Bott}$ path on ratio-of-sums | Part 0 Supp | Structural |
| **SP-10** | **$\rho_\Lambda$ Gram-path $[5,216]$ unjustified** | Part I | **High** |
| SP-11 | $\exp$ vs linear Gram form | Part I | Minor |
| SP-12 | $d_V=5$ as observer's host | Part I | Structural |
| SP-13 | "Free dimension" is physical | Part I | Structural |
| SP-14 | Frame-squaring inherits $n=2$ | Part I | Structural |
| SP-15 | Born rule Step 4 is Gleason-lite unlabeled | Part II | Structural |
| SP-16 | $J$ evolves states (static→dynamic) | Part II | Structural |
| SP-17 | CHSH bipartition chosen, not forced | Part II | Structural |
| SP-18 | Schrödinger derivation absorbs imaginary part | Part II | Minor |
| ~~**SP-19**~~ | ~~Hilbert space = spinor rep identification~~ | Part III | ✅ Fixed (Lemma 9.1 with 5 named inputs + fallback) |
| SP-20 | Lorentzian scale factor $\sqrt{1-t^2}$ imported | Part III | Structural |
| SP-21 | Lorentzian-sig = oscillatory-evolution "by definition" | Part III | Structural |
| SP-22 | Unit-lapse vs cascade-lapse $N(4)$ tension | Part III | Structural |
| SP-23 | BH $S=A/d$ conflates unit-ball with physical horizon | Part II=III | Structural |
| SP-24 | "No absolute scale" contradicts $M_{\rm Pl,red}$ use | Part II=III | Structural |
| SP-25 | "Different states, different metrics" not instantiated | Part II=III | Structural |
| SP-26 | In-domain uniqueness ≠ cross-domain consistency | Part II=III | Structural |
| SP-27 | $d=12$ self-dual crossing is 0.225% near-miss + KK-tension | Part IVa | Structural + Check-7 |
| ~~SP-28~~ | ~~"$12 = 8+3+1$" and "rank = 4" are numerical coincidences~~ | Part IVa | ✅ Fixed |
| ~~SP-29~~ | ~~"SU(3) couples chirally" is factually wrong~~ | Part IVa | ✅ Fixed |
| SP-30 | "Three generations" is "three visible + suppressed 4th" | Part IVa | Structural |
| **SP-31** | **Fermion obstruction factor (b) is physics-intuition** | Part IVb | **Structural, load-bearing on every fermion mass** |
| SP-32 | Mass formula $(2\sqrt{\pi})^{-(n_D+1)}$ "+1" observer toll asserted | Part IVb | Structural |
| ~~SP-33~~ | ~~$\alpha_s$ doesn't pick up obstruction from $d=5$ (inconsistent rule)~~ | Part IVb | ✅ Fixed (Remark scope articulated) |
| SP-34 | "Independent $C$ from $m_\tau$" check is ambiguously circular | Part IVb | Minor |
| SP-35 | Cabibbo 1/2 factor is integer-fit among $\{1,2,3\}$ | Part IVb | Structural |
| SP-36 | Source-selection types defined post-hoc from 7 observables | Part IVb | Structural |
| ~~SP-37~~ | ~~"$d=14$ carries hairy-ball obstruction" is factually wrong~~ | Part IVb | ✅ Fixed |

## Notes on scope

- This file documents **only** soft spots the papers do not themselves acknowledge. Items already flagged in each paper's "What this paper does not do" or "Open questions" sections (e.g., the observable-dependent $k_Q$ in the Supplement, the variational max-over-min in Part 0, the Gram correction being imported into Part I, the second $G_d$ route in Part II=III, the absolute-mass dimensional inputs in Part IVb, the thermal-spectrum derivation, the Page curve, the tensor $r$ magnitude) are deliberately excluded.
- Severity reflects impact on the cascade's headline claims, not the ease of fixing each soft spot. SP-1 through SP-4 are classified **Exploratory** because the Prelude is an exploration of the cascade's minimum starting point rather than the load-bearing first link; they would become Foundational only if the Prelude is promoted to load-bearing. **All four Prelude soft spots are now ✅ closed in the audit sense:** SP-2, SP-3, SP-4 via the declared austerity axiom (Prelude Definition 2.2); SP-1 via explicit acknowledgement in the Prelude's Status box and §10 Open Question 3. The underlying *interpretive* issue at SP-1 (what fixes the logic-to-geometry framework?) is research-scale and remains an open question inside the Prelude itself; the audit finding (the paper denied it was an assumption) is closed.
- **Load-bearing items by claim:**
  - SP-10 underwrites the $\rho_\Lambda$ headline closure at $-0.07\%$.
  - ~~SP-19 underwrites the $d=4$ derivation via (C1).~~ ✅ Closed: Lemma 9.1 added with 5 named inputs; remark notes the $d=4$ derivation still yields via (C2) + Cor 9.4 even if any input is disputed.
  - SP-21 underwrites Lorentzian signature.
  - SP-23 underwrites $S=A/4$ being equal to $V_d/d$ for *physical* horizons rather than just unit spheres.
  - SP-31 underwrites the $1/(2\sqrt{\pi})$ fermion obstruction factor at every Dirac layer — i.e., every charged-lepton and quark mass, $C = \alpha_s/(2\sqrt{\pi})$, and the entire geometric-topological factorisation.
- **Quantitatively testable items:**
  - SP-10 — compute the Gram sum on paths $[19,217]$ and $\{3,5,6,7,19,217\}$ and report the alternative residuals.
  - SP-17 — compute CHSH on the two alternative bipartitions of $\mathbb{C}^4$ and verify whether $2\sqrt{2}$ is robust.
  - ~~SP-33~~ ✅ fixed: obstruction-rule scope articulated in Part IVb Remark `rem:obstruction-scope`. Rule now covers all three SM gauge couplings consistently; formal derivation of the rule from a cascade action remains open.
  - SP-36 — test the source-selection rule against $\alpha_{\rm em}(M_Z)$, $m_W$, $m_e/m_\mu$, CKM $\theta_{13}$, $\theta_{23}$ (Remark 4.9's worked candidates) and verify whether the blind predictions close within experimental precision.
- **Conceptually tightenable items:** SP-5, SP-6, SP-15, SP-21, SP-23, SP-26, SP-31, SP-32, SP-35, SP-36. Each could be upgraded from "asserted" to "proved/derived" by supplying an explicit theorem. (SP-19 and SP-33 removed from this list — both now articulated.)
- **Factual corrections (minor but should be fixed):** ~~SP-29 (SU(3) is vectorial, not chiral)~~ ✅ fixed; ~~SP-37 ($d=14$ is Weyl, no hairy-ball obstruction on $S^{13}$)~~ ✅ fixed.

## Fixes Applied

Commits on this branch that close or modify entries above. Each entry records: soft-spot ID, what changed, and the resulting status.

### Commit (SP-29 and adjacent CP-phase paragraph)

**SP-29 — Closed.** The factually incorrect sentence *"$\mathrm{SU}(3)$ and $\mathrm{U}(1)$ couple chirally to fermions, while $\mathrm{SU}(2)$ couples only to left-handed fermions (vector-like pre-breaking, chiral after breaking)"* at `src/cascade-series-part4a.tex:201–205` was replaced with:

> *"This is a Clifford-algebra classification of the spinor representation space at each layer; it is distinct from the chirality structure of each gauge boson's coupling to fermions in the Standard Model (which is vectorial for $\mathrm{SU}(3)_c$, parity-violating for $\mathrm{SU}(2)_L$, and determined separately by the symmetry breaking of Section~3 and the fermion generation structure of Section~4). The assignment of $\mathrm{SU}(3)$, $\mathrm{SU}(2)$, $\mathrm{U}(1)$ to layers $d=12,13,14$ specifically is forced by Adams' theorem (Theorem~\ref{thm:adams-unique}), not by matching Clifford type to coupling chirality."*

The fix:
- Removes the factual error on SU(3) chirality.
- Separates Clifford-algebra spinor type (Weyl vs Dirac) from SM-coupling chirality (vectorial vs parity-violating), which are distinct concepts.
- Explicitly re-routes the gauge assignment through Adams' theorem, which is the actual derivation.
- Zero numerical predictions change; no theorem is touched.

**Adjacent CP-phase paragraph — Closed (same commit).** The claim *"$\mathrm{SU}(2)$ … does not generate a physical CP violation in the strong sector"* at `src/cascade-series-part4a.tex:207–210` conflated CKM CP violation (SU(2)-mediated) with strong-sector CP ($\theta_{\rm QCD}$, SU(3)). The paragraph was replaced with:

> *"The real phases ($+1$ at $d=12$, $-1$ at $d=14$) give parity-invariant propagator coefficients at the $\mathrm{SU}(3)$ and $\mathrm{U}(1)_{\rm em}$ layers, consistent with the observed vectorial character of both gauge interactions at the observer's frame. The imaginary phase ($i$ at $d=13$) marks the $\mathrm{SU}(2)$ layer as the unique propagator-odd layer in the gauge window; this is the layer at which the hairy ball zero forces symmetry breaking (Section~3). The strong-sector CP phase $\theta_{\rm QCD}$ is independently set to zero by the cascade's topological classification (Part~IVb Section~6), not by a leakage argument from the $d=13$ phase."*

The fix:
- Removes the mis-identified "SU(2) doesn't generate physical CP violation" claim (CKM does).
- Re-routes θ_QCD = 0 to its actual cascade derivation (Part IVb Theorem 6.1, via $\pi_3(S^{11}) = \mathbb{Z}_2$), not to a leakage argument.
- Retains the "propagator-odd layer" observation, which is internally cascade-consistent.

Both items were Minor severity. Cost to the series: ~6 sentences replaced; zero numerical or theorem impact.

### Commit (austerity axiom declared in Prelude)

**SP-2, SP-3, SP-4 — Closed.** The three Prelude parsimony choices (finite-vs-$\aleph_0$ dimension; countable-vs-uncountable independence; $\mathbb{R}^*$-dilation quotient) that were previously implicit are now governed by an explicit Definition~2.2 (Austerity), added right after Definition~2.1 ($0\neq 1$). The austerity principle has three clauses:

1. (i) Parameter economy — no unexplained numerical, categorical, or symmetry-group input.
2. (ii) Minimal strength — no assumption strictly stronger than $0\neq 1$ where a weaker sufficient assumption exists, with strength measured by logical implication.
3. (iii) Unobservable quotient — quotient out any continuous symmetry whose action is unobservable from within the structure.

Each step of the Prelude chain that previously smuggled a parsimony principle now explicitly cites the clause invoked:

- Theorem 4.1 (countable independence) proof: "Dimension is either 0 or $\infty$ (clause (i))" + "Countable rather than uncountable (clause (ii))".
- §5 (scale invariance): $\mathbb{R}^*$-dilation is quotiented out "by clause (iii)".
- §8 (chain summary table): added "Austerity" column marking steps 2 and 3 with the relevant clauses.

**SP-1 — Closed (audit sense).** Theorem 3.1's interpretive bridge from logical $0\neq 1$ to geometric "no shared component in an inner-product space" is a *category-different* issue from SP-2/3/4. Austerity governs which mathematical structure is admissible *once the interpretive framework is fixed*; it does not fix the interpretive framework itself. The Prelude's new §10 Open Question 3 treats this explicitly, with three sub-questions describing resolution paths: (a) is inner-product-space the unique minimal geometric realisation of $0\neq 1$? (b) can austerity be extended with a fourth clause governing interpretive choice? (c) is inner-product interpretation itself a theorem of some more austere framework? The Prelude's Status box also names the interpretive bridge explicitly as a "separate structural choice, not a consequence of austerity, also flagged as open". By the audit's own rule — "documents only soft spots the papers do not themselves acknowledge" — SP-1 moves out of the active audit the moment the Prelude acknowledges it. The conceptual issue (what fixes the interpretive framework) is unresolved; the *audit finding* (the paper denied this was an assumption) is closed.

**Phase 2 and Phase 3 added as Prelude Open Questions.** Two further hardening items — formalising the partial order of assumption strength (needed for clause (ii) across all downstream applications), and proving $B^\infty$ is *uniquely* forced by Definition 2.1 + Definition 2.2 up to isomorphism — are now Open Questions 2 and 1 respectively in the Prelude. Resolving Open Question~1 would promote the Prelude from *conditionally forced given austerity* to *unconditionally forced*.

**Does this close SP-1 through SP-4 in the audit sense?**
- SP-2, SP-3, SP-4: ✅ Yes. Each is now an explicit application of a declared clause of Definition 2.2. They are no longer *hidden* assumptions; they are *declared* meta-rules. Any remaining critique is against austerity itself (e.g., "why these three clauses?"), not against the Prelude's chain. Upgrade from "smuggled assumption" to "declared meta-principle" — genuine hardening.
- SP-1: ✅ Yes, in the audit sense. The interpretive bridge is not closed *conceptually* (austerity is a parsimony rule, not an interpretation rule), but the Prelude now explicitly names it as a separate structural choice flagged as open in Open Question 3 with three sub-questions. By the audit's own scope rule — "soft spots the papers do not themselves acknowledge" — SP-1 moves out of the active audit once the paper acknowledges it. Resolution of the underlying question is research-scale (OQ 3), but the audit finding is closed.

**Problems with being explicit in the paper.** Three structural costs worth acknowledging:

1. *"One axiom" framing loses one.* The cover sheet's marketing phrase "one hypothesis" is unaffected (it's the cover-sheet identification, not the Prelude chain), but the Prelude's implicit framing ("$B^\infty$ from $0\neq 1$ alone") becomes "$B^\infty$ from $0\neq 1$ plus austerity." The Status box has been updated accordingly. This is honest but costs rhetorical simplicity.

2. *New attack surface.* Critics can now attack the austerity principle directly. Before: hidden assumptions, critics have to dig them out. After: declared principle, critics can question its clauses, its meta-mathematical status, or its completeness. This is arguably a *feature* (invites constructive criticism rather than gotcha attacks) but it is a real change.

3. *"Austerity" stretches axiom terminology.* Austerity is a meta-mathematical preference rule, not a mathematical axiom within a single structure. The Prelude explicitly notes this: *"Austerity is a methodological principle, not a mathematical theorem. It is the second pre-mathematical input of the cascade series."* Calling it a "Definition" rather than an "Axiom" in the TeX mitigates this. Further formalisation (Open Question 2) may clarify.

Net cost: ~30 lines added to Prelude (one definition, one Open Questions section, table column, a few proof annotations, Status box rewrite). Zero numerical predictions touched. SP-2/3/4 transition from *hidden assumption* to *declared meta-rule with open uniqueness question*.

### Commit (SP-37 + bonus tightening of all four source-pairing rationalisations)

**SP-37 — Closed.** The factually incorrect sentence *"$d=14$ … the U(1) hypercharge layer, the highest of the window and the only one carrying a hairy-ball obstruction that produces the universal $2\sqrt{\pi}$ factor"* at `src/cascade-series-part4b.tex:771` was replaced. Corrections:

- Removed the false claim that $d=14$ carries a hairy-ball obstruction. $d=14$ operates on $S^{13}$ (odd-dimensional); hairy-ball zeros live on even-dimensional spheres. The obstruction is at $d=13$ (Dirac on $S^{12}$).
- Re-attributed the $2\sqrt{\pi}$ factor correctly: it appears at *every* Dirac layer crossed on a fermion's descent (Theorem 2.2), not specifically at $d=14$.
- Replaced with a structural reason for the $d=14$ assignment: a gauge-mediated coupling descending into the observer's frame from above enters the gauge window at $d=14$ (its highest layer); Green's function response is maximised at this entry point.
- The $d=13$ Dirac obstruction that contributes $1/\sqrt{\pi}$ to U(1)'s descent (Theorem 4.9) is now correctly attributed as "encountered en route" rather than "carried by $d=14$".

**Bonus: all four source-pairing rationalisations tightened.** While the SP-37 fix was in the same remark, the other three pairings (Absolute→$d_1$, Observer→$d_V$, Amplitude→$d_0$) had a consistent stylistic issue: each stated *"Green's function response is maximised"* as if derived, when in fact this is a numerical computation (`tools/cascade_greens_function.py`), not a closed-form theorem. The paper's own Remark 4.8 "Does not" list already acknowledges the formal proof is open. The four pairings have been harmonised to:

- State the *structural* role of the distinguished layer in the observable's descent.
- State the *numerical* Green's function maximum.
- Explicitly cite the "formal derivation open" caveat, pointing to Remark 4.8.

Plus a concluding sentence after the bullets: *"Each rationale identifies $d^*$ by a structural role in the observable's descent; the numerical claim that the Green's function response is maximised at the assigned $d^*$ is verified layer-by-layer via the eigenstructure of the cascade action's discrete Laplacian (tools/cascade_greens_function.py), but the closed-form derivation is open."*

This distinguishes the *structural assignment* (derived, forced) from the *Green's function maximum* (numerical, pending formal proof), which the original text conflated.

Cost: 4 bullet rewrites + 1 new summary sentence. Zero numerical predictions change; Theorem 4.4, Theorem 4.5, Theorem 4.10, Theorem 5.1 all untouched. Remark 4.8's open-questions list is referenced but unchanged.

### Commit (SP-8: Theorem 15.7 relabelled as first-order, strengthened to upper bound)

**SP-8 — Closed.** Theorem 15.7 of the Part 0 Supplement stated $\epsilon = (2/n^2)\sum_{i<j}(1-C_{ij})$ as an equality; the proof used "first-order perturbation theory" and numerical verification showed a 0.17% residual. The `=` was a cosmetic over-claim.

Changes at `src/cascade-series-part0.0.tex:153–168`:

1. Renamed theorem from "Eigenvalue deficit from perturbation theory" to "First-order eigenvalue deficit".
2. Replaced the `=` with `= … + O(‖D‖²)` in the statement, and added an explicit observation that the second-order correction is *positive*: the first-order formula is an *upper bound* for the exact eigenvalue deficit.
3. Extended the proof to exhibit the second-order term from standard Rayleigh–Schrödinger perturbation theory and show the positivity explicitly. Proof is now fully self-contained.
4. Updated the verification paragraph to name the first-order value $\epsilon^{(1)}$ explicitly and note that the exact value sits below it, consistent with the upper-bound direction.

Plus one phrase tightening at `src/cascade-series-part0.0.tex:305`: *"gives an exact sum"* → *"gives an explicit first-order expression as a sum of Beta function ratios, with second-order correction bounded by $\|D\|^2$"*.

**Structural upgrade, not just cosmetic.** The original statement had `=` and a numerical 0.17% residual with no directional information about the error. The new statement:

- is *mathematically honest* (explicit $O(\|D\|^2)$ remainder);
- is *stronger* (the RHS is now an upper bound, not merely an approximation);
- *predicts the sign* of the discrepancy (exact < first-order), which matches the numerical verification (0.008159 < 0.008173).

The 0.17% residual went from "cosmetic mismatch" to "quantitative evidence that the second-order correction is $\lesssim$ 0.2% for a typical path" — a useful handle for future hardening.

**Downstream impact:** none.

- Corollary 15.18 (derived coupling $k_Q^{(1)}$): uses the exact eigenvalue deficit $\epsilon$, not Theorem 15.7's first-order formula. The corollary's content is unchanged.
- "What this section proves" item (line 289): already said "first-order perturbation theory". Unchanged.
- Part I's Gram correction: uses Theorem 15.11 (a different theorem, explicitly first-order in its name). Unchanged.

Cost: 1 theorem statement rewrite + extended proof + 1 verification sentence + 1 downstream phrase. Zero numerical predictions change; zero tools code changed. The supplement is tighter, not just relabelled.

### Commit (SP-28: generator count demoted from theorem to remark)

**SP-28 — Closed.** Part IVa §2.7 previously stated:

> **Theorem [Generator count]** The number of cascade layers between $d_0=7$ and $d_1=19$ is exactly $12 = \dim(\mathrm{SU}(3))+\dim(\mathrm{SU}(2))+\dim(\mathrm{U}(1)) = 8+3+1$.
>
> The total rank of $\mathrm{SU}(3)\times\mathrm{SU}(2)\times\mathrm{U}(1)$ is $2+1+1=4$, equal to the observer's spacetime dimension. This is the Bott mirror at the level of Lie algebra rank …

Two issues: (1) the "theorem" observed a numerical equality $12 = 12$ without proving it structurally; the 12-layer count and the 8+3+1 gauge-dimension count come from *independent derivations* (threshold spacing in Part 0 vs Adams + Clifford–Lefschetz at layers 12, 13, 14). Their coincidence is a consistency check, not a derivation. (2) Similarly, "rank = 4 = spacetime dimension" is a numerical coincidence between separately-fixed values, not a forced identity.

Changes at `src/cascade-series-part4a.tex:221–240`:

- `\begin{theorem}[Generator count]` → `\begin{remark}[Generator count coincidence]`.
- The statement is expanded into two labeled computations (a) threshold spacing and (b) gauge-algebra assembly, explicitly sourcing each to its separate derivation, and labelled as "a numerical consistency check … not a structural identity forced by either derivation alone".
- The rank paragraph is reframed from "This is the Bott mirror at the level of Lie algebra rank" to "The cascade does not independently derive that gauge-window total rank must equal the observer's spacetime dimension … the equality is a second numerical coincidence of the same kind", noted "as a consistency check without claiming it is structurally forced".

**Downstream impact:** none. The label `thm:generators` is referenced nowhere else in the sources (verified by grep); changing `theorem` to `remark` with the same label is safe.

**What this buys.** Removes a "theorem-that-isn't" that a hostile reviewer would flag. Keeps the observation (two independent derivations giving the same integer *is* interesting, it's just not a theorem). Strengthens the rest of Part IVa by contrast: Adams' theorem (Theorem 2.4) and the Lefschetz obstruction (Theorem 3.2) remain as genuine structural theorems, now clearly distinguished from the consistency-check remark.

Cost: ~10 lines rewritten. Zero numerical predictions changed; zero theorems invalidated.

### Commit (SP-19: Lemma 9.1 added, upgrades (C1) from assumption to theorem)

**SP-19 — Closed (Option B).** The previous Part III §9.1 contained Lemma 9.2 with a conditional statement: *"For the cascade's state space (carrying $J$ with $J^2=-\mathrm{Id}$) **to serve as** the spinor representation space of $\mathrm{Spin}(1,d-1)$, the minimal spinor representation must be irreducibly complex."* The antecedent (the identification of the cascade Hilbert space with a spinor representation of the observer's Lorentz group) was never justified, making (C1) — and therefore one leg of Theorem 9.3's $d=4$ derivation — rest on an implicit assumption.

**Resolution applied:** Option B from the SP-19 analysis — formalise the identification as a lemma with named inputs.

Changes at `src/cascade-series-part3.tex`:

1. Added an introductory paragraph to §9.1 naming the gap explicitly: Paper II's construction does not equip $\mathcal{H}$ with a $\mathrm{Spin}(1,d-1)$ action; the identification is a downstream step.
2. Replaced the old Lemma 9.2 with a new **Lemma 9.1 "Cascade Hilbert space carries the minimal complex Lorentz representation"** (`\label{lem:cascade-spinor-id}`). The lemma lists five inputs explicitly:
    - (i) Physical identification hypothesis (Def 2.1) — series axiom
    - (ii) Empirical Lorentzian spacetime — empirical input, acknowledged
    - (iii) Relativistic QM covariance (Wigner) — standard QM, imported
    - (iv) Cascade complex structure (Paper II Thm 6.1) — cascade theorem
    - (v) Austerity (Prelude Def 2.2, clause (i)) — now declared meta-principle
3. The proof structures the identification as four steps: (1) the representation exists (from (i)–(iii)); (2) it is complex-admissible (from (iv) via Schur); (3) minimality forces irreducibility (from (v)); (4) Clifford classification pins the complex-admissible dimensions.
4. Added **Remark** (`\label{rem:sp-19-inputs}`) naming which inputs are cascade-internal (iv, v) vs physical-hypothesis (i) vs empirical (ii) vs imported-QM (iii). Crucially, the remark provides a **fallback**: if any input is disputed, Theorem 9.3's conclusion ($d=4$) still yields via (C2) Lovelock uniqueness + Corollary 9.4 Ricci-flatness, which are independent of the spinor-representation identification.
5. Added labels to the previously-label-free Theorem 9.3 (`thm:d4`), Corollary 9.4 (`cor:ricci-flat`), and §9.2 (`sec:clifford-table`) so the new lemma can reference them.
6. Added a bibitem for the Prelude (`\cite{paper0pre}`) in Part III's bibliography.

**What this buys structurally:**

- (C1) was previously a *conditional* whose antecedent was hidden. It is now a *theorem* (Lemma 9.1) with explicitly named inputs. The Schur-lemma argument that was Lemma 9.2's content is preserved as Step 2 of the new lemma's proof.
- If a reviewer disputes any of the five inputs, they are forced to identify *which one*. The previous hidden-assumption framing gave a reviewer no lever — they could simply say "this identification is unjustified" without having to commit. The new framing forces the dispute to land on a specific named input.
- The fallback remark means that even if (C1) is successfully disputed, $d=4$ still has two cascade-internal selections via (C2) and Cor 9.4. This is the insurance: SP-19's closure doesn't depend on the Lemma 9.1 proof surviving every attack. The series' $d=4$ derivation has three independent selections, of which two are immune to SP-19.

**What it does not claim:**

Input (iii) — "relativistic QM covariance" — is used as a standard QM result, not derived from the cascade. The lemma explicitly says so in Remark `rem:sp-19-inputs`. A deeper hardening (Option D in the SP-19 analysis) would put Lorentz covariance into Paper II itself; that remains open work, not required by the current hardening.

Cost: ~80 lines added to Part III §9.1 (replacing ~15 lines of the old Lemma 9.2). Four labels added to existing items. One bibitem added. Zero numerical predictions changed; Theorem 9.3 and Corollary 9.4 are preserved exactly. The new lemma *adds* a cascade-internal derivation where previously there was a conditional.

### Commit (austerity framing upgrade: Definition 2.2 → Principle 2.2, derived)

**Framing upgrade (not a new audit finding).** During SP-19 work it became clear that austerity need not be declared as a second pre-mathematical input. If Definition 2.1 ($0\neq 1$) is taken as the *sole* pre-mathematical input (as the Prelude's Section 1 "The Problem with Starting Points" already argues), then the three austerity clauses are consequences of what "sole input" means: any construction introducing content not forced by $0\neq 1$ violates the sole-input commitment. Austerity is the operational content of sole-input status, not a separate axiom.

Prelude changes:

1. **Preamble:** added `\newtheorem{principle}[theorem]{Principle}` so Principle 2.2 shares counter numbering with Definition 2.1.
2. **§2 body:** converted `\begin{definition}[Austerity]` to `\begin{principle}[Austerity, derived from Definition~\ref{def:axiom}]`. Added a proof block "Derivation from Definition 2.1" showing each clause (i)–(iii) is a distinct way to violate sole-input commitment. Added a Status note labelling Principle 2.2 as a *derivation rule* (analogous to modus ponens for propositional logic) rather than a further axiom.
3. **Label renamed** `def:austerity` → `princ:austerity` throughout the Prelude (one global sed). All cross-references updated from `Definition~\ref{def:austerity}` to `Principle~\ref{princ:austerity}` (second sed).
4. **Status box rewritten:** from *"Given $0\neq 1$ and the austerity principle as two declared pre-mathematical inputs"* to *"The cascade series has one pre-mathematical input, Definition 2.1. Principle 2.2 (austerity) is not a second input: it is the operational content of Definition 2.1's status as sole input, derived in §2."*
5. **§8 chain summary paragraph** updated to match: *"No step introduces a free parameter beyond the single declared pre-mathematical input Definition 2.1. Principle 2.2 (austerity) is not a second input."*
6. **§10 Open Questions intro** reframed: *"Principle 2.2 derives three previously-implicit parsimony choices as clauses of a single derivation rule from Definition 2.1"* (rather than "converts three … into three clauses of a single meta-principle").
7. **Labels added** to §1 (`sec:starting-points`) and §2 (`sec:what-nothing-means`) so the principle's derivation can cite them.

Part III changes:

8. Lemma 9.1 input (v) updated: *"Austerity (Prelude, Principle 2.2, clause (i): parameter economy). Austerity is not a separate input: in the Prelude it is derived in place from Definition 2.1 as the operational content of its sole-input status."*
9. Lemma 9.1 Remark text updated: *"the austerity principle declared in the Prelude (Principle 2.2, derived there from Definition 2.1) as a meta-mathematical commitment of the series."*

**What this buys.** The "one axiom, zero free parameters" framing is restored. Previously the Prelude had "one axiom + one meta-principle"; now it's "one axiom, with austerity as its derived inference rule." The austerity clauses remain citable by downstream papers exactly as before (Lemma 9.1's input (v) still cites "Principle 2.2, clause (i)"); only the framing of austerity's status changes.

**What the derivation does not claim.** The meta-step "sole-input commitment → don't introduce content not forced" is itself a commitment about how mathematical derivation works. This is the same status as modus ponens (an inference rule built into "logical derivation" rather than a separate axiom). A strict formalist could insist it be declared; the Prelude takes the standard position that it's implicit in "sole input."

**What this does not close.** The Prelude's Open Question 1 (uniqueness of $B^\infty$ under austerity) remains open. Austerity-as-derived is still defensibly-minimal-not-forced; promoting to "forced" still requires a uniqueness theorem.

Cost: ~20 lines changed in the Prelude; ~5 lines in Part III. Zero numerical predictions changed; zero theorems invalidated; no SP-numbered audit finding reopens or closes. This is a framing upgrade that makes the "one axiom" claim honest.

### Commit (SP-4 sharpening: ℝ* is the unique austerity-compatible quotient)

**SP-4 refinement.** The SP-4 entry originally flagged *"absence of an external ruler does not force invariance under $\mathbb{R}^*$-dilation specifically (vs conformal group, vs discrete scale invariance, vs $\mathbb{C}^*$)."* The austerity principle closed SP-4 in the audit sense by declaring the quotient explicitly; the uniqueness-of-$\mathbb{R}^*$ sub-question remained lingering. With austerity now derived from Definition 2.1's sole-input commitment, the argument against alternatives becomes clean.

Prelude §5 now includes a paragraph enumerating why each alternative candidate symmetry fails under austerity:

- **Full conformal group $\mathbb{R}^* \times \mathrm{SO}(\mathcal{H})$.** $\mathrm{SO}(\mathcal{H})$ rotations relabel which directions carry the $e_0, e_1, \ldots$ distinctions — the distinction content *is* observable (it's what Definition 2.1 declares). Clause (iii) quotients only the unobservable $\mathbb{R}^*$ factor.
- **$\mathbb{C}^*$-phase rotation.** Requires a complex structure $J$ with $J^2=-\mathrm{Id}$. No such structure is present at the Prelude stage; $\mathcal{H}$ is constructed over $\mathbb{R}$. The forced precession of Paper II induces $J$ downstream, at which point the $\mathbb{C}^*$ question becomes a separate downstream question; it is not addressed at the Prelude level.
- **Discrete scale invariance** (quotient by fixed ratio $\lambda = r$). Selecting a specific $r$ introduces an unexplained numerical input, violating clause (i).

Conclusion: $\mathbb{R}^*$-dilation is the **unique** continuous, parameter-free, fully-unobservable symmetry defined on the real Hilbert space at the Prelude stage. Clause (iii)'s application is not just "one acceptable choice" but the unique austerity-compatible quotient at this stage.

**What this buys.** SP-4's lingering "uniqueness of $\mathbb{R}^*$" sub-question is now closed inside the Prelude. The `$\mathbb{P}\mathcal{H}$ is the unique quotient` claim in §5 is no longer an assertion; it is a clause-by-clause derivation against the alternative candidates. A reviewer can still attack the premise that `$e_0, e_1$ distinctions are observable` (which is a reading of Definition 2.1), but cannot simply list an alternative quotient without addressing why it fails one of the three clauses.

**What this does not claim.** The downstream question — whether $\mathbb{C}^*$ should be quotiented once Paper II induces complex structure — is flagged as future work, not resolved here. If Paper II's derivation of $J$ makes $\mathbb{C}^*$-phase unobservable at the quantum amplitude level, the cascade may quotient there too (this is in fact what QM's projective Hilbert space does). But that's Paper II content, not Prelude content.

Cost: ~30 lines added to Prelude §5 (enumeration of failed alternatives). Zero numerical predictions changed; zero theorems invalidated.

### Commit (open-questions cleanup after austerity/ℝ* upgrades)

Consistency pass across three Prelude sections that referenced austerity in the pre-derivation framing:

1. **§9 "Does not derive physics" bullet.** Previously referenced "austerity principles made explicit in the chain (parameter economy at step 2; binary-test discreteness at step 3; ℝ*-scale invariance at step 5)" as if austerity were a separately-declared bundle of principles. Now reframes: "the single declared pre-mathematical input (Definition 2.1) and the austerity derivation (Principle 2.2) that follows from its sole-input status", with the step-wise clause citations retained. Clause names aligned with Principle 2.2 (parameter economy, minimal strength, unobservable quotient).

2. **§10 Open Question 1 (uniqueness of $B^\infty$).** Previously listed "complex Hilbert space" and "quaternionic Hilbert space" as candidate alternatives "worth ruling out" — candidates that the austerity+§5 work now rules out explicitly. Rewritten to separate (a) alternatives now explicitly ruled out inside the Prelude (complex/quaternionic starting points by clause (ii); non-separable Hilbert space by clause (ii)) from (b) alternatives that remain open candidates (non-Hilbert inner-product topologies, pathological embeddings). The uniqueness-theorem target is retained.

3. **§10 Open Question 3(b).** Previously read *"Can austerity be extended with a fourth clause..."*. The "extended" framing assumed austerity was a free-standing declaration to which clauses could be added. With austerity now derived, the cleaner question is whether the *sole-input commitment of Definition 2.1* (from which austerity is derived) extends to interpretive-framework choice. Rewritten to ask this directly.

4. **Part III `rem:sp-19-inputs`.** Changed "austerity principle declared in the Prelude … as a meta-mathematical commitment of the series" to "austerity principle of the Prelude (Principle 2.2, derived there from Definition 2.1 as the operational content of its sole-input status — i.e. as a derivation rule of the series, not a separate axiom)."

**Net effect:** the Prelude's open-questions list and Part III's Lemma 9.1 remark are now internally consistent with the derived-austerity framing. No open question is closed or opened by this cleanup; the scope of each is sharpened.

Cost: ~15 lines changed across the two files. Zero numerical predictions, zero theorems, zero audit SP-numbered findings affected.

### Commit (SP-33: obstruction-rule scope articulated for gauge-boson descent)

**SP-33 — Closed.** Part IVb previously contained an apparent inconsistency: Theorem 4.2 ($\alpha_s$) uses $\alpha_s = \alpha(12)\exp(\Phi(12\to 4))$ with no $1/\sqrt{\pi}$ obstruction factor, despite the descent path crossing the Dirac layer $d=5$; but Theorem 4.9 (Weinberg angle) applies a $1/\sqrt{\pi}$ factor to $g_1'$ for crossing the Dirac layer $d=13$. The implicit rule that reconciled these was never stated.

The rule, now articulated explicitly as Remark `rem:obstruction-scope` in Part IVb §4:

> **A gauge coupling picks up a factor of $1/\sqrt{\pi}$ for each broken-gauge-symmetry Dirac layer crossed on the descent path. Generation Dirac layers do not contribute a gauge-boson obstruction factor.**

Changes to `src/cascade-series-part4b.tex`:

1. **Theorem 4.9 Step 2 tightened.** *"A field passing through a Dirac layer encounters the topological obstruction"* → *"A gauge coupling passing through a broken-symmetry Dirac layer encounters the topological obstruction imposed by the resolving VEV"*. Added forward reference to the new scope remark. Also notes that $\mathrm{U}(1)$'s descent crosses both $d=13$ (broken) and $d=5$ (generation), with only the first contributing.

2. **New Remark `rem:obstruction-scope`** inserted after the asymmetry-is-forced remark. The remark:
   - Enumerates the three Dirac layers in the descent range: $d=5$ (Gen 3), $d=13$ (SU(2) broken), $d=21$ (Gen 1).
   - States the rule explicitly.
   - Verifies consistency across all three SM gauge couplings:
       - $\alpha_s$: zero broken-symmetry crossings → unmodified.
       - $g_2$: at its own breaking layer → obstruction consumed by breaking.
       - $g_1'$: one broken-symmetry crossing ($d=13$) → one factor $1/\sqrt{\pi}$.
   - Gives the physical reason for the distinction: $1/\sqrt{\pi}$ comes from the propagator mixing with a VEV occupying the hairy-ball zero. Generation layers have fermion wavefunctions at the zero (gauge-fermion coupling is a contact interaction, not a propagator modification); only broken-symmetry layers have gauge VEVs.
   - Contrasts with the fermion obstruction rule (Theorem 2.2): fermions see every Dirac layer because they couple to Dirac structure universally via the spin connection; bosons see only broken-symmetry layers because they couple to gauge VEVs.

3. **Cross-reference added to Theorem 4.2.** Parenthetical note after the α_s formula explains why no $1/\sqrt{\pi}$ factor enters despite crossing $d=5$.

**What this buys.**

- Apparent inconsistency between Theorem 4.2 and Theorem 4.9 resolved by a single named rule.
- Three SM gauge couplings treated consistently.
- The rule is falsifiable: a new gauge observable requiring a different count of $1/\sqrt{\pi}$ factors than the rule predicts would falsify it.
- Boson-fermion asymmetry (Theorem 2.2 vs this rule) is now physically motivated.

**What this does not claim.**

The rule is articulated structurally, not derived from the cascade's discrete action. Formal derivation from the action principle (Part IVb Remark 4.6) would promote it from "articulated" to "derived". Remains open, tracked in `rem:phase-family`'s open-questions list.

Cost: ~70 lines added to Part IVb §4. Zero numerical predictions change; Theorems 4.2, 4.9, 4.10, 5.1, 6.1 retain their existing formulas exactly. The new remark names what the papers were already doing implicitly.

---

## Hardening priorities

Suggested order for the hardening phase, cheapest first.

### Tier A — Trivial fixes (hours)

| ID | Action | Cost |
|---|---|---|
| SP-29 | Remove "SU(3) couples chirally" sentence in Part IVa §2.2 or replace with the correct statement | 1 line |
| ~~SP-37~~ | ~~Replace "d=14 … carrying a hairy-ball obstruction" with "d=14's coupling picks up the 2√π factor by crossing d=13"~~ | ✅ Done |
| ~~SP-8~~ | ~~Label Theorem 15.7 explicitly as first-order perturbative~~ | ✅ Done |
| ~~SP-28~~ | ~~Reframe "12 = 8+3+1" and "rank = 4" in Part IVa §2.7 as observations~~ | ✅ Done |
| Prelude framing | Add a "Status: exploratory" box to the Prelude; cite the cover sheet as load-bearing hypothesis | 1 box |

### Tier B — Articulate implicit rules (days)

| ID | Action | Cost |
|---|---|---|
| ~~SP-33~~ | ~~Write a half-page in Part IVb §4 stating the obstruction-rule scope explicitly~~ | ✅ Done (Remark `rem:obstruction-scope` added; rule verified consistent across $\alpha_s$, $g_2$, $g_1'$) |
| SP-32 | In Part IVb §2, unify the observer toll and the n_D count into a single derivation from a propagator formula rather than asserting the "+1" in a remark. | 1–2 pages |
| ~~SP-19~~ | ~~Articulate (C1)'s identification step~~ | ✅ Done (Option B: Lemma 9.1 with 5 named inputs; fallback to (C2)+Cor 9.4 in remark) |
| SP-21 | In Part III §10, replace "by definition" with "in the cascade's identification hypothesis, oscillatory propagator ⇔ Lorentzian signature" and defend the hypothesis. Or acknowledge that this is Wick rotation by another name. | 1 paragraph |
| SP-22 | In Part III §4.4, reconcile unit-lapse 4D metric with cascade lapse N(4) = 3π/8 explicitly. | 1 paragraph |

### Tier C — Blind-test predictive rules (weeks, high-value)

Each of these either hardens the rule significantly or exposes a defect early. All are testable by computation.

| ID | Test | What it settles |
|---|---|---|
| SP-10 | Compute the Gram sum on paths [19,217], {3,5,6,7,19,217}, and any other plausible ρ_Λ path. Publish which gives the best closure and why. | Whether the -0.07% headline is robust or cherry-picked |
| SP-36 | Blind-test the source-selection rule against α_em(M_Z), m_W absolute, m_e/m_μ, CKM θ_13, θ_23 per Remark 4.9's "falsifiable prediction". Publish the blind predictions *before* checking them. | Whether the three-flag rule is genuinely predictive or trained on the 7-observable set |
| SP-17 | Compute CHSH on alternative bipartitions of ℂ⁴. Expected: Tsirelson bound gives 2√2 for any maximally-entangled bipartition. If it does, the CHSH result is robust; soft spot downgrades to Minor. | Whether the bipartition choice in Part II §10.3 is cosmetic or structural |
| ~~SP-33~~ | ~~Apply the articulated rule consistently to all gauge couplings~~ | ✅ Done (Remark `rem:obstruction-scope` verifies for $\alpha_s$, $g_2$, $g_1'$; numerical values unchanged) |

### Tier D — Genuine open problems (months, research-scale)

| ID | What's needed | Why it matters |
|---|---|---|
| SP-31 | Derive the fermion obstruction factor (2√π)⁻¹ from a cascade action or propagator computation, rather than from the "obstruction consumes √π" intuition. Corollary 2.3's N(0)·Γ(½) identity is suggestive but not a derivation. | Load-bears on every fermion mass |
| SP-23 | Derive S = A/d for physical horizons (not just unit balls) from cascade boundary dominance, with explicit units and scaling. | Load-bears on BH thermodynamics |
| SP-5, SP-6, SP-15, SP-25, SP-26, SP-35 | Each could be upgraded from "asserted" to "proved/derived" by supplying an explicit theorem. Individually modest; collectively a review-resistant rewrite of the load-bearing proofs. | Tightens the "forced derivation" framing |

### What hardening does *not* require

- Addressing SP-1 through SP-4 while the Prelude remains exploratory. Promote them to priority only if the Prelude is later reframed as load-bearing.
- Resolving the already-acknowledged gaps (k_Q, 6π in α_em, second G_d route, tensor r, source-selection flags as cascade objects). Those are in the papers' own open-questions lists.

### Suggested first pass

Tier A + a subset of Tier B would take about a week and would materially strengthen the papers without changing any numerical result. That subset is probably:

1. All Tier A (1 day).
2. SP-33 articulation (the obstruction rule) — this is the highest-leverage tightening because it's the one cleanest example of an implicit rule, and articulating it might expose coherence issues early.
3. SP-19 articulation — equally high-leverage for the d=4 derivation's reading.

If those land cleanly, move to Tier C blind tests. If SP-33 or SP-19 articulation reveals an incoherence, fix in place before proceeding.
