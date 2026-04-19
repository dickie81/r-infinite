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

### SP-1. Logic-to-geometry translation (Theorem 3.1) — **Exploratory**
`src/cascade-series-prelude.tex:110–115`, discussion at `:102–108`.

The theorem's premise is "unit vectors representing two fully distinguishable states — states sharing no common component under any linear operation on $V$". That premise is already the geometric form of the conclusion. The theorem proves geometric no-common-component $\Rightarrow$ zero inner product rigorously; it does not prove that logical $0\ne 1$ $\Rightarrow$ geometric no-common-component. The paper denies this is an assumption ("not an additional assumption; it is a translation of the same fact into geometric language").

### SP-2. Finite $\to \aleph_0$ jump is parameter-economic, not mathematical (Theorem 4.1, step 2) — **Exploratory**
`src/cascade-series-prelude.tex:157–168`.

*"Refusing it would be [an additional assumption]"* — philosophical, not proved. $\aleph_0$ is itself a specific cardinal; the step privileges it over all finite cardinals by appealing to the Prelude §1 principle that a theory of everything cannot have inputs. That principle is assumed, not derived from $0\ne 1$.

### SP-3. "Countable rather than uncountable" presumes binary-test distinctions (Theorem 4.1, step 3) — **Exploratory**
`src/cascade-series-prelude.tex:170–179`.

*"Each distinction is a single bit: a binary test 'is the state $e_i$ or not?'"* — introduced here for the first time. Uncountable distinction is excluded "by the same parameter-economy principle that excludes finite $n$", chaining two unacknowledged assumptions.

### SP-4. $\mathbb{R}^*$-dilation invariance introduced as a new symmetry (§5) — **Exploratory**
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

### SP-8. Theorem 15.7 stated as equality, is first-order perturbative — **Minor**
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

### SP-19. Lemma 9.2 identifies the cascade's Hilbert space with "the spinor representation space of Spin(1,d−1)" without justification — **Structural** (load-bearing on the $d=4$ derivation)
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

### SP-28. Theorem 2.7 "generator count $12 = 8+3+1$" and "rank $= 4$" are numerical matches presented as structural — **Minor**
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

### SP-33. α_s's descent formula does not pick up obstruction factors from $d=5$, though the descent path crosses it — **Structural**
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

### SP-37. "Why the specific pairings type↦d$^*$" rationalisations include a factually wrong statement — **Minor**
`src/cascade-series-part4b.tex:766–774`.

The rationalisation for Gauge→$d_{\rm gw}=14$ reads: *"$d=14$ … the $\mathrm{U}(1)$ hypercharge layer, the highest of the window and **the only one carrying a hairy-ball obstruction** that produces the universal $2\sqrt\pi$ factor."* But $d=14$ is a Weyl layer on the *odd*-dimensional sphere $S^{13}$ — no hairy-ball obstruction. The hairy-ball obstruction lives at $d=13$ (Dirac, on $S^{12}$). What the rationalisation presumably intends is that $d=14$'s coupling picks up the $2\sqrt{\pi}$ factor *by crossing* $d=13$, not by carrying an obstruction itself. As stated, the claim misidentifies which layer carries the obstruction.

---

## Summary

| ID | Soft spot | Paper | Severity |
|---|---|---|---|
| SP-1 | Logic→geometry translation | Prelude | Exploratory |
| SP-2 | Finite→$\aleph_0$ parameter economy | Prelude | Exploratory |
| SP-3 | Binary-test countability | Prelude | Exploratory |
| SP-4 | $\mathbb{R}^*$-dilation as new symmetry | Prelude | Exploratory |
| SP-5 | $c_1$ uniqueness four-class exhaustiveness | Part 0 | Structural |
| SP-6 | Tower completeness misses self-dual radius | Part 0 | Structural |
| SP-7 | Scale=ratio, content=product rule | Part 0 | Structural |
| SP-8 | First-order $\epsilon$ stated as equality | Part 0 Supp | Minor |
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
| **SP-19** | **Hilbert space = spinor rep identification** | Part III | **Structural, load-bearing on $d=4$** |
| SP-20 | Lorentzian scale factor $\sqrt{1-t^2}$ imported | Part III | Structural |
| SP-21 | Lorentzian-sig = oscillatory-evolution "by definition" | Part III | Structural |
| SP-22 | Unit-lapse vs cascade-lapse $N(4)$ tension | Part III | Structural |
| SP-23 | BH $S=A/d$ conflates unit-ball with physical horizon | Part II=III | Structural |
| SP-24 | "No absolute scale" contradicts $M_{\rm Pl,red}$ use | Part II=III | Structural |
| SP-25 | "Different states, different metrics" not instantiated | Part II=III | Structural |
| SP-26 | In-domain uniqueness ≠ cross-domain consistency | Part II=III | Structural |
| SP-27 | $d=12$ self-dual crossing is 0.225% near-miss + KK-tension | Part IVa | Structural + Check-7 |
| SP-28 | "$12 = 8+3+1$" and "rank = 4" are numerical coincidences | Part IVa | Minor |
| ~~SP-29~~ | ~~"SU(3) couples chirally" is factually wrong~~ | Part IVa | ✅ Fixed |
| SP-30 | "Three generations" is "three visible + suppressed 4th" | Part IVa | Structural |
| **SP-31** | **Fermion obstruction factor (b) is physics-intuition** | Part IVb | **Structural, load-bearing on every fermion mass** |
| SP-32 | Mass formula $(2\sqrt{\pi})^{-(n_D+1)}$ "+1" observer toll asserted | Part IVb | Structural |
| SP-33 | $\alpha_s$ doesn't pick up obstruction from $d=5$ (inconsistent rule) | Part IVb | Structural |
| SP-34 | "Independent $C$ from $m_\tau$" check is ambiguously circular | Part IVb | Minor |
| SP-35 | Cabibbo 1/2 factor is integer-fit among $\{1,2,3\}$ | Part IVb | Structural |
| SP-36 | Source-selection types defined post-hoc from 7 observables | Part IVb | Structural |
| SP-37 | "$d=14$ carries hairy-ball obstruction" is factually wrong | Part IVb | Minor (factual) |

## Notes on scope

- This file documents **only** soft spots the papers do not themselves acknowledge. Items already flagged in each paper's "What this paper does not do" or "Open questions" sections (e.g., the observable-dependent $k_Q$ in the Supplement, the variational max-over-min in Part 0, the Gram correction being imported into Part I, the second $G_d$ route in Part II=III, the absolute-mass dimensional inputs in Part IVb, the thermal-spectrum derivation, the Page curve, the tensor $r$ magnitude) are deliberately excluded.
- Severity reflects impact on the cascade's headline claims, not the ease of fixing each soft spot. SP-1 through SP-4 are classified **Exploratory** because the Prelude is an exploration of the cascade's minimum starting point rather than the load-bearing first link; they would become Foundational only if the Prelude is promoted to load-bearing.
- **Load-bearing items by claim:**
  - SP-10 underwrites the $\rho_\Lambda$ headline closure at $-0.07\%$.
  - SP-19 underwrites the $d=4$ derivation via (C1).
  - SP-21 underwrites Lorentzian signature.
  - SP-23 underwrites $S=A/4$ being equal to $V_d/d$ for *physical* horizons rather than just unit spheres.
  - SP-31 underwrites the $1/(2\sqrt{\pi})$ fermion obstruction factor at every Dirac layer — i.e., every charged-lepton and quark mass, $C = \alpha_s/(2\sqrt{\pi})$, and the entire geometric-topological factorisation.
- **Quantitatively testable items:**
  - SP-10 — compute the Gram sum on paths $[19,217]$ and $\{3,5,6,7,19,217\}$ and report the alternative residuals.
  - SP-17 — compute CHSH on the two alternative bipartitions of $\mathbb{C}^4$ and verify whether $2\sqrt{2}$ is robust.
  - SP-33 — apply the obstruction rule consistently and compute the expected $\alpha_s$ if $d=5$ gave a $1/\sqrt{\pi}$ factor; compare to the formula that works.
  - SP-36 — test the source-selection rule against $\alpha_{\rm em}(M_Z)$, $m_W$, $m_e/m_\mu$, CKM $\theta_{13}$, $\theta_{23}$ (Remark 4.9's worked candidates) and verify whether the blind predictions close within experimental precision.
- **Conceptually tightenable items:** SP-5, SP-6, SP-15, SP-19, SP-21, SP-23, SP-26, SP-31, SP-32, SP-33, SP-35, SP-36. Each could be upgraded from "asserted" to "proved/derived" by supplying an explicit theorem.
- **Factual corrections (minor but should be fixed):** ~~SP-29 (SU(3) is vectorial, not chiral)~~ ✅ fixed; SP-37 ($d=14$ is Weyl, no hairy-ball obstruction on $S^{13}$) — still open.

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

---

## Hardening priorities

Suggested order for the hardening phase, cheapest first.

### Tier A — Trivial fixes (hours)

| ID | Action | Cost |
|---|---|---|
| SP-29 | Remove "SU(3) couples chirally" sentence in Part IVa §2.2 or replace with the correct statement | 1 line |
| SP-37 | Replace "d=14 … carrying a hairy-ball obstruction" with "d=14's coupling picks up the 2√π factor by crossing d=13" in Part IVb source-pairing remark | 1 line |
| SP-8 | Label Theorem 15.7 explicitly as first-order perturbative, or tighten to an inequality | 1 line |
| SP-28 | Reframe "12 = 8+3+1" and "rank = 4" in Part IVa §2.7 as *observations* rather than *structural derivations* | 1 paragraph |
| Prelude framing | Add a "Status: exploratory" box to the Prelude; cite the cover sheet as load-bearing hypothesis | 1 box |

### Tier B — Articulate implicit rules (days)

| ID | Action | Cost |
|---|---|---|
| SP-33 | Write a half-page in Part IVb §4 stating the obstruction-rule scope explicitly: "a boson's coupling picks up 1/√π on crossing a Dirac layer if that layer supports a broken gauge symmetry; it does not on crossing a generation Dirac layer." Then verify this for α_s, α_em running, and all gauge couplings. | 0.5–1 page |
| SP-32 | In Part IVb §2, unify the observer toll and the n_D count into a single derivation from a propagator formula rather than asserting the "+1" in a remark. | 1–2 pages |
| SP-19 | In Part III §9, state explicitly that (C1) assumes the cascade Hilbert space hosts a Spin(1,d-1) representation. Either justify it as a theorem or label it as an assumption. If an assumption, check that d=4 still follows from Lovelock + Cor 9.4 alone. | 1 page |
| SP-21 | In Part III §10, replace "by definition" with "in the cascade's identification hypothesis, oscillatory propagator ⇔ Lorentzian signature" and defend the hypothesis. Or acknowledge that this is Wick rotation by another name. | 1 paragraph |
| SP-22 | In Part III §4.4, reconcile unit-lapse 4D metric with cascade lapse N(4) = 3π/8 explicitly. | 1 paragraph |

### Tier C — Blind-test predictive rules (weeks, high-value)

Each of these either hardens the rule significantly or exposes a defect early. All are testable by computation.

| ID | Test | What it settles |
|---|---|---|
| SP-10 | Compute the Gram sum on paths [19,217], {3,5,6,7,19,217}, and any other plausible ρ_Λ path. Publish which gives the best closure and why. | Whether the -0.07% headline is robust or cherry-picked |
| SP-36 | Blind-test the source-selection rule against α_em(M_Z), m_W absolute, m_e/m_μ, CKM θ_13, θ_23 per Remark 4.9's "falsifiable prediction". Publish the blind predictions *before* checking them. | Whether the three-flag rule is genuinely predictive or trained on the 7-observable set |
| SP-17 | Compute CHSH on alternative bipartitions of ℂ⁴. Expected: Tsirelson bound gives 2√2 for any maximally-entangled bipartition. If it does, the CHSH result is robust; soft spot downgrades to Minor. | Whether the bipartition choice in Part II §10.3 is cosmetic or structural |
| SP-33 | Apply the articulated rule from Tier B consistently to α_s, α_em, and all cascade gauge couplings. Verify the numerical values survive. | Whether the obstruction-rule scope is coherent |

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
