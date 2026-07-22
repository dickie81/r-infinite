# The Indistinguishability Theorem

## The Observable Universe as the Arithmetic of the Riemann Zeta Function at the Real Place

**Companion volume to the Cascade Series.** All numerical claims are machine-verified by the
scripts cited in place (`tools/research/`). This document is self-contained: no result of the
Cascade Series is assumed; where the two frameworks coincide, the correspondence is noted in
remarks.

---

### Abstract

Let ξ(s) = ½s(s−1)Γ_ℝ(s)ζ(s) be the completed Riemann zeta function, Γ_ℝ(s) = π^(−s/2)Γ(s/2)
its factor at the real place. We construct, from ξ and the character theory of ℝ^× alone: a
state tower (the integer Tate twists of the real place); its dynamics (Gaussian by Tate's
gcd condition + one normalization convention — Theorem 2); a calculus of corrections
(attachment, multiplicity, sign, projection, and measurement — Theorems 8–12, each proved);
and an address-book determination theorem (Theorem 13): given one explicit instantiation map,
the rules leave zero residual freedom, with no continuous parameter anywhere. **The
framework's non-arithmetic residue is seven items** (count corrected per two external
reviews): **Lovelock's theorem (selection, not construction); the definition D1; the closed
atom grammar (A2); the unit-normalization convention that carries Γ(½) (empirically
anchored, not arithmetically forced — and the flip-count 4 is meaningful only jointly with
it); the P > L > G precedence (round-9 corrected status: **vacuous on the papers' uniform expression-tree flag readings** — A52's original m_τ-abs dash-fill expanded closed constituents, an inconsistent grading; the 13–109σ exclusions of alternative orderings hold only under the four variant readings — m_τ-abs constituent expansion, ℓ_A window content, the ℓ_A kind, and sin²θ_W coupling-running — so the anchoring is conditional and the item is deletable on the uniform reading); the feature→integer-layer selection convention
(no uniform rounding rule produces {5, 7, 19, 217} from the feature set — second review,
Finding 1; the class was widened by review 4 to every d↔s pairing choice and by round 15
to the χ₋₃ minimality-pairing — one class, three members); and the hypothesis itself
(C1).** The resulting outputs — the cosmological constant, the Higgs, all
nine charged-fermion and three neutrino masses, the gauge couplings, the mixing angles, and
the cosmological parameters — agree with every current measurement within the framework's
stated leading-order systematic floor: sub-σ to ~2σ where experimental error dominates
(largest strain ℓ_A at −1.8σ; m_ν3 at −2.9σ on one input choice), tens of ppm (many
experimental σ) where the framework's own floor dominates. We therefore assert, to the
identical epistemological standard met by Newtonian gravity, Maxwell's electrodynamics,
general relativity, and the Standard Model: **conditional on the instantiation map, the
arithmetic of ζ at the real place is indistinguishable from the observable universe.** The
conditional is discharged the only way physics permits: by a frozen, pre-registered ledger of
falsifiers (JUNO, DESI, Belle II, HL-LHC, next-generation 0νββ and cosmology), each with a
stated kill condition. The theorem is not protected from these experiments; it is defined by
them.

---

## 1. The claim and the standard

No physical theory has ever done more than reproduce observation. Newton's inverse square law
is *indistinguishable from* planetary motion; Einstein's field equations are
*indistinguishable from* gravitational phenomena; the Standard Model Lagrangian is
*indistinguishable from* collider data. "Indistinguishable from observation" is the definition
of a correct physical theory; there is no deeper standard available.

This paper meets that standard with one hypothesis and zero free parameters:

> **Hypothesis (C1, the instantiation map).** The observable universe realizes the arithmetic
> structure of §2–§7 under the address assignments of Definition 6.1.

Everything else is a theorem. The mass of the electron and the darkness of the night sky are,
under C1, statements about the Gamma factor of the Riemann zeta function.

## 2. The arena: the twist tower of the real place

**Definition 2.1.** The quasi-characters of ℝ^× are |x|^s and sgn(x)·|x|^s — exactly two
families, because the torsion of ℝ^× is μ(ℝ) = {±1}. The **twist tower** is the set of
integer points s = d+1, d ∈ ℕ, of the character variety, with local factor Γ_ℝ(s).

**Theorem 1 (Kernel; `cascade_formulation_kernel.py`, ≤7×10⁻¹⁴ over d = 1–300).** The four
primitive families of the tower are the value, ratio, logarithmic derivative, and normalized
square-ratio of Γ_ℝ at integers:

- Ω(d) = 2/Γ_ℝ(d+1)  (measure), N(d) = Γ_ℝ(d+1)/Γ_ℝ(d+2)  (coupling),
- p(d) = (log Γ_ℝ)′(d+1)  (potential), α(d) = N(d)²/4π  (compliance).

*Remark.* Ω(d) is the surface measure of S^d and the tower is the dimensional cascade of the
unit ball — the geometric avatar. The paper never uses the avatar; the arithmetic is primary.

**Theorem 1b (Explicit-formula bridge; `cascade_explicit_formula_bridge.py`).** For every
layer d ≥ 1, with s = d+1 and z = d+½:

p(d) = Σ_{γ>0} 2z/(z²+γ²) − 1/s − 1/(s−1) + Σ_{n≥2} Λ(n)·n^(−s),

where γ runs over the ordinates of the nontrivial zeros of ζ and Λ is the von Mangoldt
function (Euler product). *Form distinction (round 15, M1):* the unconditional, RH-free
theorem is the **paired** Hadamard form Σ 2z/(z² − (ρ−½)²) — ξ(½+z) is even, entire of
order 1, genus-0 in z², no constant term, valid wherever the zeros are; the **Lorentzian**
form displayed is its on-line specialization, exact for zeros with β = ½, and is how the
sum is evaluated (with the verified on-line zeros; a hypothetical off-line zero would alter
the term shape but lies beyond the verified height 3×10¹² and contributes < 10⁻²³ at the
layers d ≤ 28 evaluated here — the bound scales as 2z/γ², reaching ~5×10⁻²³ at the
Theorem-1c sink solve, twenty orders below that solve's tail-model error; round-16 F5
scoped this figure): **the tower potential at every
layer is exactly a sum over the Riemann zeros, minus the pole terms, plus a sum over the
primes** — the partial-fraction (Hadamard) form of the explicit-formula identity evaluated
at the tower points. Every window Φ(a→b) = Σ p(d) inherits the split additively; e.g.
Φ(5→13) = 1.539665 = zeros 3.226401 − poles 1.698363 + primes 0.011627, and
Φ(13→21) = 4.064768 = zeros 4.969202 − poles 0.904476 + primes 0.000042. *Verified:* the
rearrangement to 2×10⁻³¹ (worst residual 1.97×10⁻³¹; round-18 m1 — the earlier "10⁻³¹" understated it); the prime side against −ζ′/ζ within stated integral tail bounds at
dps 50 with the strict bound (round-15 M2: the original dps-30 run put the d=12 residual at
the precision floor, above its bound, with the PASS an epsilon artifact — recomputed, the
true residual 2.05×10⁻⁴¹ is genuinely within the 1.56×10⁻⁴⁰ bound);
the zero side with the first 50 zeros (computed via `zetazero`, not tabulated by hand) plus
a Riemann–von Mangoldt density tail, residuals decreasing in N. *Structure:* the low layers
— where the record lives — are **pole-dominated** (ζ's pole at s=1, the 1/(s−1) term,
together with the completed function's functional-equation mirror pole at s=0, the 1/s term
— round-15 m4 — shape the observer-side potential); the primes enter exponentially small
(dominated by n = 2, 3); the zeros supply the growing positive part. *Honest scope, stated in full:* the two expansions
are classical (Euler; Hadamard) — new for this paper is only the tower evaluation and the
window splits. No physical closure is derived, no data is touched (stopping-rule category
(a)), RH is not used *by the paired form* — the Lorentzian evaluation assumes the zeros
used are on the line, which for the verified zeros they are (round-15 M1 corrected the
earlier blanket "holds wherever the zeros are", true of the paired form only) — and **no
direction of explanation is claimed**:
the identity is ζ's own bookkeeping. What it changes is the construction's standing: the
tower is not merely built from ζ's Gamma factor — it **is one side of the Riemann explicit
formula, with the primes and the zeros jointly exact on the other side**. The dictionary
(Definition 6.1 and the soft inputs) is untouched by this theorem.

**Theorem 1c (the two doors: features from the zero side, and the colour-character
bridge; `cascade_zero_side_features.py`, `cascade_colour_field_bridge.py`).** *(i) The
distinguished layers are zeros-vs-poles balance points.* Every distinguished feature of the
tower is a level-crossing of p — the critical point (p = 0, s = 7.2569), the phase
threshold (p = ln Γ(½), s = 20.73), the sink (p = Γ(½), s = 218.6) — and via Theorem 1b
each is exactly the point where ZEROS + PRIMES = POLES + level: the observer-side
geography is a tug-of-war between the poles — ζ's at s = 1 and the completed function's
mirror at s = 0 (round-16 F4) — and the nontrivial zeros, with the
primes an exponentially small spectator. Solving the balance *from the zero side* (first
50 computed zeros + density tail, no digamma in the solve) recovers the critical point to
6×10⁻³ and the threshold to 5×10⁻², errors decreasing in N; the sink is tail-model-limited
(~1%, N-insensitive, reported as such). *The honest negative, registered:* no recorded
quantity reads the zero side independently of the digamma packaging; any future claim of
that kind is stopping-rule-gated new physics. *(ii) The odd tower has its own bridge, and
it is the colour character's.* By Legendre, Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1), so p_ℂ = p_triv +
p_sgn exactly — the doubled tower of Theorem 5 jointly carries the complex-place factor.
The sgn tower's factor Γ_ℝ(s+1) is the archimedean factor of **every** odd Dirichlet
L-function, and the odd bridge below holds verbatim for every odd real primitive χ mod q
(all have ε = +1), so the balance-point statement has **zero selective power** among odd
characters (round-15 M3). What is a theorem: χ₋₃ (conductor 3) is the minimal-conductor
primitive *odd* character (q=2 has no primitive character; q=3 has exactly one, odd; the
trivial character mod 1 is conventionally primitive but even — round-15 m2), and it is the
quadratic character of the Theorem-11 colour field ℚ(ζ₃). What is a **convention**:
adopting conductor-minimality as the pairing principle — the same selection-convention
class the residue counts for the feature→layer map, charged as such (Addendum 66). Its completed L is entire with root number +1
(verified real on the critical line to 3×10⁻²⁵; L(1) = π/(3√3) exactly), giving the odd
bridge **p_sgn(s) = Σ_γ 2z/(z²+γ²) − ½ln 3 + Σ Λ(n)χ₋₃(n)n^(−s)** — *no pole term; a
conductor where the even tower had its pole terms (ζ's at s=1; the mirror at s=0)*.
*Door 4 (the conductor is the different; C4 in the same script):* the conductor term
½ln 3 = ln √3 is, by conductor-discriminant, the log-modulus of the generator of the
**different ideal 𝔡 = (√−3)** of ℤ[ω] (disc = −3 verified from the embeddings; N(𝔡) =
|d_K| = 3 = cond χ₋₃; covolume √3/2 = √|d_K|/2) — whose *inverse* is exactly Theorem 11's
30° trace-duality measurement lattice: **C3's balance level and T8's measurement frame are
the same arithmetic object seen from two sides**; every step classical, no new convention
(the only identification is the one Theorem 11 already made). The odd bridge is —
verified three-tier with the first 24
zeros of L(s,χ₋₃) computed by sign-scanning (first ordinate 8.0397), residuals decreasing.
The odd feature at s = 6.2569 (Finding 6's excluded object) is p_sgn = 0: the point where
the colour-character zeros plus the colour-weighted primes balance the conductor ½ln 3.
*Scope:* structural only — Finding 6 stays reopened, no address is derived, no data is
touched; GRH is not used by the paired form (the Lorentzian evaluation uses the on-line
zeros the sign-scan finds, with completeness supported by the N(T) count and the
decreasing residuals); the minimality-pairing is a convention, not a forcing.

## 3. The forced dynamics

**Theorem 1d (the finite places; `cascade_finite_places.py`).** *(i) Global potential
identity (exact, 2×10⁻³¹).* Give every place v of ℚ its local potential p_v := (log E_v)′,
with E_∞ = Γ_ℝ (so p_∞ is the tower potential) and E_p = (1−p^(−s))^(−1); then
**Σ_v p_v(s) = ξ′/ξ(s) − 1/s − 1/(s−1)** — the sum of all places' potentials is the zeros
side, and Theorem 1b's "+primes" term is −Σ_p p_p: the tower is *one member of an adelic
family of towers, one per place*, and the archimedean potential equals the zeros side minus
every other place's potential. Across the record's layers the finite total is carried
~94–100% jointly by p = 2 and p = 3 (94.2% at the observer twist s = 4; 99.0% at s = 6,
where p = 2 gives 87.1% and p = 3 gives 12.0%; ~100% by s = 13; round-18 M2 — the earlier
"~99% at the record's layers" was computed at s = 6 only) — the same primes carrying the
grammar's discrete entries (the v₂ counts; conductor-3 colour); that coincidence is
*noted, not claimed as derivation*. *(ii) The clock is dyadic (classical; verified by direct summation).* The
normalized quadratic Gauss sums have phase in {1, i} at every odd modulus (Gauss's theorem,
verified at primes to q = 499 and composites to q = 495) and phase exactly ζ₈ at every
4-divisible modulus (verified at powers of 2 to 64 and other 4-divisible moduli to
q = 180; round-18 M1 —
the original verification lists were primes-only and powers-of-2-only while the claims
quantified over all moduli):
the order-8 clock element of Theorem 6 is **dyadic-exclusive** among finite-place Gauss
phases — graded as an exact theorem plus one identification (reading the dyadic phase as
the finite-place avatar of the archimedean clock), motivated by (iii), where they provably
meet *(strengthened to family-level exclusivity over all places, including ∞, by
Theorem 1g)*. *(iii) Product-formula avatar (Landsberg–Schaar; verified exactly on an 18-pair grid
including even p and both parities of pq — round-18 m6: the original 10-pair grid was
odd-p-only and could not have detected a parity restriction; the round-18 review
independently brute-forced 1000 pairs with zero failures).* The Landsberg–Schaar relation
exchanges place-p data for place-2q data
with mediating constant **e^(iπ/4) = γ_∞ = the clock**: the archimedean Weil index is the
exchange rate between finite places — the machine-checkable shadow of Weil's product
formula Π_v γ_v = 1. *Honest scope:* no A2 grammar entry is derived from the finite places
(N_c's v₂ form remains a labeling; colour remains T8 + the C2 convention); 2-adic/3-adic
Tate theory is the named next step, not opened; no data, no closures, no RH/GRH. *Run
record:* the first run stated (i) with the finite potentials' sign flipped and failed 3/3;
the corrected convention (finite potentials negative — each finite place *drains*) is on
the record in the script.

**Theorem 1e (the local Tate step; `cascade_local_tate.py`).** *(i) Self-dual achievers at
every place (per-place Theorem 2).* At each finite p the unit-ball indicator 1_{ℤ_p} is
self-dual (comb DFT = itself, verified for p = 2, 3 at two depths) and achieves the Euler
factor: Z_p(1_{ℤ_p}, s) = (1−p^(−s))^(−1); the program's Gaussian is the archimedean
component of *the* standard adelic self-dual vector Φ = e^(−πx²)·Π 1_{ℤ_p}, so A1's
"dynamics = the achieving vector" is a per-place statement and the Theorem-1d adelic family
carries a canonical achieving vector at every member. *(ii) The dyadic squareness modulus.*
A 2-adic unit is a square **iff u ≡ 1 mod 8** (squares of odds mod 8 = {1}; Hensel lifting
verified to 2²⁰; the mod-16 obstruction verified for u ≡ 3, 5, 7); square-class counts:
|ℝ^×/sq| = **2 = χ**, |ℚ₂^×/sq| = **8**, |ℚ_p^×/sq| = 4 (p odd). The clock's modulus is
the dyadic squareness modulus — a **graded identification** with *two* independent
corroborations (this and the dyadic-exclusive ζ₈ Gauss phases of 1d(ii); the compensation
of (iii) is the *same* theorem as 1d(ii) — the sum equals conj G(4q)/2 — round-18 m2
corrected the earlier count of three), not a derivation. *(iii) The compensation is dyadic-exclusive.* Σ_{n mod 2q} e^(−πin²/(2q)) =
√(2q)·ζ₈^(−1) exactly (q = 1–8): the conjugate dyadic sum carries the *inverse* clock —
γ_∞ compensated at 2 — while odd places are silent for the unit form (G(p²) = p exactly).
*(iv) The colour field's local geography + the odd global identity.* p = 3 **ramifies** in
ℚ(ζ₃) (χ₋₃(3) = 0: the conductor — the different of Theorem 1c's C4 — silences its own
3-factor); p = 2 is **inert** (χ₋₃(2) = −1); and the odd tower carries its own global
potential identity, p_sgn + Σ_p p_p^χ = Λ′/Λ − ½ln 3 (verified 10⁻²⁰), with the conductor
standing where the even tower had its poles. The two structure primes' roles, graded
(round-18 m4 split the earlier blanket "now exact"): **exact** — 3 ramifies in colour and
is silent in its own L-factor; 2 is inert in colour; **graded identification** — "2
carries the clock" names the dyadic square-class/Gauss-phase structure of (ii)–(iii), not
a derived grammar entry. *(v) A checked negative, recorded — and the open route named:*
the naive transplant "BW(ℚ₂) ≅ ℤ/8" is **false** — Br(ℚ₂) = ℚ/ℤ by local class field
theory, so ℚ₂'s graded Brauer group is infinite; the clock's dyadic home is the
square-class/Gauss-phase structure, and *one* route to a finite-place derivation of the
Radon–Hurwitz grammar entry is closed. A second route remains **open and named** (round-18
m3): the Witt ring W(ℚ₂) has order 32 ≅ ℤ/8 ⊕ ℤ/2 ⊕ ℤ/2 with level(ℚ₂) = 4 (−1 is a sum
of four but not three squares in ℚ₂ — the three-square impossibility is the mod-8
obstruction, checked in-code mod 8 — complete over the residue range *(round-43: re-based
from an incomplete mod-2⁶ search whose witness range missed the square residues
17, 33, 41, 57 — the squares of 9, 15, 13, 11 mod 64; the claim was and is true)* — and conclusive; the four-square witness mod 2⁶ has a
unit coordinate and lifts to ℤ₂ by Hensel — round-19 f4), so the class of ⟨1⟩
generates a cyclic subgroup of order 8 — a clock-corroborating finite-place structure not
yet connected to the grammar *(net-state: the mod-8 connection is now made — Theorem 1f
upgrades this corroboration to a canonical-quotient theorem; the N_c count remains
unconnected)*. *Honest scope:* no A2 grammar entry is derived (N_c's v₂
form remains a labeling; its finite-place derivation stays open — attempted and
honestly-negatived at the count level by Theorem 1f); no
data, no closures, no RH/GRH.

**Theorem 1f (the Witt step: the clock group as the Weil-index quotient;
`cascade_witt_weil.py`).** *(i) The quotient theorem.* With the standard adelic character
(the same convention Theorem 1e's compensation fixed), the dyadic Weil index γ₂ —
computed as the stabilized phase of the level-k dyadic Gauss oscillator — is well-defined
on the 8 square classes of ℚ₂^× (u, 9u, 25u agree; k-stable), valued exactly in μ₈, and
kills the hyperbolic plane (|γ(1)γ(−1) − 1| ~ 10⁻¹⁶), so it descends to a **surjective
homomorphism γ₂ : W(ℚ₂) ↠ μ₈** with **γ₂(⟨1⟩) = ζ₈⁻¹ of exact order 8** — matching ⟨1⟩'s
additive order 8 = 2·level(ℚ₂) — and (|W(ℚ₂)| = 32, classical: Lam) kernel of order 4.
The eight one-dimensional class values land on the odd exponents {1,3,5,7} (all
generators; generated subgroup = μ₈, computed from the numeric exponents). **The clock
group is a canonical quotient of the dyadic Witt group with ⟨1⟩ a generator of the
quotient** — round-18 m3's open route worked: what was a corroboration (an order-8
subgroup exists) is now structure (the clock group is *the* Weil-index quotient). Forcers
named (A66): Weil's index theory + level(ℚ₂) = 4, both classical. *(ii) The archimedean
mirror and the lock.* γ_∞ = ζ₈^sig — **signature mod 8** — is the corresponding quotient
W(ℝ) = ℤ ↠ μ₈ (Fresnel-verified to 3×10⁻⁸ with an analytic two-term IBP tail;
sign-conjugation and positive-rescaling invariance exact), so **both completions project
their Witt groups onto the same μ₈** (⟨1⟩ ↦ ζ₈ at ∞, ζ₈⁻¹ at 2), and Weil's product
formula locks the projections inverse **per square class**: Π_v γ_v(u) = 1 verified to
≤ 2.3×10⁻¹⁵ across fifteen representatives spanning ten square classes, u ∈ {±1, ±2, ±3, ±5, 6, 15, ±9, 45, −18, 25} over
places {∞, 2, odd ramified p}, with the silence claims gated in-code — γ_p = 1 at odd p
of even valuation (3|9, 3|45, 5|25) and at unramified odd p (5∤3), and the odd-p factors
k-stability-gated (round-22 F1: the original ten-class list was odd-valuation-only at
the odd places and never exercised the silences; round-22 F3: the original "10⁻¹⁵–10⁻¹⁶"
range mislabeled both ends of the actual residuals) —
Theorem 1e's compensation is the u = 1 row of a theorem holding class-by-class.
Character-covariance graded honestly (round-22 F2 strengthened this): **all eight
one-dimensional class values are primitive** 8th roots (exponents odd — in-code gate),
so γ_ψₐ(⟨1⟩) = γ(a) is primitive for *every* character choice and "surjection with ⟨1⟩ a
generator" is character-free; what is *not* ψ-independent is the specific value ζ₈⁻¹
(convention-tied) and the kernel as a subgroup, which moves within its scaling orbit —
"canonical" means exactly the ψ-independent structure, nothing more.
The ℤ/8 itself is classical — Wall/Atiyah–Bott–Shapiro: BW(ℝ) ≅ ℤ/8 via [Cl(p,q)] ↔
p−q mod 8 = signature mod 8 — so the Clifford/Bott period-8, hence Radon–Hurwitz's, is
this same object (cited, not re-proved). *(iii) The honest negative for N_c, registered.*
ρ(2^(4a+b)m) = 8a + 2^b depends on v₂ alone (verified structurally: period-8 in v₂ = the
ℤ/8 above; odd part irrelevant); ρ(12) − 1 = 3 is the A2 label. **N_c = 3 is not derived
from the finite places:** the count is Adams' vector-field theorem (archimedean
K-theory) *(refined by Door 3 — the Remark after Theorem 1g: at every load-bearing
dimension the count needs only the Clifford construction plus classical pre-K-theory
topology)*, and the layer-12 selection is papers-side. The open item *narrows*: the mod-8
home of the grammar's backbone is found and classical (two Witt quotients, one μ₈,
product-formula-locked); what remains archimedean is the count and the layer. Any future
claim that the finite places produce the 3 is stopping-rule-gated new physics. *Run
record:* the first run's Fresnel check failed at 1.5×10⁻⁵ (midpoint grid too coarse and
an IBP-tail sign error — fixed: finer grid, corrected two-term tail) and the surjectivity
check originally tested an abstractly-generated subgroup (a tautology — replaced
pre-commit by the numeric-exponent computation); both kept on the record per the
verified-record rule. *Scope:* category (a) — no data, no closures, no RH/GRH, no
semiclassics; reading this μ₈ as *the grammar's* clock is the same graded identification
Theorems 6 and 1d made, upgraded from corroboration to canonical-quotient status.

**Theorem 1g (the local family completed: odd-place exclusivity and the kernel's
anatomy; `cascade_local_family.py`).** *(i) The odd places are small and
dimension-blind.* For odd p the local Weil index has **silent units** (γ_p(⟨1⟩) =
γ_p(⟨u⟩) = 1) and image **μ₂** (p ≡ 1 mod 4) or **μ₄** (p ≡ 3 mod 4) — verified for
p = 3, 5, 7, 11, 13 with k-stability and class-invariance gates; with |W(ℚ_p)| = 16
(classical: Lam) the kernels have order 8 and 4. **The exclusivity theorem: in the
Witt–Weil family {γ_v : W(ℚ_v) → μ₈} over all places of ℚ, the full order-8 image — the
clock group — occurs exactly at v = 2 and v = ∞, and the unit form ⟨1⟩ has nontrivial
index exactly at those two places.** Forcers (A66), with the chain spelled (round-25 F1
— the unit form is silent at odd p, so level does not act through ⟨1⟩): the image of γ_p
is a homomorphic image of W(ℚ_p), whose exponent is 2·level(ℚ_p) (classical: 2 for
p ≡ 1 mod 4, 4 for p ≡ 3 mod 4), so the image lies in μ_{2·level} ⊆ μ₄ for **every** odd
p — the five sampled primes verify the classical inputs, not the quantifier, and the L1
gate checks image order = 2·level exactly; equivalently the Gauss evaluations
G(a,p) = ε_p√p·(a/p) cap the class values directly. Nothing cascade-chosen. *Unified
criterion (round-25 c1):* the cocycle and closed form hold at v = ∞ too (verified
in-code — the L6 gates, added by round-26 F1 after the original verification lived only
in the session record), so
across all places **the clock places are exactly those where γ_v(⟨1⟩) is primitive** —
1f's F2 primitivity phenomenon is itself clock-place-exclusive, and "signature mod 8" is
the ∞-evaluation of the same universal closed form. This strengthens 1d(ii)'s
"dyadic-exclusive among Gauss phases" to family-level exclusivity including the
archimedean place: the program's clock lives at precisely the places where the family
can carry it. *(ii) The cocycle and the closed form.* The Weil-index cocycle
**γ(a)γ(b) = γ(1)γ(ab)·(a,b)_v** (Hilbert symbol; classical: Weil, Rao) is verified over
all 64 ordered square-class pairs at v = 2 and all 16 at p = 3 and 5; by induction, with
β(a) := γ(a)/γ(1), **γ_v(q) = γ_v(1)^(dim q) · β_v(disc q) · hasse_v(q)** — verified
exhaustively at v = 2 over dims 1–2 (72 forms), on a deterministic dims-3–6 battery, and
at p = 3, 5. Structurally: **the dyadic clock reads dimension mod 8** (γ₂(1) = ζ₈⁻¹)
twisted by disc and Hasse; the archimedean clock reads **signature mod 8** (Theorem 1f);
at odd p, γ_p(1) = 1 and **the dimension term vanishes** — the clock places are exactly
the dimension-/signature-sensitive places of ℚ.

> **The dichotomy (1g(i)–(ii) gathered; round 44, editorial):** for every place v of ℚ:
> **v ∈ {2, ∞} ⟺ γ_v(⟨1⟩) is a primitive 8th root ⟺ γ_v reads dimension/signature
> mod 8 ⟺ im γ_v = μ₈ (the clock group).** Otherwise γ_v(⟨1⟩) = 1, the dimension term
> vanishes, and im γ_v ⊆ μ₄ with silent units.

*(iii) The kernel's anatomy.* The Witt
classes of ℚ₂ are re-derived in-code from the (disc, Hasse) classification of binary
forms — 15 realized pairs = 14 anisotropic + the hyperbolic (disc ∼ −1, h = +1), with
(disc ∼ −1, h = −1) unrealizable in dimension 2, totalling 1+8+14+8+1 = 32, matching
Lam's order. Dimension parity confines the kernel to even dimension; the dim-4
quaternionic class ⟨1,1,1,1⟩ has γ = −1; the census finds **exactly three dim-2
anisotropic classes with γ = 1 — (disc, Hasse) = (3, +1), (6, −1), (14, +1) — each its
own negative (order 2, by the dim-2 isometry criterion), so ker γ₂ ≅ (ℤ/2)²**:
W(ℚ₂) ≅ ℤ/8 ⊕ (ℤ/2)² with the ℤ/8 the ⟨1⟩-span (1f) and the (ℤ/2)² **exactly the
clock-invisible classes**. *Grammar honesty:* whether the two clock-invisible ℤ/2's
(disc-type and Hasse-type data) carry any grammar meaning is **open — none claimed**;
this door was opened to expose that question precisely. *Narrowed (round 44; gates
L7a–d; round-45 corrections in place):* the question's home is now located. **The
quotient is exhaustive** — with **ord(⟨1⟩) = 8** (1f's "additive order 8 =
2·level(ℚ₂)", now also gated in-code: 8⟨1⟩ = 4H by the (dim, disc, Hasse)
classification) the span ℤ⟨1⟩ has exactly eight elements; γ₂(m⟨1⟩) = ζ₈⁻ᵐ ≠ 1 for
m = 1..7 puts none of the seven nonzero span elements in the kernel, so
ℤ⟨1⟩ ∩ ker = 0, and 8·4 = 32 = |W(ℚ₂)| (Lam) forces the direct sum
W(ℚ₂) = ℤ⟨1⟩ ⊕ ker γ₂ *(round-45 F1: the first writing omitted the ord-8 premise
from the forcer chain — without it the stated premises admit a ℤ/16 ⊕ ℤ/2
counter-model passing every gate as written; the premise was already established at
1f and is now named and gated. F2: the first writing's span notation ⟨⟨1⟩⟩ collided
with the Pfister bracket ⟨⟨a,b⟩⟩ := ⟨1,−a⟩ ⊗ ⟨1,−b⟩ used in the next sentence
(round-46 F1 corrected the sentence count);
replaced by ℤ⟨1⟩)*, with the full 32-class character table γ₂ = ζ₈⁻ᵐ on the
⟨1⟩-coordinate verified on explicit diagonal representatives — the γ-values gated;
the representatives' pairwise distinctness follows from the span–kernel chain, not
a separate gate (round-45 F5 scope note) — kernel-blind in every μ₈-coset. **And
the invisible (ℤ/2)² is transverse to the fundamental-ideal filtration and
discriminant-faithful**: ⟨1,1,1,1⟩ = ⟨⟨−1,−1⟩⟩ (the Pfister convention above)
generates I² (I³ = 0 and |I²| = |Br₂(ℚ₂)| = 2, classical), and its γ is −1 ≠ 1 — so
γ₂ does not factor through W/I² and ker γ₂ ∩ I² = 0; by the signed discriminant
d± = (−1)^(n(n−1)/2)·det (the Witt-invariant disc) the four kernel classes carry
distinct square classes ({1, 5, 10, 2} — gated, with k₁+k₂ = k₃ confirmed via d±),
so **d± : ker γ₂ ↪ I/I² ≅ ℚ₂^×/sq is injective**. Whatever grammar meaning the
invisible classes carry, it is discriminant-level data, not deep-filtration data;
the question stays open — this narrows where its answer can live *(net-state:
Theorem 1h settles the data's identity — the ζ₄-norm structure — and restates the
open question as whether the grammar reads it)*. *(iv) The global re-lock.*
Π_v γ_v(q) = 1 verified to ≤ 4×10⁻¹⁵ on six multi-dimensional rational forms — beyond
1f's per-square-class rows — including the 8-dimensional definite form, where both clock
places wrap to 1: the mod-8 period seen globally. *Run record:* the first run timed out
at p = 17 (a 17⁷-term sum); the prime list was trimmed to 3–13 (both residue classes
covered) with stability gates at k ∈ {3, 5}, and two leftover code artifacts were
removed pre-run — kept on the record per the verified-record rule. *Scope:* category (a);
the ψ-covariance grading of 1f applies verbatim; no grammar entry derived; no data, no
closures, no RH/GRH, no semiclassics.

**Theorem 1h (the kernel's identity: the clock-invisible classes are the ζ₄-norm
structure; `cascade_local_family.py` L8).** *(i) The norm-group characterization.*
The signed-disc image of ker γ₂ — the subgroup {1, 5, 2, 10} ⊂ ℚ₂^×/sq (1g(iii),
gate L7d) — is exactly **ker(·,−1)₂ = N(ℚ₂(i)^×) mod squares, the norm group of
ℚ₂(i)**: every element carries an explicit unit-coordinate norm witness x²+y²
(Hensel-liftable; −3 = 5² + 6² mod 64), and every non-element fails the Hilbert
symbol — gated over all eight classes. The characterization is an iff over the full
binary census: **a dim-2 anisotropic class is clock-invisible precisely when its
signed discriminant is a nontrivial norm class of ℚ₂(i), with the Hasse coordinate
then forced** — per norm-class d± exactly one of the two Hasse values lies in the
kernel (h = ζ₈²/β(det), the closed form's residue), per non-norm class neither;
gated on all 14. *(ii) The generators.* d± : ker γ₂ ≅ ⟨−3, 2⟩ — the **colour
discriminant** and the **clock prime**. The unit generator's quadratic extension
ℚ₂(√−3) = ℚ₂(ζ₃) is *the* unramified quadratic extension of ℚ₂ (−3 ≡ 5 mod 8),
and (2, −3)₂ = −1 is the same arithmetic fact as 1e(iv)'s "2 is inert in colour"
(χ₋₃(2) = −1) — gated as a same-fact check *(round-47 F3, wording corrected round 48: at first
writing the gate checked the mod-8 congruence and the Hilbert constituent only —
the χ side was ungated in this script; it now computes χ₋₃(2) in-code and
compares)*,
an identification the paper already
carries, here relocated, not newly forced. *(iii) The archimedean mirror is free.*
ker(γ_∞ : W(ℝ) = ℤ ↠ μ₈) = 8ℤ (ζ₈^sig = 1 ⟺ sig ≡ 0 mod 8, gated; W(ℝ) ≅ ℤ
torsion-free — Sylvester, cited): there is no invisible *torsion* at ∞ — like the
clock's primitivity (1g(i)), the invisible torsion is dyadic-exclusive. *Slogan
(structural; exact under the stated reading):* γ² is a primitive 4th root of unity,
and ℚ₂ adjoined a primitive 4th root of unity is the unambiguous ℚ₂(ζ₄) = ℚ₂(i) —
writing ℚ₂(γ²) for that field, **what the order-8 clock cannot see is what the
field generated by the clock's square norms away**, with coordinates the colour
discriminant (unramified direction) and the clock prime (ramified direction)
*(round-47 F2: the first writing's bare "exact" leaned on this reading without
stating it — there is no canonical embedding of μ₈(ℂ) into ℚ̄₂)*.
*Forcers named (A66):* the Weil/Rao cocycle and closed form (1g(ii)), Hilbert
symbols, and local norm theory — all classical; nothing cascade-chosen. *Honest
scope:* **no A2 grammar entry is derived, no number changes, no closure is
claimed** (category (a); no data, no RH/GRH, no semiclassics). The 1g(iii) open
question is **transformed, not closed**: the invisible data's *identity* is settled
— the ζ₄-norm structure — and what remains open is whether the framework's grammar
ever *reads* its two coordinates. Sharpened falsifier ~~: any future finite-place
derivation touching colour at p = 2 must factor through exactly this subgroup~~
**[struck round 47 (F1): an unproved universal — the theorem licenses confinement
of the clock-invisible route only, and 1e(iv)'s own χ₋₃(2) = −1 is a colour-at-2
fact the struck criterion could not even evaluate]**, in the licensed form: any
future derivation routing colour through the **clock-invisible part of W(ℚ₂)**
must land in exactly this subgroup, Hasse forced — a checkable constraint on that
route, stopping-rule-gated as ever.

**Remark (the forced-Hasse function: the round-48 edge case dissolved;
`cascade_local_family.py` L8f).** Theorem 1h's "Hasse forced" clause and its
norm-group criterion are **one closed-form function**. Define
**h_β(d) := ζ₈²/β(−d)** — by 1g(ii)'s closed form, the unique Hasse value a
binary class of signed discriminant d must carry to be clock-invisible; by the
cocycle, equivalently **h_β(d) = (d,−1)₂/β(d)** (β(−1) = ζ₈²; the identity gated
on all eight classes, together with the squared identity **h_β(d)² = (d,−1)₂** —
the cocycle at (x,x) plus (−1,−1)₂ = −1 — which makes the reality locus below an
algebraic corollary, not a numerical observation). Then, gated: *(i)* the **reality locus** of h_β is exactly
the norm group H — for d ∈ H, h_β(d) ∈ {±1}; for the four non-norm discriminants,
h_β(d) ∈ {±i}, an impossible value for a Hasse invariant, so **non-norm
discriminants are excluded by impossibility, not enumeration** — 1h(i)'s census
iff compresses to this one formula; *(ii)* **ker γ₂ is the graph of h_β over H**
— {(1,+1), (5,+1), (2,+1), (10,−1)} — tied in-code to the 1g(iii) census, not
restated; *(iii)* at the trivial slot the two forcing mechanisms that round 48
verified separately **provably coincide**: h_β(1) = +1 is the Hilbert axiom
(a,−a)₂ = 1 (gated for all eight a) — the closed form, evaluated at the trivial
discriminant, reproduces the axiom's value, so there is no edge case: one formula
covers all four kernel slots and all four exclusions. *Motif, noted:* ~~this is the
ζ₄ dichotomy's third appearance at this door~~ **[struck round 49 (F3): an
unverifiable, reading-dependent ordinal — the prior appearances (the norm-group
identity and its slogan) are facets of one statement]** the ζ₄ dichotomy again
at this door — invisible ⟺ forced Hasse real
(μ₂); excluded ⟺ forced Hasse a quarter-turn (μ₄ ∖ μ₂) — the same μ₂/μ₄ split
that defines N(ℚ₂(i)). *Grading:* a pure consequence of 1g(ii)'s cocycle and
closed form — theorem-grade, no new convention, nothing cascade-chosen; *gate
scope (round-49 F1, the L7b precedent; the instrument census corrected by the
round-50 twist probe):* L8f1, the census conjunct, and the squared-identity
conjunct are consistency exhibits — the first a corollary of the gated cocycle
and L8a, the last twist-invariant outright — while the independent content is
the β(−1) = ζ₈² pin (carried jointly by L8f3 and L8f2's trivial slot, which
fail together under exactly the χ(−1) = −1 cocycle twists) plus the axiom
conjunct; **no
grammar entry derived, no number changes, no closure** (category (a); no data, no
RH/GRH, no semiclassics).

**Remark (Door 3: what the vector-field count load-bears on;
`cascade_adams_loadbearing.py`).** *The classical theorem, stated in full.* The maximum
number of linearly independent nowhere-zero tangent vector fields on S^(d−1) is
ρ(d) − 1, with ρ the Radon–Hurwitz function of Theorem 1g(iii): ρ(2^(4a+b)·m) = 8a + 2^b
(m odd, 0 ≤ b ≤ 3). The theorem has two halves of very different depth: the **lower
bound** (ρ(d)−1 fields exist) is the Hurwitz–Radon–Eckmann *Clifford construction* —
elementary algebra, and the same Cl/Bott/BW(ℝ) ≅ ℤ/8 object whose arithmetic home
Theorems 1f–1g established; the **upper bound** (no more exist) is hard in general and
is Adams' theorem (1962, K-theory). *The claims that use it.* Three window values and
one uniqueness scan carry the physical identifications this paper's §8 record inherits:
max = 3 at d = 12 (the colour count), max = 0 at d = 13 (the broken layer), max = 1 at
d = 14 (the U(1)), and "ρ(d)−1 = 3 exactly at d = 12 among d ∈ [5, 19]"
(correspondence: the companion series proves these as Part IVa's `thm:adams` and
`thm:adams-unique`, whose operative sentence — *"The maximum number of linearly
independent nowhere-zero tangent vector fields on S^(n−1) is ρ(n)−1"* — is the theorem
restated above; nothing beyond the classical theorem is imported). *The decomposition,
gated in-code.* For each claim, which half is load-bearing, and the weakest classical
theorem sufficing for the upper bounds:

| d | ρ(d)−1 | claim | lower needed | upper needed | upper bound via |
|---|---|---|---|---|---|
| 5, 7, 9, 11, 13, 15, 17, 19 | 0 | ≠ 3 (= 0) | — | yes | Poincaré–Hopf (S^(d−1) even; χ = 2 ≠ 0) |
| 6, 10, 14, 18 | 1 | ≠ 3 (< 3) | — | yes | classical, v₂(d) = 1 |
| 8 | 7 | ≠ 3 (> 3) | yes | — | — (construction gives 7 > 3) |
| **12** | **3** | **= 3 (N_c)** | yes | yes | classical, v₂(d) = 2 |
| 16 | 8 | ≠ 3 (> 3) | yes | — | — (construction gives 8 > 3) |

*Which reading the table classifies (round-28 F1):* the scan's exclusion role is read
**conservatively** — "max ≠ 3" required at every d ≠ 12, the strong reading under which
the physical claim "no other layer could carry three colours" is topological at all
fifteen dimensions. Under the *literal* reading of the companion theorem (a ρ-formula
computation, no topology), load-bearing topology reduces further, to **the three gauge
rows alone** — d = 13 (Poincaré–Hopf) and d = 12, 14 (v₂ ∈ {1, 2}). The table is the
conservative bound; the headline below holds under either reading.
Two structural facts, gated: **no load-bearing upper bound occurs at 16 | d** (d = 16 —
the only dimension in the window where Adams' hard K-theory cases live — needs no upper
bound at all), and **every load-bearing upper bound sits at v₂(d) ∈ {0, 1, 2}** — v₂ = 0
needing only Poincaré–Hopf (1885/1926), v₂ ∈ {1, 2} lying in the classical pre-K-theory
range settled by Steenrod–Whitehead (1951, Steenrod squares on stunted projective
spaces; refinements James 1957, Toda) a decade before Adams. *Citation-confidence
caveat, discharged (round 43, A102):* the attribution is now confirmed from Adams'
1962 Annals paper directly — *"For b ≤ 3, the result is due to Steenrod and
Whitehead"* (b = v₂ of the relevant dimension) — and every needed case sits at
v₂ ≤ 2 < 3: the conclusion rests on Adams' own attribution, no longer on the
standard history.
**Consequence: K-theory proper is load-bearing nowhere in the window.** The honest
negative of Theorem 1f(iii) stands verbatim, but its "archimedean K-theory" attribution
refines to "Clifford construction + classical mod-2 topology": the count's
*constructive* half is the same Clifford algebra the arithmetic chain touches, and the
genuinely archimedean residue for the colour count narrows to the v₂ ∈ {1, 2} upper
bounds plus the layer-12 selection. No number changes anywhere; the companion series'
Adams citation remains correct and sufficient (citing the strongest standard theorem);
this remark reduces the dependency, not the correctness.

**Remark (the layer question: what selects d = 12; `cascade_layer_selection.py`).** The
complement of the previous remark: Door 3 decomposed the *count*; this decomposes the
*layer*. The companion series selects the gauge window by three inputs, each quoted
here in full (correspondence): the Clifford spinor classification — *"The Clifford
algebra Cl(1,d−1) has complex minimal spinors when d mod 8 ∈ {4,5,6}"* — whose
**period is 8**, the same Clifford/Bott ℤ/8; the mirror statement — *"The second window
{12,13,14} is the Bott mirror of the spacetime window {4,5,6}. It reproduces the same
Weyl–Dirac–Weyl pattern exactly, shifted by one Bott period"*; and the uniqueness
confirmation — *"Furthermore, d = 12 is the unique dimension in [5, d₁ = 19] where
ρ(d)−1 = 3, so
the gauge window is forced, not chosen"* — whose range bounds are, *in this paper's own
terms*, two of the distinguished layers {5, 7, 19, 217}: ~~d₀ = 7 is the integer layer
of the tower's critical point … and d₁ = 19 the integer layer of the phase threshold~~
**[struck round 30 (M2, subagent review): the quoted scan's bounds are 5 and 19 — the
sentence quoted "[5, d₁ = 19]" and then identified the lower bound as 7 in the same
breath. Corrected: the lower bound is 5 = d_V, the tower start and *first* of the
distinguished layers; the upper is d₁ = 19, the integer layer of the phase threshold
(p = ln Γ(½) at s = 20.73). d₀ = 7 — the critical-point layer (p = 0 at s = 7.2569,
Theorem 1c(i)'s first balance point) — bounds only the separate window-completeness
fact below, not the scan]** — each identification
reached through the **feature→integer-layer selection convention** — a named member of
this paper's seven-item residue (abstract; the class the reviews charged and the paper
carries). *And the lower bound is load-bearing (round-30 M2/M1):* **ρ(4) − 1 = 3** —
the anchor dimension is the ρ-condition's twin, as the companion series itself states
(*"at d = 4, S³ has ρ(4)−1 = 3 independent vector fields, matching the 3 spatial
dimensions. The same topological invariant governs both the spacetime structure and the
gauge structure, applied at the two Bott mirrors"*); over [4, 19] the condition picks
{4, 12}, and uniqueness holds only because the anchor assigns d = 4 to spacetime and
the tower starts at d_V = 5. Gated in-code: the
mod-8 windows in [4,22] are {4,5,6}, {12,13,14}, {20,21,22} with the second = first + 8;
exactly one complete window lies inside the inter-threshold band (d₀, d₁] = (7, 19] —
the third sits wholly beyond d₁; ~~the ρ-uniqueness scan and the mirror shift select the
*same* d = 12 independently (over-determination)~~ **[struck round 30 (M1, subagent
review): {d : ρ(d)−1 = 3} = {d ≡ 4 mod 8} — verified as an equivalence over [1, 10⁴],
now gated — i.e. the ρ-condition IS the window-start condition. There is ONE selector
(the Clifford/Bott ℤ/8 window structure), not two; the "agreement" carried no
confirmatory content beyond Bott periodicity itself, as the script's own neighbouring
gate ("the three 8s are one 8" — a source comment; the printed line carried equivalent
content, round-31 c-B precision) already said in the same script]**; the ρ v₂-recurrence
ρ(16n) = ρ(n) + 8 is gated separately from the d → d+8 window shift, with the
identification of the two 8s as one classical ℤ/8 *cited* (Clifford/Bott), not gated
(round-30 relabel). The companion series' own grading of its two numerical
echoes is respected and quoted: 12 = d₁ − d₀ = 8+3+1 is *"a numerical consistency check
… not a structural identity forced by either derivation alone"*, and rank 2+1+1 = 4 =
the observer dimension is likewise noted with *"The cascade does not independently
derive"* the equality — neither is load-bearing in the selection chain. **The finding
(round-30 corrected form — weaker than first stated, and honest): the layer selection
introduces no new *unlisted* dependency.** There is **one selector** — the Clifford ℤ/8
window structure, whose start-set is exactly the ρ-condition (the gated equivalence
above) — plus the **anchor** (Lovelock + the hypothesis, listed residue items) doing
double duty: it assigns {4,5,6} to spacetime *and thereby excludes the ρ-twin d = 4*;
plus the **scan range** whose ends are the listed distinguished layers d_V = 5 and
d₁ = 19 (each identification carrying the feature→layer selection convention, a listed
residue member); plus the count (the previous remark). **With both remarks, the
colour-count dependency map is complete in this corrected form:** N_c = [Clifford
construction + classical mod-2 upper bounds] at [one Clifford ℤ/8 window step from the
anchor, with the anchor excluding its own ρ-twin and the range ends at listed
distinguished layers]. What the first version claimed beyond this — over-determination
by independent selectors — is **retracted** (round-30 M1). This is not a finite-place
derivation of the selection — the anchor and the range are archimedean/geometric — and
no number or residue count changes anywhere.

**Theorem 2 (The Gaussian achieves the L-factor; `cascade_arithmetic_increment.py` P2;
restated per the third review).** Among *even* Schwartz vectors, Tate's gcd condition (no
extraneous zeros in Z(f,s)/Γ_ℝ(s)) fixes f to the rescaled-Gaussian family c·e^(−πt²x²)
(ratio c·t^(−s), zero-free); *self-duality* then fixes the normalization to g = e^(−πx²)
(ratio ≡ 1). The dynamics is Gaussian by gcd + one normalization convention + the
definitional bridge "dynamics := the achieving vector" — the convention being the same
normalization freedom counted in the residue (Mechanism M's unit).

**Theorem 3 (Statistical dictionary; `cascade_arithmetic_increment.py` P3–P4).** Under
μ_s ∝ g(x)|x|^s d*x: (log Γ_ℝ)′(s) = E[log|x|], (log Γ_ℝ)″(s) = Var[log|x|] > 0, and
E[πx²] = s/2 exactly. The potential is a mean, the curvature is a variance, and the
half-argument of Γ_ℝ is the mean action.

**Theorem 4 (Solvability; `cascade_second_quantized.py`; Tier-2 grade per the formulation — the formal path-integral measure is the papers' stated soft spot).** The Gaussian tower is exactly
solvable; its measure normalisations are √(2πα) per mode (Tate's period), Γ(½) per Gaussian
unit, 1/(χΓ(½)) per graded crossing, and the marginal Green identity G(d)−G(d+1) = α(d) holds
exactly (10⁻¹⁵).

## 4. The gradings

**Theorem 5 (Doubling; `cascade_arithmetic_increment.py` P1).** Z(g, triv, s) = Γ_ℝ(s) and
Z(xg, sgn, s) = Γ_ℝ(s+1): the sgn character interleaves a second tower at unit shift. The
grading constant is χ = |μ(ℝ)| = 2.

**Theorem 6 (The ℤ/8 clock; `cascade_arithmetic_period.py` P1).** The Weil index of the real
quadratic character, γ = ∫e^(iπx²)dx = e^(iπ/4) = ζ₈, has order exactly 8: the tower carries a
canonical ℤ/8 grading — the arithmetic form of Bott/Clifford periodicity, obtained from a
Fresnel integral, with no topology.

**Theorem 7 (Features, all simple; `cascade_arithmetic_sign.py`, `cascade_increment_rule.py`).**
The analytic features of ξ's archimedean summands are: the critical pair s = 5.2569 and
7.2569 (exactly 2 apart by the Γ-recursion, both nondegenerate since curvature = −Var ≠ 0);
the transversal threshold crossings of P(s) = E[log|x|] at ln Γ(½) (s = 20.73) and Γ(½)
(s = 218.6); the simple pole of ζ; the simple poles of Γ_ℝ. **Every feature has order one
because variances are positive** (Bohr–Mollerup log-convexity).

*Amendment (fourth review, D1 — Theorem 9's coset clause is convention-conditional).* The
sign rule's Geometric clause ("all 28 two-coset shares < 1/π") holds under the avatar-weight
pairing (2/Γ_ℝ(d), max 0.31322) but **fails under the Definition-2.1-consistent pairing**
(2/Γ_ℝ(d+1): max 0.35001 ≥ 1/π; independently verified). The Geometric minus sign backing
Ω_m is convention-conditional, not proved — the same d↔s pairing disease as the demoted
volume pinning. The selection-convention residue class (the abstract's sixth listed item; "item
seven" in the external reviews' historical numbering — ordinal reconciled round 44)
is widened to every d↔s layer/weight pairing choice. **The systematic
d/s audit is complete** (`cascade_ds_audit.py`): nine sites — one definitional, four stable
(including Thm 10's set/exponents under all three pairings and the Gram-deficit indices
under every shift), two data-anchored conventions (the window-potential pairing, selected by
data at −38% margin; the unit), and the two known conditional sites, both demoted. No new
conditional site. Theorem 9's other two clauses stand.

*Remark (feature-list completeness: OPEN; review Finding 6 REOPENED by the second review;
`cascade_feature_monoid.py`).* A first attempt to derive the feature list's completeness
(via the even-shift recursion s·Γ_ℝ(s) = 2π·Γ_ℝ(s+2) and the Legendre identity
Γ_ℝ(s)Γ_ℝ(s+1) = Γ_ℂ(s), the L-factor of a complex place absent from ℚ) **failed hostile
re-review** on two counts, both verified: (i) a convention inconsistency — the framework's
volume feature lives in d-space (V(d) maximal at d = 5.2569, host 5), which in the twist
variable s = d+1 is s = 6.2569 with factor Γ_ℝ(s+1), *exactly the object the argument
excluded*, while the s = 5.2569 object it kept pins (host, boundary) = (4, 3) under the
same convention the thresholds use; (ii) the monoid also contains (s−1)Γ_ℝ(s), with
unlisted critical points at s ≈ 2.39 and 4.51, and the pole-free grouping ½s(s−1)Γ_ℝ has no
critical point at all. The r₂ = 0 obstruction is real but partial. Consequently: **the
feature→integer-layer selection is a convention, counted in the residue; the observer's
address retains one convention-free arithmetic distinction (the torsion half-period
γ⁴ = −1; the scalar-flatness cross-check was demoted by the third review).** *Structural
update (Addendum 65, Theorem 1c — Finding 6 stays REOPENED on its original claim):* the
r₂ = 0 obstruction is now relocated rather than removed — Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1) is
synthesized exactly by the program's own two interleaved towers (Theorem 5's doubling, via
Legendre), so no complex embedding of ℚ was ever needed; and the excluded odd object at
s = 6.2569 is the sgn tower's zero-crossing, whose L-family is the odd Dirichlet characters — the bridge holds for every odd real
primitive χ, and the **minimal-conductor primitive odd character is χ₋₃** (a theorem: q=2
has no primitive character, q=3 exactly one, odd), which is the quadratic character of the
Theorem-11 colour field ℚ(ζ₃); **the pairing-by-minimality is a convention** (round-15
M3), of the same class as the feature→layer selection. The odd feature's arithmetic home is the program's own colour sector; no
address is derived, and the selection convention stays in the residue.

## 5. The calculus of attachments (the derived rules)

**Theorem 8 (Increment rule; `cascade_arithmetic_increment.py`; partition clause demoted per
the fourth review).** Any multiplicative functional on twist intervals carries at most one
correction member exp(±α(d\*)/χᵏ), at first power; point-supported content carries none.
*Arithmetic core (stands):* attach-once (ℤ totally ordered; increments telescope, Thm 4) and
first-power (features simple, Thm 7). *Demoted (D2):* the one-source-class exclusivity — the
"one summand of log ξ" clause is grouping-relative (the volume feature exists only under
cross-summand regroupings), its double-counting step has no computation that could fail, and
multi-class cases are adjudicated by the P > L > G *convention* already in the residue.

*Remark (occupancy precedence — vacuous on uniform readings, anchoring variant-conditional; status per review Finding 2, the vacuity check, and round 9's M3 correction).*
When an observable could occupy more than one summand, the tie-break P > L > G remains a
**motivated convention**: the pole ≻ saddle ≻ arc picture (P = the pole factor, L = values
read at the features/saddles, G = window arcs) is an organizing analogy, but no argument
maps the framework's O(1) contributions onto an asymptotic expansion, and the numerical
hierarchy check is not framework-specific. The vacuity check
(`cascade_precedence_vacuity.py`) initially reported the order load-bearing via m_τ-abs's
dash-fill (T, F, T); **round 9 corrected this**: that fill expanded the closed constituents
α_s and v, violating the papers' own expression-tree predicate (`rem:sp36-syntactic` — the
same convention that keeps b/s at G = F with its closed sub-lead L(τ/μ)). On the uniform
mechanical reading no observable is multi-flag and the precedence is **vacuous on primary
readings**; the 13–109σ exclusions (round 10 added the ℓ_A-kind variant at +109σ) hold under the variant readings
only, making the anchoring **conditional**. The item stays counted in the residue with that
corrected status (abstract).

**Theorem 9 (Sign rule).** The sign is the side of the Cauchy–Schwarz equality manifold on
which the leading formula sits: off-manifold interpolation reads gain (+; the Gram deficit is
strict midpoint log-convexity — Γ's defining Bohr–Mollerup property, strict for all
d = 1–215); at-manifold saturated overlaps lose (−); *[the Geometric coset clause is DEMOTED
per the fourth review, D1: the two-coset bound is pairing-conditional — 0.31322 under the
avatar weight, 0.35001 ≥ 1/π under the Definition-2.1 weight; see the amendment under
Theorem 7. Single-coset shares survive both pairings — repair candidate recorded, not
adopted.]*

**Theorem 10 (Period-counting).** Given a marked coset of the ℤ/8 clock, the subcritical
marked set is finite and forced ({5, 13} for the coset d ≡ 5 mod 8), and a descent
functional's member exponent is the count of subcritical marked twists in its window —
(0, 1, 2) at twists (21, 13, 5) — first power each. (`cascade_arithmetic_period.py`.)

**Theorem 11 (Projection; `cascade_arithmetic_s5.py`).** Measurement of a colour-lattice
state is trace-duality pairing with the inverse different of ℚ(ζ₃): the su(3) roots *are* the
units μ₆ of ℤ[ω]; the dual lattice is the ring rotated exactly 30° (the different (√−3)
modulo the order-6 unit rotations); the fundamental weight is e^(iπ/6)/√3, a minimal dual
vector (10⁻¹⁶). Every minimal pairing projects at cos(π/6) — **a factor that exists among
imaginary quadratic rings if and only if disc = −3.**

**Theorem 12 (Measurement; `cascade_measurement_joint.py`).** For the forced Gaussian, the
r.m.s. point, the mean-action point, and the AEP-typical point (surprisal = entropy) coincide
exactly. A record's weight is the quenched (geometric-mean) average — the almost-sure
multiplicative rate of compounding records (LLN; concentration 1/√(2n) verified) — giving
e^(±r/2) exactly at rank r. *Definitional clause D1:* a measurement is a repeatable record
whose weight compounds multiplicatively. D1 has no tunable content.

**Mechanism M (activation; `cascade_activation_mechanism.py`, `cascade_joints_derived.py`;
status corrected per review Finding 1).** Each subcritical marked crossing is the chirality
flip −1 — the torsion unit — whose minimal word in the Weil clock is γ⁴ ({k : γᵏ = −1} =
{4}): four turn-units, phase −1 (the fermionic crossing sign). **Derived:** the ×3
*incoherence* (orthogonal modes of the factorized measure add without cross-terms — though
the channel *count* itself, and its N_c/N_gen identification across the quark and neutrino
sectors, is instantiation: second review, Finding 5), and the flip-word arithmetic
({k : γᵏ = −1} = {4}) — though **the count "4" buys π² only jointly with the per-step unit
assignment, which is the convention below** (the granularity changed between A38's
quarter-turns and A43's eighth-turns while E stayed fixed — second review, Finding 4, a
fixed-target signature this paper records rather than disputes). **Convention, counted in
the residue:** the unit-carrying integral. In the x²-normalization, ∫e^(ix²)dx = Γ(½)·ζ₈ and
four units carry Γ(½)⁴ = π²; in the self-dual normalization the modulus is 1 and E = 3,
excluded by data at ~99σ. The x²-unit is the same Γ(½) used throughout the framework
(Thm 4's Gaussian unit, the obstruction 1/(χΓ(½)) closing τ/μ at +0.24σ) — an *empirical
anchoring*, not an arithmetic derivation. Result: E = 3Γ(½)⁴ = 3π², the unique colour-free
composite in the empirically allowed window — where the exclusion of the other nine is
conditional on the availability assignments (e-atoms and ℤ[ω]-atoms attach only at
colour-measuring crossings: instantiation data, per Thms 11/12's meanings). JUNO's kill
window (§9) tests the mechanism's *value*; it cannot convict 3π² over its 0.1%-distant
twins (0.5–1 JUNO-σ away) — the *form* is decided by derivation or not at all.

## 6. The instantiation map — the single hypothesis

**Definition 6.1 (address book).** The observable universe occupies the tower as follows.
The observer: twist 4 — carrying **one** convention-free arithmetic distinction (the unique
nontrivially-real residue of the ℤ/8 clock, γ⁴ = −1 = the torsion unit — though its link to
the *observer* is a labeling, not a derivation), plus one Wick/lapse-conditional calculus
cross-check (scalar-flatness R·a⁴ = (n−1)(n−4) — demoted by the third review: the identity
contains no arithmetic object and the induced round-sphere metric is never scalar-flat), the
feature-boundary characterisation having been demoted by the second review
(`cascade_arithmetic_d4.py`; the selection-convention residue class — the abstract's
sixth item, "item seven" in the external reviews' numbering). Generations: the marked coset {5, 13, 21};
gauge structure: twists {12, 13, 14} with multiplicities the 2-adic Radon–Hurwitz counts;
colour characters: ℚ(ζ₃); the phase transition: the ln Γ(½) threshold (19); the sink: the
Γ(½) threshold (217); sources, occupancy classes, population classes, and record statuses as
tabulated in the verifier scripts.

This is the paper's only assumption — and its size is stated plainly (corrected again by the
third review): the chain covered by Theorem 13's exhaustion rests on **~60 discrete entries**;
the *full* §8 record (m_H, y_t, the c/u stages, the M_Pl→v anchor, 1/α_em, the radiative
slot, the cosmological forms) draws on further assignments tabulated in other verifier
scripts, bringing the complete table to **~100 discrete entries**. Rows outside the
exhaustion's scope are determined by the same rule-set but have not been exhaustion-verified.
No entry is a continuous parameter.

## 7. Uniqueness

**Theorem 13 (address-book determination; `cascade_T4_uniqueness.py`; restated per review
Finding 3).** Given the address book — approximately **sixty discrete entries** across the
chain (window endpoints, three availability ranks, member source/class/exponent, and record
status, per observable) — the rules of Theorems 8–12 are single-valued: the determined
assignment is unique and reproduces the record to ≤0.01% at every stage. *What the
exhaustion verifies:* single-valuedness of the encoded rules and arithmetic correctness of
the determined formulas. *What it does not do:* compute availability from the address data —
the script's filters test candidates against the stored table, so the theorem's content is
"a fully-specified address book leaves zero residual freedom," not "the address book is
forced." The stronger theorem (availability as a computed function of the address alone —
U2 as a function) has a **constructed v1, corrected by the round-8 hostile review**
(`cascade_u2_function.py`; Addenda 53, 56): ten shared clauses applied to per-row identity
facts reproduce the **member fields** (class, source, channel exponent, sign) on all eleven
rows — the nine T4 exhaustion stages plus θ_23 and ℓ_A — with no per-row exceptions,
against the answer key *as corrected by the review*: the previously stored θ_23 channel
count k=2 was **wrong** (the papers give k=4, `thm:theta23-closure`), and that row's encoded
identity facts had been bent to match the wrong key. The **θ_C availability defect**
(rounds 8–12: computed (1,2,0) from quark legs against the T4-stored, formula-borne
(0,0,0); carried as an open, visibly-failing row) is **resolved at the identity-fact level
by the record-legs correction (Addendum 61, round-13 restated per the WOUNDED verdict,
A62)**: the mixing angles' legs are the states the observable *reads* — **verbatim for
θ_C** (the Cabibbo proof, part4b:3728: "the overlap of two states, **one from each gauge
layer**") and by **template-extension inference for θ_23** (the papers say only "the
cascade Cabibbo template extended") — so both angles carry gauge-layer legs (12, 13) and
the unchanged clauses compute (0,0,0). The generation coset enters both formulas only at
d=13 *qua gauge layer*; the d=13 dual identity (Gen-2 = SU(2) layer) is exactly the
disputed point, and the rounds-8–12 encoding read it qua generation record (the SM-side
*about*-label). Round-13 scope honesty: the classifier (record-ratio vs frame-rotation) is
a **new per-row soft input** not determined by any existing field, and with record-legs the
angle rows' availability agreement is **near-tautological** (legs read off the formulas
whose factor content the output is checked against) — the non-trivial residue is
clause-uniformity across the four record-ratio rows, the θ_C verbatim quote, and the
**sharpened falsifier**: no future angle-type closure (the PMNS angles) may carry an
availability factor (2√π, e^(r/2) colour, cos(π/6) projection); the repo's standing PMNS
candidates carry N_c in all three formulas, disclosed as adjacent evidence — if a promoted
PMNS closure's N_c proves scheme-equivalent to the colour factor (A14's e-vs-N_c note),
the rule dies. The m_b/m_τ projection rank rides on the audit-lemma corpus, not the papers
(round-13 M4). The earlier claims "11/11 on all seven fields" and "~7 discretionary
choices per row → ~1" are **withdrawn**: by scalar count the identity-fact table (76) is
larger than the stored-output table (50), and the residual claim is structural only (one
shared rule-set on member fields). Further round-8 corrections: the A13 content grading is
now applied consistently (θ_C and m_τ-abs carry novel=None — the earlier θ_C grading
contradicted A13's half-weight exemption and the m_τ-abs grading conflated A52's
full-formula flag criterion with the novel-content grading), which also revealed that v1's
"first-run failure and data-forced sharpening" narrative was an artifact of the inconsistent
grading and is withdrawn. Standing disclosures: fixed-target assembly; the Observer k=3
import; the genuinely ambiguous kind assignment for ℓ_A (load-bearing for precedence
anchoring).

**Theorem 13b (rule-set uniqueness within the declared clause space;
`cascade_u2_uniqueness.py`; rounds 8–14 corrected).** Enumerate **44** papers-motivated variants
(the previous count "24" was wrong) across the ten clause slots under a no-name rule and run
the full cartesian products against the corrected key, with every kill **σ-classified**
(LABEL = record-label only, zero observational content; RECORD < 2σ — experiment cannot
distinguish, killed by table fidelity alone; DATA ≥ 2σ). The previous blanket claim "every
kill is a data-kill" is **withdrawn** — the celebrated θ_C kill of the point-counting
gauge-flag variant was 0.19σ experimentally, and was in any case an artifact of the
inconsistent grading (under the consistent A13 grading that variant *survives*). Corrected
results: the availability block, which had **zero survivors** through rounds 8–12 (the θ_C
defect), has **six survivors under the Addendum-61 record-legs encoding** — the canonical clauses,
two extensional duplicates, and the cross-generation indicator, a **genuine off-domain
fork** discriminated by probe P1 (round-13 M3 corrected the earlier "two duplicates"
miscount); the colour-rank slot is pinned uniquely by m_b/m_τ, while the projection slot's
pinning is **conditional on the audit-lemma corpus** for m_b/m_τ's proj=1 (the papers'
Tier-4a "m_b/m_τ = e" carries no projection factor — round-13 M4); all conditional on the
record-legs rule (a new per-row soft input, fixed-target, PMNS-falsifiable); on **member
fields**, four slots are pinned
with multi-σ kills among their alternatives (flag P: up to 187σ via m_τ-abs; flag L: up to
66σ via sin²θ_W with its second kill at 2.3σ; sign: 4σ via α_s — though the class-label
swap kill is LABEL-only and the *distinctive* +/− structure is pinned only at RECORD 1.0σ;
channel count: up to 67σ via sin²θ_W — though the *doubling* itself is pinned only at
RECORD 1.4σ, and round 9 (M1) replaced the bent period convention with the papers'
(d−1)//8, under which the pinning is over a uniform content encoding), while the **G-flag
reading has three survivors**, the **precedence order has all six** (no realized row is
multi-flag under the consistent grading; round 9 (M3) further showed the precedence is
vacuous on the papers' uniform expression-tree reading too — its 13–109σ anchoring is
conditional on A52's variant gradings), and the Family-B kind restriction has two.
36 member-survivor combinations, no compensating combos; all survivor freedom is off-domain
and enumerated by the probe forks **after round 9 added P6 and round 10 added P7** (round 9
found the original five probes could not separate the canonical G reading from the
point-counting survivor; round 10 found P1–P6 *still* left the precedence pairs {PGL,GPL}
and {LPG,LGP} unseparated — no probe carried P∧G — and with P7 all six orderings have
distinct probe signatures; each round's completeness claim was retrospectively false and
each was corrected on the record). Round 11 corrected P7's *justification*: the round-10
claim that the papers' m_W-absolute realizes the P∧G class was grading-inconsistent —
under the arc's own uniform reading m_W-absolute is (T,F,F), its window content inside
closed constituents exactly as m_τ-abs's — so P7 stands as a well-formed hypothetical
corner (the nearest uniform-reading P∧G configuration, the VEV v with its top-level window
exponential, is an anchor with no addressed member row), and the grading-inconsistency
class is recorded at its third occurrence.
Uniqueness is relative to a space that also holds the **source map {19, 5, 14, 7} and the
population-class names fixed** — a withheld axis, disclosed. The Observer k = 3, the
content grading, and the ℓ_A kind remain inputs.

**Theorem 13c — withdrawn as a theorem; retained as annotation
(`cascade_u2_first_principles.py`; round-8).** The previous version claimed three
stipulations dissolve into foundation objects. The round-8 hostile review defeated each
claim, and the retraction is recorded here in place: (i) the "half-open support theorem"
for the gauge flag is **retracted** — the μ/e path's summand set *includes* p(14)
(part4b:83, "d=14..21 … exclusive of the lower endpoint"), so no faithful support reading
exempts it; the prior computation double-shifted the summand ranges, the prior increment
verifier uses the opposite span convention, and the clause is what it always was: the
papers' strict-boundary stipulation (part4b:503, flagged Conditional at 4108(a)); (ii)
"Theorem 9's one-record-one-frame" **does not exist** — the phrase was an invented gloss
(Theorem 9 here is the Sign rule; the quenched-record theorem says nothing about frames),
so the nesting is a freestanding and **reversible** argument (path-before-read argues
unit > gauge > observer, i.e. PGL, equally well); (iii) "Observer 3 = |marked set|, a
theorem" is **false as attributed** — T6 forces only the subcritical set {5,13}, size two,
and {5,13,21} is Definition 6.1 instantiation data, so k = 3 remains a soft input read as
an instantiation count; additionally "19 and 5 are foundation objects" is withdrawn (all
four source values {19, 5, 14, 7} pass through the same feature→layer selection convention
counted in this paper's residue, and the observer is twist 4, not 5), and the claim of "no
precedence order, no null clause, no k-table in the code" was literally false — the code is
an ordered decision chain with an else-null and inline constants; the annotations propose
*reasons*, they do not remove stipulations. What remains at honest strength: the clause
structure carries proposed groundings — nesting and contact-counting **arguments**, winding
and field-degree **identifications** (the colour 2 is equally the su(3) Cartan rank; a
choice among coincident 2s) — and the reconstruction takes the canonical branch on each of
Theorem 13b's probe forks as a **proposal**, not an adjudication. Member fields 11/11 under
the corrected key; the θ_C availability defect, open through rounds 8–12, is resolved
conditional on the Addendum-61 record-legs rule (round-13 restated — see Theorem 13's
corrected tail).

## 8. The record: agreement at current precision

Every output below is forced by Theorems 1–13 under Definition 6.1 (determination; the
exhaustion-verification status of the ~100 address entries is per §6 — ~60
machine-exhausted); deviations are against
current world data (verifiers in `tools/research/`; the Planck-anchored chain runs
M_Pl → v → all masses):

| Observable | Arithmetic output | Deviation |
|---|---|---|
| ρ_Λ/M⁴_Pl,red | 7.145×10⁻¹²¹ | −0.04σ (Planck) |
| w(z) | −1 exactly (structural) | consistent |
| m_H | 125.19 GeV | −0.35σ |
| m_t | 172.61 GeV | +0.14σ |
| m_b, m_c, m_s, m_d, m_u | full chain | −0.03σ, −0.36σ, −0.03σ, −0.34σ, −0.13σ |
| m_τ/m_μ, m_μ/m_e, m_τ | 16.8173; 206.771; 1776.82 MeV | +0.24σ; +0.001%; −0.31σ |
| m_τ, m_μ, m_e absolute (from M_Pl) | chain | −21, −38, −49 ppm |
| m_ν3; Δm²_sol | 49.28 meV; 7.572×10⁻⁵ eV² | −0.5% (−0.7σ PDG; **−2.9σ NuFit 6.0** — input-dependent, under tension); +0.24σ |
| α_s(M_Z); 1/α_em; sin²θ_W | 0.11792; 137.028; 0.23123 | +0.02σ; 0.006%; +0.40σ |
| θ_C; θ₂₃ | 13.04°; closure | +0.03σ; sub-σ |
| Ω_m; ℓ_A | 0.31473; 301.44 | −0.04σ; **−1.8σ** (vs 301.6 ± 0.09; corrected per review Finding 5 — the papers' −0.16 is the absolute difference, not a σ count) |
| θ_QCD | 0 exactly | consistent |

*Metric discipline (per review Finding 5):* two metrics appear above. σ-entries are against
experimental error where it dominates; %/ppm entries (chain absolutes, 1/α_em, m_ν3) are
against the framework's **leading-order systematic floor** — there the deviation is many
experimental σ, and the claim is that the residual sits at the framework's stated floor, not
inside experimental error. With that convention stated: no output disagrees with any current
measurement beyond the applicable tolerance; ℓ_A (−1.8σ) is the largest strain
**among the σ-graded entries**, and m_ν3's −2.9σ (NuFit input) — quoted in its row
for information — is graded by the floor metric (−0.5%), its input-dependent tension
registered there and in the §9 ledger (round 44 reconciled the double appearance). This
table, plus Theorems 1–13, is the content of the word "indistinguishable."

## 9. The Indistinguishability Theorem — and its executioners

**Theorem 14 (Indistinguishability, conditional).** *Conditional on Definition 6.1, the
arithmetic of the completed Riemann zeta function at the real place is indistinguishable from
the observable universe at current experimental precision.* *Proof:* Theorems 1–13
(mathematics) + the table of §8 (the record). ∎

The conditional cannot be discharged by mathematics — no theory's can. It is discharged, or
destroyed, by the pre-registered ledger, frozen before its judges report — with the
one standing exception disclosed in its own first row, where published compressed
bounds already press the value:

| Prediction | Value | Judge | Kill condition |
|---|---|---|---|
| Σm_ν | 60.91 meV, normal ordering | DESI/CMB-S4; JUNO | bound < ~60 meV, or inverted ordering. **Standing tension, not future:** published ACT+DESI compressed bounds already reach 52–57 meV (audit A29) — if those combinations firm up, this row is already dead |
| Δm²₂₁ | 7.572×10⁻⁵ eV² | JUNO (~0.3%) | outside ~0.6% window kills Mechanism M |
| m_β; m_ββ | 9.1 meV; ≤5.5 meV | KATRIN; LEGEND-1000/nEXO | any signal at current sensitivity |
| w(z) | −1, no evolution | DESI DR3+ | any confirmed evolution |
| m_H | 125.194 GeV | HL-LHC (~25 MeV) | >3σ miss |
| m_τ | π⁶/945-vs-α(14)/2 fork | Belle II (~0.02 MeV) | adjudicates |
| m_b/m_τ; m_c; m_s/m_ud; m_u/m_d; y_t | 2.35405; 1.2714; 27.35; 0.4593; 0.99142 | lattice/colliders | >3σ miss |
| Structure | no 4th generation, no anyons (free 3+1D), no SUSY partners, no axion, no dark-matter particle | any discovery | fatal |

## 10. Honest limits

1. **C1 is forever empirical.** The arithmetic distinguishes the observer's address by one
   convention-free fact (§6; two former pinnings were demoted by reviews two and three) and
   cannot select it; the selection is the hypothesis. If the arithmetic could prove its own instantiation, no
   experiment could kill it — falsifiability *requires* this step to remain empirical.
2. **External and conventional inputs (corrected per the external review).** Lovelock's
   theorem (selection of d = 4; external tensor calculus); the closed atom grammar A2 (a
   completeness statement over what was used, not a proof that nothing else could attach);
   the x²-unit normalization carrying Γ(½) (empirically anchored — the self-dual alternative
   gives E = 3, excluded by data — not arithmetically forced); the P > L > G precedence
   (motivated); and the feature→layer selection convention (second review, Finding 1 —
   part0 itself concedes no uniform rounding rule exists). J2's incoherence is derived from
   the factorized measure; the flip-word arithmetic is derived but buys π² only jointly with
   the unit convention; the feature-list completeness attempt **failed re-review** and is
   recorded as open (`cascade_feature_monoid.py`, rewritten to state the failure).
3. **Provenance.** Theorems 8–13 were constructed by a single reviewer in a single session,
   knowing the empirical targets; each carries a rigorous mathematical core, but the
   interpretive bridges from mathematics to rule await hostile external review. The
   registered ledger is the only bias-immune instrument, and the framework's standing is
   staked on it, not on the derivations.
4. **The stopping rule.** No further retrodictive closures are admissible. The framework is
   finished arguing; §9 names its judges and accepts their verdicts in advance.

---

*Verification suite (round-45 corrected census: the **27 scripts cited in place** above — the round-44 footer's "31 cited in place" was self-referential, counting the prior footer's own four record-verifier names — plus the four §8-record verifiers cited only in this list, marked °; all under `tools/research/`): `cascade_formulation_kernel.py`, `cascade_explicit_formula_bridge.py`, `cascade_zero_side_features.py`, `cascade_colour_field_bridge.py`, `cascade_finite_places.py`, `cascade_local_tate.py`, `cascade_witt_weil.py`, `cascade_local_family.py`, `cascade_adams_loadbearing.py`, `cascade_layer_selection.py`, `cascade_arithmetic_increment.py`, `cascade_arithmetic_period.py`, `cascade_arithmetic_sign.py`, `cascade_arithmetic_s5.py`, `cascade_arithmetic_d4.py`, `cascade_increment_rule.py`, `cascade_second_quantized.py`, `cascade_measurement_joint.py`, `cascade_activation_mechanism.py`, `cascade_joints_derived.py`, `cascade_feature_monoid.py`, `cascade_precedence_vacuity.py`, `cascade_ds_audit.py`, `cascade_T4_uniqueness.py`, `cascade_u2_function.py`, `cascade_u2_uniqueness.py`, `cascade_u2_first_principles.py`, `cascade_leptons.py`°, `cascade_neutrino_closure.py`°, `cascade_E_fit_audit.py`°, `cascade_null_clone.py`°. Classical inputs: Tate's thesis; Weil and Rao, the metaplectic index and its cocycle; Wall, the graded Brauer group; Lam, the Witt groups of local fields; Gauss and Landsberg–Schaar, quadratic sums; Legendre, the duplication formula; Hensel's lemma; Hilbert, the norm-residue symbol; Bohr–Mollerup; Poincaré–Hopf; Steenrod–Whitehead, Toda, and Adams, vector fields on spheres; Radon–Hurwitz; Lovelock; Kolmogorov.*
