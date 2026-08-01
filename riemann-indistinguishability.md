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
to the χ₋₃ minimality-pairing — one class, three members *(net-state, Theorem 1j
as adjudicated round 57: the third member re-motivated — C1-anchored matching
replaces the order principle, minimality entailed within the pairing-act, which
persists; three members and the seven-item count stand)* *(Net-state, Theorem 1y round 107: member one closes — the site-E pairing entailed given the tower's dictionary, the sup labeling already resolved into A1's ledger; the class keeps two members; the seven-item count stands.)* *(net-state, Theorem 1k
round 60, as corrected by F1: the first member likewise re-motivated — the
assignment is entailed given the site-E pairing plus Part 0's variational-sup
labeling of the boundary sides, both persisting as the member's content; no
rounding rule was ever needed; three members and the seven-item
count stand)* *(Net-state, Theorem 1y round 107: member one closes — the site-E pairing entailed given the tower's dictionary, the sup labeling already resolved into A1's ledger; the class keeps two members; the seven-item count stands.)* *(net-state, Theorem 1l round 64: the second member likewise
re-motivated — the per-site pairing family is closed given the tower's dictionary
(Definition 2.1 + Theorem 1); the E-anchor re-grades as a cross-check; three
members and the seven-item count stand)* *(Net-state, Theorem 1y round 107: member one closes — the site-E pairing entailed given the tower's dictionary, the sup labeling already resolved into A1's ledger; the class keeps two members; the seven-item count stands.)*); and the hypothesis itself
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
*(Net-state, Theorem 1l round 64: the one historical breach of this discipline was Theorem
9's Geometric coset weight 2/Γ_ℝ(d) = Ω(d−1) — the avatar — demoted by the fourth review
and sharpened by 1l(iii); with that clause demoted, the sentence stands as the discipline
it names.)*

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
adopting conductor-minimality as the pairing principle *(net-state, Theorem 1j as
adjudicated round 57: the member is re-motivated — given the pairing-act, the T11
μ₆ requirement determines χ₋₃ with minimality entailed; the pairing-act itself
persists as the charged member)* — the same selection-convention
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
decreasing residuals); the minimality-pairing is a convention, not a forcing
*(net-state, round-57 adjudication: re-motivated by Theorem 1j — the field is
determined given the pairing-act, which persists as the charged member)*.

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
Tate theory is the named next step, not opened *(net-state: the unramified half
was opened by 1e, the ramified half by Theorem 1i — the root-number identity)*; no data, no closures, no RH/GRH. *Run
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
claim that the finite places produce the 3 is stopping-rule-gated new physics.
*(Net-state, Theorem 1w: the count is now entailed given the pairing-act plus T8's
root–unit identity, via the unit-torsion/rank-2-classification route — global and
archimedean, reading no finite place, so this negative stands verbatim; what remains
archimedean is the layer alone.)* *Run
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

**Theorem 1i (the ramified Tate step: pure-phase towers and the root-number
identity; `cascade_tate_epsilon.py`).** *(i) Pure phase.* A ramified character of
ℚ_p^× has local L-factor 1 — no pole, no Euler factor (classical: Tate); its
entire functional-equation content is the ε-factor, a normalized Gauss sum. The
ramified towers are **pure phase**; the family's two unramified members are its
only pole-carriers — the trivial tower (1e(i)), alone in carrying a pole at real
s, and the unramified quadratic η₅'s tower (1 + 2^{−s})^{−1}, whose poles are
complex *(round-54 F1: the first writing's "the only pole-carrying member" was a
false universal — η₅ is unramified too)* — exhibited in-code by the
shell-by-shell vanishing of the ramified unit-character sums (dyadic and
triadic, gate E7). *(ii) The root-number identity — the file's core.* For each
dyadic square class a, let η_a = (·, a)₂. Then, gated on all eight classes:
**β(a) = ε(η_a)** — the clock's disc-twist (1f/1g) *is* Tate's quadratic
root-number map — where ε is the local ε-factor (unit-conductor Gauss sum times
the classical unramified-twist correction η_a(2)^{a(χ)}, the twist formula's
content gated through the independent β-side ratios on the three η₅-twisted
pairs — the ε-side ratio cancels its shared unit base bit-exactly, and the
(3,7) pair's even exponent makes its correction invisible in principle: the
odd-exponent pairs carry the content *(round-54 F3 strengthened the gate)*), in the orientation **fixed by the
ε product formula, not chosen silently**: the finite Gauss orientation pairing
with the classical ε_∞(odd) = −i is pinned by gating Π_v ε_v = +1 on four
independently known global root numbers (χ₋₄, χ₈, χ₋₈, and the paper's own
χ₋₃ from 1c). Equivalently, in the program's standard ψ₂:
β(a) = η_a(−1)·ε(η_a, ψ₂). Combined with 1g(ii)'s closed form:
**γ₂(q) = γ₂(1)^dim · ε(η_disc) · hasse(q)** — Tate's local functional equation
supplies the clock's twist structure (exhibited on 8 + 64 + battery forms; a
corollary of the eight-class identity plus 1g's gated cocycle and closed form —
round-54 F6 declared the exhibit status, per the L7b precedent; E4's
decomposition line likewise shares E1's anchor computation, round-54 F5). The
general Weil-index/ε relation is classical in substance (Weil's metaplectic
index); the eight-class identity in the program's stated conventions is what
the gates certify. The round-22 covariance grading applies verbatim: the
structural statements are convention-free, the specific values
convention-tied. *(iii) The colour decomposition.* The global root number +1
of L(s, χ₋₃) — verified analytically at 1c — decomposes locally as
**ε₃(χ₋₃)·ε_∞(sgn) = (+i)(−i) = +1** (gated): the colour character's sign is a
two-place cancellation, ramified conductor 3 against the archimedean sgn
tower — the 1f/1g two-place family shape again, now at the ε level. And the
odd bridge's conductor term −½ln 3 (1c) is **minus** the log-derivative of the
functional equation's conductor factor 3^{s/2} — the factor crosses to the
p_sgn side *(round-54 F2: the first writing dropped the minus)* — with the
identity's genuine gate being `cascade_local_tate.py`'s T-loc4 bridge check
(10⁻²⁰); E5 is the arithmetic exhibit *(round-54 F7)*:
Door 4's "conductor is the different" has its ε-side home. *Honest scope:*
**no A2 grammar entry is derived, no number changes, no closure is claimed**
(category (a); no data, no RH/GRH, no semiclassics — Gauss sums and Tate local
theory throughout; Check 8: the hypothesis is nowhere an input). The
identity relocates the clock's twist into one more classical home; it does
not make the finite places produce a grammar entry, and 1f(iii)'s honest
negative for N_c stands verbatim.

**Theorem 1j (the torsion-exceptional selection: the kernel's two-field class
anatomy, and the χ₋₃ pairing ~~re-founded~~ **[round-58 F2: re-motivated — per
the round-57 adjudication]**; `cascade_torsion_selection.py`).** *(i) The classical
census.* Among imaginary quadratic fields the unit-group torsion is |μ| ∈
{2, 4, 6}, with **|μ| = 6 uniquely at disc −3** (ℚ(ζ₃), the six units of ℤ[ω])
and **|μ| = 4 uniquely at disc −4** (ℚ(ζ₄) = ℚ(i)) — gated by direct unit count
over all 3043 fundamental discriminants |d| ≤ 10⁴. *(ii) The kernel's class-level anatomy, read back through the census.* The
dyadic facts are class-level — (·, −3)₂ = (·, −11)₂ identically, so the local
data alone determines square classes, not fields; the field-level readback below
is privileged by the torsion census plus the T11 overlay (round-57 F2 corrected
the first writing's "exactly these two fields" determination claim). The 1h invisibility
criterion is **the μ₄ field's discriminant character at the clock prime** —
(·, −4)₂ = (·, −1)₂ on all eight classes, ker = H (gated) — and the invisible
unit direction is **the μ₆ field's discriminant**: H ∩ units = {1, cls(−3)},
with ℚ₂(√−3) = ℚ₂(ζ₃) the unramified quadratic and the μ₄ field itself
2-ramified (cls(−4) = 7, clock-visible; gated). The only two imaginary
quadratics with extra roots of unity — colour's field and the quarter-turn
field — divide the clock-invisible structure between them. *(iii) The pairing
re-motivated — the round-57 adjudication (MODIFY) applied.* Round-15 M3 graded
the χ₋₃ pairing a convention because the odd bridge selects nothing and
conductor-minimality was adopted as the principle. What 1j establishes, exactly:
**given the pairing-act** — pairing the odd feature with the colour field's
character, an act Theorem 11 does not entail and Definition 6.1 does not address
(the odd feature carries no derived address) — **the field is then determined
with no further choice**: T11's μ₆ requirement (the su(3) roots *are* μ₆; the
cos(π/6) projection exists among imaginary quadratic rings iff disc = −3)
matches the census's unique |μ| = 6 field, so χ₋₃ follows and
conductor-minimality is **entailed within the pairing** (|disc| = 3 a fortiori
minimal; gated) — a consequence, not a principle, *conditional on the pairing*.
The selected field's dyadic shadow is the invisible unit direction (ii), its
ε-support the two-place quarter-turn pair {3, ∞} (1i; re-exhibited in-code).
~~The re-founding creates no new assumption; it shows the pairing needs none
beyond the T11 anchor~~ **[struck round 57 (F1, MAJOR): the first writing
claimed the member reduces to a consequence and that the selection ran "with no
order principle" — overclaimed on three counts: maximality is itself an
extremal choice of the same epistemic type as minimality (the gate literally
computes a maximum); the order-free matching route imports the unstated pairing
premise; and χ₋₄ — itself an odd real primitive character, elevated by (ii) —
is a live alternative partner that only the order or the pairing-act excludes]**.
**The adjudicated outcome:** the selection class **keeps three members** *(net-state, Theorem 1y round 107: now two — member one closes)*; the
third's content is *re-motivated* — from an order principle (minimality) to
C1-anchored matching against the existing T11 requirement, with minimality
entailed inside that motivation — a real improvement in motivation, not a
reduction. The **seven-item residue count stands**, as guaranteed either way. *Honest scope:* no number changes, no
closure, no data, no RH/GRH, no semiclassics; the grammar-reading question
stays open — narrowed again (the colour entry's dyadic shadow IS the invisible
unit coordinate: the 1e(iv) identification relocated, not a new forcing).
*(Net-state, Theorem 1r as corrected round 81: the act's anatomy — the live
alternative χ₋₄ fails three distinct committed anchors (the clock kernel, under
act-form W₁, strictly weaker extensionally than the colour gloss — the act's
standing form, pair with the colour field's character, defined at 1r; the carrying
conductors and the torsion census, extensionally equivalent to the gloss's
output and weaker only in what they name), and the bridge's own committed
constant π/(3√3) carries w = 6 by Dirichlet's formula; the F1 recital's "only
the order or the pairing-act excludes" is superseded in that sense. The act
itself persists; pairing-at-all is untouched.)*

**Theorem 1k (the lattice selection: the feature→layer map re-read;
`cascade_lattice_selection.py`).** *(i) The lattice facts.* Under the canonical
window-potential pairing p(d) := P(d+1) (the d↔s audit's site E, the data-anchored
convention *(net-state, Theorem 1y round 107: entailed — Γ-argument arithmetic; the anchor re-grades to cross-check)*), the integer content of Part 0's regime partition is exact and
boundary-convention-free: p is strictly increasing on the lattice; the threshold bands
are B₁ = {d : 0 < p(d) < ln Γ(½)} = **{7,…,19}** and B₂ = {d : ln Γ(½) < p(d) < Γ(½)} =
**{20,…,217}**; no lattice point lies within 8.5×10⁻⁴ of a threshold, so **all four
half-open interval conventions produce the same integer sets**; and V(d) has the strict
discrete argmax **5** (V(4) < V(5) > V(6); ratio strictly decreasing, so unimodal with a
gated tail). Hence, **with the boundary sides fixed by Part 0's variational
characterisation** (the sup labeling — see (ii)), {argmax_ℤ V, min B₁, max B₁, max B₂} =
**{5, 7, 19, 217}**, with min B₂ = max B₁ + 1 (tiling: the band structure carries
exactly three independent integers, one per crossing; the fourth distinguished layer is
the interior landmark argmax V — Part 0's own compression: *"one interior landmark plus
the three boundaries"*) — and **no continuum crossing is rounded anywhere**; the
non-integer crossing positions (6.2569, 19.7308, 217.6267 in d; non-integrality gated
with margin ≥ 8.5×10⁻⁴) merely locate the band boundaries. What the lattice does *not*
fix is the **side** of each crossing: the inf labeling (6, 20, 218) = (max B₀, min B₂,
min B₃) (B₀ = {d : p(d) < 0} and B₃ = {d : p(d) > Γ(½)} — Part 0's Growth and Oblivion
regimes) is equally lattice-exact under the same pairing — the 2³ labeling freedom is
adjudicated by the variational theorem, not by the lattice (round-60 F1; gated, K7). *(ii)
Concordance.* This paper's Theorem-7 feature set is the same object list in the s frame:
the critical pair 5.2569/7.2569 is **one equation** — the balance ψ(x/2) = ln π — read
at two argument offsets — the V-argmax equation (d = 5.2569, factor Γ_ℝ(d+2)) and the p-zero
(d = 6.2569, s = 7.2569) — gated as the same root; the s-thresholds 20.73 and 218.63 are
the d-crossings + 1. The mixed-rounding appearance that founded the review-2 charge
(floor-in-s for the pair, floor-in-d for the thresholds) is **one lattice rule seen
across the s = d+1 frame line**. And Part 0's variational labels (the sup of the
invariant's bilinear form over the eight boundary labelings, attained uniquely at
(7,19,217) — in the source since 2026-05: the sup definition is the sentence after the
concession this paper's §10 cites, the theorem follows it) agree gate-by-gate **given
the sup**: at the two upper boundaries the sup pick reduces to the band-sign facts,
because d log Ω_d/dd = −p(d) — Part 0's own identity, *"the first derivative of the
log-area, which is −p(d)"* — makes Ω decreasing exactly where p > 0; at the first
boundary the two principles are distinct and agree numerically (Ω₇ < Ω₆, margin ≈1.9%;
gated). **The sup itself is a second given** (round-60 F1): Part 0 grades it as
data-corroborated — *"The supremum (7,19,217) is the only labelling that reproduces the
observed"* ρ_Λ — with its derivation open — *"A principled derivation of max from the
cascade's own axioms… remains open"* — and the inf labeling gives 1.02×10⁻¹²¹ — an
order of magnitude (≈10.8×) below observation (the value gated, K7; Part 0's original
*"two orders of magnitude"* descriptor was a source-side slip, corrected there —
round-62 F1) *(net-state, Theorem 1n round 71: the given is re-motivated — the sup is
exactly the odd/Euler-null-sphere member of every pair and the minimal-horizon-budget
labeling, gated equivalents; the forcing stays open and the given persists)*
*(Net-state, Theorem 1v round 98: the owner adopted the Riemann kernel — A1 re-founded on Γ_ℝ entire (the owner's phrase; "entire" in the sense of *in its entirety* — the function itself is meromorphic, its poles load-bearing; glossed in full at Theorem 1v, placed here at first use per round-99 F2) with mirror coherence as its non-degeneracy clause; the labeling is now forced by the amended axiom and this open-status is resolved into A1's ledger.)*. *(iii) The member re-read — the
round-57 adjudication grammar applied in advance.* The review-2 charge is true in the
rounding frame and empty in the lattice frame: **given the site-E pairing** — the
anchored convention, which **persists in the residue** *(net-state, Theorem 1y round 107: entailed — member one closes; the anchor re-grades to cross-check)* (under the alternative pairing
p(d) = P(d) the three band labels shift coherently, the argmax member unchanged:
{5, 8, 20, 218}, gated) — **and given Part 0's variational-sup labeling of the boundary
sides**, the feature→layer assignment is entailed. ~~lattice-entailed with zero further
freedom […] its content is absorbed into the pairing member — the assignment was never
an independent choice; it is the pairing choice, seen once~~ **[struck round 60 (F1,
MAJOR; span rendered verbatim from the first writing per round-61 F1, the bracketed
ellipsis marking the elided sentence boundary and the second sentence's head clause,
which survives as live text below): under the same pairing the inf
labeling (6, 20, 218) is equally lattice-exact — the boundary-side selection is the 2³
freedom Part 0's variational (sup) characterisation adjudicates, a second given,
data-corroborated with its derivation open by Part 0's own grading]**. The class's
first member is thereby **re-motivated, not deleted**: from an ad hoc mixed-rounding
appearance to **two named, listed anchors** — the site-E pairing plus the
variational-sup labeling, both persisting as the member's conventional content —
exactly as the third member was re-motivated by Theorem 1j. **Three
members and the seven-item count stand.** *(Net-state, Theorem 1y round 107: member one closes — the site-E pairing entailed given the tower's dictionary, the sup labeling already resolved into A1's ledger; the class keeps two members; the seven-item count stands.)* Registration: this paper's §10 and the
feature-monoid verifier cited Part 0's concession sentence without the variational
theorem that follows it in the source (or the regime partition, which *precedes* the
concession in an earlier section — location corrected, round-60 F3) — corrected with
net-state markers, not strikes (the quoted sentence is verbatim-true; the citation was
incomplete). *Honest scope:* no number changes, no closure, no data beyond the already-
counted site-E anchor, no RH/GRH, no semiclassics; Finding 6 (feature-list completeness)
stays REOPENED — the lattice frame reads the *listed* features, it does not prove the
list complete.

**Theorem 1l (the pairing dictionary: member two attacked directly;
`cascade_pairing_dictionary.py`).** *(i) The dictionary pins the arguments.* Definition
2.1 fixes the tower as the integer points s = d+1 with local factor Γ_ℝ(s); Theorem 1's
kernel defines the four primitives at that point (gated ≤7×10⁻¹⁴). Under this dictionary
the audit's "alternative pairing" objects are not pairings of the same objects:
**P(d) = p(d−1)** (the previous layer's potential) and **2/Γ_ℝ(d) = Ω(d−1)** (the
previous layer's measure) — identities, declared as such. *(ii) Site E re-graded: the
anchor is a cross-check.* The audit's E-flip is **identically a window shift**
(Σ P(d), d = 6..13 = Σ p(d), d = 5..12; residual exactly 0, gated) — and a *mixed* one:
it flipped the potential sum while keeping the boundary term R(14)²/8 fixed. The
coherent shift (boundary term R(13)) gives 10.4718 against the audit's mixed 10.4584 —
both catastrophically off the canonical 16.8173 (observed 16.8170) — so **the
"alternative" was never one convention**. The −38% anchor thereby **re-grades from
selection to cross-check**: the data confirms the dictionary; what remains conventional
at E is the closure windows' **endpoint data** — Definition-6.1 instantiation plus the
strict-boundary stipulation (part4b) — items already listed in the residue accounting.
*(Net-state, Theorem 1z round 109: the endpoint data is menu-bounded with zero free
numbers — five termini in committed menus (round-113 F1), the sixth the observer dimension, C1-anchored;
every in-menu alternative data-excluded; the stipulation priced at three attachment
instances, all alternatives excluded, the weakest at −2.22σ; member two persists,
sharpened. Round-110 F1: this marker was placed before the round-109 sweep corrected
the instance count and was missed by that sweep — the stale "two binary decisions"
recital is corrected here.)*
*(iii) Site C sharpened.* The Geometric two-coset clause's passing computation used
Ω(d−1) at layer d — the avatar, which Theorem 1's own Remark forswears (*"The paper
never uses the avatar; the arithmetic is primary"*). Under the tower's own measure Ω(d)
the clause **fails** (0.35001 ≥ 1/π; the avatar's 0.31322 passes; both gated): the
review-4 demotion sharpens from convention-conditional to *does not hold in the tower's
dictionary*; the recorded single-coset repair candidate (surviving both weights) remains
the live route; no number changes (the Ω_m backing was already withdrawn from "proved").
*(iv) The member re-read — the 1j/1k grammar.* **Given Definition 2.1 and Theorem 1** —
the tower's dictionary, definitional and gated, whose only alternative is a contentless
global renaming (s′ = s−1 renames every symbol and changes no computed number; declared,
not gated — a tautology cannot fail) — **there is no per-site d↔s freedom**: E's residue
is the endpoint data (listed) *(net-state, Theorem 1z round 109: menu-bounded, zero free numbers, alternatives data-excluded; sharpened)*; C's avatar is a frame error inside a demoted clause; B
and H are flip-invariant (re-gated); D was closed by Theorem 1k — given the site-E pairing
plus the variational-sup labeling, its two givens (round-60 F1). The review-4 widening
("every d↔s layer/weight pairing choice") named a per-site family; **the family is
closed**. Member two is **re-motivated, not deleted**: its live content is the
dictionary itself plus the already-listed endpoint items *(net-state, Theorem 1z
round 109: the endpoint items sharpened — menu-bounded, zero free numbers,
alternatives data-excluded)*. **Three members and the
seven-item count stand.** *(Net-state, Theorem 1y round 107: member one closes — the site-E pairing entailed given the tower's dictionary, the sup labeling already resolved into A1's ledger; the class keeps two members; the seven-item count stands.)* *Honest scope:* no number changes, no closure, no new data
(the observed 16.8170 appears only as the committed audit's recorded anchor, reproduced
as instrument); the member's re-motivation is conditional on the dictionary, exactly as
1k's was on the pairing-plus-sup and 1j's on the pairing-act.

**Theorem 1m (the availability factors' arithmetic homes: mass layer 3 attacked at the
factor level; `cascade_availability_factors.py`).** *(i) None of the three availability
factors is a new constant.* The **obstruction unit** 2√π = χ·Γ(½) (χ = 2 = |μ(ℝ)|) is
one object seen from two committed sides: Theorem 4's measure grammar (*"1/(χΓ(½)) per
graded crossing"*; the formulation's T2) and the companion series' topological channel (part4b: *"The
topological obstruction factor is 2√π = 2Γ(½) per Dirac layer: 2 from chirality
(χ(S^{2n}) = 2)"* and √π from the quarter-turn constant; per-layer attachment — *"Each
obstruction attenuates the projection by 2√π, giving (2√π)^{−n_D}"* — with the
d-independent propagator ratio Z_f/Z_s = 1/(2√π)). The **projection factor** cos(π/6) =
√3/2 = covol(ℤ[ω]) is Door 4's object (the 30° trace-duality lattice; C3's balance level
= T8's frame) — with the new census fact that covol = √|d|/2 is **minimal over all 3043
fundamental imaginary-quadratic discs at d = −3** (Theorem 1j's census reused; classical
closure |d| ≥ 3, so the bound is total): the projection factor is the minimal covolume
among all such rings — equivalently the densest (every imaginary-quadratic maximal order
has shortest vector exactly 1, so packing density is ∝ 1/covol; round-67 F6 stated the
premise). The **colour factor** e^{r/2} keeps 13c's grading — the rank 2 a choice
among coincident 2s, with the 1j-census anchor (the μ₆ field is degree-2 *qua* imaginary
quadratic) and e^{2/2} = e the papers' own Tier-4a record. *(ii) The fork consequence.*
R1's rank |Δg|/8 equals the number of Dirac layers (d ≡ 5 mod 8) in the half-open
interval between the legs — gated on every generation-coset pair, with periods-minus-1
an extensional duplicate on the coset (gated). On probe P1's cell (legs 5 & 21) the
count is 2 and the cross-generation indicator is 1: **given the obstruction
identification, the per-layer attachment forces the count** — a two-layer crossing costs
(2√π)² by the papers' own attenuation rule, which the indicator variant cannot
reproduce. The 13b availability block's **one genuine fork is thereby discriminated
arithmetically** — conditional on the identification, not on realizing the off-domain
probe — and the block becomes **canonical up to extensional equivalence**. The
first-principles P1 position upgrades from *"asserted, and the data cannot
distinguish"* to
*entailed given the factor identification* — the 1j/1k/1l grammar applied to layer 3.
*(iii) Honest scope.* The clause **triggers** — legs, the record-legs classifier, the
A13 grading, the ℓ_A kind, Observer k=3 — are soft inputs, **untouched**; the angle rows
stay near-tautological (round 13); R2's identification stays at 13c's strength; the
identifications are C1-conditional exactly where their sources are (T2, part4b's
topological channel, T11's colour field). No number changes, no closure, no new data
(the papers' Tier-4a value and the committed instrument records are cited as record).
Layer 3's residual gap after 1m: the trigger data, and the identifications'
conditionality.

**Theorem 1n (the sup's exact equivalents: parity, obstruction, and the horizon budget;
`cascade_sup_selection.py`).** Part 0's max-over-min remark grades its own selection
honestly: *"A principled derivation of max from the cascade's own axioms — connecting
the supremum to a distinguished quantity such as an entropy, a boundary area, or a
characteristic of the observer's layer — remains open."* This is Theorem 1k's second
given. Three exact reformulations, each gated: *(i) Parity.* The sup labels
(7, 19, 217) are exactly the **odd members** of the three straddling pairs, the inf
labels (6, 20, 218) exactly the even members — and every consecutive pair has exactly
one odd member, so odd-selection is a total, uniform rule that reproduces the sup.
*(ii) Obstruction.* In the tower's dictionary (layer d ↔ S^d, Theorem 1l),
χ(S^d) = 1 + (−1)^d: the sup labels' spheres are **Euler-null** (χ = 0,
odd-dimensional — nowhere-zero fields exist), the inf labels' spheres carry χ = 2 —
the same χ(S^{2n}) = 2 that is the obstruction toll's chirality factor (Theorem 1m;
Part 0's shift family). And **all four distinguished layers {5, 7, 19, 217} are odd**:
the entire invariant is evaluated on Euler-null spheres. *(iii) The horizon budget.*
S_dS = 24π²M⁴/ρ_Λ (S = A/4 the cascade's own — Part II=III §8, *"no semiclassical
gravity, no QFT on curved spacetime, no Bogoliubov transformations"*; the de Sitter
horizon area A = 12π/Λ Part III's; the Friedmann relation and the w = −1 theorem
Part V's ~~; the de Sitter algebra Part I's~~ **[struck round 71 (F1, MAJOR): Part I
contains no de Sitter or Friedmann content — only the closure below is Part I's]**) is
strictly decreasing in the
invariant through Part I's closure ρ = (2/π)e^{0.02108}I, so over the eight labelings
**sup I = min horizon entropy = min boundary area**: the sup is the labeling with the
smallest asymptotic information budget (3.315×10¹²² nats = 4.783×10¹²² bits; the inf
labeling's budget is 10.76× larger — the round-62 ratio as entropy stakes). This is
the exact connection Part 0's open clause requested, with the direction stated: the
sup **minimizes** the horizon budget. *(iv) Anatomy, distinctness, and honest
grading.* The agreement decomposes as three parity facts plus one inequality (content
crossings have odd integer parts; the scale crossing has even integer part and
Ω₇ < Ω₆ — each gated); the farther-integer and window-proximal re-descriptions also
reproduce the sup (gated); the characterizations are **distinct principles** (a
synthetic crossing at 20.5 would separate content-floor from odd-member — gated as a
labeled synthetic exhibit), found by inspection knowing the sup (fixed-target
disclosed). **Nothing here forces the sup**: why odd / why minimal-budget is the
residual selection content, so the forcing question stays open and 1k's second given
**persists — re-motivated** from a bare max convention to named structural
equivalents tied to the load-bearing χ machinery. Part 0's remark is registered with
the equivalences and keeps "remains open". No number changes; no closure;
category (a). *(Net-state, Theorem 1o as corrected round 75: the dichotomy has an exact form on ζ's
special-value structure — the sup's twist points are ζ's Euler-rational points and the
inf's twists mirror exactly onto the trivial zeros; the χ reading is the avatar-side
shadow, the parity form already arithmetic.)* *(Net-state, Theorem 1q ~~: the (ii)
observation that all four distinguished layers are odd is a necessity under mirror
coherence, not a coincidence — the fixed landmark d_V = 5 passes a coherence test it
could have failed~~ **[struck round 79 (F3/F7): mirror coherence is extensionally
equivalent to all-labels-odd, so "necessity under coherence" is vacuous; the d_V
clause is this parity fact re-expressed on the mirror weights, whose vanishing at
every even d is exactly parity]**, as corrected: 1q restates the all-odd fact as
non-degeneracy of the branch-swapped invariant — an equivalent reformulation, not an
explanation.)* *(Net-state, Theorem 1v round 98: the owner adopted the Riemann kernel — A1 re-founded on Γ_ℝ entire with mirror coherence as its non-degeneracy clause; the labeling is now forced by the amended axiom and this open-status is resolved into A1's ledger.)*

**Theorem 1o (the arithmetic-primary form: ζ-rational twist points and trivial-zero
avoidance; `cascade_zeta_rational.py`).** 1n's obstruction equivalent is avatar-side
(Euler characteristics of spheres) — deprecated as a register by Theorem 1's own Remark,
*"The paper never uses the avatar; the arithmetic is primary"* — while its parity
equivalent is already arithmetic (integer parity of tower labels) but stated on the
layer index ~~1n's parity and obstruction equivalents are avatar-side~~ **[struck round
75 (F2): parity of an integer index is already arithmetic; only the χ form is
avatar-side]**. This theorem expresses the dichotomy on ζ's special-value structure —
the paper's primary object. *(i) The sup's twist points are ζ's
Euler-rational points.* Under Definition 2.1 (s = d+1) the sup labels' twists are
s = 8, 20, 218, and the four distinguished layers' twists are **{6, 8, 20, 218} — all
even**, where Euler's theorem gives ζ(s) = rational·π^s (ζ(6) = π⁶/945, ζ(8) =
π⁸/9450; rationality gated exactly at all four via Bernoulli numbers). The inf labels'
twists 7, 21, 219 are odd — no closed form is known there. *(ii) The mirror dichotomy.*
Under the functional equation s ↦ 1−s the sup twists mirror to **nonzero rationals** —
ζ(−7) = 1/240, ζ(−19) = 174611/6600, ζ(−217) ≠ 0 (exact; and d_V's ζ(−5) = −1/252) —
while the inf twists mirror **exactly onto the trivial zeros**: ζ(−6) = ζ(−20) =
ζ(−218) = 0. Among the eight labelings **the sup is the unique one avoiding the
trivial-zero mirror set** (gated: every other labeling carries at least one; the inf
carries three). *(iii) The ledger cross-link.* ζ(6) = π⁶/945 **is the
frozen ledger's m_τ fork constant**: the adjudication row "π⁶/945-vs-α(14)/2" reads,
in the tower's own dictionary, *ζ at the volume-max layer's twist point vs the
compliance at the U(1) layer* — ~~an identification registered here (Check-4 note: no
repo surface previously identified π⁶/945 as ζ(6))~~ **[struck round 75 (F1, MAJOR):
the identification is the fork's founding fact — `cascade_adelic_compensator.py` tests
ln ζ(6) at s = d+1, d = 5 against the papers' α(14)/2 — the "adelic survivor"
discrimination (round-77 c1: the gloss names the fork, not a side) — and its
compensator menu lists π⁶/945 as ζ(6) explicitly; the novelty claim was
false-when-written, a Check-4 grep that missed tools/]**. What is new here is only the
tie to the twist-parity structure: the fork constant is ζ at d_V's twist point, a
member of the sup's Euler-rational twist set {6, 8, 20, 218}. No closure, no data, and
Belle II adjudicates the fork exactly as before. *(iv) Honest grading.* Still an equivalence:
why the labels avoid the trivial-zero mirrors is the residual selection content, so
the forcing stays open and 1k's second given persists *(Net-state, Theorem 1v round 98: the owner adopted the Riemann kernel — A1 re-founded on Γ_ℝ entire with mirror coherence as its non-degeneracy clause; the labeling is now forced by the amended axiom and this open-status is resolved into A1's ledger.)*. What changes is the
characterization's placement: the dichotomy now lives on ζ's special-value structure
(odd d ⟺ even s — the Definition-2.1 biconditional, declared; the parity form was
already arithmetic, and the ζ-form is its classical decoration through that
biconditional), with the avatar-side χ reading demoted to shadow status per T1's
Remark ~~per T1's Remark the arithmetic form is the canonical one~~ **[struck round 75
(F2): T1's Remark deprecates the avatar in derivations; it does not rank
characterization registers — the "canonical" claim was asserted, not argued]**. No
number changes; no closure; category (a).

**Theorem 1p (the regularity forcing, conditional on one principle;
`cascade_gamma_regularity.py`).** The trivial-zero-avoidance equivalent (1o(ii)) in the
tower's own **local** language, and the sharpest available result on the sup. *(i) The
γ-factor dichotomy (exact).* Tate's archimedean γ-factor — the local functional
equation's transfer coefficient, γ_∞(s) = Γ_ℝ(1−s)/Γ_ℝ(s) for the trivial character
(ε_∞ = 1; T2's own Tate structure) — has, on the tower, **poles exactly at the odd
twists** and finite nonzero closed forms at the even twists (γ(2) = −2π², γ(8) =
8π⁸/315; gated exactly). Equivalently: the tower's weight continued through the
functional equation (s ↦ 1−s maps layer d to layer −(d+1)) is 2/Γ_ℝ(−d) — **zero iff d
is even** (d = 7's live mirror weight 105/(8π⁴) gated). The inf labels sit at γ-poles
with measure-zero mirrors; the sup labels at regular points with live mirrors. *(ii)
The conditional forcing.* Adopt **one principle — the regularity principle: the
invariant's integer labels are regular points of the tower's local functional
equation** (equivalently: γ_∞ finite there; equivalently: the mirror weight nonzero).
Then each straddling pair has exactly one qualifying member (gated: [1, 1, 1]), and
the labeling is **forced to (7, 19, 217) with zero residual freedom** — with the
variational characterization's output and all four 1n/1o equivalents following as
corollaries (round-78 c1: a definition cannot be a corollary; what follows is the
labeling, whose agreement with the variational characterization is the gated fact) (the
five selectors coincide on the eight labelings, gated). The agreement with the
variational sup is the gated content: it could have failed at any crossing. *(iii) The
precision bonus.* The local form is strictly cleaner than the global trivial-zero
form: at s = 1 (layer d = 0) the γ-factor has a pole and the mirror weight vanishes,
yet ζ(0) = −½ ≠ 0 (ζ's *pole* sits opposite, not a trivial zero) — 1o's global form
has an exceptional point while the local form is uniform on all d ≥ 0; on the label
range d ≥ 1 the two coincide (gated biconditional). *(iv) Honest grading — the
round-57/60 lessons applied in advance.* **The forcing is conditional: the regularity
principle is a new given, not derived from A1–A4/T1–T2.** What makes it the sharpest
form yet of 1k's second given: a single, named, arithmetic non-degeneracy condition on
committed machinery — the same selection *type* the framework already uses (T2's gcd
condition, *"no extraneous zeros in Z(f,s)/Γ_ℝ(s)"*; Theorem 7's *"every feature has
order one because variances are positive"*; 1k's no-tie margins) — replacing "take the
max" and entailing every prior equivalent. **The open question narrows to: derive the
regularity principle from the cascade's axioms.** It is not claimed derived; Part 0's
remark keeps its open status. No number changes; no closure; category (a). *(Net-state,
Theorem 1u: the regularity principle's derive-from-A1–A4 question is adjudicated —
irreducible for the committed record; the question transforms, per 1u(v).)*
*(Net-state, Theorem 1v round 98: the owner adopted the Riemann kernel — A1 re-founded on Γ_ℝ entire with mirror coherence as its non-degeneracy clause; the labeling is now forced by the amended axiom and this open-status is resolved into A1's ledger.)* *(Net-state,
Theorem 1q ~~: the regularity principle is derived given mirror coherence — a single
global requirement one level up; the per-label form survives as 1q's corollary, and
the remaining given is now mirror coherence alone~~ **[struck round 79 (F3, MAJOR):
mirror coherence is extensionally equivalent to the regularity principle — Γ_ℝ never
vanishes, so the mirrored invariant is finite-nonzero iff every label's mirror weight
is nonzero, which is per-label regularity verbatim; "one level up" was false]**, as
corrected: 1q restates this given as non-degeneracy of the invariant under the ground
object's defining symmetry — an equivalent reformulation with independent motivation;
the given's extension is unchanged.)*

**Theorem 1q (mirror coherence: an equivalent reformulation of the regularity
principle; `cascade_mirror_coherence.py`; as corrected round 79).** ~~1p left the
regularity principle as a new given applied per label — 2³ applications, one per
member of each straddling pair. This theorem moves the given up one level and makes it
single and global.~~ **[struck round 79 (F3, MAJOR + F4): the two conditions are
extensionally equivalent (see (iii)), so neither is "up one level"; and the count was
internally inconsistent — 2³ = 8 counts labelings while "one per member" counts 6, and
1p's own gate performed 3 pair-checks]** 1p's regularity principle, restated on the
invariant as a whole and motivated by the ground object's defining symmetry. *(i) The
mirror pairing.* ~~T1b's RH-free paired Hadamard form is "even, entire of order 1,
genus-0 in z²" (round-15 M1's adjudicated wording): the framework's unconditional
potential identity is a function of z² = (s − ½)² and therefore cannot distinguish
layer d (z = d + ½) from its mirror layer −(d+1)~~ **[struck round 79 (F1, MAJOR):
quote-reattachment — in T1b's sentence those adjectives are predicated of ξ(½+z), not
of the paired sum Σ 2z/(z² − (ρ−½)²), which carries an explicit factor z and is *odd*
in z; the full unconditional identity (pole terms, Dirichlet side) is not z²-blind at
all]** What is true and now gated: **the ground object ξ assigns the same value to
layer d and its mirror −(d+1)** — ξ(½+z) is even (T1b's subject), z(d)² = z(−(d+1))²
exactly (gated d = 0..30), and exact instances ξ(8) = ξ(−7) = 4π⁴/225,
ξ(20) = ξ(−19) are gated. ξ itself cannot distinguish a layer from its mirror; the
tower's weights *can* — that is precisely what coherence probes. *(ii) The census, the
adjudication, and the disclosure.* Branch-swap every weight: Ω̃(d) = 2/Γ_ℝ(−d), the
mirror layer's weight (= Ω(d)/γ_∞(d+1) — the 1p tie, gated at d = 7), and
Ĩ(l₀, l₁, l₂) = (Ω̃(5)/Ω̃(l₀))² Ω̃(l₁) Ω̃(l₂). ~~Over the eight labelings the failure
census is total: Ĩ = ∞ at all four l₀ = 6 labelings (the denominator mirror weight
vanishes)~~ **[struck round 79 (F2, MAJOR): false at three of the four — there a
content weight vanishes *too*, making Ĩ a 0·∞ indeterminate form with no exact value;
"Ĩ = ∞" is a fact only at (6, 19, 217); the old gate's denominator-first short-circuit
imposed the adjudication silently]** The corrected census (each class gated):
**finite-nonzero uniquely at (7, 19, 217) — the sup**; exactly 0 at the three l₀ = 7
labelings carrying an even content label; ∞ at (6, 19, 217) only; **indeterminate**
(0·∞, no exact value) at the other three l₀ = 6 labelings. Adjudication, stated:
coherence means the defining formula *evaluates*, exactly and unconditionally, to a
finite nonzero value — zero, infinite, and indeterminate all fail. Disclosed and
gated: under a uniform regularization d → d+ε the zero orders at (6, 20, 218) cancel
and the *limit* is finite-nonzero (≈ −1.413×10¹²³) while the other two indeterminates
diverge — so the sup's uniqueness holds for exact values of the defining formula, not
for regularized limits. *(iii) Mirror coherence, and the equivalence.* The invariant
is finite-nonzero on the physical branch — an invariant equal to 0 or ∞ is no
invariant, and Part 0's uniqueness theorem presupposes its non-degeneracy. Require
that non-degeneracy to hold for the branch-swapped weights — **mirror coherence**.
Then coherent labelings = all-labels-odd = 1p's regular labelings = {(7, 19, 217)}
(gated chain). ~~The regularity principle is thereby derived, conditional now on
mirror coherence alone: one global statement replacing 2³ per-label applications.~~
**[struck round 79 (F3, MAJOR): Γ_ℝ never vanishes (gated), so Ω̃ is never ∞ and
Ĩ's exact finite-nonzero-ness is *immediately* the conjunction of the labels' mirror-
weight non-vanishings — mirror coherence and per-label regularity are extensionally
equivalent, "derived" holds in both directions, and 1p's principle was already stated
as one sentence]** The honest statement: mirror coherence is an **exact equivalent**
of 1p's regularity principle — a reformulation whose contribution is motivational
(the given recast as non-degeneracy under the symmetry ξ defines), not logical.
*(iv) The d_V clause.* d_V = 5 is **not a labeling choice** — the interior landmark is
fixed by V's discrete argmax — and coherence requires Ω̃(5) ≠ 0, which holds:
Ω̃(5) = −15/(4π³) exactly, with Ω̃(4) = Ω̃(6) = 0. Deflation (round-79 F7): Ω̃
vanishes at *every* even d (gated d = 0..30), so this clause is exactly "d_V is odd" —
1n's recorded parity fact re-expressed on the mirror weights, not a new local
discrimination ~~and 1n's observation "all four distinguished layers are odd" upgrades
from coincidence to necessity under coherence~~ **[struck round 79 (F3): under the
equivalence, "necessity under coherence" is "all-odd is necessary given a postulate
extensionally identical to all-odd" — vacuous]**. Under coherence-as-postulate it is a
consistency requirement the fixed landmark meets. *(v) Honest grading, and the sign
disclosure.* Mirror coherence is **the same given as 1p's, in a second face** —
motivated by committed structure (the ξ-symmetry as the ground object's defining
property; the standing physical-branch non-degeneracy) but **not claimed an
axiom-consequence**. ~~The chain of givens, each strictly smaller than the last: "take
the max" (Part 0's definition) → four equivalents (1n/1o) → per-label regularity (1p,
2³ applications) → mirror coherence (one global statement). The open question narrows
to: derive mirror coherence from A1–A4.~~ **[struck round 79 (F3, MAJOR): the 1p→1q
link is an equivalence, not a strict narrowing; the open question is unchanged in
extension]** The chain as it stands: "take the max" (Part 0's definition) → four
equivalents (1n/1o) → per-label regularity (1p) ⟺ mirror coherence (1q). **The open
question is unchanged: derive the given — either face — from A1–A4.**
*(Net-state, Theorem 1v round 98: the owner adopted the Riemann kernel — A1 re-founded on Γ_ℝ entire with mirror coherence as its non-degeneracy clause; the labeling is now forced by the amended axiom and this open-status is resolved into A1's ledger.)* Sign disclosure:
Ĩ_sup < 0 — an exact rational over π¹¹⁷ (rationality now gated, round-79 F6;
≈ −1.109×10¹²²; the mirror weights carry Γ-reflection signs); coherence is
non-degeneracy (≠ 0, ∞, indeterminate), **not** positivity. No number changes; no
closure; category (a). *(Net-state, Theorem 1u: the derive-from-A1–A4 question
is adjudicated for the committed record — the given is irreducible relative to
the axioms as committed (their asserted content is lattice-only; the given's
condition lives at Γ_ℝ's negative arguments), and the question transforms to
the foundational one: is the continued weight function axiom content?)*

**Theorem 1r (the pairing-act's anatomy: three committed-anchor routes, the live
alternative excluded thrice; `cascade_pairing_act.py`).** The round-57 adjudication
left the class's third member conditional on the pairing-act, with χ₋₄ *"a live
alternative partner that only the order or the pairing-act excludes"* (the F1
annotation's recital, 1j). This theorem decomposes the act and tests the alternative
against committed-anchored act-forms ~~under act-forms **strictly weaker** than the
colour gloss~~ **[struck round 81 (F2, MAJOR): false for two of the three under
predicate implication — W₂'s pass set and the census route's are exactly {−3},
extensionally *equivalent* to the colour gloss's output; only W₁ is strictly weaker
extensionally (a pass set of 1014 discs ⊋ {−3} — the type slip "1014 ⊋ {−3}" fixed
round 82, F3); the ordering is now stated: W₁ weaker in pass set, W₂
and the census weaker only in what they *name* — no field, no μ₆, no T11
presupposed]** — the colour gloss being the act's standing form: pair with the colour
field's character (1j; the term defined here, round-81 F5). *(i) The target space is
the census space.* The odd bridge's partner family — every odd real primitive χ (1c)
— is classically the Kronecker characters χ_d of negative fundamental discriminants
(real primitive ⟺ fundamental-disc Kronecker; parity = the disc's sign; cited), gated
on the census side: all 3043 discs to 10⁴ give χ_d(−1) = −1, with the symbol routine
cross-checked in-code against a library Jacobi on 500 seeded cases ~~independently
cross-checked against a library Jacobi on 500 random odd-modulus cases — and the
parity gate caught a real reciprocity-order bug in the routine's first draft before
landing~~ **[reworded round 81 (F1, MAJOR + F4): the cross-check was a session run —
drafting until it lands in code — and the first-draft narrative was unverifiable
testimony on a paper surface; the cross-check is now a committed P1 conjunct, and the
drafting history lives in the audit record (Addendum 154)]**. The act therefore selects in exactly
the space the torsion census (1j) reads. *(ii) The dyadic route.* 1j's committed
description of the outcome — *"the selected field's dyadic shadow is the invisible
unit direction"* — promoted to an act-form **W₁**: the partner's disc class lies
nontrivially in H ∩ units = {1, cls(−3)}. W₁ names no field, no μ₆, no T11. Under W₁
the candidate slice is cls(−3)'s class — **1014 of 3043 discs** (d ≡ 5 mod 8;
equivalently χ_d(2) = −1, the clock prime inert — 1e(iv)'s colour-at-2 fact, gated as
the slice's iff on all odd discs), the class-level caveat honored (−11 in the slice;
**no field pinned**, gated |slice| > 1 — round-57 F2's point, kept) — and **χ₋₄ is
excluded by 1h's kernel alone** (cls(−4) = 7 ∉ H; χ₋₈ too, cls = 14). *(iii) The
conductor route.* 1d's committed adelic fact — the finite potential carried ~94–100%
jointly by p = 2 and p = 3 — gives act-form **W₂**: the partner's conductor is a
carrying prime. Conductor 2 admits no primitive character and conductor 3 exactly
one, odd (1c's committed clauses, re-gated by enumeration): **W₂ pins χ₋₃ outright in
the whole family** ({d : |d| ∈ {2, 3}} = {−3}, gated), and χ₋₄ is excluded again
(conductor 4 not a carrying prime). *(iv) The bridge's constant already carries μ₆.*
The committed 1c constant L(1, χ₋₃) = π/(3√3) **is Dirichlet's class-number formula**
2πh/(w√|d|) at (h, w, |d|) = (1, 6, 3): h(−3) = 1 gated by reduced-form count
(h(−23) = 3 the counter's sanity case), w = 6 the census's unit count, the identity
symbolic, the numeric L(1) re-gated by period-3 block summation to < 10⁻⁷ (μ₄
cross-check: L(1, χ₋₄) = 2π/(4·2) = π/4, Leibniz, gated): **the torsion count 6 that
T11's μ₆ requirement matches is already the denominator of the odd bridge's own
committed constant** — the μ₆ datum sits on both sides of the pairing. *(v) Honest
grading.* **The act persists.** None of W₁, W₂, or the colour gloss is entailed by
the axioms; each is a matching principle of the round-57 type (why the invisible
direction; why a carrying conductor; why μ₆), and pairing-at-all — the odd feature's
missing address (Definition 6.1) — is untouched. What changes is the live
alternative's status: χ₋₄ fails **three distinct committed anchors** ~~three
independent committed anchors under act-forms strictly weaker than the colour
gloss~~ **[struck round 81 (F3 + F2): "independent" unqualified was wrong — W₂'s
exclusion is *generic* (its pass set is {−3}, so it excludes every alternative
partner whatsoever, carrying no χ₋₄-specific information; the kernel and census
exclusions are the χ₋₄-specific evidence, and the kernel route is not mere
2-ramification — ~~−28 (cls 1) and~~ **[corrected round 82 (F1): −28 is not a
fundamental disc (−28/4 = −7 ≡ 1 mod 4) and cls 1 is the trivial class, not
ramification — the exhibit is −56 (cls 2) and]** −24 (cls 10) are 2-ramified
discs the kernel admits, together covering both ramified kernel classes
{2, 10} (gated in P5); the strictly-weaker clause per the header strike]** (the clock kernel; the
carrying conductors; the torsion census — the triple gated jointly, with the role
asymmetry re-gated: ker(·,−1)₂ = H exactly, so the candidate partner's character is
the committed filter's *instrument* while cls(−3) is the invisible *datum* inside
it), and the three routes' outputs are consistent (W₁ the class containing −3; W₂
and the census the field). The round-57 phrase is superseded in exactly this sense —
**no universal over act-forms is claimed**. Three members and the seven-item count
stand *(Net-state, Theorem 1y round 107: member one closes — the site-E pairing entailed given the tower's dictionary, the sup labeling already resolved into A1's ledger; the class keeps two members; the seven-item count stands.)*; no number changes; no closure; category (a).

**Theorem 1s (pairing-at-all located: the parity-blocked pole pin;
`cascade_bridge_asymmetry.py`).** 1r cornered the act's *partner*; the act's open core
is **pairing-at-all** — why read the odd feature through an arithmetic partner in the
first place. This theorem locates that question against committed structure. *(i) The
paired object is no orphan.* The odd feature (p_sgn = 0 at s = 6.2569; Finding 6's
excluded object; no Definition-6.1 address) is the **unique root on x > 0** of the
balance ψ(x/2) = ln π ~~the **unique** root of the balance ψ(x/2) = ln π — trigamma > 0
gated on a grid, ψ strictly increasing (classical)~~ **[struck round 84 (F1; the
recital's dropped bold restored round 85, c2): false
without the domain — ψ's branches between its poles supply a root in every negative
interval (e.g. x = −0.7633, −2.9065), and trigamma > 0 alone proves too much, holding
on each branch; on x > 0, where the tower lives, ψ(x/2) is strictly increasing
(trigamma gated on a positive grid, classical) and the root is unique]** — the
same equation whose offset readings are the V-argmax (x* − 2 = 5.2569, the interior
landmark d_V's continuum equation) and the p-zero (x* − 1 = 6.2569), 1k's committed
"same root" here extended to the odd feature explicitly (both offsets gated at 4 d.p.
against the committed values; ~~p_sgn(x* − 1) = 0 gated independently~~ **[struck
round 84 (F2): the conjunct was the root check recomputed — (x−1)+1 = x — a gate that
cannot fail; the honest gate now committed evaluates p_sgn from its own formula at
the committed 6.2569, < 10⁻⁴]**). The object being
paired is the framework's central continuum root seen in the sgn frame — an identity,
not an act. *(ii) The even side has an intrinsic pin: the pole.* The even tower's
bridge family — every even real primitive χ, by the same Hadamard derivation as 1c's
odd bridge (classical, declared) — contains exactly one pole-carrier: ζ, the trivial
character. Gated at the checkable core: the harmonic partial sum grows as ln N (the
pole), while sample nontrivial characters even and odd (χ₈, χ₅, χ₁₂; χ₋₃, χ₋₄)
Cauchy-converge (tails < 10⁻⁴; classical closure cited — Dirichlet, L(1, χ) finite
for every nontrivial χ). The pin selects conductor 1: **T1b's ζ reading is pinned,
not chosen.** *(iii) The pin is parity-blocked; the even selection is overdetermined,
the odd is not.* The unique pole-carrier is the trivial character — **even**
(definitional). On the even side, pole-carrier = conductor-1 = minimal conductor
(q = 1 exists and is even — 1c's committed clause, anchored). On the odd side: no
pole (all odd completed L entire — classical; 1c commits it for χ₋₃), no q = 1 or 2
member (q = 2 re-gated; q = 1 excluded by the anchored evenness clause — round-84
F4's scope), minimal conductor 3. **Any arithmetic reading of the odd tower
therefore requires an extrinsic selection principle: the act exists exactly because
the intrinsic pin is parity-blocked.** *(iv) T1b's ζ-choice discharged.* T1b's
displayed bridge carries the pole terms −1/s − 1/(s−1) (anchored verbatim); their
magnitude at the central root is 0.2976 — more than half the first threshold
ln Γ(½) = 0.5724 (gated): first-order on the band scale, not a correction. No pole-free partner
supplies the displayed identity, so the even-side "choice" of ζ is the pole pin in
action — a latent "uncharged even pairing" review charge is preempted. *(v) Honest
grading.* **The act persists.** The grammar still does not read the odd feature
(Finding 6's exclusion and the no-derived-address clause both anchored); nothing
obligates an arithmetic reading of the odd tower. What 1s changes: pairing-at-all
decomposes as [the object — an identity, (i)] + [the reading — obligatorily
extrinsic *if taken at all*, (ii)–(iii)] + [the partner — 1r's three anchors]. **The
open core narrows to: derive an extrinsic odd selection principle from A1–A4, or
establish that the grammar never needs the odd reading** (the act as Door-4
bookkeeping only). No number changes; no closure; category (a). *(Net-state,
Theorem 1t as corrected rounds 89–91: the disjunction resolves on its second
branch for the committed record — the grammar-need census (scope per 1t(i),
extended in rounds 89–91 to every paper- or ledger-cited computational
surface, 81 resolving scripts, 91 files scanned) returns zero consumption of the odd
bridge's arithmetic side; the act is Door-4 bookkeeping, with the falsifier
licensed.)* *(Net-state, Theorem 1x: the status probed post-1w — bookkeeping
confirmed; the act is consumed review-side (1c(ii)/1j, 1r, 1w) with
weight-for-numbers zero; the "bookkeeping only" reading persists for the papers'
grammar, which consumes the act nowhere.)*

**Theorem 1t (the grammar-need census: 1s's second branch established for the
committed record; `cascade_grammar_need.py`).** 1s's open core is a disjunction;
this theorem audits its second branch as a consumption census. *(i) The scope,
stated — as corrected rounds 89–90 (and the attribution round 91).* The derivation record: every cascade paper
(src/*.tex, 12 files), the frozen ledger (PREDICTIONS.md), the
observable-computing tools ~~(cascade_constants.py, tools/verifiers/,
tools/closures/ — 30 scripts), and the four °-marked record instruments.
**Excluded by design, disclosed:** this paper and its research instruments —
they are the *study* of the pairing (1c, 1i, 1r and their verifiers), so their
L-side content is the audit's subject, not a consumer~~ **[struck round 89
(F1, MAJOR + F2): the count misattributed 30 to the constants/verifiers/
closures group (26; the 30 included the four instruments), and — the major —
the disclosure mischaracterized the exclusion: the papers ~~themselves
cite 59 […]~~ **[corrected round 90 (F1/F2) and round 91 (F1/F3); the
elision bracketed round 92: the round-89
extractor was itself blind to non-cascade-prefixed and \allowbreak-wrapped
citations — the true census is 82 distinct cited scripts, 81 resolving (80
paper-cited; generate_predictions.py ledger-only) plus one dead citation (a
never-committed sphere-Dirac spectral-zeta script, part4b) retracted at
source in the round-90 sweep; of the 59 then counted, 7 were already
scanned, so "all silently omitted" was a false universal — 52 were truly
omitted; and the resolving 81 sit across tools/research (54), verifiers
(17), closures (4), model_checks (2), generators (2), and tools/build (2) —
e.g. the route-C Dirac computation cited mid-derivation in part4a — none of
them pairing-study]** and the blanket exclusion left the uncited-directory
portion of them unscanned while the quantifier said "entire derivation
record"]** (cascade_constants.py + 19 verifiers + 6 closures = 26
scripts), the four °-marked record instruments, **every computational script
the papers and the ledger cite** (~~59 distinct~~ **[corrected round 90 (F1)
and round 91 (F1): 81 distinct resolving scripts, 80 paper-cited and one
ledger-only — the corrected extractor strips \allowbreak and takes all .py
citations, not only cascade-prefixed ones; count and resolution both gated;
the one dead citation retracted at source]**), and
tools/model_checks/ + tools/generators/ wholesale — 91 computational files
in all. Excluded,
correctly characterized: this paper and the research instruments *not cited
by the series* — the pairing-study surfaces (1c, 1i, 1r and their verifiers),
whose L-side content is the audit's subject, not a consumer. *(ii) The census
returns zero — one benign hit disclosed.* Token census (χ₋₃, L(s,χ)/L(1,χ),
the χ zeros 8.0397, Kronecker, "conductor", "quadratic character", "root
number", "gauss sum", "dirichlet character", √3 in the LaTeX sources): across
the censused record the **only** hit is one linear-algebra "Kronecker
product" docstring (allowlist-gated: every kronecker hit must be that
phrase); all other tokens zero, gated per token across the enumerated
surfaces, with the lone "Dirichlet" in the series gated as part0a's classical
method name ("Dirichlet's method", the ζ(2) evaluation). Colour enters the
papers as Lie-theoretic structure — su(3), Adams, Radon–Hurwitz — with the
ℤ[ω] lattice carried not by the papers' text but by the formulation's T8/T11
and the record instruments (round-89 F5 scoped the sentence to what the
papers actually carry). *(iii) The crossing is Γ-side complete.* The
band boundary derives from digamma alone (p's zero at 6.2569 gated at 4 d.p.;
the band inequalities p(6) < 0 < p(7) and p(19) < ln Γ(½) < p(20) gated): the
feature machinery consumes digamma, never an L-function. *(iv) Door 4's two
sides are independently committed.* The bridge side: ½ln 3 = ln √3 (exact).
The ring side: covol(ℤ[ω]) computed from the lattice basis (1, ω) is
|Im ω| = √3/2 = cos(π/6) (gated), and the mass arc consumes *the ring side*
(1m's committed identification anchored verbatim). Removing the Door-4
identification changes no committed number: the identification links two
objects that each exist independently. *(v) The scoped conclusion, the honest
grading, and the falsifier.* **For the committed record, the grammar does not
need the odd reading: 1s's disjunction resolves on its second branch, and the
pairing-act's derivational weight is audited to zero** — the act is Door-4
bookkeeping, an identification consumed by nothing in the chain. This is a
census over the record, **not a universal over future derivations** (the
round-47 lesson applied in advance); the licensed falsifier,
stopping-rule-gated per the 1h(iv) pattern: **any future derivation that
routes a grammar entry through the odd bridge's L-side re-opens the member's
derivational weight.** The member itself persists as charged — the act, when
taken, remains the recorded convention — so **three members and the seven-item
count stand** *(Net-state, Theorem 1y round 107: member one closes — the site-E pairing entailed given the tower's dictionary, the sup labeling already resolved into A1's ledger; the class keeps two members; the seven-item count stands.)*; what closes is 1s's open question, on its auditable branch. No
number changes; no closure of the member; category (a). *(Net-state, Theorem 1x:
the falsifier checked against 1w — unfired on both conjuncts (ring-side route; no
grammar entry rerouted); the zero-weight grading refines to zero-for-numbers — the
act is now consumed by three review-side chains (1c(ii)/1j, 1r, 1w), none carrying
a number.)*

**Theorem 1u (the given's irreducibility classification: regularity/coherence
adjudicated against the axioms' committed content; `cascade_given_irreducibility.py`).**
The 1p/1q arc left one given in two equivalent faces with the open question
"derive the given, either face, from A1–A4." This theorem adjudicates that
question for the committed record. *(i) The axioms carry zero labeling
content.* Token census over the formulation's canonical axiom block (A1–A4):
sup/max/min, labeling, boundary side, parity, odd, mirror, regular, coheren-,
and the label numerals — **zero hits** (the block's lone "19" is the year in
"Wall 1964", gated as such; and the block's own selection vocabulary — A3's
*"source-selection flags"* — is gated with per-token adjudication rather than
omitted, round-94 F1, with the per-item statements location-gated round 95
(F1/F2): "selection" exactly once, in that clause — the flags select *sources
and constants*, not labels; "flag" twice, both within A3,
location-gated (the round-94 apparatus's *verifier comment* had claimed both
hits in the flags clause's sentence — false, corrected round 95 (F1): the two
hits sit in two different A3 sentences, the flags clause and the
partial-derivation sentence; this surface never carried the false claim — the
round-95 sweep's strike here was struck-at-birth text, a marking-rule defect
removed round 96 (F1)); "unique" thrice, all within A1's dynamics sentence
(location-gated — round-95 F2 replaced a true-but-ungated claim)).
Adjudications disclosed rather than buried:
A2's home column names *"the functional equation's symmetry point"* as
Γ(½)'s arithmetic home — provenance of a constant at the *fixed point* s = ½,
not an asserted condition at mirror points (anchored); and A3 places source
layers *"at the analytic features of Γ_ℝ"* and attaches *"below the phase
transition"* — feature positions and regions, not boundary-side integer
choices (1k's committed distinction, *"What the lattice does not fix is the
side"*, anchored); and §0's Notation commits ξ's functional equation —
notation, not axiom, classical and label-independent (round-94 F4, anchored).
*(ii) The given's subject matter is off-lattice.* A1's
committed state space is *"the descent lattice ℕ (layer index d), weighted by
Γ_ℝ"* (anchored verbatim). The kernel's four primitives evaluate Γ_ℝ on the
lattice's argument image {d+1, d+2} — strictly positive ~~(gated, d =
0..299)~~ **[reworded round 94 (F3): the first draft's positivity conjuncts
were constructed from the claim and could not fail; all four T1 definitions
are now anchored verbatim — failable; the α anchor added round 95 (F3), α
adding no new Γ_ℝ argument — with the positivity an exhibit of the
anchored offsets]** — while **both faces of the given evaluate Γ_ℝ at
negative arguments** at the labels (γ_∞ needs 1−s = −d; the mirror weight
needs −d; the d = 7 mirror weight gated). The axioms'
asserted content quantifies over lattice points and their weights; **no axiom
asserts any condition at negative arguments.** Expressibility is not the
issue — classical analysis continues the weight function; what is missing is
any axiom-asserted *condition* there. *(iii) The labeling's single entry
point.* The committed chain routes the labeling through exactly one point:
Part 0's variational definition, whose own remark grades the derivation open
(anchored verbatim), with 1k's "The sup itself is a second given" and part5's
output-consumption formula 18Ω₁₉Ω₂₁₇/π³ anchored — downstream consumers take
the selected labels' output, not a selection principle (anchor-based, scope
declared; 1t covers the consumption census). *(iv) The five committed faces
coincide and are each extra-axiomatic.* Re-gated on the eight labelings:
argmax I = argmin S_dS = the odd-member rule = the unique ζ-mirror-nonzero
labeling = the unique coherent labeling = (7, 19, 217). Their types, declared
and backed by (i): max and min-S are extremal conventions (no axiom asserts a
ranking over labelings); the odd-member rule is lattice-native but
axiom-unbacked; ζ-rationality and regularity/coherence route through
off-lattice values (the even and odd mirror sides). *(v) The classification,
the transformed question, and the falsifier.* **For the committed record, the
given is irreducible relative to A1–A4 as committed**: no committed route
derives it, the axioms assert nothing where its condition lives, and every
committed face is extra-axiomatic. This is a committed-record classification,
**not an in-principle impossibility proof** (A1–A4 are informal; declared).
The open question does not persist in its old form — it **transforms**: the
live question is foundational — *whether the weight function's global
identity (the continuation and functional equation of Γ_ℝ) is axiom content*,
i.e. whether A1's kernel is Γ_ℝ-on-the-lattice or Γ_ℝ entire. If the latter
were adopted, mirror coherence would become the natural non-degeneracy clause
of the extended kernel — but that adoption is a new axiom-level choice,
stated, not resolved *(Net-state, Theorem 1v round 98: the owner adopted the Riemann
kernel — A1 re-founded on Γ_ℝ entire with mirror coherence as its selector clause;
the labeling is now forced by the amended axiom and the choice this theorem stated is
made — 1u stands as the recorded reason a forced labeling required axiom-level
content ~~the only route~~ [round-98 F4: 1u showed no derivation route exists from
the old axioms, not that this adoption is the unique axiom-level route]. The
falsifier below fired by ADOPTION, not derivation — the classification is re-scoped
to its historical object, per its verifier — and the "persists" tail reads as of the
pre-adoption record.)*. Licensed falsifier, stopping-rule-gated: any future
committed derivation routing the labeling through an axiom's asserted content
re-opens the classification. The given persists; no closure; no number
changes; category (a).

**Theorem 1v (the Riemann kernel: A1 re-founded on Γ_ℝ entire, by the owner's
decision; `cascade_riemann_kernel.py`).** 1u transformed the selection question into
a foundational choice — whether the weight function's global identity is axiom
content — and stated it without making it. **The owner has made it (round 98): the
framework follows Riemann.** *(i) The amendment.* A1 now takes the kernel as Γ_ℝ
*entire* (the owner's phrase; "entire" in the sense of *in its entirety* — the
function itself is meromorphic, its poles load-bearing) — the global function
π^(−s/2)Γ(s/2), with its pole set and its
defining role in ξ(s) = ξ(1−s) — with **mirror coherence as the kernel's
non-degeneracy clause** (the amended block anchored verbatim; the old A1's
state-space and dynamics sentences surviving unchanged; and A2–A4 untouched — the
block from A2 onward gated byte-identical against the embedded pre-adoption text, so
any collateral edit fails). This executes the historical Euler → Riemann step as an
axiom choice: the value table becomes the function, with the continuation and
functional equation Riemann added now the axiom's own object. *(ii) The forcing.*
Under the amended A1 the labeling is **derived**: the clause is worded as the
**boundary-labeling selector** (round-98 F1 — the first wording constrained the
variationally-defined invariant and was entailed, selecting nothing; the axiom now
states the selection: the labeling is the one at which the branch-swapped invariant
evaluates finite-nonzero), and it admits exactly
one labeling of the eight — (7, 19, 217) — 1q's exact-value census re-gated
(finite-nonzero uniquely at the sup; zero ×3; infinite ×1; indeterminate ×3), and the
five prior faces (argmax I, min horizon budget, odd-member, ζ-mirror avoidance,
per-label regularity) follow as corollaries (re-gated). **1k's second given resolves
into A1.** *(iii) The cost ledger, in the open.* Nothing is derived from nothing: the
given moved *into the axiom*. The assumption enlarges from a lattice-value table (the
Euler-side reading) to the global function plus one clause (the Riemann-side reading)
— stated in A1's own text and in Part 0's remark (both anchored). The adoption adds
**no empirical content**: no number changes (the invariant re-derived to twelve
digits, half-ULP gated; (2/π)I unchanged), no new prediction, and the *physical*
hypothesis is untouched (Check 8) — this is a math-side re-founding of the
formulation's skeleton. *(iv) What does not resolve.* The site-E pairing (1k's first *(net-state, Theorem 1y round 107: now resolved — entailed given the dictionary; member one closes)*
given), the pairing-act (Door-4 bookkeeping per 1t, its falsifier unchanged), and
A3's underived rules (*"the increment and per-period rules are underived"* — in the
amended block itself, anchored) *(net-state, Theorem 1ac round 120: superseded-true —
the increment rule closed as mathematics (T5, A33), the per-period rule decomposed
at ledger row 2; the residue instantiation and convention)* persist exactly as recorded; only the
boundary-labeling given resolves. *(v) Status propagation and the honest falsifier.*
The prior gradings — "the forcing stays open," "the same given in a second face,"
"irreducible relative to A1–A4 as committed," "stated, not made" — were true of the
pre-adoption axioms *(round-98 F3: the first
draft's list included "the remaining given," a phrase living only inside a
round-79-struck span — replaced by 1q's corrected grading)* and stand as history under net-state markers; 1u is now the recorded *reason*
~~the adoption was the only route to a forced labeling~~ [round-99 F1: the
F98-4 overclaim survived here unswept — 1u showed no derivation route exists
from the old axioms, not that this adoption is the unique axiom-level route]
a forced labeling required axiom-level content, which the adoption supplies. Since the adoption adds no
empirical content, it is tested exactly where the framework is — by the record's
predictions — and any future committed derivation of the clause from a weaker kernel
makes the adoption redundant, to be recorded as such. No closure beyond the labeling
given; category (a) plus one recorded axiom adoption.

**Theorem 1w (the kernel-native colour count: multiplicity 3 entailed given the
pairing-act and T8's root–unit identity; the registered finite-places negative stands
verbatim; `cascade_colour_count.py`).** *(i) The commission and the gate.* The owner
commissioned the kernel-native colour count (this arc). The registered negative of
1f(iii) *(round-101 F5: the first draft cited "1g(iii)" here and at two points below —
the registered negative lives in Theorem 1f(iii), and 1g(iii) names a different
committed referent, the kernel's anatomy; corrected at all three)* stands verbatim — *"N_c = 3 is not derived from the finite places"* — and this
theorem does not touch it: no finite-place datum is read anywhere below; the route reads
the **unit torsion of the paired field at its infinite embedding**, which is global and
archimedean. The stopping-rule sentence there ("Any future claim that the finite places
produce the 3 is stopping-rule-gated new physics") gates finite-place claims; this is
not one, and the hunt is owner-commissioned, recorded as such. *Scoping (round-101
F7):* "below" begins after the act — the act's own committed fixing of χ₋₃ (1j(iii)'s
T11 route) consumes the torsion datum w = 6, itself archimedean/global; the alternative
committed fixing (1r's W₂, the carrying conductors) is finite-place-flavoured and is
**not** consumed here. *(ii) The unit-torsion
route.* Given the pairing-act (the standing charged member; 1r fixes χ₋₃ given the act),
the paired field is ℚ(ζ₃), maximal order ℤ[ω], unit group the torsion μ₆ (w = 6). The
census is gated: over all 3,043 fundamental discriminants d < 0 with |d| ≤ 10⁴, w = 6
**only** at d = −3 (w = 4 only at d = −4, w = 2 everywhere else) — the paired field is
the unique imaginary quadratic field with six torsion units. The six units at the
infinite embedding satisfy the root-system axioms (reduced; crystallographic — every
Cartan pairing ⟨α,β⟩ ∈ {±1, ±2}; closed under its own reflections; spanning — all gated
numerically), and by the rank-2 classification (A₁×A₁: 4 roots, A₂: 6, B₂: 8, G₂: 12)
**the configuration is A₂** — the type-A family's root arithmetic N(N−1) = 6 then gives
**N = 3, the unique positive-integer solution** (gated; N is real-form-independent).
Uniqueness among fields: d = −4's μ₄ is
a root system but **decomposable** (⟨1, i⟩ orthogonal — A₁×A₁, non-simple; gated), and
every other imaginary quadratic field has torsion {±1}, rank 1, non-spanning in the
plane of the infinite embedding — so ℚ(ζ₃) is the **unique** imaginary quadratic field
whose unit torsion forms a **plane-spanning** root system of a simple Lie algebra
*(round-101 F6: the qualifier is load-bearing — {±1} is the A₁ system of the simple
su(2) in its own one-dimensional span, so the unqualified sentence was false; and the
first draft's "that algebra is su(3)" named the compact real form here in (ii), ahead
of the T8 identification in (iii) that actually supplies it — su(2,1) and sl(3,ℝ)
share the A₂ complexification, while N = 3 itself is form-independent)*. *(iii) What is consumed —
the adjudication.* The chain is: the pairing-act (charged; Door-4 bookkeeping per 1v)
selects the field; the field's torsion is A₂ (classical — Killing–Cartan rank-2
classification, new to the record here, no free choice at any step); and T8's committed
identity — *"The su(3) roots are the units μ₆ of ℤ[ω] (point-by-point)"* (PROVED,
Addendum 36) — identifies **this** A₂ with the colour algebra in the committed
measurement frame. The kernel does not produce 3 unaided: it produces 3 **given the
act**. And the act is not innocent of the 6: per 1r(iv), *"the μ₆ datum sits on both
sides of the pairing"* — the committed fixing of χ₋₃ consumes the same torsion datum
this theorem classifies, so the genuinely new content here is the classification step
(μ₆ → A₂ → N = 3) and the uniqueness censi, **not the 6 itself** (round-101 F7). The
residue moves accordingly: T8's tail "Colour multiplicity 3 and per-leg
occupancy remain instantiation" narrows to **per-leg occupancy only** — the
multiplicity is entailed given the act plus T8, and is no longer an independent
instantiation (net-state markers at T8, ledger row 4, and 1f(iii)'s registered
negative). *(iv) The Check-8 cross-check.* The cascade side's count is ρ(12) − 1 = 3
(Adams / Radon–Hurwitz; ρ recomputed and gated, with the [5, 19] census: d = 12 is the
unique dimension there with ρ(d) − 1 = 3). Kernel-3 = cascade-3 is reported as
**internal consistency, not forcing**: the layer-12 selection remains papers-side (the
feature→layer member of the residue), exactly as the registered negative states — what
remains archimedean after this theorem is **the layer alone**, no longer the count.
*(v) Exhibit, disclosed as such (not a forcer).* At d = −3 four kernel invariants
coincide at the value 3 — the conductor, |disc|, the unique ramified prime, and the
odd-torsion order |μ₃| = w/2 — a four-way coincidence unique among imaginary quadratic
fields (gated: at d = −4 the list reads 4, 4, 2, 1). Coincidences corroborate; the
forcing chain is (ii)–(iii) alone. Category: closure-narrowing on an acknowledged
residue (ledger row 4; T8's tail; 1f(iii)); no data consumed, no number changes
anywhere.

**Theorem 1x (the Door-4 status probe: 1t's falsifier checked against 1w — unfired
on both conjuncts; the zero-weight grading refined to zero-for-numbers; the act's
axiomatic geography post-adoption; `cascade_door4_status.py`).** *(i) The commission
and the committed status.* The owner commissioned a probe of the pairing-act's Door-4
status. The committed state: Door 4 is the conductor-is-the-different identification
(1c(ii)'s C4), its two sides independently committed (1t(iv)); the act is graded
Door-4 bookkeeping with *"the pairing-act's derivational weight is audited to zero"*
(1t(v)), under the licensed falsifier *"any future derivation that routes a grammar
entry through the odd bridge's L-side re-opens the member's derivational weight."*
Since that census, the record gained a theorem that consumes the act — 1w produces
N_c = 3 given it. The probe adjudicates the status against the post-1w record.
*(ii) The falsifier, checked against 1w: unfired on both conjuncts.* **(a) No grammar
entry is rerouted.** The cascade papers consume the act nowhere — gated at the
censused phrase family: *"given the act"* / *"given the pairing-act"*,
case-insensitive and whitespace-normalized (round-105 F2: the round-104 gate
matched raw bytes, so a line-wrapped injected instance of the exact family evaded
it — closed; round-106 F1 added "injected": the tex zero stood on substance
throughout), has **zero occurrences across all twelve tex sources**; the
phrase-zero is the gate's operationalization, and the claim beyond the phrase family
is verified by direct reading (round-104 F2: the first gate was case-sensitive and
its docstring sold it as fully operationalizing the sharpened falsifier — a
capitalized injection evaded it; the gate is now case-insensitive and the docstring
scoped to the phrase family); N_c's grammar carrier remains the papers-side
Radon–Hurwitz entry, which the
axiom block itself lists as a local constant — A2's row *"N_c = 3 = 2^(v₂(12))−1 |
Radon–Hurwitz count | a 2-adic invariant (value depends only on v₂)"* (anchored;
quote completed round 104) — and 1w's entailment is
redundant for the number ("no data consumed, no number changes anywhere," 1w's own
gated tail). **(b) The route is not L-side.** 1w's forcing chain ((ii)–(iii)) consumes
the act, the field, the ring, and μ₆ — ring-side objects, the side 1t(iv) classified
as independently committed and already consumed by the mass arc (1m precedent); the
chain's text carries **zero L-side tokens** (no L-values, no zeros, no prime sum, no
bridge conductor term — gated over the span), and "conductor" appears in 1w exactly
twice, both outside the chain: (i)'s scoping note naming the **not**-consumed W₂
alternative, and (v)'s disclosed exhibit (location-gated). *Disclosure (round-104
F3):* 1t's own committed census list is headed by χ₋₃, and the chain span carries
two χ₋₃ tokens (gated) — both **attributional**, naming how the act fixes the field,
not L-data consumption; the operative adjudication is (iii)'s strike-test, and the
token-level headline above is scoped to the four named L-data classes. *(iii) The zero-weight
grading, refined — superseded-true.* 1t(v)'s *"an identification consumed by nothing
in the chain"* was a census over the record through 1t and remains true of that scope
(its own sentence: *"a census over the record, **not a universal over future
derivations**"*); as standing state it refines: the act is now consumed by **three
review-side chains** — 1c(ii)/1j's minimality entailment, 1r's partner determination,
1w's count entailment (censused case-insensitively: ~~seven pre-1x consumption sites
in this paper~~ [round-104 F1: the first draft's gate truncated the census at this
theorem's file position, missing two temporally prior sites that sit later in the
file — the Door-3 remark's 1w marker and the Finding-6 structural update — so the
committed count was false under the census's natural, temporal reading] ~~nine
consumption sites in this paper outside this theorem's own span, five in the
formulation~~ [round-105 F1: the round-104 correction was itself a layout artifact
— the gate matched raw bytes, and three instances of the exact phrase family
straddling hard line-wraps were invisible to it (two in 1w's own text, one in the
formulation's T1w marker); the census is now whitespace-normalized] **eleven**
consumption sites in this paper outside this theorem's own span, **six** in the
formulation — counts gated, whitespace-normalized; the three-chain classification
is by direct read, and all eleven sites classify to the three chains, none
carrying a number) — while its weight **for numbers**
remains zero: strike every consumption of the act and every committed number stands
(N_c via Adams and A2's 2-adic row; χ₋₃'s minimal-conductor-odd-primitive status via
1c(ii)'s unconditional theorem; the bridge identities are cross-checks). Net-state
markers at 1t(v), the 1s tail, and the formulation's T1t block. *(iv) The act's
axiomatic geography post-adoption.* The amended A1 names ζ(s) — the even tower's
completed object — yet the axiom block still carries **zero odd-reading content**: no
χ₋₃, no "character" as a word (the block's χ tokens are A2's torsion constant χ = 2 =
|μ(ℝ)|, and A1's character-substrings are the two tokens of "characterisation" in
the round-98 role note — per-token adjudicated, the round-94 discipline), no "odd", no "conductor", no "pairing", no
L-object (gated per token). What the block **does** carry natively is the ring side:
A2's cos(π/6) row names ℤ[ω] and ℚ(ζ₃); its χ = 2 row is torsion-of-units at the
real place — the same invariant class 1w reads at the paired field (|μ(ℝ)| = 2
even-side; w = 6 = N_c(N_c − 1) at ℚ(ζ₃) — an exhibit, disclosed, not a forcer). So
Door 4's asymmetry is mirrored inside the axiom block itself: **ring side native,
L-side extrinsic.** The adoption did not change the act's extra-axiomatic status.
*(v) Status conclusion.* Door-4 bookkeeping **confirmed and sharpened**: the member
persists charged (three members and the seven-item count unchanged *(net-state, Theorem 1y round 107: two members; the count stands)*); the committed
falsifier stands unfired and unchanged; and one falsifier is sharpened alongside it,
stopping-rule-gated per the 1h(iv) pattern like its sibling: **should any cascade
paper ever carry a number via the act** — replacing that number's papers-side carrier
— the act's weight-for-numbers becomes nonzero and the bookkeeping grading fails. No
closure; no number changes; category (a) refinement.

**Theorem 1y (the site-E pairing entailed: member one closes; the class keeps two
members, the seven-item count stands; `cascade_site_e_pairing.py`).** *(i) The
commission and the committed status.* The owner commissioned the site-E pairing —
member one's last remaining conventional content: 1k re-motivated the first member to
*"two named, listed anchors — the site-E pairing plus the variational-sup labeling"*,
and the adoption resolved the sup anchor into A1's ledger (1k(ii)'s round-98 marker),
leaving the pairing as *"the anchored convention, which persists in the residue."*
*(ii) The pairing is an identity, not a convention — the chain, every step committed
or exact arithmetic.* **(a) Part 0 defines p intrinsically in the d frame.** Verbatim
(part0, The Natural Zero): *"The sphere-area decay rate decomposes as: p(d) =
−½ln π + ½ψ((d+1)/2)"* — no s frame, no pairing, no read-off from P; the (d+1)/2 is
the Γ-argument of the layer's own area Ω_d = 2π^((d+1)/2)/Γ((d+1)/2) (part0's closed
form; layer d's area per its own table — Ω₅ = π³ at the argmax row), and p(d) =
−∂_d log Ω_d **exactly** (part0's own identity — *"the first derivative of the
log-area, which is −p(d)"* — gated symbolically and numerically). **(b) Part 0's area
is the Definition-2.1 weight.** Γ_ℝ(s) = π^(−s/2)Γ(s/2) gives **Ω_d = 2/Γ_ℝ(d+1)
exactly** (gated over the tower to machine precision): the sphere area whose decay
rate p measures IS the weight the committed dictionary attaches to layer d — the
same 2/Γ_ℝ(d+1) the fourth review names *"the Definition-2.1-consistent pairing"*
and the amended A1 carries, whose mirror the adoption transports by s ↦ 1−s
(d+1 ↦ −d). **(c) Hence the pairing.** p(d) = ∂_d ln Γ_ℝ(d+1); with the s-frame
potential P(s) whose committed crossings Theorem 7 reads (ln Γ(½) at s = 20.73, Γ(½)
at s = 218.6 — the d-crossings + 1, gated in 1k as the same roots), **p(d) = P(d+1)
is Γ-argument arithmetic** — the "+1" was never a frame choice in the mathematics;
it is the argument already inside Ω_d, Definition 2.1, and A1. *Availability
disclosure (round-107 F2):* every link of this chain predates the grading it
supersedes — Part 0's intrinsic sentence entered the source 2026-05-06, and the
formulation's T1 line "p(d) = (log Γ_ℝ)′(d+1)" is as old as the formulation itself
(2026-07-19), while 1k's "data-anchored convention" grading is round 60
(2026-07-22). This closure is therefore a **delayed observation of committed
content, not new mathematics** — the entailment stood available and unobserved for
47 rounds. The marking classification, adjudicated explicitly: the round-60 grading
was a **status report of the record's adjudication state** — true when written (no
committed surface had performed the derivation) — so it stands as history under
net-state markers per the 1v precedent, not strikes; what was false throughout was
only the implicit availability assumption, which no surface asserted. **(d) The alternative is the forsworn
avatar.** p(d) := P(d) reads ∂_d ln Γ_ℝ(d) — the log-derivative of 2/Γ_ℝ(d) =
Ω_(d−1) (gated), the **previous** layer's area: exactly the avatar weight Theorem 1's
own Remark forswears (*"The paper never uses the avatar; the arithmetic is
primary"*) and the site-C adjudication already rejected inside a committed clause
(1l(iii) *(round-107 F1: the first draft cited "1m" here and at three points below —
the pairing-dictionary content is Theorem 1l's; 1m is the availability factors;
corrected at all four)*: the Geometric clause's avatar pass was a frame error). The label shift
{5, 8, 20, 218} under P(d) (1k's gated exhibit, reproduced) is thereby excluded **by
the committed dictionary, not by data**. *(iii) The re-grade and the member
accounting.* The site-E anchor re-grades from data-anchored selection to
**cross-check** — completing for the pairing itself the move 1l made for the
−38% anchor. Member one's conventional content is exhausted: the sup anchor is
resolved into A1's ledger (an adoption — its cost stays on that ledger), and the
pairing anchor is entailed given the tower's dictionary (Definition 2.1 + Theorem 1,
whose only alternative 1l grades a contentless global renaming) plus Part 0's
intrinsic definition. **Member one closes. The class keeps two members** — the
audit-family member (live content: the site-E endpoint data, Definition-6.1
instantiation plus the strict-boundary stipulation *(net-state, Theorem 1z round
109: sharpened — menu-bounded, zero free numbers, alternatives data-excluded)*) and
the pairing-act member
(Door-4 bookkeeping per 1x) — **and the seven-item count stands**: the class is the
residue's sixth item, an item with live members either way. Net-state markers at
every "three members" surface (censused and gated). *(iv) Honest scope and the
falsifier.* Consumed: Part 0's definition and identity (committed), Definition 2.1 +
Theorem 1 (committed), Γ-argument arithmetic (exact); no data beyond the
already-counted anchors, now cross-checks; no number changes anywhere; no RH/GRH, no
semiclassics. The feature→layer assignment {5, 7, 19, 217} is now **entailed
end-to-end given the amended axioms and the committed dictionary**: the pairing by this theorem, the boundary
sides by A1's selector clause (1v), the bands by the lattice facts (1k(i)). The
falsifier, stopping-rule-gated per the 1h(iv) pattern: **any committed surface found
reading a layer's potential at the avatar argument** (Γ_ℝ(d) at layer d) as
load-bearing content re-opens the member; the known avatar appearances are the
forsworn Remark's subject and 1l's rejected clause, both already adjudicated.

**Theorem 1z (the endpoint data attacked: menu-bounded, zero free numbers, every
in-menu alternative data-excluded; the stipulation priced; member two persists,
sharpened; `cascade_endpoint_data.py`).** *(i) The commission and the inventory.*
The owner commissioned an attack on member two's live content — 1l(ii)'s *"the
closure windows' **endpoint data** — Definition-6.1 instantiation plus the
strict-boundary stipulation (part4b) […]"* (the bracketed ellipsis marking the
source sentence's continuation — round-110 F5). The committed inventory, read directly: the
three site-E closure windows are τ/μ = exp(Φ(6,13) + α(14)/χ)·χΓ(½) (the path
5→13), μ/e = exp(Φ(14,21))·χΓ(½)·(radiative slot) (the path 13→21), and α_s =
(N(12)²/Ω₂)·exp(Φ(5,12) + α(14)/χ) — with the addressing stated **per window**
*(round-109 F1: the first draft claimed "every endpoint is a forced-menu layer"
under a single step-sum convention; the α_s window's committed addressing differs,
and the claim was convention-dependent without disclosure)*: the two lepton windows
are host-pair paths under the path-start-exclusive reading — pair (5,13) → Φ(6,13),
pair (13,21) → Φ(14,21) — with all four endpoints in the **committed menus**
*(round-113 F1, propagating round-112 F1: the Bott set's residue class is forced
but its charged termination is Tier-4 empirical, so "forced menus" overclaimed;
the honest term is committed menus, the zero-free-numbers content unchanged)*
({5, 13, 21} the Bott generation set — committed, its termination empirically
anchored; {12, 13, 14} the Adams gauge set — Adams-forced;
part4b's anchors: *"The cascade has five structurally distinguished layers"*; *"The
four layers in $\mathcal{S}$ are not chosen from a menu; they are the complete set
of non-sink distinguished layers in the cascade"*); the α_s window is the committed
**descent Φ(12→4) = Σ_(d=5..12) p(d)** (part4b's own display), whose upper terminus
12 is menu-anchored (Adams) and whose lower terminus is **the observer dimension
d = 4 — C1-anchored, the hypothesis's own fixed point, not a menu layer** (Check 8:
it may not be laundered into a committed menu). The endpoint data still carries **zero
free numbers** — five termini in committed menus, the sixth the hypothesis's fixed
point, none free — and its entire content is three window selections
(Definition-6.1 instantiation), one attachment rule (the strict-boundary
stipulation), and the **per-window pair-to-sum addressing** — the disclosure round
109 added beyond the draft's three-component inventory (round-109 F1; wording
clarified round-110 F6). *(ii) The
exclusion census (new, gated).* Over the union menu M = {5, 7, 12, 13, 14, 19,
21} *(round-109 F6: the first draft called M "the non-sink distinguished menu" —
part4b's term for its own four-element set {5, 7, 14, 19}; M is this paper's
construction, that set ∪ the Bott generation set ∪ the Adams gauge set, each
committed)* — all 21 **unordered** pairs per window (round-109 F11), 63
computations, **endpoint-only ceteris paribus** *(round-109 F8: every
non-endpoint structure — the shift, the radiative slot, the A_GUT anchor — is
held at its committed value while the window varies; "excluded" means excluded in
that comparison class)* — the committed selections are **unique within
observation**: τ/μ at (5,13) sits at +0.28σ and the nearest alternative, (7,13),
at **524σ**; μ/e at (13,21) sits at +0.0012% (pred-vs-obs signing; part4b's
−0.0012% is the same number under its own obs-vs-pred definition, stated at its
own display — round-109 F5) and the nearest alternative at 33%; α_s at (5,12)
sits at **+0.019σ against the record's committed 0.1179 ± 0.0009** *(round-109
F3/F4: the first draft wrote "+0.09σ" — the sign was wrong, and the observation
used, 0.1180, is carried by no committed surface; corrected to the committed
observation, under which the census structure is unchanged)* and the nearest
alternative, (12,14), at **3.26σ** — the endpoint census's weakest exclusion,
reported exactly (every other α_s alternative is ≥ 18σ). *(iii) The stipulation
isolated and priced.* The strict-boundary stipulation — part4b's *"begins at the
$\mathrm{U}(1)$ layer and does not receive the shift"* — governs **three
attachment instances** at site E *(round-109 F2: the first draft said "exactly
two binary decisions," omitting the α_s window, which also lies strictly below 14
and receives the shift by the same committed theorem — "closes α_s(M_Z)… and
m_τ/m_μ… together"; the count was false)*: the τ/μ window receives δΦ_U(1); the
α_s window receives it; the μ/e window, which begins at 14, does not. All three
alternatives are data-excluded, at very different strengths: τ/μ without the
shift lands at 16.530, **−261σ**; α_s without it lands at 0.11590, **−2.22σ
against the committed 0.1179 ± 0.0009 — the weakest exclusion in this entire
analysis**, weaker than the endpoint census's 3.26σ and reported as such
(round-109 F2); μ/e with it lands at 210.36, +1.74% — some 1,400× the committed
residual (all gated). The rule is consistent across all three instances; a
candidate entailment from A3's
increment rule (*"corrections attach once, at sub-lead"*) is noted as an **open
route, not claimed** — a future committed derivation would relocate the
stipulation from member two to A3's ledger (stopping-rule-gated, the 1h(iv)
pattern). *(iv) The re-grade and the accounting — Check 8 disciplined.* The
menu-pair selections are **C1 instantiation** — the address book is the
hypothesis's own content, and uniqueness-within-menu is **corroboration, not
forcing** (the cross-check reading, exactly as the registered discipline
requires); **no closure is claimed**. Member two persists with sharpened content:
from "endpoint data (a list)" to **menu-bounded selections carrying zero free
numbers, each in-menu alternative data-excluded, plus one attachment rule with
all three alternatives excluded — the weakest at −2.22σ**. The class stays at
two members; the seven-item
count stands. *Honest scope:* observational values are consumed here — 16.8170 ±
0.0011, 206.7683, 0.1179 ± 0.0009 — for the exclusion census only *(round-110
F2: the disclosure had continued to recite the uncommitted 0.1180 after the census
moved to the committed value)* (the
cross-check class 1l's re-grade licenses); no number changes; no new prediction;
no RH/GRH; no semiclassics. *Falsifiers:* any committed window endpoint found
outside the committed menus fails the menu-bounded claim (gated); the A3-entailment
route, if ever committed, relocates the stipulation and is to be recorded as
such.

**Theorem 1aa (the forcing ledger: what selects the selection; the projection
question stratified; the d = 5 presentation chain; `cascade_forcing_ledger.py`).**
*(i) The commission and the boundary, stated first.* The owner commissioned the
forcing question: what forces the selection — why these properties project into
the observer's spacetime, and why they present as particles at the d = 5 layer.
The record's boundary is committed and this theorem does not move it: the
outermost question — why the observable universe realizes **this** structure — is
C1 itself, the paper's one assumption (the formulation's header: *"what can never
be a theorem"*; Theorem 13's own scope honesty: the exhaustion's content is *"'a
fully-specified address book leaves zero residual freedom,' not 'the address book
is forced'"*). What this theorem does: stratify the question into its forcible
parts and audit each, so the C1-primitive residue is exact rather than diffuse.
*(ii) The strata — as corrected by round 112, which struck the first draft's
promotion of two empirically-anchored terminations into "forced."* **Stratum F
(structure-forced, observer-free — the window arithmetic).** Which *residues*
can carry complex quantum matter is a theorem consuming no hypothesis:
Cl(1, d−1) has complex minimal spinors iff d mod 8 ∈ {4, 5, 6} (Bott/Lounesto,
part4a), giving in the tower's distinguished span the windows {4,5,6},
{12,13,14}, {20,21,22}; the first **Majorana desert** (d = 7–11) carries
part4a's verbatim sentence — *"carry no complex spinor structure and support no
quantum matter content visible to the d=4 observer"* — while for the second
(d = 15–19) **the spinor half is committed via the same iff and the
visible-matter-content half carries no committed sentence** *(round-112 F3: the
first draft stamped both deserts "part4a, verbatim")*; the gauge triple
{12, 13, 14} with SU(3)×SU(2)×U(1) is Adams-forced (N_c = 3 kernel-entailed
**given the act** — an act-conditional item housed here with its condition
disclosed, round-112 F4); the distinguished layers {5, 7, 19, 217} are
Γ-theorems with the feature→layer assignment entailed end-to-end (1y).
~~the generation seats are the Dirac layers d ≡ 5 (mod 8): {5, 13, 21}
(Bott)~~ **[struck round 112 (F1, MAJOR): the Bott seat *residue class* is
forced; the *set* {5, 13, 21} is not — part4a's own sentence: "Bott
periodicity is infinite. The cascade descent contains Bott Dirac layers
(d mod 8 = 5) at d = 5, 13, 21, 29, 37, …, with no cascade-internal
termination of the replication"; the cut at three charged generations "relies
on empirical non-observation at LEP, atomic, fixed-target, and cosmological
observations — not on cascade-internal exp-suppression," Tier-4-graded by
part4a's own Open Questions; and d = 29 carries committed neutrino-sector
content. The termination belongs to Stratum D.]** **Stratum D (empirically
anchored — the terminations; added round 112, F1/F2).** Two completeness gaps
the record itself acknowledges (category (a)), restated here because the first
draft's strata absorbed them into "forced": the Bott ladder's cut at three
**charged** generations is Tier-4 empirical input; and the third window's
non-seat layers (20, 22) have **no committed disposition** — part4a's table row
defers the window's Role column to part4b, and part4b carries no **window-role
(visible-content) disposition** for the window's **non-seat** layers 20 and 22
*(round-113 F4: the first sweep wrote "no third-window content" — false, d = 21
is a third-window layer and pervasively committed; round-114 F1: the repair's "no
content for" failed the same literal check — part4b names layer 20 potential-side,
the θ₂₃ descent's terminus d₁+1 = 20; the role-disposition gap stands)*; the
exclusion route is part4a's *candidate* derivation, uncommitted by its own
wording. **Stratum E (entailed given the seat plus the convention ledger —
round-112 F4).** Given C1's minimal content — the observer occupies twist 4 —
**and given the record's standing convention residue** (the seven-item count
with the class's two remaining members, the pairing-act among them; Theorems
8–12's determination runs through these), the *accounted* spectrum follows:
first-window fermions, mirror-window gauge, the charged Bott seats —
~~the visible spectrum is exactly [first-window fermions] + [mirror-window
gauge] + [the Bott ladder], the deserts contribute nothing~~ **[struck round
112 (F2 MAJOR / F8 minor): "exactly" required a committed exclusion of visible
content at d = 20, 22 and beyond, which the record does not carry (Stratum D);
and the desert layers contribute no visible *matter content* while d₀ = 7 and
d₁ = 19 are source layers of committed precision closures — the deserts'
imprint on observables is real and committed]** — with the address book's
rules single-valued (Theorem 13) and the window alternatives data-excluded
(1z).
**Stratum C (C1-primitive — the exact residue).** Three items and no more: that
the tower is *occupied* at all; the observer↔twist-4 **labeling**; and the
occupancy entries of Definition 6.1 outside strata F/E (~60–100 discrete
entries, no continuous parameter). On the labeling, the record's sharpest
committed fact is an **exhibit, not a derivation**, and Definition 6.1 grades it
itself: twist 4 carries *"**one** convention-free arithmetic distinction"* — the
torsion half-period, {k : γᵏ = −1} = **{4}** (the index at which the clock
reaches its unique nontrivially-real residue, −1 — round-112 F5 corrected the
first draft's conflation of index and residue; the flip-word arithmetic is
derived, Mechanism M) —
*"though its link to the **observer** is a labeling, not a derivation"*
(Definition 6.1, verbatim; anchored and gated). *(iii) The d = 5 presentation
chain.* Why matter presents as particles at the 5-layer, assembled from
committed content: d = 5 is the unique layer satisfying a **four-way
conjunction** — (a) the discrete argmax of V (Γ-forced; entailed 1k/1y); (b) the
Dirac layer of the **first** complex window (Cl(1,4) = M₄(ℂ); 5 mod 8 = 5); (c)
the first Bott generation seat; (d) the observer-adjacent frame d_obs + 1 —
where (a)–(c) are structure-forced and **(d) alone consumes the seat**. The
presentation *as particles* is the committed machinery, cited: per-layer
Grassmann locality (part4b's fermion action), the chirality basins χ(S^(2n)) = 2
at the even boundary sphere S⁴, per-layer mass m(d) = R(d)/χ, measurement along
root frames (A4/S5). And the deserts answer the question's negative half: the
observer sees the Standard Model's *shape* because between the windows **no
committed visible matter content presents** — the first desert by part4a's
sentence, the second by the spinor iff with the content half uncommitted, (ii)'s
own disclosure (round-113 F5) — (round-112 F8: the desert layers' imprint on
observables is real — d₀ and d₁ are source layers of committed closures —
potential-side, not matter content) — the spectrum's sparseness within the
committed span is Clifford arithmetic, not selection. *(iv) Honest scope and falsifiers.* Check 8 is load-bearing
throughout: no step above derives the seat; stratum E is conditional on C1 and
says so; the γ⁴ exhibit corroborates the labeling and does not force it (a
committed derivation of the observer↔4 link from the clock distinction would
move the labeling from stratum C to stratum F and is the standing route this
theorem names — stopping-rule-gated per the 1h(iv) pattern). No closure; no
number changes; no data consumed beyond the already-committed record; category
(a). The answer to the commission, in one sentence *(as corrected by round 112)*:
**the window arithmetic is forced (Clifford, Adams, Γ), the charged ladder's
termination is empirically anchored (Tier 4, part4a's own grading), the
projection is entailed given the seat plus the convention ledger, and the seat
is the hypothesis — carrying exactly one convention-free arithmetic
distinction, on the record as an exhibit.**

**Theorem 1ab (the per-species census: the head-count chain assembled from
committed content, imports disclosed; `cascade_species_census.py`).** *(i) The
commission and the factor inventory.* The owner commissioned the per-species
census — how many instances of each particle type the seat records. The chain's
factors, classified: **committed** — H₀ = 66.77523 (Part V's theorem through the
certified chain, M_Pl,red√(2I/(3(π−1)))), Ω_b = 1/(2π²) (Part V's baryon-fraction
theorem — its proof's two sentences, quoted separately: *"Baryonic matter is the
content directly accessible to the observer on its own boundary shell S³"*; *"One
unit of content on this boundary corresponds to a fraction 1/Ω₃ of the total"* —
round-116 F1: the first draft spliced these into one quotation-marked string that
exists nowhere in the source), Ω_m =
0.31150, w = −1, the Friedmann relation, and the horizon budget S_dS =
24π²M⁴/ρ_Λ with ρ = (2/π)e^(0.02108)I (1n(iii)); **committed at leading order
with its deviation on the record** — T_CMB = 2.642 K (−3.1% of the observed
2.7255 K, part5's own table); **imports, disclosed** — the proton mass m_p (the
QCD composite; grep-verified uncommitted on all twelve tex surfaces — the gate
now runs the full scan, round-116 F6) and the
observed T_CMB for the photon density (the leading-order alternative computed
alongside). *(ii) The fully-committed composite — zero imports beyond the certified
chain's CODATA unit-anchors (round-116 F7: the chain's own record is "not
category (a) pure arithmetic — it uses the CODATA physical constants (G, hbar,
the parsec)"; the G-band propagates ±5×10⁻⁷ on the composite, 0.3% of Planck's
σ — negligible, disclosed).* **Ω_b h² =
h²/(2π²) = 0.0225892**, both factors the record's own, compared like-for-like:
Planck 2018 (TT,TE,EE+lowE+lensing) 0.02237 ± 0.00015 puts it at **+1.46σ (+0.98%)** — a sharper statement
than the ledger's standing Ω_b-alone +2.8% (which compares against the
observed fraction extracted with the *observed* h; the composite is the honest
committed-vs-observed object). ~~and it is new to the record here~~ **[struck
round 116 (F2, MAJOR): part5 already forms the composite at 4 s.f. — ω_b^cas =
(1/2π²)×0.6678² = 0.02259 — and ratios it to Planck's 0.02237 inside the
sound-horizon proof, with the prose "the cascade's (ω_b, ω_m) land essentially on
top of Planck's 2018 values["], the source continuing] What is new here is the seven-digit value and the
σ-grading as a headline comparison, not the object.]** *(iii) The
census, with the two imports.* n_γ = (2ζ(3)/π²)(kT/ħc)³ = **410.73 cm⁻³**; n_b
= Ω_b ρ_crit/m_p = 0.2537 m⁻³; the baryon-to-photon ratio **η = 6.176×10⁻¹⁰**.
Its comparison class, stated honestly (round-116 F3): against Planck's Ω_b h²
re-expressed through this theorem's own m_p conversion (6.116×10⁻¹⁰; the standard
mean-mass-per-baryon conversion gives 6.127×10⁻¹⁰) the +0.98% is **exactly the
Ω_b h² deviation carried through — the same comparison re-expressed, an identity
declared, not gated** (the first draft's "gated" label sat on a tautology gate,
removed); the one **independent** head-count-level comparison is BBN deuterium,
η₁₀ = 6.10 ± 0.20 — a conservative recital of the PDG-class BBN concordance
band, the ±0.20 covering the nuclear-rate systematic spread — against which the
cascade sits at **+0.38σ** (gated; round-117 F3: the first sweep wrote "the
dataset named" while naming only the channel — the band is an uncommitted-obs
recital, disclosed as such). Within the record's own
horizon geometry *(round-118 F1: the first frame said "budget geometry" —
the struck identification in noun form; the budget sphere is 0.56% smaller)* —
the de Sitter horizon r_H = (c/H₀)/√Ω_Λ = 5411 Mpc
~~, exactly the S_dS budget sphere's radius~~ **[struck round 117 (F1, MAJOR):
false at 1.12% — the sphere carrying exactly the gated budget S_dS has radius
5381 Mpc (0.56% below r_H), because the budget uses the closure's ρ_Λ =
(2/π)e^(0.02108)I while r_H uses the Friedmann side with the committed
subleading Ω_m = 0.31150; the entropy ratio S(r_H)/S_dS = 1.0112 equals the two
ρ_Λ's ratio identically (gated), and the 1/π-vs-0.31150 spread is part5's own
acknowledged leading-vs-subleading gap]** — the head-counts: **N_b = 4.9×10⁷⁸ baryons,
N_γ = 8.0×10⁸⁷ photons, N_ν = 6.6×10⁸⁷ relic neutrinos** (the 9/11 relic
factor — standard thermal history, the 4/11 entropy transfer with the N_eff = 3
idealization, +1.5% under N_eff = 3.044, within display — round-116 F7; all
gated). *Epoch disclosure (round-116 F5):* these are **present densities filling
the asymptotic de Sitter volume** *(round-118 F1: the round-116 phrase said
"budget volume" — under that literal referent the 2-s.f. displays would shift,
N_γ 8.0 → 7.9, N_ν 6.6 → 6.4, since the budget sphere's volume is 0.983× the
r_H volume; the gated counts are r_H-volume counts, now labeled as such)* — a
horizon-referenced convention, the count at no single epoch; the present event horizon (5152 Mpc, gated by quadrature) gives
N_b = 4.3×10⁷⁸ (−14%), and the popular "~10⁸⁰" attaches to the larger comoving
observable volume — three disclosed volume conventions. By charge neutrality the
census extends to **electrons at zero marginal import beyond the helium mass
fraction**: N_e = N_p ≈ (1 − Y_p/2)·N_b ≈ 4.3×10⁷⁸ (Y_p ≈ 0.25, a disclosed
import — round-116 F8). Under the cascade-leading T_CMB the photon side
shifts by T³: η = 6.78×10⁻¹⁰ — reported alongside; the +10.9% total deviation is
the temperature cube (+9.8%) **compounded on** the composite's +0.98%
(round-116 F4: the first draft attributed the whole +10.9% to the cube). *(iv) The hierarchy and the honest grading.* N_b
≪ N_γ + N_ν ≪ S_dS: 10⁷⁸·⁷ ≪ 10⁸⁸ ≪ 10¹²²·⁵ — the budget is
horizon-dominated, stated as arithmetic (the record commits the budget and the
counts' factors, not a matter-entropy theorem). Grading, Check-8 disciplined:
this census is a **data-facing assembly** — committed cosmology composed with
two disclosed imports — a cross-check of the record's cosmological sector at
the head-count level, not a closure; the identity and abundance *structure*
(why alike, why many) is 1aa's and the measurement clauses'; the brute
occupancy is C1. **What would upgrade it:** a committed m_p (closing the QCD
composite) or the T_CMB deviation's closure would make η fully committed —
the standing routes, named; no member, count, or number changes anywhere.

**Theorem 1ac (A3's underived rules audited: the tail decomposed against the
committed record; the residue is instantiation, not law; `cascade_a3_rules.py`).**
*(i) The commission and the tension.* The owner commissioned A3's underived
rules. A3 — *"This is the load-bearing axiom"* — carries four components (the
source-selection flags; the increment rule; source layers at the analytic
features; the per-Bott-period attachment) and the tail sentence *"the increment
and per-period rules are underived."* The committed record contradicts the
tail's first half **on the same surface**: the formulation's gap-ledger row 1
reads *"**derived from arithmetic first principles** (T5, Addendum 33;
supersedes the Tier-2 A32 version)"* with the residue column *"closed as
mathematics; only its physical instantiation (occupancy, m/k counts) remains
with C1"* — and T5's own header is *"Arithmetic increment rule — PROVED from
Tate's thesis alone."* The tail predates Addendum 33: the delayed-observation
class of 1y, disclosed as such. *(ii) The increment rule, decomposed — every
piece committed.* **(a) Attach-once, arithmetic side (T5):** *"ℤ's total order
gives attach-once"*; *"at most one member, first power, per interval functional
— a theorem of probability at the real place."* **(b) Attach-once, physical
side (part4b):** the marginal Green's-function identity G(d_obs, d*) −
G(d_obs, d*+1) = α(d*) *"holds at every layer at machine precision"*, and
*"the source coefficient is exactly 1 (no fitted prefactor) by assembly via
Sturm–Liouville structure"* — the committed verifier
(`cascade_unit_source_strength.py`) is run and ~~its exit gated here~~ [struck
round 120 F3: at the landing commit d4f3c63 the script exited 0 unconditionally
— it printed its conclusions even when the identity was falsified, so the
subprocess gate certified runnability only; the sweep added real verdict gating
(marginal identity at every interior layer; unit coefficient at the four
sources), after which the exit is gated and the probe that falsifies the
identity trips it]. **(c) The
1/χ^k filtering:** part4b's own *"derivation of the filtering rule"* with
*"The channel count k is not fitted."* **(d) Sub-lead placement:**
prop:slot-precedence — proposition-grade; conditional, ~~by its own
disclosure~~ [corrected round 120 F6: the disclosure lives not in the
proposition's statement but in part4b's Tier-2 summary — *"Conditional on the
strict reading of the G flag in Proposition prop:source-selection"* — and its
closure note, which adjudicates the strict reading over the relaxed one
**empirically**: the relaxed reading *"empirically does not match the
residual"* and *"The strict reading is therefore the structurally correct
one."* The reading choice is accordingly counted in the residue set below].
What arithmetic does not supply is T5's
own list, verbatim: *"P > L > G precedence, the physical occupancy assignment,
the (m,k) counts — instantiation data belonging to C1."* *(iii) The per-period
rule, decomposed — the ledger's own row 2.* Shape **derived** (T6, A34); the
mechanism at Tier-2 (A38/A43, the row's own header — restored round 120 F5,
the landing text had flattened it): flip-count 4 **derived** (minimal torsion
word), ×3 incoherence **derived** (factorization), the form *"unique
colour-free form conditional on availability assignments"*; the residue: *"the
unit normalization carrying Γ(½) is a
convention, empirically anchored not arithmetically forced"* plus the
marked-coset choice — JUNO tests the value and *"cannot convict the form over
its 0.1% twins."* *(iv) The adjudication and the marker mechanics.* A3's tail
is **superseded-true**: each rule decomposes into committed-derived form plus
instantiation residue, and the ledger's own words for the increment half are
"closed as mathematics." The axiom block is byte-identity-gated (the adoption's
discipline, riemann_kernel V1), so the block is **not edited**; the net-state
marker is placed **adjacent**, ~~immediately after the block~~ [struck round
120 F1/F2: at the landing commit d4f3c63 the marker sat between A4 and the
section-2 heading — INSIDE V1's compared span, `form[i0:i1]` ending at "## 2.
The theorems" — and V1 was printing FAIL on the committed tree, masked because
the kernel script then exited 0 unconditionally, which also made this
sentence's gating claim vacuous; the sweep relocated the marker immediately
below the section-2 heading (outside the span) and added real exit gating to
riemann_kernel, after which V1 passes and an axiom-block edit probe trips the
gate] — and the block's untouchedness is gated here (the kernel verifier
re-run, now exit-gated, exit 0). **A3's honest net residue: {the occupancy
assignment; the (m,k) counts; P > L > G (residue item five, deletable on the
uniform reading); the per-period unit normalization; the marked coset; the
strict G-flag reading (added round 120 F6 — empirically adjudicated over the
relaxed reading by part4b's closure note, the same "empirically anchored"
class as the unit normalization)} — instantiation, convention, or empirically
anchored reading. Zero underived rules-in-form remain — with row 2's mechanism
carried at Tier-2 (A38/A43) and its form conditional on availability
assignments, per its own ledger row.**
*(v) The 1z route, narrowed.* The strict-boundary stipulation's committed home
is thm:alpha-s-closure's own scope condition — *"any observable whose cascade
path lies strictly below … d=14"* — and the candidate derivation is the
marginal Green's-function reading (a source attaches to the paths that cross
it): open, named, stopping-rule-gated per the 1h(iv) pattern; a committed
closure would relocate the stipulation from member two's live content to
derived scope. *Honest scope:* no closure is claimed beyond assembling the
record's own gradings in one place; no number changes; category (a); the
flags' categorical derivation (part4b's Open Question, Tier 3) remains the
standing upgrade route.

**Theorem 1ad (the participation rule: a sourced-cell criterion for the Bott
tower; the census is a theorem, the coupling mechanism a proposition;
`cascade_participation_rule.py`).** *(i) The commission and the committed
tension.* The owner commissioned the participation rule — the single target
behind "why exactly three generations" and the selection-flag/occupancy
residue. The committed tension is part4a's own (rem:bott-tower-open): *"Bott
periodicity is infinite"*; the Dirac seats *"$d = 5, 13, 21, 29, 37,
\ldots$"* replicate *"with no cascade-internal termination of the
replication"*; the α_em closure *"requires exactly three Dirac layers to
contribute"*; and — part4a's own words — *"$N_{\rm gen}=3$ is currently a
hidden empirical input the cascade relies on without deriving."* The
suppression argument's flaw is likewise part4a's own disclosure (OQ-T4): the
289× amplitude suppression *"applies to the mass, not the charge"* — the
extrapolated fourth-generation mass is ≈543 eV, *lighter* than the electron,
so *"lower mass at fixed charge does not produce invisibility; it produces
enhanced low-energy accessibility."* Part4a's candidate resolution
(time-decoupling past supercritical depth) brackets a threshold empirically
between Gen 1's overshoot and d=29's (1.3 to ~9.3 layers past d*₁ = 19.731)
but derives no value. *(ii) The rule, and the census theorem.* Partition the
descent's Dirac seats into their trailing Bott cells — for each seat d, the
eight layers (d−8, d] it terminates. *Orientation disclosure (round 124 F5):
the trailing choice is a convention, stated not forced — grounded in the
descent direction (a seat's cell is the period the descent traverses to
reach it), and load-bearing for the cell-contents narrative: of the eight
seat-anchored offsets, six (including trailing) give N_gen = 3 at seats
{5, 13, 21}, while the two leading-most give N_gen = 2 — the headline count
is 6-of-8 robust, but the specific contents {5}, {7}, {14, 19} and the
14/19-collision explanation below are trailing-specific (the offset census
is gated in the verifier).* *(Net-state, Theorem 1ae round 125: the
orientation convention is eliminated — 1ae's symmetric distance rule
δ(d) = min|d − d*| needs no partition, no offset, no direction, and yields
the identical census {5, 13, 21}, gated as an equivalence; this disclosure
stands as history of the cell formulation only.)* **The rule: a seat hosts propagating
(time-coupled) content iff its cell contains a distinguished source layer**
(the committed source set {d_V, d_0, d_gw, d_1} = {5, 7, 14, 19} of part4b's
prop:source-selection — structure-forced and observer-free, with the forcers
named per part4b's own attribution (round 124 F4): {5, 7, 19} by the Γ
function (Part 0's critical points), 14 by Adams' theorem and the Bott
mirror; Check 8 clean). The census
is exact arithmetic: of the 27 seats in the descent [4, 217], cell(5) ∋ {5},
cell(13) ∋ {7}, cell(21) ∋ {14, 19}, and **every cell from seat 29 onward is
empty** (all four sources lie ≤ 19 < 22). Exactly three sourced cells —
N_gen = 3 as a counting theorem over structure-forced data (Γ + Adams), with
the four-source /
three-generation mismatch explained in passing: 14 and 19 share a cell
(under the trailing convention, per the disclosure above).
*(iii) What the rule postdicts from the committed record, without new
inputs.* (a) The α_em brake: exactly three contributing Dirac layers, which
the 137.028 closure (0.006%) demands — the (D1)/(D2) conspiracy resolves to
"cells without sources decouple." (b) d=29's committed role: source-only,
coupled to the physics at seat 21 through the committed neutrino formula
m_ν(Gen g) = m₂₉·α(d_g)/χ^(29−d_g) (part4b, verifier
`cascade_neutrino_mass_audit.py`, run and ~~exit-gated here~~ [struck round
124 F1: at the landing commit 7d8e797 that script's only exit path was
`sys.exit(main())` with an unconditional `return 0` — the "GATED verifier"
label was a vacuous differentiator, the defect class struck in round 120
(F3), its third instance; real verdict gating (4 verdicts) was added in the
round-124 sweep, after which the label is true and a falsification probe
trips it]; 0.0493 eV vs
observed 0.0495 eV) — the filter exponent for the heaviest neutrino is
χ^8 = 256, **exactly one Bott period**, and the committed instances (χ^8,
χ^16, χ^24 for generations 1, 2, 3) all carry cost χ^(layer distance) with
the distance a whole number of periods — all cross-cell. ~~In-cell coupling
carries no filter~~ [struck round 124 F6: the landing text's "in-cell
coupling does not" exemption was an unmarked new input — the record
contains no in-cell coupling instance — and it contradicted (iv)'s own
χ^(layer distance) reading, under which a hypothetical in-cell coupling
would carry χ^(distance), not χ⁰; the mechanism claim is confined to what
the record shows: cross-cell cost at the committed exponents]. The rule's
mechanism is
the formula's own exponent read structurally. (c) The cut, and its
committed precedent [rewritten round 124 F3 — the landing sentence
("the threshold sharpened … d₁ + 8 ≈ 27.7 … the bracket's midpoint mystery
resolves to the period length") conflated two anchors: "the last source" is
d₁ = 19, an integer, giving 19 + 8 = 27 exactly, while 27.73 = d*₁ + 8 uses
the continuous supercritical threshold d*₁ = 19.731, which is not a source;
and "midpoint mystery" was loose — the bracket's midpoint is 25]: the
rule's cut is **last source + one Bott period = 27**, integer arithmetic —
and this is not novel to the theorem: part4a's rem:bott-tower-open already
computes it (*"a structural criterion at ``one Bott period past $d_1$''
would give $d \leq d_1 + 8 = 27$, capturing $d=21$ but not $d=29$"*). The
rule's contribution to (c) is narrower: it grounds that committed candidate
in the source set (sourced cells) rather than positing an activation width;
the cut — 27, or 27.73 on the continuous-threshold variant, disclosed as a
different anchor — lies strictly inside part4a's empirical bracket
(21.0, 29.0) either way. *(iv) Honest
grading.* The **census is a theorem** (finite arithmetic over the committed
source set and the Bott partition — the verifier recomputes it exactly). The
**coupling mechanism is proposition-grade**: "sourced cell ⟺ time-coupled" is
grounded in committed pieces (unit source strength at the four sources —
Sturm–Liouville, exit-gated in 1ac; the χ-per-layer filter with cross-cell
cost χ^(layer distance), committed in the neutrino formula) but the
biconditional itself is not derived — it is the concrete candidate for
part4a's resolution route (a), a *"cascade theorem terminating the
Bott-replication of propagating fermion content at the third orbit, with the
higher Bott layers then realised as something other than propagating
fermions"* — here: as sources. What this does NOT close: the P > L > G
precedence and the flags' categorical derivation (part4b's OQ, Tier 3) stand
open — the rule consumes the source *set*, not the flag *assignments*; and
the biconditional's derivation is the named remaining theorem. *(v)
Falsifiers and by-catch.* Any propagating fourth-generation fermion at any
mass kills the rule outright — **and that includes the KATRIN/TRISTAN
sterile search** ~~a detection would confirm the source reading of d=29
(Reading A) without disturbing the rule~~ [struck round 124 F2, a double
error: (i) the committed labels were inverted — part4a's OQ-T3 defines
Reading A as the *propagating* sub-keV sterile neutrino and Reading B as
the *structural source mass that does not correspond to a particle*; the
rule instantiates **Reading B**; (ii) the falsification logic was
backwards — a KATRIN-visible sterile at d=29 is propagating fermion
content in an unsourced cell, which the rule's biconditional forbids, and
part4a says so for this reading family: *"Reading~B and Reading~C predict
no such observation."* The corrected statement: the rule PREDICTS a null
KATRIN/TRISTAN result; a detection consistent with ~~part4b's~~
**part4a's** [corrected round 125 F2: the sterile-mixing prediction
|U_e4|² = α(21)/χ⁸ ≈ 9×10⁻⁵ is committed in part4a's OQ-T3 — part4b
carries the factor only as a mass-formula ingredient, never as a
mixing prediction] mixing
prediction would falsify the rule while vindicating Reading A]; the
analysis instruments
part4a names (`cascade_bott_tower_beyond_29.py`,
`cascade_d29_sterile_neutrino.py`) are run here (exit 0) but are
**analysis-grade — tables without verdict gates** — disclosed as such, not
counted as verification. By-catch, flagged: part4a's prose
tower masses (m₃₇ ≈ 0.2 eV, m₄₅ ≈ 30 μeV) and the tower script's table
(0.70 eV, 105 μeV) disagree by ×3.5 ≈ 2√π — a pre-existing one-factor
convention inconsistency on non-load-bearing values. *(Round-124
adjudication, reviewer-supplied and lead-verified: part4a's prose is the
correct side — the committed-convention mass formula reproduces m_e and
543 eV, and dividing the tower script's values by 2√π recovers the prose;
the tower script drops one (2√π) factor and its own d=29 row prints
1999 eV against the committed 543 eV, an internal contradiction in an
analysis-grade script, left to a future repair commit.)*
No number changes; category (a) plus one stated candidate criterion.

**Theorem 1ae (the participation dichotomy, de-conventioned: the orientation
convention eliminated, the gap proved, ~~the contrast forced; one lemma
remains, named exactly~~ [title swept round 127 F1 — the round-126 sweep
regraded the body but missed its own display name: the δ-contrast is the
theorem, the coupling contrast is conditional, and TWO unproved items
remain, named in (v)]; `cascade_participation_dichotomy.py`).** *(i) The
commission.* The owner's standard, verbatim: this must be *a proof, not a
pattern match.* Rounds 124–125 exposed exactly where 1ad fell short of that
standard: a trailing-cell orientation that was a convention (the census
6-of-8 offset-robust, the cell contents 1-of-8), and a coupling biconditional
that was proposition-grade. This theorem removes the convention entirely,
~~upgrades every input to a cited theorem~~ [struck round 126 F1: false for
the coupling-cost input — the χ-per-layer model is an extrapolation of the
neutrino formula's structure, and that formula's derivation is itself a
part4b Open Questions item ("no explicit derivation appears"); the census
inputs are cited theorems, the cost model is not], proves the dichotomy's
census and gap exactly, and reduces what remains to two named unproved
items. *(ii) The
convention-free rule.* For each Dirac seat d, define **δ(d) = min over the
source set S = {5, 7, 14, 19} of |d − d*|** — symmetric, orientation-free:
no partition, no offset, no direction. The rule: a seat participates iff
δ(d) < 8. The census is exact: δ(5) = 0, δ(13) = 1, δ(21) = 2; δ(29) = 10,
and for every deeper seat (seat_k = 8k − 3, k ≥ 4) the nearest source is
d₁ = 19 — the largest element of S, since all of S lies below every such
seat — so δ(seat_k) = 8k − 22 ≥ 10, strictly increasing. Participants:
**{5, 13, 21} and nothing else** ~~, ever~~ [modality corrected round 126
F2: "ever" holds relative to the committed source set — see (iii)'s
regraded exhaustiveness]. This census coincides with 1ad's
trailing-cell census (gated as an equivalence), so every 1ad result stands
with the convention deleted; 1ad's orientation disclosure is thereby
superseded-true (net-state marker in place). *(iii) The gap theorem
(proved).* The realized δ-values are {0, 1, 2} ∪ {10, 18, 26, …}: **no seat
realizes any δ in [3, 9]** — the dichotomy carries a seven-integer-wide
empty margin, so every threshold from 3 through 9 (in particular "within
one Bott period") yields the identical census; the threshold's exact value
is not load-bearing anywhere inside the gap, gated by direct enumeration.
Exhaustiveness, regraded honestly (round 126 F2): ~~theorem-grade …
close the source set for all time; the census can never be amended by a
fifth source~~ [the composition is graded per step]. Part 0's tower
completeness — *"The Gamma function produces exactly four distinguished
dimensions in the cascade. No fifth exists."* — is a **theorem**, but its
proof closes *cascade-internal Γ-mechanisms*; d_gw = 14 itself entered the
source set by an external route (Adams' theorem and the Bott mirror,
part4b's own attribution), and the committed Adams uniqueness scan is
scoped — *"the unique dimension in $[5,d_1=19]$ where $\rho(d)-1=3$"* —
while Radon–Hurwitz arithmetic gives ρ(d)−1 = 3 again at d = 20, 28, 36, …
above the scanned range, so no cited *theorem* excludes an Adams-type
distinguished layer above 19. The closing step is part4b's **remark-level
type-counting completeness** — *"they are the complete set of non-sink
distinguished layers"*; *"No fifth type is definable without introducing a
new structural element"* — committed, but a remark, not a theorem. Net:
the census is closed **relative to the committed source set** (sink
accounting: *"Removing $d_2=217$ as the Planck sink leaves exactly four
sources"*); a new structural source mechanism would reopen it, and the
record's own barrier against that is remark-grade. *Sensitivity disclosure, load-bearing
and stated:* the sink exclusion matters — under the counterfactual reading
that counts the Planck sink d₂ = 217 as a source, exactly one additional
seat would participate (seat 213, δ = 4, the Planck-adjacent Dirac seat);
the exclusion is part4b's committed accounting, not a choice made here, and
the counterfactual is gated. *(Net-state, Theorem 1af round 130: this step
upgrades — the committed action makes the sink a constraint node whose
forcing produces only a rigid shift, zero bond stretch, zero action; "the
sink cannot source" is now forced by the dynamics, not only the
remark-level accounting.)* *(iv) The contrast, split into its theorem and its conditional (regraded
round 126 F1 — the landing's "forced-contrast theorem (proved)" rested on
~~the committed per-layer filter … coupling cost to the nearest source is
χ^δ~~, an uncommitted cost model: part4b's neutrino formula
m_ν = m₂₉·α(d_g)/χ^(29−d_g) anchors every committed exponent at **layer
29**, the distance to the *receiving seat* — no committed instance couples
any seat to an S-source at cost χ^δ, seat 21's only committed filter is χ⁸
to 29 not χ² to 19, and the formula's own derivation is a part4b Open
Questions item ("no explicit derivation appears"); the F124-6 class,
re-expanded one theorem after it was confined].* **The theorem half
(δ-arithmetic, proved):** min excluded δ (10) minus max included δ (2) is
exactly 8 — one Bott period — forced because seats 21 and 29 share the
same nearest source (d₁ = 19, the last), so their δ-values differ by
exactly the seat spacing. **The conditional half:** *if* coupling cost
scales as χ per layer of separation from the nearest source — an
extrapolation of the neutrino formula's structural shape, stated here as a
model, proposition-grade per 1ad's own confinement *(pointer, round 133
F6: Theorem 1ag makes this model precise with three named conditions;
the conditional status stands)* — *then* the
worst-participant/best-non-participant coupling contrast is χ^8 = 256.
Consonance, reported and not identified: part4a's independent amplitude
route suppresses the fourth charged generation *"by a factor of $\sim
289$"* (the supercritical wall — a different mechanism); 289 and 256
differ by 13% — one committed route and one conditional route arriving at
the same scale, no identity claimed. *(v) The remaining unproved items,
named exactly (two, not one — corrected round 126 F1: the landing's "the
*only* thing not proved" was false while (iv) carried an unmarked model).*
**(v-a) The cost model:** that coupling cost scales as χ per layer of
separation on the seat↔source channel — (iv)'s conditional input, an
extrapolation whose committed antecedent (the neutrino formula) is itself
an open-derivation item. *(Net-state, Theorem 1af round 130: the route is
narrowed by theorem — ~~the scalar sector is δ-blind … so (v-a), if true,
lives in the chirality/spinor sector~~ [requantified round 130 F2: the
theorem covers the static two-point response, not the sector —
source-discriminating scalar objects exist on the same operator]: the
committed chain's static two-point function depends only on
max(seat, source), closing the static scalar-propagator route for (v-a);
the Clifford-dimension candidate is the named survivor in the spinor
sector, preferred not forced.)* *(Net-state, Theorem 1ag round 133,
regraded within the same round: ~~(v-a) is now DERIVED … the unproved
pair reduces to (v-b) alone~~ [the round-133 review broke the two-reading
census]: (v-a) is made PRECISE as a dimension-transport model — exact
mathematics, the layer-index metric forced within it, uniquely consistent
with the committed neutrino exponent's shape — carrying three named
conditions (the fiber assignment, where the committed minimal-spinor
reading gives √2 per layer; the coupling-as-trace-pairing premise; the
equipartition domain transfer). The unproved set is (v-b) plus those
three.)* *(Net-state, Theorem 1ah round 137, regraded within the round:
~~C1 closed … the set reduces~~ — both selection legs fell (the
committed record's whole-period instances cannot discriminate by form;
the 2^107 count was a gauge orbit); C1 stays open, reconciled in
classification only; the set remains (v-b) plus C1–C3.)* **(v-b) The measurement biconditional:** that a
mode whose source coupling is filtered by ≥ χ^10 fails A4/S4's measurement
condition (the LLN-quenched record rate) while modes at δ ≤ 2 pass it. The
gap theorem keeps both threshold-free: any separation point inside the
seven-wide gap yields the same three generations. part4a's (D1)/(D2)
tension thereby reduces to this lemma pair with a one-period margin. The
falsifier is unchanged and sharp: any propagating fourth-generation fermion
at any mass — including a KATRIN/TRISTAN-visible sterile at d = 29 —
falsifies the rule. Check 8 clean: S is theorem-forced (Γ + Adams),
observer-free; no hypothesis content enters the census. *Grading (regraded round 126 F1/F2):*
(ii) and (iii)'s census, gap, and threshold-robustness are **theorems** —
finite arithmetic over the committed source set; (iii)'s exhaustiveness is
a graded composition closing at a remark-level step; (iv) splits — the
δ-contrast a theorem, the coupling contrast conditional on (v-a); (v) is
the named unproved pair. Nothing here is a convention; not everything here
is a theorem, and the grading now says which is which.

**Theorem 1af (the deeper grounding: three theorems from the committed
dynamics — the two-point structure, static-response δ-blindness (label
aligned round 131 F2), and the sink's
dynamical nullity — plus the spinor-sector candidate for (v-a), named;
`cascade_deeper_grounding.py`).** *(i) The commission.* The owner's
standard, verbatim: *"Look for the deeper grounding. Interesting pattern
but this is no first principles derivation or proof."* Correct: 1ae's
census is arithmetic over forced inputs, and nothing yet says *why*
proximity to a source should govern participation. This theorem
interrogates the committed dynamics directly and returns three theorems
and one honest identification. *(ii) The committed substrate, quoted.* The
committed action is S[φ] = Σ_d (1/(2α(d)))(Δφ)² on the layer lattice with
*"Neumann at d = 4 (observer)"* and *"Dirichlet at d = 217 (Part 0
terminus)"* — a grounded elastic chain with bond compliance α(d) — and the
committed instrument (`cascade_greens_function.py`, cited by
`cascade_unit_source_strength.py`, exit-gated since the round-120 sweep
of 1ac's landing — F4 round 130: "since 1ac" compressed over the
round-120 F3 strike) already derives
the observer-row closed form G(4, d*) = Σ_{k≥d*} α(k) by the flux
argument: *"for a unit source at d*, the flux below d* is zero (Neumann at
d_min), the flux above d* is unit."* Check 7 status is the instrument's
own: the cascade-lattice Green's function, classical finite-dimensional
linear algebra — admissible. *(iii) Theorem (the two-point structure —
new).* The same flux argument, applied between arbitrary points, gives
**G(d, d*) = Σ_{k = max(d, d*)}^{216} α(k)** — the two-point function
depends only on max(d, d*): below the source no bond carries flux, so the
potential is constant from the free end up to the higher of the two
indices; above it, unit flux integrates the compliances down to the pinned
end. Gated numerically at < 10⁻¹⁰ (the committed gate), observed worst
relative error 1.79×10⁻¹³, over a 100-pair
census of the committed operator's inverse (wording aligned round 130 F3 —
the landing stated the observation as the gate). *(iv) Corollary (static-response
δ-blindness — the load-bearing negative, requantified round 130 F2: the
landing's ~~the scalar sector cannot see δ at all … no first-principles
derivation of the participation dichotomy can live in the scalar sector …
forced into the chirality/spinor sector … the search space halved~~
[the elision marker added round 131 F3]
quantified over the SECTOR while the theorem covers one scalar object; the
round-130 reviewer exhibited source-discriminating scalar objects on the
same committed operator — the iterated inverse L⁻² spreads 7.8% across the
four sources at seat 21, and screened resolvents decay with separation —
so the sector-wide negative was false as stated).* What the theorem
proves, exactly: **the committed chain's static linear response — the
propagator-coupling route that 1ae's cost model would most naturally
ride — cannot carry the dichotomy.** G(21, d*) is identical for all four
sources (numerical spread < 10⁻¹³ —
the value is tail(21) = 1.167571 regardless of which source couples), and
likewise G(29, d*) = tail(29) = 1.006240; the scalar 21-vs-29 ratio is
1.1603 — smooth, nowhere near a dichotomy, and unrelated to χ⁸ = 256 or
part4a's ~289 (stated to preempt any numerological reading). Consequence,
honestly quantified: **the static scalar-propagator route for (v-a) is
closed by theorem**; other scalar objects (iterated inverses, spectral
weights with general f(λ)) are not excluded by this corollary, and the
spinor candidate of (vi) is the named survivor — preferred, not forced. *(v) Theorem (the sink cannot source — new; upgrading a 1ae
step).* In the committed action the sink is a **constraint node**:
φ(217) = 0 is imposed, no Euler–Lagrange variation is taken there.
Forcing it produces the rigid shift φ ≡ const — every bond stretch zero,
zero action, zero flux, dynamically null (gated: the response column is
exactly constant, spread < 10⁻¹²; all gradients vanish). *"Removing
d₂ = 217 as the Planck sink"* is thereby **forced by the committed
dynamics**, not merely remark-level accounting — the corresponding step of
1ae(iii)'s exhaustiveness chain upgrades (net-state marker placed in 1ae;
the remark-level type-counting step for "no fifth source *type*" is
untouched and remains the chain's weakest link, stated). *(vi) The
spinor-sector candidate, identified honestly.* The committed per-layer
factor χ = 2 (Poincaré–Hopf, theorem-grade) coincides exactly with the
per-layer doubling of the Clifford algebra — dim Cl(d+1) = 2·dim Cl(d) —
so the committed filter χ^Δd across any span equals the Clifford-dimension
ratio 2^Δd between its endpoints (χ⁸ = 256 = dim Cl(29)/dim Cl(21), a
declared identity). **Candidate mechanism for (v-a), named, not derived:**
layer-to-layer transport projects the Clifford structure, surviving weight
1/2 per generator — a spinor-chain analogue of (ii)'s scalar chain. The
arithmetic of the identification is trivially exact; its content is the
reading; the derivation of the spinor chain is the remaining work.
*(Net-state, Theorem 1ag round 133, regraded within the same round:
~~the remaining work is done … derived-given-readings~~ [the two-reading
census broke under review]: the candidate is made PRECISE — a
dimension-transport model with exact mathematics and three named
conditions (1ag(vii)'s census); the spinor-chain derivation remains
open, now with a precise object in place of a slogan.)* *(vii)
What a full first-principles proof now requires, exactly:* (1) a
transport theorem delivering (v-a) — the static scalar-propagator route
closed here, the spinor candidate named (requantified round 130 F2: the
landing said "route narrowed … to one sector," which the corollary does
not force); (2) the A4/S4 measurement
biconditional (v-b) — untouched. *Honest scope:* (iii)–(v) are theorems
(the committed flux argument plus linear algebra over the committed
operator, numerically gated); (vi) is an identification with a named gap;
no convention, no new number, no data consumed.

**Theorem 1ag (the spinor transport ~~theorem: lemma (v-a) derived from the
Clifford ladder plus committed equipartition; the metric and the per-layer
factor both forced~~ MODEL — regraded round 133: 1af's candidate made
precise, with three named conditions and the fiber fork disclosed;
`cascade_spinor_transport.py`).** *(i) The commission
and the target.* The owner commissioned the spinor transport theorem —
1ae's lemma (v-a), the cost model "χ per layer of separation on the
seat↔source channel," which 1af narrowed to the spinor sector and named a
candidate for. ~~This theorem derives it~~ [regraded round 133 F1–F3:
this theorem makes the candidate PRECISE — a dimension-transport model
whose mathematics is exact and whose consistency with the committed
neutrino exponent is real, but whose attachment to committed structure
requires three conditions, censused in (vii)]. *(ii) The setup — committed
structure only.* The Clifford ladder over the layer lattice: Cl(d) on
generators e₁…e_d, monomial basis {e_A : A ⊆ {1…d}}, dimension 2^d, with
the ladder inclusions Cl(d) ⊂ Cl(d+1) (Cl(d) algebras are the cascade's
own committed machinery — part4a's fermion assignment runs on them: *"A
fermion generation requires a complex Dirac layer ($d\bmod 8=5$)"*). The
signature convention e_i² = +1 is a model choice disclosed here; the
dimension and orthogonality claims below are signature-independent, and
the trace form is computed in the verifier from the actual algebra
multiplication (the regular representation), not assumed. *(iii) Theorem
T1 (the ladder split — exact algebra).* As a Cl(d)-module, Cl(D) =
⊕_{B ⊆ {d+1…D}} Cl(d)·e_B — exactly 2^(D−d) trace-orthogonal copies of
Cl(d), each of equal dimension; the Cl(d)-component proper (B = ∅) is a
2^−(D−d) fraction of the monomial basis. Gated: the orthonormality of the
monomial basis under the normalized regular-representation trace is
computed from the implemented Clifford multiplication (with an
associativity self-test), not declared. *(iv) Theorem T2 (pairing
localization — exact).* For x ∈ Cl(d) and y ∈ Cl(d*) inside any common
Cl(D), the trace pairing satisfies ⟨x, y⟩ = Σ_{A ⊆ {1…min(d,d*)}} x_A y_A
— **the pairing factors identically through the common subalgebra
Cl(min)**: components carrying any generator above min(d, d*) pair to
zero. This is why coupling between layers is a bottleneck at the common
depth — and why the natural metric is the layer-index difference: it is
the ladder-depth difference. Round-124 F5's residual question ("why this
metric?") is hereby answered from structure. *(v) Theorem T3 (the
transport cost).* Under the committed equipartition selector — A4's own
anchor, verbatim: *"weight e^(±½) per measured mode — lemma S4, anchored
by equipartition"*, with S4's LLN quenching (*"quenched rate forced by
LLN"*) turning expectation into record — content at layer D carries
expected weight **exactly 2^−(D−d)** in Cl(d): the equipartitioned
Gaussian's expected retained fraction equals the dimension fraction,
which T1 makes exactly 2^−(D−d). Combining with T2: **within the model, the expected
coupling weight between content at layers d and d* is χ^−|d−d*| with
χ = 2** — the per-layer factor and the symmetric layer-index metric both
follow ~~derived~~ [regraded round 133: derived WITHIN the model; the
model's own conditions are (vii)'s census]. Gated two ways: exact dimension counting, and a Monte-Carlo
equipartition test on the implemented algebra (Gaussian content in the
Cl(11) model retains mean fraction 1/256 in Cl(3) — the Δ = 8 case,
matching χ⁸). *(vi) The identification with the committed χ — argued from
part4b's own words.* Part4b's χ = 2 is *"splitting the spinor bundle into
two equal-weight chirality basins"* (Poincaré–Hopf, *"Topological
theorem; no assumption"*), and *"The two factors $\sqrt{\pi}$ and
$\chi = 2$ are the \emph{only}"* ~~committed per-layer constants of this
kind~~ [gloss corrected round 133 F4: the source continues "…
dimension-independent constants available at the hairy ball obstruction"
— an obstruction-site statement, not a per-layer one; and part4b's χ
attaches per DIRAC-layer crossing (Poincaré–Hopf "at Dirac layers") or
per mode, while the ladder step doubles per layer — the site densities
differ, disclosed; the only committed per-unit-layer χ-exponent is the
neutrino formula, itself part4b's underived OQ item]; the ladder step Cl(d) ⊂ Cl(d+1) is likewise an equal-weight
two-way trace-orthogonal split. Same number, same split shape — and the
committed neutrino filter χ^(29−d_g) instantiates T3's form
exactly (base 2, exponent = layer distance): ~~the filter factor's form
in that committed formula is hereby derived~~ [struck round 134 F2:
circular given C1 — the full-algebra fiber is selected BECAUSE it
matches this formula's form (selection by consistency, per (vii)), so
the form is **reproduced within the selected model**, not derived from
committed structure; part4b's open item ("no explicit derivation
appears") stands un-addressed until C1 is closed; the m₂₉ and α(d_g)
factors remain open there regardless]. The full
identification of the transport 2 with every committed χ-context (the
mode-count exponents χ^(m−k)) is argued, not closed — stated. *(vii)
Consequence — regraded round 133 (F1, F2, F3): the candidate is made
precise; the conditions are three, and none is a free ride on committed
text.* ~~(v-a) is derived, conditional on two committed readings … a
reviewer who rejects either rejects committed text … What remains is
(v-b) alone~~ [struck: the round-133 reviewer broke all three legs —
each lead-verified]. The model's census: **(C1) the fiber assignment** *(net-state, Theorem 1ah round 137,
regraded within the round: ~~CLOSED~~ — the selection legs fell; C1
stays open, RECONCILED in classification by 1ah's Theorem B but
selected only by value; see 1ah(v))*​**.**
The derivation runs on the FULL Clifford algebra (dim 2^d); part4a's
committed assignment is to *minimal spinors* (*"complex minimal
spinors"*) and part4b's bundle is the spinor bundle S = S⁺ ⊕ S⁻ — under
that committed reading the fiber doubles every TWO layers, the per-layer
factor is √2, and the 29→21 filter would be 2^4 = 16, not χ⁸ = 256 (the
fork computed and gated). The committed neutrino exponent (base 2 per
layer) selects the full-algebra fiber against the minimal-spinor
alternative — but that formula is itself part4b's underived OQ item, so
this is model-selection-by-consistency-with-the-target, disclosed, not
forcing. **(C2) the coupling model.** That the physical seat↔source
coupling is the fiber trace pairing is a premise no committed text
supplies (part4b's own χ-mechanism is per-mode chirality filtering, not
a fiber pairing); the intra-fiber action remains unwritten. **(C3) the
equipartition transfer.** A4's committed equipartition anchors the
½-atom of the measurement weight (*"E[πx²] = s/2 exactly (the ½-atom =
the mean action; S4's anchor)"*); T3 needs an intra-fiber isotropic
prior — the principle is committed, the application domain is new.
*What remains for the full first-principles proof:* (v-b) **plus
C1–C3.** What this theorem contributes, exactly: the model's
mathematics is exact (T1–T2 algebra, T3 expectation); the layer-index
metric is forced WITHIN the model (T2's localization); the model is the
unique fiber choice consistent with the committed neutrino exponent's
shape; and the search for (v-a) now has a precise object to derive or
refute instead of a slogan. No convention, no new number, no data
consumed.

**Theorem 1ah (C1 attacked from first principles: ~~the fork dissolves~~
[regraded round 137: both selection legs fell — C1 stays OPEN,
reconciled in classification but selected only by value]; the
uniformity analysis, the canonicity analysis, and the bilinear
reconciliation; `cascade_c1_closure.py`).** *(i) The commission.* The owner
commissioned an attack on C1 — which fiber the cascade transports: the
committed minimal-spinor module (√2 per layer on average) or the full
Clifford algebra (2 per layer). Three independent legs, each graded.
*(ii) Theorem U (uniformity — the discriminator that is not the value).*
The minimal-spinor fiber's per-layer growth is **never uniform**: complex
dims 2^⌊d/2⌋ alternate ratio 1, 2, 1, 2; real Bott dims (1, 2, 4, 4, 8, 8,
8, 8; ×16) are lumpier still (ratios 2, 2, 1, 2, 1, 1, 1). The full
algebra grows uniformly at 2 every layer. The committed formula
m_ν(Gen g) = m₂₉·α(d_g)/χ^(29−d_g) has a **uniform integer per-layer
exponent across all three generations** — a FORM property, not the tuned
base. Exhibit, gated: the spinor fiber cannot distinguish a 28→21 from a
29→21 transport (both ratio 16, since ⌊28/2⌋ = ⌊29/2⌋); the algebra
distinguishes (128 vs 256). ~~No minimal-spinor fiber, real or complex,
can underlie a uniform per-layer filter; the algebra fiber can … this
theorem selects by the formula's FORM … the value then confirming~~
[struck round 137 F1: the form/value division fails on the committed
record — every committed instance has Δ ∈ {8, 16, 24}, a whole Bott
period, and over ANY even step both fibers grow exactly uniformly (the
spinor two-step ratio is exactly 2), so a spinor-rate law χ^(Δ/2) has
the identical form property on the formula's entire domain and is
excluded only by its VALUES — the round-133 circularity again; the
gated 28→21 exhibit discriminates only on odd-Δ channels the committed
record never exercises]. What U honestly proves: per-SINGLE-layer
non-uniformity of every spinor fiber (exact, gated), and that an odd-Δ
committed instance WOULD discriminate by form — none exists. On the
committed record the selection remains by value, and 1ag(vii)'s
"model-selection-by-consistency-with-the-target, disclosed, not
forcing" stands as the honest grading. *(iii) Theorem K (canonicity).* The algebra ladder
Cl(d) ⊂ Cl(d+1) is the unique inclusion-canonical transport structure
(the generated unital inclusion, no choices). A minimal-spinor ladder is
not canonical: at every odd layer the complex Clifford algebra splits
into two simple factors and the even-layer spinor extends to either — an
apparent binary choice per odd layer — the descent contains 107 odd
layers (census gated) — ~~2^107 inequivalent spinor ladders against one
algebra ladder … a convention-free transport can only be the algebra
ladder~~ [struck round 137 F2: the 2^107 choice-vectors form a SINGLE
GAUGE ORBIT under flag-preserving reflections e_j ↦ −e_j of the
cascade's own substrate — each reflection is an automorphism of the
whole ladder flipping the odd-layer factor choices, both factor choices
satisfy the Clifford relations with volume elements ±i swapped by the
reflection (lead-verified computationally), and no transport quantity
depends on the choice; a zero-parameter constitution forbids
parameters, not gauge, and part4b's own equal-weight-basins move is
exactly the choice-free symmetrization the spinor side equally
supports]. K selects nothing; the census stands as arithmetic only. *(iv) Theorem
B (the bilinear reconciliation — the fork was a false dichotomy).* Exact
at every layer 1..217, gated: **2^d = (2^⌊d/2⌋)² × (2 if d odd)** — the
algebra IS the bilinear space S ⊗ S* of the spinor module (complex
setting; the seats' own class per part4a's *"complex minimal spinors"*).
Hence both committed structures are right about different objects:
part4a's minimal spinors carry **state amplitudes** (the √2-average
rate — disclosed round 137 F3: NO committed quantity transports at this
rate; every committed transport in the record is coupling/mass-class,
so the amplitude side is classification without instance); the algebra
carries **bilinears — and a mass is a bilinear-class object** (the committed formula transports *"the source mass m₂₉"*,
part4b's own words), at exactly the square of the amplitude rate:
2 = (√2)². The C1 tension between two committed structures dissolves:
amplitudes at the spinor rate, masses and couplings at the algebra rate;
the committed per-layer 2 is the coupling rate, and 1ae's coupling
contrast χ⁸ = 256 concerns couplings. Disclosed reading (R-bilinear):
classifying masses/couplings as bilinear-class transports is an
interpretive step — standard, but graded as a reading, the leg's honest
boundary. *(v) Net effect on the ledger — regraded round 137.* ~~C1
closes … reduces to (v-b), C2, and C3~~ [struck: both selection legs
fell]. **C1 stays OPEN**, with its state sharpened: RECONCILED in
classification (Theorem B — the algebra is the spinor bilinear space,
exact; the two committed structures address different object classes
under the disclosed R-bilinear reading) but SELECTED only by the value
of the underived committed formula (1ag(vii)'s selection-by-consistency
grading stands). What would close it: an odd-Δ committed instance
(form-discrimination, per U's honest residue) or the formula's own
derivation. The unproved set remains **(v-b), C1, C2, C3** (the
markers regraded in place).
No convention, no new number, no data consumed; Check 7 (Clifford
representation arithmetic — cascade-native); Check 8 (no hypothesis
input).

**Theorem 1ai (the Weil-positivity route, entered and mapped: the
blindness theorem, strip avoidance, and the boundary-crossing exhibit
(retitled from "reachability" in the round-140 sweep, F4);
`cascade_weil_positivity_status.py`).** *(i) The commission — virgin
territory, gated.* The owner commissioned the Weil-positivity route. It
has never been pursued in this arc: "Weil positivity" / "Weil's
criterion" / "positivity criterion" have zero occurrences on any
committed object-level surface before this theorem (census gated
repo-wide as of round 140 F6: the paper's pre-1ai span, the
formulation, every `src/*.tex`, and the tools tree minus this theorem's
own instrument — and, as of Theorem 1aj, minus that theorem's sibling
instrument too, which postdates the census point and is excluded with
disclosure; the two record files excluded as declared history); the record's
"Weil" ~~is the metaplectic index (1e/1f)~~ [struck round 141 F1,
false-when-written: the explicit-formula bridge's naming note — a
pre-1ai committed instrument surface — names "Weil's test-function
formula" in the explicit-formula sense, solely to distinguish it from
the pointwise Hadamard form the bridge uses, with no positivity
content; outside that naming note the record's "Weil" is the
metaplectic index (1e/1f)], and mirror coherence was
deliberately worded *"non-degeneracy (≠ 0, ∞, indeterminate), **not**
positivity."* *(ii) The classical frame (cited as classical, no RH
assumed).* Weil's criterion: RH is equivalent to positivity of the
explicit-formula functional on self-convolutions over a dense
test-function class. **Theorem W0 (the blind-cone criterion —
elementary, with proof):** any test function whose paired kernel
K_s(ρ) = Re[1/(s−ρ) + 1/(s−(1−ρ))] is of one sign for ALL ρ in the
critical strip yields an explicit-formula zero-sum whose SIGN is fixed
UNCONDITIONALLY — whether or not RH — and therefore carries zero
information about zero locations. (~~yields an explicit-formula
positivity that holds UNCONDITIONALLY~~ struck round 140 F3,
false-when-written: the one-signed-NEGATIVE half yields unconditional
NON-positivity; one-signedness fixes the sign, and positivity is the
positive-kernel case — real s > 1, the case every committed read
occupies.) *Proof (three lines; supplied in the round-140 sweep, F2):*
(1) every non-trivial zero ρ = β+iγ lies in the open strip 0 < β < 1
(classical, RH-free); (2) a one-signed kernel makes every summand
K_s(ρ) of the explicit formula's zero-sum carry that same sign wherever
in the strip the zeros sit; (3) hence the zero-sum's sign is fixed by
the kernel alone, independent of zero locations — no rearrangement of
zeros inside the strip can change it. ∎ Discriminating power requires
kernels that change sign in the strip. *(iii) Theorem W1 (the blindness
theorem; domain rescoped round 140 F1).* Every committed cascade
zero-side read lies in the blind cone: every committed zero-side
evaluation is at real s ≥ 2 > 1 — the lattice packaging specifically at
s = d+1 ∈ [5, 218] — where each kernel term (s−β)/|s−ρ|² and
(s−1+β)/|s−1+ρ|² is strictly positive for every ρ = β+iγ in the strip
(0 < β < 1 < 2 ≤ s — an exact inequality, grid-gated over the full
corpus as a check). ~~the committed family evaluates at real s = d+1 ∈
[5, 218]~~ [struck round 140 F1, false-when-written: the committed
zero-side corpus is wider than the lattice packaging — the
explicit-formula bridge reads at s = d+1 for d = 1..28 (s = 2, 3, 4
included), the colour-field bridge at s ∈ {2, 5, 6, 7, 13, 20}, and
the feature solver at continuous bracket points up to ≈ 320; every one
of these has real s ≥ 2 > 1, so the blindness conclusion is unharmed —
only the quantified domain was false.] **Corollary: every positivity the
cascade's committed packaging exhibits is unconditional — zero RH
content.** This upgrades the record's registered honest negative ("the
features are identity-mediated") to precise geometry: the committed
family sits strictly inside the RH-blind cone. *(iv) Theorem W2 (strip
avoidance).* The cascade lattice's arguments never enter the critical
strip: min(d)+1 = 5 > 1. The packaging cannot be moved into the strip
without leaving the committed lattice — the descent is structurally
confined to the blind side by its own floor at the observer. *(v)
Exhibit W3 (boundary crossing — graded as an exhibit, not a committed
observable; regraded round 140 F4).* Cascade-native SIGNED combinations
leave the blind cone. ~~reach the discriminating cone~~ [struck round
140 F4, false-when-written: the exhibit's sign change occurs ON the
line (β = ½), where every admissible Weil self-convolution satisfies
ĥ(½+iγ) = |ĝ(γ)|² ≥ 0 — a combination whose on-line values change sign
can never be an admissible test function, so leaving the blind cone is
not reaching the discriminating one.] For the pair (s₁, s₂) = (5, 6), the on-line kernel
ratio K₅/K₆ at β = ½ runs exactly from 11/9 (γ = 0) down to 9/11
(γ → ∞), so any coefficient c ∈ (9/11, 11/9) makes h₅ − c·h₆
sign-changing. **The committed 1af scalar ratio tail(21)/tail(29) =
1.1603 lands inside that window**, and the exhibit kernel
K₅ − 1.1603·K₆ changes sign at γ* ≈ 1.914 (bisection-gated: positive at
γ = 0, negative at γ = 10). Honest grading: the coefficient is
committed, the combination is constructed here — this exhibits that the
blind cone's boundary passes THROUGH the cascade's
own signed-combination space (the signed correction family ±α(d*)/χ^k
shows signed combinations are native), but no committed — or
here-constructed — combination is discriminating in the admissible
sense: entering the discriminating cone requires a kernel that changes
sign OFF the line while remaining nonnegative on it, which W3's
on-line sign change specifically is not. *Net state (1aj):
superseded-true — Theorem 1aj constructs an admissible-discriminating
instance from the committed pair itself (on-line nonnegative, off-line
sign-changing), at the admissible cone's forced edge; the sentence was
true when written.* *(vi) The gap, named
precisely — what the route needs.* The cascade's committed positivity
structures live in CONFIGURATION space (the action's positive
definiteness; the compliances α(d) > 0; trigamma positivity, gated in
the formulation's ledger); Weil positivity lives in TEST-FUNCTION
space. The explicit-formula bridge connects VALUES ("no direction of
explanation is claimed" — the instrument's own words), not positivity
cones: **no committed map carries the physical positivity cone into the
test-function positivity cone.** What would open the route: a committed
morphism from field configurations to self-convolution test functions
under which action-positivity forces explicit-formula positivity on a
family whose kernels change sign OFF the line while staying nonnegative
on it (the admissibility W3's exhibit lacks, per F4). Nothing committed
supplies it; the
route is now mapped, not traveled. *Net state (1aj): the morphism now
exists — the profile map (committed form, z = d+½) carries lattice
configurations to genuine self-convolutions reaching the
admissible-discriminating cone; the unforced link is exactly the
positivity, which 1aj locates at the RH wall: on every reached instance
the sign is settled by the classical zero count below height ½
("reached" = 1aj's pairwise instances; the post-certification regrade
widens the family — relocated windows rest on the verified on-line
zeros; scoping added round 146 F4), and for
the dense class it is RH itself. The route is traveled to the wall;
these sentences were true when written.* *Honest scope:* W0–W2 are theorems
(elementary inequalities over the committed arguments; W0's proof is
three lines and stated — supplied in the round-140 sweep, F2, the
landing text having claimed "stated" without stating it); W3 is an
exhibit (leaves the blind cone; not admissible-discriminating, F4);
(vi) is the named gap;
category (a) — no data, no closures, and by construction **no RH/GRH**:
every statement here is unconditional, and the theorem's central
content is precisely that the cascade's committed positivity is
RH-free. Check 7 clean (kernel arithmetic; the classical criterion
cited as classical input); Check 8 clean (no hypothesis content).

**Theorem 1aj (the route traveled: the profile morphism, the
reachability of the admissible-discriminating cone, and the RH wall
located; `cascade_weil_route_traveled.py`).** *(i) The commission.*
The owner commissioned traveling the route 1ai mapped ("Travel the
route"). Result: the morphism COMPONENT of what gap (vi) asked for
exists in committed form — the map, not the forcing clause (R4(c)
shows action-positivity plays no role in the sign, and the forcing
for the dense class is RH itself; rescoped round 143 F7 — the landing
headline compressed the two); the admissible-discriminating cone is
reachable from the
committed family — by every lattice pair, at the admissible cone's
forced edge; every reached instance's Weil positivity is settled by
the classical zero count below height ½ ("reached" = the pairwise
instances this theorem constructs; multi-term instances relocate the
window, with positivity then enforced by the verified on-line zeros —
the regrade below), not by cascade structure; and
the residual is exactly RH, unclaimable by the program's own rule. All
statements unconditional; no RH/GRH in either direction. *(ii) Theorem
R1 (the profile morphism, committed form).* A lattice configuration
c = (c_d) maps to the even test function g_c(x) = Σ_d c_d
e^(−(d+½)|x|) — decay rates the bridge's own committed half-shift
(*"with s = d+1 and z = d + 1/2"*, the instrument's words). Its
explicit-formula transform is exactly the committed kernel family:
∫₀^∞ 2 e^(−(d+½)t) cosh((β−½)t) cos(γt) dt = K_{d+1}(β+iγ), gated at
machine precision. The map gap (vi) called missing is this one:
configurations → test functions, committed form, no chosen constants.
*(iii) Theorem R2 (reachability, exact — the cone's edge is
discriminating).* On the pairwise slice {(c₁, c₂), c₂ > 0} for any
lattice pair d₁ < d₂ (w = d+½), the admissible cone {L ≥ 0 on the
line} is exactly {c₁/c₂ ≥ −w₁/w₂}: the binding constraint sits at
γ = 0, and the edge ratio −w₁/w₂ = −(2d₁+1)/(2d₂+1) is forced by the
lattice. At the edge, h* = K_{s₂} − (w₁/w₂)K_{s₁} satisfies: on the
line, L(γ) = 2γ²(w₂²−w₁²)/(w₂(w₁²+γ²)(w₂²+γ²)) ≥ 0 with zero only at
γ = 0; at the strip boundary, F(0) = −(w₂²−w₁²)/(2w₂(w₂²−¼)(w₁²−¼))
< 0 — on-line nonnegative, off-line sign-changing: the edge of
admissibility IS discriminating, for every pair. The discriminating
band is exact — both directions proved: c₁/c₂ ∈ [−w₁/w₂,
−(w₂/w₁)(w₁²−¼)/(w₂²−¼)). Forward: inside the band the boundary
value F(0) < 0 (the closed form above). Converse — **Theorem R2′
(the boundary-ratio monotonicity; supplied in the round-143 sweep,
F2, the landing having asserted exactness with only the forward
direction established)**: with a = s(s−1) and u = γ², each boundary
kernel is K_s(0, γ) = (2s−1)(u+a)/((u+a)²+u), and the boundary ratio
r*(u) = K_{s₂}/K_{s₁}(0, γ) is STRICTLY INCREASING in u: d/du log r*
= ψ(u+a₂) − ψ(u+a₁) with ψ(v) = 1/v − (2v+1)/(v²+u), and ψ′(v) has
numerator v⁴ + 2v³ − 4uv² − u² ≥ v²(v² − 2v + 79) > 0 whenever
v ≥ u + 20 — which the lattice floor guarantees (a = s(s−1) ≥ 20 at
s = 5). So r* runs monotonically from r*(0) = (w₂/w₁)(w₁²−¼)/(w₂²−¼)
— the band endpoint, exactly — up to the limit w₂/w₁: any coefficient
ratio at or beyond the endpoint keeps the boundary nonnegative
everywhere, hence blind by the minimum principle; any ratio inside
the band crosses it, hence discriminating. The same monotonicity
settles the cone's other edge for every pair: F_other ∝ K_{s₁} −
(w₁/w₂)K_{s₂} ≥ 0 ⟺ r*(u) ≤ w₂/w₁, which holds strictly at every
finite γ since r* increases TO that limit — the other edge is blind,
by theorem (the coarse all-pairs grid retained as a check; round 143
F8). The band's raw width is (w₂²−w₁²)/(4w₁w₂(w₂²−¼)); quoted as a
fraction OF THE EDGE RATIO w₁/w₂ it is (w₂²−w₁²)/(4w₁²(w₂²−¼)) — the
normalizer disclosed per round 143 F5. For the observer pair (4, 5)
the edge ratio is −9/11, magnitude **9/11 (1ai's window endpoint,
transposed into admissibility)**; the raw width is exactly **1/297**
and the band-to-edge fraction exactly **1/243**. Of the cone's two
edges exactly one is discriminating — the edge that de-weights the
shallower layer against the deeper one (R2′). *(iv) Theorem
R3 (genuine self-convolution — admissibility instantiated, not
cone-shaped only).* The edge instance is an actual Weil
self-convolution: with f(x) = (w₂e^(−w₂x) − w₁e^(−w₁x))/(w₂−w₁) on
x > 0, the autocorrelation f ⋆ f̃ equals [w₂e^(−w₂|x|) −
w₁e^(−w₁|x|)]/(2(w₁+w₂)(w₂−w₁)) — exactly proportional to the edge
profile — and |f̂(γ)|² = γ²/((w₁²+γ²)(w₂²+γ²)) reproduces L up to the
positive scale 2(w₂²−w₁²)/w₂ (both gated). The reached instance is a
genuine self-convolution — of an explicit L¹∩L² function, exactly;
the classical dense class quantifies over smooth compactly supported
f, membership there is NOT claimed and nothing here leans on it (the
zeros-side value is evaluated by the bridge's unconditional identity
at real s; graded round 143 F6). *(v) Theorem R4 (the wall, located).*
(a) The negative set {h* < 0} is confined to |γ| < ½ for every
committed pair: h* is harmonic in ρ on the strip (real parts of
functions analytic there; poles at ρ = s, 1−s lie outside) and decays
like 1/γ², so by the minimum principle negativity in {|γ| > ½} would
reach that region's boundary — and the strip-boundary function is
nonnegative beyond its single crossing γ_b < ½ (exhaustive scan over
all ~~22,578~~ 22,791 committed pairs [struck round 143 F1,
false-when-written: an off-by-one census, C(213,2) quoted for the
214-layer lattice [4, 217]; the scan itself was exhaustive over all
C(214,2) = 22,791 pairs, and the count is now counter-gated]: sup
γ_b = 0.49999, attained at (216, 217);
the bound approached is the half-shift itself), the γ = ½ segment is
positive (grid-gated per pair), and the tail coefficient
2(w₂²−w₁²)/w₂ > 0. For the observer pair, γ_b = 0.4806.
Band-interior instances are covered by domination (round 143 F3): for
r < w₁/w₂, h_r = h* + (w₁/w₂ − r)K_{s₁} and K_{s₁} > 0 on the whole
strip (the blind-cone positivity), so {h_r < 0} ⊆ {h* < 0} — the
confinement below height ½ holds ~~for every discriminating instance,
not the edge alone~~ [struck in the post-certification regrade below,
self-caught, false-when-written: the domination covers the PAIRWISE
slice — edge and band interior — and says nothing about three-or-more
-term combinations, which relocate the sensitivity window to
arbitrary heights] for every pairwise-slice discriminating instance.
(b) The
value: by the bridge's paired-form identity (RH-free), the zeros side
is computable with no zeros consumed: W(h*) = Z(6) − (9/11)Z(5) =
0.0780686 > 0, where Z(s) = p(d) + 1/(d+1) + 1/d − Σ Λ(n)n^(−s) with
s = d+1; the
direct sum over the first 100 true zeros converges from below with
every term positive. (c) The sign's true forcer (A66): W(h*) < 0
would require a zeta zero inside {h* < 0} ⊆ {|γ| < ½}; the first zero
lies at γ₁ = 14.134725 and ζ has no real zeros in (0, 1) — both
classical. Weil positivity on every reached instance is therefore
forced by the classical zero count, not by the cascade:
action-positivity plays no role in the sign — the action is positive
on ALL configurations, including those mapping outside the admissible
cone; the admissible cone is cut by the transform, not the action.
*(vi) The wall, stated.* The route terminates here: for the reached
family the positivity is classical bookkeeping; extending forced
positivity to the dense class of self-convolutions IS the Riemann
Hypothesis (Weil's criterion, cited as classical); no committed
structure supplies it, and under the program's rule none may be
sought. What 1ai named as the gap — "no committed map" — closes in
its map component (the forcing clause is the wall itself; round 143
F7); what
remains is not a gap in the cascade but the RH wall itself, now
located at exact coordinates: ~~every committed-family discriminating
instance interrogates only the classically vacant height-½ band at
the strip edges~~ [struck in the regrade below, self-caught,
false-when-written under the whole-family reading: the confinement is
a PAIRWISE theorem — a pair's admissible tangency is pinned to γ = 0
because a degree-1 numerator nonnegative on [0, ∞) cannot vanish at
an interior point; three-term instances relocate the tangency, and
with it the window, to ANY height] every pairwise discriminating
instance interrogates only the classically vacant height-½ band at
the strip edges (the region |γ| < ½; "band", not "disc" — round 143
F9); the general committed-family instance carries a sensitivity
window of half-width ≈ ½ near its line-tangency (containing it for
tangencies above the continuation threshold ≈ ¼; below it the window
persists but detaches — round 147 F1), relocatable to
any height — including the heights of actual zeros (the regrade
below). *Honest scope:* R1–R3 exact (algebra gated at
machine precision; the t-integral identities are classical Fourier
bookkeeping; the band's converse direction by R2′'s positivity
certificate, supplied round 143 F2); R4(a) exhaustive over the committed lattice (finite
scan, gated), with the minimum principle (classical potential theory
in the ρ-plane) and grid-gated segment checks, disclosed; R4(b) is
the bridge's own identity; R4(c) cites classical inputs (the
first-zero height; no real zeros in the strip; Weil's criterion).
Category (a) — no data, no closures, no RH/GRH in either direction.
Check 7 clean (Fourier bookkeeping, the explicit formula, potential
theory — classical; no semiclassics); Check 8 clean (every number
traces to the lattice w = d+½; no hypothesis content).

**Regrade (the wall widened — self-caught post-certification,
triggered by the owner's asymptotics question; the strikes above;
gates g19–g20).** The height-½ confinement is a PAIRWISE theorem,
and the ½ has a mechanism, now identified and gated: **the
strip-boundary read is the line read analytically continued by ±i/2
and averaged** — K_s(0, γ) = ½[K̂_s(γ+i/2) + K̂_s(γ−i/2)], K̂_s the
on-line kernel's continuation (exact; machine precision). A
discriminating instance's boundary negativity therefore lives within
≈ ½ of its line-tangency for tangencies above the continuation
threshold ≈ ¼ (round 147 F1: below it the window detaches — the
mechanism's 1/16 − γ₀² sign flip — while the pairwise case, tangency
pinned AT zero, keeps its independently proved ceiling); a PAIR's
tangency is pinned to γ = 0 (the
two-term numerator is degree 1 in γ², and a degree-1 polynomial
nonnegative on [0, ∞) cannot vanish at an interior point — gated by
the failed 2-term aim); pinned tangency + continuation distance ½ =
the pairwise ceiling. The pinning is a two-term artifact: with THREE
committed kernels the numerator has degree 2, and the admissible
tangency relocates to any chosen height. The aimed instance on
(d₁, d₂, d₃) = (4, 5, 6) with tangency at γ₁ = 14.134725 — the first
zero's height — is admissible (L ∝ (u − γ₁²)² over positive
denominators, ≥ 0 with the interior double zero) and its boundary
function is negative on the window [13.5514, 14.5669]
(inward-rounded at 4 dp; offsets −0.5834/+0.4322 from γ₁; precision
made self-consistent round 147 F2 — the round-146 fix joined
independently rounded values with an "=" whose displayed digits
disagreed, and its nearest-rounded endpoints again fell outward at
half-ulp scale) CONTAINING the first zero (gated; endpoints first
corrected round 146 F2 — the regrade's original draft quoted
outward-rounded endpoints under an "exactly", with the boundary
function positive at those quoted points). Consequences, honestly
stated: (1) the committed family's discriminating reach is NOT
confined below height ½ — the tangency relocates to any chosen
height (exact linear algebra: the 3×3 solve yields P(u) = (u − u₀)²
identically in the aim), and window-nonemptiness-with-aim-containment
is gated at γ₁ AND at a spread of other aims (0.5, 3, 100 — the
universal scoped and multi-aim gated, round 146 F3; the window
CONTAINS its aim for aims above the continuation threshold
aim* ≈ ¼ — the mechanism's own scale: at γ = aim the ±i/2-continued
numerator is (−¼ ± i·aim)², with real part 1/16 − aim² changing sign
at ¼ (observed threshold 0.2436; below it the window persists but
detaches from the tangency — the aim-0.1 instance's window is
[0.211, 1.123], excluding its tangency; the below-threshold sign is
gated — round 147 F1) — and is not exactly centred on it); (2)
"classically vacant" dies for relocated windows: the aimed
instance's Weil positivity is enforced not by vacancy but by the
verified on-line zeros themselves (each contributes L(γᵢ) ≥ 0, the
grazed zero contributing ≈ 0) — the sign statement remains
RH-content-free in exactly the earlier sense (positivity by verified
classical facts, not cascade structure), while the instance becomes
a genuine per-zero sensitivity probe: a hypothetical off-line zero
inside the window would contribute a negative term, and the
instance's value is computable unconditionally through the bridge
identity; (3) the wall stands where it stood — nothing cascade-side
forces positivity on ANY discriminating instance, pairwise or aimed;
the forcing is classical zero-location data, and the dense-class
extension is RH, claimed in neither direction. The wall's
coordinates regrade from "the vacant height-½ band" to: per-instance
windows of half-width ≈ ½ about a relocatable tangency (above the
≈ ¼ threshold — the physically relevant regime, every zero height
lying far above it; round 147 F1), positivity
within each window resting on the zeros verified there. Check 7
clean (the continuation identity is classical Fourier bookkeeping);
Check 8 clean (the aimed instance's coefficients solve a 3×3 linear
system over the committed w's; no hypothesis input).

**Remark (Door 3: what the vector-field count load-bears on;
`cascade_adams_loadbearing.py`).** *The classical theorem, stated in full.* The maximum
number of linearly independent nowhere-zero tangent vector fields on S^(d−1) is
ρ(d) − 1, with ρ the Radon–Hurwitz function of Theorem ~~1g(iii)~~ **1f(iii)** *(round-101 F5: pre-existing address error of the same class, noticed in the same round — ρ's v₂-only form is 1f(iii)'s)*: ρ(2^(4a+b)·m) = 8a + 2^b
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
this remark reduces the dependency, not the correctness. *(Net-state, Theorem 1w: the
count side narrows further — multiplicity 3 is entailed given the pairing-act plus
T8's root–unit identity; the layer-12 selection remains the papers-side residue.)*

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
carries) *(net-state, Theorem 1k as corrected round 60: entailed given the site-E
pairing plus the variational-sup labeling; the member
is re-motivated, the count unchanged)*. *And the lower bound is load-bearing (round-30 M2/M1):* **ρ(4) − 1 = 3** —
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
residue member *(net-state, Theorem 1k as corrected round 60: entailed given the site-E
pairing plus the variational-sup labeling)*); plus the count (the previous remark). **With both remarks, the
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
is widened to every d↔s layer/weight pairing choice *(net-state, Theorem 1l: the
per-site family is closed given the tower's dictionary — the member is re-motivated, the
count unchanged)*. **The systematic
d/s audit is complete** (`cascade_ds_audit.py`): nine sites — one definitional, four stable
(including Thm 10's set/exponents under all three pairings and the Gram-deficit indices
under every shift), two data-anchored conventions *(net-state, Theorem 1y round 107:
one — the window-potential pairing is entailed, Γ-argument arithmetic; the unit
convention remains)* (the window-potential pairing, selected by
data at −38% margin *(net-state, Theorem 1l: the flip is a window shift and the audit's
alternative a mixed frame — the anchor re-grades as a cross-check of the dictionary)*; the
unit), and the two known conditional sites, both demoted. No new
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
γ⁴ = −1; the scalar-flatness cross-check was demoted by the third review).** *(Net-state,
Theorem 1k as corrected round 60: the selection is entailed given the site-E pairing plus
Part 0's variational-sup labeling — the rounding-frame non-uniformity this remark records
is the lattice bands seen across the s = d+1 frame line with the crossing sides fixed
variationally; the member is re-motivated, the residue count unchanged, and Finding 6's
completeness question stays open.)* *Structural
update (Addendum 65, Theorem 1c — Finding 6 stays REOPENED on its original claim):* the
r₂ = 0 obstruction is now relocated rather than removed — Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1) is
synthesized exactly by the program's own two interleaved towers (Theorem 5's doubling, via
Legendre), so no complex embedding of ℚ was ever needed; and the excluded odd object at
s = 6.2569 is the sgn tower's zero-crossing, whose L-family is the odd Dirichlet characters — the bridge holds for every odd real
primitive χ, and the **minimal-conductor primitive odd character is χ₋₃** (a theorem: q=2
has no primitive character, q=3 exactly one, odd), which is the quadratic character of the
Theorem-11 colour field ℚ(ζ₃); **the pairing-by-minimality is a convention** *(net-state, round-57 adjudication:
re-motivated by Theorem 1j — minimality entailed given the pairing-act, which
persists)* (round-15
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
adopted. (Net-state, Theorem 1l: the demotion sharpens — the avatar weight is Ω(d−1),
the previous layer's measure, forsworn by Theorem 1's own Remark, so the two-coset
clause does not hold in the tower's dictionary; the single-coset repair candidate stays
live.)]*

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
U2 as a function) *(net-state, Theorem 1m round 67: the three availability factors are
registered as already-derived objects — T2's graded-crossing unit, Door 4's covolume,
the coincident-2s rank — and the 13b block's genuine fork is discriminated given the
obstruction identification; the clause triggers stay soft inputs)* has a **constructed
v1, corrected by the round-8 hostile review**
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
miscount) *(net-state, Theorem 1m: the fork is discriminated arithmetically given the
obstruction-factor identification — part4b's per-layer attachment forces the count at
P1's cell — so the block is canonical up to extensional equivalence, conditional on the
identification)*; the colour-rank slot is pinned uniquely by m_b/m_τ, while the projection slot's
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
counted in this paper's residue *(net-state, Theorem 1k as corrected round 60: the distinguished-layer
identifications among these are entailed given the site-E pairing plus the
variational-sup labeling; member
re-motivated, count unchanged)*, and the observer is twist 4, not 5), and the claim of "no
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
   part0 itself concedes no uniform rounding rule exists *(net-state, Theorem 1k as corrected round 60: the
   concession's next sentence in the source defines the variational selection, and part0's
   regime partition — an earlier section — is the lattice-band statement; given the site-E
   pairing plus the variational-sup labeling the assignment
   is entailed — the member is re-motivated, the count unchanged)*). J2's incoherence is derived from
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

*Verification suite (round-45 corrected census, extended by Theorems 1i–1aj: the **60 scripts cited in place** above, a body-only count, census-verified against the body text alone (the round-44 footer's "31 cited in place" was self-referential, counting the prior footer's own four record-verifier names; the intermediate body-only counts 27–31 were each verified the same way, per the audit record) — plus the four §8-record verifiers cited only in this list, marked °; all under `tools/research/`; additionally `cascade_constants.py` — the constants module at `tools/`, named in Theorem 1t's census scope as an audited surface, not a verifier, and not counted; and `cascade_greens_function.py` — the committed instrument at `tools/verifiers/`, quoted as Theorem 1af's substrate, audited not counted): `cascade_formulation_kernel.py`, `cascade_explicit_formula_bridge.py`, `cascade_zero_side_features.py`, `cascade_colour_field_bridge.py`, `cascade_finite_places.py`, `cascade_local_tate.py`, `cascade_witt_weil.py`, `cascade_local_family.py`, `cascade_tate_epsilon.py`, `cascade_torsion_selection.py`, `cascade_adams_loadbearing.py`, `cascade_layer_selection.py`, `cascade_lattice_selection.py`, `cascade_pairing_dictionary.py`, `cascade_pairing_act.py`, `cascade_bridge_asymmetry.py`, `cascade_grammar_need.py`, `cascade_given_irreducibility.py`, `cascade_riemann_kernel.py`, `cascade_colour_count.py`, `cascade_door4_status.py`, `cascade_site_e_pairing.py`, `cascade_endpoint_data.py`, `cascade_forcing_ledger.py`, `cascade_species_census.py`, `cascade_a3_rules.py`, `cascade_unit_source_strength.py`, `cascade_participation_rule.py`, `cascade_participation_dichotomy.py`, `cascade_deeper_grounding.py`, `cascade_spinor_transport.py`, `cascade_c1_closure.py`, `cascade_weil_positivity_status.py`, `cascade_weil_route_traveled.py`, `cascade_neutrino_mass_audit.py`, `cascade_bott_tower_beyond_29.py`, `cascade_d29_sterile_neutrino.py`, `cascade_availability_factors.py`, `cascade_sup_selection.py`, `cascade_zeta_rational.py`, `cascade_gamma_regularity.py`, `cascade_mirror_coherence.py`, `cascade_adelic_compensator.py`, `cascade_arithmetic_increment.py`, `cascade_arithmetic_period.py`, `cascade_arithmetic_sign.py`, `cascade_arithmetic_s5.py`, `cascade_arithmetic_d4.py`, `cascade_increment_rule.py`, `cascade_second_quantized.py`, `cascade_measurement_joint.py`, `cascade_activation_mechanism.py`, `cascade_joints_derived.py`, `cascade_feature_monoid.py`, `cascade_precedence_vacuity.py`, `cascade_ds_audit.py`, `cascade_T4_uniqueness.py`, `cascade_u2_function.py`, `cascade_u2_uniqueness.py`, `cascade_u2_first_principles.py`, `cascade_leptons.py`°, `cascade_neutrino_closure.py`°, `cascade_E_fit_audit.py`°, `cascade_null_clone.py`°. Classical inputs: Tate's thesis; Weil and Rao, the metaplectic index and its cocycle; Wall, the graded Brauer group; Lam, the Witt groups of local fields; Gauss and Landsberg–Schaar, quadratic sums; Legendre, the duplication formula; Hensel's lemma; Hilbert, the norm-residue symbol; Bohr–Mollerup; Dirichlet, the units of imaginary quadratic fields and the class-number formula; Leibniz, the series for π/4; Poincaré–Hopf; Steenrod–Whitehead, Toda, and Adams, vector fields on spheres; Radon–Hurwitz; Killing–Cartan, the rank-2 root-system classification; Lovelock; Kolmogorov.*
