# The Cascade as a Theorem of Number Theory: A Formulation

**Status:** formal skeleton, written under the stopping rule of Addendum 30 (admissible
category (a): work checkable without reference to data). This document states exactly what can
be a theorem, what is currently an axiom, and what can never be a theorem. Machine
verifications: `tools/research/cascade_formulation_kernel.py` (T1),
`cascade_second_quantized.py` (T2), `cascade_epsilon_dictionary.py` (T3),
`cascade_null_clone.py` (the numerical shadow of T4).

## 0. Notation

Γ_ℝ(s) := π^(−s/2) Γ(s/2) — the archimedean Euler factor of the completed Riemann zeta
function ξ(s) = ½ s(s−1) Γ_ℝ(s) ζ(s), with ξ(s) = ξ(1−s).

## 1. The axiom system

**A1 (Arithmetic kernel).** The state space is the descent lattice ℕ (layer index d), weighted
by Γ_ℝ; the dynamics is the unique Gaussian elastic action with bond compliance α(d)
(uniqueness: papers' `rem:action-uniqueness`).

**A2 (Local-constant calculus).** Every multiplicative factor attached to a descent is drawn
from the local constants of the adelic structure:

| Constant | Identity | Arithmetic home |
|---|---|---|
| χ = 2 | \|μ(ℝ)\| | torsion of the real units |
| Γ(½) = √π | Γ_ℝ critical value | the functional equation's symmetry point |
| 2π | χ·Γ(½)² | Tate's self-dual period at the real place |
| ½ | half-argument of Γ_ℝ | the Gaussian, Tate's self-dual test function |
| mod-8 grading | Brauer–Wall group BW(ℝ) ≅ ℤ/8 | graded Brauer group of the real place (Wall 1964) — the arithmetic avatar of Bott/Clifford periodicity |
| N_c = 3 = 2^(v₂(12))−1 | Radon–Hurwitz count | a 2-adic invariant (value depends only on v₂) |
| cos(π/6) | weight–root angle of ℤ[ω] | ring of integers of ℚ(ζ₃) |
| phases i, ζ₈ | quaternionic frame, Bott | the cyclotomic tower ζ₂, ζ₃, ζ₄, ζ₈ |

**A3 (Assignment rules).** Which constant attaches where: the source-selection flags (P, L, G)
as ξ-occupancy functors; the increment rule (corrections attach once, at sub-lead); source
layers at the analytic features of Γ_ℝ; the per-Bott-period attachment below the phase
transition. *This is the load-bearing axiom.* Partial derivation exists (Addendum 12: the
flags recovered 9/9 from ξ's factorization); the increment and per-period rules are underived.

**A4 (Measurement).** Measurement records the typical value of a Gaussian mode (weight
e^(±½) per measured mode — lemma S4, anchored by equipartition); projection is along root
frames (lemma S5).

## 2. The theorems

**T1 (Kernel — PROVED, elementary).** The cascade's four primitive families are exactly the
log-geometry of Γ_ℝ at integer arguments:

- Ω(d) = 2/Γ_ℝ(d+1)  (sphere measure = reciprocal Euler factor)
- N(d) = Γ_ℝ(d+1)/Γ_ℝ(d+2)  (coupling = Euler-factor ratio)
- p(d) = (log Γ_ℝ)′(d+1)  (potential = logarithmic derivative)
- α(d) = N(d)²/4π  (compliance)

Each is an elementary Gamma identity; machine-verified to ≤7×10⁻¹⁴ across d = 1–300
*(round-43: requoted from a false ≤6×10⁻¹⁴ — the N(d) residual is 6.44×10⁻¹⁴; the
standalone paper's copy was requoted by the early review, this one missed)*. The
cascade lattice **is** the discrete log-geometry of ζ's factor at the real place — this
sentence is a theorem, not an analogy.

**T1b (Explicit-formula bridge — PROVED; Addendum 64; `cascade_explicit_formula_bridge.py`).**
For every d ≥ 1, with s = d+1, z = d+½: p(d) = Σ_{γ>0} 2z/(z²+γ²) − 1/s − 1/(s−1) +
Σ Λ(n)n^(−s) — the cascade potential is exactly (Riemann zeros) − (poles) + (primes), the
Hadamard partial-fraction form of the explicit-formula identity on the tower; every window
inherits the split. Verified three-tier (rearrangement 2×10⁻³¹ — round-18 m1; Euler side within strict tail bounds at dps 50 —
round-15 M2; Hadamard side with 50 computed zeros, residuals decreasing). Round-15 M1: the
RH-free theorem is the *paired* Hadamard form; the Lorentzian display is its on-line
evaluation. Classical content Euler + Hadamard; program-new content: the tower evaluation
only. Grounds the *scaffold*
one level deeper (the tower sits on one side of the explicit formula); grounds the
*dictionary* not at all; claims no direction of explanation.

**T1c (The two doors — PROVED at their stated strengths; Addendum 65;
`cascade_zero_side_features.py`, `cascade_colour_field_bridge.py`).** (i) Every
distinguished feature is a level-crossing of p, hence by T1b an exact ZEROS + PRIMES =
POLES + level balance point; solving from the zero side (50 computed zeros + density tail)
recovers the critical point to 6×10⁻³ and the threshold to 5×10⁻² with decreasing error
(sink tail-model-limited ~1%, reported as such). Honest negative registered: no recorded
quantity reads the zero side independently of the digamma packaging. (ii) Legendre gives
p_ℂ = p_triv + p_sgn *exactly* — T5's doubled tower synthesizes the complex-place factor,
relocating F6's r₂ = 0 obstruction; the odd bridge p_sgn = zeros(L(χ)) − ½ln q + χ-weighted primes (no pole; a conductor
instead) holds for **every** odd real primitive χ — the balance point is
character-independent (round-15 M3) — with χ₋₃ the minimal-conductor primitive odd
character (theorem) = the T8 colour field's character, and pairing-by-minimality a
**convention** charged to the selection-convention class *(net-state, round-57
adjudication: re-motivated by T1j — minimality entailed given the pairing-act,
which persists)*; verified with 24
sign-scan-computed zeros of L(χ₋₃); the odd feature 6.2569 = the conductor balance point.
No direction of explanation is claimed (the identity is ζ's/L's own bookkeeping — m6). F6
stays reopened on its original claim; no address derived.

**T1d (The finite places — PROVED at stated strengths; Addendum 69;
`cascade_finite_places.py`).** (i) Global potential identity (exact): Σ_v p_v = ξ′/ξ −
poles with p_v = (log E_v)′ per place; T1b's "+primes" = −Σ_p p_p — the tower is one member
of an adelic family, and p = 2, 3 jointly carry ~94–100% of the finite total across the
record's layers (94.2% at s = 4, 99.0% at s = 6, ~100% by s = 13 — round-18 M2 scoped the
earlier s=6-only "~99%") (noted, not claimed as derivation). (ii) The order-8 clock
element is dyadic-exclusive among finite-place Gauss phases (Gauss's theorem verified at
primes to q = 499 and composites to q = 495; ζ₈ at 4-divisible moduli including non-powers-of-2 to
q = 180 — round-18 M1 extended the primes-only/powers-only lists) — exact theorem + one
graded identification. (iii) Landsberg–Schaar verified (18-pair grid incl. even p —
round-18 m6; the review's independent 1000-pair sweep: zero failures): the
archimedean Weil index ζ₈ is the exchange constant between finite places — the product
formula's machine-checkable avatar. Scope: no grammar entry derived; 2/3-adic Tate theory
named, not opened *(net-state: unramified half opened by T1e, ramified half by
T1i)*; sign-convention failure on the first run kept on the record.

**T1e (The local Tate step — PROVED at stated strengths; Addendum 70;
`cascade_local_tate.py`).** (i) Per-place T2: 1_{ℤ_p} is self-dual and achieves E_p; the
Gaussian is the archimedean component of the standard adelic self-dual vector. (ii) The
clock's modulus = the dyadic squareness modulus (u square in ℤ₂ iff u ≡ 1 mod 8; classes
2/8/4 at ∞/2/odd p) — graded identification, *two* independent corroborations (the
compensation of (iii) is the same theorem as T1d(ii) — round-18 m2). (iii) The
compensation is dyadic-exclusive (conjugate dyadic sum = √(2q)ζ₈^(−1) exactly; odd places
silent). (iv) Colour geography: 3 ramified (conductor = different silences its own
factor), 2 inert; the odd tower's global identity verified with the conductor in the pole
slot; "2 carries the clock" is itself a graded identification, not exact (round-18 m4).
(v) Checked negative: BW(ℚ₂) ≇ ℤ/8 (Br(ℚ₂) = ℚ/ℤ) — *one* route to deriving the
Radon–Hurwitz entry is closed; the Witt-ring route is open and named (W(ℚ₂) of order 32
≅ ℤ/8⊕ℤ/2⊕ℤ/2, level(ℚ₂) = 4 verified in-code, ⟨1⟩ of order 8 — round-18 m3); the
derivation stays open. No grammar entry derived. *(Net-state: T1f has since worked the
Witt route at its achievable scope — mod-8 connection made, count still archimedean.)*

**T1f (The Witt step — PROVED at stated strengths; Addendum 75;
`cascade_witt_weil.py`).** (i) The dyadic Weil index descends to a surjective
homomorphism **γ₂ : W(ℚ₂) ↠ μ₈** (well-defined on the 8 square classes, k-stable,
hyperbolic-trivial at 10⁻¹⁶, values exactly in μ₈) with ⟨1⟩ ↦ ζ₈⁻¹ of exact order 8
(= its additive order, 2·level); kernel order 4 (|W(ℚ₂)| = 32, Lam, cited). **The clock
group is a canonical quotient of the dyadic Witt group.** Forcers: Weil index theory +
level(ℚ₂) = 4 (classical). (ii) Mirror: γ_∞ = ζ₈^sig is the same quotient of W(ℝ) = ℤ
(Fresnel-verified 3×10⁻⁸); Weil's product formula locks the two projections inverse
**per square class** (Π_v γ_v(u) = 1 to ≤ 2.3×10⁻¹⁵ for fifteen representatives — ten square classes — incl.
even-valuation and unramified odd places with in-code silence gates — round-22 F1/F3
extended the ten-class odd-valuation-only list and corrected the residual range;
T1e's compensation = the u = 1 row). ψ-covariance graded (round-22 F2 strengthened):
all eight class values primitive (gated), so surjection-with-⟨1⟩-generator is
character-free; the kernel moves in its scaling orbit — "canonical" = the ψ-independent
structure only. The ℤ/8 = Wall/ABS's BW(ℝ) = the Clifford/Bott (hence
Radon–Hurwitz) period (cited). (iii) Honest negative registered: **N_c = 3 NOT
derived** — ρ is a function of v₂ alone (verified) but the count is Adams (archimedean)
and the layer is papers-side; the open item narrows to those two. *(Door 3 refinement,
A83: at every load-bearing dimension the count needs only the Clifford construction +
Poincaré–Hopf + pre-Adams v₂ ≤ 2 upper bounds; K-theory load-bears nowhere in the
window — `cascade_adams_loadbearing.py`, 5 gates PASS. Layer question, A87, corrected by round 30 (A89): the
selection of d = 12 introduces no new *unlisted* dependency — ONE selector (the
Clifford ℤ/8 window structure; {ρ−1 = 3} = {d ≡ 4 mod 8}, gated), the anchor excluding
its own ρ-twin d = 4 (ρ(4)−1 = 3, disclosed), scan-range ends at the listed layers
d_V = 5 and d₁ = 19; the "over-determined by independent selectors" claim is retracted;
the N_c dependency map is complete in this corrected form —
`cascade_layer_selection.py`, 4 gates PASS.)* Run record: first-run
Fresnel failure (grid + tail sign) and a tautologous surjectivity check both fixed and
recorded. Round-18 m3's route worked at achievable scope. No data, no closures, no
RH/GRH, no semiclassics.

**T1g (The local family completed — PROVED at stated strengths; Addendum 79;
`cascade_local_family.py`).** (i) Odd places: units silent, image μ₂ (p ≡ 1 mod 4) or
μ₄ (p ≡ 3 mod 4), verified p = 3–13; **exclusivity theorem: the order-8 clock image and
the nontrivial unit form occur exactly at v = 2 and v = ∞** — family-level, upgrading
T1d(ii)'s Gauss-phase exclusivity. Forcer chain (round-25 F1): image = homomorphic image
of W(ℚ_p), exp W(ℚ_p) = 2·level ≤ 4 for odd p — an every-odd-p theorem, samples verify
the inputs not the quantifier; unified criterion (c1): the clock places are exactly
those where γ_v(⟨1⟩) is primitive.
(ii) Cocycle γ(a)γ(b) = γ(1)γ(ab)(a,b)_v verified exhaustively (64 pairs at 2, 16 at
p = 3, 5) ⇒ closed form **γ_v(q) = γ_v(1)^dim·β_v(disc)·hasse_v(q)** (verified 72
exhaustive + battery): dim mod 8 at v = 2, sig mod 8 at ∞, **no dimension term at odd
p** — the clock places are exactly the dimension-sensitive places. (iii) Kernel
anatomy: Witt census re-derived (1+8+14+8+1 = 32); **ker γ₂ = (ℤ/2)² = the three dim-2
anisotropic classes (disc, Hasse) = (3,+1), (6,−1), (14,+1), each order 2, plus 0** —
the clock-invisible classes; their grammar meaning OPEN, none claimed *(narrowed
round 44, gates L7a–d; round-45: ord(⟨1⟩) = 8 named in the chain and gated, span
notation ℤ⟨1⟩ replacing the Pfister-colliding ⟨⟨1⟩⟩: the quotient made exhaustive —
W(ℚ₂) = ℤ⟨1⟩ ⊕ ker γ₂ direct,
full 32-class character table — and the invisible (ℤ/2)² shown transverse to the
fundamental-ideal filtration (γ(⟨⟨−1,−1⟩⟩) = −1 on the I² generator; Pfister
bracket in the paper's ⟨1,−a⟩-factor convention — round-46 F2) and
signed-disc-faithful (d± injects the kernel into I/I²): disc-level data, question
open)*. (iv) Global
re-lock on six multi-dim forms ≤ 4×10⁻¹⁵ incl. the dim-8 definite form (both clock
places wrap to 1). Run record: p = 17 timeout → primes trimmed, two pre-run code
artifacts removed. 35 PASS 0 FAIL *(the forced-Hasse Remark's three L8f gates
added to Theorem 1h's five L8; the lineage: 21 at first commit, 23 after
round-26's L6, 27 after round-44's L7, 32 at Theorem 1h, 35 now)*. No grammar entry
derived; no data, no closures.

**T1h (the kernel's identity — the ζ₄-norm structure; L8, five gates).**
d±(ker γ₂) = N(ℚ₂(i)^×)/sq = ⟨−3, 2⟩: in-kernel ⟺ signed disc a nontrivial norm
class of ℚ₂(i) (= ℚ₂(ζ₄); γ² read as an abstract primitive 4th root — round-47
F2), Hasse forced (one per norm class, zero per non-norm, all
14 gated); generators = the colour discriminant (unramified — ℚ₂(√−3) = ℚ₂(ζ₃);
(2,−3)₂ = −1 is 1e(iv)'s inert fact, relocated) and the clock prime; the ∞-mirror
kernel is free (8ℤ — invisible torsion dyadic-exclusive). Identity settled; whether
the grammar reads the two coordinates stays open; sharpened falsifier (round-47 F1
rescoped): any derivation routing colour through the clock-invisible part of
W(ℚ₂) must land in this subgroup, Hasse forced. No entry
derived; category (a). The forced-Hasse function (L8f, three gates):
h_β(d) = ζ₈²/β(−d) = (d,−1)₂/β(d); its reality locus is exactly H (the four
non-norm discs are forced to ±i — excluded by impossibility, not enumeration);
ker γ₂ is its graph over H; h_β(1) = +1 = the Hilbert axiom (a,−a)₂ = 1 — the
round-48 edge case's two mechanisms are one formula.

**T1i (the ramified Tate step — pure phase + the root-number identity;
`cascade_tate_epsilon.py`, seven gates).** Ramified characters have L-factor 1 —
the ramified towers are pure phase, all content in ε (shell-vanishing gated);
**β(a) = ε(η_a) on all eight classes** (orientation fixed by gating the ε product
formula on four known global root numbers, incl. 1c's χ₋₃), so
γ₂(q) = γ₂(1)^dim·ε(η_disc)·hasse — the clock's twist is the quadratic
root-number map; the colour character's global +1 decomposes as
ε₃(χ₋₃)·ε_∞(sgn) = (+i)(−i) (two-place cancellation), and the odd bridge's
−½ln 3 is minus the ε-conductor factor's log-derivative (round-54 F2 restored
the sign; the genuine gate is local_tate's T-loc4). No entry derived;
category (a).

**T1j (the torsion-exceptional selection; `cascade_torsion_selection.py`, six
gates; round-57 adjudication MODIFY applied).** |μ| = 6 uniquely at disc −3 and
|μ| = 4 uniquely at disc −4 (census, |d| ≤ 10⁴); the 1h kernel's class-level
anatomy read back through the census — invisibility = the μ₄ disc character
((·,−4)₂ = (·,−1)₂, ker = H), invisible unit direction = the μ₆ disc class
(H ∩ units = {1, cls(−3)}, unramified ℚ₂(ζ₃)); given the pairing-act (not
entailed by T11), the μ₆ requirement determines χ₋₃ with minimality entailed;
ε-support {3, ∞} (T1i). Adjudicated: the member is re-motivated, not reduced —
three members and the seven-item count stand. No closure; category (a).
*(Net-state, T1r as corrected round 81: χ₋₄ fails three distinct committed
anchors — W₁ strictly weaker extensionally than the colour gloss (the act's
standing form: pair with the colour field's character; defined at T1r); the
carrying-conductor and census routes equivalent to the gloss's output, weaker
only in what they name; the act persists.)*

**T1k (the lattice selection; `cascade_lattice_selection.py`, seven gates;
round-60 F1 correction applied).** Under the site-E canonical pairing
p(d) = P(d+1), the threshold bands are exact integer intervals B₁ = {7..19} and
B₂ = {20..217}, boundary-convention-free (no lattice point within 8.5×10⁻⁴ of a
threshold, so all four interval conventions agree), and V(d) has strict discrete
argmax 5 — hence, **with the crossing sides fixed by part0's variational-sup
labeling** (round-60 F1: the inf labeling (6, 20, 218) is equally lattice-exact
under the same pairing — the sup is a second given, data-corroborated, its
derivation open by part0's own grading; gated K7), {argmax V, min B₁, max B₁,
max B₂} = {5, 7, 19, 217} with **zero rounding anywhere**; the s-space critical
pair is one equation (ψ(x/2) = ln π) read at two argument offsets; part0's
variational labels agree gate-by-gate given the sup (the sup pick reduces to the
band-sign facts at the two upper boundaries via d log Ω/dd = −p(d), part0's own
identity; numerically at the first, Ω₇ < Ω₆, ≈1.9%). Given the pairing plus the
sup labeling — both persisting as the member's content (the alternative pairing
shifts the three band labels to 8, 20, 218 — the argmax member 5 unchanged:
{5, 8, 20, 218}) — the assignment is entailed:
the class's first member is re-motivated, not deleted, exactly as T1j
re-motivated the third. Three members and the seven-item count stand. No
closure; category (a).

**T1l (the pairing dictionary; `cascade_pairing_dictionary.py`, five gates).**
Member two attacked directly: given the tower's dictionary (the standalone
paper's Definition 2.1 — s = d+1 with factor Γ_ℝ(s) — whose kernel theorem is
this document's T1, primitives at that point), the audit's
"alternative pairing" objects are the *previous layer's* potential and measure
(P(d) = p(d−1); 2/Γ_ℝ(d) = Ω(d−1) — identities). Site E's flip is identically a
window shift (Σ residual exactly 0) and the audit's alternative a mixed frame
(potential flipped, boundary term kept: 10.4584 vs the coherent 10.4718, both
catastrophically off the canonical 16.8173) — the −38% anchor re-grades from
selection to **cross-check of the dictionary**, with E's residual content the
window endpoint data (Definition-6.1 instantiation + the strict-boundary
stipulation, already listed). Site C sharpens: the avatar weight is Ω(d−1),
forsworn by the standalone paper's Theorem-1 Remark ("The paper never uses the
avatar"), so the
Geometric two-coset clause fails under the tower's measure (0.35001 ≥ 1/π;
single-coset repair candidate stays live; no number changes). B/H re-gated
flip-invariant; D closed by T1k (given the site-E pairing plus the
variational-sup labeling). The review-4 per-site family is closed;
member two re-motivated, not deleted — its live content is the dictionary plus
already-listed endpoint items. Three members and the seven-item count stand. No
closure; category (a).

**T1m (the availability factors' arithmetic homes; `cascade_availability_factors.py`,
five gates).** Mass layer 3 attacked at the factor level: none of the three U2
availability factors is a new constant. The obstruction unit 2√π = χ·Γ(½) is one
object on two committed sides — T2's graded-crossing normalisation and part4b's
per-Dirac-layer topological toll (with the d-independent propagator ratio
1/(2√π)); the projection factor cos(π/6) = √3/2 = covol(ℤ[ω]) is Door 4's
object, and (new) minimal over all 3043 fundamental imaginary-quadratic discs at
d = −3 (the T1j census reused; classical closure |d| ≥ 3); the colour factor's
rank 2 stays a coincident-2s identification (13c) with the T1j-census degree
anchor, e^{2/2} = e the papers' Tier-4a record. Fork consequence: R1's rank
counts Dirac layers in the half-open leg interval (gated on every coset pair;
periods-minus-1 an extensional duplicate); at probe P1's cell (legs 5 & 21) the
count is 2 vs the indicator's 1, and given the obstruction identification the
per-layer attachment forces the count — the 13b availability block's one genuine
fork discriminated arithmetically, the block canonical up to extensional
equivalence, conditional on the identification. The clause triggers (legs,
record-legs classifier, A13 grading, ℓ_A kind, Observer k=3) stay soft inputs,
untouched; the angle rows stay near-tautological. No number changes; no closure;
category (a).

**T1n (the sup's exact equivalents; `cascade_sup_selection.py`, five gates).**
Part0's open max-over-min question (T1k's second given) narrowed by three gated
reformulations: the sup labels (7, 19, 217) are exactly the **odd members** of
the three straddling pairs (the inf the even members; odd-selection is total
and uniform); in the tower's dictionary the sup labels' spheres are Euler-null
(χ(S^d) = 0; the inf's carry χ = 2 — the obstruction toll's chirality factor,
T1m) and all four distinguished layers {5, 7, 19, 217} are odd; and
S_dS = 24π²M⁴/ρ_Λ is strictly decreasing in the invariant (Part I's closure),
so **sup I = min horizon entropy = min boundary area** (S_sup = 3.315×10¹²²
nats; the inf's budget 10.76× larger) — the exact connection part0's open
clause requested, with the direction stated. The characterizations are
distinct principles (synthetic-crossing exhibit gated) agreeing at the actual
crossings (three parity facts + Ω₇ < Ω₆, each gated); farther-integer and
window-proximal re-descriptions also verified. Nothing forces the sup: the
forcing stays open, part0's remark registered with the equivalences and
keeping "remains open"; the 1k given persists, re-motivated. No number
changes; no closure; category (a).

**T1o (the arithmetic-primary form; `cascade_zeta_rational.py`, five gates).**
1n's parity dichotomy re-expressed on ζ itself: the sup labels' twist points
s = 8, 20, 218 (and all four distinguished layers' twists {6, 8, 20, 218}) are
even — ζ's Euler-rational points (ζ(6) = π⁶/945, ζ(8) = π⁸/9450; rationality
gated exactly via Bernoulli numbers) — whose functional-equation mirrors are
nonzero rationals (ζ(−7) = 1/240, ζ(−19) = 174611/6600, ζ(−217) ≠ 0); the inf
twists 7, 21, 219 mirror exactly onto the trivial zeros (ζ(−6) = ζ(−20) =
ζ(−218) = 0), and the sup is the unique labeling among the eight avoiding the
trivial-zero mirror set. Cross-link: ζ(6) = π⁶/945 is the frozen ledger's
m_τ fork constant — ζ at the volume-max layer's twist point vs the compliance
at the U(1) layer *(round-75 F1: the identification is the fork's founding
fact — `cascade_adelic_compensator.py`, the "adelic survivor" discrimination — not novel
here; new is only the tie to the sup's Euler-rational twist set; no closure;
Belle II adjudicates as before)*. The dichotomy now lives on ζ's
special-value structure, the χ reading its avatar-side shadow (round-75 F2
struck the canonical-register-per-T1's-Remark claim (label, not verbatim; round-76 F2) — the Remark deprecates
the avatar in derivations, it does not rank registers); still an equivalence,
the forcing open, 1k's second given persisting. No number changes; no
closure; category (a).

**T1p (the regularity forcing, conditional on one principle;
`cascade_gamma_regularity.py`, five gates).** 1o's trivial-zero avoidance in
local form: Tate's archimedean γ-factor γ_∞(s) = Γ_ℝ(1−s)/Γ_ℝ(s) has poles
exactly at the odd twists (finite nonzero closed forms at the even: γ(2) =
−2π², γ(8) = 8π⁸/315, gated exactly); equivalently the functional-equation
mirror weight 2/Γ_ℝ(−d) is zero iff d even (d = 7's live 105/(8π⁴) gated).
The inf labels sit at γ-poles/measure-zero mirrors, the sup at regular
points/live mirrors. GIVEN one principle — **labels at regular points of the
tower's local functional equation** (the same non-degeneracy type as T2's
gcd condition and Theorem 7's order-one requirement) — each pair has exactly
one qualifying member and the labeling is **forced to (7, 19, 217)**, the
variational characterization's output and all four 1n/1o equivalents following
as corollaries (five selectors coincide, gated; round-78 c1). Precision bonus: at s = 1
(d = 0) the local form is uniform where the global trivial-zero form has its
exceptional point (ζ(0) = −½, ζ's pole opposite). The principle is a **new
given, not derived** — the open question narrows to deriving it from the
axioms; 1k's second given at its sharpest form. No number changes; no
closure; category (a). *(Net-state, T1q ~~: the per-label principle is derived
given mirror coherence — one global requirement~~ **[struck round 79 (F3,
MAJOR): the two are extensionally equivalent]**, as corrected: an equivalent
reformulation with independent motivation; the given's extension unchanged.)*

**T1q (mirror coherence: an equivalent reformulation of the regularity
principle; `cascade_mirror_coherence.py`, five gates; as corrected round
79).** ~~1p's given moved up one level, single and global. T1b's paired
Hadamard form is "even, entire of order 1, genus-0 in z²" — a function of
z² = (s − ½)², blind to the difference between layer d (z = d + ½) and its
mirror −(d+1)~~ **[struck round 79 (F1/F3, MAJOR): T1b predicates those
adjectives of ξ(½+z), not of the paired sum, which is odd in z; and the two
conditions are extensionally equivalent, so neither is "up one level"]** The
ground object ξ assigns the same value to layer d and its mirror −(d+1) —
ξ(½+z) even, same z²; gated d = 0..30 plus exact instances ξ(8) = ξ(−7) =
4π⁴/225, ξ(20) = ξ(−19). Branch-swap every weight (Ω̃(d) = 2/Γ_ℝ(−d) =
Ω(d)/γ_∞(d+1), the 1p tie gated); the corrected census (round-79 F2, each
class gated): Ĩ finite-nonzero **uniquely at the sup**; 0 at the three l₀ = 7
labelings with an even content label; ∞ at (6, 19, 217) *only*;
**indeterminate** (0·∞, no exact value) at the other three l₀ = 6 labelings —
adjudication stated (coherence = the formula *evaluates* to a finite nonzero
value), and the convention-dependence disclosed and gated (under d → d+ε the
(6, 20, 218) *limit* is finite-nonzero ≈ −1.413×10¹²³; uniqueness holds for
exact values, not regularized limits). Requiring the invariant's standing
non-degeneracy for the branch-swapped weights — **mirror coherence** —
entails coherent = all-odd = 1p-regular = {(7, 19, 217)}; but Γ_ℝ never
vanishes (gated), so this is an **exact biconditional with 1p's per-label
regularity**: an equivalent reformulation whose contribution is motivational,
~~the regularity principle is derived, 2³ per-label applications replaced by
one requirement […] 1n's all-four-odd upgrades to necessity […] the open
question narrows~~ **[struck round 79 (F3/F4, MAJOR): "derived" holds in both
directions; the 2³-vs-6 count was inconsistent; "necessity" under an
extensionally identical postulate is vacuous; the open question is unchanged
in extension]**. The d_V clause deflated (F7): Ω̃(5) = −15/(4π³) ≠ 0 with
Ω̃(4) = Ω̃(6) = 0, but Ω̃ vanishes at *every* even d — the content is exactly
"d_V is odd," 1n's parity fact on the mirror weights. Sign disclosed:
Ĩ_sup < 0 (exact rational over π¹¹⁷, rationality gated per F6, ≈
−1.109×10¹²²); coherence is non-degeneracy, not positivity. Mirror coherence
is **the same given in a second face** — motivated (the ground object's
defining symmetry; what "invariant" means) but **not an axiom-consequence** —
and the open question is unchanged: derive the given, either face, from
A1–A4. No number changes; no closure; category (a).

**T1r (the pairing-act's anatomy; `cascade_pairing_act.py`, five gates).** The
act decomposed, the live alternative excluded thrice on committed anchors.
The partner family (every odd real primitive χ) is classically the Kronecker
characters of negative fundamental discs — the census's own space (parity
gated on all 3043; the symbol routine cross-checked in-code against a library
Jacobi on 500 seeded cases ~~cross-checked against a library Jacobi~~
**[reworded round 81 (F1, MAJOR): a session run until landed; now a committed
P1 conjunct]**). Act-form W₁ (1j's committed "dyadic shadow = the invisible unit
direction", promoted; no field, no μ₆, no T11 named): the slice is cls(−3)'s
class, 1014 of 3043 (iff χ_d(2) = −1, 1e(iv)'s inert clock prime; −11 in the
slice, no field pinned — round-57 F2 kept), and **χ₋₄ is excluded by 1h's
kernel alone** (cls(−4) = 7 ∉ H). Act-form W₂ (conductor among 1d's carrying
primes {2, 3}): q = 2 has no primitive character, q = 3 exactly one, odd —
**W₂ pins χ₋₃ outright** ({d : |d| ∈ {2,3}} = {−3}, gated); χ₋₄ excluded
again. And the committed 1c constant L(1, χ₋₃) = π/(3√3) **is Dirichlet's
2πh/(w√|d|) at (1, 6, 3)** — h(−3) = 1 by reduced-form count, w = 6 the
census's unit count, numerics re-gated (μ₄ cross-check π/4, Leibniz): the μ₆
datum sits on both sides of the pairing. Role asymmetry re-gated:
ker(·,−1)₂ = H — the candidate partner's character is the committed filter's
*instrument*, cls(−3) the invisible *datum*. **The act persists** — no
act-form is entailed, pairing-at-all (the odd feature's missing address) is
untouched, no universal over act-forms claimed; the round-57 "only the order
or the pairing-act excludes" is superseded by the triple exclusion — the three
anchors distinct, not "independent," and only W₁ strictly weaker extensionally
than the colour gloss (the act's standing form: pair with the colour field's
character), the other two equivalent in output and weaker only in what they
name (round-81 F2/F3). Three
members and the seven-item count stand. No closure; category (a).

**T1s (pairing-at-all located; `cascade_bridge_asymmetry.py`, five gates).**
The act's open core after T1r, located. (i) The odd feature is the unique
root of ψ(x/2) = ln π (trigamma > 0 gated; offsets x*−2 = 5.2569 the
V-argmax, x*−1 = 6.2569 the p-zero — both gated at 4 d.p.; p_sgn(x*−1) = 0
gated): the paired object is the central continuum root in the sgn frame —
an identity, not an act. (ii) The even tower's bridge family (every even
real primitive χ — same Hadamard derivation as the odd bridge, classical)
has exactly one pole-carrier, ζ (harmonic sum grows as ln N, gated; sample
even and odd character sums Cauchy-converge, gated; Dirichlet cited): T1b's
ζ reading is **pinned by the pole, not chosen**. (iii) The pin is
**parity-blocked** — the unique pole-carrier is even (definitional); the
even selection is overdetermined (pole = conductor-1 = minimal, q = 1
even), the odd side has no pole, no q ≤ 2 member (re-gated), minimum 3:
any odd arithmetic reading requires an **extrinsic** principle — the act
is located there. (iv) T1b's display carries the pole terms −1/s − 1/(s−1)
(anchored; 0.2976 at the central root, more than half ln Γ(½), gated) — no
pole-free partner supplies it; a latent "uncharged even pairing" charge is
preempted. (v) **The act persists**: the grammar does not read the odd
feature (Finding 6's exclusion anchored); nothing obligates the odd
reading. Pairing-at-all = [object: identity] + [reading: extrinsic if
taken] + [partner: T1r]. Open core: derive an extrinsic odd principle from
A1–A4, or establish the grammar never needs the odd reading. No closure;
category (a).

**T2 (Solvability — PROVED at the papers' Tier-2 grade).** The A1 action is Gaussian, hence
second-quantizable in closed form; its measure normalisations are √(2πα) per mode (Tate's
period), Γ(½) per Gaussian unit, 1 per Berezin unit, 1/(χΓ(½)) per graded crossing; and the
marginal Green identity G(d)−G(d+1) = α(d) holds exactly (verified 10⁻¹⁵). All physical
content of the free theory lives in these normalisations. (Addendum 25.)

**T3 (Dictionary — PROVED as a completeness statement).** Every constant used anywhere in the
mass arc (Addenda 12–29) is the image of an A2 local constant; the one-rule recomputation of
the full spectrum uses no per-case number (Addendum 24). The grammar is closed over A2.

**T4 (Address-book determination; Addendum 40, restated per external reviews).** *Given the arena,
the dictionary, the derived rules (T5–T9, exclusion, flags, channel count), the instantiation
data (address book, record statuses), and D1, the observable map is unique.* Proof: U1
exactly-once (at-most-once = T5; at-least-once = completeness of the Gaussian measure, T2/T9);
U2 availability (rounds 8–13 corrected state, Addenda 53–62: **member fields** computed by one
shared rule-set on all 11 rows against the *corrected* key — the previously stored θ_23
channel count was wrong (papers: k=4) — and the rounds-8–12 **θ_C availability defect is
resolved by the A61 record-legs correction, round-13 restated (WOUNDED)** — angles read
gauge-layer states (verbatim for θ_C, template-inference for θ_23); the generation pairing
was an about-label mislabeled as legs; avail block 6 survivors = canonical + 2 duplicates +
the cross-generation-indicator fork (P1); colour rank pinned by m_b/m_τ, projection pinning
conditional on the audit-lemma corpus (M4); the classifier is a new per-row soft input;
sharpened PMNS falsifier with the repo's N_c-bearing candidates disclosed); member-field
uniqueness relative
to the declared 44-variant space with σ-classified kills — P/L/sign/channel-count slots
pinned at up to 187σ/66σ/4σ/67σ, G-flag reading 3 survivors, precedence all 6 (round 9:
vacuous on the papers' uniform expression-tree reading too — anchoring only under the four
variant readings, 13–109σ conditional; round 10: survivor freedom enumerated
by probes P1–P7 after P7 closed the P∧G gap), Family-B
2 — with the source map {19,5,14,7} held fixed as a disclosed withheld axis;
first-principles groundings at argument/identification strength only, the half-open-support
"theorem" and the T9/T6 attributions retracted); U3 member determinism (flags + T7 +
channel count + T5). Exhaustion:
every stage's naive space (1,764–7,056 assignments) filters to exactly one survivor, each
reproducing the recorded formula to ≤0.01%; the neutrino E-stage collapses to
(N_c·π², (0,1,2)). The exhaustion verifies single-valuedness against the ~60-entry table, not forcedness. The unconditional question — why *this* address book — is C1 itself, not mathematics.

**T9 (Quenched-record theorem — PROVED; Addendum 39).** For the forced Gaussian, the three
candidate meanings of "recorded value" (r.m.s. point, mean-action point, AEP-typical point)
coincide exactly (−ln f(x) − h = S(x) − ½ identically); a record's weight is the quenched
(geometric-mean) average — the almost-sure multiplicative rate of compounding records
(Kolmogorov LLN, concentration 1/√(2n)) — giving e^(±r/2) exactly at every rank r via
⟨S_r⟩ = r/2 (T5-P4). S4's entire content reduces to two identities + one LLN theorem + the
definitional clause **D1**: a measurement is a repeatable record whose weight compounds
multiplicatively over independent realizations.

**T8 (S5 as trace duality — PROVED; Addendum 36).** The su(3) roots are the units μ₆ of ℤ[ω]
(point-by-point); the measurement frame is the trace-dual lattice — the inverse different
𝔡⁻¹ = (1/√−3)ℤ[ω], which is the ring rotated exactly 30° modulo unit rotations; the su(3)
fundamental weight w₁ = e^(iπ/6)/√3 is a minimal vector of 𝔡⁻¹ (10⁻¹⁶); every minimal pairing
projects at cos(π/6), a factor unique among imaginary quadratic rings to disc = −3. Colour
multiplicity 3 and per-leg occupancy remain instantiation.

**T7 (Arithmetic sign rule — PROVED; Addendum 35).** The sign of a correction is the side of
the Cauchy–Schwarz equality manifold on which the observable's leading formula sits:
off-manifold interpolation reads gain (+) — the Gram deficit is strict midpoint log-convexity
of Γ_ℝ, i.e. Bohr–Mollerup, verified strict for all d = 1–215; at-manifold saturated overlaps
lose (−); proper coset restrictions of the peaked weight 2/Γ_ℝ under the ℤ/8 Weil grading lose
(−) — all 28 two-coset shares < 1/π under the avatar-weight pairing; **convention-conditional
per review 4: the Definition-2.1 pairing gives max 0.35001 ≥ 1/π** — the Geometric clause is
demoted *(net-state, T1l: the demotion sharpens — the avatar weight is Ω(d−1), the previous
layer's measure, and the clause does not hold in the tower's dictionary; the single-coset
repair candidate stays live)*. The other two clauses stand. Population-class assignment remains instantiation.

**T6 (Per-period shape theorem — PROVED conditional on marking + activation; Addendum 34).**
The twist tower carries a canonical ℤ/8 grading: the Weil index of the real quadratic
character, γ = ∫e^(iπx²)dx = ζ₈, has order 8 (arithmetic Bott, no topology). Given a marked
coset (instantiation) and source-activation of its subcritical members, the subcritical marked
set is finite and forced — {5, 13} for C = {d ≡ 5 mod 8} — and the member exponent of a
descent functional is the count of subcritical marked twists in its window: (0, 1, 2) at
(21, 13, 5), first power each. The exponent pattern of the neutrino closure is forced
counting; only the member's *value* remains unfixed.

**T5 (Arithmetic increment rule — PROVED from Tate's thesis alone; Addendum 33).** With no
cascade or physics input: the sgn character doubles the twist tower at unit shift (χ = 2 =
|μ(ℝ)|); the Gaussian achieves the L-factor (gcd fixes the rescaled family; self-duality is
a normalization convention — restated per reviews 3–4); (log Γ_ℝ)′ = E[log|x|] and (log Γ_ℝ)″ = Var[log|x|] > 0 under the twisted Gaussian
measure, so every feature of ξ's archimedean summands is order one (simplicity = variance
positivity); E[πx²] = s/2 exactly (the ½-atom = the mean action; S4's anchor); ℤ's total order gives
attach-once (the one-summand partition clause was demoted by review 4, D2). Hence: at most one member, first power, per interval
functional — a theorem of probability at the real place. What arithmetic does not supply:
P > L > G precedence, the physical occupancy assignment, the (m,k) counts — instantiation data
belonging to C1.

## 3. The conjectures (never theorems)

**C1 (The physical conjecture).** The observed universe realizes A1–A4: the Standard-Model
mass spectrum is the epsilon-factor system of the completed Riemann zeta function at the real
place, with multiplicities from the 2-adic place and phases from the cyclotomic tower. *No
formulation can make this a theorem.* It is decided only by the frozen ledger (Addendum 26 +
29D): Σm_ν = 60.9 meV, JUNO ordering, Belle II m_τ, DESI w(z), HL-LHC m_H, lattice ratios,
the forced negatives.

**C2 (The arithmetic dynamics conjecture).** The finite places enter as the prime clock
(Addenda 5–6): census convergence at rate 1/√x ⟺ GRH. The framework's dynamical side is
equivalent to the Generalized Riemann Hypothesis in the only sense available to physics:
indistinguishability of the event stream from the GRH-governed one.

## 4. Gap ledger: what stands between here and bulletproof

| # | Gap | Type | Closes when |
|---|---|---|---|
| 1 | Increment rule (A3) | **derived from arithmetic first principles** (T5, Addendum 33; supersedes the Tier-2 A32 version) | closed as mathematics; only its physical instantiation (occupancy, m/k counts) remains with C1 |
| 2 | Per-period attachment (A3) | **shape derived** (T6, A34); mechanism at Tier-2 (A38/A43, amended per external review): flip-count 4 derived (minimal torsion word), ×3 incoherence derived (factorization); **the unit normalization carrying Γ(½) is a convention, empirically anchored not arithmetically forced** (self-dual form gives E = 3, excluded by data) ⟹ E = 3π², unique colour-free form *conditional on availability assignments* | remaining: the marked-coset choice, the unit convention; JUNO tests the value (~0.6% window), cannot convict the form over its 0.1% twins |
| 3 | S4 lemma: measurement-at-typical-value | **derived** (T9, Addendum 39): typicality unambiguous (three notions coincide exactly), factor = quenched rate forced by LLN, all ranks exact | residue: definitional clause D1 (records compound multiplicatively) — no tunable content |
| 4 | S5 lemma: root-frame projection | **derived** (T8, Addendum 36): frame = trace-dual lattice (inverse different of ℚ(ζ₃)); value = 30° rotation of ℤ[ω], unique to disc −3 | colour count 3 and per-leg occupancy remain instantiation |
| 5 | Sign rule | two clauses derived (T7: Bohr–Mollerup off/at the equality manifold); **coset clause demoted** (review 4, D1: convention-conditional) | population-class assignment remains instantiation |
| 5b | P > L > G precedence | **vacuous on uniform primary readings at both layers; anchoring conditional** (round 9, M3: A52's m_τ-abs dash-fill expanded closed constituents against the papers' expression-tree predicate — the same convention keeping b/s at G=F — so on the uniform mechanical reading no row is multi-flag anywhere and the order never fires; the 13–109σ exclusions hold only under the four variant readings — m_τ-abs constituent expansion, ℓ_A window, ℓ_A kind (+109σ, round 10), sin²θ_W coupling-running; A52 script corrected). Round 8 standing: all six orders survive the U2 exhaustion; the A55 nesting argument is **reversible** (retracted "T9" anchor) | counted in the residue; on the uniform reading the item is deletable-as-vacuous — papers' adjudication of the grading would settle it |
| 6 | T4 uniqueness | **address-book determination + U2 (rounds 8–14 corrected)** (Addenda 40, 53–63): member fields computed by one shared rule-set (11/11 against the corrected key — the stored θ_23 k was wrong, papers give k=4); the rounds-8–12 θ_C availability defect **resolved by A61's record-legs correction (round-13: WOUNDED, restated)** — angles read gauge-layer states (verbatim θ_C / template-inference θ_23); avail 6 survivors incl. the indicator fork (P1); colour rank pinned, projection pinning corpus-conditional (M4); classifier = new soft input; sharpened PMNS falsifier with standing N_c candidates disclosed; member uniqueness relative to the declared space with σ-classified kills (four slots multi-σ pinned; G-flag 3 survivors; precedence all 6; Family-B 2; source map held fixed = withheld axis); collapse claim ("~60→~30") **withdrawn** (input scalars 76 > output scalars 50); first-principles groundings argument-strength only | open: extension to the full ~100-entry record; absolute forcing unavailable in principle; soft inputs: Observer k=3 (instantiation count — the \|T6-set\| upgrade was retracted, T6 forces {5,13} size 2), A13 grading, ℓ_A kind, and now the record-legs rule (identification, PMNS-falsifiable); all four source twists {19,5,14,7} convention-selected *(net-state, T1k as corrected round 60: the distinguished-layer identifications among these are entailed given the site-E pairing plus the variational-sup labeling; member re-motivated, count unchanged)* |
| 7 | χ = 2 ↔ \|μ(ℝ)\| vs χ(S^even) | bridge unformalized | show the Euler characteristic's role factors through the unit-torsion identity, or keep topology as justification |
| 8 | C1 | empirical forever | the ledger |

Items 1–6 are mathematics: each is checkable without data, and each success converts an axiom
into a theorem, shrinking the axiom system toward A1 + A2 alone. Item 8 is physics and cannot
be moved by proof.

## 5. The honest summary sentence

The framework admits exactly this formulation: **a proved kernel (T1–T3) identifying the
cascade with the log-geometry of ζ's real place and its mass grammar with adelic local
constants; the assignment rules derived as theorems (T5 increment, T6 period shape, T7 sign,
T8 projection, T9 measurement) with the activation mechanism at Tier-2; address-book
determination verified (T4, restated); one definitional clause (D1); a seven-item
non-arithmetic residue (see the standalone paper's abstract); and one physical conjecture
(C1) that no mathematics can settle.** Every number is either a theorem's output, a
convention's output (counted in the residue), or a frozen ledger entry awaiting JUNO, DESI, Belle II, the HL-LHC, and the lattice. The claim
that *our* universe instantiates the skeleton is, and will always remain, the ledger's to
decide.
