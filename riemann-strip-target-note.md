# The strip target: a theoretical attempt, and what it proves

**Working note, not a paper surface.** Written at the owner's commission
("try to prove it theoretically before running any long winded numerics")
after Addendum 537. No numerics were run for this note. The Lean pilot was
not touched. Every statement below is either proved here in full, or is
marked as a proof sketch with the unfinished step named, or is marked as
heuristic. Nothing here is a claim of `riemann-indistinguishability.md`,
which asserts the Riemann Hypothesis neither true nor false.

**The target that was set.** The pilot's chain (README rounds 54–65) derives
Mathlib's `RiemannHypothesis` from one hypothesis: the top-of-chain ground
states of Weil's truncated form converge, after normalisation, to Riemann's
Ξ locally uniformly on the strip |Im z| < ½. The proposal was to prove the
convergence on a smaller strip |Im z| < b₀ and collect a zero-free strip of
width b₀ as the payoff. §1 proves the payoff would be real. §2 proves the
theorem this attempt actually yields, quantitative and under one genericity
assumption on the farthest zero: an off-line zero forces the ground energy
exponentially negative, with the farthest zero from the line setting the
exponent. §3 argues, heuristically
but with the min–max obstruction quantified, that the strip target's
hypothesis is not attackable below full strength by the methods available,
and locates where the difficulty sits. §4 states the reformulated open
problem that the analysis leaves as the honest next target.

---

## 0. Setting and conventions

Throughout, a > 0 is the half-support and δ = 2a the support.

**Probes.** A probe at half-support a is a real even g ∈ L²(ℝ) supported in
[−a, a] with the archimedean integral of the paper's Theorem 1bn(i) finite
(the pilot's `Probe a g`, Roadmap.lean). Its transform is

  ĝ(z) = ∫ g(u) e^{izu} du = 2 ∫₀^a g(u) cos(zu) du,

entire, even, real on ℝ and on iℝ, with ĝ(z̄) = conj ĝ(z) and
|ĝ(z)| ≤ ‖g‖₁ e^{a|Im z|}. Every C_c^∞ even real function supported in
[−a, a] is a probe.

**Zeros.** ρ runs over the nontrivial zeros of ζ with multiplicity, written
ρ = ½ + iγ_ρ, γ_ρ ∈ ℂ, |Im γ_ρ| < ½. The set of γ_ρ is closed under
γ ↦ −γ and γ ↦ γ̄ (the functional equation and conjugation). For a zero off
the line, the four zeros ρ, ρ̄, 1 − ρ, 1 − ρ̄ have γ ∈ {γ, −γ̄, −γ, γ̄},
and for even real g their contributions to Σ ĝ(γ)² sum to 4 Re ĝ(γ)².
Write β_ρ = |Re ρ − ½| = |Im γ_ρ| and

  β* := sup_ρ β_ρ ∈ [0, ½].

RH is the statement β* = 0 (and then the sup is attained).

**The form.** For g ∈ C_c^∞ even, Weil's explicit formula gives

  Q(g) := Σ_ρ ĝ(γ_ρ)²  =  2 poleR(g)² + (ψ(¼) − ln π)‖g‖² + ∫₀^∞ [f(0) − f(u)] e^{u/2}/sinh u du − 2 Σ_n Λ(n) n^{−1/2} f(ln n),

with f = g ⋆ g̃ the autocorrelation and poleR(g) = ĝ(i/2) = ∫ g e^{−u/2}.
The right side is the pilot's `weilQ a g` and the paper's Theorem 1bn(i)
form; the left side is the zero side, summed symmetrically, and for
g ∈ C_c^∞ every zero sum below converges absolutely. Q(g) is real. For
probes in general the pilot defines the form by the right side. The ground
energy is

  λ₁(a) := inf { weilQ(g) : g a probe at half-support a, ‖g‖ = 1 },

attained (the pilot's `exists_groundState`); a ground state is a normalised
minimiser. Since every normalised C_c^∞ even function supported in [−a, a]
is a probe,

  (0.1)  λ₁(a) ≤ Q(g)/‖g‖²  for every nonzero even real g ∈ C^∞ supported in [−a, a]

(the pilot's `lam_mul_le`; its `Probe` clause `a < |u| → g u = 0` admits the closed support).

The form enters §2.1–2.2 only through its defining right side, (0.1) and
the explicit formula for C_c^∞ functions (with Rosser–Schoenfeld, Backlund's
count and the first zero's height as the arithmetic inputs); §2.3's
Corollary 4 also uses Theorem A, whose trial Φ_a has a jump at ±a and
whose zero-side identity therefore rests on the explicit formula in the
wider class of Weil (1952) and Barner (1981): h = Φ_a ⋆ Φ̃_a is Lipschitz,
compactly supported and of bounded variation, since Φ_a is smooth on
[−a, a] with two jumps of size Φ(a), and the zero sum converges absolutely
because |Φ̂_a(γ)| = |E_a(γ)| ≤ e₁(a)/|γ|. This is the class the paper's
Theorem 1bn(i) evaluates the form in (Yoshida's periodic class, with jumps
at ±a).

**Riemann's kernel.** Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) e^{−πn²e^{2u}},
even, positive, with Φ(u) ≤ C_B e^{−B|u|} for every B, and

  (0.2)  ∫ Φ(u) e^{izu} du = Ξ(z)/2  for every z ∈ ℂ,   Ξ(z) = ξ(½ + iz),

the pilot's `RPhiHat_eq` (round 64). Write Φ_a = Φ·1_{[−a,a]} and
E_a(z) = ∫_{|u|>a} Φ(u) e^{izu} du, so Φ̂_a = Ξ/2 − E_a.

**The two statements.** For 0 < b ≤ ½:

- S(b): for some sequence a_n > 0, the normalised transforms
  ĝ_n(z)/ĝ_n(0) of the top-of-chain ground states g_n = topGS(a_n)
  converge to Ξ(z)/Ξ(0) locally uniformly on U_b := {|Im z| < b}. (The
  pilot's `HypConvStrip` needs no divergence of a_n, and none is used
  below; convergence at z = 0 forces ĝ_n(0) ≠ 0 for all large n, and the
  sequence is understood shifted past that point, as the pilot's
  `rh_of_strip_cross` does.)
- (a′): the paper's §11 label for the same convergence on all of ℂ, the
  normalised transform ĝ₁/ĝ₁(0) → Ξ/Ξ(0) locally uniformly (the pilot's
  `HypConv`).
- ZFS(b): ζ has no zero with 0 < |Re ρ − ½| < b.

S(½) is the pilot's hypothesis `HypConvStrip`; ZFS(½) is RH.

**Pilot facts used, by name.** `topGS_cross` (StructureD.lean): at every
a > 0 every zero z of the top ground state's transform has z ∈ ℝ ∪ iℝ, with
no hypothesis beyond a > 0. `hurwitz_closed_on` (Roadmap.lean): if entire
F_n → F locally uniformly on an open set U, F not identically zero on a
component, and every zero of every F_n (in all of ℂ, as the Lean statement
asks) lies in a closed set C, then every zero of F in U lies in C. `xi_real_ne_zero` (RiemannKernel.lean):
ξ(σ) ≠ 0 for every real σ. Theorem A (README round 40, paper-level):
Q(Φ_a) ≤ S·e₁(a)² with e₁(a) = 2[Φ(a)cosh(a/2) + ∫_a^∞|Φ′|cosh(u/2)] and
S the README's explicit bound on Σ_ρ 1/γ_ρ²; below, S₂ := Σ_ρ |γ_ρ|^{−2}
is used in its place, and the theorem is re-proved in §3.1.

---

## 1. The payoff would be real: S(b) implies ZFS(b)

**Proposition 1.** For every 0 < b ≤ ½, S(b) implies ZFS(b).

*Proof.* Let F_n(z) = ĝ_n(z)/ĝ_n(0) with g_n = topGS(a_n), for n past the
point where ĝ_n(0) ≠ 0, and suppose F_n → Ξ/Ξ(0) locally uniformly on U_b.
Ξ(0) = ξ(½) ≠ 0 by `xi_real_ne_zero`, so the limit is not identically zero.
By `topGS_cross` every zero of every F_n, in all of ℂ, lies in the closed
set C = ℝ ∪ iℝ. U_b is open and connected. By
`hurwitz_closed_on`, every zero z₀ of Ξ in U_b lies in C. If z₀ = iy with
y ≠ 0 then |y| < b ≤ ½ and Ξ(iy) = ξ(½ − y) with ½ − y a real number, so
Ξ(iy) ≠ 0 by `xi_real_ne_zero`; hence z₀ ∈ ℝ. Now ξ(s) = 0 exactly at the
nontrivial zeros, and s = ½ + iz₀ has Re s − ½ = −Im z₀. So every zero
ρ = ½ + iz₀ of ζ with |Re ρ − ½| < b has Im z₀ = 0, i.e. Re ρ = ½. ∎

For b = ½ this is the pilot's `rh_of_hypConvStrip_top`; the proof above is
its restriction to a sub-strip and adds nothing to it. The point of
recording it is only that the conclusion of the strip target is genuinely
graded: a proof of S(b) for any b > 0 would give a zero-free strip of width
b about the critical line, which is not known for any b > 0.

---

## 2. What the attempt proves: the energy signature of an off-line zero

The natural first question about S(b) for small b is what the ground states
look like if RH fails. That question has a sharp answer for the ground
*energy*, under one genericity assumption, which is the theorem of this
note.

**Hypothesis (H₁).** β* > 0, and the supremum is attained by exactly one
zero up to the symmetries: there is ρ₀ = ½ + β* + it₀ with t₀ > 0, of
multiplicity m₀ ≥ 1, such that every zero not in {ρ₀, ρ̄₀, 1−ρ₀, 1−ρ̄₀}
has β_ρ < β*.

(H₁) is a genericity assumption; §2.3 says what survives without it.

**Theorem 2 (energy signature).** Under (H₁), with η(t₀) := 2β*(β* + t₀)/t₀² + 20/t₀² (so η(t₀) < 0.2 for t₀ ≥ 14 and η(t₀) < 10⁻¹¹ for t₀ > 3·10¹²), as a → ∞,

  λ₁(a) ≤ − (1 − η(t₀)) · (m₀ e^{−2β*} / (2β*)) · e^{2β* a} · (1 − o(1)) ≤ − (1 − η(t₀)) · e^{2β* a} / (2e β*) · (1 − o(1)).

In particular −λ₁(a) grows at least exponentially with exponent 2β*.

**Theorem 3 (the trivial lower bound, unconditional).** For every a > 0,

  λ₁(a) ≥ (ψ(¼) − ln π) − 2·1.03883·(2e^{a} − 1) > −5.3722 − 4.1554 e^{a}.

Theorem 3 is the statement that no zero has β_ρ > ½, read through Theorem
2: the exponent 1 = 2·½. Together they say, under (H₁), that the growth
exponent of the negative part of the ground energy detects the zero
farthest from the critical line, and that improving the exponent in
Theorem 3 uniformly in a is then a zero-free-strip statement (β* ≤ b uniformly in height), stronger
than the classical zero-free regions, which narrow with height. The sign dichotomy itself — λ₁(a) < 0 for all large a if
and only if RH fails — is Weil's criterion with the monotonicity of λ₁ in the support (the pilot's
README states the RH-false half, round 40). The closest prior
to Theorem 2 is Bombieri (E. Bombieri, *Remarks on Weil's quadratic
functional in the theory of prime numbers, I*, Rend. Lincei Mat. Appl. 11
(2000) 183–233): for the quadratic form in the zero variables truncated to a finite set of zeros, at every support, and "if the Riemann
Hypothesis is false but only with finitely many non-trivial zeros off the
critical line", he shows that "the number of negative eigenvalues is
precisely one-half of the number of zeros failing to satisfy the Riemann
Hypothesis, provided the truncation is big enough" (abstract; Theorems 8–9
there), and for the L² window functional a trichotomy: negative, or
infinitely many off-line zeros, or a linear relation among the x^{−ρ} on the
window (his Theorem 11 and its corollary). No growth rate in the support
appears there. His numerical section inserts a fictitious off-line zero
(at 0.52 + 3.14i, with the first N zeros of ζ, N up to 160) and reports, in each parity sector, a critical half-support: below it the
sector's negative eigenvalue tends to 0 as N grows, with the eigenfunction's L²-mass concentrating at the boundary
of the interval; above it the eigenvalue converges to a strictly negative
value. (This note's Remark (b) concerns the supercritical trial's edge
concentration; the analogy with his subcritical observation is this
note's, not his.) Theorem 2 is the quantitative form of
that count for the lowest eigenvalue under (H₁), which trades Bombieri's
"finitely many off-line zeros" for a condition on the farthest one (his
introduction anticipates replacing finiteness "by a suitable density
hypothesis").

### 2.1 Proof of Theorem 3

Take a probe g with ‖g‖ = 1 and f = g ⋆ g̃. On the right side of the
explicit formula: 2 poleR(g)² ≥ 0; the archimedean integral is ≥ 0, since
f(0) = ‖g‖² ≥ |f(u)| by Cauchy–Schwarz and e^{u/2}/sinh u > 0 for u > 0;
the constant is ψ(¼) − ln π = −γ_E − π/2 − 3 ln 2 − ln π = −5.37218…; and f
vanishes outside [−2a, 2a], so the prime sum runs over n ≤ e^{2a} with
|f(ln n)| ≤ 1. Rosser–Schoenfeld give ψ(x) < 1.03883 x for all x > 0, and
partial summation gives Σ_{n≤x} Λ(n) n^{−1/2} = ψ(x) x^{−1/2} + ½∫₁^x ψ(t) t^{−3/2} dt
≤ 1.03883 (√x + (√x − 1)) = 1.03883 (2√x − 1). With x = e^{2a} the prime
term is ≥ −2·1.03883·(2e^{a} − 1). ∎

### 2.2 Proof of Theorem 2

Fix a smooth step w: ℝ → [0, 1] with w(s) = 0 for s ≤ 0, w(s) = 1 for
s ≥ 1, w′(0) = w′(1) = 0, and set C_w := ‖w″‖_∞ + 2‖w′‖_∞ + ½. (The standard
choice w(s) = h(s)/(h(s) + h(1 − s)), h(s) = e^{−1/s} for s > 0, has
‖w′‖_∞ = 2 exactly, attained at s = ½, and ‖w″‖_∞ ≈ 9.84; only ‖w′‖_∞ ≤ 2
is used, at one place.)
For a ≥ 2 put w_a(u) := w(a − |u|), even, C^∞, equal to 1 on |u| ≤ a − 1
and to 0 for |u| ≥ a. Write β := β* and S(u) := sinh(βu). The trial function
is

  g(u) := w_a(u) · sinh(βu) · sin(t₀u),

real, even (odd × odd), C_c^∞ with support in [−a, a]. By (0.1),
λ₁(a) ≤ Q(g)/‖g‖², and Q(g) = Σ_ρ ĝ(γ_ρ)² absolutely.

**Step 1: the norm.** ‖g‖² = ∫ w_a² S² sin²(t₀u) du ≥ ∫_{|u|≤a−1} S² sin²(t₀u) du.
With A = a − 1 and sin² = (1 − cos 2t₀u)/2,

  ∫_{−A}^{A} S² sin²(t₀u) du = ½ [ sinh(2βA)/(2β) − A ] − ½ ∫_{−A}^{A} sinh²(βu) cos(2t₀u) du.

The oscillatory term, with sinh² = (cosh 2βu − 1)/2 and the elementary
∫_{−A}^{A} cosh(2βu) cos(2t₀u) du = [2β sinh(2βA) cos(2t₀A) + 2t₀ cosh(2βA) sin(2t₀A)]/(2β² + 2t₀²),
is bounded in modulus by ¼[(β + t₀) cosh(2βA)/t₀² + 1/t₀]. Writing
sinh(2βA)/(2β) = e^{2βA}(1 − e^{−4βA})/(4β) and cosh(2βA) ≤ e^{2βA},

  (2.1)  ‖g‖² ≥ e^{2β(a−1)}/(8β) · (1 − ε₁(a)),
         ε₁(a) := e^{−4βA} + 4βA e^{−2βA} + 2β e^{−2βA}/t₀ + 2β(β + t₀)/t₀²,   A = a − 1.

The first three terms tend to 0 as a → ∞; the last, ε₁^∞ := 2β(β + t₀)/t₀²,
is the edge correction to the average of sin² over the window and does not
depend on a. It is the first part of η(t₀) in the theorem's statement. For
small β and a near 2, ε₁(a) exceeds 1 (at a = 2 it does for every β ≤ 0.4),
so every division by (2.1) below is taken for a ≥ a₀(β), the point past
which ε₁(a) < 1; the theorem's statement is asymptotic and a₀ costs nothing.

**Step 2: the value at the maximising zero.** Take γ₀ = t₀ + iβ, the
ordinate of the member ½ − β + it₀ of ρ₀'s quadruple (the four members
contribute symmetrically, so any one may be used). Then
e^{iγ₀u} = e^{−βu}(cos t₀u + i sin t₀u). Since g is even, the odd parts
integrate to zero and

  ĝ(γ₀) = ∫ g cosh(βu) cos(t₀u) du − i ∫ g sinh(βu) sin(t₀u) du = R − iJ,

  R := ¼ ∫ w_a sinh(2βu) sin(2t₀u) du,   J := ∫ w_a sinh²(βu) sin²(t₀u) du.

Because 0 ≤ w_a ≤ 1, J ≥ ∫ w_a² S² sin² = ‖g‖². Hence Re ĝ(γ₀)² = R² − J² ≤ R² − ‖g‖⁴.
The quadruple of ρ₀ contributes m₀ · 4 Re ĝ(γ₀)² ≤ 4m₀R² − 4m₀‖g‖⁴ to Q(g).

**Step 3: R is small.** Integrate by parts once (w_a vanishes at ±a):
R = ¼ ∫ (w_a sinh 2βu)′ cos(2t₀u)/(2t₀) du, so |R| ≤ ‖(w_a sinh 2βu)′‖₁/(8t₀).
Now (w_a sinh 2βu)′ = w_a′ sinh 2βu + 2β w_a cosh 2βu, w_a′ is supported in
a − 1 ≤ |u| ≤ a with |w_a′| ≤ ‖w′‖_∞, and ∫_{a−1}^{a} sinh 2βu du ≤ e^{2βa}(1 − e^{−2β})/(4β) ≤ e^{2βa}/2,
∫_{−a}^{a} cosh 2βu du = sinh(2βa)/β ≤ e^{2βa}/(2β). So
‖(w_a sinh 2βu)′‖₁ ≤ e^{2βa}(‖w′‖_∞ + 1) and

  (2.2)  |R| ≤ e^{2βa} (‖w′‖_∞ + 1)/(8t₀).

**Step 4: the other zeros.** Write sin(t₀u) = (e^{it₀u} − e^{−it₀u})/(2i), so
ĝ(z) = (1/2i)[F(z + t₀) − F(z − t₀)] with F(ζ) := ∫ w_a S e^{iζu} du. For
any ζ ∈ ℂ, |e^{iζu}| ≤ e^{|Im ζ| a} on the support, and two integrations by
parts (w_a S and its derivative vanish at ±a) give
|F(ζ)| ≤ e^{|Im ζ|a} ‖(w_a S)″‖₁/|ζ|². Here (w_a S)″ = w_a″S + 2w_a′S′ + w_aS″,
and with ∫_{a−1}^{a} sinh βu ≤ e^{βa}(1 − e^{−β})/(2β) ≤ e^{βa}/2,
∫_{a−1}^{a} cosh βu ≤ e^{βa} (cosh βu ≤ cosh βa ≤ e^{βa} on an interval of
length 1), and ∫_{−a}^{a}|S| ≤ e^{βa}/β, one gets ‖(w_a S)″‖₁ ≤ e^{βa}(‖w″‖_∞ + 2‖w′‖_∞ + β) ≤ C_w e^{βa}.
Also trivially |F(ζ)| ≤ e^{|Im ζ|a}‖w_a S‖₁ ≤ e^{(β+|Im ζ|)a}/β. So for every ζ,

  (2.3)  |F(ζ)| ≤ e^{(β + |Im ζ|) a} · min( 1/β, C_w/|ζ|² ).

(i) *Zeros on the line.* For real γ, ĝ(γ)² ≤ ½(|F(γ+t₀)|² + |F(γ−t₀)|²). By the
classical bound on the zero count in unit intervals, the number of γ with
T < |γ| ≤ T + 1 is at most A₀ ln T for T ≥ 2, with A₀ an absolute constant
(Backlund). Then, using (2.3),

  Σ_{γ real} ĝ(γ)² ≤ e^{2βa} · [ 2A₀ ln(t₀+2)/β² + 2A₀C_w² Σ_{k≥1} ln(t₀+k+2)/k⁴ ] ≤ e^{2βa} · A₁ ln(t₀+2) (β^{−2} + C_w²),

with A₁ absolute (Σ_k ln(t₀+k+2)/k⁴ ≤ 1.09 ln(t₀+2) + 0.8). Dividing by (2.1):

    (2.4)  Σ_{γ real} ĝ(γ)² / ‖g‖² ≤ C₁(a) := 8β e^{2β} A₁ ln(t₀+2)(β^{−2} + C_w²)/(1 − ε₁(a))

for a ≥ a₀(β), bounded uniformly in a ≥ a₀(β) and tending to the
a-independent limit with 1 − ε₁^∞ in the denominator; C₁ below means that
limit.

(ii) *Zeros off the line other than ρ₀'s quadruple.* Group them into
quadruples with representative γ′ = t′ + iβ′, t′ > 0, 0 < β′ < β (the strict
inequality is (H₁)); a quadruple contributes 4 Re ĝ(γ′)² ≤ 4|ĝ(γ′)|² (times
multiplicity, which is absorbed into the enumeration). By (2.3) with
|Im ζ| = β′ and |ζ| ≥ |t′ ∓ t₀|,

  |ĝ(γ′)|² ≤ ½ e^{2(β+β′)a} [ min(β^{−2}, C_w²/(t′−t₀)⁴) + C_w²/(t′+t₀)⁴ ] =: e^{2(β+β′)a} M(ρ′)/2.

M(ρ′) does not depend on a, and Σ_{ρ′} M(ρ′) < ∞ by the same unit-interval
count as in (i) (it is bounded by A₂ ln(t₀+2)(β^{−2} + C_w²)). Dividing by
(2.1),

    Σ_{ρ′} 4|ĝ(γ′)|²/‖g‖² ≤ 16β e^{2β}/(1 − ε₁) · e^{2βa} · Σ_{ρ′} e^{−2(β−β′)a} M(ρ′)   (a ≥ a₀(β)).

Each term of the last sum tends to 0 as a → ∞ because β′ < β, and the sum
is dominated by Σ M(ρ′) < ∞; by dominated convergence it tends to 0. So

  (2.5)  Σ_{ρ′} 4|ĝ(γ′)|²/‖g‖² = e^{2βa} · o(1)   (a → ∞).

**Step 5: assembly.** From Steps 2–4, for a ≥ a₀(β),

  Q(g)/‖g‖² ≤ −4m₀‖g‖² + 4m₀R²/‖g‖² + C₁ + e^{2βa} o(1).

By (2.1), −4m₀‖g‖² ≤ −m₀ e^{2β(a−1)}(1 − ε₁)/(2β). By (2.2) and (2.1),
4m₀R²/‖g‖² ≤ m₀ e^{2βa} · β e^{2β}(‖w′‖_∞ + 1)²/(2t₀²(1 − ε₁)), and the ratio
of this to the negative main term is β² e^{4β}(‖w′‖_∞ + 1)²/(t₀²(1 − ε₁)²),
which with β < ½, ‖w′‖_∞ ≤ 2, t₀ ≥ 14 and ε₁ < 0.08 (for large a, since
ε₁(a) → ε₁^∞ ≤ 0.074) is at most 20/t₀² < 0.11,
strictly less than 1. Hence, with ε₁(a) → ε₁^∞,

  λ₁(a) ≤ Q(g)/‖g‖² ≤ − m₀ e^{−2β} e^{2βa}/(2β) · (1 − ε₁^∞ − 20/t₀² − o(1)) + C₁.

Since m₀ ≥ 1 and e^{−2β} ≥ e^{−1}, and η(t₀) = ε₁^∞ + 20/t₀², the stated
bound follows. The verified height 3·10¹² is used nowhere in the proof; it
enters only the remark that η(t₀) is then below 10⁻¹¹. ∎

*Remarks on the proof.* (a) The trial is the Cauchy–Schwarz maximiser of
−Im ĝ(γ₀) at fixed norm: −Im ĝ(γ₀) = ∫ g sinh(βu) sin(t₀u), maximised by
g ∝ sinh(βu) sin(t₀u), and the window w_a only makes the explicit formula
apply in its classical class. The constant 1/(2β) is therefore the sharp
constant for a single-quadruple trial. (b) The whole negativity comes from
the u = ±a edges: sinh²(βu) has its mass within O(1/β) of the edge. This
is the edge-concentrated state referred to in §3.

### 2.3 Without (H₁)

If the supremum β* is attained by finitely many zeros, the same proof goes
through with a trial prescribing purely imaginary values ĝ(γ_j) = i c_j at
every maximising zero (the evaluation map from real even L²[−a, a] onto
ℂ^k at one representative per quadruple, k zeros with distinct positive
real parts t_j, is surjective: cos(t_ju)cosh(βu) and sin(t_ju)sinh(βu) are
linearly independent; a conjugate pair would give only conjugate values), at the cost of a Gram
constant depending on that finite configuration; I have not written this
out. If β* is not attained, the trial above at a zero with β₀ > β* − ε
loses control of the infinitely many zeros with β′ ∈ (β₀, β*), whose
contributions are bounded only by e^{2εa} times a convergent sum, and the
argument gives nothing for a → ∞. A Landau-type Ω-argument on the prime
side would give λ₁(a) ≤ −e^{2(β*−ε)a} along a sequence a_k → ∞; that route
is classical but was not carried out here. So what is proved in
general is Theorem 3 plus the (H₁) case of Theorem 2, and the
contrapositive below is stated with (H₁).

**Corollary 4.** If λ₁(a) ≥ −C e^{2ba} for some b < ½, some C, and all large
a, then no zero ρ₀ satisfies (H₁) with β_{ρ₀} > b. Assume RH, or else
(H₁). Then Theorem A and Theorem 2 give a dichotomy: either RH holds and
0 ≤ λ₁(a) ≤ S₂ e₁(a)²/‖Φ_a‖² = exp(−2πe^{2a} + O(a)) for every a, or RH fails
under (H₁) and λ₁(a) ≤ −(1 − η(t₀)) e^{2β*a}/(2eβ*)(1 − o(1)). There is no
intermediate regime. (The lower bound 0 ≤ λ₁ under RH is Weil's criterion
on smooth probes, extended to the pilot's L² probe class by mollification:
the pilot's Mollify.lean gives convergence of box averages in L² and in
archimedean energy, three box averages give a C² function (`av3_C2`, TheoremC.lean) that is a probe (`probe_Av`, thrice; for box width h the half-support
grows by 3h/2, harmless since positivity under RH holds at every support), and the pole and prime terms are L²-continuous
on probes of bounded support.)

*Consequence for the computed cells.* At the paper's cells (a ≤ 1.75)
Theorem 2's trial is not even defined (it needs a ≥ 2), and its bound turns
negative only beyond a threshold: its positive part C₁ is of order
β ln t₀ (β^{−2} + C_w²) with t₀ > 3·10¹² for any off-line zero, so the
negative term e^{2βa}/(2eβ) wins only for a ≳ (1/2β) ln(C₁ · 2eβ), which is
about 40 for β = 0.1 and a few hundred for β = 0.01. The positivity of λ₁ at the
cells is therefore not contradicted by Theorem 2 under either alternative,
RH or its failure at any height above the verified one. This is not a
defect of the cells; it is the content of Corollary 4: the RH-false branch is invisible until the half-support a exceeds about
(ln ln(height) + O(1))/(2β), the O(1) carrying the constants of C₁.

---

## 3. Why the strip target's hypothesis is expected not to be graded

### 3.1 The min–max route, and why it fails quantitatively

Theorem A (re-proved). Φ̂(γ_ρ) = Ξ(γ_ρ)/2 = 0 at every zero, on or off the
line, by (0.2). So Q(Φ_a) = Σ_ρ E_a(γ_ρ)² ≤ Σ_ρ |E_a(γ_ρ)|². Integrating
E_a(z) = 2∫_a^∞ Φ(u) cos(zu) du by parts and using |sin(zu)| ≤ cosh(u/2)
for |Im z| ≤ ½ gives |E_a(z)| ≤ e₁(a)/|z| on the strip, hence
Q(Φ_a) ≤ e₁(a)² Σ_ρ |γ_ρ|^{−2}, unconditionally, with e₁(a) = exp(−πe^{2a} + O(a)).
So the ground energy, when nonnegative, is at most exp(−2πe^{2a} + O(a)).

The pilot's min–max bound (`normSq_sub_le_of_gap`) reads
‖g − φ‖² ≤ 2(Q(φ) − λ₁)/(s − λ₁) for a normalised trial φ with nonnegative
overlap with the ground state g, and any s > λ₁ certified as a lower bound
for the second eigenvalue (`Lam2Ge a s`); write λ₂ for the best such s. To reach S(b) from it one needs Q(φ) − λ₁ ≤ e^{−2ba}(λ₂ − λ₁),
i.e. a trial whose excess energy over the ground energy is a fraction
e^{−2ba} of the spectral gap. The pilot's measurements (README round 62,
its own scripts) put λ₂ many orders of magnitude below Q(Φ_a); in its words,
"A usable trial would need `Q(φ) ≪ λ₂`." The structural reason is the
dimension count: the even probes of half-support a have about aT/π
degrees of freedom below height T (the cosine modes cos(kπu/a) with
kπ/a ≤ T; an even entire function of exponential type a in the
Paley–Wiener class has aT/π + o(T) zeros in [0, T] at most, Cartwright–Levinson), while the zeros number (T/2π) ln(T/2πe) there; the two agree at
T = 2πe^{2a+1} = e·T₀, above the paper's measured wall (2T₀/e, 2T₀). Below that
height a probe can vanish at every zero and pay nothing, so the form has a
near-null space of dimension of order a e^{2a}, and its second eigenvalue
is set by the tail of the zeros beyond the height the second state can
reach, not by a gap of order one. Any trial that is only e^{−ba}-close to
Φ_a in L² may differ from it pointwise at the zeros by that much and can
be made to vanish there, but the residual energy of Φ_a-based trials is
governed by e₁(a)² ≈ exp(−2πe^{2a}), and to push it below λ₂ the trial
would have to reproduce the ground state's own dodging up to its own
horizon, i.e. be the ground state. By this accounting the route is closed
rather than merely hard; the accounting rests on the pilot's measured λ₂
and on the dimension count, not on a theorem, and it is offered as such.
The pilot's round 68 (its `frontier/nullvec/`, after this note's first
version) measures exactly this from the arithmetic side alone: the
truncation's energy is the truncation defect, of order (0.03–0.11)·Φ(a)²;
the ratio R = (Q(φ_a) − λ₁)/(λ₂ − λ₁), with φ_a the normalised truncation
of Φ (this note's Φ̃) and θ its angle to the ground state, grows from 0.04
to 10⁴¹ over δ ∈ [0.7, 3] while sin²θ falls to 2·10⁻⁴; its own verdict is "The energy route
is dead" and "The L² route survives", and it names the need as "a
structural reason why the minimiser tracks the null vector Φ away from
the edges, not a spectral-gap estimate" — the pilot's numbers and words,
not this note's.

### 3.2 What S(b) asks of the ground state when RH fails

Suppose RH fails and (H₁) holds. By Theorem 2 the ground state at large
support has energy ≤ −(1 − η(t₀)) e^{2β*a}/(2eβ*)(1 − o(1)). The following
inequality is exact.

**Proposition 5.** Let g be a ground state at half-support a, ‖g‖ = 1,
Φ̃ = Φ_a/‖Φ_a‖, c = ⟨g, Φ̃⟩, r = g − cΦ̃, q_a = Q(Φ̃), and B the symmetric
bilinear form of Q. Then |c| · (q_a − λ₁(a)) ≤ 2 |B(Φ̃, r)|.

*Proof.* Q(g) = c²q_a + 2cB(Φ̃, r) + Q(r) and Q(r) ≥ λ₁‖r‖² = λ₁(1 − c²),
while Q(g) = λ₁. So λ₁c² ≥ c²q_a + 2cB, i.e. c²(q_a − λ₁) ≤ −2cB ≤ 2|c||B|. ∎

When λ₁ ≤ −(1 − η)e^{2β*a}/(2eβ*)(1 − o(1)), the left side is at least
|c|[(1 − η)e^{2β*a}/(2eβ*)(1 − o(1)) − |q_a|], and |q_a| ≤ exp(−2πe^{2a} + O(a))
by Theorem A (its bound is on the modulus, the sign of q_a being unknown
without RH);
while B(Φ̃, r) = Σ_ρ Φ̂̃(γ_ρ) r̂(γ_ρ) — the zero-side form of B for the L²
probe r, part of the same unwritten step as the sampling bound below — has
every first factor bounded by
e₁(a)/(|γ_ρ|‖Φ_a‖) = exp(−πe^{2a} + O(a)). *Provided* the zero sum
Σ_ρ |r̂(γ_ρ)|² is finite with at most exponential growth in a (a sampling
bound for probes at the zeros — the pilot's `weighted_le_archE` and
`tail_le` in Existence.lean bound a logarithmically weighted sum of Fourier
coefficients on [−2a, 2a] by the archimedean energy, and the passage from
that to a sum over the zeros, whose density is of order ln T, is written
out neither there nor here, for zeros on the line or off it),
Cauchy–Schwarz gives |c| ≤ exp(−πe^{2a} + O(a)): the ground state is
super-exponentially orthogonal to Φ_a. This is the one step of this
section that is a sketch, and its unwritten part is the sampling bound.

What the sketch shows is what S(b) would have to mean if RH failed: the
ground state's mass sits in the edge-concentrated, high-frequency state of
Theorem 2, orthogonal to Φ_a; S(b) is a statement about the *shape* of the
normalised transform near the origin, scale-free, and is not formally
contradicted by |c| → 0, because ĝ(0) may be tiny with ĝ/ĝ(0) still of the
right shape on compacts. But nothing in the variational problem supplies
that shape: the Euler–Lagrange equation Σ_ρ ĝ(γ_ρ) φ̂(γ_ρ) = λ₁⟨g, φ⟩ couples
the low-frequency part of g to the edge state through the far zero, at
relative size of order 1/t₀ per unit of e^{2β*a}, and drives it with the
eigenvalue λ₁ ≈ −e^{2β*a}, not toward Ξ. I therefore expect S(b) for any
b > 0 to fail whenever RH fails, which would make S(b) equivalent in
strength to RH for every b, and its conclusion ZFS(b) graded only because
Proposition 1 discards information. This expectation is heuristic; I have
not proved that S(b) fails when RH fails, and Proposition 1 is all that is
rigorous in this direction.

### 3.3 Where the difficulty sits under RH

Assume RH. Then λ₁(a) ∈ [0, exp(−2πe^{2a} + O(a))] and the pilot's chain would
be an equivalence if the closeness rate could be proved. The transform's
convergence has a mechanism in the paper's own Theorem 1bu(ii): under Hypothesis D at half-support a with horizon T_D(a) (the zero multisets of the
transform and of Ξ agreeing below T_D, with multiplicity), the normalised
transform satisfies
|ln[ĝ(r)/ĝ(0)] − ln[Ξ(r)/Ξ(0)]| ≤ 2R²ε(a) for |r| ≤ R ≤ T_D/2, with
ε(a) = Σ_{|τ|≥T_D}|τ|^{−2} + Σ_{γ≥T_D}γ^{−2}, where τ runs over the zeros of
the transform. The paper marks the rate of ε unproved ("Not proved: the
rate of ε(δ)"). Its second sum is classical, ≍ (ln T_D)/T_D. Its first is
bounded by Jensen's formula: an even entire function of exponential type a
with |ĝ(z)| ≤ ‖g‖₁e^{a|Im z|} has at most aer + ln(‖g‖₁/|ĝ(0)|) zeros in |z| ≤ r when ĝ(0) ≠ 0 (under D
at any positive horizon, ĝ_a(0) ≠ 0 follows from Ξ(0) ≠ 0 and the equal
orders at 0), so Σ_{|τ|≥T}|τ|^{−2} ≤ 2ae/T + ln(‖g‖₁/|ĝ(0)|)/T², and the first
sum is also O(a/T_D) provided ln(1/|ĝ_a(0)|) ≲ a e^{2a}, a mild lower bound
on the transform at the origin that is not proved here. With T_D of order
e^{2a}, as the dimension count of §3.1 and the paper's measured horizons
indicate, and that bound, ε(a) ≍ a e^{−2a}. The same exponent 2 appears in the pilot's
measured decay of the L² angle to Φ_a, e^{−2a} with a slowly drifting local
exponent (README round 62), four times the threshold ½ of the chain;
1bu(ii) explains the transform's exponent, and whether the angle's has the
same origin is not shown here (L² closeness implies transform closeness on
compacts, by the pilot's `norm_ghatC_sub_le`, not conversely). So under RH and Hypothesis
D the transform's convergence rate has a mechanism: it is the tail of the
zeros beyond the dodging horizon. What is unproved is Hypothesis D itself: that the ground state's
transform vanishes at every zero below a horizon T_D(a) ≍ e^{2a} and has no
other zero there. The pilot located where RH enters the natural proof of convergence ("uses `Q = Σ_γ |ĝ(γ)|²`, a sum of squares, which is RH", README
round 40); under RH that obstacle is absent, and D becomes a statement in
approximation theory about the minimiser of a sum of squares over a
sampling set of near-critical density, with the zeros' separation properties (unknown) as the likely technical
input. The pilot's round 69 (its `frontier/nullvec/`, after this note's
sixth sweep) locates the structure numerically, on supports up to δ = 4.5:
the ground state's deviation from Φ lies almost entirely along Φ″ (share
0.99976 of the deviation at δ = 3, and 1 − 1.2·10⁻¹⁴ within the span of
Φ″, Φ⁗, Φ⁽⁶⁾), with coefficient ≈ −0.020·e^{−δ}, so that locally
ĝ_a ≈ c·Ξ(z)·e^{τz²} with a zero-free Gaussian multiplier, τ ≈ 0.020·e^{−δ};
its own status line reads "The laws `sin²θ ~ e^{−4a}` and `β ~ e^{−δ}` are
inferred, not proved", and it remarks that "`Φ`'s even derivatives are,
like `Φ`, null directions of Weil's form (their transforms vanish at every
zero), so a structural explanation plausibly starts there" — the pilot's
numbers, conjecture and words, not this note's. That is the same target as
item 3 of §4, seen from the minimiser's side: the structure to prove is
that the minimiser stays in the null directions of the form.

---

## 4. Conclusion, and the honest next target

1. **The strip target as posed is not expected to be attackable below full
   strength.** Its conclusion is graded (Proposition 1); its hypothesis is
   expected not to be: S(b) requires the ground states to converge to Ξ at
   all, which, by the heuristic of §3.2, should fail whenever RH fails at
   any distance from the line.
   The audacious framing in the preceding discussion was right about the
   payoff and, if §3's heuristic is right, wrong about the difficulty; this
   note corrects it to that extent.

2. **What the attempt proves** is Theorem 2 with Theorem 3 and Corollary 4:
   the truncated Weil ground energy has two regimes, super-exponentially
   small nonnegative under RH, exponentially negative with exponent 2β*
   when RH fails under (H₁), and, assuming RH or (H₁), nothing in between. Under (H₁) the growth
   exponent of −λ₁ detects the *farthest* zero from the line, and lower
   bounds on λ₁(a) uniform in a with exponent below 1 are then
   zero-free-strip statements uniform in height, beyond the classical
   zero-free regions, so the variational structure gives no cheap route to
   those either. The qualitative
   sign dichotomy is Weil's criterion; the count of negative eigenvalues
   is Bombieri's (2000, cited after Theorem 3); the growth rate with the
   sharp single-quadruple constant 1/(2β*) is the quantitative form, which
   I have not found stated elsewhere.

3. **The honest open problem** that this analysis isolates, conditional and
   well-posed: *under RH, prove Hypothesis D from the form* — that the
   top-of-chain ground state's transform (the family of Proposition 1)
   vanishes at every zero below a horizon T_D(a) → ∞ with T_D(a) ≥ c e^{2a},
   with the zero's multiplicity, and at no other point below it, with the
   tail ε(a) of §3.3 tending to 0. With 1bu(ii)'s bound this would prove,
   under RH, the locally uniform convergence of the normalised transform to
   Ξ/Ξ(0) — the paper's (a′), the pilot's `HypConv` — at the rate ε(a) on
   compacts, a e^{−2a} under the origin bound of §3.3, and with
   Proposition 1 at b = ½ make the chain an equivalence, RH ⟺ (a′). The L²
   closeness the pilot measures (its angle to Φ_a) is a stronger statement
   that 1bu(ii) does not give; the paper itself adds mass and
   second-moment conditions to reach even ĝ₁(0)² → 2πΞ(0)²/∫Ξ². It does
   not prove RH, and nothing in this note does.

4. **No numerics were run.** The only arithmetic inputs of §2's proofs are the constants of Theorem 3, the first zero's height (t₀ ≥ 14, used in Theorem 2's statement and in
   Step 5 for η(t₀) < 0.2, ε₁ < 0.08 and 20/t₀² < 0.11), the verified height 3·10¹² for the
   first off-line zero (used to remark that η(t₀) is then negligible and in
   the cells arithmetic of §2.3), and Backlund's
   unit-interval zero count with an unspecified absolute constant, which enters the term C₁(a), of a-independent limit, and the summability
   of M(ρ′) in Step 4(ii). §3 reports the pilot's and the paper's figures as theirs.
