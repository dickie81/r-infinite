#!/usr/bin/env python3
"""
THEOREM 1am -- the selection justified from Riemann: the pole-balance
flank and the Gamma(1/2) ladder.

THE COMMISSION.  Justify the source selection from Riemann: ground the
committed source-selecting features in zeta-native structure rather
than standalone Gamma-phenomenology.

ROUND-159 SWEEP (the landing's hostile round; findings verified by
the lead and swept here and in the paper): F1 MAJOR -- the paper's
census phrase "both sink rungs" was false-when-written (ONE sink,
one selecting feature; struck on both carriers); F2 minor -- the
"single root" claim lacked its domain (qualifier "on x > 0" added
here and in the paper; on psi's full domain every negative branch
carries a root, e.g. -0.3816...); F3 minor -- the census attributed
the Absolute/sink thresholds to the bridge identity while only S2
used it (g6 extended with the bridge-route recomputation of BOTH
crossings; the attribution now computed, not associative).

THE CONTENT (three theorems + honest partials).
  S1 (one equation, three landmarks, unit-spaced exactly).  psi(x) =
      ln(pi) has a single root ON x > 0, x* = 3.6284732024... (psi
      strictly increasing there; domain qualifier round 159 F2), and
      the extremum conditions of the cascade's Gamma-objects are that
      ONE equation in three half-unit-shifted arguments: the
      ball-volume maximum at d = 2x*-2 = 5.2569...,
      the sphere-area (Omega_d) maximum = the potential's zero at
      d = 2x*-1 = 6.2569..., and the S^(d-1)-area maximum at
      d = 2x* = 7.2569... -- spaced EXACTLY one layer apart.
      Equivalently the volume max is p(d+1) = 0 and the third rung is
      p(d-1) = 0: one condition, three consecutive tower arguments.
      The committed Observer feature (part0: "$V_d$ has a unique
      maximum at $d_V = 5$") and Amplitude feature (part0: "$p(d)$
      has a unique zero at $d_0 = 7$") are the first two rungs.  The
      third rung is structure only -- NOT a derivation of the integer
      label 7; the convention residue stands.
  S2 (the flanked point is zeta's pole balance).  By the committed
      bridge identity (p = zeros - poles + primes,
      cascade_explicit_formula_bridge.py), p = 0 is the exact balance
      zeros + primes = poles: at d = 6.2569... the Hadamard zero side
      (0.292665...) plus the prime side (0.004955...) equals the
      two-pole term 1/s + 1/(s-1) = 0.297621... -- zeta's pole at
      s = 1 with its functional-equation mirror at s = 0.  The
      Observer/Amplitude features are selected by zeta's own
      pole-balance condition at consecutive tower arguments -- the
      Amplitude feature AT the balance point, the Observer feature at
      exactly -1 from it; the +1 flank is the third, structure-only
      rung (the rung pair flanks at exactly +/-1, but only the -1
      side is a committed feature).
  S3 (the threshold ladder is one constant: Gamma(1/2)).  The
      committed privileged levels ("zero, c_1, c_2", part0) are
      {0, ln Gamma(1/2), Gamma(1/2)}: c_1 = (1/2)ln(pi) =
      ln Gamma(1/2) and c_2 = sqrt(pi) = Gamma(1/2) = e^{c_1}
      exactly.  One generating constant -- Gamma at the functional
      equation's symmetry point 1/2 (whose square is 1ak's 1/4) --
      read on the log scale (the Absolute threshold, d_1* =
      19.730775..., label 19) and the value scale (the sink
      threshold, d_2* = 217.626708..., label 217, excluded from
      sourcing by the 1af dynamics).
  HONEST PARTIALS.  The Gauge layer 14 stays Adams-native (the
      record's own attribution: entered by an external route); the
      feature->integer convention residue is retained -- the
      zeta-native content is at the CONTINUOUS features, no rounding
      story is offered; the categorical flag derivation persists.

HONEST SCOPE.  Pure mathematics on the committed p and the committed
bridge identity; no data, no closures, no new physics -- category (a).
The bridge's own no-direction caveat applies.  Check 7 clean (Gamma/psi
and committed-bridge bookkeeping; no semiclassics); Check 8 clean (no
hypothesis input).

VERIFICATION (12 gates, exit-gated).
  V1 -- g1 the one-equation ladder: three INDEPENDENT root-finds
       (psi(d/2+1), psi((d+1)/2), psi(d/2) each = ln pi), brackets
       (5,6)/(6,7)/(7,8), pairwise spacings exactly 1 to 30 digits,
       psi' > 0 sampled; g2 the object identification: d/dd ln V_d and
       d/dd ln Omega_d vanish at the rungs by direct numerical
       differentiation of log-Gamma forms (independent of the digamma
       formula), integer argmaxes V:5 and Omega:6 (part0's d_V = 5,
       d_max = 6); g3 the displacement identity: p(r1+1) = p(r2) =
       p(r3-1) = 0 with p the bridge's digamma form -- one condition,
       three consecutive arguments.
  V2 -- g4 the pole balance at r2: zeros := xi'/xi(s0) (numerical
       log-derivative of the assembled xi, the bridge's own prefactor
       form), primes := -zeta'/zeta(s0), poles := 1/s0 + 1/(s0-1);
       |zeros + primes - poles| < 1e-30 with component brackets.
  V3 -- g5 the ladder exactness: c_1 = ln Gamma(1/2), c_2 =
       Gamma(1/2) = sqrt(pi) = e^{c_1}, all residuals < 1e-35 at dps
       40; g6 the threshold crossings: d_1* in (19,20) within
       [19.7307750, 19.7307751], d_2* in (217,218) within
       [217.6267086, 217.6267087] (inward-rounded brackets), both
       rounding to part0's printed 19.7308 / 217.6267, AND both
       recomputed through the bridge route zeros - poles + primes =
       the level constant (round 159 F3).
  V4 -- g7 part0 anchors (the privileged-values sentence >= 2; the
       d_V = 5 and d_0 = 7 sentences; 19.7308, 217.6267, 6.257 each
       >= 2); g8 the substrate: the bridge file's identity block +
       xi prefactor + s = d+1 convention anchored, and the committed
       classifier imported LIVE (eight observables; the source map
       {Absolute:19, Observer:5, Gauge:14, Amplitude:7}; Observer =
       the integer below r1; Amplitude = the integer above r2;
       Absolute = the integer below d_1*).
  V5 -- g9 the honest partials retained in the paper (the
       external-route attribution; the front-matter convention
       residue; "the sink cannot source"); g10 1am's key sentences
       anchored by content, plus the round-159 sweep anchors (two F1
       strike frames counted, the one-sink content, the F2 domain
       qualifier); g11 the sibling chain green after the
       census advance (cascade_type_counting.py 12/0, which itself
       re-runs the two Weil-arc siblings); g12 the footer census
       (this script backticked; "71 scripts cited in place";
       "Theorems 1i-1au" -- the census advances with each landing
       (the census-evolution class, disclosed; the gate carries
       the live values)).

Sabotage record (full-tree scratchpad copy, tar --exclude=.git, at
the landing): (a) the verifier copy's r3 equation flipped to
psi(d/2) = ln(2 pi) -> g1 trips (bracket + spacing: the flipped root
lands at 13.55) AND g3 trips (p(r3-1) != 0), 10/2, exit 1 -- g2 is
unaffected, it differentiates at r1/r2 only (the drafted prediction
"g2/g3, 9/3" was wrong; census corrected to the run, per the
round-156 F2 lesson); (b) the paper copy's 1am sentence "one
condition, three consecutive tower arguments" mangled mid-anchor
("three" -> "two") -> g10 trips, 11/1, exit 1; (c) the part0 copy's
"$p(d)$ has a unique zero at $d_0 = 7$" mangled ("unique" ->
"special") -> g7 trips, 11/1, exit 1.  At the round-159 sweep:
(d) the F1 one-sink annotation content mangled in the paper copy
(ONE -> A) -> g10 trips, 11/1, exit 1; (e) the bridge-route probe
decoupled in the verifier copy (sB = ds_ + 1.1) -> g6 trips, 11/1,
exit 1.  Clean baselines 12/0 exit 0
before and after each.  Twelve gates (count checked against the
gate() census pre-commit).
"""
import os
import subprocess
import sys

from mpmath import mp, mpf, log, exp, sqrt, pi as mppi, digamma, findroot, \
    gamma as mpgamma, zeta, diff, polygamma

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
PART0 = os.path.join(ROOT, "src", "cascade-series-part0.tex")
BRIDGE = os.path.join(ROOT, "tools", "research",
                      "cascade_explicit_formula_bridge.py")

sys.path.insert(0, os.path.join(ROOT, "tools", "verifiers"))
import verify_selection_rule as vsr  # noqa: E402

mp.dps = 40
results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


lnpi = log(mppi)


def p(d):
    """The committed potential (bridge form): p(d) = -ln(pi)/2 + psi((d+1)/2)/2."""
    return -lnpi / 2 + digamma((mpf(d) + 1) / 2) / 2


print("V1 -- S1: one equation, three landmarks, unit-spaced exactly")
r1 = findroot(lambda d: digamma(d / 2 + 1) - lnpi, mpf("5.3"))
r2 = findroot(lambda d: digamma((d + 1) / 2) - lnpi, mpf("6.3"))
r3 = findroot(lambda d: digamma(d / 2) - lnpi, mpf("7.3"))
mono = all(polygamma(1, mpf(x)) > 0 for x in ("0.5", "1", "3.63", "10", "110"))
ok = 5 < r1 < 6 and 6 < r2 < 7 and 7 < r3 < 8
ok &= abs((r2 - r1) - 1) < mpf("1e-30") and abs((r3 - r2) - 1) < mpf("1e-30")
ok &= mono
gate("g1 three independent root-finds of the ONE equation psi = ln pi "
     "(shifts d/2+1, (d+1)/2, d/2): brackets (5,6)/(6,7)/(7,8), "
     "spacings exactly 1 to 30 digits, psi' > 0 sampled on x > 0 "
     "(the domain of the uniqueness claim, round 159 F2)",
     ok, f"r1={float(r1):.10f} r2={float(r2):.10f} r3={float(r3):.10f}")

lnV = lambda d: (d / 2) * lnpi - log(mpgamma(d / 2 + 1))     # noqa: E731
lnOm = lambda d: log(2) + ((d + 1) / 2) * lnpi - log(mpgamma((d + 1) / 2))  # noqa: E731
dV = diff(lnV, r1)
dOm = diff(lnOm, r2)
V = lambda d: mppi ** (mpf(d) / 2) / mpgamma(mpf(d) / 2 + 1)  # noqa: E731
Om = lambda d: 2 * mppi ** ((mpf(d) + 1) / 2) / mpgamma((mpf(d) + 1) / 2)  # noqa: E731
ok = abs(dV) < mpf("1e-25") and abs(dOm) < mpf("1e-25")
ok &= V(5) > V(4) and V(5) > V(6)          # part0: d_V = 5
ok &= Om(6) > Om(5) and Om(6) > Om(7)      # part0: d_max = 6
gate("g2 the object identification: ln V_d and ln Omega_d stationary "
     "at r1/r2 by direct log-Gamma differentiation; integer argmaxes "
     "V at 5, Omega at 6 (part0's d_V, d_max)",
     ok, f"|dV|={float(abs(dV)):.1e} |dOm|={float(abs(dOm)):.1e}")

ok = abs(p(r1 + 1)) < mpf("1e-30")
ok &= abs(p(r2)) < mpf("1e-30")
ok &= abs(p(r3 - 1)) < mpf("1e-30")
gate("g3 the displacement identity: p(r1+1) = p(r2) = p(r3-1) = 0 -- "
     "one balance condition, three consecutive tower arguments", ok)

print("V2 -- S2: the flanked point is zeta's pole balance")
s0 = r2 + 1


def xi(s):
    return mpf("0.5") * s * (s - 1) * mppi ** (-s / 2) * mpgamma(s / 2) * zeta(s)


zeros = diff(lambda t: log(xi(t)), s0)
primes = -diff(lambda t: log(zeta(t)), s0)
poles = 1 / s0 + 1 / (s0 - 1)
resid = abs(zeros + primes - poles)
ok = resid < mpf("1e-30")
ok &= mpf("0.292") < zeros < mpf("0.293")
ok &= mpf("0.0049") < primes < mpf("0.0050")
ok &= mpf("0.297") < poles < mpf("0.298")
ok &= abs(poles - (1 / (r2 + 1) + 1 / r2)) < mpf("1e-35")
gate("g4 the pole balance at r2: zeros (xi'/xi, the bridge's "
     "prefactor form) + primes (-zeta'/zeta) = poles (1/s + 1/(s-1)) "
     "to 30 digits, components bracketed",
     ok, f"resid={float(resid):.1e}")

print("V3 -- S3: the threshold ladder is one constant, Gamma(1/2)")
c1 = lnpi / 2
c2 = sqrt(mppi)
half = mpf(1) / 2
ok = abs(c1 - log(mpgamma(half))) < mpf("1e-35")
ok &= abs(c2 - mpgamma(half)) < mpf("1e-35")
ok &= abs(exp(c1) - c2) < mpf("1e-35")
gate("g5 the ladder exactness: c1 = ln Gamma(1/2), c2 = Gamma(1/2) = "
     "sqrt(pi) = e^{c1} -- levels {0, L, e^L}, one generator", ok)

d1s = findroot(lambda d: p(d) - c1, mpf("19.7"))
d2s = findroot(lambda d: p(d) - c2, mpf("217.6"))
ok = 19 < d1s < 20 and 217 < d2s < 218
ok &= mpf("19.7307750") < d1s < mpf("19.7307751")
ok &= mpf("217.6267086") < d2s < mpf("217.6267087")
ok &= abs(d1s - mpf("19.7308")) < mpf("0.00005")     # part0's printed value
ok &= abs(d2s - mpf("217.6267")) < mpf("0.00005")
# round 159 F3: the census attributed the thresholds to the bridge
# identity while only S2 used it -- both crossings are now recomputed
# through the bridge route itself: zeros - poles + primes (zeros =
# xi'/xi, primes = -zeta'/zeta) must equal the level constant at the
# crossing.
for ds_, c_ in ((d1s, c1), (d2s, c2)):
    sB = ds_ + 1
    zB = diff(lambda t: log(xi(t)), sB)
    pB = -diff(lambda t: log(zeta(t)), sB)
    ok &= abs(zB - (1 / sB + 1 / (sB - 1)) + pB - c_) < mpf("1e-30")
gate("g6 the threshold crossings: p = c1 at d1* in "
     "[19.7307750, 19.7307751], p = c2 at d2* in "
     "[217.6267086, 217.6267087] (inward brackets), both rounding to "
     "part0's printed values; AND both recomputed through the bridge "
     "route zeros - poles + primes = the level (round 159 F3)",
     ok, f"d1*={float(d1s):.9f} d2*={float(d2s):.9f}")

print("V4 -- the committed anchors and the live substrate")
part0 = norm(open(PART0, encoding="utf-8").read())
ok = part0.count("The three privileged values of $p(d)$---zero, $c_1") >= 2
ok &= "$V_d$ has a unique maximum at $d_V = 5$" in part0
ok &= "$p(d)$ has a unique zero at $d_0 = 7$" in part0
ok &= part0.count("19.7308") >= 2
ok &= part0.count("217.6267") >= 2
ok &= part0.count("6.257") >= 2
gate("g7 part0 anchors: the privileged-values sentence (>=2), the "
     "d_V = 5 and d_0 = 7 sentences, the printed crossings 19.7308 / "
     "217.6267 / 6.257 (each >=2)", ok)

bridge = norm(open(BRIDGE, encoding="utf-8").read())
ok = "p(d) = [ZEROS" in bridge
ok &= 'mpf("0.5") * s * (s - 1)' in bridge
ok &= "with s = d+1 and z = d + 1/2" in bridge
src = {t: vsr.predict_source(t)
       for t in ("Absolute", "Observer", "Gauge", "Amplitude")}
ok &= len(vsr.OBSERVABLES) == 8
ok &= src == {"Absolute": 19, "Observer": 5, "Gauge": 14, "Amplitude": 7}
ok &= src["Observer"] == int(r1)          # 5 = the integer below r1
ok &= src["Amplitude"] == int(r2) + 1     # 7 = the integer above r2
ok &= src["Absolute"] == int(d1s)         # 19 = the integer below d1*
gate("g8 the substrate: the bridge identity block + xi prefactor + "
     "s = d+1 convention anchored; the committed classifier LIVE "
     "(eight observables; sources {19, 5, 14, 7} tied to the rungs)", ok)

print("V5 -- the paper: partials, key sentences, siblings, footer")
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = ("entered the source set by an external route (Adams' theorem and "
      "the Bott mirror," in paper)
ok &= ("no uniform rounding rule produces {5, 7, 19, 217} from the "
       "feature set" in paper)
ok &= "the sink cannot source" in paper
gate("g9 the honest partials retained: the Gauge layer's "
     "external-route attribution; the front-matter feature->integer "
     "convention residue; the 1af sink exclusion", ok)

ok = "one condition, three consecutive tower arguments" in paper
ok &= ("the Amplitude feature AT the balance point, the Observer "
       "feature at exactly −1 from it" in paper)
ok &= "The ladder is generated by the single constant Γ(½)" in paper
ok &= "it is NOT offered as a derivation of the integer label 7" in paper
ok &= "the ζ-native content is at the CONTINUOUS features" in paper
# round 159 sweep anchors, BY CONTENT: the two F1 strike frames (count
# == 2), the one-sink annotation content, and the F2 domain qualifier.
ok &= paper.count("struck round 159 F1") == 2
ok &= "the record has ONE sink" in paper
ok &= "single root on x > 0" in paper
gate("g10 1am's key sentences anchored by content (the one-condition "
     "ladder; the flank; the one-constant ladder; the label-7 "
     "non-claim; the continuous-features scope; the round-159 sweep: "
     "two F1 strike frames, the one-sink content, the F2 domain "
     "qualifier)", ok,
     f"F1 frames {paper.count('struck round 159 F1')}")

rr = subprocess.run([sys.executable,
                     os.path.join(ROOT, "tools", "research",
                                  "cascade_type_counting.py")],
                    capture_output=True, text=True)
ok = rr.returncode == 0 and "12 pass / 0 fail" in rr.stdout
gate("g11 the sibling chain green after the census advance "
     "(type_counting 12/0, itself re-running the two Weil-arc "
     "footer-gating siblings)", ok)

# 1an landing: the footer census advanced (63 -> 64; range -> 1an);
# 1ao landing: advanced again (64 -> 65; range -> 1ao) -- the
# census-evolution class, disclosed each time.
ok = "`cascade_riemann_selection.py`" in paper
ok &= "71 scripts cited in place" in paper
ok &= "Theorems 1i–1au" in paper
gate("g12 the footer census (advanced at the 1an-1ap landings, "
     "disclosed): this script backticked; 71 cited in place; the "
     "range 1i–1au (label re-synced rounds 167 F6, 175 F2)", ok)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (12 gates)")
print("READING: the selection justified from Riemann.  S1: the")
print("cascade's dynamic landmarks are ONE equation, psi(x) = ln pi,")
print("read in three half-unit-shifted arguments -- the volume max")
print("(5.2569...), the potential's zero = Omega max (6.2569...), and")
print("the S^(d-1)-area max (7.2569...) -- unit-spaced EXACTLY;")
print("equivalently p(d+1) = 0 / p(d) = 0 / p(d-1) = 0.  S2: by the")
print("committed bridge identity the flanked point is zeta's pole")
print("balance, zeros + primes = poles -- the Observer and Amplitude")
print("features are zeta's own balance condition at consecutive tower")
print("arguments: the Amplitude feature AT the balance point, the")
print("Observer feature at exactly -1 from it (the +1 flank is the")
print("structure-only third rung).  S3: the privileged")
print("levels are {0, ln Gamma(1/2), Gamma(1/2)} -- one constant,")
print("Gamma at the functional equation's half, read on the log scale")
print("(the Absolute threshold, label 19) and the value scale (the")
print("sink threshold, label 217, dynamics-excluded from sourcing).")
print("HONEST PARTIALS: the Gauge layer 14 stays Adams-native (the")
print("record's own external-route attribution); the feature->integer")
print("convention residue is retained -- the zeta-native content is at")
print("the continuous features, no rounding story offered; the")
print("categorical flag derivation persists.  No data, no closures,")
print("no new physics; no direction of explanation claimed.")
sys.exit(0 if n_fail == 0 else 1)
