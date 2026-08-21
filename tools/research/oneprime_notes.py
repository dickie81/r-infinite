#!/usr/bin/env python3
"""THE ONE-PRIME POSITIVITY ARC -- opening notes and the sweep
verdict (owner's commission: "the word", after the audacity
assessment named this the program's first attempt at proving
unconditional new mathematics).

THE TARGET. Prove epsilon_infty(L) > 0 -- Weil positivity for the
full test-function class -- for support lengths L in
[log 2, log 3), where the prime side is carried by p = 2 alone.

STAGE 0 -- THE LITERATURE SWEEP (run 2026-08-21; the
pre-registered kill DOES NOT FIRE):
  PROVEN: Connes-Consani, "Weil positivity and Trace formula, the
    archimedean place" (arXiv:2006.13771; Selecta Math. 27, 77
    (2021)), Theorem 1: positivity for g supported in
    [2^{-1/2}, 2^{1/2}] -- f = g * g^* supported in (1/2, 2),
    "so that rational primes are not involved" -- the prime-free
    regime, exactly up to L = log 2. Mechanism: the semi-local
    trace formula's Hilbert-space framework; the Sonin-space
    compression of the scaling action; prolate spheroidal wave
    functions; hermitian Toeplitz control of (Weil distribution
    minus Sonin trace). Their stated strategy sentence covers
    Support(f) in (p^{-1}, p) generally; the paper executes only
    the archimedean case.
  NUMERICAL, NOT PROVEN: Connes-Consani, "Spectral triples and
    zeta-cycles" (arXiv:2106.01715), section 2.2, verbatim: "the
    positivity is restored after that value, and precisely in the
    interval log 2 <= L < log 3, by implementing also the
    contribution of the prime p = 2, in terms of the related
    functional -W2" -- framed inside "The numerical tests consist
    in ..." with Figure 6; no theorem for L > log 2 anywhere in
    the swept record.
  THE SHARPENER (same paper, section 2.3, verbatim substance):
    "the computations show that the positivity of the quadratic
    form fails if one considers real values of p outside an
    interval of size < 10^-3 around 2." CONSEQUENCE FOR ANY
    PROOF: no p-insensitive estimate (no soft norm bound on the
    prime term) can possibly close the interval -- the argument
    must consume the arithmetic of 2 exactly. This matches the
    certified record's own measurements (1bf/1bg: PRIME/ARCH =
    -1 at 1e-8 -- the positivity lives inside a near-exact
    cancellation, 96% of the floor consumed at delta = 0.7).
  Adjacent prior art logged for the predictor's novelty scope:
    arXiv:2605.20224, "High-Precision Approximation of Riemann
    Zeros via the Truncated Weil Form" (May 2026) -- to be read
    before any predictor claim is called novel.

THE STAGED PLAN (each stage with its own kill):
  STAGE A -- THE BRIDGE (doubles as the consensus CCM-bridge
    item). Build the exact map between CC's quadratic form
    Q_W(g) on [n^{-1/2}, n^{1/2}]-supported g (their sigma+/-
    matrices in the eta_n basis) and this program's certified
    section margins (prolate basis, aperture A, the 1az/1bb
    machinery) -- same units, same normalization, agreement
    gated. Kill: a normalization mismatch that cannot be closed
    exposes which instrument convention diverges; either way the
    map is the deliverable.
  STAGE B1 -- THE CERTIFICATE ROUTE (T0-dependent theorem). For
    L < log 3 the form is ARCH + POLE - W2 with W2 a single
    translation-pair term. Unconditional-given-the-verified-
    zeros chain: Q_W(g) = sum over zeros (explicit formula,
    unconditional identity); on-line zeros (verified to T0 ~
    3x10^12) contribute |f_hat(gamma)|^2 >= 0 termwise; possible
    off-line zeros exist only above T0 and contribute terms
    bounded by shifted-Parseval mass (weight e^{|x|} <= e^{L/2}
    ~ 1.73 at L = log 3) against the archimedean density's
    log(T0/2pi) ~ 27.5 growth at those heights. The inequality
    to close, with explicit constants: pole + arch(above-T0
    floor) >= e^{L/2} x (worst-case off-line tail) on the
    unit-arch-mass class, PLUS the 2-adic cancellation handled
    exactly below T0. If the constants close (interval
    arithmetic where needed), the result is a theorem of the
    Turing-method epistemic class: Weil positivity for
    L < log 3, given the verified ordinate ledger. Kill: the
    constants do not close -- the gap size is then itself the
    finding (how much more verified height, or how much less
    support, closes it).
  STAGE B2 -- THE STRUCTURAL ROUTE (the prize; T0-free). Extend
    the CC Sonin-compression + Toeplitz control to the
    semi-local place set {infinity, 2}: the semi-local trace
    formula and the semi-local Sonin space exist (CCM
    arXiv:2310.18423 proves the Sonin-space stability under
    adding places); the missing piece is the Toeplitz-control
    step at {infinity, 2}. This is the field's own teed-up
    route; attempting it honestly means reading the CC proof at
    the level of its estimates first. Kill: the Toeplitz step's
    archimedean-specific ingredient (if any) is identified as
    non-transferable -- a finding worth recording precisely.

CHECKS. 7: classical throughout (explicit formula, Paley-Wiener,
Toeplitz/prolate theory, interval arithmetic; the CC machinery is
classical operator theory -- no semiclassics anywhere). 8: no
hypothesis input; the physics is nowhere in this arc. No RH
leverage claimed: L < log 3 is one prime's worth of the wall; the
dense-class extension remains RH, in neither direction.

This file is the arc's opening record; no computation yet (the
instruments arrive with Stage A). Sweep sources, for the record:
arxiv.org/abs/2006.13771 (+ Selecta 27:77), arxiv.org/abs/
2106.01715, arxiv.org/abs/2310.18423, arxiv.org/abs/2605.20224.
"""

if __name__ == "__main__":
    print(__doc__)
