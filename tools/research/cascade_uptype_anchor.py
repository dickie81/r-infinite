#!/usr/bin/env python3
"""
The up-type absolute anchor: y_t = exp(-alpha(14)/chi^2).

Route: the top Yukawa.  Observed y_t = sqrt(2) m_t / v = 0.99119(167)
-- the famous 'top Yukawa ~ 1'.  In the session's machinery the bare
unit has a home: the variance theorem's V''_bare = 1 (the unfiltered
unit mode).  The claim: the Gen-3 up-type is the bare unit Yukawa,
filtered ONCE by the gauge-window member at k = 2:

    y_t = exp(-alpha(14)/chi^2)  =>  m_t = (v/sqrt(2)) e^(-alpha(14)/4)

Flag consistency: the up-type selection happens AT the gauge window
(Addendum 20), so the filter is Gauge-class (source d_gw = 14); the
channel-count rule (part4b rem:theta23-channel-count) gives k = 2 for
a one-Bott-period path -- the same k as theta_C.  Exclusion scan: the
needed exponent -0.008854(168) admits exactly one grid member within
1 sigma; nearest alternatives at +/-1.4 sigma.

Two traps defused below: (A) the cascade-v error-cancellation mirage
(y_t = 1 bare with the cascade's own -1.0%-residual v lands at -0.15%
by TWO ERRORS CANCELLING -- rejected, not celebrated); (B) the charm
strain: the chain c = t/(N_c b/s) meets the precise PDG m_c(m_c) =
1.2730(46) at +2.8 sigma -- the t/c relation is scheme-sensitive
(m_c convention) and may need its own unresolved correction; reported
as a strain, not hidden.

Gen-1 refusal maintained: u and d remain outside the crossing pattern.
"""

import math

SQRTPI = math.sqrt(math.pi)
V_GF = 246.2196            # (sqrt(2) G_F)^(-1/2), GeV
MT, SMT = 172.57, 0.29     # PDG top mass


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def main():
    yt_obs = math.sqrt(2) * MT / V_GF
    syt = yt_obs * SMT / MT
    need = math.log(yt_obs)
    print("=" * 74)
    print("PART A: the observed top Yukawa and the mirage")
    print("=" * 74)
    print(f"  y_t = sqrt(2) m_t / v = {yt_obs:.5f} +/- {syt:.5f}"
          f"   (ln y_t = {need:+.6f})")
    print(f"  bare y_t = 1 vs observed: {(1-yt_obs)/syt:+.1f} sigma -- NOT")
    print(f"  a closure.  Mirage check: cascade v (-1.0% residual, 243.7)")
    print(f"  with bare y_t = 1 gives m_t = {243.7/math.sqrt(2):.1f} GeV"
          f" (-0.15% 'match'):")
    print(f"  two ~1% errors cancelling.  Rejected.")

    print()
    print("=" * 74)
    print("PART B: exclusion scan for the Yukawa filter")
    print("=" * 74)
    cands = [("-alpha(14)/chi^2  [Gauge, k=2]", -alpha(14) / 4),
             ("-alpha(19)/chi^2", -alpha(19) / 4),
             ("-alpha(5)/chi^3", -alpha(5) / 8),
             ("-alpha(14)/chi^3", -alpha(14) / 8),
             ("-alpha(7)/chi^2", -alpha(7) / 4),
             ("-alpha(19)/chi", -alpha(19) / 2)]
    for lab, v in cands:
        print(f"  {lab:<32} {v:+.6f}  ({(v-need)/syt:+5.2f} sigma)")
    print("  => exactly one member within 1 sigma; flag-consistent (the")
    print("     selection is gauge-window-resident: Gauge class) and")
    print("     channel-consistent (one Bott period: k = 2, as theta_C).")

    print()
    print("=" * 74)
    print("PART C: the anchor and the spectrum it generates")
    print("=" * 74)
    mt_pred = (V_GF / math.sqrt(2)) * math.exp(-alpha(14) / 4)
    print(f"  m_t = (v/sqrt(2)) e^(-alpha(14)/4) = {mt_pred:.2f} GeV"
          f"   (obs {MT} +/- {SMT}: {(mt_pred-MT)/SMT:+.2f} sigma)")
    # b/s closed (Addendum 13 form)
    from scipy.special import digamma
    Phi = sum(0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)
              for d in range(6, 14))
    bs = math.exp(Phi) * 2 * SQRTPI * math.e * math.exp(-alpha(7) / 16)
    c_pred = mt_pred / (3 * bs)
    print(f"  c = t/(N_c (b/s)) = {c_pred:.4f} GeV")
    print(f"    vs m_c(m_c) = 1.2730 +/- 0.0046:"
          f" {(c_pred-1.2730)/0.0046:+.1f} sigma  ** STRAIN **")
    print(f"    vs looser m_c = 1.27 +/- 0.02: {(c_pred-1.27)/0.02:+.1f} sigma")
    print("  the strain is scheme-sensitive (m_c convention; the Addendum 19")
    print("  caveat with force) and may signal a missing correction on the")
    print("  t/c relation.  Reported, not hidden.")

    print()
    print("  ledger: t anchored (+0.14 sigma, robust vs G_F and m_t);")
    print("  c strained (+2.8 sigma vs precise m_c); u, d refused (Gen-1")
    print("  outside the crossing pattern).  Residuals named: the doublet-")
    print("  assignment lemma; the t/c correction assignment; the scheme.")


if __name__ == "__main__":
    main()
