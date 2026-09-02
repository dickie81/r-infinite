"""THE UNCERTAINTY PRINCIPLE, MEASURED (owner: "Search out the uncertainty
principle"; Addendum 423). A research probe -- not a tower member, not cited
by the paper; float64; nothing certified. On the prime side (no zeros anywhere), for the full form's ground
state g at support delta (both parities):
  * the balance  lambda_1 = A(g) + Pi(g) - P(g): archimedean, pole, primes;
  * the Fourier profile |ghat(r)|^2 (normalised to (1/2pi) int = 1) and its
    mass on the NEGATIVE SET N_delta = {r : W_delta(r) < 0} of the kernel, and
    on the central well [-r0, r0];
  * the SLEPIAN CAPS: the largest fraction of the mass of a Paley-Wiener
    function of type a = delta/2 that can sit on [-r0, r0] (lambda_0(a r0))
    and on the whole negative set N_delta (the top eigenvalue of the
    concentration operator restricted to N_delta, Nystrom);
  * the WELL DEFICIT  D = (1/2pi) int_N |ghat|^2 |W| dr  and how it is repaid:
    by the pole term Pi(g) and by the positive kernel region.
The uncertainty principle a proof needs is the inequality  A + Pi - P >= 0 for
every PW_a probe; this measures how the minimiser sits against the caps.
Scratch research probe, float64, twoprime_recon's operator via tile_tightness.
"""
import sys, os, math, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import digamma
import twoprime_recon as R
from tile_tightness import term, LOG2, LOG3, LOG4

def terms_for(delta):
    ts = []
    for n in (2, 3, 4, 5, 7, 8, 9):
        if math.log(n) < delta:
            p = {2: 2, 3: 3, 4: 2, 5: 5, 7: 7, 8: 2, 9: 3}[n]
            ts.append((math.log(n), 2.0*math.log(p)/math.sqrt(n)))
    return ts

def W_delta(r, ts):
    r = np.asarray(r, float)
    out = digamma(0.25 + 0.5j*r).real - math.log(math.pi)
    for lag, w in ts:
        out = out - w*np.cos(r*lag)
    return out

def components(md, ts, base):
    """arch-only TB, the prime TBs, and the pole rank-one, on one grid."""
    a, parity = md.a, md.parity
    kinks = tuple(sorted({min(max(lag - a, 0.0), a) for lag, w in ts}))
    tn, tw = R.gl_panels(0.0, a, sing=kinks + (a,), base=base)
    B = md.t_eval(tn)
    TA = -R.LG4PI*B.copy()
    f = np.cos if parity == "even" else np.sin
    for k, t in enumerate(tn):
        bt = B[:, k]; acc = np.zeros(md.n)
        for lo, hi, sing in (((0.0, a - t, (a - t,))), ((a - t, a + t, (a - t, a + t)))):
            u, wu = R.gl_panels(lo, hi, sing=sing, base=base)
            if len(u) == 0: continue
            A = (np.exp(u/2) - 1)/np.sinh(u)
            both_in = (t + u <= a) & (t - u >= -a)
            Bp = md.t_eval(t + u); Bm = md.t_eval(t - u)
            Dfull = (Bp + Bm)/2 - bt[:, None]
            Dh = -2*f(md.w[:, None]*t)*np.sin(md.w[:, None]*u[None, :]/2)**2
            D = np.where(both_in[None, :], np.vstack([Dh, Dfull[md.nharm:]]), Dfull)
            acc += bt*np.sum(A*wu)
            acc += (D*(np.exp(u/2)/np.sinh(u)*wu)[None, :]).sum(1)
        TA[:, k] -= acc
        TA[:, k] += bt*math.log(1.0/math.tanh((a + t)/2))
    TP = np.zeros_like(TA)
    for lag, w in ts:
        TP += -(w/2)*(md.t_eval(tn + lag) + md.t_eval(tn - lag))
    chi = (np.cosh(tn/2) if parity == "even" else np.sinh(tn/2))
    v = 2*(B*(tw*chi)[None, :]).sum(1)
    TPi = R.psign(parity)*2*np.outer(v, chi)
    return tn, tw, B, TA, TP, TPi

def slepian_cap_set(a, pieces, M=60):
    """Top eigenvalue of the concentration operator of PW_a on the union of
    symmetric intervals {|r| in [lo, hi]}: Nystrom with GL nodes per piece."""
    xs, ws = [], []
    x0, w0 = np.polynomial.legendre.leggauss(M)
    for lo, hi in pieces:
        if lo == 0.0:
            ivs = [(-hi, hi)]
        else:
            ivs = [(lo, hi), (-hi, -lo)]
        for l, h in ivs:
            xs.append(0.5*(h - l)*x0 + 0.5*(h + l)); ws.append(0.5*(h - l)*w0)
    x = np.concatenate(xs); w = np.concatenate(ws)
    D = x[:, None] - x[None, :]
    K = np.where(np.abs(D) < 1e-14, a/math.pi, np.sin(a*D)/(math.pi*np.where(np.abs(D) < 1e-14, 1.0, D)))
    A = np.sqrt(w)[:, None]*K*np.sqrt(w)[None, :]
    return float(np.linalg.eigvalsh((A + A.T)/2)[-1])

def negative_set(ts, rmax=80.0, h=0.002):
    r = np.arange(0.0, rmax, h); W = W_delta(r, ts)
    neg = W < 0; pieces = []; i = 0
    while i < len(r):
        if neg[i]:
            j = i
            while j < len(r) and neg[j]: j += 1
            pieces.append((float(r[i]), float(r[min(j, len(r)-1)]))); i = j
        else: i += 1
    return pieces, float(W.min())

def anatomy(delta, parity, base=0.012):
    a = delta/2; ts = terms_for(delta)
    md = R.Modes(a, parity)
    tn, tw, B, TA, TP, TPi = components(md, ts, base)
    N = 2*(B*tw[None, :]) @ B.T
    d = 1.0/np.sqrt(np.diag(N)); ev, U = np.linalg.eigh(d[:, None]*N*d[None, :]); keep = ev > 1e-4
    Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T*d[None, :]); Bw = Wh @ B
    NA = 2*(Bw*tw[None, :]) @ Bw.T; NA = (NA + NA.T)/2
    def M(T):
        Tw = Wh @ T; MA = 2*(Bw*tw[None, :]) @ Tw.T; return (MA + MA.T)/2
    MA, MP, MPi = M(TA), M(TP), M(TPi)
    lam, vec = R.scipy_eigh(MA + MP + MPi, NA)
    c = vec[:, 0]; nn = float(c @ NA @ c)
    Aq, Pq, Piq = (float(c @ X @ c)/nn for X in (MA, MP, MPi))
    # Fourier profile of g on [-a, a] (parity-extended): ghat(r) = 2 int_0^a g(t) cos/sin(rt) dt
    craw = Wh.T @ c
    tq, wq = np.polynomial.legendre.leggauss(400); tq = 0.5*a*(tq + 1); wq = 0.5*a*wq
    g = craw @ md.t_eval(tq)
    r = np.arange(0.0, 80.0, 0.01)
    if parity == "even":
        gh = 2*(np.cos(np.outer(r, tq)) @ (g*wq))
    else:
        gh = 2*(np.sin(np.outer(r, tq)) @ (g*wq))
    prof = gh**2/(2*math.pi)/nn*2          # both signs of r; (1/2pi) int_-inf^inf |ghat|^2 = 1 (up to the tail beyond 80)
    total = float(np.trapezoid(prof, r))
    W = W_delta(r, ts)
    pieces, wmin = negative_set(ts)
    inN = W < 0
    mass_N = float(np.trapezoid(np.where(inN, prof, 0.0), r))
    deficit = float(np.trapezoid(np.where(inN, prof*(-W), 0.0), r))
    surplus = float(np.trapezoid(np.where(~inN, prof*W, 0.0), r))
    r0 = pieces[0][1] if pieces and pieces[0][0] == 0.0 else 0.0
    mass_well = float(np.trapezoid(np.where(r <= r0, prof, 0.0), r))
    cap_well = slepian_cap_set(a, [(0.0, r0)]) if r0 > 0 else 0.0
    cap_N = slepian_cap_set(a, pieces) if pieces else 0.0
    return dict(delta=delta, parity=parity, lam1=float(lam[0]), lam2=float(lam[1]), A=Aq, P=Pq, Pi=Piq,
                check=Aq + Pq + Piq, wmin=wmin, r0=r0, pieces=pieces, mass_total80=total,
                mass_well=mass_well, cap_well=cap_well, mass_N=mass_N, cap_N=cap_N,
                deficit=deficit, surplus=surplus, edge2=float((craw @ md.t_eval(np.array([a]))[:, 0])**2/nn))

if __name__ == "__main__":
    base = float(sys.argv[1]) if len(sys.argv) > 1 else 0.012
    deltas = [float(s) for s in sys.argv[2:]] or [0.3, 0.5, 0.6, 0.69, 0.8, 0.9, 1.0, 1.09, 1.2, 1.3, 1.38]
    out = []
    print("delta par | lam1 | A(arch) Pi(pole) P(primes) [A+Pi+P] | Wmin r0 | mass well/cap  mass N/cap | deficit surplus | edge2", flush=True)
    for d in deltas:
        for par in ("even", "odd"):
            t0 = time.time(); r = anatomy(d, par, base); out.append(r)
            print(f"{d:5.2f} {par:4s} | {r['lam1']:+.3e} | {r['A']:+.4f} {r['Pi']:+.4f} {r['P']:+.4f} [{r['check']:+.3e}] | {r['wmin']:+.2f} {r['r0']:5.2f} | "
                  f"{r['mass_well']:.4f}/{r['cap_well']:.4f} {r['mass_N']:.4f}/{r['cap_N']:.4f} | {r['deficit']:.4f} {r['surplus']:.4f} | {r['edge2']:.2e}  ({time.time()-t0:.0f}s)", flush=True)
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'checkpoints', f'uncertainty_anatomy_base{base}.json'), 'w'), indent=1)
    print("done", flush=True)
