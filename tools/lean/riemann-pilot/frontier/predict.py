"""Round 36: out-of-sample predictions of the constrained-equilibrium model (rounds 33-34),
written down before the measurement.
For each delta: T_edge; the fronts T_pin(tau) for tau = 1e-1, 1e-3, 1e-6 (A = 1/(2 sigma(T_edge)));
the depth 2 Delta(0) and the predicted -log lam1 = 2 Delta(0) - offset. The offset is extrapolated
linearly from the in-sample values 4.0, 4.4, 4.6, 5.1, 5.6 at delta = 1, 1.2, 1.38, 1.6, 2."""
import sys, math, json
import numpy as np
from scipy.optimize import brentq
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import transition as TR, edge_model as E
ds_in = np.array([1.0, 1.2, 1.3828125, 1.6, 2.0]); off_in = np.array([3.96, 4.42, 4.61, 5.12, 5.64])
k, c = np.polyfit(ds_in, off_in, 1)
for d in map(float, sys.argv[1:]):
    a = d / 2; T, Delta, ys, up = TR.model(a)
    A = 1 / (2 * E.sig(T))
    fr = {}
    for tau in (1e-1, 1e-3, 1e-6):
        f = lambda x: 2 * Delta(x) - math.log(A / tau)
        fr[str(tau)] = brentq(f, 0, T * 0.99999) if f(0) > 0 else 0.0
    D0 = 2 * Delta(0.0); off = k * d + c
    print(json.dumps(dict(delta=d, T_edge=T, T_pin=fr, two_Delta0=D0, offset_extrap=off,
                          predicted_minus_log_lam=D0 - off, predicted_lam=math.exp(-(D0 - off)))))
    sys.stdout.flush()
