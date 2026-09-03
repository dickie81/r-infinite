"""Finite-delta balayage formula (Addendum 442).  With the zeta zeros discrete, the fixed part of the
zero-deviation measure is sigma_0 = sum_{0<gamma<T} (delta_gamma + delta_{-gamma}) - (a/pi) dt on [-T, T];
its balayage onto E = {|x| >= T} gives the exterior potential
    s_delta(T) = int g_Omega(t, 0) d sigma_0 = 2 sum_{gamma<T} g_T(gamma) - a T,
    g_T(t) = ln[(1 + sqrt(1 - t^2/T^2)) T / t]   (Green function of the doubly slit plane, pole 0),
using (a/pi) * 2 int_0^T g_T = (a/pi) T pi = a T.  Prediction:  ln lambda_1 = min_T 2 s_delta(T) + O(log).
Continuum limit: 2 s_delta -> -4 pi e^delta at T = 2 T0.  This script evaluates the formula on a T grid at
each delta and compares with the exact zero-side values.
Usage: discrete_balayage.py [delta ...]"""
import sys, os, json, math, numpy as np
ZEROS = np.array([float(z) for z in json.load(open(os.environ.get("CASCADE_ZEROS", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkpoints", "zeta_zeros_2000.json"))))])
EXACT = {1.0: -13.883, 1.3828125: -27.759, 2.0: -67.334, 2.3: -98.327, 2.6: -140.776, 3.0: -221.946, 3.5: -383.223, 3.75: -496.128, 4.0: -637.893}

def s_delta(delta, T):
    a = delta/2; z = ZEROS[ZEROS < T]
    return 2*np.sum(np.log((1 + np.sqrt(1 - z*z/(T*T)))*T/z)) - a*T

def best(delta, xs=np.linspace(1.2, 3.0, 361)):
    T0 = 2*math.pi*math.exp(delta)
    vals = [(2*s_delta(delta, x*T0), x) for x in xs]
    return min(vals)          # lambda_1 is the MINIMUM over probes: the prediction is min_T 2 s_delta(T)

if __name__ == "__main__":
    ds = [float(v) for v in sys.argv[1:]] or sorted(EXACT)
    print(f"{'delta':>7} {'T*/T0':>6} {'2 s_delta(T*)':>14} {'exact ln lambda_1':>17} {'offset':>8} {'offset/delta':>12} | {'-4 pi e^delta':>13} {'f_pred':>7} {'f_exact':>8}")
    for d in ds:
        v, x = best(d); ex = EXACT.get(d); ed = math.exp(d)
        print(f"{d:7.4f} {x:6.3f} {v:14.3f} {ex if ex is not None else float('nan'):17.3f} {ex - v if ex is not None else float('nan'):8.3f} {(ex - v)/d if ex is not None else float('nan'):12.3f} | {-4*math.pi*ed:13.2f} {-v/ed:7.3f} {-ex/ed if ex is not None else float('nan'):8.3f}")
    print("continuum check: -2 s(T)/e^delta at delta = 8, T = 2 T0 (needs zeros to 2 T0 = 37,000: beyond the list) -- instead the closed form 2 pi X (1 + ln 2 - ln X) at X = 2 is 4 pi = 12.566")
