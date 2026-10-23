import json, sys
r = json.load(open(sys.argv[1])); X = r['X']
r0 = r['rows'][0]; g0 = r0['log_g_over_Phi']; h0 = r0['log_heat_over_Phi']; q0 = r0['gauss_x_pred']
print('delta', r['delta'], 'X', round(X, 2))
for w in r['rows'][::int(sys.argv[2]) if len(sys.argv) > 2 else 3]:
    if w['log_g_over_Phi'] is None or w['log_heat_over_Phi'] is None:
        print(f"t={w['t']:.3f} x/X={w['x']/X:.3f}  (non-positive value)"); continue
    print(f"t={w['t']:.3f} x/X={w['x']/X:.3f} g:{w['log_g_over_Phi']-g0:+.3f} heat:{w['log_heat_over_Phi']-h0:+.3f} gauss_x:{w['gauss_x_pred']-q0:+.3f} rec_err={w['Phi_rec_relerr']:.0e} heat_tail={w['heat_last_term_rel']:.0e}")
