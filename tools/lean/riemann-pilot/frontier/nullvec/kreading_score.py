#!/usr/bin/env python3
"""Round 99: score PREREG_readingheight.md from r99_*.jsonl."""
import sys, json, numpy as np
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])      # load, spectrum, present, peaks
wt, Yt, rt = spectrum("r95_true.jsonl"); out = {"keep": {}, "drop": {}}
for m in ("keep", "drop"):
    for j in range(1, 11):
        w, Y, r = spectrum(f"r99_{m}_{j}.jsonl")
        out[m][j] = dict(band=[round(0.2*j, 1), round(0.2*j + 0.2, 1)], corr_true=round(float(np.corrcoef(r, rt)[0, 1]), 4),
                         rms_ratio=round(float(r.std()/rt.std()), 3), line_9_42=present(w, Y, 9.42)[0], peaks=peaks(w, Y, 3))
loss = {j: 1 - out["drop"][j]["corr_true"] for j in range(1, 11)}; rc = {j: 0.2*j + 0.1 for j in range(1, 11)}
rbar = sum(loss[j]*rc[j] for j in loss)/sum(loss.values()); jmax = max(loss, key=loss.get)
out.update(loss=loss, rbar=round(rbar, 4), largest_loss_band=out["drop"][jmax]["band"], RH_i=bool(1.03 <= rbar <= 1.13), RH_ii=bool(jmax == 5),
           RH=bool(1.03 <= rbar <= 1.13 and jmax == 5), implied_line_p2=round(float(rbar*4*np.pi*np.log(2)), 3))
for m in ("keep", "drop"):
    for j, v in out[m].items(): print(m, j, v)
for k in ("loss", "rbar", "largest_loss_band", "RH_i", "RH_ii", "RH", "implied_line_p2"): print(k, out[k])
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
