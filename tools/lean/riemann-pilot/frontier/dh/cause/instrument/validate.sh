#!/usr/bin/env bash
# validate.sh -- the full validation battery of dh_census.py, on t <= 200 only (pre-registration).
# Usage: bash validate.sh [OUTDIR]     (default: ./validation)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$HERE/validation}"
mkdir -p "$OUT"
cd "$HERE"
cmp_line() {  # compact comparison of a test file against the reference
  python3 val_extra.py compare "$OUT/val_1_200.jsonl" "$1" | python3 -c '
import json, sys
d = json.load(sys.stdin)
print("  range", d["range"], " roots f/chi/chibar",
      [(d[k]["n"], d[k]["same"]) for k in ("roots_f", "roots_chi", "roots_chibar")],
      " offline", (d["offline"]["n"], d["offline"]["same"]), " flags", d["flags"])
print("  diag", d["diag_total"])'
}
echo "== self-test";            python3 dh_census.py --selftest | python3 -c 'import json,sys; d=json.load(sys.stdin); print(" ", {k: d[k] for k in ("theta_sign", "dirichlet_l_rel_diff")}, d["theta_sign=+1"], d["theta_sign=-1"]["pass"])'
echo "== reference census [1, 200], dt 25"
rm -f "$OUT/val_1_200.jsonl"
python3 dh_census.py --t0 1 --t1 200 --out "$OUT/val_1_200.jsonl" 2> "$OUT/val_1_200.log"
python3 dh_census.py --summary "$OUT/val_1_200.jsonl" > "$OUT/val_1_200.summary.json"
python3 - "$OUT/val_1_200.summary.json" <<'EOF'
import json, sys
s = json.load(open(sys.argv[1]))
exp = [(0.808517, 85.699348), (0.650830, 114.163343), (0.574356, 166.479306), (0.724258, 176.702461)]
off = sorted(s["offline"], key=lambda o: o[1])
print("  windows", s["windows"], "range", [s["T_start"], s["T_end"]], "N_f", s["N_f"], "N_chi", s["N_chi"],
      "N_chibar", s["N_chibar"], "on-line", s["online_roots"])
print("  accounting f/chi/chibar", s["accounting_f"], s["accounting_chi"], s["accounting_chibar"],
      " flagged windows", s["flagged_windows"], " continuity problems", s["continuity_problems"])
print("  self-test maxima: im %.2e  id %.2e (pass < 1)" % (s["max_selftest_im_ratio"], s["max_selftest_id_ratio"]))
ok = len(off) == 4 and all(abs(o[0] - e[0]) < 1e-6 and abs(o[1] - e[1]) < 1e-6 for o, e in zip(off, exp))
for o in off:
    print("  rho = %.9f + %.9f i   |f| = %.1e" % tuple(o))
print("  four expected zeros matched to 1e-6:", ok)
EOF
echo "== independent: argument principle for f around [1/2+delta, 2] x [1, 200]"
python3 val_extra.py rect --t0 1 --t1 200 --delta 0.001
python3 val_extra.py rect --t0 1 --t1 200 --delta 0.05
echo "== the strip (T1_last, 200] not covered by the shifted last end"
python3 val_extra.py tail "$OUT/val_1_200.jsonl"
echo "== channel roots against flint's dirichlet_l (max |L| or |f| at the roots)"
python3 val_extra.py dirl "$OUT/val_1_200.jsonl"
for m in fine coarse harsh harsh_nogolden nodips; do
  echo "== sabotage/variant: $m"
  rm -f "$OUT/$m.jsonl"; python3 val_extra.py run "$OUT/$m.jsonl" $m 2> "$OUT/$m.log"; cmp_line "$OUT/$m.jsonl"
done
for d in 10 50; do
  echo "== dt $d"
  rm -f "$OUT/dt$d.jsonl"; python3 dh_census.py --t0 1 --t1 200 --dt $d --out "$OUT/dt$d.jsonl" 2> "$OUT/dt$d.log"; cmp_line "$OUT/dt$d.jsonl"
done
echo "== resume: kill after ~1 s, append a torn line, resume"
rm -f "$OUT/resume.jsonl"
timeout 1.2 python3 dh_census.py --t0 1 --t1 200 --out "$OUT/resume.jsonl" 2>/dev/null || true
echo "  complete lines after kill: $(wc -l < "$OUT/resume.jsonl")"
printf '{"format":"dh_census/1","k":99,"T0":1' >> "$OUT/resume.jsonl"
python3 dh_census.py --t0 1 --t1 200 --out "$OUT/resume.jsonl" 2> "$OUT/resume.log"
python3 - "$OUT/val_1_200.jsonl" "$OUT/resume.jsonl" <<'EOF'
import json, sys
A = [json.loads(l) for l in open(sys.argv[1])]
B = [json.loads(l) for l in open(sys.argv[2])]
keys = ["T0", "T1", "Nf0", "Nf1", "Nchi0", "Nchi1", "Nchib0", "Nchib1", "roots_f", "roots_chi",
        "roots_chibar", "offline", "offline_hp", "K", "flags"]
print("  windows", len(A), len(B), " bitwise identical science fields:",
      len(A) == len(B) and all(a[k] == b[k] for a, b in zip(A, B) for k in keys),
      " resumed at", [b["startup"]["resumed_at_window"] for b in B if "startup" in b])
EOF
