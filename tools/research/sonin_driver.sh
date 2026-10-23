#!/bin/bash
# 1bd harvest driver: four independent resumable passes in parallel,
# then the merged report. Run under run_with_checkpoints.sh.
set -u
cd /home/user/r-infinite
python3 tools/research/sonin_shoot_ck.py 1 even &
python3 tools/research/sonin_shoot_ck.py 1 odd &
python3 tools/research/sonin_shoot_ck.py s2 even &
python3 tools/research/sonin_shoot_ck.py s2 odd &
wait
python3 tools/research/sonin_shoot_ck.py
