#!/bin/sh
# worker j of 4 over x = 12 + 0.12 i (i = 0..150): response, true chain, Gamma chain
J=$1; XS=$(python3 -c "print(' '.join(str(round(12+0.12*i,4)) for i in range($J,151,4)))")
python3 klinresp3.py 2500 pzeros_0_2500.json true=true 15 $XS > r105B_resp_$J.jsonl 2> r105B_resp_$J.err
python3 kzeroside2.py true 2500 15 $XS > r105B_true_$J.jsonl 2> r105B_true_$J.err
python3 kzeroside2.py pzeros_0_2500.json 2500 15 $XS > r105B_base_$J.jsonl 2> r105B_base_$J.err
