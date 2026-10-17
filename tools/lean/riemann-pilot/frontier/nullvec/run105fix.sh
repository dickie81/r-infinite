#!/bin/sh
J=$1
XA=$(python3 -c "print(' '.join(str(round(3+0.04*i,4)) for i in range($J,226,4)))")
python3 klinresp3.py 1000 pzeros_0.json true=true,P7=pzeros_7.json 15 $XA > r105A_$J.jsonl 2> r105A_$J.err
XB=$(python3 -c "print(' '.join(str(round(12+0.12*i,4)) for i in range($J,151,4)))")
python3 klinresp3.py 2500 pzeros_0_2500.json true=true 15 $XB > r105B_resp_$J.jsonl 2> r105B_resp_$J.err
