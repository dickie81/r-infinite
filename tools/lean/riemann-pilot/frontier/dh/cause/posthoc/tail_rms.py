#!/usr/bin/env python3
"""Post-hoc: the size of the inert primes above a cutoff X in log R at sigma, in the random-phase approximation:
log R - log P_X = sum over inert p > X of log((1 + chi(p)p^-s)/(1 - chi(p)p^-s)) ~ 2 sum chi(p) p^-s, whose root mean
square over independent uniform phases is 2 sqrt(S0), S0 = sum over inert p > X of p^(-2 sigma) (sieve to 2e7, then the
inert primes' density 1/(2 log u)); each of Re and Im has standard deviation sqrt(2 S0).
Usage: tail_rms.py"""
import math
import numpy as np
from scipy.special import exp1
Y = 20_000_000
s = np.ones(Y + 1, dtype=bool); s[:2] = False
for i in range(2, int(Y**0.5) + 1):
    if s[i]: s[i*i::i] = False
pr = np.nonzero(s)[0]; inert = pr[(pr % 5 == 2) | (pr % 5 == 3)].astype(float)
for X, sig in ((100_000, 0.6), (100_000, 0.8), (3000, 0.8), (3000, 0.85)):
    S0 = float(np.sum(inert[inert > X]**(-2*sig))) + 0.5*exp1((2*sig - 1)*math.log(Y))
    print(f'X = {X:>6}, sigma = {sig}: S0 = {S0:.3e}   rms |change in log R| = {2*math.sqrt(S0):.4f}   '
          f'sd of Re, Im = {math.sqrt(2*S0):.4f}')
