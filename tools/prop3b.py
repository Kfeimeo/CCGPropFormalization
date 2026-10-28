#!/usr/bin/env python3
"""Prop III: whole-sentence S-derivability, no left-to-right constraint.
Reference grammar G = standard CCG (FA/BA + Bn + lexically licensed T), two variants (with / without
crossed composition).  LTR system R = fullLTRs [S, Sq] (same two variants).
  completeness: G derives S => R derives S     soundness: R derives S => G derives S."""
import sys, itertools
from multiprocessing import Pool
from ltr_enum import *
from stdccg import CATS, GOALS
def H(R): R = dict(R); R['harmonic_only'] = True; return R
STD, LTR = {'comp': True, 'tr_lex': CATS}, fullLTRclause(GOALS)
PAIRS = {'crossed': (STD, LTR), 'harmonic': (H(STD), H(LTR))}
def check(words):
    out = []
    for g in GOALS:
        for v, (G, R) in PAIRS.items():
            a, b = derivable(words, g, G, 13), derivable(words, g, R, 13)
            if a != b: out.append((v + (': std-only (LTR incomplete)' if a else ': LTR-only (LTR unsound)'), tuple(show(w) for w in words), show(g)))
    return out
if __name__ == '__main__':
    L = int(sys.argv[1]); diff = []
    with Pool() as p:
        for n in range(2, L+1):
            for r in p.imap_unordered(check, (list(w) for w in itertools.product(CATS, repeat=n)), chunksize=100): diff.extend(r)
            print(f"length {n}: differences so far {len(diff)}", flush=True)
    by = {}
    for k, ws, g in diff: by.setdefault(k, []).append((ws, g))
    for k in sorted(by):
        v = sorted(by[k], key=lambda x: (len(x[0]), x)); print(f"{k}: {len(v)}"); [print("   ", e) for e in v[:8]]
