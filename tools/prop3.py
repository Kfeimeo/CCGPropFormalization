#!/usr/bin/env python3
"""Prop III (soundness): sentences the extended system derives to S/Sq that FA/BA+Bn does not."""
import sys, itertools, time
from multiprocessing import Pool
from ltr_enum import *
from stdccg import LEX, CATS, GOALS
SYS = {'std-Tlex': {'comp': True, 'tr_lex': CATS},
       'std-Tlex-harmonic': {'comp': True, 'harmonic_only': True, 'tr_lex': CATS},
       'fullLTRclause': fullLTRclause(GOALS),
       'ASP-only': {'comp': True, 'asp': True}}
def check(words):
    out = []
    for g in GOALS:
        if derivable(words, g, ORIG, 13): continue
        for name, R in SYS.items():
            if derivable(words, g, R, 13): out.append((name, tuple(show(w) for w in words), show(g)))
    return out
if __name__ == '__main__':
    L = int(sys.argv[1]); over = []
    with Pool() as p:
        for n in range(2, L+1):
            for r in p.imap_unordered(check, (list(w) for w in itertools.product(CATS, repeat=n)), chunksize=100): over.extend(r)
            print(f"length {n}: overgenerated so far {len(over)}", flush=True)
    by = {}
    for nm, ws, g in over: by.setdefault(nm, []).append((ws, g))
    for nm in SYS:
        ex = sorted(by.get(nm, []), key=lambda x: (len(x[0]), x))
        print(f"{nm}: {len(ex)} overgenerated; e.g. {ex[:4]}")
