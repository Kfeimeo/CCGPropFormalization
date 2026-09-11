#!/usr/bin/env python3
"""Scan the GTR system (FA/BA + Bn + ASP + AC + GTR + D + GAC) for grammatical-acceptability
counterexamples over a natural, TMA-compliant lexicon."""
import sys, itertools, time
from multiprocessing import Pool
from ltr_enum import *

LEX = [
 'NP', 'N', 'PP',
 'S\\NP', '(S\\NP)/NP', '(S\\NP)\\NP', 'S/NP', 'NP/N', '(NP/N)\\NP', '(S\\NP)/S', '(S\\NP)\\S',
 '(N\\N)/(S/NP)', '(N\\N)/(S\\NP)', 'S/(S/NP)', 'S/(S\\NP)', '(S\\NP)/PP', 'PP/NP', 'PP\\NP',
 '((S\\NP)/NP)/NP', '((S\\NP)\\NP)\\NP', '(Sq\\NP)\\NP', '(Sq\\NP)/NP', 'Sq\\S', 'Sq/S',
 '((S\\NP)\\NP)/(S\\NP)', '(S/NP)/N', 'NP\\N',
]
CATS = [parse(c) for c in LEX]
assert not any(is_transparent(c) for c in CATS)
GOALS = [S, SQ]
MAXSIZE_SCAN = 15
MAXSIZE_CHECK = 22

def check(words):
    out = []
    nder = 0
    for goal in GOALS:
        if not derivable(words, goal, ORIG, MAXSIZE_SCAN):
            continue
        nder += 1
        R = fullLTRclause(GOALS)          # TR targets: all clause-type atoms
        bad = acceptable(words, goal, R, MAXSIZE_SCAN)
        if bad:
            bad2 = acceptable(words, goal, R, MAXSIZE_CHECK)   # re-check with a larger bound
            harm = derivable(words, goal, ORIG_HARMONIC, MAXSIZE_SCAN)
            out.append((tuple(show(w) for w in words), show(goal), bad, bad2, 'harmonic-derivable' if harm else 'NEEDS-CROSSED'))
    return nder, out

def main(maxlen):
    t0 = time.time()
    total = 0; derivable_count = 0; failures = []
    with Pool() as pool:
        for L in range(2, maxlen + 1):
            seqs = (list(ws) for ws in itertools.product(CATS, repeat=L))
            for nder, res in pool.imap_unordered(check, seqs, chunksize=200):
                total += 1; derivable_count += nder
                failures.extend(res)
            print(f"length {L} done, cumulative sequences {total}, derivable (seq,goal) pairs {derivable_count}, failures so far {len(failures)}, {time.time()-t0:.0f}s", flush=True)
    print(f"\n=== bounded failures (words, goal, failing prefixes @{MAXSIZE_SCAN}, failing prefixes @{MAXSIZE_CHECK}) ===")
    for f in failures:
        print(f)
    print(f"total failures: {len(failures)}; robust (also fail @{MAXSIZE_CHECK}): {sum(1 for f in failures if f[3])}")

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
