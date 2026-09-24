#!/usr/bin/env python3
"""Standard CCG (FA/BA + generalized harmonic/crossed composition + order-preserving type raising),
read left to right: do Prop I (prefix reducibility) and Prop II (grammatical acceptability) hold?
Two versions of T:  tr_lex  = X => T/(T\\X) only if T\\X is a lexical category (and mirror image);
                    tr_any  = T ranges over a finite pool of categories (bounded approximation of unrestricted T)."""
import sys, itertools, time
from multiprocessing import Pool
from ltr_enum import *
from scan import LEX as SCAN_LEX

LEX = SCAN_LEX + ['(S\\NP)\\(S\\NP)', 'S/S', 'S\\S', '(S\\NP)/(S\\NP)', 'Sq\\NP']
CATS = [parse(c) for c in LEX]
GOALS = [S, SQ]
POOL = [parse(c) for c in ['S', 'NP', 'N', 'Sq', 'PP', 'S\\NP', 'S/NP', 'S\\S', 'S/S', 'N\\N', 'N/N', 'NP\\NP', 'NP/NP', 'Sq\\S', 'Sq/S', '(S\\NP)\\(S\\NP)', '(S\\NP)/NP']]
STD_LEX = {'comp': True, 'tr_lex': CATS}
STD_ANY = {'comp': True, 'tr_targets': POOL}
MAXSIZE, MAXSIZE_CHECK = 13, 18

CASES = [
 ("what John likes",            ['S/(S/NP)', 'NP', '(S\\NP)/NP'], S),
 ("John likes Mary",            ['NP', '(S\\NP)/NP', 'NP'], S),
 ("John likes Mary madly",      ['NP', '(S\\NP)/NP', 'NP', '(S\\NP)\\(S\\NP)'], S),
 ("SOV: NP NP (S\\NP)\\NP",      ['NP', 'NP', '(S\\NP)\\NP'], S),
 ("what apparently Mary likes", ['S/(S/NP)', 'S/S', 'NP', '(S\\NP)/NP'], S),
 ("SOV question, root Sq",      ['NP', 'PP', '(Sq\\NP)\\PP'], SQ),
 ("heavy NP shift",             ['NP', '(S\\NP)/NP', '((S\\NP)\\(S\\NP))/NP', 'NP', 'NP'], S),
 ("determiner: NP NP/N N (S\\NP)\\NP", ['NP', 'NP/N', 'N', '(S\\NP)\\NP'], S),
 ("possessive: S/NP NP (NP/N)\\NP N", ['S/NP', 'NP', '(NP/N)\\NP', 'N'], S),
 ("relative clause",            ['NP/N', 'N', '(N\\N)/(S/NP)', 'NP', '(S\\NP)/NP', 'S\\NP'], S),
]

def props(words, goal, R, maxsize):
    ch = chart(words, R, maxsize)
    der = goal in ch[(0, len(words))]
    p1 = [i for i in range(1, len(words)) if not ch[(0, i)]]
    p2 = [i for i in range(1, len(words)) if not acceptable_prefix(words, goal, i, R, maxsize, ch)] if der else None
    return der, p1, p2

def cases():
    for name, ws, goal in CASES:
        words = [parse(w) for w in ws]
        line = f"{name:36s}"
        for rname, R, ms in [('T-lex', {'comp': True, 'tr_lex': CATS + words}, MAXSIZE_CHECK), ('T-any', STD_ANY, 12)]:
            if sys.argv[2:] and rname not in sys.argv[2:]: continue
            der, p1, p2 = props(words, goal, R, ms)
            line += f" | {rname}: derivable={der} PropI-bad={p1} PropII-bad={p2}"
        print(line, flush=True)

def check(words):
    out = []
    R = STD_LEX
    ch = chart(words, R, MAXSIZE)
    if ch[(0, len(words))]:
        p1 = [i for i in range(1, len(words)) if not ch[(0, i)]]
        if p1:
            ch2 = chart(words, R, MAXSIZE_CHECK)
            p1 = [i for i in p1 if not ch2[(0, i)]]
            sent = any(g in ch2[(0, len(words))] for g in GOALS)
            if p1: out.append(('I/sentence' if sent else 'I/any-root', tuple(show(w) for w in words), p1))
    for goal in GOALS:
        if not derivable(words, goal, ORIG, MAXSIZE): continue
        bad = acceptable(words, goal, R, MAXSIZE)
        if bad:
            bad = acceptable(words, goal, R, MAXSIZE_CHECK)
            if bad:
                harm = derivable(words, goal, ORIG_HARMONIC, MAXSIZE)
                out.append(('II' + ('/harm' if harm else '/crossed'), tuple(show(w) for w in words), show(goal), bad))
    return out

def scan(maxlen):
    t0 = time.time(); fails = []
    with Pool() as pool:
        for L in range(2, maxlen + 1):
            for r in pool.imap_unordered(check, (list(ws) for ws in itertools.product(CATS, repeat=L)), chunksize=100):
                fails.extend(r)
            print(f"length {L}: cumulative failures {len(fails)} ({time.time()-t0:.0f}s)", flush=True)
    by = {}
    for f in fails: by.setdefault(f[0], []).append(f[1:])
    for k in sorted(by):
        ex = sorted(by[k], key=lambda x: (len(x[0]), x))
        print(f"{k}: {len(ex)} failures; shortest {ex[0]}")
        for e in ex[:8]: print("   ", e)

if __name__ == '__main__':
    if sys.argv[1] == 'cases': cases()
    else: scan(int(sys.argv[1]))
