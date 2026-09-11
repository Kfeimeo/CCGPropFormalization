#!/usr/bin/env python3
"""Do Prop I (prefix reducibility) / Prop II (grammatical acceptability) hold when every
lexical category has at most k slashes (total, or forward only)?  Bounded enumeration."""
import sys, itertools, time
from multiprocessing import Pool
from ltr_enum import *

def all_cats(atoms, maxslash):
    by = {0: [atom(a) for a in atoms]}
    for n in range(1, maxslash + 1):
        by[n] = []
        for i in range(n):
            for x in by[i]:
                for y in by[n - 1 - i]:
                    by[n].append(fwd(x, y)); by[n].append(bwd(x, y))
    return [c for n in by for c in by[n]]

def nslash(c, kind):
    if c[0] == 'a': return 0
    return (1 if (kind == 'total' or c[0] == '/') else 0) + nslash(c[1], kind) + nslash(c[2], kind)

PROP1 = ['noTR', 'appAsp', 'appCompAsp', 'appAspAC', 'appCompAspAC']   # Prop I for STR systems is a Lean theorem (prefixReducible_fullStrAC)
PROP2 = ['fullStrAC', 'fullStrACASF', 'fullLTR', 'fullLTRclause']
MAXSIZE = 13
MAXSIZE_CHECK = 20
CFG = {}

def check(words):
    res = []
    for name in CFG['prop1']:
        R = SYSTEMS[name]
        ch = chart(words, R, MAXSIZE)
        if not ch[(0, len(words))]: continue
        bad = [i for i in range(1, len(words)) if not ch[(0, i)]]
        if bad:
            ch2 = chart(words, R, MAXSIZE_CHECK)
            bad = [i for i in bad if not ch2[(0, i)]]
            if not bad: continue
            Rh = dict(R); Rh['harmonic_only'] = True
            harm = bool(chart(words, Rh, MAXSIZE)[(0, len(words))])
            res.append(('I', name + ('/harm' if harm else '/crossed'), tuple(show(w) for w in words), bad))
    for name in CFG['prop2']:
        R = SYSTEMS[name] if name != 'fullLTRclause' else fullLTRclause([S])
        for src in ('orig', 'R'):
            if src == 'orig' and not derivable(words, S, ORIG, MAXSIZE): continue
            if src == 'R' and not derivable(words, S, R, MAXSIZE): continue
            bad = acceptable(words, S, R, MAXSIZE)
            if bad:
                bad = acceptable(words, S, R, MAXSIZE_CHECK)
                if not bad: continue
                harm = derivable(words, S, ORIG_HARMONIC, MAXSIZE)
                res.append(('II', name + '/' + src + ('/harm' if harm else '/crossed'), tuple(show(w) for w in words), bad))
    return res

def main(kind, k, atoms, maxlen, prop1=PROP1, prop2=PROP2):
    CFG['prop1'], CFG['prop2'] = prop1, prop2
    cats = [c for c in all_cats(atoms, max(k, 2)) if nslash(c, kind) <= k]   # total slashes <= max(k,2)
    print(f"kind={kind} k={k} atoms={atoms} lexicon={len(cats)} maxlen={maxlen}", flush=True)
    t0 = time.time(); fails = []
    with Pool() as pool:
        for L in range(2, maxlen + 1):
            seqs = (list(ws) for ws in itertools.product(cats, repeat=L))
            for r in pool.imap_unordered(check, seqs, chunksize=100):
                fails.extend(r)
            print(f"  length {L}: cumulative failures {len(fails)}  ({time.time()-t0:.0f}s)", flush=True)
    seen = {}
    for p, name, ws, bad in fails:
        seen.setdefault((p, name), []).append((ws, bad))
    for key in sorted(seen):
        ex = sorted(seen[key], key=lambda x: (len(x[0]), x[0]))
        print(f"{key[0]} {key[1]}: {len(ex)} failures; shortest: {ex[0][0]} failing prefixes {ex[0][1]}")
    keys = set(seen)
    print("Prop I, no failure at all:", [n for n in prop1 if not any(k[0]=='I' and k[1].startswith(n+'/') for k in keys)])
    print("Prop I, no failure among harmonic-derivable sentences:", [n for n in prop1 if ('I', n+'/harm') not in keys])
    print("Prop II, no failure at all:", [n+'/'+s for n in prop2 for s in ('orig','R') if not any(k[0]=='II' and k[1].startswith(n+'/'+s+'/') for k in keys)])
    print("Prop II, no failure among harmonic-derivable sentences:", [n+'/'+s for n in prop2 for s in ('orig','R') if ('II', n+'/'+s+'/harm') not in keys])

if __name__ == '__main__':
    kind, k, maxlen = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    atoms = sys.argv[4].split(',') if len(sys.argv) > 4 else ['S', 'NP', 'N']
    main(kind, k, atoms, maxlen)
