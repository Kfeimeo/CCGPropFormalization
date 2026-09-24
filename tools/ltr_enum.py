#!/usr/bin/env python3
"""
Bounded enumerator for the left-to-right CCG audits.

Categories are tuples:  ('a', name) | ('/', X, Y) | ('\\', X, Y).
A rule set is a dict of flags.  All derivability questions are answered by bounded CKY
(categories with more than MAXSIZE nodes are discarded), so

  * a positive answer ("acceptable") is a genuine derivation;
  * a negative answer is only a bounded-negative (no derivation within the size bound).

Grammatical acceptability (the Lean `GrammAcceptable`): for every proper prefix [0,i) there is a
category P of the prefix (in the target system) that can be extended, using the suffix words in any
bracketing, to the goal.  This is computed as a left-spine chart `cont` seeded with chart[0][i].
"""
import itertools, sys, random
from functools import lru_cache

# ---------- categories ----------
def atom(x): return ('a', x)
def fwd(x, y): return ('/', x, y)
def bwd(x, y): return ('\\', x, y)
def slash(x, d, y): return (d, x, y)

def size(c):
    return 1 if c[0] == 'a' else 1 + size(c[1]) + size(c[2])

def show(c):
    if c[0] == 'a': return c[1]
    l = show(c[1]); r = show(c[2])
    if c[1][0] != 'a': l = '(' + l + ')'
    if c[2][0] != 'a': r = '(' + r + ')'
    return l + c[0] + r

def flatten(c):
    """head, slots innermost-first"""
    slots = []
    while c[0] != 'a':
        slots.append((c[0], c[2]))
        c = c[1]
    slots.reverse()
    return c, slots

def rebuild(h, slots):
    for d, a in slots:
        h = (d, h, a)
    return h

def is_transparent(c):
    return c[0] != 'a' and c[1] == c[2]

# ---------- binary rules ----------
def app(a, b):
    """FA/BA only"""
    out = set()
    if a[0] == '/' and a[2] == b: out.add(a[1])
    if b[0] == '\\' and b[2] == a: out.add(b[1])
    return out

def binary(a, b, R):
    out = set()
    # FA / BA
    if a[0] == '/' and a[2] == b: out.add(a[1])
    if b[0] == '\\' and b[2] == a: out.add(b[1])
    # generalized composition (any slashes in the spine => harmonic + crossed), n >= 1
    if R.get('comp'):
        harmonic = R.get('harmonic_only', False)
        if a[0] == '/':
            X, Y = a[1], a[2]
            h, sp = flatten(b)
            for m in range(len(sp)):
                if rebuild(h, sp[:m]) == Y and (not harmonic or all(d == '/' for d, _ in sp[m:])):
                    out.add(rebuild(X, sp[m:]))
        if b[0] == '\\':
            X, Y = b[1], b[2]
            h, sp = flatten(a)
            for m in range(len(sp)):
                if rebuild(h, sp[:m]) == Y and (not harmonic or all(d == '\\' for d, _ in sp[m:])):
                    out.add(rebuild(X, sp[m:]))
    # AC : X/Y, A => X/(Y\A)
    if R.get('ac') and a[0] == '/':
        out.add(fwd(a[1], bwd(a[2], b)))
    # GAC : X/Y, A|Zs => (X/(Y\A))|Zs   (A any head-prefix of the right spine)
    if R.get('gac') and a[0] == '/':
        h, sp = flatten(b)
        for m in range(len(sp) + 1):
            A = rebuild(h, sp[:m])
            out.add(rebuild(fwd(a[1], bwd(a[2], A)), sp[m:]))
    # D : X/(Y|Z), Y/W => X/(W|Z)
    if R.get('d') and a[0] == '/' and a[2][0] != 'a' and b[0] == '/':
        inner = a[2]
        if inner[1] == b[1]:
            out.add(fwd(a[1], slash(b[2], inner[0], inner[2])))
    # D_bwd (mirror of D) : X/(A\\B), Y\\B => X/(A\\Y)   (the argument is completed by backward composition)
    if R.get('dbwd') and a[0] == '/' and a[2][0] == '\\' and b[0] == '\\' and b[2] == a[2][2]:
        out.add(fwd(a[1], bwd(a[2][1], b[1])))
    # SA : delete one matching slot anywhere
    if R.get('sa'):
        h, sp = flatten(b)
        for k, (d, arg) in enumerate(sp):
            if d == '\\' and arg == a: out.add(rebuild(h, sp[:k] + sp[k+1:]))
        h, sp = flatten(a)
        for k, (d, arg) in enumerate(sp):
            if d == '/' and arg == b: out.add(rebuild(h, sp[:k] + sp[k+1:]))
    return out

# ---------- unary rules ----------
def unary(c, R):
    out = set()
    if R.get('asp'):
        h, sp = flatten(c)
        if len(sp) >= 2:
            for perm in itertools.permutations(sp):
                out.add(rebuild(h, list(perm)))
    for g in R.get('gtr', []):          # goal-targeted / S-targeted TR:  X => g/(g\X)
        if R.get('tr_no_nest') and c[0] == '/' and c[2][0] == '\\' and c[1] == c[2][1] and c[1] in R.get('gtr', []):
            continue                    # do not raise an already raised category
        out.add(fwd(g, bwd(g, c)))
    if R.get('tr_targets'):             # TR with a finite target pool, both directions
        for t in R['tr_targets']:
            out.add(fwd(t, bwd(t, c))); out.add(bwd(t, fwd(t, c)))
    if R.get('tr_lex'):                 # Steedman's order-preserving TR licensed by the lexicon:
        for L in R['tr_lex']:           #   X => T/(T\X) if T\X is lexical;  X => T\(T/X) if T/X is lexical
            if L[0] == '\\' and L[2] == c: out.add(fwd(L[1], L))
            if L[0] == '/' and L[2] == c: out.add(bwd(L[1], L))
    if R.get('asf'):
        h, sp = flatten(c)
        for k in range(len(sp) - 1):
            (d1, A), (d2, B) = sp[k], sp[k+1]
            if d1 == d2 == '\\':
                for C in app(A, B): out.add(rebuild(h, sp[:k] + [('\\', C)] + sp[k+2:]))
            if d1 == d2 == '/':
                for C in app(B, A): out.add(rebuild(h, sp[:k] + [('/', C)] + sp[k+2:]))
    return out

def closure(cats, R, maxsize):
    cats = {c for c in cats if size(c) <= maxsize}
    frontier = list(cats)
    while frontier:
        c = frontier.pop()
        for d in unary(c, R):
            if size(d) <= maxsize and d not in cats:
                cats.add(d); frontier.append(d)
    return cats

# ---------- charts ----------
def chart(words, R, maxsize):
    n = len(words)
    ch = {}
    for i in range(n):
        ch[(i, i+1)] = closure({words[i]}, R, maxsize)
    for length in range(2, n+1):
        for i in range(0, n-length+1):
            j = i + length
            acc = set()
            for k in range(i+1, j):
                for a in ch[(i, k)]:
                    for b in ch[(k, j)]:
                        acc |= binary(a, b, R)
            ch[(i, j)] = closure(acc, R, maxsize)
    return ch

ORIG = {'comp': True}                          # FA/BA + generalized composition, no unary rules
ORIG_HARMONIC = {'comp': True, 'harmonic_only': True}
APP = {}                                       # FA/BA only

def derivable(words, goal, R=ORIG, maxsize=30):
    return goal in chart(words, R, maxsize)[(0, len(words))]

def acceptable_prefix(words, goal, i, R, maxsize, ch=None):
    """∃ P ∈ chart[0,i) that continues (suffix in any bracketing) to goal"""
    n = len(words)
    if ch is None: ch = chart(words, R, maxsize)
    cont = {i: set(ch[(0, i)])}
    for k in range(i+1, n+1):
        acc = set()
        for j in range(i, k):
            for a in cont[j]:
                for d in ch[(j, k)]:
                    acc |= binary(a, d, R)
        cont[k] = closure(acc, R, maxsize)
    return goal in cont[n]

def acceptable(words, goal, R, maxsize=30):
    n = len(words)
    ch = chart(words, R, maxsize)
    bad = [i for i in range(1, n) if not acceptable_prefix(words, goal, i, R, maxsize, ch)]
    return bad   # list of failing prefixes (empty = grammatically acceptable)

# ---------- rule sets used in the audits ----------
S, NP, N, PP, SQ = atom('S'), atom('NP'), atom('N'), atom('PP'), atom('Sq')
def RS(**kw):
    R = {'comp': True}; R.update(kw); return R
SYSTEMS = {
    'noTR':        RS(),
    'appAsp':      {'asp': True},
    'appCompAsp':  RS(asp=True),
    'appAspAC':    {'asp': True, 'ac': True},
    'appCompAspAC':RS(asp=True, ac=True),
    'fullStrAC':   RS(asp=True, ac=True, gtr=[S]),
    'fullStrACASF':RS(asp=True, ac=True, gtr=[S], asf=True),
    'fullLTR':     RS(asp=True, ac=True, gtr=[S], d=True, gac=True),
}
def fullLTRg(goal): return RS(asp=True, ac=True, gtr=[goal], d=True, gac=True)
def fullLTRclause(goals): return RS(asp=True, ac=True, gtr=list(goals), d=True, gac=True, tr_no_nest=True)

def parse(s):
    """tiny parser: atoms are alnum, slashes / and \\, parentheses; left associative"""
    s = s.replace(' ', '')
    pos = 0
    def peek(): return s[pos] if pos < len(s) else ''
    def primary():
        nonlocal pos
        if peek() == '(':
            pos += 1; c = expr(); assert peek() == ')'; pos += 1; return c
        j = pos
        while pos < len(s) and (s[pos].isalnum() or s[pos] in "'_"): pos += 1
        return atom(s[j:pos])
    def expr():
        nonlocal pos
        c = primary()
        while peek() in ('/', '\\'):
            d = s[pos]; pos += 1
            c = (d, c, primary())
        return c
    c = expr(); assert pos == len(s), s
    return c

def sentence(*cats): return [parse(c) for c in cats]
