#!/usr/bin/env python3
"""Calibration against the machine-checked results of rounds 1-7."""
from ltr_enum import *

CASES = [
 # name, words, goal, system, expected failing prefixes (None = derivable-check only)
 ("R1 noTR  [X/Y, W, Y\\W]",         sentence('S/NP','N','NP\\N'),                 S, 'noTR',         [2]),
 ("R2 appAsp NP NP (S\\NP)\\NP",     sentence('NP','NP','(S\\NP)\\NP'),             S, 'appAsp',       [2]),
 ("R2 appCompAsp same",             sentence('NP','NP','(S\\NP)\\NP'),             S, 'appCompAsp',   [2]),
 ("R2 appAsp John likes Mary",      sentence('NP','(S\\NP)/NP','NP'),              S, 'appAsp',       []),
 ("R3 appAspAC NP NP verb",         sentence('NP','NP','(S\\NP)\\NP'),             S, 'appCompAspAC', [2]),
 ("R3 appAspAC S/S NP S\\NP",        sentence('S/S','NP','S\\NP'),                  S, 'appAspAC',     []),
 ("R3 appAspAC what John likes",    sentence('S/(S/NP)','NP','(S\\NP)/NP'),         S, 'appAspAC',     []),
 ("R4 fullStrAC NP NP verb",        sentence('NP','NP','(S\\NP)\\NP'),             S, 'fullStrAC',    []),
 ("R4 fullStrAC John likes Mary madly", sentence('NP','(S\\NP)/NP','NP','(S\\NP)\\(S\\NP)'), S, 'fullStrAC', [2]),
 ("R5 ASF John likes Mary madly",   sentence('NP','(S\\NP)/NP','NP','(S\\NP)\\(S\\NP)'), S, 'fullStrACASF', []),
 ("R5 ASF what apparently Mary likes", sentence('S/(S/NP)','S/S','NP','(S\\NP)/NP'), S, 'fullStrACASF', [2]),
 ("R7 fullLTR John the man likes",  sentence('NP','NP/N','N','(S\\NP)\\NP'),        S, 'fullLTR',      []),
 ("R7 fullStrAC John the man likes (no GAC)", sentence('NP','NP/N','N','(S\\NP)\\NP'), S, 'fullStrAC', [2]),
 ("R7 fullLTR Read Mary's book",    sentence('S/NP','NP','(NP/N)\\NP','N'),         S, 'fullLTR',      []),
 ("R7 fullLTR what apparently Mary likes", sentence('S/(S/NP)','S/S','NP','(S\\NP)/NP'), S, 'fullLTR', []),
 ("R7 fullLTR SOV question root Sq", sentence('NP','N','(Sq\\NP)\\N'),              SQ, 'fullLTR',     [2]),
 ("R7 fullLTRg(Sq) SOV question",   sentence('NP','N','(Sq\\NP)\\N'),              SQ, fullLTRg(SQ),  []),
]

ok = True
for name, words, goal, sysname, expect in CASES:
    R = SYSTEMS[sysname] if isinstance(sysname, str) else sysname
    der = derivable(words, goal, R, maxsize=24)   # full derivation in the target system
    bad = acceptable(words, goal, R, maxsize=24)
    match = der and ((bad == [] and expect == []) or (expect != [] and set(expect) <= set(bad)))
    status = 'OK ' if match else 'XX '
    if not match: ok = False
    print(f"{status}{name:48s} derivable={der} failing_prefixes={bad} expected={expect}")
print("ALL CALIBRATION CASES MATCH" if ok else "MISMATCH")
