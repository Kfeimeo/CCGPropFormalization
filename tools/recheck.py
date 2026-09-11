from ltr_enum import *
FAILS = [
 (('NP','S/(S\\NP)','(S\\NP)\\NP','Sq\\S'),'Sq'),
 (('NP','S/(S\\NP)','Sq\\S','(S\\NP)\\NP'),'Sq'),
 (('N','S/NP','Sq\\S','NP\\N'),'Sq'),
 (('N','S/NP','NP\\N','Sq\\S'),'Sq'),
 (('NP/N','NP','(S\\NP)\\NP','N'),'S'),
 (('NP/N','NP','(Sq\\NP)\\NP','N'),'Sq'),
 (('S/NP','S/(S\\NP)','(S\\NP)\\S','NP'),'S'),
 (('NP/N','S/(S\\NP)','(S\\NP)\\NP','N'),'S'),
 (('NP/N','Sq/S','S\\NP','N'),'Sq'),
 (('N','(S/NP)/N','N','NP\\N'),'S'),
 (('S/(S/NP)','S/(S\\NP)','(S\\NP)\\S','S/NP'),'S'),
]
R = fullLTRclause([S, SQ])
for ws, g in FAILS:
    words = sentence(*ws); goal = parse(g)
    harm = derivable(words, goal, ORIG_HARMONIC, 20)
    bad = acceptable(words, goal, R, 22)
    print(f"{' '.join(ws):48s} goal={g}  harmonic-derivable={harm}  failing prefixes (targets S,Sq, size 22) = {bad}")
