# Length-3, two-slash, harmonic-only Prop II check of fullLTR (+ mirror D when R["dbwd"] is set); run from tools/
import itertools
from multiprocessing import Pool
from slashbound import *
cats=[c for c in all_cats(['S','NP'],2)]
R=dict(SYSTEMS['fullLTR']); R['dbwd']=True
def chk(ws):
    if not derivable(ws,S,ORIG_HARMONIC,13): return None
    bad=acceptable(ws,S,R,13)
    if bad and acceptable(ws,S,R,20): return (tuple(show(w) for w in ws), bad)
    return None
if __name__=='__main__':
    with Pool(2) as p:
        res=[r for r in p.imap_unordered(chk,(list(w) for w in itertools.product(cats,repeat=3)),chunksize=200) if r]
    def has_bwd_over_fwd(c):
        return c[0]=='\\' and c[2][0]=='/' or (c[0]!='a' and (has_bwd_over_fwd(c[1]) or has_bwd_over_fwd(c[2])))
    for ws,bad in sorted(res): print(ws,bad, 'has X\\(Y/Z):', any(has_bwd_over_fwd(parse(w)) for w in ws))
    print(len(res))
