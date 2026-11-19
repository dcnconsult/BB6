"""Finite comparison probes, not Lean proofs. Upstream pinned in source-manifest.json.
T315: source next lines 615-630; BMO8: next lines 1040-1047;
A11: syracuseScan/finishC3/finishC6/highLevelNext lines 1370-1409.
The local mirrors are existing scripts/verify_lean_package.py.
"""
from pathlib import Path
import json, sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'scripts'))
from verify_lean_package import lean_stepT315, lean_stepBMO8, lean_epochStepA11

def dm_t315(s):
    a,b,c=s
    if b==0:
        if c==0: return None
        if c==1: return (0,a+3,1)
        if c==2: return (0,a+2,2)
        return (a+3,0,c-3)
    if b==1:
        if c==0: return (a+1,0,1)
        return (a+1,1,c-1)
    if b==2: return (0,a,c+3)
    v=b-3
    if c==0:
        if v%3==0: return None
        if v%3==1: return (a+1,v+2,1)
        return (a+1,v,2)
    if v%3==0: return (a+1,v+1,c+1)
    if v%3==1: return (a+1,v+3,c-1)
    return (a+1,v,c+2)

def dm_bmo(s):
    b,k,c=s
    if b==0: return (3*k+3,0,c+2)
    if b==1:
        if c==0: return (7,2,18) if k==2 else None
        if c==1: return (7,2,18) if k==1 else None
        return (0,k+1,c-2)
    if c==0: return (b-2,0,3*k+5)
    if c==1: return (b-2,0,3*k+8)
    return (b-1,k+1,c-2)

def first_return(f,s,section):
    for count in range(1,10001):
        s=f(s)
        if s is None or section(s): return s,count
    raise RuntimeError('probe limit')

def scan(r,b,k):
    for _ in range(k):
        s=b+int(r)
        r,b=bool(s%2),3*(s//2)+9
    return r,b

def finish3(r,b,rem):
    if rem==0:
        if b%2==0:return (3,int(r),0,b//2+3)
        if r:return (3,0,12,b//2)
        return None
    if b%2==1:return (6,int(r),0,b//2+3)
    if not r:return None
    if b==0:return (6,1,0,13)
    return (6,0,12,b//2-1)

def finish6(r,b,rem):
    if rem==0:
        if b%2==1:return (3,int(r),0,b//2+5)
        if r:return (3,0,12,b//2+1)
        return None
    s=b+int(r)
    s1=3*(s//2)+6+s%2
    return finish3(bool(s1%2),3*(s1//2)+9,1)

def a11_next(st):
    d,r,b,c=st
    r,b=scan(r,b,c//2)
    return (finish3 if d==3 else finish6)(r,b,c%2)

def epoch_coord(st):
    if st is None:return None
    d,r,b,c=st
    return (r+2*(b//3)+12,c,d)

def main():
    result={'evidence':'finite Python comparison only; no Lean interoperability theorem'}
    failures=[]; maximum=0; count=0
    for a in range(101):
        for b in range(1,101):
            got,n=first_return(dm_t315,(0,a,b),lambda s:s[0]==0)
            actual=None if got is None else got[1:]
            expected=lean_stepT315(a,b)
            count+=1;maximum=max(maximum,n)
            if actual!=expected:failures.append([a,b,expected,actual])
    result['T315']={'candidate_embedding':'D(0,a,b), one raw step after local C(a,b)',
        'domain':'0 <= a <= 100; 1 <= b <= 100','cases':count,
        'max_upstream_macro_steps':maximum,'mismatches':failures[:10],'mismatch_count':len(failures)}
    failures=[];maximum=0;count=0
    for a in range(101):
        for c in range(2,101):
            if a+c<8 or not(a%3==0 or c%3==2):continue
            got,n=first_return(dm_bmo,(a,0,c),lambda s:s[1]==0)
            actual=None if got is None else (got[0],got[2])
            expected=lean_stepBMO8(a,c)
            count+=1;maximum=max(maximum,n)
            if actual!=expected:failures.append([a,c,expected,actual])
    result['BMO8']={'candidate_embedding':'P(a,0,c)',
        'domain':'0 <= a <= 100; 2 <= c <= 100; a+c>=8; a mod3=0 or c mod3=2',
        'cases':count,'max_upstream_macro_steps':maximum,'mismatches':failures[:10],'mismatch_count':len(failures)}
    # Compare the finite blank-path overlap, after the local initial epoch.
    s=(3,0,0,6);local=(12,6,3);sequence=[list(local)]
    for _ in range(3):
        s=a11_next(s)
        local=lean_epochStepA11(*local)
        assert epoch_coord(s)==local,(s,local)
        sequence.append(list(local))
    result['A11']={'coordinate':'X=r+2*(b/3)+12, b divisible by 3, r=0 or 1',
        'matched_transitions':3,'epoch_sequence':sequence,
        'scope':'finite d=3 blank-path overlap; not full four-sector conjugacy'}
    out=Path(__file__).with_name('finite-comparison-results.json')
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
    assert result['T315']['mismatch_count']==0
    assert result['BMO8']['mismatch_count']==0

if __name__=='__main__':main()
