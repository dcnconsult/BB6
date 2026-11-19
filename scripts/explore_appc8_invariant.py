"""Bounded exploratory n-gram abstraction; NOT a raw nonhalting proof.
A reachable abstract halt is inconclusive because contexts are merged.
"""
import argparse,json,time
from verify_appc8_raw_shuttle import TABLE

def closure(n, cap=100000):
    zero=(0,)*n
    centers={('A',zero,zero)}
    left={(0,)*(n+1)};right=set(left)
    rounds=0;start=time.time()
    while True:
        rounds+=1;before=(len(centers),len(left),len(right))
        new=set()
        for st,l,r in sorted(centers):
            ins=TABLE[st,r[0]]
            if ins is None:
                return dict(width=n,status='abstract_halt_inconclusive',centers=len(centers),rounds=rounds,seconds=time.time()-start)
            w,d,s=ins
            if d==1:
                left.add((w,)+l)
                for b in (0,1):
                    if r+(b,) in right:new.add((s,(w,)+l[:-1],r[1:]+(b,)))
            else:
                right.add((l[0],w)+r[1:])
                # Writing the old head changes the next interior right n-gram too.
                for b in (0,1):
                    if r+(b,) in right:right.add((w,)+r[1:]+(b,))
                for b in (0,1):
                    if l+(b,) in left:new.add((s,l[1:]+(b,),(l[0],w)+r[1:-1]))
        centers.update(new)
        if len(centers)>cap:return dict(width=n,status='resource_cap_inconclusive',centers=len(centers),rounds=rounds)
        if before==(len(centers),len(left),len(right)):
            return dict(width=n,status='candidate_closed_no_halt_requires_certificate',centers=len(centers),left=len(left),right=len(right),rounds=rounds,seconds=time.time()-start)

def language_probes():
    import itertools,random
    from verify_appc8_raw_shuttle import tape_of
    witnesses=[];escapes=[];counts={'exhaustive':0,'random':0}
    def probe(tail,limit,kind):
        counts[kind]+=1;tape=tape_of('10'+tail);h=-1;st='A'
        for t in range(limit):
            ins=TABLE[st,tape.get(h,0)]
            if ins is None:
                witnesses.append(dict(word=tail,defined_steps=t));return
            w,d,st=ins
            if w:tape[h]=1
            else:tape.pop(h,None)
            h+=d
            if st=='A' and h==min(tape)-1 and tape.get(h+2,0)==0:
                word=''.join(str(tape.get(i,0)) for i in range(h+3,max(tape)+1))
                if not word.startswith('1') or '00' in word:
                    escapes.append(dict(word=tail,time=t+1,output=word));return
    for length in range(1,15):
        for bits in itertools.product('01',repeat=length):
            tail=''.join(bits)
            if tail.startswith('1') and tail.endswith('1') and '00' not in tail:
                probe(tail,3000,'exhaustive')
    rng=random.Random(20261118)
    for _ in range(180):
        runs=[rng.randint(1,18) for _ in range(rng.randint(2,10))]
        probe('0'.join('1'*n for n in runs),120000,'random')
    return dict(counts=counts,exhaustive_max_length=14,exhaustive_step_cap=3000,
        random_seed=20261118,random_step_cap=120000,halts=witnesses,boundary_escapes=escapes,
        scope='No counterexample in bounded probes does not establish BoundaryReturn.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--max-width',type=int,default=6)
    p.add_argument('--output');p.add_argument('--language-tests',action='store_true');a=p.parse_args()
    results=[]
    for n in range(2,a.max_width+1):
        r=closure(n);results.append(r);print(json.dumps(r),flush=True)
    result={'contexts':results}
    if a.language_tests:
        result['language_probes']=language_probes();print(json.dumps(result['language_probes']),flush=True)
    if a.output:
        from pathlib import Path
        Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
