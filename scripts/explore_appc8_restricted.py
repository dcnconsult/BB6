"""Finite exploration using named proved laws and labeled bounded raw bridges.
Not a closure certificate. Uncovered large branches stop rather than extrapolate.
"""
import argparse,json
from pathlib import Path

def advance(k,m,tail):
    tail=list(tail)
    if m>=5:
        r=(m-1)//4
        return k+2*r,m-4*r,tail,12*k*r+12*r*(r-1)+26*r,'tail_shuttle_rounds'
    if m==2:
        if tail:return k+1,tail[0],tail[1:],0,'absorb_defect'
        return 3,3*k+1,[],8*k+54,'exit_then_reset'
    if m==4:
        if not tail:return 0,3*k+10,[],14*k+36,'four_collapse'
        if tail==[2]:return 0,3*k+13,[],14*k+44,'appC8_odd_terminal'
        if tail[0]>=3:return k+3,tail[0]-2,tail[1:],12*k+32,'four_long'
    if m==3:
        if tail==[26,2] and k>=5:return k-3,1,[44],12*k+644,'three_twenty_six'
        if tail==[8,2] and k>=2:return k,1,[17],12*k+116,'three_eight'
        if not tail:return 0,3*k+7,[2],14*k+36,'appC8_odd_collapse'
        if tail==[2]:return k+1,1,[5],12*k+40,'three_with_tail'
    if m==1:
        if tail==[17] and k>=4:return 0,1,[3*k-7,26,2],8*k+323,'seventeen_collapse'
        if not tail:return 0,1,[3*k+2,2],8*k+17,'one_collapse'
        if k==0 and tail[0]>=5:return 3,tail[0]-4,tail[1:],37,'run_list_zero_long'
        if tail==[5]:
            if k==0:return 3,1,[],37,'five_zero'
            return 0,1,[3*k-1,8,2],8*k+65,'five_collapse'
        if tail==[2] and k>=2:return 0,3*k+1,[8,2],14*k+90,'defect_one_collapse'
        if tail==[8,2] and k>=5:return 0,3*k-8,[26,2],14*k+416,'defect_eight_collapse'
    return None

def raw_return(k,m,tail,cap=2000000):
    from verify_appc8_raw_shuttle import TABLE
    bits=[0,1,0]+[1,1,0]*k+list(map(int,'0'.join('1'*n for n in [m]+tail)))
    tape={i:1 for i,b in enumerate(bits) if b};h=0;st='A';leftones=0
    for t in range(1,cap+1):
        ins=TABLE[st,tape.get(h,0)]
        if ins is None:return dict(status='halt',defined_steps=t-1)
        w,d,st=ins
        if w:tape[h]=1
        else:tape.pop(h,None)
        if d==1:leftones+=w
        else:leftones-=tape.get(h-1,0)
        h+=d
        if st=='A' and leftones==0 and [tape.get(h+i,0) for i in range(3)]==[0,1,0]:
            word=''.join(str(tape.get(i,0)) for i in range(h+3,max(tape)+1))
            if not word or not word.startswith('1') or '00' in word:return dict(status='language_escape',time=t,word=word)
            runs=[len(x) for x in word.split('0')];b=0
            while len(runs)>1 and runs[0]==2:b+=1;runs.pop(0)
            return dict(status='return',k=b,m=runs[0],tail=runs[1:],duration=t)
    return dict(status='raw_cap')

def explore(cap):
    k,m,tail,t=0,2,[],5;records=[]
    for i in range(cap):
        step=advance(k,m,tail)
        if step is None and 3*k+m+sum(tail)<100000:
            probe=raw_return(k,m,tail)
            if probe['status']=='return':step=(probe['k'],probe['m'],probe['tail'],probe['duration'],'raw_finite_return')
        records.append(dict(index=i,time=t,k=k,m=m,tail=tail,rule=step[-1] if step else None))
        if step is None:break
        k,m,tail,dt,rule=step;t+=dt
    return dict(status='uncovered_branch' if step is None else 'macro_cap',records=records)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=2000);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=explore(a.cap);a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(dict(status=r['status'],count=len(r['records']),last=r['records'][-10:]),indent=2))
