"""Independent full dictionary-tape checks for restricted AppC8 phases.
Finite probes are reported separately from Lean's universal statements.
"""
import argparse,itertools,json
from pathlib import Path
from verify_appc8_run_lists import check,back,blocks,c
from explore_appc8_restricted import raw_return,explore

def phase(l,b,m,t):return ('A',l,[0,1,0]+blocks(b,[1]*m+t))
def suffix(ns):return [int(x) for x in ''.join('0'+'1'*n for n in ns)]
def admissible(k,m,tail):
    core=tail in [[],[2],[8,2],[26,2]]
    terminal=m==1 and tail in [[5],[17],[44],[68]]
    emitted=k==0 and m==1 and len(tail)>1 and tail[0]%3==2 and tail[1:] in [[2],[8,2],[26,2]]
    return core or terminal or emitted

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();counts={}
    def test(name,start,steps,end):check(start,steps,end);counts[name]=counts.get(name,0)+1
    tails=[list(x) for n in range(3) for x in itertools.product([0,1],repeat=n)]
    lefts=[list(x) for n in range(4) for x in itertools.product([0,1],repeat=n)]
    for l,t,b,n in itertools.product(lefts,tails,range(6),range(4)):
        test('residual_cycle',phase(back(1,l),b,n+7,t),18*b+47,phase(l,b+3,n+1,t))
    for marker,b,n,t in itertools.product([[1,0,1],[1,0]],range(8),range(4),tails):
        first=marker==[1,0,1]
        test('marker_finish',phase(marker,b,n+7,t),18*b+(50 if first else 47),c(b+(4 if first else 3),n+1,t))
    for marker,left,b,n,t in itertools.product([[1,0,1],[1,0]],range(6),range(4),range(3),[[],[0,1],[0,1,1],[0]+[1]*8+[0,1,1]]):
        test('residual_drain',phase(back(left,marker),b,6*left+n+7,t),27*left*left+20*left+18*left*b,phase(marker,b+3*left,n+7,t))
    for k in range(2,41):test('three_eight',c(k,3,suffix([8,2])),12*k+116,c(k,1,suffix([17])))
    for k in range(4,41):test('seventeen_collapse',c(k,1,suffix([17])),8*k+323,c(0,1,suffix([3*k-7,26,2])))
    for k in range(5,41):test('three_twenty_six',c(k,3,suffix([26,2])),12*k+644,c(k-3,1,suffix([44])))
    test('actual_blank_entry',('A',[],[]),2286,phase(back(4,[1,0,1]),2,40,[]))
    test('actual_phase_drain',phase(back(4,[1,0,1]),2,40,[]),656,phase([1,0,1],14,16,[]))
    test('actual_phase_finish',phase([1,0,1],14,16,[]),302,c(18,10))
    trajectory=explore(2000)
    assert all(admissible(x['k'],x['m'],x['tail']) for x in trajectory['records'])
    failures=[];probes=0
    for k,m in itertools.product(range(24),range(1,5)):
        for tail in [[],[2],[8,2],[26,2]]+([[5],[17],[44],[68]] if m==1 else []):
            r=raw_return(k,m,tail,200000);probes+=1
            if r['status']!='return' or not admissible(r['k'],r['m'],r['tail']):
                failures.append(dict(input=dict(k=k,m=m,tail=tail),output=r))
    result=dict(universal_rule_finite_checks=counts,total_full_tape_checks=sum(counts.values()),
      blank_fueled_entry=dict(time=2286,left_blocks=4,right_blocks=2,active_ones=40,margin=9),
      catalog_probes=probes,catalog_first_return_escapes=failures,trajectory_records=len(trajectory['records']),
      final_frontier=trajectory['records'][-1],scope='Finite full-tape differential checks. Catalog first-return escape is not a refutation of eventual CandidateClosure. Global nonhalting remains open.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(counts=counts,total=result['total_full_tape_checks'],catalog_probes=probes,escapes=failures[:6],escape_count=len(failures)),indent=2));print('PASS: independent restricted-phase checks')
if __name__=='__main__':main()
