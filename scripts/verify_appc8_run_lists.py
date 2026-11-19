"""Independent complete-tape checks for the AppC 8 run-list refinements.
Kernel proofs establish the universal statements; these finite dictionary-tape
checks do not prove the open DefectReturn or BoundaryReturn predicates.
"""
from pathlib import Path
import argparse,itertools,json
from verify_appc8_raw_shuttle import TABLE,simulate_tm


def blocks(n,t):return [1,1,0]*n+t
def back(n,t):return [1,0,0]*n+t
def ones(n,t):return [1]*n+t
def defect(n):return [0]+ones(n,[0,1,1])
def c(k,m,t=()):return ('A',[],[0,1,0]+blocks(k,ones(m,list(t))))
def e(k,marker,right):return ('E',back(k,marker),right)
def check(start,steps,end):
    s,left,right=start
    tape={-i-1:1 for i,b in enumerate(left) if b}
    tape.update({i:1 for i,b in enumerate(right) if b})
    halted,out,h,st=simulate_tm(TABLE,steps,tape,0,s)
    es,el,er=end
    expected={h-i-1:1 for i,b in enumerate(el) if b}
    expected.update({h+i:1 for i,b in enumerate(er) if b})
    assert halted is None and st==es and out==expected,(steps,st,es,h)
    return h


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    counts={}
    def test(label,start,steps,end):
        h=check(start,steps,end);counts[label]=counts.get(label,0)+1;return h
    tails=[list(x) for n in range(5) for x in itertools.product((0,1),repeat=n)]
    lefts=[list(x) for n in range(6) for x in itertools.product((0,1),repeat=n)]
    for l in lefts:
        test('five_turn',e(1,l,[1,0]+ones(5,[])),61,('A',l,[1]+defect(8)))
        for t in tails:
            test('defect_push',('E',l,[1,0,1]+t),8,('E',[1,0]+l,[1]+t))
            test('defect_strip_block',e(1,l,[1,0]+ones(5,t)),31,('A',l,[0,1,0]+blocks(2,[1]+t)))
    for n in range(33):
        test('five_collapse',c(n+1,1,[0]+ones(5,[])),8*(n+1)+65,c(0,1,[0]+ones(3*n+2,defect(8))))
    test('five_zero',c(0,1,[0]+ones(5,[])),37,c(3,1))
    for k in range(9):
        for n in range(9):
            for t in tails:
                test('four_long',c(k,4,[0]+ones(n+3,t)),12*k+32,c(k+3,n+1,t))
                test('first_long',e(k,[1,0,1],ones(n+3,t)),3*k+9,('E',[1,0],blocks(k+1,ones(n+1,t))))
                test('second_long',e(k,[1,0],ones(n+3,t)),3*k+8,c(k+1,n+1,t))
    for k in range(33):
        test('first_one',e(k,[1,0,1],[1]),5*k+14,c(0,1,defect(3*k+2)))
        test('first_two',e(k,[1,0,1],[1,1]),5*k+51,c(3,3*k+1))
        test('second_one',e(k,[1,0],[1]),5*k+16,c(0,3*k+4,[0,1,1]))
        test('second_two',e(k,[1,0],[1,1]),5*k+16,c(0,3*k+7))
        test('second_defect_two',e(k,[1,0],[1,0,1,1]),3*k+22,c(k,1,[0]+ones(5,[])))
    for t in tails:
        test('first_zero_long',e(0,[1,0,1],[1,0]+ones(5,t)),34,c(3,1,t))
        test('second_zero_long',e(0,[1,0],[1,0]+ones(5,t)),31,c(2,1,t))
    for k in range(7):
        for n in range(7):
            for t in [[],[0,1],[0,1,0,1,1],[0]+[1]*8+[0,1,1]]:
                test('one_long_local',c(k+1,1,[0]+ones(n+5,t)),3*k+37,
                    ('A',back(k,[1,0,1]),[0,1,0]+blocks(2,ones(n+1,t))))
                test('zero_long',c(0,1,[0]+ones(n+5,t)),37,c(3,n+1,t))
    h=test('requested_concrete_frontier',c(306555,1,[0]+ones(5,[])),2452505,
        c(0,1,[0]+ones(919664,defect(8))))
    result=dict(family_cases=counts,total_cases=sum(counts.values()),
        requested_frontier=dict(blocks=306555,duration=2452505,output_run_lengths=[1,919664,8,2],relative_head_shift=h),
        scope='Finite independent complete-tape tests; full trillion-step certificate is Lean composition. BoundaryReturn remains open.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2));print('PASS: run-list differential checks')

if __name__=='__main__':main()
