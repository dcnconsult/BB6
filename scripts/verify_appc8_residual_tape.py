"""Independent nonblank counterexamples and guarded residual checks.
No result here asserts that AppC 8 halts from the blank tape.
"""
from pathlib import Path
import argparse,itertools,json
from verify_appc8_raw_shuttle import TABLE,simulate_tm

def word(ns):return [int(x) for x in '0'.join('1'*n for n in ns)]
def back(k,marker):return [1,0,0]*k+marker
def blocks(k,w):return [1,1,0]*k+w
def tape_of_cfg(left,right):
    tape={-i-1:1 for i,b in enumerate(left) if b}
    tape.update({i:1 for i,b in enumerate(right) if b});return tape

def trace(name,state,left,right,expected,exclude_heads=False):
    tape=tape_of_cfg(left,right);head=0;heads=[]
    for t in range(expected+1):
        if state=='A' and not any(i<head for i in tape):heads.append(t)
        ins=TABLE[state,tape.get(head,0)]
        if ins is None:
            assert t==expected,(name,t,expected)
            if exclude_heads:assert not heads,(name,heads)
            assert state=='F' and tape.get(head,0)==1
            return dict(name=name,defined_steps=t,undefined_attempt=t+1,
                possible_blank_left_boundary_heads=heads,halting_state=state,read_symbol=1)
        w,d,state=ins
        if w:tape[head]=1
        else:tape.pop(head,None)
        head+=d
    raise AssertionError((name,'did not halt'))

def check_run(state,left,right,steps,es,el,er):
    halt,tape,h,s=simulate_tm(TABLE,steps,tape_of_cfg(left,right),0,state)
    expected={h-i-1:1 for i,b in enumerate(el) if b}
    expected.update({h+i:1 for i,b in enumerate(er) if b})
    assert halt is None and s==es and tape==expected

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    cases=[trace('boundary_original','A',[],[0,1,0]+word([3,5,4,2,2,5,1]),1199),
        trace('boundary_short','A',[],[0,1,0]+word([2,1,5,5,5,2]),748),
        trace('first_defect','E',back(1,[1,0,1]),[1,0]+word([5,5,5,2]),742,True),
        trace('second_defect','E',back(1,[1,0]),[1,0]+word([2,2,5,3,1,2]),680,True),
        trace('residual_first','A',[1,0,1],[0,1,0]+blocks(2,word([1,5,5,2])),711,True)]
    local=0
    defect=[0]+[1]*8+[0,1,1]
    for length in range(9):
        for l in itertools.product((0,1),repeat=length):
            l=list(l);check_run('A',l,[0,1,0]+blocks(2,[1]),30,'A',l,[1]+defect);local+=1
    for k in range(65):
        check_run('A',back(k,[1,0,1]),[0,1,0]+blocks(2,[1]),5*k+36,'A',[],
            [0,1,0,1,0]+[1]*(3*k+2)+defect)
        check_run('A',back(k,[1,0]),[0,1,0]+blocks(2,[1]),5*k+38,'A',[],
            [0,1,0]+[1]*(3*k+4)+defect)
    # Test a proposed stronger guard, without claiming it is an invariant.
    initial=[0,1,0]+blocks(8,word([3,41,35]))
    halt,tape,h,s=simulate_tm(TABLE,2716,tape_of_cfg([],initial),0,'A')
    assert halt is None and s=='A' and min(tape)==h+1 and tape.get(h+2,0)==0
    w=''.join(str(tape.get(i,0)) for i in range(h+3,max(tape)+1));k=0
    while w.startswith('110'):k+=1;w=w[3:]
    runs=[len(z) for z in w.split('0')]
    assert not all(x>y for x,y in zip(runs[1:],runs[2:]))
    result=dict(counterexamples=cases,local_arbitrary_left_checks=local,
        guarded_residual_checks=130,extra_guard_probe=dict(input=dict(k=8,m=3,tail=[41,35]),
        duration=2716,output=dict(k=k,runs=runs),result='strictly descending inactive-tail guard not preserved'),
        scope='Nonblank refutations and finite guarded tests. Blank global nonhalting remains open.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2));print('PASS: independent counterexamples and guarded residual checks')

if __name__=='__main__':main()
