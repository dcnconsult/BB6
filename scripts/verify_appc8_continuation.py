"""Independent raw execution checks for new continuation families.
These finite checks complement the universal Lean proofs; they do not prove
BoundaryReturn or enumerate the 507,471,992,896-step certificate.
"""
import argparse,json
from pathlib import Path
from verify_appc8_raw_shuttle import TABLE,tape_of,simulate_tm


def check(k,m,tail,duration,k2,m2,tail2):
    tape=tape_of('010'+'110'*k+'1'*m+tail)
    halted,out,h,s=simulate_tm(TABLE,duration,tape,0,'A')
    expected=tape_of('010'+'110'*k2+'1'*m2+tail2,h)
    assert halted is None and s=='A' and out==expected,(k,m,tail,duration,h,s)


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    counts={}
    for k in range(33):
        check(k,4,'',14*k+36,0,3*k+10,'')
        check(k,1,'',8*k+17,0,1,'0'+'1'*(3*k+2)+'011')
        check(k,3,'011',12*k+40,k+1,1,'011111')
    counts.update(four_collapse=33,one_collapse=33,three_with_tail=33)
    tails=['','1','0','011','0010111','1010101']
    for n in range(21):
        for tail in tails:check(0,1,'0'+'1'*(n+6)+tail,37,3,n+2,tail)
    counts['zero_block_defect_param']=21*len(tails)
    for n in range(17):check(n+2,1,'',8*(n+2)+54,3,3*n+4,'011')
    counts['one_to_tail']=17
    for q in range(17):
        c=4*q+2;left='100'*c+'101'
        tape={-i-1:1 for i,b in enumerate(left) if b=='1'}
        duration=108*q*q+170*q+53
        halted,out,h,s=simulate_tm(TABLE,duration,tape,0,'E')
        assert halted is None and s=='A' and out==tape_of('010'+'110'*(6*q+3)+'1111',h)
    counts['even_carry_to_four']=17
    halted,out,h,s=simulate_tm(TABLE,13314194,{},0,'A')
    assert halted is None and s=='A' and out==tape_of('010'+'1'*4717,h)
    halted,_,_,_=simulate_tm(TABLE,49,tape_of('01010010111'),0,'A')
    assert halted is not None
    result=dict(family_cases=counts,total_family_cases=sum(counts.values()),
        independent_blank_check=dict(time=13314194,k=0,m=4717,absolute_head=h),
        arbitrary_suffix_halting_witness=True,
        scope='Finite complete-tape comparisons. Infinite survival and BoundaryReturn remain unproved.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2));print('PASS: independent continuation checks')

if __name__=='__main__':main()
