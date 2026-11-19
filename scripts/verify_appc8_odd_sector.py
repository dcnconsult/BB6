"""Independent raw checks for the universal AppC8 k=4a+3 odd excursion.
Finite checks validate the implementation; the universal statements are Lean proofs.
"""
from pathlib import Path
import argparse,itertools,json
from verify_appc8_raw_shuttle import TABLE,CODE,tape_of,list_lean,simulate_tm,check_shuttle


def check(kind,k):
    if kind=='collapse':
        bits='10'+'110'*k+'111';duration=14*k+36
        expected='10'+'1'*(3*k+7)+'011';expected_head=-5;cfg=f'shuttleCfg {k} 3'
    elif kind=='terminal':
        bits='10'+'110'*k+'1111011';duration=14*k+44
        expected='10'+'1'*(3*k+13);expected_head=-5;cfg=f'shuttleTailCfg {k} 4 [false,true,true]'
    else:
        bits='10'+'110'*(4*k+3)+'111';duration=108*k*k+398*k+356
        expected='10'+'1'*(18*k+31);expected_head=-6*k-15;cfg=f'shuttleCfg {4*k+3} 3'
    halted,tape,head,state=simulate_tm(TABLE,duration,tape_of(bits),-1,'A')
    assert halted is None and (head,state)==(expected_head,'A'),(kind,k,head,state)
    assert tape==tape_of(expected,head+1),(kind,k)
    right=[tape.get(i,0) for i in range(head,max(tape)+1)]
    fixture=f'example : run {duration} ({cfg}) = some ⟨.A, [], {list_lean(right)}⟩ := by decide'
    return {'parameter':k,'duration':duration,'head_displacement':head+1},fixture


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);parser.add_argument('--lean-fixtures',type=Path);args=parser.parse_args()
    samples={kind:[check(kind,k)[0] for k in ns] for kind,ns in [('collapse',range(65)),('terminal',range(65)),('full',range(33))]}
    tails=[''.join(x) for n in range(4) for x in itertools.product('01',repeat=n)]
    tailed=0
    for k in range(6):
        for r in range(5):
            for extra in [1,4]:
                for tail in tails:check_shuttle(k,4*r+extra,rounds=r,tail=tail);tailed+=1
    blanks=[]
    for n,k,m,expected_head in [(18306,0,175,-152),(41096,86,3,-238)]:
        halted,tape,head,state=simulate_tm(TABLE,n,{},0,'A')
        assert halted is None and (head,state)==(expected_head,'A')
        assert tape==tape_of('10'+'110'*k+'1'*m,head+1)
        blanks.append({'time':n,'k':k,'m':m,'head':head,'ones':len(tape)})
    assert 108*8*8+398*8+356==10452 and 7854+10452==18306
    assert 18306+12*43*42+26*43==41096
    result={'machine':CODE,'cases':{k:len(v) for k,v in samples.items()},'tailed_round_cases':tailed,
            'blank_checkpoints':blanks,'samples':samples,
            'scope':'Universal family k=4a+3,m=3 and its blank-run application. New endpoint C(86,3) is not a clean input; this module excludes neither every intermediate clean visit nor global future behavior. Actual clean entry is proved in AppC8RawMod2Sector.'}
    if args.lean_fixtures:
        lines=['import CryptidSolvePhase4.AppC8RawOddSector','open CryptidSolvePhase4.AppC8Raw','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
        for kind,ns in [('collapse',range(9)),('terminal',range(9)),('full',range(4))]:lines.extend(check(kind,k)[1] for k in ns)
        lines.append('#eval IO.println "[PASS] 22 independent complete-configuration odd-sector fixtures"')
        args.lean_fixtures.parent.mkdir(parents=True,exist_ok=True);args.lean_fixtures.write_text('\n'.join(lines)+'\n',encoding='utf-8')
        result['generated_lean_fixtures']=22
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='samples'},indent=2))
    print('[PASS] AppC8 odd collapse, tailed rounds, terminal collapse, universal-family samples, and extended blank checkpoints')


if __name__=='__main__':main()
