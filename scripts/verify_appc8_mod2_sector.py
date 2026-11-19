"""Independent complete-tape checks for modulo-four reduction and clean entry.
The universal claims are proved in AppC8RawMod2Sector.lean. These finite checks
compare full tape, state, head, duration, and the actual clean-sector guard.
"""
from pathlib import Path
import argparse,json
from verify_appc8_raw_shuttle import TABLE,CODE,tape_of,list_lean,simulate_tm


def check(kind,x):
    if kind=='one':
        k=x+2;bits='10'+'110'*k+'1011';duration=14*k+90
        expected='10'+'1'*(3*k+1)+'0'+'1'*8+'011';head=-5;state='A';cfg=f'shuttleTailCfg {k} 1 [false,true,true]'
    elif kind=='eight':
        k=x+5;bits='10'+'110'*k+'10'+'1'*8+'011';duration=14*k+416
        expected='10'+'1'*(3*x+7)+'0'+'1'*26+'011';head=-5;state='A';cfg=f'shuttleTailCfg {k} 1 (defectTail 8)'
    elif kind=='mod2':
        k=4*x+2;bits='10'+'110'*k+'111';duration=108*x*x+398*x+388
        expected='10'+'1'*(18*x+19)+'0'+'1'*8+'011';head=-6*x-15;state='A';cfg=f'shuttleCfg {k} 3'
    elif kind=='mod16':
        k=16*x+6;bits='10'+'110'*k+'111';duration=14364*x*x+18494*x+6438
        expected='10'+'110'*(54*x+36)+'11';head=-114*x-77;state='A';cfg=f'shuttleCfg {k} 3'
    elif kind=='carry':
        k=16*x+6;bits='10'+'110'*k+'111';duration=14364*x*x+18656*x+6552
        expected='10'+'100'*(54*x+37)+'1';head=48*x+37;state='E';cfg=f'shuttleCfg {k} 3'
        assert (54*x+37)%2==1 and (54*x+37)%4!=0
    else:
        k=4*x+1;bits='10'+'110'*k+'111';duration=108*x*x+260*x+147
        expected='10'+'100'*(6*x+6)+'1';head=12*x+12;state='E';cfg=f'shuttleCfg {k} 3'
        assert ((6*x+6)%4==0)==(x%2==1)
    halted,tape,actual_head,actual_state=simulate_tm(TABLE,duration,tape_of(bits),-1,'A')
    assert halted is None and (actual_head,actual_state)==(head,state),(kind,x)
    assert tape==tape_of(expected,head+1 if state=='A' else head-len(expected)),(kind,x)
    left=[tape.get(i,0) for i in range(head-1,min(tape)-1,-1)] if min(tape)<head else []
    right=[tape.get(i,0) for i in range(head,max(tape)+1)] if max(tape)>=head else []
    fixture=f'example : run {duration} ({cfg}) = some ⟨.{state}, {list_lean(left)}, {list_lean(right)}⟩ := by decide'
    return {'parameter':x,'duration':duration,'head':head,'state':state},fixture


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);parser.add_argument('--lean-fixtures',type=Path);args=parser.parse_args()
    samples={kind:[check(kind,x)[0] for x in ns] for kind,ns in [('one',range(33)),('eight',range(33)),('mod2',range(21)),('mod16',range(13)),('carry',range(13)),('mod1',range(21))]}
    blanks=[]
    for n,kind,k,m,head in [(499104,'C',306,2,-884),(500028,'D',307,0,40),(501606,'C',3,919,-890),(1142348,'C',461,3,-1348),(2600695,'D',696,0,45),(5890701,'D',1046,0,47)]:
        halted,tape,h,st=simulate_tm(TABLE,n,{},0,'A')
        bits='10'+('110'*k+'1'*m if kind=='C' else '100'*k+'1')
        expected_state='A' if kind=='C' else 'E'
        assert halted is None and (h,st)==(head,expected_state)
        assert tape==tape_of(bits,head+1 if kind=='C' else head-len(bits))
        blanks.append({'time':n,'family':kind,'k_or_c':k,'m':m if kind=='C' else None,'head':h,'ones':len(tape)})
    assert 696==4*(173+1) and 6*173+8==1046
    assert 108*173*173+332*173+238==3290006 and 2600695+3290006==5890701
    result={'machine':CODE,'cases':{k:len(v) for k,v in samples.items()},'samples':samples,'blank_checkpoints':blanks,
       'clean_entry':{'time':2600695,'c':696,'q':173},'clean_output':{'time':5890701,'c':1046},
       'scope':'Uniform k=4a+2 reduction retains a suffix. Full exit proved for k=16b+6; following k=4a+1 branch proves actual clean entry. No first-entry minimality, all-residue complete excursion, or global survival claim.'}
    if args.lean_fixtures:
        lines=['import CryptidSolvePhase4.AppC8RawMod2Sector','open CryptidSolvePhase4.AppC8Raw','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
        for kind,ns in [('one',range(6)),('eight',range(6)),('mod2',range(4)),('mod16',range(1)),('carry',range(1)),('mod1',range(4))]:lines.extend(check(kind,x)[1] for x in ns)
        lines.append('#eval IO.println "[PASS] 22 independent complete-configuration residue-branch fixtures"')
        args.lean_fixtures.parent.mkdir(parents=True,exist_ok=True);args.lean_fixtures.write_text('\n'.join(lines)+'\n',encoding='utf-8');result['generated_lean_fixtures']=22
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='samples'},indent=2))
    print('[PASS] AppC8 residue reductions, branch exits, complete blank checkpoints, and actual clean-macro application')


if __name__=='__main__':main()
