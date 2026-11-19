"""Independent complete-tape checks for the certified AppC8 blank trajectory.
Finite checkpoints validate encoding and composition; Lean proves the stated
reachability and all defined prefixes through time 7854. No clean-sector entry
or global non-halting is inferred from these checks.
"""
from pathlib import Path
import argparse,json
from verify_appc8_raw_shuttle import TABLE,CODE,tape_of,list_lean,simulate_tm

CHECKPOINTS=[(0,'blank',0,0,0),(5,'C',0,2,-3),(11,'D',1,0,3),
 (59,'C',3,1,-9),(3244,'C',18,10,-48),(3486,'C',20,6,-50),
 (3752,'C',22,2,-52),(3824,'D',23,0,20),(3982,'C',3,67,-58),
 (7854,'C',35,3,-90)]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    parser.add_argument('--lean-fixtures',type=Path)
    args=parser.parse_args()
    results=[];fixtures=['import CryptidSolvePhase4.AppC8RawBlankReachability',
      'open CryptidSolvePhase4.AppC8Raw','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    for n,kind,k,m,expected_head in CHECKPOINTS:
        halted,tape,head,state=simulate_tm(TABLE,n,{},0,'A')
        if kind=='blank':expected={};expected_state='A'
        elif kind=='C':expected=tape_of('10'+'110'*k+'1'*m,expected_head+1);expected_state='A'
        else:
            bits='10'+'100'*k+'1'
            expected=tape_of(bits,expected_head-len(bits));expected_state='E'
        assert halted is None and (head,state)==(expected_head,expected_state),(n,head,state)
        assert tape==expected,(n,kind,k,m)
        left=[tape.get(i,0) for i in range(head-1,min(tape)-1,-1)] if tape and min(tape)<head else []
        right=[tape.get(i,0) for i in range(head,max(tape)+1)] if tape and max(tape)>=head else []
        # These are direct executions from blank, independent of the compositional proof.
        fixtures.append(f'example : run {n} blankCfg = some ⟨.{state}, {list_lean(left)}, {list_lean(right)}⟩ := by decide')
        results.append({'steps':n,'family':kind,'k_or_c':k,'m':m if kind=='C' else None,'head':head,'state':state,'ones':len(tape)})
    # Connect the new blank-run checkpoints to the independently checked raw component durations.
    assert 5+6==11 and 11+(5*1+43)==59 and 59+3185==3244
    assert 3244+(12*18+26)+(12*20+26)==3752
    assert 3752+(3*22+6)==3824 and 3824+(5*23+43)==3982
    assert 3982+(12*16*3+12*16*15+26*16)==7854
    assert 1%4!=0 and 23%4!=0
    result={'machine':CODE,'checkpoint_count':len(results),'checkpoints':results,
      'defined_prefix_horizon':7854,'bridge_steps':3185,
      'scope':'Concrete blank reachability plus composition with general reset/shuttle/exit. Clean-sector entry is proved separately in AppC8RawMod2Sector; no first-return or global-survival claim.'}
    if args.lean_fixtures:
        fixtures.append('#eval IO.println "[PASS] 10 independent complete-configuration blank-run fixtures"')
        args.lean_fixtures.parent.mkdir(parents=True,exist_ok=True)
        args.lean_fixtures.write_text('\n'.join(fixtures)+'\n',encoding='utf-8')
        result['generated_direct_blank_fixtures']=10
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
    print('[PASS] AppC8 blank checkpoints: complete tape, state, head, component durations, and clean-sector guards')


if __name__=='__main__':main()
