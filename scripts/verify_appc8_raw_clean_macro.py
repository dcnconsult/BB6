"""Independent dictionary-tape checks for AppC8 raw reset, exit, and composition.
Universal proofs live in AppC8RawCleanMacro.lean; these are finite cross-checks.
"""
from pathlib import Path
import argparse
import json
from verify_appc8_raw_shuttle import TABLE, CODE, tape_of, list_lean, simulate_tm


def check(kind, parameter):
    if kind == 'reset':
        c=parameter
        assert c>=1
        bits='10'+'100'*c+'1'
        initial_head=len(bits); initial_state='E'; duration=5*c+43
        expected='10'+'110'*3+'1'*(3*c-2)
        expected_offset=-5; expected_head=-6; expected_state='A'
        cfg=f'cleanCfg {c}'
    elif kind == 'exit':
        k=parameter
        bits='10'+'110'*k+'11'
        initial_head=-1; initial_state='A'; duration=3*k+6
        expected='10'+'100'*(k+1)+'1'
        expected_offset=-1; expected_head=3*k+5; expected_state='E'
        cfg=f'shuttleCfg {k} 2'
    else:
        q=parameter; c=4*(q+1)
        bits='10'+'100'*c+'1'
        initial_head=len(bits); initial_state='E'; duration=108*q*q+332*q+238
        expected='10'+'100'*(6*q+8)+'1'
        expected_offset=-6*q-10; expected_head=12*q+17; expected_state='E'
        assert 2*((6*q+8)+4)==3*(c+4)
        cfg=f'cleanCfg {c}'
    halt,tape,head,state=simulate_tm(TABLE,duration,tape_of(bits),initial_head,initial_state)
    assert halt is None and (head,state)==(expected_head,expected_state),(kind,parameter,halt,head,state)
    assert tape==tape_of(expected,expected_offset),(kind,parameter)
    # The certified families have no redundant trailing zero padding.
    # Build the complete expected zipper from the independent simulator output.
    left=[tape.get(i,0) for i in range(head-1,min(tape)-1,-1)] if min(tape)<head else []
    right=[tape.get(i,0) for i in range(head,max(tape)+1)] if max(tape)>=head else []
    fixture=f'example : run {duration} ({cfg}) = some ⟨.{state}, {list_lean(left)}, {list_lean(right)}⟩ := by decide'
    return {'parameter':parameter,'duration':duration,'head_displacement':head-initial_head},fixture


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    parser.add_argument('--lean-fixtures',type=Path)
    args=parser.parse_args()
    cases={'reset':range(1,129),'exit':range(129),'clean_macro':range(33)}
    results={kind:[check(kind,n)[0] for n in ns] for kind,ns in cases.items()}
    result={'machine':CODE,'cases':{k:len(v) for k,v in results.items()},'ranges':{'reset_c':[1,128],'exit_k':[0,128],'clean_q':[0,32]},
            'elapsed_count':'Defined transitions; no first-return assertion.',
            'scope':'Positive carry reset, all exit block counts, clean sector c=4(q+1). Blank reachability is proved separately in the residue-refinement module; general future behavior remains open.',
            'samples':results}
    if args.lean_fixtures:
        lines=['import CryptidSolvePhase4.AppC8RawCleanMacro','open CryptidSolvePhase4.AppC8Raw',
               'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
        for kind,ns in [('reset',range(1,13)),('exit',range(17)),('clean_macro',range(4))]:
            lines.extend(check(kind,n)[1] for n in ns)
        count=len(lines)-4
        lines.append(f'#eval IO.println "[PASS] {count} independent complete-configuration clean-macro fixtures"')
        args.lean_fixtures.parent.mkdir(parents=True,exist_ok=True)
        args.lean_fixtures.write_text('\n'.join(lines)+'\n',encoding='utf-8')
        result['generated_complete_configuration_fixtures']=count
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='samples'},indent=2))
    print('[PASS] AppC8 raw reset, exit, and full clean macro; complete tape, state, head, and duration')


if __name__=='__main__':
    main()
