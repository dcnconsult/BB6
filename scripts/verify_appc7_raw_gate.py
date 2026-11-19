"""Independent raw-dictionary checks for the universal AppC7 Lean gate proof.

The universal result is AppC7RawGate.lean, not these finite tests. This script
checks transition-table transcription, boundaries, the counting convention,
and optional kernel-checked differential fixtures generated from the existing
dictionary-tape simulator. No macro rule is used to simulate raw execution.
"""
from pathlib import Path
import argparse
import itertools
import json
import re

from phase4_beyond_collatz_toolkit import parse_tm, simulate_tm

ROOT = Path(__file__).resolve().parent.parent
CODE = '1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC'
TABLE = parse_tm(CODE)


def tape_of(bits, offset=0):
    return {i+offset: 1 for i, b in enumerate(bits) if b == '1'}


def list_lean(bits):
    return '[' + ','.join('true' if b else 'false' for b in bits) + ']'


def make_fixtures(path):
    lines = ['import CryptidSolvePhase4.AppC7RawGate',
             'open CryptidSolvePhase4.AppC7Raw',
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
             'def observe (c : Cfg) : State × List Bool :=',
             '  (c.st, ((List.range 8).reverse.map (fun n => read (c.left.drop n))) ++',
             '    ((List.range 9).map (fun n => read (c.right.drop n))))']
    count = 0
    for state in 'ABCDEF':
        for bit in [0, 1]:
            for mask in [0, 7, 21, 63]:
                left = [(mask >> i) & 1 for i in range(3)]
                right = [bit] + [(mask >> (i+3)) & 1 for i in range(3)]
                tape = {i:b for i,b in enumerate(right) if b}
                tape.update({-i-1:b for i,b in enumerate(left) if b})
                cfg = f'⟨.{state}, {list_lean(left)}, {list_lean(right)}⟩'
                for n in [1, 2, 7, 19]:
                    halt, out, head, st = simulate_tm(TABLE, n, tape, 0, state)
                    rhs = 'none' if halt is not None else f'some (.{st}, {list_lean([out.get(head+i,0) for i in range(-8,9)])})'
                    lines.append(f'example : (run {n} {cfg}).map observe = {rhs} := by decide')
                    count += 1
    lines.append(f'#eval IO.println "[PASS] {count} independent dictionary/Lean execution fixtures"')
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text('\n'.join(lines)+'\n',encoding='utf-8')
    return count


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    parser.add_argument('--lean-fixtures',type=Path)
    args=parser.parse_args()
    source=(ROOT/'lean_phase4/CryptidSolvePhase4/AppC7RawGate.lean').read_text(encoding='utf-8')
    pattern=r'\|\s*\.(\w),\s*(false|true)\s*=>\s*(?:some\s*\((true|false),\s*(true|false),\s*\.(\w)\)|none)'
    lean_delta={}
    for state, bit, write, direction, target in re.findall(pattern,source):
        key=(state,int(bit=='true'))
        assert key not in lean_delta
        lean_delta[key]=None if not target else (int(write=='true'),1 if direction=='true' else -1,target)
    assert lean_delta==TABLE and len(lean_delta)==12

    gate_cases=0
    for a in range(13):
        for r in range(9):
            duration=16*r*r+(8*a+12)*r+2*a+5
            bits='10'*a+'1110'*r+'11'
            before=simulate_tm(TABLE,duration-1,tape_of(bits),-1,'D')
            assert before[0] is None and before[3]=='F' and before[1].get(before[2],0)==0
            after=simulate_tm(TABLE,duration,tape_of(bits),-1,'D')
            assert after[0]==duration
            gate_cases+=1
    prefixed=[]
    for b in range(33):
        bits='00'+'1110'*b+'11'
        duration=16*b*b+28*b+15
        assert simulate_tm(TABLE,duration,tape_of(bits),-1,'A')[0]==duration
        prefixed.append({'b':b,'halting_attempt':duration,'defined_transitions':duration-1})
    tails=[''.join(x) for length in range(5) for x in itertools.product('01',repeat=length)]
    phase_cases=0
    for a in range(13):
        for tail in tails:
            bits='10'*a+'1110'+tail
            halt,tape,head,state=simulate_tm(TABLE,8*a+20,tape_of(bits),-1,'D')
            assert halt is None and state=='D' and head==-5
            assert tape==tape_of('10'*(a+4)+tail,offset=-4)
            phase_cases+=1
    result={'machine':CODE,'table_entries_matched':12,'general_gate_cases':gate_cases,
            'gate_ranges':{'a':[0,12],'r':[0,8]},'prefixed_family_cases':len(prefixed),
            'phase_with_arbitrary_tail_cases':phase_cases,'prefixed_samples':prefixed,
            'universal_proof':'CryptidSolvePhase4.AppC7Raw.gate_sweep_exact_time and appC7_raw_gate_exact_time',
            'scope':'Blank left half-tape and the displayed finite gate input; not blank-tape reachability.'}
    if args.lean_fixtures:
        result['generated_differential_fixtures']=make_fixtures(args.lean_fixtures)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='prefixed_samples'},indent=2))
    print('[PASS] AppC7 transition table, exact gate times, boundary cases, and arbitrary-tail phases')


if __name__=='__main__':
    main()
