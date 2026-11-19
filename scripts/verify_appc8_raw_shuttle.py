"""Independent raw-dictionary checks for the universal AppC8 Lean shuttle proof.

The universal result is AppC8RawShuttle.lean, not these finite tests. This script
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
CODE = '1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---'
TABLE = parse_tm(CODE)


def tape_of(bits, offset=0):
    return {i+offset: 1 for i, b in enumerate(bits) if b == '1'}


def list_lean(bits):
    return '[' + ','.join('true' if b else 'false' for b in bits) + ']'


def make_fixtures(path):
    lines = ['import CryptidSolvePhase4.AppC8RawShuttle',
             'open CryptidSolvePhase4.AppC8Raw',
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


def check_shuttle(k, m, rounds=1, tail=''):
    assert m >= 4*rounds+1
    duration=12*rounds*k+12*rounds*(rounds-1)+26*rounds
    bits='10'+'110'*k+'1'*m+tail
    halt,tape,head,state=simulate_tm(TABLE,duration,tape_of(bits),-1,'A')
    expected='10'+'110'*(k+2*rounds)+'1'*(m-4*rounds)+tail
    assert halt is None and state=='A', (k,m,rounds,tail)
    assert head==-1-2*rounds, (k,m,rounds,head)
    assert tape==tape_of(expected,offset=-2*rounds), (k,m,rounds,tail)
    return duration


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    parser.add_argument('--lean-fixtures',type=Path)
    args=parser.parse_args()
    source=(ROOT/'lean_phase4/CryptidSolvePhase4/AppC8RawShuttle.lean').read_text(encoding='utf-8')
    pattern=r'\|\s*\.(\w),\s*(false|true)\s*=>\s*(?:some\s*\((true|false),\s*(true|false),\s*\.(\w)\)|none)'
    lean_delta={}
    for state,bit,write,direction,target in re.findall(pattern,source):
        key=(state,int(bit=='true'))
        assert key not in lean_delta
        lean_delta[key]=None if not target else (int(write=='true'),1 if direction=='true' else -1,target)
    assert len(lean_delta)==12 and lean_delta==TABLE

    singles=0
    for k in range(21):
        for m in range(5,25):
            check_shuttle(k,m)
            singles+=1
    tails=[''.join(x) for length in range(6) for x in itertools.product('01',repeat=length)]
    tail_cases=0
    for k in range(13):
        for tail in tails:
            check_shuttle(k,5,tail=tail)
            tail_cases+=1
    repeated=0
    for k in range(9):
        for r in range(7):
            for extra in range(8):
                check_shuttle(k,4*r+1+extra,rounds=r)
                repeated+=1
    middle=[]
    for q in range(13):
        r=3*q+2
        duration=check_shuttle(3,12*q+10,rounds=r)
        assert 3+2*r==6*q+7 and 12*q+10-4*r==2
        middle.append({'q':q,'rounds':r,'duration':duration,'output_k':6*q+7,'output_m':2})
    result={'machine':CODE,'table_entries_matched':12,'single_round_cases':singles,
            'single_round_ranges':{'k':[0,20],'m':[5,24]},'arbitrary_tail_cases':tail_cases,
            'repeated_round_cases':repeated,'clean_middle_cases':len(middle),'clean_middle_samples':middle,
            'elapsed_count':'defined raw transitions; no minimal first-return claim',
            'scope':'Raw shuttle and its finite repetitions; reset and exit are checked separately by verify_appc8_raw_clean_macro.py.'}
    if args.lean_fixtures: result['generated_differential_fixtures']=make_fixtures(args.lean_fixtures)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='clean_middle_samples'},indent=2))
    print('[PASS] AppC8 table, raw shuttle, arbitrary right tails, repeated rounds, and clean middle stage')


if __name__=='__main__':
    main()


