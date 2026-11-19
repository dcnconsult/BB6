"""Generate untrusted trace data; Lean independently checks every transition.
--check verifies that the checked-in data is reproducible without changing it.
"""
from pathlib import Path
import argparse
from verify_appc8_raw_shuttle import TABLE

def word(ns):return list(map(int,'0'.join('1'*n for n in ns)))

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    lines=['import BB6Interop.AppC8ResidualCertificate','','/-! Generated finite zipper traces. Every adjacent step and the final halt are',
        'checked by rejectTrace; generated data is not a trusted proof oracle. -/','set_option maxRecDepth 20000',
        'namespace BB6Interop.AppC8ResidualTape','open CryptidSolvePhase4.AppC8Raw','']
    fixtures=[('firstTrace','E',[1,0,0,1,0,1],[1,0]+word([5,5,5,2]),742),
        ('secondTrace','E',[1,0,0,1,0],[1,0]+word([2,2,5,3,1,2]),680),
        ('residualTrace','A',[1,0,1],[0,1,0]+[1,1,0]*2+word([1,5,5,2]),711)]
    for name,st,l,r,expected in fixtures:
        lines.append(f'def {name} : List Cfg := [')
        for t in range(expected+1):
            lv=sum(b<<i for i,b in enumerate(l));rv=sum(b<<i for i,b in enumerate(r))
            lines.append(f'  traceCfg .{st} {len(l)} {lv} {len(r)} {rv}'+(',' if t<expected else ''))
            ins=TABLE[st,r[0] if r else 0]
            if ins is None:
                assert t==expected;break
            w,d,st=ins
            if d==1:l=[w]+l;r=r[1:]
            else:r=[l[0] if l else 0,w]+r[1:];l=l[1:]
        else:raise AssertionError('Expected halting instruction missing')
        lines+= [']','']
    lines+=['end BB6Interop.AppC8ResidualTape','']
    data='\n'.join(lines)
    path=Path(__file__).resolve().parents[1]/'lean_interop/BB6Interop/AppC8ResidualTraceData.lean'
    if a.check:assert path.read_text(encoding='utf-8')==data
    else:path.write_text(data,encoding='utf-8')
    print('PASS: three finite trace datasets reproduce exactly')

if __name__=='__main__':main()
