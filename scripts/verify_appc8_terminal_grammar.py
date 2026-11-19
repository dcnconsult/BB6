"""Independent complete-tape checks and bounded generated-grammar return probes.
Universal claims come from Lean; bounded return probes are not closure proofs.
"""
import argparse,itertools,json
from pathlib import Path
from verify_appc8_run_lists import check,back,c
from explore_appc8_restricted import raw_return

def terminal(n):return [0]+[1]*n
def defect(n):return [0]+[1]*n+[0,1,1]
def generated(k,m,t):
    return (not t or t==[2] or (m==1 and len(t)==1 and t[0]>=2 and t[0]%3==2)
      or (len(t)==2 and t[0]>=8 and t[0]%9==8 and t[1]==2)
      or (k==0 and m==1 and len(t)==2 and t[0]>=2 and t[0]%3==2 and t[1]==2)
      or (k==0 and m==1 and len(t)==3 and t[0]>=2 and t[0]%3==2 and t[1]>=8 and t[1]%9==8 and t[2]==2))

def probe(k,m,t,cap=200000,max_returns=20):
    total=0;path=[]
    for _ in range(max_returns):
        r=raw_return(k,m,t,cap)
        if r['status']!='return':return dict(status=r['status'],defined_steps_before_segment=total,last_input=[k,m,t])
        total+=r['duration'];k,m,t=r['k'],r['m'],r['tail'];path.append([k,m,t])
        if generated(k,m,t):return dict(status='generated_return',duration=total,boundary_visits=len(path),output=[k,m,t])
    return dict(status='boundary_cap',duration=total,last_input=[k,m,t])

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();counts={}
    def test(name,start,steps,end):check(start,steps,end);counts[name]=counts.get(name,0)+1
    lefts=[list(x) for n in range(5) for x in itertools.product([0,1],repeat=n)]
    for q,l in itertools.product(range(25),lefts):
        read=l[0] if l else 0
        test('terminal_even_local',('E',back(q,l),[1]+terminal(6*q+2)),27*q*q+44*q+19,
            ('A',l[1:],[read]+terminal(9*q+5)))
        test('terminal_odd_local',('E',back(q+1,l),[1]+terminal(6*q+5)),27*q*q+80*q+61,
            ('A',l,[1]+defect(9*q+8)))
    for k,s in itertools.product(range(9),range(17)):
        test('double_even',c(k+5*s+3,1,terminal(12*s+8)),12*k+351*s*s+685*s+336,c(k,1,terminal(27*s+23)))
        test('even_odd',c(k+5*s+1,1,terminal(12*s+2)),14*k+351*s*s+361*s+104,c(0,3*k+4,defect(27*s+8)))
    for k,q in itertools.product(range(9),range(25)):
        test('odd_boundary',c(k+q+1,1,terminal(6*q+5)),8*k+27*q*q+83*q+73,c(0,1,terminal(3*k+2)+defect(9*q+8)))
    for k in range(18,100):test('44_to_104',c(k,1,terminal(44)),12*k+5334,c(k-18,1,terminal(104)))
    for k in range(43,100):test('104_to_239',c(k,1,terminal(104)),12*k+27764,c(k-43,1,terminal(239)))
    terminal_probes=[];paired_probes=[]
    for k,r in itertools.product(range(25),range(41)):
        v=probe(k,1,[3*r+2]);assert v['status']=='generated_return',(k,r,v);terminal_probes.append(v)
    for k,q,m in itertools.product(range(25),range(41),[1,3]):
        v=probe(k,m,[9*q+8,2]);paired_probes.append(dict(input=[k,m,[9*q+8,2]],**v))
    stats={s:sum(v['status']==s for v in paired_probes) for s in sorted({v['status'] for v in paired_probes})}
    result=dict(full_tape_rule_cases=counts,total_full_tape_checks=sum(counts.values()),
      terminal_generated_return_probes=len(terminal_probes),paired_generated_return_probes=len(paired_probes),
      paired_statuses=stats,paired_unresolved=[x for x in paired_probes if x['status']!='generated_return'],
      max_terminal_boundary_visits=max(x['boundary_visits'] for x in terminal_probes),
      paired_sample=[x for x in paired_probes if x.get('boundary_visits',0)>1][:12],
      below_44_guard=dict(input=[17,1,[44]],output=raw_return(17,1,[44])),
      scope='Full tape differential checks plus bounded raw searches: 200000 transitions per segment, at most 20 boundary visits. PairedOneReturn and PairedThreeReturn remain unproved.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['paired_unresolved','paired_sample']},indent=2));print('PASS: exact-time differential checks; bounded probe results recorded separately')
if __name__=='__main__':main()
