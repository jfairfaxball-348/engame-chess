"""Two fixed local controls only. No class scan, oracle or game-value search."""
import datetime,hashlib,json,sys
from pathlib import Path
r=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(r/'scripts'))
import krk_diagnostic as kd  # legal_moves only; kd.run NEVER called

def direct(p,q,side):
    assert set(q)==set(p) and len(set(q.values()))==3
    changes=[k for k in p if p[k]!=q[k]]
    assert len(changes)==1 and changes[0][0]==side
    k=changes[0];src,dst=p[k],q[k]
    assert all(0<=z<=7 for z in dst)
    dx,dy=dst[0]-src[0],dst[1]-src[1]
    if k[1]=='K':assert max(abs(dx),abs(dy))==1
    else:
        assert (dx==0)!=(dy==0)
        vx,vy=(dx>0)-(dx<0),(dy>0)-(dy<0)
        x,y=src[0]+vx,src[1]+vy
        while (x,y)!=dst:
            assert (x,y) not in p.values()
            x,y=x+vx,y+vy
    s,rook,w=q[('W','K')],q[('W','R')],q[('B','K')]
    assert max(abs(s[0]-w[0]),abs(s[1]-w[1]))>=2
    if side=='B':
        if rook[0]==w[0]:assert s[0]==rook[0] and min(rook[1],w[1])<s[1]<max(rook[1],w[1])
        if rook[1]==w[1]:assert s[1]==rook[1] and min(rook[0],w[0])<s[0]<max(rook[0],w[0])

edges=[]
def move(p,side,kind,t):
    q=dict(p);q[(side,kind)]=t
    assert q in kd.legal_moves(p,side),(p,side,kind,t)
    direct(p,q,side)
    edges.append(dict(side=side,kind=kind,source=p[(side,kind)],target=t))
    return q
def replies(p):
    out=kd.legal_moves(p,'B');assert out
    for q in out:
        direct(p,q,'B')
        edges.append(dict(side='B',kind='K',source=p[('B','K')],target=q[('B','K')]))
    return out
def mate(p):assert kd.in_check(p,'B') and not kd.legal_moves(p,'B')

p={('W','K'):(5,5),('W','R'):(6,6),('B','K'):(7,7)}
first=replies(move(p,'W','R',(0,6)))
assert [q[('B','K')] for q in first]==[(6,7)]
second=replies(move(first[0],'W','R',(1,6)))
assert {q[('B','K')] for q in second}=={(5,7),(7,7)}
lengths=[]
for q in second:
    if q[('B','K')]==(5,7):
        mate(move(q,'W','R',(1,7)));lengths.append(5)
    else:
        third=replies(move(q,'W','K',(6,5)))
        assert [q[('B','K')] for q in third]==[(6,7)]
        mate(move(third[0],'W','R',(1,7)));lengths.append(7)
corner_edges=list(edges);assert len(corner_edges)==9
edges=[]
start={('W','K'):(2,2),('W','R'):(3,3),('B','K'):(5,4)}
p=dict(start)
for side,kind,t in [('W','K',(3,2)),('B','K',(4,4)),('W','R',(4,3)),('B','K',(3,4)),
                    ('W','R',(3,3)),('B','K',(4,4)),('W','K',(2,2)),('B','K',(5,4))]:
    p=move(p,side,kind,t)
assert p==start
data=dict(scope='Fixed guarded1x1 corner policy, ALL weak replies <=7 plies; fixed8-ply check-and-restore cycle only',
          corner_terminal_lengths=sorted(lengths),corner_distinct_edges=corner_edges,
          check_restore_cycle=edges,independent_direct_edge_replay=True,
          universal_class_or_RAW_history_certificate=False,
          finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
          source_hashes={str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in [Path(__file__),r/'scripts/krk_diagnostic.py']})
Path(__file__).with_name('small-box.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in data.items() if k not in ['corner_distinct_edges','check_restore_cycle','source_hashes']},indent=2))
