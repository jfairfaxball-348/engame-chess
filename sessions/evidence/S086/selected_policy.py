"""One fixed CLOCK-FREE coordinate-policy trajectory. No class/game-value search.
The imported diagnostic's exhaustive entrypoint is NEVER called; only legal
ordinary ray/king move generation and the disclosed WallRun policy are used.
"""
import datetime,hashlib,json,sys,time
from pathlib import Path
root=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(root/'scripts'))
import krk_diagnostic as kd
from krk_wall_policy_diagnostic import WallRun

class Selected(WallRun):
    def __init__(self):
        super().__init__((0,0),(7,1),(1,2),kd.W,'local_interior_away')
        self.trace=[(0,dict(self.p))]
    def choose_defence(self,replies):
        self.trace.append((self.plies,dict(self.p)))
        s,_,_=self.squares()
        def key(p):
            v=p[(self.weak,'K')]
            # Immediate local coordinates only: low rank, away from strong king,
            # then prefer interior on ties, then stable file tie-break.
            return (v[1],-abs(v[0]-s[0]),-min(v[0],7-v[0]),v[0])
        reply=min(replies,key=key)
        self.trace.append((self.plies+1,dict(reply)))
        return reply

start=time.monotonic();run=Selected();failure=None;result=None
try:
    result=run.run()
except Exception as exc:
    failure=repr(exc)
if run.trace[-1][0]!=run.plies:run.trace.append((run.plies,dict(run.p)))
replay=[]
for index,((a,p),(b,q)) in enumerate(zip(run.trace,run.trace[1:])):
    assert b==a+1
    side=kd.W if index%2==0 else kd.B
    assert q in kd.legal_moves(p,side),(index,'illegal selected move')
    assert len(q)==3 and (kd.W,'R') in q
    changed=[(piece,p[piece],q[piece]) for piece in p if p[piece]!=q[piece]]
    assert len(changed)==1
    piece,src,dst=changed[0]
    replay.append(dict(ply=b,side=side,piece=piece[1],src=list(src),dst=list(dst)))
data=dict(scope='ONE selected clock-free ordinary coordinate-policy trajectory; NOT RAW admitted history or class proof',root=dict(strong_king=[0,0],rook=[7,1],weak_king=[1,2],turn='W',rights='none'),selector='immediate lowest rank, farthest king file, most interior on ties, file tie-break; no lookahead/evaluation',result=result,failure=failure,replayed_legal_edges=len(replay),moves=replay,trace=[dict(ply=n,pieces=[dict(colour=c,kind=k,square=list(sq)) for (c,k),sq in sorted(p.items())]) for n,p in run.trace],elapsed_seconds=round(time.monotonic()-start,3),finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),raw_history_compatibility='NOT ASSERTED; after claim/automatic thresholds this remains CLOCK-FREE ONLY',source_sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),root/'scripts/krk_diagnostic.py',root/'scripts/krk_check_phase_diagnostic.py',root/'scripts/krk_wall_policy_diagnostic.py']})
if failure is None:
    assert kd.in_check(run.p,kd.B) and not kd.legal_moves(run.p,kd.B)
    data['ends_in_model_mate']=True
(out/'selected-policy.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in data.items() if k not in ['moves','trace','source_sha256']},indent=2))
sys.exit(1 if failure else 0)
