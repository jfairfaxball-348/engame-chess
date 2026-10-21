"""Selected coordinate-policy lines only; no class graph or game-value search.
The old module's class-enumeration run() is NEVER called. Only legal_moves and
in_check are used. Every selected ordinary edge is independently replayed below.
"""
import collections,datetime,hashlib,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'scripts'))
import krk_diagnostic as kd

def direct(p,q,side):
    assert set(p)==set(q) and len(set(q.values()))==3
    changed=[k for k in p if p[k]!=q[k]]
    assert len(changed)==1 and changed[0][0]==side
    k=changed[0];src,dst=p[k],q[k]
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
    s,r,w=q[('W','K')],q[('W','R')],q[('B','K')]
    assert max(abs(s[0]-w[0]),abs(s[1]-w[1]))>=2
    if side=='B':
        if r[0]==w[0]:assert s[0]==r[0] and min(r[1],w[1])<s[1]<max(r[1],w[1])
        if r[1]==w[1]:assert s[1]==r[1] and min(r[0],w[0])<s[0]<max(r[0],w[0])

def toward_center(x):return x+1 if x<3 else x-1 if x>4 else x

class Line:
    def __init__(self,root,selector):
        self.p={('W','K'):root[0],('W','R'):root[1],('B','K'):root[2]}
        self.frame=[(0,1),(1,1)];self.plies=0;self.done=False
        self.trace=[];self.events=collections.Counter();self.selector=selector
        self.checkpoints=[]
    def f(self,s):return tuple(s[a] if d==1 else 7-s[a] for a,d in self.frame)
    def inv(self,s):
        p=[0,0]
        for i,(a,d) in enumerate(self.frame):p[a]=s[i] if d==1 else 7-s[i]
        return tuple(p)
    def squares(self):return tuple(self.f(self.p[k]) for k in [('W','K'),('W','R'),('B','K')])
    def swap(self):self.frame.reverse()
    def flip_x(self):a,d=self.frame[0];self.frame[0]=(a,-d)
    def margin(self):_,r,w=self.squares();return abs(r[0]-w[0])
    def action(self,kind,target,event):
        assert not self.done and self.plies<200
        q=dict(self.p);q[('W',kind)]=self.inv(target)
        assert q in kd.legal_moves(self.p,'W'),('illegal chosen move',self.squares(),kind,target,event)
        direct(self.p,q,'W');self.events[event]+=1
        self.trace.append(dict(ply=self.plies+1,side='W',kind=kind,source=self.p[('W',kind)],target=q[('W',kind)],event=event,frame=list(self.frame)))
        self.p=q;self.plies+=1
        replies=kd.legal_moves(self.p,'B')
        if not replies:
            assert kd.in_check(self.p,'B'),('stalemate',self.squares(),event)
            self.done=True;return
        assert all(set(p)==set(self.p) for p in replies),('rook capture branch',self.squares(),event)
        s,r,_=self.squares()
        def key(p):
            w=self.f(p[('B','K')])
            if self.selector=='low_away':return (w[1],-abs(w[0]-s[0]),-min(w[0],7-w[0]),w[0])
            if self.selector=='pressure':return (max(abs(w[0]-r[0]),abs(w[1]-r[1])),w[1],w[0])
            if self.selector=='up':return (-w[1],abs(w[0]-s[0]),w[0])
            return (w[1],w[0] if self.plies%4==1 else -w[0])
        q=min(replies,key=key);direct(self.p,q,'B')
        self.trace.append(dict(ply=self.plies+1,side='B',kind='K',source=self.p[('B','K')],target=q[('B','K')],event='selected reply',frame=list(self.frame)))
        self.p=q;self.plies+=1
    def far(self,event):
        _,r,w=self.squares();x=0 if w[0]>=4 else 7
        assert x!=r[0]
        self.action('R',(x,r[1]),event)
    def initial_prepare(self):
        start=self.plies;s,r,w=self.squares()
        t=max(r[1]-1-s[1],max(3-s[0],s[0]-4,0))
        while True:
            s,r,w=self.squares()
            if s[1]==r[1]-1 and 3<=s[0]<=4:break
            if self.margin()<2:self.far('initial rescue')
            s,r,w=self.squares()
            self.action('K',(toward_center(s[0]),s[1]+(s[1]<r[1]-1)),'initial king')
        if self.margin()<2:self.far('initial final rescue')
        assert self.plies-start<=2*(t+t//2+1)
        self.checkpoints.append(dict(phase='initial preparation',cost=self.plies-start,t=t))
    def restoration(self):
        start=self.plies;s,r,w=self.squares()
        assert r[1]-s[1]==2 and 1<=s[0]<=6
        if self.margin()<3:self.far('restore rescue')
        s,r,w=self.squares();self.action('K',(toward_center(s[0]),s[1]+1),'restore diagonal')
        s,r,w=self.squares()
        if not 3<=s[0]<=4:self.action('K',(toward_center(s[0]),s[1]),'restore horizontal')
        assert self.plies-start<=6
        self.checkpoints.append(dict(phase='restoration',cost=self.plies-start))
    def oriented_rook(self,d,wait):
        s,r,w=self.squares();u=w[0] if d==1 else 7-w[0];v=r[0] if d==1 else 7-r[0]
        if not wait:z=0 if u>=3 else 7
        elif u>=4:z=0 if v!=0 else 1
        elif u==3:z=0 if v!=0 else 7
        else:z=7 if v!=7 else 6
        self.action('R',(z if d==1 else 7-z,r[1]),'pursuit wait' if wait else 'pursuit normalize')
    def pursuit(self,budget):
        start=self.plies
        while True:
            s,r,w=self.squares();m=self.margin()
            assert r[1]==s[1]+1 and w[1]>r[1]
            if m>=2 and (w[1]>=r[1]+2 or w[0]==s[0]):break
            if w[0]==s[0]:self.far('aligned repair');continue
            d=1 if w[0]>s[0] else -1;delta=abs(w[0]-s[0])
            if delta==1:self.oriented_rook(d,True)
            elif m<3:self.oriented_rook(d,False)
            else:
                assert w[1]==r[1]+1
                self.action('K',(s[0]+d,s[1]),'pursuit king')
        assert self.plies-start<=budget,('pursuit budget',self.plies-start,budget,self.squares())
        self.checkpoints.append(dict(phase='pursuit',cost=self.plies-start,budget=budget))
    def advance(self):
        s,r,w=self.squares();assert self.margin()>=2
        if w[1]>=r[1]+2:self.action('R',(r[0],r[1]+1),'rank advance')
        else:
            assert w[0]==s[0] and w[1]==r[1]+1
            self.action('R',(r[0],w[1]),'opposition check')
    def central_direct(self):
        start=self.plies;s,r,w=self.squares();n=7-r[1]
        assert 3<=s[0]<=4 and r[1]==s[1]+1
        while not self.done:
            self.pursuit(10);self.advance()
            if not self.done:self.restoration()
        assert self.plies-start<=18*(n-1)+11
    def guarded(self):
        start=self.plies;s,r,w=self.squares();width=7-r[0]
        assert s==(r[0]-1,r[1]-1) and w[0]>r[0] and w[1]>r[1] and 2<=width<=4
        self.action('K',(s[0],r[1]),'guarded king entry');self.swap()
        s,r,w=self.squares();assert s[0]==r[0] and 1<=s[0]<=6 and w[0]>s[0]
        self.pursuit(18);self.advance()
        if not self.done:self.restoration();self.central_direct()
        assert self.plies-start<=18*width+3
    def central(self):
        start=self.plies;s,r,w=self.squares();n=7-r[1];ready=self.margin()>=2
        if n<=3:self.central_direct()
        else:
            if self.margin()<2:self.far('search repair')
            s,r,w=self.squares()
            if w[1]==r[1]+1 and abs(w[0]-s[0])==1:
                self.oriented_rook(1 if w[0]>s[0] else -1,True)
            s,r,w=self.squares()
            if w[1]>=r[1]+2 or w[0]==s[0]:
                self.advance()
                if not self.done:self.restoration();self.central()
            else:
                assert abs(w[0]-s[0])>=2
                d=1 if w[0]>s[0] else -1;target=(s[0]+d,r[1])
                if target!=r:self.action('R',target,'protected pivot')
                if d==-1:self.flip_x()
                self.guarded()
        cap=({1:11,2:29,3:47,4:61,5:73,6:85} if ready else {1:11,2:29,3:47,4:63,5:75,6:87})[n]
        assert self.plies-start<=cap,('central budget',self.plies-start,cap)
        self.checkpoints.append(dict(phase='central wall',n=n,ready=ready,cost=self.plies-start,budget=cap))
    def run(self):
        self.initial_prepare();self.central()
        assert self.done and self.plies<=95
        return dict(plies=self.plies,events=dict(self.events),checkpoints=self.checkpoints,trace=self.trace)

roots=[((0,0),(7,1),(1,2)),((0,0),(3,3),(2,4)),((7,0),(0,1),(6,2)),
       ((2,2),(3,3),(5,4)),((2,2),(3,3),(4,4)),((5,5),(6,6),(7,7)),
       ((0,0),(0,6),(3,7)),((3,0),(7,1),(3,2)),((6,4),(6,5),(7,6))]
results=[];failure=None;start=time.monotonic()
for root in roots:
    for selector in ['low_away','pressure','up','alternate']:
        run=Line(root,selector)
        try:result=run.run()
        except Exception as exc:
            failure=repr(exc);result=dict(plies=run.plies,events=dict(run.events),checkpoints=run.checkpoints,trace=run.trace)
        results.append(dict(root=root,selector=selector,result=result,failure=failure))
        if failure:break
    if failure:break
out=Path(__file__).with_name('central-wall.json')
data=dict(scope='NINE fixed disclosed roots, FOUR immediate coordinate selectors each; selected lines only, NOT class proof or RAW initial histories',
          failure=failure,elapsed_seconds=round(time.monotonic()-start,3),results=results,
          finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
          source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),ROOT/'scripts/krk_diagnostic.py']})
out.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(failure=failure,selected_lines=len(results),max_observed_plies=max(x['result']['plies'] for x in results),elapsed_seconds=data['elapsed_seconds']),indent=2))
sys.exit(1 if failure else 0)
