"""Record complete authoring output, command, native exit/time and UTC."""
import datetime,json,subprocess,sys,time
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
r=Path(__file__).resolve().parents[3];out=Path(__file__).resolve().parent
index=len(list(out.glob('working-*.log')))+1;log=out/f'working-{index:03}.log'
args=sys.argv[1:];start=time.monotonic();utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
with log.open('wb') as f:p=subprocess.run(args,cwd=r/'formal',stdout=f,stderr=subprocess.STDOUT)
item=dict(args=args,cwd=str(r/'formal'),exit=p.returncode,seconds=round(time.monotonic()-start,3),started_utc=utc,log=log.name)
with (out/'commands.jsonl').open('a',encoding='utf-8',newline='\n') as f:f.write(json.dumps(item)+'\n')
print(log.read_text(encoding='utf-8'));print(json.dumps(item));sys.exit(p.returncode)
