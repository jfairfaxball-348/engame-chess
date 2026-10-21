"""Record every authoring command and its complete output, including failures."""
import datetime,json,subprocess,sys,time
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
r=Path(__file__).resolve().parents[3]; out=Path(__file__).resolve().parent
index=len(list(out.glob('working-*.log')))+1
log=out/f'working-{index:03}.log'; start=time.monotonic()
args=sys.argv[1:]
with log.open('wb') as f:
    p=subprocess.run(args,cwd=r/'formal',stdout=f,stderr=subprocess.STDOUT)
item=dict(args=args,cwd=str(r/'formal'),exit=p.returncode,seconds=round(time.monotonic()-start,3),finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),logfile=log.name)
with (out/'working-commands.jsonl').open('a',encoding='utf-8') as f:f.write(json.dumps(item)+'\n')
print(log.read_text(encoding='utf-8'));print(json.dumps(item))
sys.exit(p.returncode)
