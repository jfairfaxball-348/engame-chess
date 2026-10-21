"""Retain native command, complete output, elapsed time, exit and UTC."""
import datetime,json,subprocess,sys,time
from pathlib import Path
r=Path(__file__).resolve().parents[3];out=Path(__file__).resolve().parent
args=sys.argv[1:];start=time.monotonic();utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'diagnostic.log').write_bytes(p.stdout)
(out/'commands.json').write_text(json.dumps(dict(args=args,cwd=str(r),exit=p.returncode,
    elapsed_seconds=round(time.monotonic()-start,3),started_utc=utc,log='diagnostic.log'),indent=2)+'\n',encoding='utf-8',newline='\n')
print(p.stdout.decode('utf-8',errors='replace').replace('\r\n','\n'));sys.exit(p.returncode)
