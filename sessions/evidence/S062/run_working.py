import datetime,json,os,subprocess,time
from pathlib import Path
out=Path('sessions/evidence/S062'); env=os.environ.copy();env['ELAN_HOME']='/workspace/.tools/elan';env['PATH']=env['ELAN_HOME']+'/bin:'+env['PATH']; commands=[]
for args,log in [(['lake','build'],'working-build.log'),(['lake','env','lean','AxiomCheck.lean'],'working-axioms.log')]:
 start=time.monotonic();utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with (out/log).open('w') as f:r=subprocess.run(args,cwd='formal',env=env,stdout=f,stderr=subprocess.STDOUT)
 commands.append(dict(args=args,cwd='formal',logfile=log,exit=r.returncode,seconds=round(time.monotonic()-start,3),started_utc=utc));(out/'working-commands.json').write_text(json.dumps(commands,indent=2)+'\n')
 if r.returncode: print(log,'FAILED');break
 else: print(log,'PASS',flush=True)
