"""Own-source fresh Gate F for C051: five declarations, six complete modules."""
from pathlib import Path
r=Path(__file__).resolve().parents[3]
source=(r/'sessions/evidence/S078/verify.py').read_text(encoding='utf-8')
source=source.replace('S078','S087').replace('working-007','working-002').replace('==364','==395').replace('KRKHolding','KRKBox').replace('len(modules)==11','len(modules)==6')
names=['krk_box_reply_exists','krk_box_reply_region','krk_guarded_large_box_phase','krk_guarded_large_box_cost','krk_width_four_escort_cycle']
lines=source.splitlines()
assert sum(line.startswith('names=') for line in lines)==1
source='\n'.join('names='+repr(['EndgameChess.Rules.'+n for n in names]) if line.startswith('names=') else line for line in lines)+'\n'
exec(compile(source,__file__,'exec'))
