"""Exact-source fresh Gate F specialised to C049's8 declarations/9 modules."""
from pathlib import Path
r=Path(__file__).resolve().parents[3]
source=(r/'sessions/evidence/S078/verify.py').read_text(encoding='utf-8')
source=source.replace('S078','S084').replace('working-007','working-005').replace('==364','==390').replace('KRKHolding','KRKFresh').replace('len(modules)==11','len(modules)==9')
names=['key_material','prefix_region','clock_zero_counts','winning_move_material','restricted_append','restricted_lifting','clock_zero_sub100','clock_zero_axis_wall']
lines=source.splitlines();assert sum(line.startswith('names=') for line in lines)==1
source='\n'.join('names='+repr(['EndgameChess.Rules.KRKFresh.'+n for n in names]) if line.startswith('names=') else line for line in lines)+'\n'
exec(compile(source,__file__,'exec'))
