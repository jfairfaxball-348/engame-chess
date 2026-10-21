"""Same exact-source native Gate F workflow, specialised to C047.
Usage: python verify.py OWN_SHA NEW_CLONE NEW_OUTPUT
"""
from pathlib import Path
r=Path(__file__).resolve().parents[3]
source=(r/'sessions/evidence/S078/verify.py').read_text(encoding='utf-8')
source=source.replace('S078','S080').replace('working-007','working-004').replace('==364','==374').replace('KRKHolding','KRKHighClock')
names=['arisen_no_weak_goal','good_step','good_no_weak_goal','strong_hold','weak_not_force','terminal_force_iff_goal','winning_child_quiet','weak_high_clock_not_force','strong_high_clock_iff','high_clock_exact_one']
lines=source.splitlines()
assert sum(line.startswith('names=') for line in lines)==1
source='\n'.join('names='+repr(['EndgameChess.Rules.KRKHighClock.'+n for n in names]) if line.startswith('names=') else line for line in lines)+'\n'
exec(compile(source,__file__,'exec'))
