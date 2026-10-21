"""Exact-source fresh Gate F, specialised to C048's8 declarations/9 modules."""
from pathlib import Path
r=Path(__file__).resolve().parents[3]
source=(r/'sessions/evidence/S078/verify.py').read_text(encoding='utf-8')
source=source.replace('S078','S082').replace('working-007','working-005').replace('==364','==382').replace('KRKHolding','KRKWinning').replace('len(modules)==11','len(modules)==9')
names=['forcing_actions','winning_policy','winning_safety','actual_win_of_force','policy_certificate','actual_win_iff_force','winning_maximal_goal','winning_mate_continuation']
lines=source.splitlines();assert sum(line.startswith('names=') for line in lines)==1
source='\n'.join('names='+repr(['EndgameChess.Rules.KRKWinning.'+n for n in names]) if line.startswith('names=') else line for line in lines)+'\n'
exec(compile(source,__file__,'exec'))
