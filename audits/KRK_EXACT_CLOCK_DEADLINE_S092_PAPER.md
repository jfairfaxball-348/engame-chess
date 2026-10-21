# S092 separate clock-deadline paper audit

2026-10-21. Separate same-agent reasoning pass, not external review.

Attempted falsifications: strict<100 is too strong at a mating boundary;
100-h without the strong one-ply exception loses mate from h>=100; max1 on
weak turn would mask a genuinely empty nonmate domain at h>=99. The stated
turn-dependent bound avoids these three errors. Terminal mate has W0 even at
large h; other terminal endpoints cannot possess a non-goal winning certificate.

Capture/reset counterexample: a weak capture to KK resets the clock, but cannot
be a winning child for the strong material colour. Frozen child quietness
already proves this for EVERY certified edge, not a chosen favourable reply.
No new zeroing premise is assumed. Turns follow actual Legal, including flags.

At a nonterminal weak root h=99, intended claims matter even before clock100.
The frozen weak high-clock theorem includes that fact; current claims alone
would incorrectly permit an extra defending pair. It is applied to ongoing
winning weak roots only. A mate endpoint is taken separately before this use.
The recurrence100-(h+1)+1=100-h is used only at h<=98 (or strong h<=97).
No natural-subtraction identity is applied above its valid range.

Strong can ignore its own optional claim: the proof keeps its winning chosen
move and imposes no no-claim premise on strong nodes. Defended nodes retain
their original no-claim proof and ALL actual replies with a real witness.
Arbitrary incoming repetitions are not pruned or replaced by board-key data.

Verdict: local paper argument is sound as a NECESSARY deadline dependency.
It does not establish the all-history outcome formula, sufficiency of the
projected board distance, optimal mate distances, FIDE or WDL/DTZ. Formalise
only this exact needed statement; no standalone freeze or generic extension.
