# S025 Gate Z verification for EC-T0008 and EC-T0009

Fresh, independent rerun for the two simultaneous freezes. Exact proof-source: `fca2ca88c8391b1d2bd49c3db9f2fa04258a4a87`. Gate Z completed UTC: `2026-10-19T07:11:01Z`.

- `lake_build.log`: fresh GitHub checkout, no `.lake` before build, official Lean 4.35.0; 26 jobs, 274.68 seconds, exit 0.
- `axioms.log`: all 180 declared reports within standard allowed axiom sets; exact report content matches S024 Gate F, rerun here.
- `statements.log`: exact `#check` output for all 19 S024 declarations and witnesses; `statement-commands.txt` records the commands run via a temporary file outside the proof checkout. No source was edited.
- `source-sha256.txt`: all Lean sources in the clean checkout, checked against the freeze working tree.
- `forbidden_tokens.log`: zero forbidden proof escapes in the four S024 modules.
- `python-tests.log`: all 33 tests passed. The ledger check is structural only and is recorded in the session closeout.

The build uses the host executable-path compatibility shim already retained with EC-T0007; see `../EC-T0007/verification-environment.md`. Only denied own-process executable-path discovery is redirected to `/proc/self/exe`. The official compiler, kernel routines and all proof sources remain unmodified. Ordinary hosts can omit the shim.

These logs are new S025 Gate Z evidence. The earlier S024 Gate F records remain unchanged. Remote CI is not asserted as observed. Both freezes reference the already existing proof commit, not their own manifest commit.
