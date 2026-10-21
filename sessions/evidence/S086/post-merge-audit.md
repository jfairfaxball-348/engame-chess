# S086 post-merge provenance audit

The first publication b1385f8495fd244d7448cbbd5372cdd1607933e0 matched local main,
origin/main and the session branch. Git checkout converted selected_policy.py
from its EXECUTED LF bytes to CRLF. Original runtime SHA256 in selected-policy.json
is retained unchanged; its LF Git blob at that first publication matches exactly.
All three imported source files still match their original raw runtime hashes.
The validator now accepts a mismatch only after comparing the exact first-
publication Git blob and proving the recorded hash is precisely its LF or CRLF
encoding. This does not permit source-content changes or alter diagnostic results.

The mutable candidate register's EC-C046-C049 notes also labelled pre-freeze
counts as if current. They now explicitly distinguish their historical Gate F
counts from the subsequent freeze milestones. The live total remains46. No
frozen theorem, manifest, ledger row, Lean source or proof-status promotion.

The first rerun then caught double-CR output in the now-tracked native check
log: decoded CRLF subprocess text had been written with another Windows newline
conversion. Full failure retained in validation-newline-failure.json. Validator
output now explicitly normalizes subprocess CRLF and writes LF; source/diagnostic
runtime hashes are unchanged. This is a packaging log repair, not a proof change.
