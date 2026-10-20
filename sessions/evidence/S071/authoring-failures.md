# Retained S071 authoring failure

working-build-01.log: append/current-count helper compiled. The lifting proof
needed explicit RawTrace.erase/append unfolding to identify the actual played
endpoint inside its winning/rank terms. The layer interface's erase projection
also needed an explicit change to RawHistoryLayer.erase before rewriting.
New-source-only normalization fixes; statement, model and all quantifiers
unchanged. working-build-02 passed; final aggregate/full runner passed.
Commands, exits, actual times and UTC in working-commands.jsonl. Fresh Gate F
is separate and no fresh retry is implied by authoring attempts.
