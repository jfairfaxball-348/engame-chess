# Reproducing S034 evidence

Use the checkout containing the S034 freeze record when validating that
snapshot. Later sessions may append additional rows or extend status documents;
that later main is not the twenty-row snapshot this validator checks.

`python verify.py REPO_ROOT NEW_OUTPUT_DIRECTORY NEW_CLONE_DIRECTORY` makes a
new GitHub clone at the pinned proof-source SHA, asserts no .lake before build,
runs the build and exact statement/axiom checks, and inventories source bytes.
The clone and completed output must not be reused. Activate the official pinned
Lean toolchain as documented; inherited proxy/TLS trust must remain enabled.

`python validate.py REPO_ROOT` checks the retained evidence, source and complete
module boundaries, exact declarations, ledger append/preservation, manifest
links, stable progress table and full next-session prompt without rebuilding.
These Python checks validate records, not chess mathematics. The actual proof
is checked by Lean, under the assumptions stated in the manifest. Hosted CI
was not observed.
