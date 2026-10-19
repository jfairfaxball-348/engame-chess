# S031 verification procedure

verify.py records the exact-source clone/build/axiom/statement/hash/scan procedure. Source sessions are S028, S029 and S030 with full SHAs in the evidence index. It activates the official preinstalled toolchain at /workspace/.tools/elan and uses /workspace/engame-chess. No toolchain, proof source or project dependency is patched. It asserts that the new clone has no formal/.lake before building.

The first three invocations ran concurrently; S029 was killed by the memory limit, S028 was deliberately stopped to release memory, and S030 completed successfully. Final S028 and S029 invocations used S031_CLONE_SUFFIX=-retry and ran sequentially. Failed logs remain separate. Never treat an interrupted run as certification or a cached rebuild as a fresh clone.

The retained verifier includes a corrected nonaggregate source comparison: later additive EndgameChess.lean/AxiomCheck.lean imports differ from earlier anchors, whose exact bytes are retained in each inventory. No source mismatch or proof correction was required. The original S030 run had no aggregate mismatch and completed successfully.

validate.py checks the final records, hashes, immutable baseline, ledger prefix, statement/axiom coverage, stable table, full prompt and local links. These are structural checks, not mathematical proofs.

These scripts are provenance, not permission to overwrite frozen evidence. A new reproduction must use new clone/output directories and retain the full source SHA, absence-of-cache precondition, commands and observed exits. Do not rerun historical certifications during routine later sessions.
