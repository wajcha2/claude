# Compiler compatibility repairs after CI 41714131927

These focused checks use the exact accepted dependency snapshot of commit `0e7a654645d92fe82473e358a925b47101305e97`. They validate candidates against that frozen interface. Changed ancestors in the current main graph still require rebuilding.

- **LSClassicalActions passed in 4.381 s.** Missing namespace opens and composition association were repaired. The current source bytes match the passing input.
- **LSBranchRamification passed in 5.582 s.** All seven original diagnostics were resolved through explicit equality transport, coercions and namespace qualification. The current source bytes match the passing input.
- **LSProductGeometry remains pending.** The original CI reached the 2,000,000-heartbeat cap. A scoped 6,000,000-heartbeat candidate reached a 300 s local wall limit. The refined candidate uses actual principal-open affineness directly and avoids unnecessary Noetherian-instance synthesis; its bounded diagnostic reached 90.327 s without a source diagnostic. No native pass is claimed. The current source differs from that tested candidate only in the status comment.

Theorem types and admission boundaries are unchanged by these compatibility repairs. Previous receipts, exact logs, tested and current hashes, and the final bounded-run validation are retained. The newer mathematical ancestor edits make full current-source replay a separate gate.
