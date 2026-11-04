# Point 1 acceptance preparation

This directory contains report-generation code prepared while the final compilation gate is still open. It is **not an acceptance event** and does not change the milestone ledger.

`finalize-point1.mjs` exports pure functions; none invokes Lean or writes project files. `finalizePoint1Ledger` requires a successful full current-source stock-native verification, exact source/runtime/dependency/recursive-stamp checks, the unchanged 190-module audited boundary, the complete 44-root/50-published-input audit, the fixed 30/133 accounting baseline, the exact archived verification bytes, and official successful-workflow artifact metadata. It promotes only OBL-001 through OBL-043 and the separately proved OBL-069. Definition validations and final theorem gates remain pending.

The supplied context must include `accepted_utc`, `workflow_conclusion`, `verification_path`, `verification_text`, `verification_sha256`, `preparation_record`, `artifact` (`id`, `name`, `run_id`, `sha256`), `acceptance_path`, and `previous_ledger_path`. The document/status functions additionally use the history and previous-status paths documented in their parameters. The caller must preserve the previous ledger and dated preparation/publication records, review the returned records, and publish them only after independently checking the official native evidence. Current source changes and native checks continue on diagnostic branches until then.

The prepared accounting after those gates pass is 74/133 (55.64%, rounded to 56%), leaving 47 original obligations, eight definition validations and four final gates. This is a checklist fraction, not an effort or time estimate. The unchanged unconditional frozen theorem remains a separate final requirement.
