# Transitive ancestry bound to reused proof artifacts

The original local driver could reuse a downstream artifact after a transitive source changed if a rebuilt intermediate artifact happened to retain identical bytes. A simulated compiler fixture reproduced that failure: A changed, B rebuilt to identical bytes, and C was wrongly reused. The repaired driver binds every receipt and explicit seed to the recursive source/import/output ancestry and rechecks C. No Lean compiler was used for this tooling test.

Three explicit-seed cases and ten strict-cache-restoration cases pass, including unchanged reuse, transitive changes, old unstamped seed rejection, and verified migration of unchanged historical CI receipts. A new ancestry stamp is derived during strict CI restoration only after the complete original graph has been validated. Historical native receipts, logs, outputs, and source snapshots are preserved unchanged. Separate V2 seed files provide the additional derived metadata.

The existing GitHub runs use immutable source checkouts and a cache preflight that already recursively rejects changed source ancestry. The current early/full stages also share the same fixed snapshot. Their recorded results are unaffected. This repair protects future local incremental work; it creates no mathematical proof or additional milestone acceptance.
