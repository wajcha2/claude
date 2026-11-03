# Tangent determinant translation

The standalone proof and dependency audit passed the pinned native Lean kernel
on 2026-11-03 at 20:58:31 UTC in 6.855 seconds. Its four imported project
ancestors, Base01–04, were exact source/dependency/output-hash validated outputs
from GitHub CI run 41685948946. All five selected modules passed the replay
driver's final source, import, dependency, output, and runtime checks.

The proof obtains determinant duality by applying the generic exterior-power
map to the identity sequence E → E → 0, then proving the zero-rank and tensor
cancellation steps. The only new admitted input is the globally locally-free
case of [Stacks Project Lemma 48.29.1, Tag 0E9Y](https://stacks.math.columbia.edu/tag/0E9Y).
That lemma is stated for locally ringed spaces and therefore applies directly
to ordinary sheaves on a scheme. It provides the same exterior-power morphism
and its invertibility where the quotient is locally free of the difference
rank. The rank inequality is explicit in the Lean signature.

The dependency audit traversed 33,148 constants. It verified that the old
project-specific tangent determinant admission is absent from the new proof's
closure and that the generic Stacks input is present. The other direct sorry
dependencies are exterior local freeness, smooth cotangent rank, exterior
representability, and cotangent representability. This receipt does not
independently audit those existing inputs.

`LSTangentDeterminant.lean` is the exact compiled draft, including its audit
command. Its SHA-256 is
`44fcd39532d88f6fa8e72ade95f391f1ae092973c947ab3a66c017e16bb6967b`.
The output olean hash is recorded in `receipt.json`; binaries remain in the
local diagnostic build. The local compiler used the already documented
explicit executable-path adapter with the unchanged pinned kernel and libraries.

The proof has also been inserted into `source/RecompileBasePart04.lean`, and
the former admitted theorem now calls the proved translation. The exact edit
is in `INTEGRATION.patch`. The integrated Base04 module and its reverse
dependency cone require a fresh replay; this standalone receipt is not a
claim that the newly integrated full source graph has passed.
