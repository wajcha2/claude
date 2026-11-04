#!/usr/bin/env python3
"""Prepare an isolated, reversible OBL055 source proposal; grant no acceptance."""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parents[2]
ROOT = BASE / "github_checkpoint_audit/continuation_3h_infrastructure/repo/lebrun-salamon/continuation"
OUT = Path(__file__).resolve().parent / "root"
OUT.mkdir(parents=True, exist_ok=True)


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


probe = (BASE / "root_diagnostics/next3i/LSRelativeHomFunctorTranslationProbe.lean").read_text()
normal = (BASE / "published_leaf_recovery/next3i/LSRelativeHomBaseChangeEquiv.lean").read_text()
old = (ROOT / "source/RecompileExtensionsPart04Geometry.lean").read_text()
assert sha(probe) == "59cbcc588e537e2086481618563bee2d3a84944395dbd67b868bd2b4240431de"
assert sha(normal) == "b80a07b1bbc10c07697424cb647653ce8f71d3a58364f44c3be5ef41bcebaf4c"
assert sha(old) == "97e4af54a212b50d235ce936a9e87e91d6908da4c0395ed6830e73c844fbcd5e"

generic = probe[probe.index("abbrev sourceOver"):probe.index("/-- Base changing the target")]
comparison = probe[probe.index("/-- Base changing the target"):probe.index("end LeBrunSalamon.RelativeMorphismsFunctorPrototype")]
normalization = normal[normal.index("/-- A map from the base-changed source"):normal.index("end LeBrunSalamon.RelativeHomBaseChangeNormalization")]

published = """/-- **Published input (scheme-representer specialization):** Stacks Project,
Proposition 99.12.3 (0D1C), for the genuine all-test relative-morphism functor.
The source is proper, flat and of finite presentation; the target is separated
and of finite presentation. Finite presentation is written as local finite
presentation, quasi-compactness and quasi-separatedness (Definition29.22.1,
01TO). The theorem gives an algebraic-space representer locally of finite
presentation. A supplied scheme representing the same functor has that
property by Yoneda uniqueness and invariance under isomorphism. This input
asserts no scheme-existence conclusion from properness.

The displayed Stacks functor uses maps Y_T → Z_T over T. The actual functor
below uses maps Y_T → Z over S. Their explicit pullback equivalence, both
projection equations and naturality are proved in homBaseChangeEquiv above.
No contact, conic, project family or selected subfamily enters this input.
https://stacks.math.columbia.edu/tag/0D1C
https://stacks.math.columbia.edu/tag/0D19
https://stacks.math.columbia.edu/tag/01TO -/
theorem locallyOfFinitePresentation {S Y Z : Scheme.{0}}
    (pi : Y ⟶ S) (q : Z ⟶ S)
    (hproper : IsProper pi) (hflat : Flat pi)
    (hsourceLFP : LocallyOfFinitePresentation pi)
    (hsourceQC : QuasiCompact pi) (hsourceQS : QuasiSeparated pi)
    (hseparated : IsSeparated q) (htargetLFP : LocallyOfFinitePresentation q)
    (htargetQC : QuasiCompact q) (htargetQS : QuasiSeparated q)
    (H : Over S) (hrep : (morphismFunctor pi q).RepresentableBy H) :
    LocallyOfFinitePresentation H.hom := by
  sorry
"""
module = """import Mathlib

/-! The genuine relative-morphism functor and one generic published
finite-presentation input. All comparison maps retain both projections. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace LeBrunSalamon.RelativeMorphismsFunctor

""" + generic + normalization + """end LeBrunSalamon.RelativeMorphismsFunctor

namespace LeBrunSalamon.PublishedInputs.RelativeHom

open LeBrunSalamon.RelativeMorphismsFunctor

""" + published + """
end LeBrunSalamon.PublishedInputs.RelativeHom

end
"""

insertion = """namespace FunctorComparison

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.RelativeMorphismsFunctor

""" + comparison + """end FunctorComparison

"""
anchor = "namespace StandardInputs\n\n/-- Grothendieck, Bourbaki expose 221"
assert old.count(anchor) == 1
start = old.index("theorem locallyOfFinitePresentation {S Y : Scheme}")
end = old.index("\n\n/-- Standard deformation-theory corollary", start)
original = old[start:end]
assert original.endswith(":= by\n  sorry")
replacement = original[:-len("  sorry")] + """  exact FunctorComparison.locallyOfFinitePresentation_of_generic_input
    @LeBrunSalamon.PublishedInputs.RelativeHom.locallyOfFinitePresentation pi sS X H"""
edits = [
    {"old": "import LSSectionRepresentability\n", "new": "import LSRelativeHomFunctor\nimport LSSectionRepresentability\n"},
    {"old": anchor, "new": insertion + anchor},
    {"old": original, "new": replacement},
]
candidate = old
for edit in edits:
    assert candidate.count(edit["old"]) == 1
    candidate = candidate.replace(edit["old"], edit["new"], 1)
inverse = candidate
for edit in reversed(edits):
    assert inverse.count(edit["new"]) == 1
    inverse = inverse.replace(edit["new"], edit["old"], 1)
assert inverse == old
assert original.split(":= by")[0] == replacement.split(":= by")[0]
assert module.count("\n  sorry\n") == 1
assert generic in module and normalization in module and comparison in candidate

(OUT / "LSRelativeHomFunctor.lean").write_text(module)
(OUT / "RecompileExtensionsPart04Geometry.lean").write_text(candidate)
guard = {
    "schema": "lebrun-proposed-055-integration-v1",
    "scope": "Isolated source proposal only; no native production selection or obligation acceptance",
    "original_geometry_sha256": sha(old),
    "candidate_geometry_sha256": sha(candidate),
    "new_generic_module_sha256": sha(module),
    "tested_comparison_source_sha256": sha(probe),
    "tested_generic_normalization_source_sha256": sha(normal),
    "generic_block_sha256": sha(generic),
    "normalization_block_sha256": sha(normalization),
    "comparison_block_sha256": sha(comparison),
    "tested_proof_blocks_byte_identical": True,
    "original_055_header_sha256": sha(original.split(":= by")[0]),
    "original_055_header_byte_identical": True,
    "complete_inverse_byte_identical": True,
    "edits": edits,
    "new_published_inputs": ["LeBrunSalamon.PublishedInputs.RelativeHom.locallyOfFinitePresentation"],
    "new_input_scope": "Scheme-representer specialization of Stacks0D1C; generic target-base-change normalization proved explicitly",
    "source_imports": ["Mathlib"],
    "milestone_units_added": 0,
    "native_compilation_pending": True,
}
(OUT / "OBL055_INTEGRATION_GUARD.json").write_text(json.dumps(guard, indent=2, ensure_ascii=False) + "\n")
print(json.dumps({k: v for k, v in guard.items() if k != "edits"}))
