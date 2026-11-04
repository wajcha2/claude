from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "contingency_v5"
OUT.mkdir(exist_ok=True)
BASE = ROOT / "LSFormalArcComparisonFiveCandidateV4.lean"
EXPECTED = "4e93758a009dada71a46f2bc32ab314bb57b21fd8ed9e095ae3c1c2cb22088ab"

def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()

base = BASE.read_text()
assert sha(base) == EXPECTED

def inferred(side):
    return f'''private def nodal_{side}_regular_inferred
    (S : Smoothing.StandardSource) (a : Coefficients) (ha : a ≠ 0)
    (u : Source F (baseArc F gamma) ≅ Model S a)
    (hu : u.hom ≫ modelProjection S a = parameter F (baseArc F gamma))
    (ell : (TraitPullback.line F (baseArc F gamma)).sheaf ≅
      pullbackModule u.hom (modelLine S a).sheaf)
    (c : Coefficients)
    (hc : ContactScalar.morphism X S a (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu) =
    GlobalScalars.scalarEnd (modelLine S a).sheaf
      ((modelProjection S a).appTop (coefficientSection a)) ≫
        RegularModel.dividedContact X S a (Transport.evaluation F gamma u)
          (Transport.line F gamma u ell) c)
    (hU : Dense (gamma.val ⁻¹ᵁ F.smoothSquareOpen : Set Trait)) :=
  {side}_regular_of_model Q gamma (modelProjection S a) u hu
    (ModelGenericComparison.genericParametrization S a ha)
    (ModelGenericComparison.genericParametrization_isPullback S a ha)
    hU
    (RegularModel.{side}Section X S a (Transport.evaluation F gamma u)
      (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
      (Transport.line F gamma u ell) c)
    (nodal_{side}_normalized F gamma S a ha u hu ell c hc)

'''

insertion = inferred("left") + inferred("right")
anchor = "theorem nodal_regular (S : Smoothing.StandardSource)"
assert base.count(anchor) == 1
old_body = '''  obtain ⟨c, hc, _⟩ := Nodal.common_exists F gamma S a u hu ell ha
  let k := ModelGenericComparison.genericParametrization S a ha
  let hk := ModelGenericComparison.genericParametrization_isPullback S a ha
  constructor
  · apply left_regular_of_model Q gamma (modelProjection S a) u hu k hk hU
      (RegularModel.leftSection X S a (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c)
    exact nodal_left_normalized F gamma S a ha u hu ell c hc
  · apply right_regular_of_model Q gamma (modelProjection S a) u hu k hk hU
      (RegularModel.rightSection X S a (Transport.evaluation F gamma u)
        (Transport.evaluation_overC F gamma (modelProjection S a) u hu)
        (Transport.line F gamma u ell) c)
    exact nodal_right_normalized F gamma S a ha u hu ell c hc
'''
new_body = '''  obtain ⟨c, hc, _⟩ := Nodal.common_exists F gamma S a u hu ell ha
  exact ⟨nodal_left_regular_inferred Q gamma S a ha u hu ell c hc hU,
    nodal_right_regular_inferred Q gamma S a ha u hu ell c hc hU⟩
'''
assert base.count(old_body) == 1
candidate = base.replace(anchor, insertion + anchor, 1).replace(old_body, new_body, 1)
assert candidate.count(insertion + anchor) == 1
assert candidate.count(new_body) == 1
inverse = candidate.replace(new_body, old_body, 1).replace(insertion + anchor, anchor, 1)
assert inverse == base

names = ["smooth_regular", "nodal_regular", "regular", "left_regular", "right_regular"]
def header(text, name):
    start = re.search(r"(?m)^theorem " + re.escape(name) + r"\b", text).start()
    return text[start:text.index(" :=", start) + 3]

headers = []
for name in names:
    before = header(base, name)
    after = header(candidate, name)
    assert before == after
    headers.append({"name": name, "sha256": sha(before), "unchanged": True})

prefix_end = base.index("end NodalNormalization") + len("end NodalNormalization")
prefix = base[:prefix_end]
assert candidate[:prefix_end] == prefix
ingredient_names = re.findall(r"(?m)^private theorem (\w+)", prefix)
assert len(ingredient_names) == 16
assert re.findall(r"(?m)^theorem (\w+)(?:[ \t]*\(|[ \t]*$)", candidate) == names
assert len(re.findall(r"(?m)^private (?:theorem|def) (\w+)", candidate)) == 18
for token in ["sorry", "admit", "axiom", "unsafe"]:
    assert not re.search(r"\b" + token + r"\b", candidate)
assert "hLeft" not in candidate and "hRight" not in candidate
assert BASE.read_text() == base

source_path = OUT / "LSFormalArcComparisonFiveCandidateV5.lean"
source_path.write_text(candidate)
(OUT / "INFERRED_NODAL_REGULARITY_DEFS.lean.txt").write_text(insertion)
guard = {
    "schema": "arc-five-v5-contingency-source-guard-v1",
    "status": "UNCOMPILED off-graph contingency only; no proof or acceptance claim",
    "dispatch_policy": "Use only after actual real-parent V4 fails or caps; discard untested if V4 passes.",
    "base_path": str(BASE),
    "base_sha256": sha(base),
    "candidate_path": str(source_path),
    "candidate_sha256": sha(candidate),
    "candidate_git_blob_sha1": hashlib.sha1(b"blob " + str(len(candidate.encode())).encode() + b"\0" + candidate.encode()).hexdigest(),
    "inverse_byte_exact": inverse == base,
    "unchanged_public_headers": headers,
    "unchanged_checked_ingredient_count": 16,
    "unchanged_checked_ingredient_names": ingredient_names,
    "unchanged_checked_prefix_sha256": sha(prefix),
    "new_private_proof_definitions": ["nodal_left_regular_inferred", "nodal_right_regular_inferred"],
    "new_assumptions_or_admissions": 0,
    "changed_original_proof_bodies": ["nodal_regular"],
    "unchanged_original_proof_bodies": ["smooth_regular", "regular", "left_regular", "right_regular"],
    "scope": "Same c,hc from Nodal.common_exists, same hU, model sections, normalizations, parametrization and pullback proof. Only complete regularity proof applications are named separately with inferred result types.",
    "patches": [
        {"name": "insert_two_inferred_regular_proofs", "before": anchor, "after": insertion + anchor, "match_count": 1},
        {"name": "assemble_nodal_pair_from_named_proofs", "before": old_body, "after": new_body, "match_count": 1}
    ],
}
guard_path = OUT / "V5_CONTINGENCY_GUARD.json"
guard_path.write_text(json.dumps(guard, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"source": str(source_path), "source_sha256": sha(candidate), "git_blob_sha1": guard["candidate_git_blob_sha1"], "guard": str(guard_path), "guard_sha256": sha(guard_path.read_text()), "private_ingredients_unchanged": 16, "original_headers_unchanged": len(headers), "inverse_exact": inverse == base, "compiled": False}, indent=2))
