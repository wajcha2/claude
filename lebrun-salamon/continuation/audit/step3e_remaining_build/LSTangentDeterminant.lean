import RecompileBasePart04
import Lean.Util.CollectAxioms

/-!
# Determinant duality from the fundamental exterior map

This draft replaces the project-specific tangent determinant admission by one
generic published input and proves the complete specialization.

Source: Stacks Project, Lemma 48.29.1, Tag 0E9Y,
https://stacks.math.columbia.edu/tag/0E9Y . The lemma is stated for locally
ringed spaces, so it applies directly to the ordinary Zariski sheaves on a
scheme. It constructs the displayed map of exterior powers and says it is
invertible wherever the quotient is locally free of the difference rank.
The input below retains that map, assuming the quotient has that rank
everywhere. It does not assume a determinant-duality conclusion.

The identity sequence E → E → 0, its zero-rank quotient, the zeroth exterior
power, tensor cancellation, and the intrinsic tangent/cotangent translation
are proved below. No theorem about the tangent determinant is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.PublishedInputs.Determinant

/-- The globally locally-free case of the canonical map and invertibility
criterion in Stacks Project, Lemma 48.29.1 (Tag 0E9Y). All objects are genuine
module sheaves, and the conclusion provides a morphism with `IsIso`.
The rank inequality avoids the source's negative-exterior-degree convention. -/
theorem lciExteriorMap_isIso {X : Scheme} {r₁ r₀ : ℕ}
    (E₁ : AlgebraicVectorBundle X r₁) (E₀ : AlgebraicVectorBundle X r₀)
    (F : OModule X) (α : E₁.sheaf ⟶ E₀.sheaf) (β : E₀.sheaf ⟶ F)
    (hcomp : α ≫ β = 0)
    (hseq : (ShortComplex.mk α β hcomp).ShortExact)
    (hrank : r₁ ≤ r₀) (hF : IsLocallyFreeOfRank F (r₀ - r₁)) :
    ∃ δ : exteriorSheaf F (r₀ - r₁) ⟶
        tensorSheaf (exteriorSheaf (dualSheaf E₁.sheaf) r₁)
          (exteriorSheaf E₀.sheaf r₀), IsIso δ := by
  sorry

end LeBrunSalamon.PublishedInputs.Determinant

namespace LeBrunSalamon.TangentDeterminantProof

/-- A concrete free sheaf on the empty basis, with the genuine rank-zero proof. -/
def zeroRankBundle (X : Scheme) : AlgebraicVectorBundle X 0 :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) (Fin 0), freeSheaf_rank X 0⟩

theorem zeroRankBundle_isZero (X : Scheme) :
    IsZero (zeroRankBundle X).sheaf := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.freeHomEquiv (zeroRankBundle X).sheaf).injective
  funext i
  exact Fin.elim0 i

/-- The identity followed by the map to the actual zero-rank sheaf is short exact. -/
theorem identityZero_shortExact {X : Scheme} (E : OModule X) :
    (ShortComplex.mk (𝟙 E) (0 : E ⟶ (zeroRankBundle X).sheaf)
      (by simp)).ShortExact := by
  letI : Epi (0 : E ⟶ (zeroRankBundle X).sheaf) := by
    constructor
    intro W f g _
    exact (zeroRankBundle_isZero X).eq_of_src f g
  refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
  exact (ShortComplex.exact_iff_epi _ rfl).2 inferInstance

/-- The identity sequence gives a tensor inverse for the top exterior power. -/
theorem exteriorDual_tensor_exterior {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) :
    Nonempty (tensorSheaf (exteriorSheaf (dualSheaf E.sheaf) r)
      (exteriorSheaf E.sheaf r) ≅ structureModule X) := by
  have hF : IsLocallyFreeOfRank (zeroRankBundle X).sheaf (r - r) := by
    simpa only [Nat.sub_self] using (zeroRankBundle X).locallyFree
  obtain ⟨δ, hδ⟩ := PublishedInputs.Determinant.lciExteriorMap_isIso
    E E (zeroRankBundle X).sheaf (𝟙 E.sheaf) 0 (by simp)
    (identityZero_shortExact E.sheaf) (Nat.le_refl r) hF
  letI := hδ
  let e : exteriorSheaf (zeroRankBundle X).sheaf 0 ≅
      tensorSheaf (exteriorSheaf (dualSheaf E.sheaf) r)
        (exteriorSheaf E.sheaf r) := by
    simpa only [Nat.sub_self] using asIso δ
  obtain ⟨z⟩ := exteriorSheaf_zero (zeroRankBundle X).sheaf
  exact ⟨e.symm ≪≫ z⟩

/-- Tensor inverses of an invertible sheaf agree with its actual internal dual. -/
theorem inverse_iso_dual {X : Scheme} (L : LineBundle X) (D : OModule X)
    (h : Nonempty (tensorSheaf D L.sheaf ≅ structureModule X)) :
    Nonempty (D ≅ dualSheaf L.sheaf) := by
  obtain ⟨q⟩ := h
  obtain ⟨ev⟩ := line_dual_evaluation L
  let P := dualSheaf L.sheaf
  let A := L.sheaf
  exact ⟨(TensorConstruction.leftUnitIso D).symm ≪≫
    tensorIso ev.symm (Iso.refl D) ≪≫
    SheafTensor.associativityIso P A D ≪≫
    tensorIso (Iso.refl P) (TensorConstruction.commIso A D) ≪≫
    tensorIso (Iso.refl P) q ≪≫ TensorConstruction.rightUnitIso P⟩

/-- Determinant duality for every finite locally free sheaf on every scheme. -/
theorem determinantDual_iso {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) :
    Nonempty (exteriorSheaf (dualSheaf E.sheaf) r ≅
      dualSheaf (exteriorSheaf E.sheaf r)) := by
  exact inverse_iso_dual (determinantLine E)
    (exteriorSheaf (dualSheaf E.sheaf) r) (exteriorDual_tensor_exterior E)

/-- The requested intrinsic statement is the cotangent-bundle specialization. -/
theorem tangentDeterminant_anticanonical {d : ℕ}
    (X : SmoothProperComplexVariety d) :
    Nonempty ((determinantLine (intrinsicTangentBundle X)).sheaf ≅
      (anticanonicalLine X).sheaf) := by
  exact determinantDual_iso (intrinsicCotangentBundle X)

end LeBrunSalamon.TangentDeterminantProof

#print axioms LeBrunSalamon.TangentDeterminantProof.tangentDeterminant_anticanonical

/- Evidence-only check. Integration should keep this command in an audit module. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let target := ``LeBrunSalamon.TangentDeterminantProof.tangentDeterminant_anticanonical
  let mut todo : Array Name := #[target]
  let mut cursor := 0
  let mut seen : NameSet := ({} : NameSet).insert target
  let mut directSorry : Array Name := #[]
  while cursor < todo.size do
    let name := todo[cursor]!
    cursor := cursor + 1
    let some ci := env.checked.get.find? name | throwError "Missing dependency {name}"
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if let .inductInfo value := ci then
      deps := deps ++ value.ctors.toArray
    if deps.contains ``sorryAx then
      directSorry := directSorry.push name
    for dep in deps do
      if !seen.contains dep then
        seen := seen.insert dep
        todo := todo.push dep
  let old : Name := `LeBrunSalamon.PublishedInputs.Step3e.tangentDeterminant_anticanonical
  let generic := ``LeBrunSalamon.PublishedInputs.Determinant.lciExteriorMap_isIso
  if seen.contains old then
    throwError "The old project-specific tangent determinant admission is still used."
  if !seen.contains generic then
    throwError "The expected generic Stacks exterior map is absent from the proof."
  logInfo m!"TANGENT_DETERMINANT_DEPENDENCIES old_admission_used={seen.contains old} generic_stacks_leaf_used={seen.contains generic} all_constants={seen.toArray.size}"
  logInfo m!"DIRECT_SORRY_DECLARATIONS\n{String.intercalate "\n" (directSorry.toList.map Name.toString)}"

end
