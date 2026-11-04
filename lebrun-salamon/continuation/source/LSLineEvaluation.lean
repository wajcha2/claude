import LSConicCotangentTools

/-! Evaluation on a specified original line section commutes with the actual
module pullback. The statements apply to any sheaf and any scheme morphism;
no replacement frame or pointwise detection is used. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton
open LeBrunSalamon.Skeleton.ContactDerivativeIsoProof
open LeBrunSalamon.Construction.ConicModelSections
open LeBrunSalamon.Construction.Smoothing.CoordinateCharts

namespace LeBrunSalamon.LineEvaluation

def atSection {Y : Scheme} {E : OModule Y} (s : AlgebraicSection E) :
    dualSheaf E ⟶ structureModule Y :=
  dualMap s ≫ (DualFrame.unitIso Y).hom

theorem atSection_apply {Y : Scheme} {E : OModule Y}
    (s : AlgebraicSection E) (U : Y.Opens) (v : SectionsOn (dualSheaf E) U) :
    (atSection s).app U v = (dualEvaluation E).apply U v
      (Scheme.Modules.Hom.app s U (1 : RingSections Y U)) := by
  change (DualFrame.unitIso Y).hom.app U ((dualMap s).app U v) = _
  rw [DualFrame.unitIso_apply, dualMap_evaluate]

theorem pullSection_apply_one {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (s : AlgebraicSection E) (U : Y.Opens) :
    Scheme.Modules.Hom.app (pullSection f s) (f ⁻¹ᵁ U) (1 : RingSections X (f ⁻¹ᵁ U)) =
      pullLocalSection f E U (Scheme.Modules.Hom.app s U (1 : RingSections Y U)) := by
  have h := congrArg (fun k : structureModule Y ⟶
      (Scheme.Modules.pushforward f).obj (pullbackModule f E) =>
        Scheme.Modules.Hom.app k U (1 : RingSections Y U))
    (pullSection_adjoint f s)
  change Scheme.Modules.Hom.app (pullSection f s) (f ⁻¹ᵁ U)
      (f.app U (1 : RingSections Y U)) =
    pullLocalSection f E U (Scheme.Modules.Hom.app s U (1 : RingSections Y U)) at h
  simpa only [map_one] using h

/-- Evaluation on the same original section, before or after base change. -/
@[reassoc] theorem pullback {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (s : AlgebraicSection E) :
    (Scheme.Modules.pullback f).map (atSection s) ≫ unitPullbackMap f =
      dualBaseChange f E ≫ atSection (pullSection f s) := by
  apply PullbackPairProof.pullbackHom_ext f (dualSheaf E) (structureModule X)
  intro U v
  change (unitPullbackMap f).app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullback f).map (atSection s)).app (f ⁻¹ᵁ U)
        (pullLocalSection f (dualSheaf E) U v)) =
    (atSection (pullSection f s)).app (f ⁻¹ᵁ U)
      ((dualBaseChange f E).app (f ⁻¹ᵁ U) (pullLocalSection f (dualSheaf E) U v))
  rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
    unitPullbackMap_pullLocalSection, atSection_apply, atSection_apply,
    pullSection_apply_one, dualBaseChange_pullLocalSection]

/-- Evaluating a dual unit section on a scalar is multiplication by that
scalar after the fixed unit-dual identification. -/
theorem atScalar {Y : Scheme} (r : RingSections Y ⊤) :
    atSection (scalarSection r) = (DualFrame.unitIso Y).hom ≫ scalarSection r := by
  apply (cancel_epi (DualFrame.unitIso Y).inv).mp
  apply (sectionValue_bijective (structureModule Y)).injective
  let v := (DualFrame.unitIso Y).inv.app ⊤ (1 : RingSections Y ⊤)
  have hv : (dualEvaluation (structureModule Y)).apply ⊤ v (1 : RingSections Y ⊤) =
      (1 : RingSections Y ⊤) := by
    rw [← DualFrame.unitIso_apply]
    exact ExternalExchangeCoherenceProof.iso_hom_inv_app (DualFrame.unitIso Y) ⊤
      (1 : RingSections Y ⊤)
  change (atSection (scalarSection r)).app ⊤ v =
    Scheme.Modules.Hom.app (scalarSection r) ⊤ ((DualFrame.unitIso Y).hom.app ⊤ v)
  rw [atSection_apply]
  have hs : Scheme.Modules.Hom.app (scalarSection r) ⊤ (1 : RingSections Y ⊤) = r :=
    sectionFromValue_spec (E := structureModule Y) r
  rw [hs]
  calc
    (dualEvaluation (structureModule Y)).apply ⊤ v r =
        (dualEvaluation (structureModule Y)).apply ⊤ v (r • (1 : RingSections Y ⊤)) :=
      congrArg ((dualEvaluation (structureModule Y)).apply ⊤ v) (mul_one r).symm
    _ = r • (dualEvaluation (structureModule Y)).apply ⊤ v (1 : RingSections Y ⊤) :=
      map_smul _ r (1 : RingSections Y ⊤)
    _ = r := by rw [hv]; exact mul_one r
    _ = Scheme.Modules.Hom.app (scalarSection r) ⊤ ((DualFrame.unitIso Y).hom.app ⊤ v) := by
      rw [DualFrame.unitIso_apply, hv, hs]

/-- The scalar in an actual frame completely determines evaluation on the
section, with the original frame's dual comparison. -/
theorem atSection_frame {Y : Scheme} {E : OModule Y}
    (e : E ≅ structureModule Y) (s : AlgebraicSection E) (r : RingSections Y ⊤)
    (h : s ≫ e.hom = scalarSection r) :
    atSection s = (DualFrame.ofFrame e).hom ≫ scalarSection r := by
  have hs : s = scalarSection r ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  rw [hs]
  change dualMap (scalarSection r ≫ e.inv) ≫ _ = _
  rw [dualMap_comp, Category.assoc]
  change dualMap e.inv ≫ atSection (scalarSection r) = _
  rw [atScalar]
  rfl

instance atSection_isIso {Y : Scheme} {E : OModule Y}
    (s : AlgebraicSection E) [IsIso s] : IsIso (atSection s) := by
  change IsIso (DualFrame.ofFrame (asIso s).symm).hom
  infer_instance

end LeBrunSalamon.LineEvaluation
end
