import LSHomVelocity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFour
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Lines
open LeBrunSalamon.Construction.Lines.FamilyVariation
namespace LeBrunSalamon.Step3fScalarCheck
variable {Y : Scheme}
theorem homSection_scalar {E : OModule Y} (h : E ⟶ structureModule Y)
    (c : RingSections Y ⊤) :
    TwoChartSections.homSection (h ≫ GlobalScalars.scalarEnd (structureModule Y) c) =
      TwoChartSections.homSection h ≫ GlobalScalars.scalarEnd (dualSheaf E) c := by
  apply ContactDerivativeIsoProof.dual_hom_ext
  intro U r e
  change RingSections Y U at r
  let t : RingSections Y U :=
    Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c
  let hs : SectionsOn (dualSheaf E) U :=
    Scheme.Modules.Hom.app (TwoChartSections.homSection h) U r
  have heval : (dualEvaluation E).apply U hs e = r • h.app U e :=
    homSection_evaluate h U r e
  have hlinear : (dualEvaluation E).apply U (t • hs) e =
      t • ((dualEvaluation E).apply U hs e) := by
    exact congrArg
      (fun k : SectionsOn E U →ₗ[RingSections Y U] SectionsOn (structureModule Y) U =>
        k e)
      (map_smul ((dualEvaluation E).apply U) t hs)
  change (dualEvaluation E).apply U
      (Scheme.Modules.Hom.app
        (TwoChartSections.homSection (h ≫ GlobalScalars.scalarEnd (structureModule Y) c)) U r) e =
    (dualEvaluation E).apply U (t • hs) e
  calc
    _ = r • (h ≫ GlobalScalars.scalarEnd (structureModule Y) c).app U e :=
      homSection_evaluate (h ≫ GlobalScalars.scalarEnd (structureModule Y) c) U r e
    _ = r • (t • h.app U e) := rfl
    _ = t • (r • h.app U e) := smul_comm r t (h.app U e)
    _ = t • ((dualEvaluation E).apply U hs e) :=
      congrArg (fun z : SectionsOn (structureModule Y) U => t • z) heval.symm
    _ = _ := hlinear.symm

end LeBrunSalamon.Step3fScalarCheck
end
