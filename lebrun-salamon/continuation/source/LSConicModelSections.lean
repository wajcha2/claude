import LSStandardConicDifferential
import LSConicCotangentTools

/-!
# The actual node of the standard conic

The fundamental-class map vanishes after pullback to the node.  The
proof uses its two fixed chart coefficients and the universal property
of relative differentials.  Affine localization faithfulness extends
the calculation from the two polynomial generators to every open.
No local freeness of the relative cotangent sheaf at the node is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.ConicModelSections

open Smoothing Smoothing.SourceAffineCharts
open StandardConicDifferential ContactDerivativeIsoProof

/-- The literal point u=v=0 in the nodal affine chart. -/
def origin : ComplexBase ⟶ Plane := planeFromFunctions (𝟙 ComplexBase) 0 0

theorem origin_coordinate (i : Fin 2) :
    origin.appTop (planeFunction (MvPolynomial.X i)) = 0 := by
  rw [origin, planeFromFunctions_apply, MvPolynomial.eval₂_X]
  simp

variable (F : StandardSource)

def node : ComplexBase ⟶ F.source := origin ≫ modelMap F 0

@[reassoc] theorem node_parameter : node F ≫ F.parameter = scalarPoint 0 := by
  change Smoothing.FixedEndsProof.BranchCharts.nodeSource F (𝟙 ComplexBase) 0 0 ≫
    F.parameter = scalarPoint 0
  rw [Smoothing.FixedEndsProof.BranchCharts.nodeSource_parameter, zero_mul,
    Smoothing.FixedEndsProof.BranchCharts.fromFunction_zero, Category.id_comp]

/-- Express the actual chart form in its fixed dual O(1,1) frame. -/
def nodeChartScalar : cotangentSheaf (modelMap F 0 ≫ F.parameter) ⟶
    structureModule Plane :=
  chartForm F (fundamentalClass F) 0 ≫ (DualFrame.ofFrame (chartLineFrame F 0)).hom

theorem nodeChartScalar_differential (i : Fin 2) :
    (nodeChartScalar F).app ⊤
      ((cotangentPresentation (modelMap F 0 ≫ F.parameter)).differential.apply ⊤
        (planeFunction (MvPolynomial.X i))) = chartLogValue 0 i := by
  change (DualFrame.ofFrame (chartLineFrame F 0)).hom.app ⊤
    ((chartForm F (fundamentalClass F) 0).app ⊤
      ((cotangentPresentation (modelMap F 0 ≫ F.parameter)).differential.apply ⊤
        (planeFunction (MvPolynomial.X i)))) = _
  rw [DualFrame.ofFrame_apply]
  exact fundamentalClass_chartCoefficient F 0 i

theorem nodeChartScalar_pullback_zero :
    (Scheme.Modules.pullback origin).map (nodeChartScalar F) = 0 := by
  let pi := modelMap F 0 ≫ F.parameter
  have hpi : pi ≫ affineLineToC = planeBase := by
    dsimp only [pi]
    rw [(modelMap_spec F 0).1, polynomialLine_over]
  have h : (Scheme.Modules.pullback origin).map (nodeChartScalar F) ≫
      unitPullbackMap origin = 0 := by
    apply plane_pulledCotangent_hom_ext pi affineLineToC hpi origin
    intro i
    change (unitPullbackMap origin).app (origin ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullback origin).map (nodeChartScalar F)).app (origin ⁻¹ᵁ ⊤)
        (pullLocalSection origin (cotangentSheaf pi) ⊤
          ((cotangentPresentation pi).differential.apply ⊤
            (planeFunction (MvPolynomial.X i))))) = 0
    rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
      nodeChartScalar_differential, unitPullbackMap_pullLocalSection]
    change origin.appTop (chartLogValue 0 i) = 0
    fin_cases i <;> simp [chartLogValue, origin_coordinate]
  letI := unitPullbackMap_isIso origin
  apply (cancel_mono (unitPullbackMap origin)).mp
  simpa only [zero_comp] using h

/-- The original source fundamental class has zero fiber at the actual
node.  Both coordinate generators are killed, before base change to any
nonreduced thickened node. -/
theorem fundamentalClass_node_zero :
    (Scheme.Modules.pullback (node F)).map (fundamentalClass F) = 0 := by
  have hform : (Scheme.Modules.pullback origin).map
      (chartForm F (fundamentalClass F) 0) = 0 := by
    apply (cancel_mono
      ((Scheme.Modules.pullback origin).mapIso (DualFrame.ofFrame (chartLineFrame F 0))).hom).mp
    rw [zero_comp]
    change (Scheme.Modules.pullback origin).map (chartForm F (fundamentalClass F) 0) ≫
      (Scheme.Modules.pullback origin).map (DualFrame.ofFrame (chartLineFrame F 0)).hom = 0
    rw [← Functor.map_comp]
    exact nodeChartScalar_pullback_zero F
  letI := dualBaseChange_isIso (modelMap F 0) (line F).locallyFree
  have hiter : (Scheme.Modules.pullback origin).map
      ((Scheme.Modules.pullback (modelMap F 0)).map (fundamentalClass F)) = 0 := by
    apply (cancel_epi
      ((Scheme.Modules.pullback origin).mapIso (chartCotangentIso F 0)).inv).mp
    apply (cancel_mono
      ((Scheme.Modules.pullback origin).map (dualBaseChange (modelMap F 0) (line F).sheaf))).mp
    simpa only [chartForm, Functor.mapIso_inv, Functor.map_comp,
      Category.assoc, comp_zero, zero_comp] using hform
  apply (cancel_epi (compositionPullback origin (modelMap F 0) (node F) rfl
    (cotangentSheaf F.parameter)).hom).mp
  rw [← Normalization.BundleGluing.compositionPullback_naturality,
    hiter, zero_comp, comp_zero]

end LeBrunSalamon.Construction.ConicModelSections

end
