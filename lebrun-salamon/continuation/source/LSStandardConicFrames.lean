import LSHomVelocity

/-!
# The actual cotangent and logarithmic frames of the standard conic

The three source charts and the O(1,1) frames are fixed by the original
homogeneous quotient coordinates. The local coefficient below evaluates an
actual morphism out of the relative cotangent sheaf in precisely those
frames; it does not choose a coordinate derivation in place of that map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseTwentyNine
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.Skeleton

open LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.StandardConicDifferential

open Smoothing Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

variable (F : StandardSource)

/-- The actual homogeneous O(1,1) line on the represented conic. -/
def line : LineBundle F.source :=
  tensorLine (pullbackLine F.left (projectiveCoordinates 1).hyperplane)
    (pullbackLine F.right (projectiveCoordinates 1).hyperplane)

/-- The four actual homogeneous tensor-coordinate sections. -/
def coordinate (i j : Fin 2) : AlgebraicSection (line F).sheaf :=
  tensorSection (pullSection F.left ((projectiveCoordinates 1).coordinate i))
    (pullSection F.right ((projectiveCoordinates 1).coordinate j))

/-- Each displayed affine-plane chart is the actual open inclusion
after its already constructed isomorphism onto that open. -/
theorem modelMap_isOpenImmersion (k : Fin 3) :
    IsOpenImmersion (modelMap F k) := by
  have h : modelMap F k =
      (chartIso F k).inv ≫ (chartOpen F (leftIndex k) (rightIndex k)).ι :=
    (modelToChart_inclusion F k).symm
  rw [h]
  infer_instance

/-- The selected coordinate m_(leftIndex,rightIndex) is the unit
generator of the pulled line. Every composition and tensor comparison is
the canonical one used by the source's projective quotient coordinates. -/
def chartLineFrame (k : Fin 3) :
    pullbackModule (modelMap F k) (line F).sheaf ≅ structureModule Plane := by
  let c := modelMap F k
  let H := (projectiveCoordinates 1).hyperplane.sheaf
  letI := tensorPullbackComparison_isIso c
    (pullbackModule F.left H) (pullbackModule F.right H)
  exact (asIso (tensorPullbackComparison c
      (pullbackModule F.left H) (pullbackModule F.right H))).symm ≪≫
    tensorIso
      (compositionPullback c F.left
        (polynomialLine (leftPolynomial k) ≫ (ratioPoint (leftIndex k)).val)
        (modelMap_spec F k).2.1 H)
      (compositionPullback c F.right
        (polynomialLine (rightPolynomial k) ≫ (ratioPoint (rightIndex k)).val)
        (modelMap_spec F k).2.2 H) ≪≫
    productFrame (polynomialLine (leftPolynomial k))
      (polynomialLine (rightPolynomial k)) (leftIndex k) (rightIndex k)

theorem chartLineFrame_coordinate (k : Fin 3) (i j : Fin 2) :
    pullSection (modelMap F k) (coordinate F i j) ≫
        (chartLineFrame F k).hom =
      scalarSection
        (coefficient (leftIndex k) i (planeFunction (leftPolynomial k)) *
          coefficient (rightIndex k) j (planeFunction (rightPolynomial k))) := by
  letI := tensorPullbackComparison_isIso (modelMap F k)
    (pullbackModule F.left (projectiveCoordinates 1).hyperplane.sheaf)
    (pullbackModule F.right (projectiveCoordinates 1).hyperplane.sheaf)
  rw [coordinate, ← tensorPullbackComparison_onSections]
  change (tensorSection _ _ ≫
    tensorPullbackComparison (modelMap F k)
      (pullbackModule F.left (projectiveCoordinates 1).hyperplane.sheaf)
      (pullbackModule F.right (projectiveCoordinates 1).hyperplane.sheaf)) ≫ _ = _
  simp only [chartLineFrame, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc]
  change (tensorSection _ _ ≫ tensorMap _ _) ≫ _ = _
  rw [tensorSection_map,
    compositionPullback_sections, compositionPullback_sections]
  change tensorSection _ _ ≫
    (tensorMap (ratioPullFrame _ _).hom (ratioPullFrame _ _).hom ≫
      (TensorConstruction.leftUnitIso (structureModule Plane)).hom) = _
  rw [← Category.assoc, tensorSection_map, ratioPullFrame_coefficient,
    ratioPullFrame_coefficient, tensorScalarSection,
    polynomialLine_parameter, polynomialLine_parameter]

theorem chartLineFrame_generator (k : Fin 3) :
    pullSection (modelMap F k)
        (coordinate F (leftIndex k) (rightIndex k)) =
      (chartLineFrame F k).inv := by
  apply (cancel_mono (chartLineFrame F k).hom).mp
  rw [chartLineFrame_coordinate, Iso.inv_hom_id]
  simp [coefficient, scalarSection_one]

/-- The source cotangent comparison is the actual differential of the
open immersion, not a separately supplied identification. -/
def chartCotangentIso (k : Fin 3) :
    pullbackModule (modelMap F k) (cotangentSheaf F.parameter) ≅
      cotangentSheaf (modelMap F k ≫ F.parameter) := by
  letI := modelMap_isOpenImmersion F k
  letI := openImmersion_cotangentMap_isIso (modelMap F k) F.parameter
  exact asIso (cotangentMap (modelMap F k) F.parameter)

/-- A cotangent-to-dual-line map transported to the actual affine chart. -/
def chartForm
    (q : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf) (k : Fin 3) :
    cotangentSheaf (modelMap F k ≫ F.parameter) ⟶
      dualSheaf (pullbackModule (modelMap F k) (line F).sheaf) :=
  (chartCotangentIso F k).inv ≫
    (Scheme.Modules.pullback (modelMap F k)).map q ≫
      dualBaseChange (modelMap F k) (line F).sheaf

/-- Coefficient of the actual differential dX_i against the selected
O(1,1) generator on the k-th actual affine-plane chart. -/
def chartCoefficient
    (q : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf)
    (k : Fin 3) (i : Fin 2) : RingSections Plane ⊤ :=
  (dualEvaluation (pullbackModule (modelMap F k) (line F).sheaf)).apply ⊤
    ((chartForm F q k).app ⊤
      ((cotangentPresentation (modelMap F k ≫ F.parameter)).differential.apply ⊤
        (planeFunction (MvPolynomial.X i))))
    (sectionValue (chartLineFrame F k).inv)

/-- At the node: (u,-v). At the left outer chart: (0,-1).
At the right outer chart: (0,1). The first outer coordinate is the
base parameter, so its relative differential has zero coefficient. -/
def chartLogValue (k : Fin 3) (i : Fin 2) : RingSections Plane ⊤ :=
  if k = 0 then
    (if i = 0 then planeFunction (MvPolynomial.X 0)
      else -planeFunction (MvPolynomial.X 1))
  else if i = 0 then 0 else if k = 1 then -1 else 1

end LeBrunSalamon.Construction.StandardConicDifferential
end
