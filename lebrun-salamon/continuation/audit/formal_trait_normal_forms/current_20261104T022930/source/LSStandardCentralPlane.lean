import LSStandardConicZeroComparison
import LSPlaneConicZeroPresentation
import LSPolarizedProjectiveEmbedding
import LSNodalFibreComparison

/-! The actual central standard conic is the literal plane zero scheme
xy=0.  The comparison is proved from both all-test quotient presentations,
and its plane embedding preserves the originally selected O(1,1) line.
This candidate needs the normalized public coordinate constructor. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.Normalization

namespace LeBrunSalamon.StandardCentralPlane

variable (F : StandardSource)

theorem parameter_zero : StandardConicTriple.parameter (scalarPoint 0) =
    PlaneConicZeroPresentation.parameter ℂ 0 := by
  change (scalarPoint 0).appTop parameterFunction =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv 0
  exact SourceMarksProof.scalarPoint_zero_parameter.trans
    (map_zero ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)).symm

def sourcePresentation : PlaneConicPresentation.Presentation ComplexBase
    (PlaneConicZeroPresentation.parameter ℂ 0) :=
  PlaneConicPresentation.reparameterize
    (StandardConicTriple.presentation F (scalarPoint 0)) parameter_zero

/-- This is an isomorphism to the literal quadratic zero scheme,
including its nonreduced-test universal property. -/
def iso : CentralFiber F ≅ PlaneQuadratic.ZeroScheme ℂ (PlaneQuadratic.split ℂ 0) :=
  StandardConicZeroComparison.iso ℂ F (scalarPoint 0) 0 parameter_zero

@[reassoc] theorem iso_over :
    (iso F).hom ≫ PlaneQuadratic.projection ℂ (PlaneQuadratic.split ℂ 0) = centralBase F :=
  StandardConicZeroComparison.iso_over ℂ F (scalarPoint 0) 0 parameter_zero

/-- The chosen source line, not merely its degree, is identified with
the actual restricted plane hyperplane. -/
def lineIso : pullbackModule (iso F).hom
    (PlaneConicZeroPresentation.line ℂ 0).sheaf ≅ (NodalFibreComparison.centralLine F).sheaf :=
  (StandardConicZeroComparison.lineIso ℂ F (scalarPoint 0) 0 parameter_zero).symm

def embedding : PolarizedProjectiveEmbedding ℂ 2 (CentralFiber F) (centralBase F)
    (NodalFibreComparison.centralLine F) where
  hom := (iso F).hom ≫ PlaneQuadratic.inclusion ℂ (PlaneQuadratic.split ℂ 0)
  over_base := (Category.assoc (iso F).hom
    (PlaneQuadratic.inclusion ℂ (PlaneQuadratic.split ℂ 0))
    (StandardTautological.toSpec ℂ 2)).trans (iso_over F)
  closed := by
    letI : IsIso (iso F).hom := (iso F).isIso_hom
    exact IsClosedImmersion.comp (iso F).hom
      (PlaneQuadratic.inclusion ℂ (PlaneQuadratic.split ℂ 0))
  lineIso :=
    ((Scheme.Modules.pullbackComp (iso F).hom
      (PlaneQuadratic.inclusion ℂ (PlaneQuadratic.split ℂ 0))).app
        (StandardTautological.line ℂ 2).sheaf).symm ≪≫ lineIso F

theorem plane_embedding : Nonempty (PolarizedProjectiveEmbedding ℂ 2
    (CentralFiber F) (centralBase F) (NodalFibreComparison.centralLine F)) :=
  ⟨embedding F⟩

/-- Exact image comparison needed by the relative Cartier extraction:
the displayed embedding has precisely the split quadratic zero scheme. -/
theorem image_equation :
    (iso F).hom ≫ PlaneQuadratic.inclusion ℂ (PlaneQuadratic.split ℂ 0) =
      (embedding F).hom := rfl

theorem split_zero_nonzero : PlaneQuadratic.split ℂ 0 ≠ 0 := by
  intro h
  have h5 := congrFun h 5
  norm_num [PlaneQuadratic.split] at h5

end LeBrunSalamon.StandardCentralPlane
end
