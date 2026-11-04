import LSFiniteTypeSpreading
import LSContactLineTests
import LSFamilyDescentReparametrization
import LSFamilyReparametrizationFibres

/-!
# Reparametrization in families and over arbitrary fields

Complex-point detection is used only on reduced schemes locally of
finite type over C.  A field-valued source automorphism is first spread
while retaining the original parameterized family; the tensor identities
then return along the actual field-valued base map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FamilyBivectors

namespace FamilyReparametrization

open Parametrized

variable (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)

variable (e : Source P sB ≅ Source P sB)
variable (he : e.hom ≫ parameter P sB = parameter P sB)

variable {n : ℕ} (X : ContactFanoManifold n)
variable (f : Source P sB ⟶ X.variety.scheme)
variable (hf : f ≫ X.variety.structureMap = parameter P sB ≫ sB)
variable (C : NonconstantFamily P sB X f)
variable (g : Source P sB ⟶ X.variety.scheme)
variable (hg : g ≫ X.variety.structureMap = parameter P sB ≫ sB)
variable (hcomp : e.hom ≫ f = g)

include C in
/-- Actual reparametrization invariance over a reduced locally
finite-type base; the only point test is on its complete source square. -/
theorem leftSection_finiteType [AlgebraicGeometry.IsReduced B] [LocallyOfFiniteType sB] :
    pullSection (squareMap P sB e he) (ParametrizedContact.leftSection P sB X f hf) ≫
        (compositionPullback (squareMap P sB e he)
          (ParametrizedContact.evaluationSquare P sB X f hf)
          (ParametrizedContact.evaluationSquare P sB X g hg)
          (squareMap_evaluation P sB e he X f hf g hg hcomp)
          (movingPairBundleLeft X.variety X.contact)).hom =
      ParametrizedContact.leftSection P sB X g hg := by
  letI : AlgebraicGeometry.IsReduced (Square P sB) := square_reduced P sB
  letI : LocallyOfFiniteType (squareToC P sB) := square_locallyOfFiniteType P sB
  apply sections_eq_of_fibres P sB
    (MovingPair.leftBundle (ParametrizedContact.evaluationSquare P sB X g hg))
  intro t
  let D := reparametrizedFamily P sB e he X f C g hcomp
  let a := fibreIso P sB e he t
  have ha : a.hom ≫ P.structureMap = P.structureMap := fibreIso_overC P sB e he t
  have hg' : (D.curve t).map = a.hom ≫ (C.curve t).map := rfl
  exact SectionTransport.reparametrization_on_fibre (fibreSquare P sB t)
    (squareMap P sB e he) (curveSquareMap P (Reparametrization.curve P a ha))
    (fibreSquare_squareMap P sB e he t)
    (ParametrizedContact.evaluationSquare P sB X f hf)
    (ParametrizedContact.evaluationSquare P sB X g hg)
    (squareMap_evaluation P sB e he X f hf g hg hcomp)
    (curveSquareMap P (C.curve t)) (curveSquareMap P (D.curve t))
    (fibreSquare_evaluation P sB X f hf C t) (fibreSquare_evaluation P sB X g hg D t)
    (Reparametrization.square_comp P a ha X (C.curve t) (D.curve t) hg')
    (ParametrizedContact.leftSection P sB X f hf)
    (ParametrizedContact.leftSection P sB X g hg)
    (Curve.leftSection P X (C.curve t)) (Curve.leftSection P X (D.curve t))
    (left_at_fibre P sB X f hf C t) (left_at_fibre P sB X g hg D t)
    (Reparametrization.leftSection P a ha X (C.curve t) (D.curve t) hg')

end FamilyReparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
