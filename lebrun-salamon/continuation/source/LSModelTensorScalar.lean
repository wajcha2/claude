import LSModelGenericParametrization
/-!
# Whole-generic-square comparison for the actual conic model

The dense test used below is the residue-field point of the integral
generic square.  The final equalities are on the complete square,
including the diagonal and both outer endpoints.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirty
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

open StableMaps.FormalArcs StableMaps.FormalArcs.ModelGeometry
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts
open FamilyBivectors

variable (F : Smoothing.StandardSource) (a : Coefficients)

variable {d : ℕ} (X : SmoothProperComplexVariety d)
variable (e : Model F a ⟶ X.scheme)
variable (he : e ≫ X.structureMap = modelProjection F a ≫ toC)

namespace TensorScalar

theorem right {Y : Scheme} {E E' H H' : OModule Y}
    (r : RingSections Y ⊤) (u : E ⟶ E') (v : H ⟶ H') :
    tensorMap u (GlobalScalars.scalarEnd H r ≫ v) =
      GlobalScalars.scalarEnd (tensorSheaf E H) r ≫ tensorMap u v := by
  apply ((tensorPresentation E H).universal _).1
  apply sheafBilinearMap_ext
  intro U x y
  change (tensorMap u (GlobalScalars.scalarEnd H r ≫ v)).app U
      ((tensorPresentation E H).pair.apply U x y) =
    (tensorMap u v).app U
      ((GlobalScalars.scalarEnd (tensorSheaf E H) r).app U
        ((tensorPresentation E H).pair.apply U x y))
  rw [tensorMap_apply, GlobalScalars.scalarEnd_app,
    Scheme.Modules.Hom.app_smul (tensorMap u v), tensorMap_apply]
  change ((tensorPresentation E' H').pair.apply U (u.app U x))
    (v.app U ((GlobalScalars.scalarEnd H r).app U y)) = _
  rw [GlobalScalars.scalarEnd_app, Scheme.Modules.Hom.app_smul v]
  exact map_smul ((tensorPresentation E' H').pair.apply U (u.app U x)) _ _

theorem «section» {Y : Scheme} {E : OModule Y} (s : AlgebraicSection E)
    (r : RingSections Y ⊤) :
    s ≫ GlobalScalars.scalarEnd E r = scalarSection r ≫ s := by
  rw [← section_scale]
  apply (sectionValue_bijective E).injective
  rw [sectionValue_comp, sectionFromValue_spec]
  simp only [GlobalScalars.scalarEnd_app, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]

theorem relative_right {C B : Scheme} (pi : C ⟶ B)
    {E E' H H' : OModule C} (r : RingSections B ⊤)
    (u : E ⟶ E') (v : H ⟶ H') (s : AlgebraicSection (RelativeSquare.box pi E H)) :
    s ≫ RelativeSquare.boxMap pi u (GlobalScalars.scalarEnd H (pi.appTop r) ≫ v) =
      scalarSection ((RelativeSquare.left pi ≫ pi).appTop r) ≫
        s ≫ RelativeSquare.boxMap pi u v := by
  have hr : (RelativeSquare.right pi).appTop (pi.appTop r) =
      (RelativeSquare.left pi ≫ pi).appTop r := by
    change (RelativeSquare.right pi ≫ pi).appTop r = _
    rw [← pullback.condition]
  unfold RelativeSquare.boxMap
  rw [Functor.map_comp, LineEndomorphisms.scalarEnd_pullback, hr, right,
    ← Category.assoc]
  erw [«section» (E := RelativeSquare.box pi E H) s
    ((RelativeSquare.left pi ≫ pi).appTop r)]
  simp only [Category.assoc]

theorem relative_left {C B : Scheme} (pi : C ⟶ B)
    {E E' H H' : OModule C} (r : RingSections B ⊤)
    (u : E ⟶ E') (v : H ⟶ H') (s : AlgebraicSection (RelativeSquare.box pi E H)) :
    s ≫ RelativeSquare.boxMap pi (GlobalScalars.scalarEnd E (pi.appTop r) ≫ u) v =
      scalarSection ((RelativeSquare.left pi ≫ pi).appTop r) ≫
        s ≫ RelativeSquare.boxMap pi u v := by
  rw [ScalarTensor.relative_move, relative_right]

end TensorScalar

def genericBaseCoefficient : RingSections GenericPoint ⊤ :=
  genericPoint.appTop (coefficientSection a)

theorem genericCoefficient_base (ha : a ≠ 0) :
    (RelativeSquare.left p1Parameter ≫ p1Parameter).appTop (genericBaseCoefficient a) =
      genericCoefficient F a ha := by
  change ((RelativeSquare.left p1Parameter ≫ p1Parameter) ≫ genericPoint).appTop
    (coefficientSection a) = _
  have hm : (RelativeSquare.left p1Parameter ≫ p1Parameter) ≫ genericPoint =
      parametrizedToModelSquare F a ha ≫ ModelNumerator.squareProjection F a :=
    (parametrizedToModelSquare_base F a ha).symm
  exact congrArg (fun k => k.appTop (coefficientSection a)) hm

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
