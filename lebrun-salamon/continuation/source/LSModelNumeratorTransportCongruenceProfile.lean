import LSModelGenericParametrization

/-!
# Transport of the actual model numerator

This module isolates the original numerator transport theorem from the
independent parametrization declarations. Its statement is unchanged.
The current proof repair is pending native validation.
-/

noncomputable section
set_option stderrAsMessages false
set_option Elab.async false
set_option profiler true
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

/-- Base change of the actual three-term model numerator, after any
specified pair of maps out of its logarithmic line. -/
theorem numerator_transport (ha : a ≠ 0)
    {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (eB : Model F a ⟶ Y) (heB : eB ≫ sY = modelProjection F a ≫ toC)
    (eA : P1Generic ⟶ Y) (heA : eA ≫ sY = p1Parameter ≫ genericBase)
    (hke : genericParametrization F a ha ≫ eB = eA)
    {E H : OModule Y}
    (uB : (modelLine F a).sheaf ⟶ pullbackModule eB E)
    (vB : (modelLine F a).sheaf ⟶ pullbackModule eB H)
    (uA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA E)
    (vA : pullbackModule (genericParametrization F a ha) (modelLine F a).sheaf ⟶
      pullbackModule eA H)
    (hu : (Scheme.Modules.pullback (genericParametrization F a ha)).map uB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke E).hom = uA)
    (hv : (Scheme.Modules.pullback (genericParametrization F a ha)).map vB ≫
      (compositionPullback (genericParametrization F a ha) eB eA hke H).hom = vA) :
    pullSection (parametrizedToModelSquare F a ha)
      (ModelNumerator.numerator F a ≫
        RelativeSquare.boxMap (modelProjection F a) uB vB ≫
          RelativeSquare.comparison (modelProjection F a) sY toC eB heB E H) ≫
      (compositionPullback (parametrizedToModelSquare F a ha)
        (RelativeSquare.evaluation (modelProjection F a) sY toC eB heB)
        (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (RelativeSquare.map_evaluation p1Parameter (modelProjection F a)
          (genericParametrization F a ha) genericPoint
          (genericParametrization_parameter F a ha) sY genericBase toC
          eA eB heA heB hke) (externalTensor sY E H)).hom =
      genericNumerator F a ha ≫ RelativeSquare.boxMap p1Parameter uA vA ≫
        RelativeSquare.comparison p1Parameter sY genericBase eA heA E H := by
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE ENTER_PROOF"
    err.flush
  let k := genericParametrization F a ha
  let q := parametrizedToModelSquare F a ha
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE BEFORE_HP"
    err.flush
  have hp (s t : AlgebraicSection (modelLine F a).sheaf) :=
    RelativeSquare.product_baseChange p1Parameter (modelProjection F a)
      sY genericBase toC eA eB heA heB k hke q
      (RelativeSquare.map_left _ _ _ _ _) (RelativeSquare.map_right _ _ _ _ _)
      (RelativeSquare.map_evaluation p1Parameter (modelProjection F a) k genericPoint
        (genericParametrization_parameter F a ha) sY genericBase toC eA eB heA heB hke)
      (s ≫ uB) (t ≫ vB) (pullSection k s ≫ uA) (pullSection k t ≫ vA)
      (by rw [pullSection_naturality, Category.assoc, hu])
      (by rw [pullSection_naturality, Category.assoc, hv])
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_HP"
    err.flush
  have hadd {V : OModule (ModelNumerator.Square F a)}
      (s t : AlgebraicSection V) : pullSection q (s + t) = pullSection q s + pullSection q t := by
    simp only [pullSection, restrictSection, Functor.map_add, Preadditive.comp_add]
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_HADD"
    err.flush
  have hsection (s t : AlgebraicSection (modelLine F a).sheaf) :
      RelativeBox.section (modelProjection F a) (L := modelLine F a) s t =
        RelativeSquare.productSection (modelProjection F a) s t := rfl
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_HSECTION"
    err.flush
  unfold genericNumerator ModelNumerator.numerator
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_UNFOLD"
    err.flush
  rw [section_scale]
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_SCALE"
    err.flush
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Normalization.BundleGluing.pullSection_sub,
    Category.assoc, LogVelocity.pullSection_scalar]
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_ADDITIVE_SCALAR_SIMP"
    err.flush
  erw [hadd]
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_PULL_ADD"
    err.flush
  simp only [Preadditive.add_comp, Category.assoc, hsection,
    RelativeSquare.productSection_map_assoc]
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_PRODUCT_MAP"
    err.flush
  have hcoeff : (parametrizedToModelSquare F a ha).appTop
      (2 * (ModelNumerator.squareProjection F a).appTop (coefficientSection a)) =
      2 * genericCoefficient F a ha := by
    simp only [genericCoefficient, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      map_mul, map_ofNat]
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_COEFFICIENT"
    err.flush
  simp only [genericCoordinate]
  run_tac
    let err ← IO.getStderr
    err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE AFTER_COORDINATE"
    err.flush
  refine congrArg₂ (fun x y : AlgebraicSection
    (pullbackModule (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
      (externalTensor sY E H)) => x - y) ?_ ?_
  · run_tac
      let err ← IO.getStderr
      err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE BEFORE_SUM"
      err.flush
    exact congrArg₂ (fun x y : AlgebraicSection
      (pullbackModule (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
        (externalTensor sY E H)) => x + y)
      (hp (ModelNumerator.coordinate F a 1 0) (ModelNumerator.coordinate F a 0 1))
      (hp (ModelNumerator.coordinate F a 0 1) (ModelNumerator.coordinate F a 1 0))
  · run_tac
      let err ← IO.getStderr
      err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_STAGE BEFORE_SCALAR"
      err.flush
    exact congrArg₂
      (fun (r : RingSections (Parametrized.Square Lines.P genericBase) ⊤)
        (s : AlgebraicSection
          (pullbackModule (RelativeSquare.evaluation p1Parameter sY genericBase eA heA)
            (externalTensor sY E H))) => scalarSection r ≫ s)
      hcoeff (hp (ModelNumerator.coordinate F a 0 0) (ModelNumerator.coordinate F a 0 0))

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "MODEL_NUMERATOR_CONGRUENCE_DECLARATION_COMPLETE"
  err.flush

end LeBrunSalamon.Construction.TraitContact.ModelGenericComparison

end
