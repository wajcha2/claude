import LSNodalTraitQuadraticPresentation
import LSFormalTraitSourceComparison
import LSQuadraticPolarizedModels

/-! Assemble the actual two-component formal-trait model, preserving
the complete smoothing element and the original line bundle. The only
classification input is the precise generic quadratic normal form;
all geometric comparisons below are constructed. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.StableMaps.FormalArcs

namespace LeBrunSalamon.NodalTraitNormalForm

local notation "Model" => LeBrunSalamon.Construction.StableMaps.FormalArcs.Model

theorem exists_model
    (F : StandardSource) {X : Scheme.{0}} (pi : X ⟶ Trait) [IsProper pi] [Flat pi]
    [Smooth (pullback.snd pi genericPoint)]
    (L : LineBundle X) (i j : ProjectiveLine ⟶ pullback pi closedPoint)
    (p q : ProjectiveLinePoint Lines.P) [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : i ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hj : j ≫ pullback.snd pi closedPoint = Lines.P.structureMap)
    (hpush : IsPushout p.map q.map i j)
    (hdi : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (i ≫ pullback.fst pi closedPoint) L) = 1)
    (hdj : projectiveLineDegree Lines.P Lines.marking
      (pullbackLine (j ≫ pullback.fst pi closedPoint) L) = 1) :
    ∃ a : Coefficients, a ≠ 0 ∧ PowerSeries.constantCoeff a = 0 ∧
      ∃ e : X ≅ Model F a,
        e.hom ≫ modelProjection F a = pi ∧
        Nonempty (L.sheaf ≅ pullbackModule e.hom (modelLine F a).sheaf) := by
  obtain ⟨hns, d, hd, e, he, ⟨eL⟩⟩ := nodal_quadratic_equation
    F pi L i j p q hi hj hpush hdi hdj
  have hr := FormalQuadraticConditions.reduced_residue_of_pushout pi d e he p q i j hpush
  have hnr := FormalQuadraticConditions.notSmooth_residue_of_closed_fibre pi d e he hns
  obtain ⟨M, c, hM, hc⟩ := FormalQuadraticConditions.reduced_normal_form d hd hr hnr
  let family : PolarizedOverIso pi (PlaneQuadratic.projection Coefficients d)
      L (QuadraticPolarizedModels.line Coefficients d) := ⟨e, he, eL⟩
  let diagonal := QuadraticPolarizedModels.linear Coefficients d
    (PlaneQuadratic.diagonal Coefficients c) M hM
  let familyDiagonal := family.trans diagonal.symm
  letI : Smooth (pullback.snd pi (Spec.map (CommRingCat.ofHom
      (algebraMap Coefficients (FractionRing Coefficients))))) :=
    ‹Smooth (pullback.snd pi genericPoint)›
  have hcne : c ≠ 0 := FormalQuadraticConditions.diagonal_parameter_ne_zero
    pi c familyDiagonal.iso familyDiagonal.over_base
  let split := QuadraticPolarizedModels.linear Coefficients
    (PlaneQuadratic.split Coefficients (-c)) (PlaneQuadratic.diagonal Coefficients c)
    (ComplexQuadraticMatrix.unit Coefficients)
    (ComplexQuadraticMatrix.transformed_split Coefficients c)
  let familySplit := familyDiagonal.trans split
  obtain ⟨m, hm, ⟨mL⟩⟩ := FormalTraitSourceComparison.model_quadratic_comparison F (-c)
  let model : PolarizedOverIso (modelProjection F (-c))
      (PlaneQuadratic.projection Coefficients (PlaneQuadratic.split Coefficients (-c)))
      (modelLine F (-c)) (QuadraticPolarizedModels.line Coefficients
        (PlaneQuadratic.split Coefficients (-c))) := ⟨m, hm, mL⟩
  refine ⟨-c, neg_ne_zero.mpr hcne, ?_, (familySplit.trans model.symm).exists_iso⟩
  simp only [map_neg, hc, neg_zero]

end LeBrunSalamon.NodalTraitNormalForm
end
