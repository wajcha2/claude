import RecompileExtensionsPart01
import LSP1TangentSections

/-! Genuine polynomial coordinates of global tangent sections. The supplied
complex-base automorphism is explicitly undone, so the final map is complex
linear for every ProjectiveLineOverC, not only the canonical one. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Core.ExternalTensorCoordinates
open LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames LeBrunSalamon.P1TangentTranslation
open scoped TensorProduct
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

namespace LeBrunSalamon.P1CoordinatePolynomials

def baseFieldIso (P : ProjectiveLineOverC) : CommRingCat.of ℂ ≅ CommRingCat.of ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm ≪≫
    Scheme.Γ.mapIso (CotangentTwistProof.baseChangeIso P).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of ℂ)

def baseFieldAuto (P : ProjectiveLineOverC) : ℂ ≃+* ℂ :=
  (baseFieldIso P).commRingCatIsoToRingEquiv

theorem chart_constant (P : ProjectiveLineOverC) (i : Fin 2) (c : ℂ) :
    polynomialChartRingEquiv i (constants P.structureMap (chartOpen i) c) =
      Polynomial.C (baseFieldAuto P c) := by
  let A := CotangentTwistProof.baseChangeIso P
  let d := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  change polynomialChartRingEquiv i
    (complexConstant P.structureMap (chartOpen i) c) = Polynomial.C d
  have hd : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv d =
      A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) :=
    Iso.hom_inv_id_apply _ _
  rw [complexConstant, ← CotangentTwistProof.baseMap_factor P,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ← hd]
  exact polynomialChartRingEquiv_canonical_constant i d

def chartAlgebraEquiv (P : ProjectiveLineOverC) (i : Fin 2) :
    Coefficients P.structureMap (chartOpen i) ≃ₐ[ℂ] Polynomial ℂ :=
  { (polynomialChartRingEquiv i).trans (Polynomial.mapEquiv (baseFieldAuto P).symm) with
    commutes' c := by
      change Polynomial.mapEquiv (baseFieldAuto P).symm
        (polynomialChartRingEquiv i (constants P.structureMap (chartOpen i) c)) =
          Polynomial.C c
      rw [chart_constant]
      change Polynomial.map (baseFieldAuto P).symm.toRingHom
        (Polynomial.C (baseFieldAuto P c)) = Polynomial.C c
      rw [Polynomial.map_C]
      exact congrArg Polynomial.C ((baseFieldAuto P).symm_apply_apply c) }

theorem chartAlgebraEquiv_coordinate (P : ProjectiveLineOverC) (i : Fin 2) :
    chartAlgebraEquiv P i (coordinate i) = Polynomial.X := by
  change Polynomial.mapEquiv (baseFieldAuto P).symm
    (polynomialChartRingEquiv i ((polynomialChartRingEquiv i).symm Polynomial.X)) = _
  rw [RingEquiv.apply_symm_apply]
  exact Polynomial.map_X _

def frame (P : ProjectiveLineOverC) (i : Fin 2) :
    AffineLineFrame (identityCurveContact P).sequence.line where
  openSet := chartOpen i
  isAffine := chartOpen_affine i
  coefficient := coordinates (derivativeFrame P i)

theorem action_coordinate (P : ProjectiveLineOverC) (i : Fin 2)
    (v : SectionsOn (tangentSheaf P.structureMap) (chartOpen i)) :
    tangentActs P.structureMap (chartOpen i) v (coordinate i) =
      (frame P i).coefficient v := by
  have h := congrArg (fun w => tangentActs P.structureMap (chartOpen i) w (coordinate i))
    (reconstruct (derivativeFrame P i) v)
  rw [TangentActionProof.smul_field, derivativeFrame_coordinate, mul_one] at h
  exact h.symm

def polynomialAction (P : ProjectiveLineOverC) (i : Fin 2)
    (v : SectionsOn (tangentSheaf P.structureMap) (chartOpen i)) :
    Derivation ℂ (Polynomial ℂ) (Polynomial ℂ) where
  toLinearMap := (chartAlgebraEquiv P i).toLinearMap.comp
    ((coefficientDerivation P.structureMap (chartOpen i) v).toLinearMap.comp
      (chartAlgebraEquiv P i).symm.toLinearMap)
  map_one_eq_zero' := by
    change chartAlgebraEquiv P i
      ((coefficientDerivation P.structureMap (chartOpen i) v)
        ((chartAlgebraEquiv P i).symm 1)) = 0
    simp
  leibniz' := by
    intro a b
    change chartAlgebraEquiv P i
      ((coefficientDerivation P.structureMap (chartOpen i) v)
        ((chartAlgebraEquiv P i).symm (a * b))) =
      a * chartAlgebraEquiv P i
        ((coefficientDerivation P.structureMap (chartOpen i) v)
          ((chartAlgebraEquiv P i).symm b)) +
      b * chartAlgebraEquiv P i
        ((coefficientDerivation P.structureMap (chartOpen i) v)
          ((chartAlgebraEquiv P i).symm a))
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, AlgEquiv.apply_symm_apply]

theorem action_polynomial (P : ProjectiveLineOverC) (i : Fin 2)
    (v : SectionsOn (tangentSheaf P.structureMap) (chartOpen i))
    (a : RingSections ProjectiveLine (chartOpen i)) :
    chartAlgebraEquiv P i (tangentActs P.structureMap (chartOpen i) v a) =
      (chartAlgebraEquiv P i a).derivative *
        chartAlgebraEquiv P i ((frame P i).coefficient v) := by
  have h := (polynomialAction P i v).map_aeval
    (chartAlgebraEquiv P i a) Polynomial.X
  have hx : (chartAlgebraEquiv P i).symm Polynomial.X = coordinate i := by
    apply (chartAlgebraEquiv P i).injective
    rw [AlgEquiv.apply_symm_apply, chartAlgebraEquiv_coordinate]
  simp only [Polynomial.aeval_X_left_apply, smul_eq_mul] at h
  have ha : polynomialAction P i v (chartAlgebraEquiv P i a) =
      chartAlgebraEquiv P i (tangentActs P.structureMap (chartOpen i) v a) := by
    change chartAlgebraEquiv P i
      (tangentActs P.structureMap (chartOpen i) v
        ((chartAlgebraEquiv P i).symm (chartAlgebraEquiv P i a))) = _
    rw [AlgEquiv.symm_apply_apply]
  have hX : polynomialAction P i v Polynomial.X =
      chartAlgebraEquiv P i ((frame P i).coefficient v) := by
    change chartAlgebraEquiv P i
      (tangentActs P.structureMap (chartOpen i) v
        ((chartAlgebraEquiv P i).symm Polynomial.X)) = _
    rw [hx, action_coordinate]
  rw [ha, hX] at h
  exact h

theorem generator_action (P : ProjectiveLineOverC) (i : Fin 2)
    (a : RingSections ProjectiveLine (chartOpen i)) :
    chartAlgebraEquiv P i
      (tangentActs P.structureMap (chartOpen i) (generator (derivativeFrame P i)) a) =
        (chartAlgebraEquiv P i a).derivative := by
  rw [action_polynomial]
  change _ * chartAlgebraEquiv P i (coordinates _ (generator _)) = _
  rw [coordinates_generator, map_one, mul_one]

def polynomial (P : ProjectiveLineOverC) (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    Polynomial ℂ := chartAlgebraEquiv P 0 ((frame P 0).localCoefficient a)

theorem polynomial_eq_matching (P : ProjectiveLineOverC)
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    polynomial P a = Polynomial.mapEquiv (baseFieldAuto P).symm
      (P1TangentSections.matchingEquiv P a).val.1 := by
  rw [P1TangentSections.matchingEquiv_zero]
  change Polynomial.mapEquiv (baseFieldAuto P).symm
    (polynomialChartRingEquiv 0 (coordinates (derivativeFrame P 0)
      (Scheme.Modules.Hom.app a (chartOpen 0) (1 : RingSections ProjectiveLine (chartOpen 0))))) = _
  exact congrArg (fun v : SectionsOn (tangentSheaf P.structureMap) (chartOpen 0) =>
    Polynomial.mapEquiv (baseFieldAuto P).symm
      (polynomialChartRingEquiv 0 (coordinates (derivativeFrame P 0) v)))
    (section_app_one a (chartOpen 0))

theorem polynomial_injective (P : ProjectiveLineOverC) : Function.Injective (polynomial P) := by
  intro a b hab
  rw [polynomial_eq_matching, polynomial_eq_matching] at hab
  apply (P1TangentSections.matchingEquiv P).injective
  apply P1Overlap.matchingSpace_ext
  exact (Polynomial.mapEquiv (baseFieldAuto P).symm).injective hab

theorem polynomial_natDegree_le (P : ProjectiveLineOverC)
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    (polynomial P a).natDegree ≤ 2 := by
  rw [polynomial_eq_matching, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [P1Overlap.polynomialCoefficientEquiv_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (P1Overlap.matching_degree_le
        (P1TangentSections.matchingEquiv P a).property) hn), map_zero]

def polynomialLinear (P : ProjectiveLineOverC) :
    ComplexSections P.structureMap (tangentSheaf P.structureMap) →ₗ[ℂ] Polynomial ℂ :=
  (chartAlgebraEquiv P 0).toLinearMap.comp
    (coefficientLinear P.structureMap (identityCurveContact P).sequence.line (frame P 0))

theorem polynomialLinear_sectionValue (P : ProjectiveLineOverC)
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    polynomialLinear P (sectionValue a) = polynomial P a := by
  change chartAlgebraEquiv P 0
    (coefficientLinear P.structureMap (identityCurveContact P).sequence.line (frame P 0)
      (sectionValue a)) = _
  rw [coefficientLinear_sectionValue]
  rfl

theorem polynomialLinear_injective (P : ProjectiveLineOverC) :
    Function.Injective (polynomialLinear P) := by
  intro a b h
  have hab : sectionFromValue a = sectionFromValue b := by
    apply polynomial_injective P
    rw [← polynomialLinear_sectionValue, ← polynomialLinear_sectionValue,
      sectionFromValue_spec, sectionFromValue_spec]
    exact h
  simpa only [sectionFromValue_spec] using congrArg (fun a => sectionValue a) hab

def polynomialTensor (P : ProjectiveLineOverC) :=
  TensorProduct.map (polynomialLinear P) (polynomialLinear P)

theorem polynomialTensor_injective (P : ProjectiveLineOverC) :
    Function.Injective (polynomialTensor P) := by
  let V := ComplexSections P.structureMap (tangentSheaf P.structureMap)
  let f := polynomialLinear P
  have he : polynomialTensor P =
      (f.lTensor (Polynomial ℂ)).comp (f.rTensor V) := by
    ext a b
    rfl
  rw [he]
  exact (Module.Flat.lTensor_preserves_injective_linearMap f (polynomialLinear_injective P)).comp
    (Module.Flat.rTensor_preserves_injective_linearMap f (polynomialLinear_injective P))

end LeBrunSalamon.P1CoordinatePolynomials

end
