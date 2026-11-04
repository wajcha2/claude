import LSP1BivectorConstruction
import LSAffineFrame

/-! The normalized Hessian is proved in every supplied affine frame by
restricting its actual sheaf trivialization to the two polynomial charts.
The gauge terms cancel in the explicit four-term global expansion. -/
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
open LeBrunSalamon.P1TangentSections
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety

namespace LeBrunSalamon.P1BivectorNormalization

def localCoefficient {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e : OverFrame E U) (a : AlgebraicSection E) : RingSections X U :=
  coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections X U))

theorem localCoefficient_restrict {X : Scheme} {E : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : OverFrame E U) (a : AlgebraicSection E) :
    X.presheaf.map i.op (localCoefficient e a) =
      localCoefficient (restrict i e) a := by
  have h := coordinates_restrict i e (Scheme.Modules.Hom.app a U (1 : RingSections X U))
  rw [sheafHom_naturality a i] at h
  change coordinates (restrict i e)
      (Scheme.Modules.Hom.app a V (X.presheaf.map i.op (1 : RingSections X U))) =
    X.presheaf.map i.op
      (coordinates e (Scheme.Modules.Hom.app a U (1 : RingSections X U))) at h
  rw [map_one] at h
  exact h.symm

theorem localCoefficient_change {X : Scheme} {E : X.Modules} {U : X.Opens}
    (e f : OverFrame E U) (a : AlgebraicSection E) :
    localCoefficient e a = localCoefficient f a * coordinates e (generator f) :=
  coordinates_change e f (Scheme.Modules.Hom.app a U (1 : RingSections X U))

variable (P : ProjectiveLineOverC)

abbrev TangentLine := (identityCurveContact P).sequence.line

instance tangentQuasicoherent : (tangentSheaf P.structureMap).IsQuasicoherent :=
  KunnethDegreeZero.quasicoherent_of_locallyFreeRank (tangentLine P).locallyFree

instance tangentLineQuasicoherent : ((TangentLine P).sheaf).IsQuasicoherent :=
  KunnethDegreeZero.quasicoherent_of_locallyFreeRank (TangentLine P).locallyFree

def actualFrame (F : AffineLineFrame (TangentLine P)) :
    OverFrame (tangentSheaf P.structureMap) F.openSet :=
  AffineFrameProof.frame F.openSet F.isAffine F.coefficient

theorem actualFrame_coordinates (F : AffineLineFrame (TangentLine P))
    (v : SectionsOn (tangentSheaf P.structureMap) F.openSet) :
    coordinates (actualFrame P F) v = F.coefficient v :=
  AffineFrameProof.frame_coordinates F.openSet F.isAffine F.coefficient v

def localCoefficientAddHom (F : AffineLineFrame (TangentLine P)) :
    AlgebraicSection (tangentSheaf P.structureMap) →+ RingSections ProjectiveLine F.openSet where
  toFun := F.localCoefficient
  map_zero' := by change F.coefficient 0 = 0; exact map_zero F.coefficient
  map_add' a b := by
    change F.coefficient (Scheme.Modules.Hom.app a F.openSet (1 : RingSections ProjectiveLine F.openSet) +
      Scheme.Modules.Hom.app b F.openSet (1 : RingSections ProjectiveLine F.openSet)) = _
    exact map_add F.coefficient _ _

theorem coefficient_neg (F : AffineLineFrame (TangentLine P))
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    F.localCoefficient (-a) = -F.localCoefficient a :=
  (localCoefficientAddHom P F).map_neg a

theorem coefficientDerivation_apply (U : ProjectiveLine.Opens)
    (u : SectionsOn (tangentSheaf P.structureMap) U)
    (a : Coefficients P.structureMap U) :
    coefficientDerivation P.structureMap U u a = tangentActs P.structureMap U u a := rfl

theorem expansion_hessian_formula (F : AffineLineFrame (TangentLine P))
    (u v : SectionsOn (tangentSheaf P.structureMap) F.openSet) :
    (P1BivectorConstruction.expansion P).secondSlotSecond F u v =
      P1SourceAlgebra.fourHessian
        (coefficientDerivation P.structureMap F.openSet u)
        (coefficientDerivation P.structureMap F.openSet v)
        (F.localCoefficient (polynomialField P 0))
        (F.localCoefficient (polynomialField P 1))
        (F.localCoefficient (polynomialField P 2)) := by
  simp only [ExternalExpansion.secondSlotSecond, P1BivectorConstruction.expansion,
    P1BivectorConstruction.left, P1BivectorConstruction.right,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cases_zero, Fin.cases_succ, add_zero,
    coefficient_neg, P1SourceAlgebra.fourHessian, coefficientDerivation_apply]
  ring

abbrev chart (F : AffineLineFrame (TangentLine P)) (i : Fin 2) : ProjectiveLine.Opens :=
  F.openSet ⊓ chartOpen i

abbrev frameOn (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    OverFrame (tangentSheaf P.structureMap) (chart P F i) :=
  restrict (homOfLE inf_le_left) (actualFrame P F)

abbrev derivativeOn (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    OverFrame (tangentSheaf P.structureMap) (chart P F i) :=
  restrict (homOfLE inf_le_right) (derivativeFrame P i)

abbrev coordinateOn (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    RingSections ProjectiveLine (chart P F i) :=
  ProjectiveLine.presheaf.map (homOfLE inf_le_right).op (coordinate i)

def gauge (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    RingSections ProjectiveLine (chart P F i) :=
  coordinates (frameOn P F i) (generator (derivativeOn P F i))

theorem derivativeOn_coordinate (F : AffineLineFrame (TangentLine P)) (i : Fin 2) :
    tangentActs P.structureMap (chart P F i) (generator (derivativeOn P F i))
      (coordinateOn P F i) = 1 := by
  rw [derivativeOn, ← generator_restrict, coordinateOn,
    ← TangentActionProof.naturality, derivativeFrame_coordinate, map_one]

theorem coordinates_action (F : AffineLineFrame (TangentLine P)) (i : Fin 2)
    (u : SectionsOn (tangentSheaf P.structureMap) (chart P F i)) :
    coordinates (frameOn P F i) u = gauge P F i *
      tangentActs P.structureMap (chart P F i) u (coordinateOn P F i) := by
  have h := congrArg
    (fun v => tangentActs P.structureMap (chart P F i) v (coordinateOn P F i))
    (reconstruct (derivativeOn P F i) u)
  rw [TangentActionProof.smul_field, derivativeOn_coordinate, mul_one] at h
  rw [coordinates_change (frameOn P F i) (derivativeOn P F i), h]
  exact mul_comm _ _

theorem field_chart_zero (k : Fin 3) :
    localCoefficient (derivativeFrame P 0) (polynomialField P k) =
      coordinate 0 ^ k.val := by
  apply (polynomialChartRingEquiv 0).injective
  rw [map_pow]
  change polynomialChartRingEquiv 0
      (coordinates (derivativeFrame P 0) (Scheme.Modules.Hom.app (polynomialField P k) (chartOpen 0) (1 : RingSections ProjectiveLine (chartOpen 0)))) =
    (polynomialChartRingEquiv 0 ((polynomialChartRingEquiv 0).symm Polynomial.X)) ^ k.val
  rw [RingEquiv.apply_symm_apply, section_app_one]
  exact polynomialField_zero P k

theorem field_chart_one (k : Fin 3) :
    localCoefficient (derivativeFrame P 1) (polynomialField P k) =
      -(coordinate 1 ^ (2-k.val)) := by
  apply (polynomialChartRingEquiv 1).injective
  rw [map_neg, map_pow]
  change polynomialChartRingEquiv 1
      (coordinates (derivativeFrame P 1) (Scheme.Modules.Hom.app (polynomialField P k) (chartOpen 1) (1 : RingSections ProjectiveLine (chartOpen 1)))) =
    -((polynomialChartRingEquiv 1 ((polynomialChartRingEquiv 1).symm Polynomial.X)) ^ (2-k.val))
  rw [RingEquiv.apply_symm_apply, section_app_one]
  exact polynomialField_one P k

theorem coefficient_on_zero (F : AffineLineFrame (TangentLine P)) (k : Fin 3) :
    localCoefficient (frameOn P F 0) (polynomialField P k) =
      gauge P F 0 * coordinateOn P F 0 ^ k.val := by
  rw [localCoefficient_change (frameOn P F 0) (derivativeOn P F 0)]
  change localCoefficient (restrict (homOfLE inf_le_right) (derivativeFrame P 0))
    (polynomialField P k) * gauge P F 0 = _
  rw [← localCoefficient_restrict, field_chart_zero, map_pow]
  exact mul_comm _ _

theorem coefficient_on_one (F : AffineLineFrame (TangentLine P)) (k : Fin 3) :
    localCoefficient (frameOn P F 1) (polynomialField P k) =
      -(gauge P F 1 * coordinateOn P F 1 ^ (2-k.val)) := by
  rw [localCoefficient_change (frameOn P F 1) (derivativeOn P F 1)]
  change localCoefficient (restrict (homOfLE inf_le_right) (derivativeFrame P 1))
    (polynomialField P k) * gauge P F 1 = _
  rw [← localCoefficient_restrict, field_chart_one, map_neg, map_pow]
  ring

theorem restricted_coefficient (F : AffineLineFrame (TangentLine P)) (i : Fin 2)
    (a : AlgebraicSection (tangentSheaf P.structureMap)) :
    ProjectiveLine.presheaf.map (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
      (F.localCoefficient a) = localCoefficient (frameOn P F i) a := by
  change ProjectiveLine.presheaf.map
      (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
      (F.coefficient (Scheme.Modules.Hom.app a F.openSet (1 : RingSections ProjectiveLine F.openSet))) = _
  rw [← actualFrame_coordinates P F]
  exact localCoefficient_restrict (homOfLE inf_le_left) (actualFrame P F) a

theorem restricted_vector_coefficient (F : AffineLineFrame (TangentLine P)) (i : Fin 2)
    (u : SectionsOn (tangentSheaf P.structureMap) F.openSet) :
    ProjectiveLine.presheaf.map (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
      (F.coefficient u) = coordinates (frameOn P F i)
        ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_left).op u) := by
  rw [← actualFrame_coordinates P F]
  exact (coordinates_restrict (homOfLE inf_le_left) (actualFrame P F) u).symm

/-- The local identity after restriction to either genuine polynomial chart. -/
theorem local_hessian (F : AffineLineFrame (TangentLine P)) (i : Fin 2)
    (u v : SectionsOn (tangentSheaf P.structureMap) (chart P F i)) :
    P1SourceAlgebra.fourHessian
      (coefficientDerivation P.structureMap (chart P F i) u)
      (coefficientDerivation P.structureMap (chart P F i) v)
      (localCoefficient (frameOn P F i) (polynomialField P 0))
      (localCoefficient (frameOn P F i) (polynomialField P 1))
      (localCoefficient (frameOn P F i) (polynomialField P 2)) =
        (2 : RingSections ProjectiveLine (chart P F i)) *
          coordinates (frameOn P F i) u * coordinates (frameOn P F i) v := by
  rw [coordinates_action, coordinates_action]
  have htwo : (2 : Fin 3).val = 2 := rfl
  fin_cases i
  · simp only [coefficient_on_zero, Fin.val_zero, Fin.val_one, htwo, Fin.reduceFinMk,
      pow_zero, pow_one, mul_one]
    erw [P1SourceAlgebra.fourHessian_gauge_zero]
    have hring : (2 : RingSections ProjectiveLine (chart P F 0)) * gauge P F 0 ^ 2 *
      tangentActs P.structureMap (chart P F 0) u (coordinateOn P F 0) *
      tangentActs P.structureMap (chart P F 0) v (coordinateOn P F 0) =
        (2 : RingSections ProjectiveLine (chart P F 0)) *
          (gauge P F 0 * tangentActs P.structureMap (chart P F 0) u (coordinateOn P F 0)) *
          (gauge P F 0 * tangentActs P.structureMap (chart P F 0) v (coordinateOn P F 0)) := by ring
    exact hring
  · simp only [coefficient_on_one, Fin.val_zero, Fin.val_one, htwo, Fin.reduceFinMk,
      Nat.reduceSub, pow_zero, pow_one, mul_one]
    erw [P1SourceAlgebra.fourHessian_gauge_one]
    have hring : (2 : RingSections ProjectiveLine (chart P F 1)) * gauge P F 1 ^ 2 *
      tangentActs P.structureMap (chart P F 1) u (coordinateOn P F 1) *
      tangentActs P.structureMap (chart P F 1) v (coordinateOn P F 1) =
        (2 : RingSections ProjectiveLine (chart P F 1)) *
          (gauge P F 1 * tangentActs P.structureMap (chart P F 1) u (coordinateOn P F 1)) *
          (gauge P F 1 * tangentActs P.structureMap (chart P F 1) v (coordinateOn P F 1)) := by ring
    exact hring

/-- The coordinate calculation glues on the supplied affine open. -/
theorem normalized : HasNormalizedContactSymbol (identityCurveContact P)
    (P1BivectorConstruction.bivector P) := by
  refine ⟨P1BivectorConstruction.expansion P, ?_⟩
  intro F u v
  change (P1BivectorConstruction.expansion P).secondSlotSecond F u v =
    2 * F.coefficient u * F.coefficient v
  rw [expansion_hessian_formula]
  have hloc (i : Fin 2) :
      ProjectiveLine.presheaf.map
        (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
          (P1SourceAlgebra.fourHessian (R := Coefficients P.structureMap F.openSet)
            (coefficientDerivation P.structureMap F.openSet u)
            (coefficientDerivation P.structureMap F.openSet v)
            (F.localCoefficient (polynomialField P 0))
            (F.localCoefficient (polynomialField P 1))
            (F.localCoefficient (polynomialField P 2))) =
      ProjectiveLine.presheaf.map
        (homOfLE (show chart P F i ≤ F.openSet from inf_le_left)).op
          (2 * F.coefficient u * F.coefficient v) := by
    simp only [P1SourceAlgebra.fourHessian, coefficientDerivation_apply,
      map_sub, map_add, map_mul, map_ofNat, TangentActionProof.naturality,
      restricted_coefficient, restricted_vector_coefficient P F i u,
      restricted_vector_coefficient P F i v]
    simpa only [P1SourceAlgebra.fourHessian, coefficientDerivation_apply] using local_hessian P F i
      ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_left).op u)
      ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_left).op v)
  have hcover : chart P F 0 ⊔ chart P F 1 = F.openSet := by
    simp only [chart, ← inf_sup_left, chartOpen_zero_sup_one, inf_top_eq]
  exact (TwoChartSections.sectionSheaf (structureModule ProjectiveLine)).eq_of_locally_eq₂
    (homOfLE (show chart P F 0 ≤ F.openSet from inf_le_left))
    (homOfLE (show chart P F 1 ≤ F.openSet from inf_le_left)) hcover.ge _ _
    (hloc 0) (hloc 1)

end LeBrunSalamon.P1BivectorNormalization

end
