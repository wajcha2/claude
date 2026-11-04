import LSConicJets

/-!
# Polynomial coordinates of the normalized source bivector

The canonical affine tangent frame acts by the actual polynomial
derivative.  Global tangent fields have degree at most two in this frame,
by the existing tangent-twist theorem and the proved Laurent matching
calculation.  The three diagonal symbol equations therefore determine
the complete two-variable polynomial, over every complex algebra.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Core.ExternalTensorCoordinates
open LeBrunSalamon.Refinement LeBrunSalamon.Refinement.Jets
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.P1TwistSections LeBrunSalamon.LocalFrames
open scoped BigOperators

namespace LeBrunSalamon.Construction.SourceBivectorCoordinates

abbrev P := Lines.P
abbrev U : ProjectiveLine.Opens := chartOpen 0
abbrev TangentLine : LineBundle ProjectiveLine := (identityCurveContact P).sequence.line

def chartAlgebraEquiv : Coefficients P.structureMap U ≃ₐ[ℂ] Polynomial ℂ :=
  { polynomialChartRingEquiv 0 with
    commutes' := fun c => polynomialChartRingEquiv_canonical_constant 0 c }

def coordinate : RingSections ProjectiveLine U := chartAlgebraEquiv.symm Polynomial.X

/-- Conjugation of the actual affine tangent action by the proved
polynomial chart, preserving the actual complex constants. -/
def polynomialAction (v : SectionsOn (tangentSheaf P.structureMap) U) :
    Derivation ℂ (Polynomial ℂ) (Polynomial ℂ) where
  toLinearMap := chartAlgebraEquiv.toLinearMap.comp
    ((coefficientDerivation P.structureMap U v).toLinearMap.comp
      chartAlgebraEquiv.symm.toLinearMap)
  map_one_eq_zero' := by
    change chartAlgebraEquiv
      ((coefficientDerivation P.structureMap U v) (chartAlgebraEquiv.symm 1)) = 0
    simp
  leibniz' := by
    intro a b
    change chartAlgebraEquiv
      ((coefficientDerivation P.structureMap U v) (chartAlgebraEquiv.symm (a * b))) =
        a * chartAlgebraEquiv
          ((coefficientDerivation P.structureMap U v) (chartAlgebraEquiv.symm b)) +
        b * chartAlgebraEquiv
          ((coefficientDerivation P.structureMap U v) (chartAlgebraEquiv.symm a))
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, AlgEquiv.apply_symm_apply]

/-- A polynomial derivation is its value on the coordinate times the
ordinary derivative. This is an equality of actual local functions. -/
theorem action_polynomial (v : SectionsOn (tangentSheaf P.structureMap) U)
    (a : RingSections ProjectiveLine U) :
    chartAlgebraEquiv (tangentActs P.structureMap U v a) =
      (chartAlgebraEquiv a).derivative *
        chartAlgebraEquiv (tangentActs P.structureMap U v coordinate) := by
  have h := (polynomialAction v).map_aeval (chartAlgebraEquiv a) Polynomial.X
  simp only [Polynomial.aeval_X_left_apply, smul_eq_mul] at h
  have ha : polynomialAction v (chartAlgebraEquiv a) =
      chartAlgebraEquiv (tangentActs P.structureMap U v a) := by
    change chartAlgebraEquiv
      (tangentActs P.structureMap U v (chartAlgebraEquiv.symm (chartAlgebraEquiv a))) = _
    rw [AlgEquiv.symm_apply_apply]
  have hX : polynomialAction v Polynomial.X =
      chartAlgebraEquiv (tangentActs P.structureMap U v coordinate) := rfl
  rw [ha, hX] at h
  exact h

def coordinateFunctional :
    SectionsOn (tangentSheaf P.structureMap) U →ₗ[RingSections ProjectiveLine U]
      RingSections ProjectiveLine U where
  toFun v := tangentActs P.structureMap U v coordinate
  map_add' v w := tangentActs_add_field P.structureMap U v w coordinate
  map_smul' a v := TangentActionProof.smul_field P.structureMap U v a coordinate

theorem coordinateFunctional_injective : Function.Injective coordinateFunctional := by
  intro v w h
  apply TangentAffine.affine_tangent_action_faithful P.structureMap U
    (chartOpen_affine 0) v w
  intro a
  apply chartAlgebraEquiv.injective
  rw [action_polynomial, action_polynomial]
  exact congrArg (fun z => (chartAlgebraEquiv a).derivative * chartAlgebraEquiv z) h

theorem coordinateFunctional_surjective : Function.Surjective coordinateFunctional := by
  let D : RingSections ProjectiveLine U → RingSections ProjectiveLine U :=
    fun a => chartAlgebraEquiv.symm (chartAlgebraEquiv a).derivative
  obtain ⟨v, hv⟩ := TangentAffine.affine_tangent_action_exists P.structureMap U
    (chartOpen_affine 0) D
    (by simp [D])
    (fun a b => by simp [D, Polynomial.derivative_add])
    (fun a b => by simp [D, Polynomial.derivative_mul, mul_comm])
    (fun c => by
      change chartAlgebraEquiv.symm
        (chartAlgebraEquiv (constants P.structureMap U c)).derivative = 0
      rw [chartAlgebraEquiv.commutes, Polynomial.derivative_C, map_zero])
  have hcoord : coordinateFunctional v = 1 := by
    change tangentActs P.structureMap U v coordinate = 1
    rw [hv]
    simp [D, coordinate]
  intro a
  exact ⟨a • v, by rw [map_smul, hcoord, smul_eq_mul, mul_one]⟩

/-- The coefficient is the value on dz. Thus its inverse generator is
the genuine d/dz field, without choosing a scalar normalization. -/
def frame : AffineLineFrame TangentLine where
  openSet := U
  isAffine := chartOpen_affine 0
  coefficient := LinearEquiv.ofBijective coordinateFunctional
    ⟨coordinateFunctional_injective, coordinateFunctional_surjective⟩

def coordinateVector : SectionsOn (tangentSheaf P.structureMap) U :=
  frame.coefficient.symm 1

@[simp]
theorem coordinateVector_coefficient : frame.coefficient coordinateVector = 1 :=
  frame.coefficient.apply_symm_apply 1

theorem coordinateVector_action (a : RingSections ProjectiveLine U) :
    chartAlgebraEquiv (tangentActs P.structureMap U coordinateVector a) =
      (chartAlgebraEquiv a).derivative := by
  rw [action_polynomial]
  change (chartAlgebraEquiv a).derivative *
    chartAlgebraEquiv (frame.coefficient coordinateVector) = _
  rw [coordinateVector_coefficient, map_one, mul_one]

/-- The polynomial coefficient of an actual global tangent section. -/
def polynomial (a : AlgebraicSection TangentLine.sheaf) : Polynomial ℂ :=
  chartAlgebraEquiv (frame.localCoefficient a)

private def sectionsLinearEquiv {Y : Scheme} {E F : OModule Y}
    (e : E ≅ F) (V : Y.Opens) :
    SectionsOn E V ≃ₗ[RingSections Y V] SectionsOn F V where
  toFun := Scheme.Modules.Hom.app e.hom V
  invFun := Scheme.Modules.Hom.app e.inv V
  left_inv v := congrArg (fun k : E ⟶ E => Scheme.Modules.Hom.app k V v) e.hom_inv_id
  right_inv v := congrArg (fun k : F ⟶ F => Scheme.Modules.Hom.app k V v) e.inv_hom_id
  map_add' v w := (Scheme.Modules.Hom.app e.hom V).hom.map_add v w
  map_smul' c v := (Scheme.Modules.Hom.app e.hom V).hom.map_smul c v

def twistFrame (e : TangentLine.sheaf ≅ (projectiveTwist P Lines.marking 2).sheaf) :
    AffineLineFrame TangentLine where
  openSet := U
  isAffine := chartOpen_affine 0
  coefficient := (sectionsLinearEquiv e U).trans
    (coordinates (twistOverFrame P Lines.marking 2 0))

theorem twistFrame_polynomial
    (e : TangentLine.sheaf ≅ (projectiveTwist P Lines.marking 2).sheaf)
    (a : AlgebraicSection TangentLine.sheaf) :
    chartAlgebraEquiv ((twistFrame e).localCoefficient a) =
      (algebraicMatchingEquiv P Lines.marking 2 (a ≫ e.hom)).val.1 := by
  rw [algebraicMatchingEquiv_fst]
  change chartAlgebraEquiv
      (coordinates (twistOverFrame P Lines.marking 2 0)
        (e.hom.app U (Scheme.Modules.Hom.app a U (1 : RingSections ProjectiveLine U)))) =
    polynomialCoordinates P Lines.marking 2 0
      ((projectiveTwist P Lines.marking 2).sheaf.presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op (sectionValue (a ≫ e.hom)))
  rw [← section_app_one (a ≫ e.hom) U]
  rfl

/-- The degree bound is transported from the actual Laurent matching
space. Two frames on Spec C[z] differ by a constant unit, so the
canonical derivative frame has the same bound. -/
theorem polynomial_natDegree_le (a : AlgebraicSection TangentLine.sheaf) :
    (polynomial a).natDegree ≤ 2 := by
  obtain ⟨e⟩ := projectiveLine_tangent_twist P Lines.marking
  obtain ⟨q, hq, _⟩ := affineLineFrame_change_isUnit TangentLine U
    (chartOpen_affine 0) (twistFrame e).coefficient frame.coefficient
  have hu : IsUnit (chartAlgebraEquiv (q : RingSections ProjectiveLine U)) :=
    q.isUnit.map chartAlgebraEquiv.toRingHom
  obtain ⟨c, hc, heq⟩ := Polynomial.isUnit_iff.mp hu
  have hpoly : polynomial a = Polynomial.C c *
      (algebraicMatchingEquiv P Lines.marking 2 (a ≫ e.hom)).val.1 := by
    change chartAlgebraEquiv
      (frame.coefficient (Scheme.Modules.Hom.app a U (1 : RingSections ProjectiveLine U))) = _
    rw [hq, map_mul, ← heq]
    rw [← twistFrame_polynomial]
    rfl
  rw [hpoly]
  calc
    _ ≤ (Polynomial.C c).natDegree +
        ((algebraicMatchingEquiv P Lines.marking 2 (a ≫ e.hom)).val.1).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 2 := by
      simpa only [Polynomial.natDegree_C, zero_add] using
        P1Overlap.matching_degree_le
          (algebraicMatchingEquiv P Lines.marking 2 (a ≫ e.hom)).property

abbrev kernel := ConicJetProof.SourceMixedSymbol.sourceKernel P
abbrev expansion := kernel.expansion

def left (i : Fin expansion.size) : Polynomial ℂ := polynomial (expansion.left i)
def right (i : Fin expansion.size) : Polynomial ℂ := polynomial (expansion.right i)

theorem polynomial_value : ∑ i, left i * right i = 0 := by
  have h := congrArg chartAlgebraEquiv
    (expansion.diagonalValue_zero_of_orderTwo kernel.orderTwo frame)
  simpa only [ExternalExpansion.diagonalValue, map_sum, map_mul, map_zero,
    left, right, polynomial] using h

theorem polynomial_first : ∑ i, left i * (right i).derivative = 0 := by
  have h := congrArg chartAlgebraEquiv
    (expansion.secondSlotFirst_zero_of_orderTwo kernel.orderTwo frame coordinateVector)
  simpa only [ExternalExpansion.secondSlotFirst, map_sum, map_mul, map_zero,
    coordinateVector_action, left, right, polynomial] using h

theorem polynomial_second : ∑ i, left i * (right i).derivative.derivative = 2 := by
  have h := congrArg chartAlgebraEquiv
    (kernel.expansion_normalized frame coordinateVector coordinateVector)
  change chartAlgebraEquiv
      (∑ i, frame.localCoefficient (expansion.left i) *
        tangentActs P.structureMap U coordinateVector
          (tangentActs P.structureMap U coordinateVector
            (frame.localCoefficient (expansion.right i)))) =
    chartAlgebraEquiv (2 * frame.coefficient coordinateVector *
      frame.coefficient coordinateVector) at h
  simpa only [map_sum, map_mul, coordinateVector_action,
    coordinateVector_coefficient, map_one, map_ofNat, mul_one,
    left, right, polynomial] using h

namespace QuadraticAlgebra

/-- Literal Taylor expansion of a polynomial of degree at most two.
The coefficient ring of the test point is arbitrary. -/
theorem taylor_two {R : Type*} [CommRing R] [Algebra ℂ R]
    (q : Polynomial ℂ) (hq : q.natDegree ≤ 2) (z w : R) :
    Polynomial.aeval w q = Polynomial.aeval z q +
      Polynomial.aeval z q.derivative * (w - z) +
      (algebraMap ℂ R (1 / 2)) * Polynomial.aeval z q.derivative.derivative * (w - z)^2 := by
  have he : q = Polynomial.C (q.coeff 0) + Polynomial.C (q.coeff 1) * Polynomial.X +
      Polynomial.C (q.coeff 2) * Polynomial.X^2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, mul_one, pow_one] using
      q.as_sum_range_C_mul_X_pow' (show q.natDegree < 3 by omega)
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_X_sq,
    Polynomial.derivative_zero, Polynomial.derivative_one,
    map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, pow_one,
    Nat.reduceSub, Nat.cast_ofNat, map_ofNat, pow_zero]
  have hhalf : (algebraMap ℂ R (1 / 2)) * 2 = 1 := by
    have h := congrArg (algebraMap ℂ R) (show (1 / 2 : ℂ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  linear_combination
    -((algebraMap ℂ R (q.coeff 2)) * (w - z)^2) * hhalf

end QuadraticAlgebra

/-- The exact normalized two-point polynomial over every complex
algebra, including nonreduced algebras and trait fraction fields. -/
theorem polynomial_formula {R : Type*} [CommRing R] [Algebra ℂ R] (z w : R) :
    ∑ i, Polynomial.aeval z (left i) * Polynomial.aeval w (right i) = (z - w)^2 := by
  have h₀ := congrArg (Polynomial.aeval z) polynomial_value
  have h₁ := congrArg (Polynomial.aeval z) polynomial_first
  have h₂ := congrArg (Polynomial.aeval z) polynomial_second
  simp only [map_sum, map_mul, map_zero, map_ofNat] at h₀ h₁ h₂
  have ht (i : Fin expansion.size) := QuadraticAlgebra.taylor_two (right i)
    (polynomial_natDegree_le (expansion.right i)) z w
  simp_rw [ht, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs₁ : (∑ i, Polynomial.aeval z (left i) *
      (Polynomial.aeval z (right i).derivative * (w - z))) =
      (∑ i, Polynomial.aeval z (left i) * Polynomial.aeval z (right i).derivative) *
        (w - z) := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i hi; ring
  have hs₂ : (∑ i, Polynomial.aeval z (left i) *
      ((algebraMap ℂ R (1 / 2)) * Polynomial.aeval z (right i).derivative.derivative *
        (w - z)^2)) =
      (algebraMap ℂ R (1 / 2)) *
        (∑ i, Polynomial.aeval z (left i) *
          Polynomial.aeval z (right i).derivative.derivative) * (w - z)^2 := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs₁, hs₂, h₀, h₁, h₂, zero_mul, zero_add, zero_add]
  have hhalf : (algebraMap ℂ R (1 / 2)) * 2 = 1 := by
    have h := congrArg (algebraMap ℂ R) (show (1 / 2 : ℂ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  rw [hhalf, one_mul]
  ring

namespace TestMaps

open PointFrame.LocalFrameJetProof
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

variable {T : Scheme} (sT : T ⟶ ComplexBase)

/-- Actual pullback of chart functions, including the complex structure
on the test scheme and the original appLE map. -/
def onCoefficients (f : T ⟶ ProjectiveLine) (hf : f ≫ P.structureMap = sT)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) : Coefficients P.structureMap U →ₐ[ℂ] Coefficients sT ⊤ where
  toRingHom := (f.appLE U ⊤ hU).hom
  commutes' c := by
    change f.appLE U ⊤ hU (complexConstant P.structureMap U c) =
      complexConstant sT ⊤ c
    exact (Lines.SectionAlgebra.onFunctionsLE f hf U ⊤ hU).commutes c

def polynomialMap (f : T ⟶ ProjectiveLine) (hf : f ≫ P.structureMap = sT)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) : Polynomial ℂ →ₐ[ℂ] Coefficients sT ⊤ :=
  (onCoefficients sT f hf hU).comp chartAlgebraEquiv.symm.toAlgHom

theorem polynomialMap_eq_aeval (f : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hU : ⊤ ≤ f ⁻¹ᵁ U) :
    polynomialMap sT f hf hU = Polynomial.aeval (f.appLE U ⊤ hU coordinate) := by
  apply Polynomial.algHom_ext
  rw [Polynomial.aeval_X]
  rfl

theorem coefficient_evaluation (f : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hU : ⊤ ≤ f ⁻¹ᵁ U)
    (a : AlgebraicSection TangentLine.sheaf) :
    f.appLE U ⊤ hU (frame.localCoefficient a) =
      Polynomial.aeval (f.appLE U ⊤ hU coordinate) (polynomial a) := by
  rw [← polynomialMap_eq_aeval sT f hf hU]
  change _ = f.appLE U ⊤ hU (chartAlgebraEquiv.symm
    (chartAlgebraEquiv (frame.localCoefficient a)))
  rw [AlgEquiv.symm_apply_apply]

/-- The polynomial formula with literal structure-sheaf pullback maps.
There is no reducedness or finite-type assumption on the test scheme. -/
theorem coefficient_formula (f g : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hg : g ≫ P.structureMap = sT)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ U) :
    (∑ i, f.appLE U ⊤ hU (frame.localCoefficient (expansion.left i)) *
      g.appLE U ⊤ hV (frame.localCoefficient (expansion.right i))) =
        (f.appLE U ⊤ hU coordinate - g.appLE U ⊤ hV coordinate)^2 := by
  simp_rw [coefficient_evaluation sT f hf hU, coefficient_evaluation sT g hg hV]
  exact polynomial_formula (R := Coefficients sT ⊤)
    (f.appLE U ⊤ hU coordinate) (g.appLE U ⊤ hV coordinate)

def pulledCoefficient (f : T ⟶ ProjectiveLine) (hU : ⊤ ≤ f ⁻¹ᵁ U) :
    GlobalSections (pullbackModule f TangentLine.sheaf) ≃ₗ[RingSections T ⊤]
      RingSections T ⊤ := coefficientOn frame f ⊤ hU

def frameSection (f : T ⟶ ProjectiveLine) (hU : ⊤ ≤ f ⁻¹ᵁ U) :
    AlgebraicSection (pullbackModule f TangentLine.sheaf) :=
  sectionFromValue ((pulledCoefficient f hU).symm 1)

theorem frameSection_apply (f : T ⟶ ProjectiveLine) (hU : ⊤ ≤ f ⁻¹ᵁ U)
    (a : RingSections T ⊤) :
    (frameSection f hU).app ⊤ a = (pulledCoefficient f hU).symm a := by
  have h1 : (frameSection f hU).app ⊤ (1 : RingSections T ⊤) =
      (pulledCoefficient f hU).symm 1 := sectionFromValue_spec _
  calc
    _ = a • (frameSection f hU).app ⊤ (1 : RingSections T ⊤) := by
      simpa only [smul_eq_mul, mul_one] using
        ((frameSection f hU).app ⊤).hom.map_smul a (1 : RingSections T ⊤)
    _ = _ := by
      rw [h1, ← (pulledCoefficient f hU).symm.map_smul]
      simp only [smul_eq_mul, mul_one]

theorem frameSection_isIso [IsAffine T] (f : T ⟶ ProjectiveLine)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) : IsIso (frameSection f hU) := by
  letI : (structureModule T).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank (structureModule_rank T)
  letI : (pullbackModule f TangentLine.sheaf).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank
      (pullbackLine f TangentLine).locallyFree
  apply affine_isIso_of_appTop_bijective
  constructor
  · intro a b h
    exact (pulledCoefficient f hU).symm.injective
      ((frameSection_apply f hU a).symm.trans (h.trans (frameSection_apply f hU b)))
  · intro a
    exact ⟨pulledCoefficient f hU a, by
      rw [frameSection_apply, (pulledCoefficient f hU).symm_apply_apply]⟩

/-- The affine test-scheme frame is fixed by the actual coefficient on
dz. Its inverse is the pulled d/dz generator. -/
def frameIso [IsAffine T] (f : T ⟶ ProjectiveLine) (hU : ⊤ ≤ f ⁻¹ᵁ U) :
    pullbackModule f TangentLine.sheaf ≅ structureModule T := by
  letI := frameSection_isIso f hU
  exact (asIso (frameSection f hU)).symm

theorem frameIso_apply [IsAffine T] (f : T ⟶ ProjectiveLine)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (a : GlobalSections (pullbackModule f TangentLine.sheaf)) :
    (frameIso f hU).hom.app ⊤ a = pulledCoefficient f hU a := by
  letI := frameSection_isIso f hU
  have h := congrArg (fun q : structureModule T ⟶ structureModule T =>
    q.app ⊤ (pulledCoefficient f hU a)) (asIso (frameSection f hU)).hom_inv_id
  change (frameIso f hU).hom.app ⊤
    ((frameSection f hU).app ⊤ (pulledCoefficient f hU a)) = pulledCoefficient f hU a at h
  rw [frameSection_apply, (pulledCoefficient f hU).symm_apply_apply] at h
  exact h

theorem frameIso_section [IsAffine T] (f : T ⟶ ProjectiveLine)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (a : AlgebraicSection TangentLine.sheaf) :
    pullSection f a ≫ (frameIso f hU).hom =
      scalarSection (f.appLE U ⊤ hU (frame.localCoefficient a)) := by
  apply (sectionValue_bijective (structureModule T)).injective
  rw [sectionValue_comp, frameIso_apply]
  change pulledCoefficient f hU (sectionValue (pullSection f a)) = _
  simpa only [scalarSection, sectionFromValue_spec, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply] using coefficientOn_global frame f ⊤ hU a

def pair (f g : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hg : g ≫ P.structureMap = sT) :
    T ⟶ SelfProduct P.structureMap := pullback.lift f g (hf.trans hg.symm)

def pairPullIso (f g : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hg : g ≫ P.structureMap = sT) :
    pullbackModule (pair sT f g hf hg) (externalSquareLine P.structureMap TangentLine).sheaf ≅
      tensorSheaf (pullbackModule f TangentLine.sheaf) (pullbackModule g TangentLine.sheaf) := by
  let c := pair sT f g hf hg
  let p := firstProjection P.structureMap
  let q := secondProjection P.structureMap
  letI := tensorPullbackComparison_isIso c
    (pullbackModule p TangentLine.sheaf) (pullbackModule q TangentLine.sheaf)
  exact (asIso (tensorPullbackComparison c
    (pullbackModule p TangentLine.sheaf) (pullbackModule q TangentLine.sheaf))).symm ≪≫
      tensorIso
        (compositionPullback c p f (by simp [c, p, pair, firstProjection]) TangentLine.sheaf)
        (compositionPullback c q g (by simp [c, q, pair, secondProjection]) TangentLine.sheaf)

theorem pairPullIso_product (f g : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hg : g ≫ P.structureMap = sT)
    (a b : AlgebraicSection TangentLine.sheaf) :
    pullSection (pair sT f g hf hg) (externalProductSection P.structureMap a b) ≫
      (pairPullIso sT f g hf hg).hom = tensorSection (pullSection f a) (pullSection g b) := by
  let c := pair sT f g hf hg
  letI := tensorPullbackComparison_isIso c
    (pullbackModule (firstProjection P.structureMap) TangentLine.sheaf)
    (pullbackModule (secondProjection P.structureMap) TangentLine.sheaf)
  rw [externalProductSection, ← tensorPullbackComparison_onSections]
  simp only [pairPullIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [tensorSection_map, compositionPullback_sections, compositionPullback_sections]

def pairFrameIso [IsAffine T] (f g : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hg : g ≫ P.structureMap = sT)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ U) :
    pullbackModule (pair sT f g hf hg) (externalSquareLine P.structureMap TangentLine).sheaf ≅
      structureModule T :=
  pairPullIso sT f g hf hg ≪≫ tensorIso (frameIso f hU) (frameIso g hV) ≪≫
    TensorConstruction.leftUnitIso (structureModule T)

theorem pairFrameIso_product [IsAffine T] (f g : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hg : g ≫ P.structureMap = sT)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ U)
    (a b : AlgebraicSection TangentLine.sheaf) :
    pullSection (pair sT f g hf hg) (externalProductSection P.structureMap a b) ≫
      (pairFrameIso sT f g hf hg hU hV).hom =
        scalarSection (f.appLE U ⊤ hU (frame.localCoefficient a) *
          g.appLE U ⊤ hV (frame.localCoefficient b)) := by
  change (pullSection _ _ ≫ (pairPullIso sT f g hf hg).hom) ≫
    tensorMap (frameIso f hU).hom (frameIso g hV).hom ≫
      (TensorConstruction.leftUnitIso (structureModule T)).hom = _
  rw [pairPullIso_product, ← Category.assoc, tensorSection_map,
    frameIso_section, frameIso_section]
  exact tensorScalarSection _ _

/-- The original sourceBivector itself, pulled to any actual affine
test scheme, has coefficient (z-w)^2 in the two canonical tangent frames.
The result holds over arbitrary extensions of C, not just complex points. -/
theorem sourceBivector_coefficient [IsAffine T] (f g : T ⟶ ProjectiveLine)
    (hf : f ≫ P.structureMap = sT) (hg : g ≫ P.structureMap = sT)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ U) :
    pullSection (pair sT f g hf hg) (sourceBivector P) ≫
      (pairFrameIso sT f g hf hg hU hV).hom =
        scalarSection ((f.appLE U ⊤ hU coordinate - g.appLE U ⊤ hV coordinate)^2) := by
  have he : sourceBivector P = ∑ i,
      externalProductSection P.structureMap (expansion.left i) (expansion.right i) :=
    expansion.equation
  rw [he]
  have hp {E : OModule (SelfProduct P.structureMap)}
      (a : Fin expansion.size → AlgebraicSection E) :
      pullSection (pair sT f g hf hg) (∑ i, a i) =
        ∑ i, pullSection (pair sT f g hf hg) (a i) := by
    simp only [pullSection, restrictSection, Functor.map_sum, Preadditive.comp_sum]
  rw [hp, Preadditive.sum_comp]
  simp_rw [pairFrameIso_product]
  apply (sectionValue_bijective (structureModule T)).injective
  change (sectionAddEquiv (structureModule T)) (∑ i, scalarSection
    (f.appLE U ⊤ hU (frame.localCoefficient (expansion.left i)) *
      g.appLE U ⊤ hV (frame.localCoefficient (expansion.right i)))) = _
  rw [map_sum]
  change (∑ i, sectionValue (scalarSection
    (f.appLE U ⊤ hU (frame.localCoefficient (expansion.left i)) *
      g.appLE U ⊤ hV (frame.localCoefficient (expansion.right i))))) = _
  simp only [scalarSection, sectionFromValue_spec]
  exact coefficient_formula sT f g hf hg hU hV

end TestMaps

end LeBrunSalamon.Construction.SourceBivectorCoordinates

end
