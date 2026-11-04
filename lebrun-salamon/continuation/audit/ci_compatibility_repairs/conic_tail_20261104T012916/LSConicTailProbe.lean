import LSConicHessianPrefix

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseFourteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Refinement.Jets
open LeBrunSalamon.Construction LeBrunSalamon.Construction.Lines

-- These are existing type aliases. Expose their projections to rewrite
-- matching, so the actual chart rings and projective-line scheme agree.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety PointFrame.ChartRing
  identityCurveContact intrinsicTangentBundle

namespace LeBrunSalamon.Refinement

/-- SOURCE jet:second-symbol. Lower symbols vanish first, so the
curve acceleration contributes zero. The undivided Hessian equals 2 theta^2. -/
theorem fullFamily_secondSymbol (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X)
    (D : FamilyKernel P p X g) (h1 : FamilyKernel.HasZeroFirstSymbol P p D) :
    HasNormalizedContactSymbol X.contact D.kernel := by
  classical
  obtain ⟨E⟩ := externalExpansion_exists X.variety X.contact.sequence.line D.kernel
  refine ⟨E, ?_⟩
  intro F u v
  apply sub_eq_zero.mp
  apply ConicJetProof.function_zero_on_full_family P p X g D.family F.openSet
  intro t r q hq
  let x : ComplexPoint X.variety := ⟨q ≫ F.openSet.ι, by
    rw [hq, Category.assoc, (D.family.curveAt t).overC, r.overC]⟩
  let Fp : PointFrame X.variety X.contact.sequence.line x := ⟨F, q, rfl⟩
  obtain ⟨A⟩ := contactAtPoint_exists X.contact Fp
  obtain ⟨G, hG⟩ := GlobalVelocity.targetChart_exists_inside X.variety x F.openSet (by
    rintro _ ⟨z, rfl⟩
    exact Fp.pointSupport trivial)
  have hdef := ConicJetProof.frameDefect_zero_on_curve P p X g D E t r x
    hq.symm Fp A G hG
  have hh := ConicJetProof.pointHessian_of_defect_zero E h1 Fp A G hG hdef u v
  change Fp.evaluation (E.secondSlotSecond F u v -
    2 * localContactValue X.contact F u * localContactValue X.contact F v) = 0
  rw [map_sub, map_mul, map_mul, map_ofNat, hh]
  ring

namespace SourceReparamProof

open ConicJetProof

/-- Pull the actual external section back along the actual curve square,
then use the specified canonical external-product comparison. -/
def curvePull (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L) :
    ExternalSquareSections (projectiveLineVariety P) (pullbackBundle f.map L) := by
  let q := curveExternalComparison P f L.sheaf L.sheaf
  letI : IsIso q := curveExternalComparison_isIso P f L.sheaf L.sheaf
  exact pullSection (curveSquareMap P f) B ≫ inv q

theorem curvePull_comparison (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L) :
    curvePull P f L B ≫ curveExternalComparison P f L.sheaf L.sheaf =
      pullSection (curveSquareMap P f) B := by
  letI := curveExternalComparison_isIso P f L.sheaf L.sheaf
  simp only [curvePull, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem curvePull_product (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (a b : AlgebraicSection L.sheaf) :
    curvePull P f L (externalProductSection X.structureMap a b) =
      externalProductSection P.structureMap (pullSection f.map a) (pullSection f.map b) := by
  letI := curveExternalComparison_isIso P f L.sheaf L.sheaf
  apply (cancel_mono (curveExternalComparison P f L.sheaf L.sheaf)).mp
  rw [curvePull_comparison, curveExternalComparison_onProducts]

theorem curvePull_sum (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) {N : ℕ} (B : Fin N → ExternalSquareSections X L) :
    curvePull P f L (∑ i, B i) = ∑ i, curvePull P f L (B i) := by
  simp only [curvePull, pullSection, restrictSection, Functor.map_sum,
    Preadditive.comp_sum, Preadditive.sum_comp]

def pulledExpansion (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    {L : LineBundle X.scheme} {B : ExternalSquareSections X L}
    (E : ExternalExpansion X L B) :
    ExternalExpansion (projectiveLineVariety P) (pullbackBundle f.map L) (curvePull P f L B) where
  size := E.size
  left i := pullSection f.map (E.left i)
  right i := pullSection f.map (E.right i)
  equation := by
    conv_lhs => rw [E.equation]
    rw [curvePull_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact curvePull_product P f L (E.left i) (E.right i)

theorem curvePull_symmetric (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L)
    (hB : IsSymmetricExternalSection X.structureMap L B) :
    IsSymmetricExternalSection P.structureMap (pullbackBundle f.map L) (curvePull P f L B) := by
  obtain ⟨E⟩ := externalExpansion_exists X L B
  let EP := pulledExpansion P f E
  let EQ := pulledExpansion P f (SymmetricDiagonalProof.exchangedSameExpansion E hB)
  let sigma := ExchangeAlgebraProof.swapSectionAddHom
    (chosenExternalExchange P.structureMap (pullbackBundle f.map L)).identification
  change sigma (curvePull P f L B) = curvePull P f L B
  conv_lhs => rw [EP.equation, map_sum]
  have hs (i : Fin E.size) : sigma
      (externalProductSection P.structureMap (EP.left i) (EP.right i)) =
      externalProductSection P.structureMap (EQ.left i) (EQ.right i) :=
    (chosenExternalExchange P.structureMap (pullbackBundle f.map L)).onProducts _ _
  simp_rw [hs]
  exact EQ.equation.symm

theorem curvePull_orderTwo (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L : LineBundle X.scheme) (B : ExternalSquareSections X L)
    (hB : IsSymmetricExternalSection X.structureMap L B)
    (h2 : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap L).sheaf B) :
    VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (pullbackBundle f.map L)).sheaf (curvePull P f L B) := by
  apply SymmetricDiagonalProof.orderTwo_of_orderOne (projectiveLineVariety P)
    (pullbackBundle f.map L) (curvePull P f L B) (curvePull_symmetric P f L B hB)
  apply FullFamilyDiagonalProof.orderOne_of_diagonal_zero
  have hdiag := FullFamilyDiagonalProof.diagonal_zero_of_orderTwo X.structureMap B h2
  have hpull : pullSection (diagonal P.structureMap)
      (pullSection (curveSquareMap P f) B) = 0 := by
    apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff
      (diagonal P.structureMap) (curveSquareMap P f) B).2
    rw [FullFamilyDiagonalProof.curveSquare_diagonal]
    apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff
      f.map (diagonal X.structureMap) B).1
    rw [hdiag, FullFamilyDiagonalProof.pullSection_zero]
  simp only [curvePull, pullSection_naturality, hpull, zero_comp]

theorem curvePull_map (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f : RationalCurve P X)
    (L M : LineBundle X.scheme) (q : L.sheaf ⟶ M.sheaf)
    (B : ExternalSquareSections X L) :
    curvePull P f M (B ≫ externalTensorMap X.structureMap q q) =
      curvePull P f L B ≫ externalTensorMap P.structureMap
        ((Scheme.Modules.pullback f.map).map q) ((Scheme.Modules.pullback f.map).map q) := by
  obtain ⟨E⟩ := externalExpansion_exists X L B
  rw [(pulledExpansion P f (SourceMixedSymbol.mappedExpansion E q)).equation,
    (pulledExpansion P f E).equation, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  change externalProductSection P.structureMap
      (pullSection f.map (E.left i ≫ q)) (pullSection f.map (E.right i ≫ q)) = _
  rw [pullSection_naturality, pullSection_naturality]
  exact (CurveExchangeProof.externalTensorMap_product P.structureMap
    (pullbackBundle f.map L) (pullbackBundle f.map M)
    ((Scheme.Modules.pullback f.map).map q)
    (pullSection f.map (E.left i)) (pullSection f.map (E.right i))).symm

theorem externalTensorMap_comp {Y : Scheme} (s : Y ⟶ ComplexBase)
    {E F G : OModule Y} (q : E ⟶ F) (r : F ⟶ G) :
    externalTensorMap s q q ≫ externalTensorMap s r r =
      externalTensorMap s (q ≫ r) (q ≫ r) := by
  simp only [externalTensorMap, Functor.map_comp, tensorMap_comp]

/-- Mapping an order-two section between actual line bundles changes
its repeated mixed symbol by the square of the actual frame multiplier. -/
theorem mapped_mixed_of_orderTwo {d : ℕ} {Y : SmoothProperComplexVariety d}
    {L M : LineBundle Y.scheme} {B : ExternalSquareSections Y L}
    (E : ExternalExpansion Y L B) (q : L.sheaf ⟶ M.sheaf)
    (h2 : VanishesQuadraticallyAlongDiagonal Y.structureMap
      (externalSquareLine Y.structureMap L).sheaf B)
    (S : AffineLineFrame L)
    (m : SectionsOn M.sheaf S.openSet ≃ₗ[RingSections Y.scheme S.openSet]
      RingSections Y.scheme S.openSet)
    (u : SectionsOn (tangentSheaf Y.structureMap) S.openSet) :
    (SourceMixedSymbol.mappedExpansion E q).mixedSecond (SourceMixedSymbol.frameOn S m) u u =
      (SourceMixedSymbol.multiplier q S m)^2 * E.mixedSecond S u u := by
  rw [(SourceMixedSymbol.mappedExpansion E q).mixedSecond_eq_neg_of_orderTwo
      (SourceMixedSymbol.mapped_orderTwo q h2),
    SourceMixedSymbol.mapped_secondSlotSecond,
    E.diagonalValue_zero_of_orderTwo h2, E.secondSlotFirst_zero_of_orderTwo h2,
    E.mixedSecond_eq_neg_of_orderTwo h2]
  ring

theorem normalized_point_quadratic {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (w : TangentFiber X x) :
    (∑ i, (F.fiberEquiv w).val (F.coefficient (K.expansion.left i)) *
      (F.fiberEquiv w).val (F.coefficient (K.expansion.right i))) +
      2 * (A.theta (F.fiberEquiv w)) ^ 2 = 0 := by
  obtain ⟨v, hv⟩ := F.evaluateVector_surjective (F.fiberEquiv w)
  have hm := congrArg F.evaluation
    (K.expansion.mixedSecond_eq_neg_of_orderTwo K.orderTwo F.frame v v)
  rw [K.expansion_normalized F.frame v v] at hm
  have hsum : (∑ i, (F.evaluateVector v).val (F.coefficient (K.expansion.left i)) *
      (F.evaluateVector v).val (F.coefficient (K.expansion.right i))) =
      F.evaluation (K.expansion.mixedSecond F.frame v v) := by
    simp only [ExternalExpansion.mixedSecond, map_sum, map_mul]
    rfl
  rw [← hv, A.theta_normalized, hsum]
  simp only [map_neg, map_mul, map_ofNat] at hm
  linear_combination hm

theorem pointDifferential_contact_coefficient (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) (f : RationalCurve P X)
    {x : ComplexPoint X} (hx : p.map ≫ f.map = x.map)
    {M : LineBundle ProjectiveLine}
    (S : PointFrame (projectiveLineVariety P) M ⟨p.map, p.overC⟩)
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (hV : S.frame.openSet ≤ f.map ⁻¹ᵁ F.frame.openSet)
    (u : SectionsOn (tangentSheaf P.structureMap) S.frame.openSet) :
    A.theta (F.fiberEquiv (SourceTangent.pointDifferential (projectiveLineVariety P) X
      f.map f.overC ⟨p.map, p.overC⟩ x hx
      (PositiveFrame.localFiberValue p.map (tangentSheaf P.structureMap)
        S.frame.openSet S.pointSupport u))) =
      S.evaluation (PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
        ((curveContactVelocity P C f).app S.frame.openSet u)) := by
  rw [theta_fiber_coefficient C F A]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (F.lineFiberCoefficient (fiberMap C.sequence.form x.map
        (fiberComposition f.map p.map x.map hx (tangentSheaf X.structureMap)
          (fiberMap (differentialOver (projectiveLineVariety P) X f.map f.overC) p.map
            (PositiveFrame.localFiberValue p.map (tangentSheaf P.structureMap)
              S.frame.openSet S.pointSupport u))))) = _
  rw [← ContactPositive.fiberComposition_naturality,
    ← ContactPositive.fiberMap_comp, ← PositiveFrame.localFiberValue_map]
  rw [F.lineFiberCoefficient_composition f.map p.map hx S.frame.openSet hV S.pointSupport]
  exact (S.evaluation_eq_localRingValue _).symm

/-- Pullback of a normalized kernel has the expected mixed point symbol
along the actual differential of every source vector. This is a direct
first-derivative chain rule and uses no source-automorphism invariance. -/
theorem pulled_mixed_point (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)} {C : IntrinsicContactStructure X}
    (K : NormalizedContactKernel X C) (f : RationalCurve P X)
    {x : ComplexPoint X} (hx : p.map ≫ f.map = x.map)
    {M : LineBundle ProjectiveLine}
    (S : PointFrame (projectiveLineVariety P) M ⟨p.map, p.overC⟩)
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (hV : S.frame.openSet ≤ f.map ⁻¹ᵁ F.frame.openSet)
    (u : SectionsOn (tangentSheaf P.structureMap) S.frame.openSet) :
    S.evaluation ((pulledExpansion P f K.expansion).mixedSecond
      (SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line) S.frame
        (PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV)) u u) =
      -2 * (S.evaluation
        (PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
          ((curveContactVelocity P C f).app S.frame.openSet u))) ^ 2 := by
  let w := SourceTangent.pointDifferential (projectiveLineVariety P) X
    f.map f.overC ⟨p.map, p.overC⟩ x hx
    (PositiveFrame.localFiberValue p.map (tangentSheaf P.structureMap)
      S.frame.openSet S.pointSupport u)
  let m := PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
  have hc (a : AlgebraicSection C.sequence.line.sheaf) :
      (SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line) S.frame m).localCoefficient
        (pullSection f.map a) =
      f.map.appLE F.frame.openSet S.frame.openSet hV (F.coefficient a) := by
    change m (Scheme.Modules.Hom.app (pullSection f.map a)
      S.frame.openSet (1 : RingSections ProjectiveLine _)) = _
    rw [ScalarSections.section_app_one]
    exact PointFrame.LocalFrameJetProof.coefficientOn_global F.frame f.map S.frame.openSet hV a
  have hD (a : F.ChartRing) : (F.fiberEquiv w).val a =
      S.evaluation (tangentActs P.structureMap S.frame.openSet u
        (f.map.appLE F.frame.openSet S.frame.openSet hV a)) :=
    pointDifferential_frame_function (projectiveLineVariety P) X f.map f.overC
      ⟨p.map, p.overC⟩ x hx S F hV u a
  have hm : (∑ i, (F.fiberEquiv w).val (F.coefficient (K.expansion.left i)) *
      (F.fiberEquiv w).val (F.coefficient (K.expansion.right i))) =
      S.evaluation ((pulledExpansion P f K.expansion).mixedSecond
        (SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line) S.frame m) u u) := by
    simp only [ExternalExpansion.mixedSecond, map_sum, map_mul]
    simp_rw [hD, hc]
    rfl
  have hz := normalized_point_quadratic K F A w
  rw [hm, pointDifferential_contact_coefficient P p C f hx S F A hV u] at hz
  linear_combination hz

theorem inverse_overC (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    e.inv ≫ P.structureMap = P.structureMap := by
  calc
    _ = e.inv ≫ (e.hom ≫ P.structureMap) := congrArg (fun f => e.inv ≫ f) he.symm
    _ = _ := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

def isoCurve (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    RationalCurve P (projectiveLineVariety P) where
  map := e.hom
  overC := he
  nonconstant := by
    rintro ⟨x, hx, hc⟩
    let p0 := ProjectiveLinePoint.rebase P marking
    let pinf := ProjectiveLinePoint.rebase P infinity
    have hp : p0.map ≫ e.hom = pinf.map ≫ e.hom := by
      rw [hc, ← Category.assoc, p0.overC, Category.id_comp,
        ← Category.assoc, pinf.overC, Category.id_comp]
    have hp' : p0.map = pinf.map := (cancel_mono e.hom).mp hp
    exact zero_ne_infinity ((ProjectiveLinePoint.rebase_map_eq_iff P marking infinity).1 hp')

/-- Construct the inverse differential at an abstract variety before
specializing to the concrete projective-line model. -/
def differentialIso {d e : ℕ} (X : SmoothProperComplexVariety d)
    (Y : SmoothProperComplexVariety e) (f : X.scheme ⟶ Y.scheme) [IsIso f]
    (hf : f ≫ Y.structureMap = X.structureMap) :
    tangentSheaf X.structureMap ≅ pullbackModule f (tangentSheaf Y.structureMap) := by
  letI := ContactDerivativeIsoProof.differentialOver_isIso X Y f hf
  exact asIso (differentialOver X Y f hf)

def derivativeIso (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    tangentSheaf P.structureMap ≅ pullbackModule e.hom (tangentSheaf P.structureMap) :=
  differentialIso (projectiveLineVariety P) (projectiveLineVariety P) e.hom he

theorem source_contactVelocity (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    curveContactVelocity P (identityCurveContact P) (isoCurve P e he) =
      (derivativeIso P e he).hom := by
  change differentialOver (projectiveLineVariety P) (projectiveLineVariety P) e.hom he ≫
      (Scheme.Modules.pullback e.hom).map (𝟙 (tangentSheaf P.structureMap)) =
    differentialOver (projectiveLineVariety P) (projectiveLineVariety P) e.hom he
  rw [(Scheme.Modules.pullback e.hom).map_id, Category.comp_id]

/-- A source frame is transported to its entire image open using the
actual differential of the inverse isomorphism. This prevents any
unrecorded shrinking or frame-change scalar in the normalization test. -/
abbrev imageFrame (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    (S : AffineLineFrame (identityCurveContact P).sequence.line) :
    AffineLineFrame (identityCurveContact P).sequence.line where
  openSet := e.inv ⁻¹ᵁ S.openSet
  isAffine := S.isAffine.preimage e.inv
  coefficient := by
    let D : SectionsOn (tangentSheaf P.structureMap) (e.inv ⁻¹ᵁ S.openSet)
        ≃ₗ[RingSections ProjectiveLine (e.inv ⁻¹ᵁ S.openSet)]
      SectionsOn (pullbackModule e.inv (tangentSheaf P.structureMap))
        (e.inv ⁻¹ᵁ S.openSet) :=
      (((SheafOfModules.evaluation ProjectiveLine.ringCatSheaf
        (op (e.inv ⁻¹ᵁ S.openSet))).mapIso
          (derivativeIso P e.symm (inverse_overC P e he))).toLinearEquiv)
    exact D.trans
      (PointFrame.LocalFrameJetProof.coefficientOn S e.inv (e.inv ⁻¹ᵁ S.openSet) le_rfl)

theorem imageFrame_support (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    (S : AffineLineFrame (identityCurveContact P).sequence.line) :
    S.openSet ≤ e.hom ⁻¹ᵁ (imageFrame P e he S).openSet := by
  change S.openSet ≤ (e.hom ≫ e.inv) ⁻¹ᵁ S.openSet
  rw [e.hom_inv_id]
  simp

def sourceTransport (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    ExternalSquareSections (projectiveLineVariety P) (identityCurveContact P).sequence.line :=
  curvePull P (isoCurve P e he) (identityCurveContact P).sequence.line (sourceBivector P) ≫
    externalTensorMap P.structureMap (derivativeIso P e he).inv (derivativeIso P e he).inv

def sourceTransportExpansion (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) :
    ExternalExpansion (projectiveLineVariety P) (identityCurveContact P).sequence.line
      (sourceTransport P e he) :=
  SourceMixedSymbol.mappedExpansion (M := (identityCurveContact P).sequence.line)
    (pulledExpansion P (isoCurve P e he) (SourceMixedSymbol.sourceKernel P).expansion)
    (derivativeIso P e he).inv

theorem sourceTransport_symmetric (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    IsSymmetricExternalSection P.structureMap (identityCurveContact P).sequence.line
      (sourceTransport P e he) :=
  CurveExchangeProof.map_symmetric (projectiveLineVariety P)
    (pullbackBundle e.hom (identityCurveContact P).sequence.line)
    (identityCurveContact P).sequence.line (derivativeIso P e he).inv _
    (curvePull_symmetric P (isoCurve P e he) _ _ (SourceMixedSymbol.sourceKernel P).symmetric)

theorem sourceTransport_orderTwo (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap (identityCurveContact P).sequence.line).sheaf
      (sourceTransport P e he) := by
  have h2 : VanishesQuadraticallyAlongDiagonal P.structureMap
      (externalSquareLine P.structureMap
        (pullbackBundle e.hom (identityCurveContact P).sequence.line)).sheaf
      (curvePull P (isoCurve P e he) (identityCurveContact P).sequence.line
        (sourceBivector P)) :=
    curvePull_orderTwo P (isoCurve P e he) (identityCurveContact P).sequence.line
      (sourceBivector P) (SourceMixedSymbol.sourceKernel P).symmetric
      (SourceMixedSymbol.sourceKernel P).orderTwo
  exact SourceMixedSymbol.mapped_orderTwo (Y := projectiveLineVariety P)
    (L := pullbackBundle e.hom (identityCurveContact P).sequence.line)
    (M := (identityCurveContact P).sequence.line)
    (B := curvePull P (isoCurve P e he) (identityCurveContact P).sequence.line
      (sourceBivector P)) (derivativeIso P e he).inv h2

/-- The transported source tensor retains its exact normalized repeated
Hessian at every actual complex point. The inverse differential cancels
the actual derivative; its frame multiplier is computed, never assumed. -/
theorem sourceTransport_point_self (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap)
    (p : ProjectiveLinePoint P)
    (S : PointFrame (projectiveLineVariety P) (identityCurveContact P).sequence.line
      ⟨p.map, p.overC⟩)
    (u : SectionsOn (tangentSheaf P.structureMap) S.frame.openSet) :
    S.evaluation ((sourceTransportExpansion P e he).secondSlotSecond S.frame u u) =
      2 * (S.evaluation (S.frame.coefficient u)) ^ 2 := by
  let x : ComplexPoint (projectiveLineVariety P) :=
    ⟨p.map ≫ e.hom, by
      change (p.map ≫ e.hom) ≫ P.structureMap = 𝟙 ComplexBase
      rw [Category.assoc, he, p.overC]⟩
  let H := imageFrame P e he S.frame
  have hV : S.frame.openSet ≤ e.hom ⁻¹ᵁ H.openSet := imageFrame_support P e he S.frame
  have hr : Set.range x.map ⊆ Set.range H.openSet.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change e.hom (p.map z) ∈ H.openSet
    exact hV (S.pointSupport trivial)
  let F : PointFrame (projectiveLineVariety P) (identityCurveContact P).sequence.line x :=
    ⟨H, IsOpenImmersion.lift H.openSet.ι x.map hr, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨A⟩ := contactAtPoint_exists (identityCurveContact P) F
  let K := SourceMixedSymbol.sourceKernel P
  let EP := pulledExpansion P (isoCurve P e he) K.expansion
  let q := (derivativeIso P e he).inv
  let m := PointFrame.LocalFrameJetProof.coefficientOn F.frame e.hom S.frame.openSet hV
  let R := SourceMixedSymbol.frameOn
    (M := pullbackBundle e.hom (identityCurveContact P).sequence.line) S.frame m
  let lambda := SourceMixedSymbol.multiplier q R S.frame.coefficient
  have h2 := curvePull_orderTwo P (isoCurve P e he)
    (identityCurveContact P).sequence.line K.twoPointSection K.symmetric K.orderTwo
  have hraw := pulled_mixed_point P p K (isoCurve P e he) (x := x) rfl S F A hV u
  rw [source_contactVelocity] at hraw
  change S.evaluation (EP.mixedSecond R u u) =
    -2 * (S.evaluation
      (m ((derivativeIso P e he).hom.app S.frame.openSet u))) ^ 2 at hraw
  have hmapped := congrArg S.evaluation
    (mapped_mixed_of_orderTwo (M := (identityCurveContact P).sequence.line)
      EP q h2 R S.frame.coefficient u)
  change S.evaluation ((sourceTransportExpansion P e he).mixedSecond S.frame u u) =
    S.evaluation (lambda ^ 2 * EP.mixedSecond R u u) at hmapped
  rw [map_mul, map_pow] at hmapped
  have hdu : q.app S.frame.openSet ((derivativeIso P e he).hom.app S.frame.openSet u) = u :=
    congrArg (fun k : tangentSheaf P.structureMap ⟶ tangentSheaf P.structureMap =>
      k.app S.frame.openSet u) (derivativeIso P e he).hom_inv_id
  have hcoeff := SourceMixedSymbol.coefficient_map q R S.frame.coefficient
    ((derivativeIso P e he).hom.app S.frame.openSet u)
  change S.frame.coefficient
      (q.app S.frame.openSet ((derivativeIso P e he).hom.app S.frame.openSet u)) =
    lambda * m ((derivativeIso P e he).hom.app S.frame.openSet u) at hcoeff
  rw [hdu] at hcoeff
  have hvalue := congrArg S.evaluation hcoeff
  change S.evaluation (S.frame.coefficient u) =
    S.evaluation (lambda * m ((derivativeIso P e he).hom.app S.frame.openSet u)) at hvalue
  rw [map_mul] at hvalue
  have hmix : S.evaluation ((sourceTransportExpansion P e he).mixedSecond S.frame u u) =
      -2 * (S.evaluation (S.frame.coefficient u)) ^ 2 := by
    rw [hmapped, hraw, hvalue]
    ring
  have hh := congrArg S.evaluation
    ((sourceTransportExpansion P e he).mixedSecond_eq_neg_of_orderTwo
      (sourceTransport_orderTwo P e he) S.frame u u)
  rw [map_neg] at hh
  linear_combination hh - hmix

theorem sourceTransport_point_hessian (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap)
    (p : ProjectiveLinePoint P)
    (S : PointFrame (projectiveLineVariety P) (identityCurveContact P).sequence.line
      ⟨p.map, p.overC⟩)
    (u v : SectionsOn (tangentSheaf P.structureMap) S.frame.openSet) :
    S.evaluation ((sourceTransportExpansion P e he).secondSlotSecond S.frame u v) =
      2 * S.evaluation (S.frame.coefficient u) * S.evaluation (S.frame.coefficient v) := by
  let E := sourceTransportExpansion P e he
  have hu := sourceTransport_point_self P e he p S u
  have hv := sourceTransport_point_self P e he p S v
  have huv := sourceTransport_point_self P e he p S (u + v)
  have hs : E.secondSlotSecond S.frame (u + v) (u + v) =
      E.secondSlotSecond S.frame u u + E.secondSlotSecond S.frame u v +
        E.secondSlotSecond S.frame v u + E.secondSlotSecond S.frame v v := by
    simp only [ExternalExpansion.secondSlotSecond, tangentActs_add_field,
      tangentActs_add_function, mul_add, Finset.sum_add_distrib] <;> abel
  rw [hs, E.secondSlotSecond_symmetric_of_orderTwo (sourceTransport_orderTwo P e he)
    S.frame v u, map_add, map_add, map_add, S.frame.coefficient.map_add,
    map_add] at huv
  linear_combination (1 / 2 : ℂ) * huv - (1 / 2 : ℂ) * hu - (1 / 2 : ℂ) * hv

theorem sourceTransport_normalized (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    HasNormalizedContactSymbol (identityCurveContact P) (sourceTransport P e he) := by
  refine ⟨sourceTransportExpansion P e he, ?_⟩
  intro S u v
  apply sub_eq_zero.mp
  let a := (sourceTransportExpansion P e he).secondSlotSecond S u v -
    2 * localContactValue (identityCurveContact P) S u *
      localContactValue (identityCurveContact P) S v
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  letI : Smooth (S.openSet.ι ≫ P.structureMap) := inferInstance
  letI : AlgebraicGeometry.IsReduced S.openSet.toScheme :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced (S.openSet.ι ≫ P.structureMap)
  have hz : S.openSet.topIso.inv a = 0 := by
    apply ComplexPointSectionDetection.function_zero (S.openSet.ι ≫ P.structureMap)
    intro q
    let p : ProjectiveLinePoint P :=
      ⟨q.val ≫ S.openSet.ι, by simpa only [Category.assoc] using q.property⟩
    let F : PointFrame (projectiveLineVariety P) (identityCurveContact P).sequence.line
        ⟨p.map, p.overC⟩ := ⟨S, q.val, rfl⟩
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).injective
    rw [map_zero]
    change F.evaluation a = 0
    have hh := sourceTransport_point_hessian P e he p F u v
    change F.evaluation ((sourceTransportExpansion P e he).secondSlotSecond S u v -
      2 * S.coefficient u * S.coefficient v) = 0
    rw [map_sub, map_mul, map_mul, map_ofNat, hh]
    ring
  apply (ConcreteCategory.bijective_of_isIso S.openSet.topIso.inv).injective
  rw [map_zero]
  exact hz

/-- Uniqueness of the original normalized source tensor now proves its
automorphism invariance, after its normalization was checked through
the actual inverse derivative. -/
theorem sourceTransport_eq (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    sourceTransport P e he = sourceBivector P :=
  (Classical.choose_spec (sourceBivector_existsUnique P)).2 _
    ⟨sourceTransport_symmetric P e he, sourceTransport_orderTwo P e he,
      sourceTransport_normalized P e he⟩

theorem sourceBivector_curvePull (P : ProjectiveLineOverC)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap) :
    curvePull P (isoCurve P e he) (identityCurveContact P).sequence.line (sourceBivector P) =
      sourceBivector P ≫ externalTensorMap P.structureMap
        (derivativeIso P e he).hom (derivativeIso P e he).hom := by
  have h := congrArg (fun B : ExternalSquareSections (projectiveLineVariety P)
      (identityCurveContact P).sequence.line =>
    B ≫ externalTensorMap P.structureMap (derivativeIso P e he).hom (derivativeIso P e he).hom)
    (sourceTransport_eq P e he)
  have hc : externalTensorMap P.structureMap (derivativeIso P e he).inv
        (derivativeIso P e he).inv ≫
      externalTensorMap P.structureMap (derivativeIso P e he).hom
        (derivativeIso P e he).hom =
      𝟙 (externalTensor P.structureMap
        (pullbackModule e.hom (tangentSheaf P.structureMap))
        (pullbackModule e.hom (tangentSheaf P.structureMap))) := by
    rw [externalTensorMap_comp, (derivativeIso P e he).inv_hom_id, externalTensorMap_id]
  simpa only [sourceTransport, isoCurve, Category.assoc, hc, Category.comp_id] using h

theorem curveKernelIdentity_curvePull (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line) :
    CurveKernelIdentity P C f B ↔
      curvePull P f C.sequence.line B = sourceBivector P ≫
        externalTensorMap P.structureMap (curveContactVelocity P C f) (curveContactVelocity P C f) := by
  rw [curveKernelIdentity_iff]
  let q := curveExternalComparison P f C.sequence.line.sheaf C.sequence.line.sheaf
  letI : IsIso q := curveExternalComparison_isIso P f C.sequence.line.sheaf C.sequence.line.sheaf
  constructor
  · intro h
    have hh := congrArg (fun a => a ≫ inv q) h
    simpa only [curvePull, sourceContactValue, q, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id] using hh
  · intro h
    rw [← curvePull_comparison P f C.sequence.line B, h]
    rfl

/-- Composition of actual curve pullbacks, proved on a genuine finite
external expansion and the canonical composition pullback on each factor. -/
theorem curvePull_iso_comp (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (f g : RationalCurve P X)
    (e : ProjectiveLine ≅ ProjectiveLine) (he : e.hom ≫ P.structureMap = P.structureMap)
    (hg : g.map = e.hom ≫ f.map) (L : LineBundle X.scheme)
    (B : ExternalSquareSections X L) :
    curvePull P (isoCurve P e he) (pullbackBundle f.map L) (curvePull P f L B) ≫
      externalTensorMap P.structureMap
        (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom
        (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom =
      curvePull P g L B := by
  obtain ⟨E⟩ := externalExpansion_exists X L B
  rw [(pulledExpansion P (isoCurve P e he) (pulledExpansion P f E)).equation,
    Preadditive.sum_comp, (pulledExpansion P g E).equation]
  apply Finset.sum_congr rfl
  intro i hi
  change externalProductSection P.structureMap
      (pullSection e.hom (pullSection f.map (E.left i)))
      (pullSection e.hom (pullSection f.map (E.right i))) ≫
        externalTensorMap P.structureMap
          (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom
          (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom = _
  rw [CurveExchangeProof.externalTensorMap_product P.structureMap
    (pullbackBundle e.hom (pullbackBundle f.map L)) (pullbackBundle g.map L)
    (compositionPullback e.hom f.map g.map hg.symm L.sheaf).hom
    (pullSection e.hom (pullSection f.map (E.left i)))
    (pullSection e.hom (pullSection f.map (E.right i))),
    compositionPullback_sections, compositionPullback_sections] <;> rfl

/-- The original contact velocity obeys the actual differential chain
rule, with the original composition comparison on its quotient line. -/
theorem curveContactVelocity_comp (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f g : RationalCurve P X) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) (hg : g.map = e.hom ≫ f.map) :
    (derivativeIso P e he).hom ≫
      (Scheme.Modules.pullback e.hom).map (curveContactVelocity P C f) ≫
      (compositionPullback e.hom f.map g.map hg.symm C.sequence.line.sheaf).hom =
      curveContactVelocity P C g := by
  rcases g with ⟨gmap, hgC, hgNonconstant⟩
  change gmap = e.hom ≫ f.map at hg
  subst gmap
  simp only [compositionPullback, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  have hn := (Scheme.Modules.pullbackComp e.hom f.map).hom.naturality C.sequence.form
  change (Scheme.Modules.pullback e.hom).map
        ((Scheme.Modules.pullback f.map).map C.sequence.form) ≫
      (Scheme.Modules.pullbackComp e.hom f.map).hom.app C.sequence.line.sheaf =
    (Scheme.Modules.pullbackComp e.hom f.map).hom.app (tangentSheaf X.structureMap) ≫
      (Scheme.Modules.pullback (e.hom ≫ f.map)).map C.sequence.form at hn
  change (derivativeIso P e he).hom ≫
      (Scheme.Modules.pullback e.hom).map (curveContactVelocity P C f) ≫
      (Scheme.Modules.pullbackComp e.hom f.map).hom.app C.sequence.line.sheaf = _
  calc
    _ = (differentialOver (projectiveLineVariety P) (projectiveLineVariety P) e.hom he ≫
        (Scheme.Modules.pullback e.hom).map
          (differentialOver (projectiveLineVariety P) X f.map f.overC) ≫
        (Scheme.Modules.pullbackComp e.hom f.map).hom.app (tangentSheaf X.structureMap)) ≫
          (Scheme.Modules.pullback (e.hom ≫ f.map)).map C.sequence.form := by
      simp only [curveContactVelocity, Functor.map_comp, Category.assoc]
      rw [hn] <;> rfl
    _ = _ := by
      rw [ContactDerivativeIsoProof.differentialOver_comp (projectiveLineVariety P)
        (projectiveLineVariety P) X e.hom f.map he f.overC hgC] <;> rfl

theorem reparametrize_forward (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f g : RationalCurve P X) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    (hg : g.map = e.hom ≫ f.map) (B : ExternalSquareSections X C.sequence.line)
    (h : CurveKernelIdentity P C f B) : CurveKernelIdentity P C g B := by
  have hf := (curveKernelIdentity_curvePull P C f B).1 h
  apply (curveKernelIdentity_curvePull P C g B).2
  let c := (compositionPullback e.hom f.map g.map hg.symm C.sequence.line.sheaf).hom
  let qe := (derivativeIso P e he).hom
  let qf := (Scheme.Modules.pullback e.hom).map (curveContactVelocity P C f)
  have hq : qe ≫ qf ≫ c = curveContactVelocity P C g :=
    curveContactVelocity_comp P C f g e he hg
  calc
    curvePull P g C.sequence.line B =
        curvePull P (isoCurve P e he) (pullbackBundle f.map C.sequence.line)
          (curvePull P f C.sequence.line B) ≫ externalTensorMap P.structureMap c c :=
      (curvePull_iso_comp P f g e he hg C.sequence.line B).symm
    _ = curvePull P (isoCurve P e he) (pullbackBundle f.map C.sequence.line)
          (sourceBivector P ≫ externalTensorMap P.structureMap
            (curveContactVelocity P C f) (curveContactVelocity P C f)) ≫
        externalTensorMap P.structureMap c c := by rw [hf]
    _ = (curvePull P (isoCurve P e he) (identityCurveContact P).sequence.line
          (sourceBivector P) ≫ externalTensorMap P.structureMap qf qf) ≫
        externalTensorMap P.structureMap c c := by rw [curvePull_map]; rfl
    _ = ((sourceBivector P ≫ externalTensorMap P.structureMap qe qe) ≫
          externalTensorMap P.structureMap qf qf) ≫
        externalTensorMap P.structureMap c c := by rw [sourceBivector_curvePull]
    _ = sourceBivector P ≫ externalTensorMap P.structureMap (qe ≫ qf ≫ c) (qe ≫ qf ≫ c) := by
      simp only [Category.assoc]
      rw [externalTensorMap_comp P.structureMap qf c,
        externalTensorMap_comp P.structureMap qe (qf ≫ c)]
    _ = sourceBivector P ≫ externalTensorMap P.structureMap
        (curveContactVelocity P C g) (curveContactVelocity P C g) := by rw [hq]

end SourceReparamProof

/-- PGL2-invariance of the source bivector is needed for this lemma. -/
theorem curveKernelIdentity_reparametrize (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f g : RationalCurve P X) (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap)
    (hg : g.map = e.hom ≫ f.map) (B : ExternalSquareSections X C.sequence.line) :
    CurveKernelIdentity P C f B ↔ CurveKernelIdentity P C g B := by
  constructor
  · intro h
    exact SourceReparamProof.reparametrize_forward P C f g e he hg B h
  · intro h
    have hf : f.map = e.inv ≫ g.map := by
      rw [hg, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    exact SourceReparamProof.reparametrize_forward P C g f e.symm
      (SourceReparamProof.inverse_overC P e he) hf B h

end LeBrunSalamon.Refinement

namespace LeBrunSalamon.Skeleton

/-- SOURCE jet:diagonal. Proof order: value on Delta, first symbol,
then the quadratic symbol. No acceleration term survives once the
first symbol has vanished. Openness of value--velocity is essential. -/
theorem fullFamilyKernel_normalized (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} (X : ContactFanoManifold n)
    (g : VeryFreeContactConic P p X) (D : FullFamilyKernel P p X g) :
    ∃ K : NormalizedContactKernel X.variety X.contact,
      K.twoPointSection = D.kernel := by
  have h0 := Refinement.fullFamily_diagonalValue P p X g D
  have h1 := Refinement.fullFamily_firstSymbol P p X g D h0
  exact ⟨⟨D.kernel, D.symmetry, h1,
    Refinement.fullFamily_secondSymbol P p X g D h1⟩, rfl⟩

end LeBrunSalamon.Skeleton

end
