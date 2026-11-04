import RecompileExtensionsPart04Nodes

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

namespace LeBrunSalamon.Construction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace Normalization
open Lines Smoothing

set_option backward.isDefEq.respectTransparency false in
/-- Freeness on the components and surjective evaluation at the node
kill the actual first cohomology of f0*TX on the nodal fibre. -/
theorem centralBundle_H1_vanishes {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) :
    HasVanishingFirstCohomology (centralBundle G).sheaf := by
  let E := centralBundle G
  let eL := compositionPullback (leftBranch G.marks) (centralMap G) D.first.curve.map
    (centralMap_left G) (tangentSheaf X.variety.structureMap)
  let eR := compositionPullback (rightBranch G.marks) (centralMap G) D.second.curve.map
    (centralMap_right G) (tangentSheaf X.variety.structureMap)
  have hL : IsGloballyGenerated (pullbackModule (leftBranch G.marks) E.sheaf) :=
    (DirectSumGeometry.globallyGenerated_iso_iff eL).mpr D.first.free
  have hR : IsGloballyGenerated (pullbackModule (rightBranch G.marks) E.sheaf) :=
    (DirectSumGeometry.globallyGenerated_iso_iff eR).mpr D.second.free
  exact NodeCohomology.of_branches G.marks E
    (freeBundle_firstCohomology_vanishes P marking (pullbackBundle (leftBranch G.marks) E) hL)
    (freeBundle_firstCohomology_vanishes P marking (pullbackBundle (rightBranch G.marks) E) hR)
    (NodeCohomology.leftAtNode_surjective G.marks E hL)

/-- Outer endpoint evaluation on an actual pullback tangent bundle. -/
def outerEvaluation {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    ComponentSections f →ₗ[ℂ]
      Fiber (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap)) infinity.map :=
  evaluateSection P.structureMap _ infinity.map infinity.overC

theorem outerEvaluation_surjective {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) : Function.Surjective (outerEvaluation f) := by
  exact GeneratedFiberEvaluation.evaluateSection_surjective_of_globallyGenerated
    P.structureMap _ infinity.map infinity.overC f.free


def endpointSectionsMap {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) : CentralSections G →ₗ[ℂ]
      (Fiber (pullbackModule D.first.curve.map (tangentSheaf X.variety.structureMap)) infinity.map ×
       Fiber (pullbackModule D.second.curve.map (tangentSheaf X.variety.structureMap)) infinity.map) :=
  ((outerEvaluation D.first).comp (restrictLeft G)).prod
    ((outerEvaluation D.second).comp (restrictRight G))

/-- The concrete normalization restriction intertwines the two actual
endpoint maps with the abstract matching-sections map from Phase 34. -/
theorem endpointSectionsMap_matching {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) :
    endpointSectionsMap G =
      (matchingEndpointMap (nodeEvaluation D.first D.node D.firstAtNode)
        (nodeEvaluation D.second D.node D.secondAtNode)
        (outerEvaluation D.first) (outerEvaluation D.second)).comp
          (normalizationRestriction G) := by
  apply LinearMap.ext
  intro s
  rfl

/-- The quotient is the actual contact-normal line at the NODE, even
though the endpoint values live over two different target points. -/
theorem endpointSections_cokernel {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) :
    Nonempty (((Fiber (pullbackModule D.first.curve.map
          (tangentSheaf X.variety.structureMap)) infinity.map ×
        Fiber (pullbackModule D.second.curve.map
          (tangentSheaf X.variety.structureMap)) infinity.map) ⧸
      LinearMap.range (endpointSectionsMap G)) ≃ₗ[ℂ]
        (TangentFiber X.variety D.node ⧸ contactPlane X D.node)) := by
  have hr : LinearMap.range (endpointSectionsMap G) =
      LinearMap.range (matchingEndpointMap
        (nodeEvaluation D.first D.node D.firstAtNode)
        (nodeEvaluation D.second D.node D.secondAtNode)
        (outerEvaluation D.first) (outerEvaluation D.second)) := by
    rw [endpointSectionsMap_matching]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (normalizationRestriction_bijective G).surjective)
  obtain ⟨e⟩ := matchingEndpoint_cokernel
    (nodeEvaluation D.first D.node D.firstAtNode)
    (nodeEvaluation D.second D.node D.secondAtNode)
    (outerEvaluation D.first) (outerEvaluation D.second)
    (nodeEvaluation_surjective D.first D.node D.firstAtNode)
    (outerEvaluation_surjective D.first) (outerEvaluation_surjective D.second)
  have hs : endpointFixedNodeValues (nodeEvaluation D.first D.node D.firstAtNode)
        (outerEvaluation D.first) ⊔
      endpointFixedNodeValues (nodeEvaluation D.second D.node D.secondAtNode)
        (outerEvaluation D.second) = contactPlane X D.node := by
    simpa only [endpointFixedNodeValues, positiveNodeSpace, outerEvaluation] using D.spans
  exact ⟨(Submodule.quotEquivOfEq _ _ hr).trans
    (e.trans (Submodule.quotEquivOfEq _ _ hs))⟩

/-- Source of the number one in sm:vertical-cokernel. -/
theorem contactNormal_dimension {n : ℕ} (X : ContactFanoManifold n)
    (x : ComplexPoint X.variety) :
    Module.finrank ℂ (TangentFiber X.variety x ⧸ contactPlane X x) = 1 := by
  have hsurj : Function.Surjective (contactFiber X x) :=
    (vectorBundle_fiber_exact X.contact.sequence.distribution
      (intrinsicTangentBundle X.variety) X.contact.sequence.line
      X.contact.sequence.inclusion X.contact.sequence.form
      X.contact.sequence.comp_zero X.contact.sequence.shortExact x.map).2.1
  exact ((contactFiber X x).quotKerEquivOfSurjective hsurj).finrank_eq.trans
    (fiber_dimension X.contact.sequence.line x.map)

/-- The remaining comparison is precisely the tangent description of
relative Hom. It must identify vertical deformations with these ACTUAL
central sections and commute with BOTH endpoint evaluations. The schema
below records that commuting diagram; it is not a construction of it. -/
structure RelativeTangentComparison {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) where
  verticalSections : LinearMap.ker G.baseDifferential ≃ₗ[ℂ] CentralSections G
  firstFibre : G.firstTarget.Tangent ≃ₗ[ℂ]
    Fiber (pullbackModule D.first.curve.map (tangentSheaf X.variety.structureMap)) infinity.map
  secondFibre : G.secondTarget.Tangent ≃ₗ[ℂ]
    Fiber (pullbackModule D.second.curve.map (tangentSheaf X.variety.structureMap)) infinity.map
  endpointCompatibility : ∀ z : LinearMap.ker G.baseDifferential,
    (firstFibre (G.verticalEvaluation z).1, secondFibre (G.verticalEvaluation z).2) =
      endpointSectionsMap G (verticalSections z)

/- `relativeTangentComparison_exists` is proved in LSNodalTangent, after
the actual affine-lift and intrinsic tangent-fibre machinery. Its exact
header is preserved there, together with both endpoint normalizations. -/

theorem relativeTangentComparison_defectOne {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) (T : RelativeTangentComparison G) :
    G.VerticalDefectOne := by
  let e := T.firstFibre.prodCongr T.secondFibre
  have hmaps : e.toLinearMap.comp G.verticalEvaluation =
      (endpointSectionsMap G).comp T.verticalSections.toLinearMap := by
    apply LinearMap.ext
    intro z
    exact T.endpointCompatibility z
  have hr : (LinearMap.range G.verticalEvaluation).map e.toLinearMap =
      LinearMap.range (endpointSectionsMap G) := by
    rw [← LinearMap.range_comp, hmaps]
    exact LinearMap.range_comp_of_range_eq_top _ T.verticalSections.range
  let eqv := Submodule.Quotient.equiv _ _ e hr
  obtain ⟨targetEqv⟩ := endpointSections_cokernel G
  exact eqv.finrank_eq.trans (targetEqv.finrank_eq.trans
    (contactNormal_dimension X D.node))

/-- Library-sized target before tackling the fixed-end obstruction. -/
def proofOrder : List String :=
  [ "centralFiber_pushout; centralMap_left; centralMap_right",
    "normalizationRestriction_bijective; centralBundle_H1_vanishes",
    "outerEvaluation_surjective; endpointSections_cokernel",
    "square-zero universal evaluation -> RelativeTangentComparison",
    "contactNormal_dimension -> relativeTangentComparison_defectOne" ]

end Normalization

namespace Smoothing

open Lines

/-- The source normalization sequence and freeness give H1(E)=0, then
sm:relative-hom gives this smoothness assertion. -/
theorem germ_smoothingMap_smooth {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) :
    ∃ U : G.chart.scheme.Opens, Set.range G.chart.point.val ⊆ U ∧
      Smooth (U.ι ≫ G.inclusion ≫ G.hom.toBase) := by
  letI : IsLocallyNoetherian AffineLine := by
    dsimp [AffineLine]
    infer_instance
  letI : IsProper G.source.parameter := standardSource_proper G.source
  letI : Flat G.source.parameter := standardSource_flat G.source
  letI : LocallyOfFinitePresentation G.source.parameter := standardSource_lfp G.source
  letI : LocallyOfFinitePresentation G.hom.toBase :=
    relativeHom_lfp G.source X.variety (contactFano_hasProjectiveEmbedding X) G.hom
  letI : LocallyOfFinitePresentation (HomDeformationInput.ofRelativeHom G.hom).toBase := by
    change LocallyOfFinitePresentation G.hom.toBase
    infer_instance
  have hp : (G.chart.point.val ≫ G.inclusion) ≫ G.hom.toBase ≫ affineLineToC =
      𝟙 ComplexBase := by
    simpa only [Category.assoc, scalarPoint_overC] using
      congrArg (fun k => k ≫ affineLineToC) G.centre_base
  obtain ⟨U, hU, hS⟩ :=
    HomDeformationInput.StandardInputs.smooth_of_firstCohomology_vanishes
      G.source.parameter affineLineToC X.variety
      (HomDeformationInput.ofRelativeHom G.hom)
      (G.chart.point.val ≫ G.inclusion) hp (scalarPoint 0)
      (by
        change (G.chart.point.val ≫ G.inclusion) ≫ G.hom.toBase = scalarPoint 0
        exact (Category.assoc G.chart.point.val G.inclusion G.hom.toBase).trans G.centre_base)
      (by exact Normalization.centralBundle_H1_vanishes G)
  change Smooth (U.ι ≫ G.hom.toBase) at hS
  let V : G.chart.scheme.Opens := G.inclusion ⁻¹ᵁ U
  refine ⟨V, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact hU ⟨z, rfl⟩
  · letI : IsOpenImmersion G.inclusion := G.openImmersion
    letI : IsOpenImmersion (G.inclusion ∣_ U) := by
      dsimp only [morphismRestrict]
      infer_instance
    have hf : Smooth (G.inclusion ∣_ U) := inferInstance
    have hs : Smooth ((G.inclusion ∣_ U) ≫ (U.ι ≫ G.hom.toBase)) :=
      @AlgebraicGeometry.smooth_comp (V : Scheme) (U : Scheme)
        (G.inclusion ∣_ U) AffineLine (U.ι ≫ G.hom.toBase) hf hS
    have he : (G.inclusion ∣_ U) ≫ (U.ι ≫ G.hom.toBase) =
        V.ι ≫ (G.inclusion ≫ G.hom.toBase) :=
      morphismRestrict_ι_assoc G.inclusion U G.hom.toBase
    exact Eq.mp (congrArg (fun f : (V : Scheme) ⟶ AffineLine => Smooth f) he) hs

namespace BaseDifferentialProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual pointed affine parameter line, centred at the nodal value. -/
def baseChart : Charts.PointedAffine where
  scheme := AffineLine
  affine := inferInstance
  toC := affineLineToC
  point := ⟨scalarPoint 0, scalarPoint_overC 0⟩

/-- The canonical identification of parameter-line functions with C[s],
including its actual C-algebra structure. -/
def baseFunctions : baseChart.Ring →ₐ[ℂ] Polynomial ℂ where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom.hom
  commutes' := by
    intro c
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom
      (complexConstants affineLineToC c) = Polynomial.C c
    rw [complexConstants_apply_top]
    have h := congrArg (fun k : CommRingCat.of ℂ ⟶ Γ(AffineLine, ⊤) => k c)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)))
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv (Polynomial.C c) =
      affineLineToC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) at h
    rw [← h]
    exact Iso.inv_hom_id_apply _ _

theorem baseEvaluation (a : baseChart.Ring) :
    baseChart.evaluation a = (baseFunctions a).coeff 0 := by
  have h := congrArg (fun k : Γ(AffineLine, ⊤) ⟶ CommRingCat.of ℂ => k a)
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℂ))))
  change baseChart.evaluation a = (baseFunctions a).eval 0 at h
  exact h.trans (Polynomial.coeff_zero_eq_eval_zero _).symm

/-- The coefficient of s is the normalized tangent direction at s=0. -/
def unitDirection : baseChart.Tangent :=
  ⟨(Polynomial.lcoeff ℂ 1).comp baseFunctions.toLinearMap, by
    intro a b
    change (baseFunctions (a * b)).coeff 1 =
      baseChart.evaluation a * (baseFunctions b).coeff 1 +
        baseChart.evaluation b * (baseFunctions a).coeff 1
    rw [map_mul, Polynomial.mul_coeff_one, baseEvaluation, baseEvaluation]
    ring⟩

theorem unitDirection_parameter : unitDirection.val parameterFunction = 1 := by
  change ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv Polynomial.X)).coeff 1 = 1
  rw [Iso.inv_hom_id_apply]
  simp

/-- This is the actual smoothing morphism between the specified charts. -/
def smoothingChartMap {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) : Charts.Hom G.chart baseChart where
  map := G.inclusion ≫ G.hom.toBase
  overC := by
    change (G.inclusion ≫ G.hom.toBase) ≫ affineLineToC = G.chart.toC
    exact (Category.assoc G.inclusion G.hom.toBase affineLineToC).trans G.chart_overC
  atCentre := G.centre_base

end BaseDifferentialProof

theorem germ_baseDifferential_surjective {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) :
    Function.Surjective G.baseDifferential := by
  have hs : Charts.SmoothAtCentre (BaseDifferentialProof.smoothingChartMap G) := by
    obtain ⟨U, hU, hS⟩ := germ_smoothingMap_smooth G
    exact ⟨U, hU, by
      change Smooth (U.ι ≫ G.inclusion ≫ G.hom.toBase)
      exact hS⟩
  have hd := Charts.smooth_differential_surjective
    (BaseDifferentialProof.smoothingChartMap G) hs
  intro c
  obtain ⟨v, hv⟩ := hd (c • BaseDifferentialProof.unitDirection)
  refine ⟨v, ?_⟩
  change v.val ((G.inclusion ≫ G.hom.toBase).appTop parameterFunction) = c
  calc
    _ = ((BaseDifferentialProof.smoothingChartMap G).differential v).val
        parameterFunction := rfl
    _ = (c • BaseDifferentialProof.unitDirection).val parameterFunction :=
      congrArg (fun z : BaseDifferentialProof.baseChart.Tangent =>
        z.val parameterFunction) hv
    _ = c := by
      change c * BaseDifferentialProof.unitDirection.val parameterFunction = c
      rw [BaseDifferentialProof.unitDirection_parameter, mul_one]

namespace GermProof

open Normalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem first_central {F : StandardSource} (m : SourceMarks F) :
    scalarPoint 0 ≫ m.first = infinity.map ≫ m.branchLeft := by
  apply StandardSourceProof.coordinates_ext F
  · rw [Category.assoc, m.first_base, Category.comp_id, Category.assoc,
      m.left_base, ← Category.assoc, infinity.overC, Category.id_comp]
  · rw [Category.assoc, m.first_left, ← Category.assoc, scalarPoint_overC,
      Category.id_comp, Category.assoc, m.left_left, Category.comp_id]
  · rw [Category.assoc, m.first_right, ← Category.assoc, scalarPoint_overC,
      Category.id_comp, Category.assoc, m.left_right, ← Category.assoc,
      infinity.overC, Category.id_comp]

theorem second_central {F : StandardSource} (m : SourceMarks F) :
    scalarPoint 0 ≫ m.second = infinity.map ≫ m.branchRight := by
  apply StandardSourceProof.coordinates_ext F
  · rw [Category.assoc, m.second_base, Category.comp_id, Category.assoc,
      m.right_base, ← Category.assoc, infinity.overC, Category.id_comp]
  · rw [Category.assoc, m.second_left, ← Category.assoc, scalarPoint_overC,
      Category.id_comp, Category.assoc, m.right_left, ← Category.assoc,
      infinity.overC, Category.id_comp]
  · rw [Category.assoc, m.second_right, ← Category.assoc, scalarPoint_overC,
      Category.id_comp, Category.assoc, m.right_right, Category.comp_id]

theorem markedEvaluation_overC {d : ℕ} {F : StandardSource}
    {X : SmoothProperComplexVariety d} (H : RelativeHom F X)
    (m : AffineLine ⟶ F.source) (hm : m ≫ F.parameter = 𝟙 AffineLine) :
    markedEvaluation H m hm ≫ X.structureMap = H.toBase ≫ affineLineToC := by
  simp only [markedEvaluation, Category.assoc, H.overC,
    pullback.lift_snd_assoc, Category.id_comp]

theorem markedEvaluation_first_central {d : ℕ} {F : StandardSource}
    {X : SmoothProperComplexVariety d} (H : RelativeHom F X) (m : SourceMarks F)
    (p : ComplexBase ⟶ H.parameter) (hp : p ≫ H.toBase = scalarPoint 0) :
    p ≫ markedEvaluation H m.first m.first_base =
      infinity.map ≫ leftBranch m ≫
        sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp ≫ H.evaluation := by
  have h : p ≫ pullback.lift (H.toBase ≫ m.first) (𝟙 H.parameter)
      (by simp [Category.assoc, m.first_base]) =
      (infinity.map ≫ leftBranch m) ≫
        sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sourceBaseChangeMap, leftBranch,
        pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, hp, first_central]
    · simp only [Category.assoc, sourceBaseChangeMap, leftBranch,
        pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      rw [← Category.assoc, infinity.overC, Category.id_comp]
  simpa only [markedEvaluation, Category.assoc] using
    congrArg (fun k => k ≫ H.evaluation) h

theorem markedEvaluation_second_central {d : ℕ} {F : StandardSource}
    {X : SmoothProperComplexVariety d} (H : RelativeHom F X) (m : SourceMarks F)
    (p : ComplexBase ⟶ H.parameter) (hp : p ≫ H.toBase = scalarPoint 0) :
    p ≫ markedEvaluation H m.second m.second_base =
      infinity.map ≫ rightBranch m ≫
        sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp ≫ H.evaluation := by
  have h : p ≫ pullback.lift (H.toBase ≫ m.second) (𝟙 H.parameter)
      (by simp [Category.assoc, m.second_base]) =
      (infinity.map ≫ rightBranch m) ≫
        sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sourceBaseChangeMap, rightBranch,
        pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, hp, second_central]
    · simp only [Category.assoc, sourceBaseChangeMap, rightBranch,
        pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      rw [← Category.assoc, infinity.overC, Category.id_comp]
  simpa only [markedEvaluation, Category.assoc] using
    congrArg (fun k => k ≫ H.evaluation) h

/-- The glued map is represented by a point of the full relative Hom
scheme; both branch maps are recovered from the universal evaluation. -/
theorem nodalPoint_exists {n : ℕ} {X : ContactFanoManifold n} (D : SuitablePair X)
    (F : StandardSource) (m : SourceMarks F) (H : RelativeHom F X.variety) :
    ∃ p : ComplexBase ⟶ H.parameter, ∃ hp : p ≫ H.toBase = scalarPoint 0,
      leftBranch m ≫ sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp ≫
        H.evaluation = D.first.curve.map ∧
      rightBranch m ≫ sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp ≫
        H.evaluation = D.second.curve.map := by
  obtain ⟨f, hf, _⟩ := centralFiber_pushout m X.variety.scheme
    D.first.curve.map D.second.curve.map
    (D.firstAtNode.trans D.secondAtNode.symm)
  have ho : f ≫ X.variety.structureMap = centralBase F := by
    apply centralFiber_hom_ext m
    · rw [← Category.assoc, hf.1, D.first.curve.overC, leftBranch_over]
    · rw [← Category.assoc, hf.2, D.second.curve.overC, rightBranch_over]
  have ho' : f ≫ X.variety.structureMap =
      pullback.snd F.parameter (scalarPoint 0) ≫ scalarPoint 0 ≫ affineLineToC := by
    rw [scalarPoint_overC, Category.comp_id]
    exact ho
  obtain ⟨p, hp⟩ := (H.universal ComplexBase (scalarPoint 0)).surjective ⟨f, ho'⟩
  have he : sourceBaseChangeMap F (scalarPoint 0) H.toBase p.val p.property ≫
      H.evaluation = f := congrArg Subtype.val hp
  exact ⟨p.val, p.property, by rw [he]; exact hf.1,
    by rw [he]; exact hf.2⟩

/-- Lift a specified complex point to an actual affine open. -/
def chartOfOpen {Y : Scheme} (s : Y ⟶ ComplexBase)
    (p : PointsOver ComplexBase (𝟙 ComplexBase) Y s)
    (U : Y.Opens) (hU : IsAffineOpen U) (hp : Set.range p.val ⊆ (U : Set Y)) :
    Charts.PointedAffine where
  scheme := U.toScheme
  affine := hU
  toC := U.ι ≫ s
  point := ⟨IsOpenImmersion.lift U.ι p.val
    (by simpa only [Scheme.Opens.range_ι] using hp), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac, p.property]⟩

theorem chartOfOpen_point {Y : Scheme} (s : Y ⟶ ComplexBase)
    (p : PointsOver ComplexBase (𝟙 ComplexBase) Y s)
    (U : Y.Opens) (hU : IsAffineOpen U) (hp : Set.range p.val ⊆ (U : Set Y)) :
    (chartOfOpen s p U hU hp).point.val ≫ U.ι = p.val :=
  IsOpenImmersion.lift_fac _ _ _

theorem point_range_in_open {Y : Scheme} (p : ComplexBase ⟶ Y)
    (U : Y.Opens) (h : p (default : PrimeSpectrum ℂ) ∈ U) :
    Set.range p ⊆ (U : Set Y) := by
  rintro _ ⟨z, rfl⟩
  have hz : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim _ _
  change p (default : PrimeSpectrum ℂ) ∈ (U : Set Y) at h
  simpa only [hz] using h

/-- Simultaneously choose both actual endpoint charts and an affine source
chart on which both evaluations factor. The central map is kept fixed. -/
def ofNodalPoint {n : ℕ} {X : ContactFanoManifold n} (D : SuitablePair X)
    (F : StandardSource) (m : SourceMarks F) (H : RelativeHom F X.variety)
    (p : ComplexBase ⟶ H.parameter) (hp : p ≫ H.toBase = scalarPoint 0)
    (hl : leftBranch m ≫ sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp ≫
      H.evaluation = D.first.curve.map)
    (hr : rightBranch m ≫ sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp ≫
      H.evaluation = D.second.curve.map) : Germ D := by
  let y₁ : PointsOver ComplexBase (𝟙 ComplexBase) X.variety.scheme
      X.variety.structureMap := ⟨infinity.map ≫ D.first.curve.map, by
        rw [Category.assoc, D.first.curve.overC, infinity.overC]⟩
  let y₂ : PointsOver ComplexBase (𝟙 ComplexBase) X.variety.scheme
      X.variety.structureMap := ⟨infinity.map ≫ D.second.curve.map, by
        rw [Category.assoc, D.second.curve.overC, infinity.overC]⟩
  let hU₁exists := exists_isAffineOpen_mem_and_subset
    (X := X.variety.scheme) (x := y₁.val (default : PrimeSpectrum ℂ))
    (U := ⊤) (by trivial)
  let U₁ : X.variety.scheme.Opens := Classical.choose hU₁exists
  have hU₁ : IsAffineOpen U₁ := (Classical.choose_spec hU₁exists).1
  have hy₁ : y₁.val (default : PrimeSpectrum ℂ) ∈ U₁ :=
    (Classical.choose_spec hU₁exists).2.1
  let hU₂exists := exists_isAffineOpen_mem_and_subset
    (X := X.variety.scheme) (x := y₂.val (default : PrimeSpectrum ℂ))
    (U := ⊤) (by trivial)
  let U₂ : X.variety.scheme.Opens := Classical.choose hU₂exists
  have hU₂ : IsAffineOpen U₂ := (Classical.choose_spec hU₂exists).1
  have hy₂ : y₂.val (default : PrimeSpectrum ℂ) ∈ U₂ :=
    (Classical.choose_spec hU₂exists).2.1
  have hy₁range := point_range_in_open y₁.val U₁ hy₁
  have hy₂range := point_range_in_open y₂.val U₂ hy₂
  let A₁ := chartOfOpen X.variety.structureMap y₁ U₁ hU₁ hy₁range
  let A₂ := chartOfOpen X.variety.structureMap y₂ U₂ hU₂ hy₂range
  have hA₁ : A₁.point.val ≫ U₁.ι = y₁.val :=
    chartOfOpen_point X.variety.structureMap y₁ U₁ hU₁ hy₁range
  have hA₂ : A₂.point.val ≫ U₂.ι = y₂.val :=
    chartOfOpen_point X.variety.structureMap y₂ U₂ hU₂ hy₂range
  let e₁ := markedEvaluation H m.first m.first_base
  let e₂ := markedEvaluation H m.second m.second_base
  have he₁ : p ≫ e₁ = y₁.val := by
    change p ≫ markedEvaluation H m.first m.first_base =
      infinity.map ≫ D.first.curve.map
    rw [markedEvaluation_first_central H m p hp, hl]
  have he₂ : p ≫ e₂ = y₂.val := by
    change p ≫ markedEvaluation H m.second m.second_base =
      infinity.map ≫ D.second.curve.map
    rw [markedEvaluation_second_central H m p hp, hr]
  let W : H.parameter.Opens := e₁ ⁻¹ᵁ U₁ ⊓ e₂ ⁻¹ᵁ U₂
  have hpW : p (default : PrimeSpectrum ℂ) ∈ W := by
    constructor
    · change (p ≫ e₁) (default : PrimeSpectrum ℂ) ∈ U₁
      rw [he₁]
      exact hy₁
    · change (p ≫ e₂) (default : PrimeSpectrum ℂ) ∈ U₂
      rw [he₂]
      exact hy₂
  let hVexists := exists_isAffineOpen_mem_and_subset
    (X := H.parameter) (x := p (default : PrimeSpectrum ℂ)) (U := W) hpW
  let V : H.parameter.Opens := Classical.choose hVexists
  have hV : IsAffineOpen V := (Classical.choose_spec hVexists).1
  have hpV : p (default : PrimeSpectrum ℂ) ∈ V :=
    (Classical.choose_spec hVexists).2.1
  have hVW := (Classical.choose_spec hVexists).2.2
  let pC : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter
      (H.toBase ≫ affineLineToC) := ⟨p, by
        rw [← Category.assoc, hp, scalarPoint_overC]⟩
  have hpVrange := point_range_in_open p V hpV
  let A := chartOfOpen (H.toBase ≫ affineLineToC) pC V hV hpVrange
  have hA : A.point.val ≫ V.ι = p :=
    chartOfOpen_point (H.toBase ≫ affineLineToC) pC V hV hpVrange
  have hfirstRange : Set.range (V.ι ≫ e₁) ⊆ Set.range U₁.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hVW w.property).1
  have hsecondRange : Set.range (V.ι ≫ e₂) ⊆ Set.range U₂.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hVW w.property).2
  let f₁ : A.scheme ⟶ A₁.scheme :=
    IsOpenImmersion.lift U₁.ι (V.ι ≫ e₁) hfirstRange
  let f₂ : A.scheme ⟶ A₂.scheme :=
    IsOpenImmersion.lift U₂.ι (V.ι ≫ e₂) hsecondRange
  have hf₁ : f₁ ≫ U₁.ι = V.ι ≫ e₁ := IsOpenImmersion.lift_fac _ _ _
  have hf₂ : f₂ ≫ U₂.ι = V.ι ≫ e₂ := IsOpenImmersion.lift_fac _ _ _
  have hf₁C : f₁ ≫ A₁.toC = A.toC := by
    change f₁ ≫ (U₁.ι ≫ X.variety.structureMap) =
      V.ι ≫ (H.toBase ≫ affineLineToC)
    rw [← Category.assoc, hf₁, Category.assoc]
    exact congrArg (fun k => V.ι ≫ k)
      (markedEvaluation_overC H m.first m.first_base)
  have hf₂C : f₂ ≫ A₂.toC = A.toC := by
    change f₂ ≫ (U₂.ι ≫ X.variety.structureMap) =
      V.ι ≫ (H.toBase ≫ affineLineToC)
    rw [← Category.assoc, hf₂, Category.assoc]
    exact congrArg (fun k => V.ι ≫ k)
      (markedEvaluation_overC H m.second m.second_base)
  have hf₁point : A.point.val ≫ f₁ = A₁.point.val := by
    apply (cancel_mono U₁.ι).mp
    rw [Category.assoc, hf₁, ← Category.assoc, hA, he₁, hA₁]
  have hf₂point : A.point.val ≫ f₂ = A₂.point.val := by
    apply (cancel_mono U₂.ι).mp
    rw [Category.assoc, hf₂, ← Category.assoc, hA, he₂, hA₂]
  refine
    { source := F
      marks := m
      hom := H
      chart := A
      inclusion := V.ι
      openImmersion := inferInstance
      chart_overC := rfl
      centre_base := by rw [← Category.assoc, hA, hp]
      firstTarget := A₁
      firstOpen := U₁.ι
      firstOpen_immersion := inferInstance
      firstOpen_over := rfl
      firstCentre := hA₁
      secondTarget := A₂
      secondOpen := U₂.ι
      secondOpen_immersion := inferInstance
      secondOpen_over := rfl
      secondCentre := hA₂
      firstEval := ⟨f₁, hf₁C, hf₁point⟩
      secondEval := ⟨f₂, hf₂C, hf₂point⟩
      firstEval_spec := hf₁
      secondEval_spec := hf₂
      leftCentral := ?_
      rightCentral := ?_ }
  · calc
      _ = (leftBranch m ≫ sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp) ≫
          H.evaluation := by
        congr 1
        apply pullback.hom_ext
        · simp only [leftBranch, sourceBaseChangeMap, Category.assoc,
            pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [leftBranch, sourceBaseChangeMap, Category.assoc,
            pullback.lift_snd, pullback.lift_snd_assoc]
          rw [hA]
      _ = D.first.curve.map := by simpa only [Category.assoc] using hl
  · calc
      _ = (rightBranch m ≫ sourceBaseChangeMap F (scalarPoint 0) H.toBase p hp) ≫
          H.evaluation := by
        congr 1
        apply pullback.hom_ext
        · simp only [rightBranch, sourceBaseChangeMap, Category.assoc,
            pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [rightBranch, sourceBaseChangeMap, Category.assoc,
            pullback.lift_snd, pullback.lift_snd_assoc]
          rw [hA]
      _ = D.second.curve.map := by simpa only [Category.assoc] using hr

end GermProof

/-- Full relative-Hom representability and the glued map give such a germ;
it does not by itself imply unobstructedness or full endpoint evaluation. -/
theorem germ_exists {n : ℕ} {X : ContactFanoManifold n} (D : SuitablePair X) :
    Nonempty (Germ D) := by
  obtain ⟨F⟩ := standardSource_exists
  obtain ⟨m⟩ := sourceMarks_exists F
  obtain ⟨H⟩ := relativeHom_exists F X.variety (contactFano_hasProjectiveEmbedding X)
  obtain ⟨p, hp, hl, hr⟩ := GermProof.nodalPoint_exists D F m H
  exact ⟨GermProof.ofNodalPoint D F m H p hp hl hr⟩

/- `germ_verticalDefectOne` is proved in LSNodalTangent, immediately
after the exact normalized relative tangent comparison that it uses. -/

end Smoothing

/-! ## The differential-to-dualizing calculation at a node -/
namespace NodeDifferential

open LeBrunSalamon.PhaseTwentyNine

section PolynomialModel
variable (R : Type*) [CommRing R] (a : R)

abbrev Q := NodeAlgebra R a

/-- The logarithmic derivation, normalized by du |-> u and dv |-> -v.
It is first constructed on the FINITE-TYPE polynomial node. Identifying
its completion with the geometric dualizing map is a separate theorem.
Ordinary algebraic differentials of a formal power-series ring are not
silently identified with continuous differentials. -/
def polynomialLogDerivation :
    Derivation R (NodePolynomialRing R) (NodePolynomialRing R) :=
  MvPolynomial.mkDerivation R
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else -MvPolynomial.X 1)

theorem polynomialLogDerivation_u :
    polynomialLogDerivation R (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [polynomialLogDerivation]

theorem polynomialLogDerivation_v :
    polynomialLogDerivation R (MvPolynomial.X 1) = -MvPolynomial.X 1 := by
  simp [polynomialLogDerivation]

theorem polynomialLogDerivation_equation :
    polynomialLogDerivation R (nodeEquation R a) = 0 := by
  simp [nodeEquation, Derivation.leibniz, polynomialLogDerivation_u,
    polynomialLogDerivation_v, smul_eq_mul, mul_comm]

theorem polynomialLogDerivation_preservesIdeal :
    ∀ x : NodePolynomialRing R,
      (Ideal.Quotient.mkₐ R (nodeIdeal R a)) x = 0 →
      (Ideal.Quotient.mkₐ R (nodeIdeal R a)) (polynomialLogDerivation R x) = 0 := by
  intro x hx
  change Ideal.Quotient.mk (nodeIdeal R a) x = 0 at hx
  rw [Ideal.Quotient.eq_zero_iff_mem, nodeIdeal, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  change Ideal.Quotient.mk (nodeIdeal R a)
    (polynomialLogDerivation R (nodeEquation R a * y)) = 0
  rw [Derivation.leibniz, polynomialLogDerivation_equation]
  simp only [smul_eq_mul, mul_zero, add_zero, map_mul]
  have h : Ideal.Quotient.mk (nodeIdeal R a) (nodeEquation R a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [h, zero_mul]

theorem nodeQuotient_surjective :
    Function.Surjective (Ideal.Quotient.mkₐ R (nodeIdeal R a)) := by
  intro x
  exact Ideal.Quotient.mk_surjective x

def explicitLogDerivation : Derivation R (Q R a) (Q R a) :=
  Derivation.liftOfSurjective
    (f := Ideal.Quotient.mkₐ R (nodeIdeal R a))
    (nodeQuotient_surjective R a)
    (polynomialLogDerivation_preservesIdeal R a)

theorem explicitLogDerivation_u :
    explicitLogDerivation R a (nodeU R a) = nodeU R a := by
  change explicitLogDerivation R a
    ((Ideal.Quotient.mkₐ R (nodeIdeal R a)) (MvPolynomial.X 0)) = nodeU R a
  rw [explicitLogDerivation, Derivation.liftOfSurjective_apply,
    polynomialLogDerivation_u]
  rfl

theorem explicitLogDerivation_v :
    explicitLogDerivation R a (nodeV R a) = -nodeV R a := by
  change explicitLogDerivation R a
    ((Ideal.Quotient.mkₐ R (nodeIdeal R a)) (MvPolynomial.X 1)) = -nodeV R a
  rw [explicitLogDerivation, Derivation.liftOfSurjective_apply,
    polynomialLogDerivation_v, map_neg]
  rfl

theorem logDerivation_existsUnique :
    ∃! D : Derivation R (Q R a) (Q R a),
      D (nodeU R a) = nodeU R a ∧ D (nodeV R a) = -nodeV R a := by
  refine ⟨explicitLogDerivation R a,
    ⟨explicitLogDerivation_u R a, explicitLogDerivation_v R a⟩, ?_⟩
  intro D hD
  have h : D.compAlgebraMap (NodePolynomialRing R) =
      (explicitLogDerivation R a).compAlgebraMap (NodePolynomialRing R) := by
    apply MvPolynomial.derivation_ext
    intro i
    fin_cases i
    · change D (nodeU R a) = explicitLogDerivation R a (nodeU R a)
      rw [hD.1, explicitLogDerivation_u]
    · change D (nodeV R a) = explicitLogDerivation R a (nodeV R a)
      rw [hD.2, explicitLogDerivation_v]
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h p

def logDerivation : Derivation R (Q R a) (Q R a) :=
  Classical.choose (logDerivation_existsUnique R a)

theorem logDerivation_u : logDerivation R a (nodeU R a) = nodeU R a :=
  (Classical.choose_spec (logDerivation_existsUnique R a)).1.1

theorem logDerivation_v : logDerivation R a (nodeV R a) = -nodeV R a :=
  (Classical.choose_spec (logDerivation_existsUnique R a)).1.2

def toDualizing : KaehlerDifferential R (Q R a) →ₗ[Q R a] Q R a :=
  (logDerivation R a).liftKaehlerDifferential

theorem toDualizing_du :
    toDualizing R a (KaehlerDifferential.D R (Q R a) (nodeU R a)) = nodeU R a := by
  rw [toDualizing, Derivation.liftKaehlerDifferential_comp_D, logDerivation_u]

theorem toDualizing_dv :
    toDualizing R a (KaehlerDifferential.D R (Q R a) (nodeV R a)) = -nodeV R a := by
  rw [toDualizing, Derivation.liftKaehlerDifferential_comp_D, logDerivation_v]

/-- u,v generate the algebra, so du,dv generate its Kahler differentials. -/
def generators : (Q R a × Q R a) →ₗ[Q R a] KaehlerDifferential R (Q R a) :=
  (LinearMap.fst (Q R a) (Q R a) (Q R a)).smulRight
      (KaehlerDifferential.D R (Q R a) (nodeU R a)) +
    (LinearMap.snd (Q R a) (Q R a) (Q R a)).smulRight
      (KaehlerDifferential.D R (Q R a) (nodeV R a))

theorem generators_surjective : Function.Surjective (generators R a) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← KaehlerDifferential.span_range_derivation R (Q R a)]
  apply Submodule.span_le.mpr
  rintro z ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hgen (i : Fin 2) :
      KaehlerDifferential.D R (Q R a)
        (Ideal.Quotient.mk (nodeIdeal R a) (MvPolynomial.X i)) ∈
        LinearMap.range (generators R a) := by
    fin_cases i
    · exact ⟨(1, 0), by
        change (1 : Q R a) • KaehlerDifferential.D R (Q R a) (nodeU R a) +
          (0 : Q R a) • KaehlerDifferential.D R (Q R a) (nodeV R a) =
          KaehlerDifferential.D R (Q R a) (nodeU R a)
        exact (congrArg₂ (fun x y : KaehlerDifferential R (Q R a) => x + y)
          (one_smul (Q R a) (KaehlerDifferential.D R (Q R a) (nodeU R a)))
          (zero_smul (Q R a) (KaehlerDifferential.D R (Q R a) (nodeV R a)))).trans
            (add_zero _)
        ⟩
    · exact ⟨(0, 1), by
        change (0 : Q R a) • KaehlerDifferential.D R (Q R a) (nodeU R a) +
          (1 : Q R a) • KaehlerDifferential.D R (Q R a) (nodeV R a) =
          KaehlerDifferential.D R (Q R a) (nodeV R a)
        exact (congrArg₂ (fun x y : KaehlerDifferential R (Q R a) => x + y)
          (zero_smul (Q R a) (KaehlerDifferential.D R (Q R a) (nodeU R a)))
          (one_smul (Q R a) (KaehlerDifferential.D R (Q R a) (nodeV R a)))).trans
            (zero_add _)
        ⟩
  induction p using MvPolynomial.induction_on with
  | C c =>
    change KaehlerDifferential.D R (Q R a) (algebraMap R (Q R a) c) ∈ _
    simp
  | add p q hp hq =>
    rw [map_add, map_add]
    exact (LinearMap.range (generators R a)).add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, Derivation.leibniz]
    exact (LinearMap.range (generators R a)).add_mem
      ((LinearMap.range (generators R a)).smul_mem _ (hgen i))
      ((LinearMap.range (generators R a)).smul_mem _ hp)

/-- The relation is v du + u dv = 0. In particular no claim is made that
Omega is locally free at the singular point. -/
theorem generators_kernel :
    LinearMap.ker (generators R a) =
      Submodule.span (Q R a) {((nodeV R a, nodeU R a) : Q R a × Q R a)} := by
  classical
  let N : Submodule (Q R a) (Q R a × Q R a) :=
    Submodule.span (Q R a) {((nodeV R a, nodeU R a) : Q R a × Q R a)}
  let M := (Q R a × Q R a) ⧸ N
  let q : NodePolynomialRing R →ₐ[R] Q R a := Ideal.Quotient.mkₐ R (nodeIdeal R a)
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R (nodeIdeal R a)
  let D₀ : Derivation R (NodePolynomialRing R) M :=
    MvPolynomial.mkDerivation R
      (fun i : Fin 2 => if i = 0 then N.mkQ (1, 0) else N.mkQ (0, 1))
  have hscalar (p : NodePolynomialRing R) (z : M) : p • z = q p • z := by
    change p • z = algebraMap (NodePolynomialRing R) (Q R a) p • z
    exact (IsScalarTower.algebraMap_smul (Q R a) p z).symm
  have hD₀u : D₀ (MvPolynomial.X 0) = N.mkQ (1, 0) := by simp [D₀]
  have hD₀v : D₀ (MvPolynomial.X 1) = N.mkQ (0, 1) := by simp [D₀]
  have hqrel : q (nodeEquation R a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [nodeIdeal]))
  have hrel : D₀ (nodeEquation R a) = 0 := by
    rw [nodeEquation, map_sub, Derivation.leibniz, hD₀u, hD₀v,
      MvPolynomial.derivation_C, sub_zero, hscalar, hscalar]
    change nodeU R a • N.mkQ (0, 1) + nodeV R a • N.mkQ (1, 0) = 0
    rw [← map_smul, ← map_smul, ← map_add]
    have hpair : nodeU R a • ((0, 1) : Q R a × Q R a) +
        nodeV R a • ((1, 0) : Q R a × Q R a) = (nodeV R a, nodeU R a) := by
      ext <;> simp
    rw [hpair]
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span (by simp [N]))
  have hker : LinearMap.ker q.toLinearMap ≤ LinearMap.ker D₀.toLinearMap := by
    intro p hp
    change q p = 0 at hp
    have hp' : p ∈ nodeIdeal R a := Ideal.Quotient.eq_zero_iff_mem.mp hp
    change p ∈ Ideal.span ({nodeEquation R a} : Set (NodePolynomialRing R)) at hp'
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hp'
    change D₀ (nodeEquation R a * y) = 0
    rw [Derivation.leibniz, hrel, smul_zero, add_zero, hscalar, hqrel]
    exact Module.zero_smul (R := Q R a) (M := M) (D₀ y)
  let d₁ : Q R a →ₗ[R] M := q.toLinearMap.liftOfSurjective hq ⟨D₀.toLinearMap, hker⟩
  have hd (p : NodePolynomialRing R) : d₁ (q p) = D₀ p :=
    LinearMap.equivOfSurjective_apply hq hker
  let D : Derivation R (Q R a) M :=
    { toLinearMap := d₁
      map_one_eq_zero' := by
        exact (congrArg d₁ (map_one q).symm).trans
          ((hd 1).trans D₀.map_one_eq_zero)
      leibniz' := by
        intro x y
        obtain ⟨p, rfl⟩ := hq x
        obtain ⟨r, rfl⟩ := hq y
        rw [← map_mul q, hd, hd, hd, Derivation.leibniz, hscalar, hscalar] }
  have hDu : D (nodeU R a) = N.mkQ (1, 0) := by
    change d₁ (q (MvPolynomial.X 0)) = _
    rw [hd, hD₀u]
  have hDv : D (nodeV R a) = N.mkQ (0, 1) := by
    change d₁ (q (MvPolynomial.X 1)) = _
    rw [hd, hD₀v]
  have hleft (z : Q R a × Q R a) :
      D.liftKaehlerDifferential (generators R a z) = N.mkQ z := by
    rcases z with ⟨u, v⟩
    change D.liftKaehlerDifferential
        (u • KaehlerDifferential.D R (Q R a) (nodeU R a) +
          v • KaehlerDifferential.D R (Q R a) (nodeV R a)) = N.mkQ (u, v)
    rw [map_add, map_smul, map_smul,
      Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D, hDu, hDv,
      ← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  apply le_antisymm
  · intro z hz
    change z ∈ N
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQ z = 0
    change generators R a z = 0 at hz
    rw [← hleft z, hz, map_zero]
  · apply Submodule.span_le.mpr
    intro z hz
    have hz' : z = (nodeV R a, nodeU R a) := Set.mem_singleton_iff.mp hz
    subst z
    change nodeV R a • KaehlerDifferential.D R (Q R a) (nodeU R a) +
      nodeU R a • KaehlerDifferential.D R (Q R a) (nodeV R a) = 0
    rw [add_comm, ← Derivation.leibniz, node_relation]
    exact (KaehlerDifferential.D R (Q R a)).map_algebraMap a


def branchIdeal : Ideal (Q R a) := Ideal.span {nodeU R a, nodeV R a}

/-- Image of the ACTUAL universal differential-to-dualizing map. -/
theorem toDualizing_range : LinearMap.range (toDualizing R a) = branchIdeal R a := by
  apply le_antisymm
  · rintro z ⟨differentialForm, rfl⟩
    obtain ⟨⟨x, y⟩, rfl⟩ := generators_surjective R a differentialForm
    change toDualizing R a
        (x • KaehlerDifferential.D R (Q R a) (nodeU R a) +
          y • KaehlerDifferential.D R (Q R a) (nodeV R a)) ∈ branchIdeal R a
    rw [map_add, map_smul, map_smul, toDualizing_du, toDualizing_dv]
    apply (branchIdeal R a).add_mem
    · exact (branchIdeal R a).smul_mem x (Ideal.subset_span (by simp))
    · exact (branchIdeal R a).smul_mem y
        ((branchIdeal R a).neg_mem (Ideal.subset_span (by simp)))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨KaehlerDifferential.D R (Q R a) (nodeU R a), toDualizing_du R a⟩
    · refine ⟨-KaehlerDifferential.D R (Q R a) (nodeV R a), ?_⟩
      rw [map_neg, toDualizing_dv, neg_neg]


/-- The quotient fixes every base scalar, not just an abstract isomorphism type. -/
theorem branchQuotient :
    ∃ e : (Q R a ⧸ branchIdeal R a) ≃+* (R ⧸ Ideal.span {a}),
      ∀ r : R, e (Ideal.Quotient.mk (branchIdeal R a) (algebraMap R (Q R a) r)) =
        Ideal.Quotient.mk (Ideal.span {a}) r := by
  classical
  let polynomialQuotientMap : NodePolynomialRing R →+* (Q R a ⧸ branchIdeal R a) :=
    (Ideal.Quotient.mk (branchIdeal R a)).comp (Ideal.Quotient.mk (nodeIdeal R a))
  let β : R →+* (Q R a ⧸ branchIdeal R a) := polynomialQuotientMap.comp MvPolynomial.C
  have hX (i : Fin 2) : polynomialQuotientMap (MvPolynomial.X i) = 0 := by
    fin_cases i
    · change Ideal.Quotient.mk (branchIdeal R a) (nodeU R a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    · change Ideal.Quotient.mk (branchIdeal R a) (nodeV R a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hβa : β a = 0 := by
    change Ideal.Quotient.mk (branchIdeal R a) (algebraMap R (Q R a) a) = 0
    rw [← node_relation R a, map_mul]
    change polynomialQuotientMap (MvPolynomial.X 0) * polynomialQuotientMap (MvPolynomial.X 1) = 0
    rw [hX, hX]
    exact @MulZeroClass.mul_zero (Q R a ⧸ branchIdeal R a) inferInstance 0
  have hβ : Ideal.span ({a} : Set R) ≤ RingHom.ker β := by
    apply Ideal.span_le.mpr
    intro r hr
    have hr' : r = a := Set.mem_singleton_iff.mp hr
    subst r
    exact RingHom.mem_ker.mpr hβa
  let backward : (R ⧸ Ideal.span {a}) →+* (Q R a ⧸ branchIdeal R a) :=
    Ideal.Quotient.lift (Ideal.span {a}) β
      (fun r hr => RingHom.mem_ker.mp (hβ hr))
  let ρ : NodePolynomialRing R →+* (R ⧸ Ideal.span {a}) :=
    (Ideal.Quotient.mk (Ideal.span {a})).comp MvPolynomial.constantCoeff
  have haq : Ideal.Quotient.mk (Ideal.span ({a} : Set R)) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hrel : nodeIdeal R a ≤ RingHom.ker ρ := by
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = nodeEquation R a := Set.mem_singleton_iff.mp hp
    subst p
    apply RingHom.mem_ker.mpr
    simp [ρ, nodeEquation, haq]
  let ρ₁ : Q R a →+* (R ⧸ Ideal.span {a}) :=
    Ideal.Quotient.lift (nodeIdeal R a) ρ
      (fun p hp => RingHom.mem_ker.mp (hrel hp))
  have hbranch : branchIdeal R a ≤ RingHom.ker ρ₁ := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp [ρ₁, ρ, nodeU, nodeV]
  let forward : (Q R a ⧸ branchIdeal R a) →+* (R ⧸ Ideal.span {a}) :=
    Ideal.Quotient.lift (branchIdeal R a) ρ₁
      (fun z hz => RingHom.mem_ker.mp (hbranch hz))
  have hconst (p : NodePolynomialRing R) : polynomialQuotientMap p = β (MvPolynomial.constantCoeff p) := by
    induction p using MvPolynomial.induction_on with
    | C r =>
      change β r = β (MvPolynomial.constantCoeff (MvPolynomial.C r : NodePolynomialRing R))
      exact congrArg β (MvPolynomial.constantCoeff_C (Fin 2) r).symm
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, hX]
      have hz : polynomialQuotientMap p * (0 : Q R a ⧸ branchIdeal R a) = 0 :=
        @MulZeroClass.mul_zero (Q R a ⧸ branchIdeal R a) inferInstance
          (polynomialQuotientMap p)
      rw [hz, map_mul (MvPolynomial.constantCoeff : NodePolynomialRing R →+* R),
        MvPolynomial.constantCoeff_X]
      have hr : MvPolynomial.constantCoeff p * (0 : R) = 0 :=
        @MulZeroClass.mul_zero R inferInstance (MvPolynomial.constantCoeff p)
      rw [hr, map_zero]
  have hleft : Function.LeftInverse backward forward := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    change β (MvPolynomial.constantCoeff p) = polynomialQuotientMap p
    exact (hconst p).symm
  have hright : Function.RightInverse backward forward := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk (Ideal.span {a})
        (MvPolynomial.constantCoeff (MvPolynomial.C r)) =
      Ideal.Quotient.mk (Ideal.span {a}) r
    rw [MvPolynomial.constantCoeff_C]
  let e := RingEquiv.ofBijective forward ⟨hleft.injective, hright.surjective⟩
  refine ⟨e, ?_⟩
  intro r
  change Ideal.Quotient.mk (Ideal.span {a})
      (MvPolynomial.constantCoeff (MvPolynomial.C r)) =
    Ideal.Quotient.mk (Ideal.span {a}) r
  rw [MvPolynomial.constantCoeff_C]


/-- Exact algebraic content of ext:ideal-intersection. -/
theorem baseCoefficient_in_image_iff (r : R) :
    algebraMap R (Q R a) r ∈ LinearMap.range (toDualizing R a) ↔ a ∣ r := by
  rw [toDualizing_range, ← Ideal.mem_span_singleton]
  obtain ⟨e, he⟩ := branchQuotient R a
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← he r, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [map_zero, he r]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h


/-- A different nowhere-zero local generator changes the coefficient by
an actual unit. It does not change divisibility by the smoothing parameter. -/
theorem unitCoefficient_in_image_iff (r : R) (c : (Q R a)ˣ) :
    algebraMap R (Q R a) r * c.val ∈ LinearMap.range (toDualizing R a) ↔ a ∣ r := by
  rw [toDualizing_range, (branchIdeal R a).mul_unit_mem_iff_mem c.isUnit,
    ← toDualizing_range]
  exact baseCoefficient_in_image_iff R a r


/-- The map is surjective precisely on the base where the smoothing
parameter is invertible. No smoothness assumption is silently imposed. -/
theorem toDualizing_surjective_iff :
    Function.Surjective (toDualizing R a) ↔ IsUnit a := by
  constructor
  · intro hs
    apply isUnit_iff_dvd_one.mpr
    apply (baseCoefficient_in_image_iff R a 1).mp
    obtain ⟨v, hv⟩ := hs (algebraMap R (Q R a) 1)
    exact ⟨v, hv⟩
  · intro ha
    apply LinearMap.range_eq_top.mp
    rw [toDualizing_range, Ideal.eq_top_iff_one]
    have h := (baseCoefficient_in_image_iff R a 1).mpr (isUnit_iff_dvd_one.mp ha)
    simpa only [map_one, toDualizing_range] using h


/-- SOURCE ext:contact-order. The geometry must first show that the
contact differential equals h times one GLOBAL generator of L tensor omega.
The local calculation then gives divisibility by pi^r, not merely by pi. -/
theorem thickness_divides_coefficient (pi : R) (r : ℕ) (h : R)
    (c : (Q R (pi^r))ˣ)
    (himage : algebraMap R (Q R (pi^r)) h * c.val ∈
      LinearMap.range (toDualizing R (pi^r))) : pi^r ∣ h :=
  (unitCoefficient_in_image_iff R (pi^r) h c).mp himage

end PolynomialModel

/-- The global geometry cannot be replaced by the local calculation:
triviality of L tensor omega on the special tree and base change are
needed to make its coefficient a BASE scalar. -/
def geometricPrerequisites : List String :=
  [ "proper flat nodal genus-zero family over a DVR",
    "dualizing line and its formation under base change",
    "L tensor omega has multidegree (0,0) on the two special components",
    "H1 vanishing, Nakayama, and evaluation give a global generator",
    "completed differential-to-dualizing map agrees with du->u, dv->-v",
    "height-one component local rings use the same base uniformizer" ]

end NodeDifferential

/-! ## Regression tests for hypotheses that must not be weakened -/
namespace Regression

/-- A one-dimensional base direction cannot repair a two-dimensional defect. -/
def defectTwoEvaluation : ℂ →ₗ[ℂ] (ℂ × ℂ) where
  toFun z := (z, 0)
  map_add' := by intros; simp
  map_smul' := by intros; simp

theorem defectTwo_hasNoFixedEnds :
    ¬ ∃ z : ℂ, z = 1 ∧ defectTwoEvaluation z = 0 := by
  rintro ⟨z, hz, he⟩
  have h := congrArg Prod.fst he
  simpa [defectTwoEvaluation, hz] using h

theorem defectTwo_not_surjective : ¬ Function.Surjective defectTwoEvaluation := by
  intro h
  obtain ⟨z, hz⟩ := h (0, 1)
  have hs := congrArg Prod.snd hz
  simpa [defectTwoEvaluation] using hs

/-- A finite double cover need not descend every section. The polynomial
X is not a function of X², even though the latter gives a finite dominant
morphism A1 -> A1. Properness of that morphism is not effective descent. -/
theorem squareCover_has_nondescending_function :
    ¬ ∃ f : Polynomial ℂ, f.comp (Polynomial.X^2) = Polynomial.X := by
  rintro ⟨f, hf⟩
  have h := congrArg Polynomial.natDegree hf
  simp only [Polynomial.natDegree_comp, Polynomial.natDegree_X_pow,
    Polynomial.natDegree_X] at h
  omega

/-- The cusp subalgebra remembers the missing first-order coefficient. -/
def cuspSubalgebra : Subalgebra ℂ (Polynomial ℂ) :=
  Algebra.adjoin ℂ {(Polynomial.X : Polynomial ℂ)^2, Polynomial.X^3}

theorem cusp_has_no_linear_term (f : cuspSubalgebra) : Polynomial.coeff f.val 1 = 0 := by
  rcases f with ⟨f, hf⟩
  change Polynomial.coeff f 1 = 0
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl <;> simp
  | algebraMap c => simp
  | add f g hf hg ihf ihg => simp [Polynomial.coeff_add, ihf, ihg]
  | mul f g hf hg ihf ihg =>
    simp [Polynomial.mul_coeff_one, ihf, ihg]

theorem normalization_function_not_on_cusp :
    (Polynomial.X : Polynomial ℂ) ∉ cuspSubalgebra := by
  intro h
  have hc := cusp_has_no_linear_term ⟨Polynomial.X, h⟩
  simpa using hc

/-- The square and cube belong to the cusp although their ratio need not.
This illustrates why normality is needed in height-one extension. -/
theorem cusp_square_cube :
    (Polynomial.X : Polynomial ℂ)^2 ∈ cuspSubalgebra ∧
      (Polynomial.X : Polynomial ℂ)^3 ∈ cuspSubalgebra := by
  constructor <;> apply Algebra.subset_adjoin <;> simp

/-- Dimension of a finite vector space is not an evaluation map. A zero
map between equal nonzero dimensions cannot replace the actual derivative. -/
theorem equal_dimensions_do_not_force_evaluation :
    Module.finrank ℂ ℂ = Module.finrank ℂ ℂ ∧
      ¬ Function.Surjective (0 : ℂ →ₗ[ℂ] ℂ) := by
  refine ⟨rfl, ?_⟩
  intro h
  obtain ⟨x, hx⟩ := h 1
  simpa using hx

end Regression

/-! ## Integrated project route with refined smoothing and descent inputs -/

/-- The moving-pair construction and its two pullback comparisons remain
separate from contact-value descent. In particular no existence of the
final global kernel is stored in these data. -/
structure KernelExtensionInputs : Prop where
  construction : ∀ (n : ℕ) (X : ContactFanoManifold n), HasPrimitiveContactPicard X.contact →
    ∀ g : VeryFreeContactConic Lines.P Lines.marking X,
      Nonempty (Refinement.CoveredMovingPair Lines.P Lines.marking X g)
  recoverIdentity : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : Refinement.ProperPair X)
    (f : RationalCurve Lines.P X.variety)
    (Q : Refinement.CoveredCurveComparison Lines.P X D f)
    (B : ExternalSquareSections X.variety X.contact.sequence.line),
    D.DescendsTo B → CurveKernelIdentity Lines.P X.contact f B
  recoverSymmetry : ∀ (n : ℕ) (X : ContactFanoManifold n)
    (g : VeryFreeContactConic Lines.P Lines.marking X)
    (H : FullConicNeighborhood Lines.P Lines.marking X g)
    (B : ExternalSquareSections X.variety X.contact.sequence.line),
    (∀ t, CurveKernelIdentity Lines.P X.contact (H.curveAt t) B) →
      IsSymmetricExternalSection X.variety.structureMap X.contact.sequence.line B

/-- Explicit conversion: the descent field is proved by the finite-image,
all-sheet, ramification, purity and graph argument, from its supplied inputs.
It does NOT call Refinement.contactValueDescent_obligation. -/
def KernelExtensionInputs.toMovingPair (K : KernelExtensionInputs)
    (D : Descent.Inputs) : Refinement.MovingPairInputs Lines.P Lines.marking where
  construction := K.construction
  descent := by
    intro n X hp Q
    exact Descent.Inputs.assemble D X hp Q
  recoverIdentity := K.recoverIdentity
  recoverSymmetry := K.recoverSymmetry

/-- The preferred input interface now resolves smoothing and contact-value
descent into manuscript-sized obligations. Fixed source P1/[1:0] avoids
transporting every statement through arbitrary choices of C-structure.
No theorem asserts this package exists until its components are proved. -/
structure AlgebraicInputs : Prop where
  nonprimitive : NonprimitiveBranch
  smoothing : Smoothing.Inputs
  extension : KernelExtensionInputs
  descent : Descent.Inputs
  diagonal : Refinement.DiagonalInputs Lines.P Lines.marking
  jets : Refinement.Jets.Inputs
  Hamiltonians : HamiltonianEvaluation
  integration : AlgebraicIntegration
  classification : HomogeneousClassification

def AlgebraicInputs.toRefinement (H : AlgebraicInputs) :
    Refinement.AlgebraicInputs Lines.P Lines.marking where
  nonprimitive := H.nonprimitive
  smoothing := Smoothing.Inputs.assemble H.smoothing
  movingPair := KernelExtensionInputs.toMovingPair H.extension H.descent
  diagonal := H.diagonal
  jets := H.jets
  Hamiltonians := H.Hamiltonians
  integration := H.integration
  classification := H.classification

/-- Direct access to the newly derived smoothing stage. -/
theorem project_veryFreeConic (H : AlgebraicInputs) {n : ℕ}
    (X : ContactFanoManifold n) (hp : HasPrimitiveContactPicard X.contact) :
    Nonempty (VeryFreeContactConic Lines.P Lines.marking X) :=
  Smoothing.Inputs.assemble H.smoothing n X hp

/-- Direct access to contact-value descent, independent of jet generation
or homogeneous classification. This is still conditional on Descent.Inputs. -/
theorem project_contactValueDescent (H : Descent.Inputs) {n : ℕ}
    (X : ContactFanoManifold n) (hp : HasPrimitiveContactPicard X.contact)
    (D : Refinement.ProperPair X) :
    ∃! B : ExternalSquareSections X.variety X.contact.sequence.line, D.DescendsTo B :=
  Descent.Inputs.assemble H X hp D

theorem project_fullFamilyKernel (H : AlgebraicInputs) {n : ℕ}
    (X : ContactFanoManifold n) (hp : HasPrimitiveContactPicard X.contact)
    (g : VeryFreeContactConic Lines.P Lines.marking X) :
    Nonempty (FullFamilyKernel Lines.P Lines.marking X g) :=
  Refinement.MovingPairInputs.assemble Lines.P Lines.marking
    (KernelExtensionInputs.toMovingPair H.extension H.descent) n X hp g

theorem project_firstJets (H : AlgebraicInputs) {n : ℕ} (X : ContactFanoManifold n) :
    SeparatesFirstJets X.variety X.contact.sequence.line :=
  Skeleton.project_firstJets Lines.P Lines.marking
    (Refinement.AlgebraicInputs.toSkeleton Lines.P Lines.marking H.toRefinement) X

theorem project_Hamiltonians (H : AlgebraicInputs) {n : ℕ} (X : ContactFanoManifold n) :
    HamiltoniansSpan X := H.Hamiltonians n X (project_firstJets H X)

theorem project_contactFanoClassification (H : AlgebraicInputs) : ContactFanoClassification :=
  Refinement.project_contactFanoClassification Lines.P Lines.marking H.toRefinement

universe uR

structure ProjectInputs : Prop where
  algebraic : AlgebraicInputs
  riemannian : Skeleton.RiemannianInputs.{uR}

def ProjectInputs.toRefinement (H : ProjectInputs.{uR}) :
    Refinement.ProjectInputs.{uR} Lines.P Lines.marking where
  algebraic := H.algebraic.toRefinement
  riemannian := H.riemannian

theorem project_symmetricHomothety (H : ProjectInputs.{uR}) {n : ℕ}
    (M : ClosedPositiveQK.{uR} n) : Nonempty (SymmetricHomothety.{uR} M.space) :=
  Skeleton.project_symmetricHomothety Lines.P Lines.marking
    (Refinement.ProjectInputs.toSkeleton Lines.P Lines.marking H.toRefinement) M

theorem project_parallelCurvature (H : ProjectInputs.{uR}) {n : ℕ}
    (M : ClosedPositiveQK.{uR} n) : IsLocallyRiemannianSymmetric n M.space.carrier :=
  Refinement.project_parallelCurvature Lines.P Lines.marking H.toRefinement M

/-- PREFERRED ROOT for the expanded construction skeleton. All geometric
proof packages are explicit arguments. No local sorry or old admitted
main target occurs in this assembly. Foundational definitions may still
contain admissions, so this is NOT an axiom-free proof claim. -/
theorem leBrunSalamon_project (n : ℕ) (M : Type uR)
    [EMetricSpace M] [ChartedSpace (Model n) M] [IsManifold (model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
      (fun x : M => TangentSpace (model n) x)]
    [IsRiemannianManifold (model n) M] [Nonempty M] [CompactSpace M] [ConnectedSpace M]
    (H : ProjectInputs.{uR}) (hn : 2 ≤ n) (hQK : IsPositiveQuaternionicKahler n M) :
    IsLocallyRiemannianSymmetric n M :=
  Refinement.leBrunSalamon_project n M H.toRefinement hn hQK

end LeBrunSalamon.Construction



end


/- Canonical affine-chart tangent comparison and exact original wrappers; UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Refinement.Jets.PointFrame

variable {d : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
  {x : ComplexPoint X} (F : PointFrame X L x)

/-- The specified frame open, with its actual structure map and its original point lift. -/
def pointedAffineChart : Construction.Charts.PointedAffine where
  scheme := F.frame.openSet.toScheme
  affine := F.frame.isAffine
  toC := F.frame.openSet.ι ≫ X.structureMap
  point := ⟨F.pointLift, by rw [← Category.assoc, F.overPoint, x.overC]⟩

/-- The canonical top-section comparison retains the original complex algebra structure. -/
def chartRingEquiv : F.ChartRing ≃ₐ[ℂ] F.pointedAffineChart.Ring where
  toFun a := F.frame.openSet.topIso.inv a
  invFun a := F.frame.openSet.topIso.hom a
  left_inv a := by
    change (F.frame.openSet.topIso.inv ≫ F.frame.openSet.topIso.hom) a = a
    rw [Iso.inv_hom_id]
    rfl
  right_inv a := by
    change (F.frame.openSet.topIso.hom ≫ F.frame.openSet.topIso.inv) a = a
    rw [Iso.hom_inv_id]
    rfl
  map_add' a b := F.frame.openSet.topIso.inv.hom.map_add a b
  map_mul' a b := F.frame.openSet.topIso.inv.hom.map_mul a b
  commutes' c := by
    change F.frame.openSet.topIso.inv
        (Skeleton.complexConstant X.structureMap F.frame.openSet c) =
      Construction.complexConstants (F.frame.openSet.ι ≫ X.structureMap) c
    rw [Construction.complexConstants_apply_top]
    change F.frame.openSet.topIso.inv
        (X.scheme.presheaf.map (homOfLE (show F.frame.openSet ≤ ⊤ from le_top)).op
          (X.structureMap.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) =
      (F.frame.openSet.ι ≫ X.structureMap).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
    rw [ScalarSections.topIso_inv_restrict, Scheme.Hom.comp_appTop]
    rfl

/-- The two point maps evaluate exactly the same local function. -/
theorem chartRingEquiv_evaluation (a : F.ChartRing) :
    F.pointedAffineChart.evaluation (F.chartRingEquiv a) = F.evaluation a := rfl

/-- Actual point derivations are transported by the canonical ring equivalence. -/
def tangentChartEquiv : F.Tangent ≃ₗ[ℂ] F.pointedAffineChart.Tangent where
  toFun D := ⟨D.val.comp F.chartRingEquiv.symm.toLinearMap, by
    intro a b
    change D.val (F.chartRingEquiv.symm (a * b)) =
      F.pointedAffineChart.evaluation a * D.val (F.chartRingEquiv.symm b) +
        F.pointedAffineChart.evaluation b * D.val (F.chartRingEquiv.symm a)
    rw [map_mul, D.property]
    have he (z : F.pointedAffineChart.Ring) :
        F.evaluation (F.chartRingEquiv.symm z) = F.pointedAffineChart.evaluation z := by
      rw [← F.chartRingEquiv_evaluation, F.chartRingEquiv.apply_symm_apply]
    rw [he, he]⟩
  invFun D := ⟨D.val.comp F.chartRingEquiv.toLinearMap, by
    intro a b
    change D.val (F.chartRingEquiv (a * b)) =
      F.evaluation a * D.val (F.chartRingEquiv b) +
        F.evaluation b * D.val (F.chartRingEquiv a)
    rw [map_mul, D.property, F.chartRingEquiv_evaluation, F.chartRingEquiv_evaluation]⟩
  left_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change D.val (F.chartRingEquiv.symm (F.chartRingEquiv a)) = D.val a
    rw [F.chartRingEquiv.symm_apply_apply]
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change D.val (F.chartRingEquiv (F.chartRingEquiv.symm a)) = D.val a
    rw [F.chartRingEquiv.apply_symm_apply]
  map_add' D D' := by apply Subtype.ext; ext a; rfl
  map_smul' c D := by apply Subtype.ext; ext a; rfl

/-- Restriction to the frame open preserves the given relative smooth dimension. -/
theorem pointedAffineChart_smooth :
    SmoothOfRelativeDimension d F.pointedAffineChart.toC := by
  change SmoothOfRelativeDimension d (F.frame.openSet.ι ≫ X.structureMap)
  simpa only [Nat.zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + d)
      (F.frame.openSet.ι ≫ X.structureMap))

theorem tangent_dimension : Module.finrank ℂ F.Tangent = d := by
  calc
    Module.finrank ℂ F.Tangent = Module.finrank ℂ F.pointedAffineChart.Tangent :=
      F.tangentChartEquiv.finrank_eq
    _ = d := Construction.Charts.tangent_dimension_of_smooth
      F.pointedAffineChart d F.pointedAffineChart_smooth

end LeBrunSalamon.Refinement.Jets.PointFrame

namespace LeBrunSalamon.Refinement.Jets

open LeBrunSalamon.PhaseSeventeen LeBrunSalamon.PhaseTwentyTwo
open LeBrunSalamon.PhaseTwentySeven

/-- A sanity-check consequence: a normalized kernel needs at least dim(X)+1
terms in every finite external expansion. This is NOT a tensor-nondegeneracy claim. -/
theorem expansion_size_lower_bound {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} (K : NormalizedContactKernel X C)
    (E : ExternalExpansion X C.sequence.line K.twoPointSection) :
    2*n+2 ≤ E.size := by
  classical
  have hpoint : Nonempty (ComplexPoint X) := by
    by_contra h
    have htop : (⊥ : X.scheme.Opens) = ⊤ :=
      LeBrunSalamon.PhaseNine.ClosedPointGenerationProof.open_eq_top_of_complexPoints X ⊥
        (fun x => False.elim (h ⟨x⟩))
    obtain ⟨z⟩ := X.nonempty
    have hz : z ∈ (⊥ : X.scheme.Opens) := by rw [htop]; trivial
    exact hz
  let x : ComplexPoint X := Classical.choice hpoint
  obtain ⟨F⟩ := pointFrame_exists X C.sequence.line x
  obtain ⟨T⟩ := taylorRealization_exists K E F
  let J := coefficientJet E F
  have hi : J.IsProjectivelyImmersive := T.immersive (coefficient_value_nonzero K E F)
  let f : (ℂ × F.Tangent) →ₗ[ℂ] (Fin E.size → ℂ) :=
    (LinearMap.fst ℂ ℂ F.Tangent).smulRight J.value +
      J.derivative.comp (LinearMap.snd ℂ ℂ F.Tangent)
  have hzero : ∀ p : ℂ × F.Tangent, f p = 0 → p = 0 := by
    intro p hp
    change p.1 • J.value + J.derivative p.2 = 0 at hp
    have hd : J.derivative p.2 = (-p.1) • J.value := by
      rw [neg_smul]
      exact eq_neg_iff_add_eq_zero.mpr
        ((add_comm (J.derivative p.2) (p.1 • J.value)).trans hp)
    have hv : p.2 = 0 := hi.2 p.2 (-p.1) hd
    have hc : p.1 • J.value = 0 := by
      simpa only [hv, map_zero, add_zero] using hp
    exact Prod.ext ((smul_eq_zero.mp hc).resolve_right hi.1) hv
  have hf : Function.Injective f := by
    intro p q hpq
    apply sub_eq_zero.mp
    exact hzero (p - q) (by rw [map_sub, hpq, sub_self])
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_prod, Module.finrank_self, F.tangent_dimension,
    Module.finrank_fin_fun] at hd
  omega

end LeBrunSalamon.Refinement.Jets

end
