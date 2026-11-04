import LSRelativeHomFunctor
import LSSectionRepresentability
import LSAffineSectionRepresentability
import LSGeneratingUnitOpens
import RecompileExtensionsPart03
import LSConicSplitting

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

/- END RELOCATED POSITIVE-NODE DEPENDENCY: LSContactCompletion -/

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

namespace HomNeighborhood

/-- An actual affine open neighborhood in the full Hom scheme. All curve
maps and the evaluation morphism are restrictions of its universal map. -/
structure FreeOpen (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomSpacePresentation P X) (f : RationalCurve P X)
    (L : LineBundle X.scheme) where
  neighborhood : H.parameter.Opens
  affine : IsAffineOpen neighborhood
  marked : PointsOver ComplexBase (𝟙 ComplexBase) neighborhood.toScheme
    (neighborhood.ι ≫ H.toC)
  center : H.mapAt P
    ⟨marked.val ≫ neighborhood.ι, by simpa [Category.assoc] using marked.property⟩ = f.map
  smooth : Smooth (neighborhood.ι ≫ H.toC)
  irreducible : IrreducibleSpace neighborhood.toScheme
  smoothEvaluation : Smooth
    (rationalSourceMap P (⟨neighborhood.ι, rfl⟩ :
      PointsOver neighborhood.toScheme (neighborhood.ι ≫ H.toC) H.parameter H.toC) ≫
        H.evaluation)
  dominantEvaluation : DenseRange (fun z =>
    (rationalSourceMap P (⟨neighborhood.ι, rfl⟩ :
      PointsOver neighborhood.toScheme (neighborhood.ι ≫ H.toC) H.parameter H.toC) ≫
        H.evaluation) z)
  curveAt : ∀ t : PointsOver ComplexBase (𝟙 ComplexBase) neighborhood.toScheme
    (neighborhood.ι ≫ H.toC), RationalCurve P X
  curveAt_spec : ∀ t, (curveAt t).map = H.mapAt P
    ⟨t.val ≫ neighborhood.ι, by simpa [Category.assoc] using t.property⟩
  free : ∀ t, IsFreeRationalCurve P X (intrinsicTangentBundle X) (curveAt t)
  degree : ∀ t, degreeOnCurve P p (curveAt t).toParametrizedCurve L =
    degreeOnCurve P p f.toParametrizedCurve L
  preservesVeryFree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f →
    ∀ t, IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) (curveAt t)

namespace StandardInputs

/-- Standard free-curve neighborhood corollary: Kollár, Rational Curves,
II.3.2 and II.3.5; Kollár, Portugaliae Math. 67 (2010), Theorem 18 and
Definition 24; Gounelas, Documenta Math. 21 (2016), pp.298--299,305.
Degree constancy is Stacks 0B9T on the proper flat P1 family. The input
contains no contact or Picard hypothesis and no nodal or descent claim. -/
theorem free_neighborhood (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} (X : SmoothProperComplexVariety d) (hX : HasProjectiveEmbedding X)
    (H : HomSpacePresentation P X) (f : RationalCurve P X)
    (hf : IsFreeRationalCurve P X (intrinsicTangentBundle X) f)
    (L : LineBundle X.scheme) : Nonempty (FreeOpen P p X H f L) := by
  sorry

end StandardInputs

theorem mapAt_restrict (P : ProjectiveLineOverC) {d : ℕ}
    {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (U : H.parameter.Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC)) :
    H.mapAt P ⟨t.val ≫ U.ι, by simpa [Category.assoc] using t.property⟩ =
      pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val)
        (by simp [Category.assoc, t.property]) ≫
      (rationalSourceMap P (⟨U.ι, rfl⟩ :
        PointsOver U.toScheme (U.ι ≫ H.toC) H.parameter H.toC) ≫ H.evaluation) := by
  dsimp only [HomSpacePresentation.mapAt]
  refine (congrArg
    (fun k : ProjectiveLine ⟶ RationalSourceOver P H.parameter H.toC =>
      k ≫ H.evaluation) ?_).trans (Category.assoc _ _ _)
  apply pullback.hom_ext <;> simp [rationalSourceMap, Category.assoc]

/-- The existing splitting and interpolation criteria give freeness from
very-freeness without invoking any contact-manifold conclusion. -/
theorem veryFree_isFree (P : ProjectiveLineOverC) {d : ℕ}
    (X : SmoothProperComplexVariety d) (f : RationalCurve P X)
    (hf : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    IsFreeRationalCurve P X (intrinsicTangentBundle X) f := by
  let E := pullbackBundle f.map (intrinsicTangentBundle X)
  obtain ⟨p, q, hpq⟩ := hf.1
  obtain ⟨a, ha⟩ := birkhoffGrothendieck P p E
  have hpos : a.IsVeryFree :=
    (splitBundle_twoPointEvaluation_iff P p q hpq E a ha).mp (hf.2 p q hpq)
  change IsGloballyGenerated E.sheaf
  apply (splitBundle_globallyGenerated_iff P p E a ha).mpr
  intro i
  have hi := hpos i
  omega

end HomNeighborhood

namespace Lines

theorem positiveNodeSpace_horizontal {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    positiveNodeSpace f x hx ≤ contactPlane X x :=
  ContactPositive.positiveNodeSpace_horizontal f x hx

/-- SOURCE lines:positive. No claim that EVERY free contact line has the
standard generic splitting: special splitting types must remain possible. -/
theorem positiveNodeSpace_rank_le {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) :
    Module.finrank ℂ (positiveNodeSpace f x hx) ≤ n :=
  ContactPositive.positiveNodeSpace_rank_le f x hx

theorem positiveNodeSpace_isotropic {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (u v : Fiber X.contact.sequence.distribution.sheaf x.map)
    (hu : fiberMap X.contact.sequence.inclusion x.map u ∈ positiveNodeSpace f x hx)
    (hv : fiberMap X.contact.sequence.inclusion x.map v ∈ positiveNodeSpace f x hx) :
    leviFiberValue X x u v = 0 :=
  ContactPositive.positiveNodeSpace_isotropic f x hx u v hu hv

set_option maxHeartbeats 800000 in
/-- Output of lines:suitable-pair. All subspaces and tangent vectors below
come from actual curve maps, their pullback tangent bundles, and df. -/
structure SuitablePair {n : ℕ} (X : ContactFanoManifold n) where
  node : ComplexPoint X.variety
  first : FreeLine X
  second : FreeLine X
  firstAtNode : marking.map ≫ first.curve.map = node.map
  secondAtNode : marking.map ≫ second.curve.map = node.map
  firstParameter : Fiber (tangentSheaf P.structureMap) marking.map
  secondParameter : Fiber (tangentSheaf P.structureMap) marking.map
  firstParameter_ne : firstParameter ≠ 0
  secondParameter_ne : secondParameter ≠ 0
  spans : positiveNodeSpace first node firstAtNode ⊔
    positiveNodeSpace second node secondAtNode = contactPlane X node
  transverse : NonzeroLeviPair X node
    (nodeDifferential first node firstAtNode firstParameter)
    (nodeDifferential second node secondAtNode secondParameter)

set_option backward.isDefEq.respectTransparency false in
theorem suitablePair_complementary {n : ℕ} {X : ContactFanoManifold n}
    (D : SuitablePair X) :
    Disjoint (positiveNodeSpace D.first D.node D.firstAtNode)
      (positiveNodeSpace D.second D.node D.secondAtNode) := by
  letI : FiniteDimensional ℂ (TangentFiber X.variety D.node) :=
    fiber_finite (intrinsicTangentBundle X.variety) D.node.map
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq
    (positiveNodeSpace D.first D.node D.firstAtNode)
    (positiveNodeSpace D.second D.node D.secondAtNode)
  rw [D.spans, contactPlane_dimension] at hadd
  have hfirst := positiveNodeSpace_rank_le D.first D.node D.firstAtNode
  have hsecond := positiveNodeSpace_rank_le D.second D.node D.secondAtNode
  apply disjoint_iff.mpr
  apply Submodule.finrank_eq_zero.mp
  omega

set_option backward.isDefEq.respectTransparency false in
theorem suitablePair_positive_dimensions {n : ℕ} {X : ContactFanoManifold n}
    (D : SuitablePair X) :
    Module.finrank ℂ (positiveNodeSpace D.first D.node D.firstAtNode) = n ∧
    Module.finrank ℂ (positiveNodeSpace D.second D.node D.secondAtNode) = n := by
  letI : FiniteDimensional ℂ (TangentFiber X.variety D.node) :=
    fiber_finite (intrinsicTangentBundle X.variety) D.node.map
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq
    (positiveNodeSpace D.first D.node D.firstAtNode)
    (positiveNodeSpace D.second D.node D.secondAtNode)
  rw [D.spans, contactPlane_dimension] at hadd
  have hfirst := positiveNodeSpace_rank_le D.first D.node D.firstAtNode
  have hsecond := positiveNodeSpace_rank_le D.second D.node D.secondAtNode
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Changing a nonzero source tangent rescales, but does not erase, the Levi test. -/
theorem nonzeroLeviPair_rescale {n : ℕ} (X : ContactFanoManifold n)
    (x : ComplexPoint X.variety) (a b : TangentFiber X.variety x)
    (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0) :
    NonzeroLeviPair X x (c • a) (d • b) ↔ NonzeroLeviPair X x a b := by
  constructor
  · rintro ⟨u, v, hu, hv, hlevi⟩
    refine ⟨c⁻¹ • u, d⁻¹ • v, ?_, ?_, ?_⟩
    · rw [map_smul, hu, inv_smul_smul₀ hc]
    · rw [map_smul, hv, inv_smul_smul₀ hd]
    · rw [leviFiberValue_smul_smul]
      exact smul_ne_zero (inv_ne_zero hc) (smul_ne_zero (inv_ne_zero hd) hlevi)
  · rintro ⟨u, v, hu, hv, hlevi⟩
    refine ⟨c • u, d • v, ?_, ?_, ?_⟩
    · rw [map_smul, hu]
    · rw [map_smul, hv]
    · rw [leviFiberValue_smul_smul]
      exact smul_ne_zero hc (smul_ne_zero hd hlevi)

/- The unchanged suitablePair_exists declaration is proved in LSSuitablePair
after the actual bounded Hom families and cone-addition geometry. -/

/-- A smooth irreducible parameter family with ACTUAL smooth dominant evaluation.
This is weaker than representing the Hom functor, but adequate for divisor tests. -/
structure CoveringFamily {n : ℕ} (X : ContactFanoManifold n) where
  parameter : Scheme
  toC : parameter ⟶ ComplexBase
  smooth : Smooth toC
  irreducible : IrreducibleSpace parameter
  /-- Zariski quasi-compactness; together with smoothness this is finite type over C. -/
  quasiCompact : CompactSpace parameter
  evaluation : RationalSourceOver P parameter toC ⟶ X.variety.scheme
  overC : evaluation ≫ X.variety.structureMap =
    pullback.fst P.structureMap toC ≫ P.structureMap
  smoothEvaluation : Smooth evaluation
  dominantEvaluation : DenseRange (fun z => evaluation z)
  lineAt : ∀ t : PointsOver ComplexBase (𝟙 ComplexBase) parameter toC, FreeLine X
  lineAt_spec : ∀ t, (lineAt t).curve.map =
    pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val)
      (by simp [Category.assoc, t.property]) ≫ evaluation

/-- SOURCE lines:free-cover; no connectedness or reducedness of later
pullback fibres is assumed here. -/
theorem coveringFamily_exists {n : ℕ} (X : ContactFanoManifold n)
    (hPic : HasPrimitiveContactPicard X.contact) : Nonempty (CoveringFamily X) := by
  classical
  obtain ⟨f, hdegree, hfree⟩ := primitiveContactFano_hasFreeContactLine P marking X hPic
  obtain ⟨H⟩ := homSpacePresentation_exists P X.variety (contactFano_hasProjectiveEmbedding X)
  obtain ⟨O⟩ := HomNeighborhood.StandardInputs.free_neighborhood P marking X.variety
    (contactFano_hasProjectiveEmbedding X) H f hfree X.contact.sequence.line
  letI : IsAffine O.neighborhood.toScheme := O.affine
  refine ⟨{
    parameter := O.neighborhood.toScheme
    toC := O.neighborhood.ι ≫ H.toC
    smooth := O.smooth
    irreducible := O.irreducible
    quasiCompact := inferInstance
    evaluation := rationalSourceMap P ⟨O.neighborhood.ι, rfl⟩ ≫ H.evaluation
    overC := ?_
    smoothEvaluation := O.smoothEvaluation
    dominantEvaluation := O.dominantEvaluation
    lineAt := fun t => ⟨O.curveAt t, (O.degree t).trans hdegree, O.free t⟩
    lineAt_spec := ?_ }⟩
  · rw [Category.assoc, H.overC, ← Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _
  · intro t
    exact (O.curveAt_spec t).trans (HomNeighborhood.mapAt_restrict P H O.neighborhood t)

end Lines

end LeBrunSalamon.Construction

namespace LeBrunSalamon.Skeleton

open LeBrunSalamon.Construction
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.PhaseThirtyTwo LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.Core

theorem fullConicNeighborhood_exists (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} (X : ContactFanoManifold n)
    (g : VeryFreeContactConic P p X) : Nonempty (FullConicNeighborhood P p X g) := by
  classical
  obtain ⟨H⟩ := homSpacePresentation_exists P X.variety (contactFano_hasProjectiveEmbedding X)
  obtain ⟨O⟩ := HomNeighborhood.StandardInputs.free_neighborhood P p X.variety
    (contactFano_hasProjectiveEmbedding X) H g.curve
    (HomNeighborhood.veryFree_isFree P X.variety g.curve g.veryFree) X.contact.sequence.line
  exact ⟨{
    homSpace := H
    neighborhood := O.neighborhood
    marked := O.marked
    center := O.center
    smooth := O.smooth
    curveAt := O.curveAt
    curveAt_spec := O.curveAt_spec
    degreeTwo := fun t => (O.degree t).trans g.contactDegreeTwo
    veryFree := O.preservesVeryFree g.veryFree }⟩

end LeBrunSalamon.Skeleton

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

/-! ## The standard conic source and the genuine relative Hom functor -/
namespace Smoothing

open Lines

abbrev AffineLine : Scheme := Spec (CommRingCat.of (Polynomial ℂ))
def affineLineToC : AffineLine ⟶ ComplexBase :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ))
def scalarPoint (c : ℂ) : ComplexBase ⟶ AffineLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))

theorem scalarPoint_overC (c : ℂ) :
    scalarPoint c ≫ affineLineToC = 𝟙 ComplexBase := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) = _
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of ℂ) using 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp

def parameterFunction : RingSections AffineLine ⊤ :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv Polynomial.X

/-- The homogeneous equation U1*V1=s*U0*V0 on an arbitrary test scheme.
Nonreduced tests matter: set-theoretic zero loci lose first-order smoothings. -/
def ConicEquation {T : Scheme} (t : T ⟶ AffineLine)
    (u v : T ⟶ ProjectiveLine) : Prop :=
  let C := projectiveCoordinates 1
  tensorSection (pullSection u (C.coordinate 1)) (pullSection v (C.coordinate 1)) =
    sectionFromValue (t.appTop parameterFunction •
      sectionValue (tensorSection (pullSection u (C.coordinate 0))
        (pullSection v (C.coordinate 0))))

/-- A presentation of the fixed (1,1)-hypersurface, NOT an arbitrary family
of genus-zero curves. The universal property specifies its scheme structure. -/
structure StandardSource where
  source : Scheme
  parameter : source ⟶ AffineLine
  left : source ⟶ ProjectiveLine
  right : source ⟶ ProjectiveLine
  left_over : left ≫ P.structureMap = parameter ≫ affineLineToC
  right_over : right ≫ P.structureMap = parameter ≫ affineLineToC
  equation : ConicEquation parameter left right
  universal : ∀ (T : Scheme) (sT : T ⟶ ComplexBase)
    (t : PointsOver T sT AffineLine affineLineToC)
    (u v : PointsOver T sT ProjectiveLine P.structureMap),
    ConicEquation t.val u.val v.val →
      ∃! h : T ⟶ source, h ≫ parameter = t.val ∧ h ≫ left = u.val ∧ h ≫ right = v.val

/- The exact standardSource_flat declaration is proved below after the
three actual chosen-coordinate affine charts have been constructed. -/

/-- The node is [1:0] in each factor; the two outer endpoints are fixed.
All component and section maps are tied to these coordinates. -/
structure SourceMarks (F : StandardSource) where
  branchLeft : ProjectiveLine ⟶ F.source
  branchRight : ProjectiveLine ⟶ F.source
  left_base : branchLeft ≫ F.parameter = P.structureMap ≫ scalarPoint 0
  right_base : branchRight ≫ F.parameter = P.structureMap ≫ scalarPoint 0
  left_left : branchLeft ≫ F.left = 𝟙 ProjectiveLine
  left_right : branchLeft ≫ F.right = P.structureMap ≫ marking.map
  right_left : branchRight ≫ F.left = P.structureMap ≫ marking.map
  right_right : branchRight ≫ F.right = 𝟙 ProjectiveLine
  node_agreement : marking.map ≫ branchLeft = marking.map ≫ branchRight
  first : AffineLine ⟶ F.source
  second : AffineLine ⟶ F.source
  first_base : first ≫ F.parameter = 𝟙 AffineLine
  second_base : second ≫ F.parameter = 𝟙 AffineLine
  first_left : first ≫ F.left = affineLineToC ≫ infinity.map
  first_right : first ≫ F.right = affineLineToC ≫ marking.map
  second_left : second ≫ F.left = affineLineToC ≫ marking.map
  second_right : second ≫ F.right = affineLineToC ≫ infinity.map

namespace SourceMarksProof

set_option backward.isDefEq.respectTransparency false in
theorem scalarUnitSection_zero : scalarUnitSection 0 = 0 := by
  rw [ProjectiveCoordinateProof.scalarUnitSection_eq_scalarEnd, map_zero,
    GlobalScalars.scalarEnd_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The chosen point [1:0] is tied to the same universal quotient used
in the defining equation of the conic source. -/
theorem marking_second_coordinate_zero :
    pullSection marking.map ((projectiveCoordinates 1).coordinate 1) = 0 := by
  let v : Fin 2 → ℂ := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa [v] using h0
  let x := Classical.choose
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)
  obtain ⟨e, he⟩ := (Classical.choose_spec
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)).1.2
  change pullSection x.val ((projectiveCoordinates 1).coordinate 1) = 0
  apply (cancel_mono e.hom).mp
  rw [zero_comp, he 1]
  simpa [v] using scalarUnitSection_zero

set_option backward.isDefEq.respectTransparency false in
theorem infinity_first_coordinate_zero :
    pullSection infinity.map ((projectiveCoordinates 1).coordinate 0) = 0 := by
  let v : Fin 2 → ℂ := Pi.single 1 1
  have hv : v ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simpa [v] using h1
  let x := Classical.choose
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)
  obtain ⟨e, he⟩ := (Classical.choose_spec
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)).1.2
  change pullSection x.val ((projectiveCoordinates 1).coordinate 0) = 0
  apply (cancel_mono e.hom).mp
  rw [zero_comp, he 0]
  simpa [v] using scalarUnitSection_zero

set_option backward.isDefEq.respectTransparency false in
theorem pullSection_comp_zero {T Y Z : Scheme} (s : T ⟶ Y) (x : Y ⟶ Z)
    {E : OModule Z} (a : AlgebraicSection E) (ha : pullSection x a = 0) :
    pullSection (s ≫ x) a = 0 := by
  rw [← LeBrunSalamon.Construction.pullSection_comp s x a, ha]
  simp only [pullSection, restrictSection, Functor.map_zero, comp_zero, zero_comp]

theorem scalarPoint_zero_parameter : (scalarPoint 0).appTop parameterFunction = 0 := by
  let φ : CommRingCat.of (Polynomial ℂ) ⟶ CommRingCat.of ℂ :=
    CommRingCat.ofHom (Polynomial.evalRingHom 0)
  have h := (congrArg
    (fun k : CommRingCat.of (Polynomial ℂ) ⟶ Γ(ComplexBase, ⊤) => k Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality φ)).symm
  change (scalarPoint 0).appTop parameterFunction =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (φ Polynomial.X) at h
  simpa [φ] using h

theorem constant_zero_parameter {T : Scheme} (s : T ⟶ ComplexBase) :
    (s ≫ scalarPoint 0).appTop parameterFunction = 0 := by
  rw [Scheme.Hom.comp_appTop]
  change s.appTop ((scalarPoint 0).appTop parameterFunction) = 0
  rw [scalarPoint_zero_parameter, map_zero]

theorem equation_zero_parameter_right {T : Scheme} (t : T ⟶ AffineLine)
    (u v : T ⟶ ProjectiveLine)
    (ht : t.appTop parameterFunction = 0)
    (hv : pullSection v ((projectiveCoordinates 1).coordinate 1) = 0) :
    ConicEquation t u v := by
  dsimp [ConicEquation]
  rw [hv, tensorSection_zero_right, ht, zero_smul, sectionFromValue_zero]

theorem equation_zero_parameter_left {T : Scheme} (t : T ⟶ AffineLine)
    (u v : T ⟶ ProjectiveLine)
    (ht : t.appTop parameterFunction = 0)
    (hu : pullSection u ((projectiveCoordinates 1).coordinate 1) = 0) :
    ConicEquation t u v := by
  dsimp [ConicEquation]
  rw [hu, tensorSection_zero_left, ht, zero_smul, sectionFromValue_zero]

theorem equation_first_mark {T : Scheme} (s : T ⟶ ComplexBase)
    (t : T ⟶ AffineLine) :
    ConicEquation t (s ≫ infinity.map) (s ≫ marking.map) := by
  have hu := pullSection_comp_zero s infinity.map
    ((projectiveCoordinates 1).coordinate 0) infinity_first_coordinate_zero
  have hv := pullSection_comp_zero s marking.map
    ((projectiveCoordinates 1).coordinate 1) marking_second_coordinate_zero
  dsimp [ConicEquation]
  rw [hv, tensorSection_zero_right, hu, tensorSection_zero_left,
    sectionValue_zero, smul_zero, sectionFromValue_zero]

theorem equation_second_mark {T : Scheme} (s : T ⟶ ComplexBase)
    (t : T ⟶ AffineLine) :
    ConicEquation t (s ≫ marking.map) (s ≫ infinity.map) := by
  have hu := pullSection_comp_zero s marking.map
    ((projectiveCoordinates 1).coordinate 1) marking_second_coordinate_zero
  have hv := pullSection_comp_zero s infinity.map
    ((projectiveCoordinates 1).coordinate 0) infinity_first_coordinate_zero
  dsimp [ConicEquation]
  rw [hu, tensorSection_zero_left, hv, tensorSection_zero_right,
    sectionValue_zero, smul_zero, sectionFromValue_zero]

end SourceMarksProof

theorem sourceMarks_exists (F : StandardSource) : Nonempty (SourceMarks F) := by
  have hmark (T : Scheme) (s : T ⟶ ComplexBase) :
      (s ≫ marking.map) ≫ P.structureMap = s := by
    simp only [Category.assoc, marking.overC, Category.comp_id]
  have hinfty (T : Scheme) (s : T ⟶ ComplexBase) :
      (s ≫ infinity.map) ≫ P.structureMap = s := by
    simp only [Category.assoc, infinity.overC, Category.comp_id]
  have hbase (T : Scheme) (s : T ⟶ ComplexBase) :
      (s ≫ scalarPoint 0) ≫ affineLineToC = s := by
    simp only [Category.assoc, scalarPoint_overC, Category.comp_id]
  obtain ⟨l, hl, _⟩ := F.universal ProjectiveLine P.structureMap
    ⟨P.structureMap ≫ scalarPoint 0, hbase _ _⟩
    ⟨𝟙 ProjectiveLine, Category.id_comp _⟩
    ⟨P.structureMap ≫ marking.map, hmark _ _⟩
    (SourceMarksProof.equation_zero_parameter_right _ _ _
      (SourceMarksProof.constant_zero_parameter P.structureMap)
      (SourceMarksProof.pullSection_comp_zero P.structureMap marking.map _
        SourceMarksProof.marking_second_coordinate_zero))
  obtain ⟨r, hr, _⟩ := F.universal ProjectiveLine P.structureMap
    ⟨P.structureMap ≫ scalarPoint 0, hbase _ _⟩
    ⟨P.structureMap ≫ marking.map, hmark _ _⟩
    ⟨𝟙 ProjectiveLine, Category.id_comp _⟩
    (SourceMarksProof.equation_zero_parameter_left _ _ _
      (SourceMarksProof.constant_zero_parameter P.structureMap)
      (SourceMarksProof.pullSection_comp_zero P.structureMap marking.map _
        SourceMarksProof.marking_second_coordinate_zero))
  obtain ⟨a, ha, _⟩ := F.universal AffineLine affineLineToC
    ⟨𝟙 AffineLine, Category.id_comp _⟩
    ⟨affineLineToC ≫ infinity.map, hinfty _ _⟩
    ⟨affineLineToC ≫ marking.map, hmark _ _⟩
    (SourceMarksProof.equation_first_mark affineLineToC (𝟙 AffineLine))
  obtain ⟨b, hb, _⟩ := F.universal AffineLine affineLineToC
    ⟨𝟙 AffineLine, Category.id_comp _⟩
    ⟨affineLineToC ≫ marking.map, hmark _ _⟩
    ⟨affineLineToC ≫ infinity.map, hinfty _ _⟩
    (SourceMarksProof.equation_second_mark affineLineToC (𝟙 AffineLine))
  obtain ⟨c, _, hc⟩ := F.universal ComplexBase (𝟙 ComplexBase)
    ⟨scalarPoint 0, scalarPoint_overC 0⟩
    ⟨marking.map, marking.overC⟩ ⟨marking.map, marking.overC⟩
    (SourceMarksProof.equation_zero_parameter_right _ _ _
      SourceMarksProof.scalarPoint_zero_parameter
      SourceMarksProof.marking_second_coordinate_zero)
  have hlc : marking.map ≫ l = c := by
    apply hc
    exact ⟨by rw [Category.assoc, hl.1, ← Category.assoc,
      marking.overC, Category.id_comp],
      by rw [Category.assoc, hl.2.1, Category.comp_id],
      by rw [Category.assoc, hl.2.2, ← Category.assoc,
        marking.overC, Category.id_comp]⟩
  have hrc : marking.map ≫ r = c := by
    apply hc
    exact ⟨by rw [Category.assoc, hr.1, ← Category.assoc,
      marking.overC, Category.id_comp],
      by rw [Category.assoc, hr.2.1, ← Category.assoc,
        marking.overC, Category.id_comp],
      by rw [Category.assoc, hr.2.2, Category.comp_id]⟩
  exact ⟨{
    branchLeft := l
    branchRight := r
    left_base := hl.1
    right_base := hr.1
    left_left := hl.2.1
    left_right := hl.2.2
    right_left := hr.2.1
    right_right := hr.2.2
    node_agreement := hlc.trans hrc.symm
    first := a
    second := b
    first_base := ha.1
    second_base := hb.1
    first_left := ha.2.1
    first_right := ha.2.2
    second_left := hb.2.1
    second_right := hb.2.2 }⟩


theorem sourceMarks_disjoint (F : StandardSource) (m : SourceMarks F) :
    Disjoint (Set.range (fun x => m.first x)) (Set.range (fun x => m.second x)) := by
  letI : SmoothOfRelativeDimension 1 P.structureMap :=
    LeBrunSalamon.Skeleton.ProjectiveLineProof.structureMap_smooth P
  letI : Smooth P.structureMap := SmoothOfRelativeDimension.smooth 1 P.structureMap
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨a, ha⟩ := hz₁
  obtain ⟨b, hb⟩ := hz₂
  have hab : m.first a = m.second b := ha.trans hb.symm
  have hl := congrArg (fun f : AffineLine ⟶ ProjectiveLine => f a) m.first_left
  have hr := congrArg (fun f : AffineLine ⟶ ProjectiveLine => f b) m.second_left
  simp only [Scheme.Hom.comp_apply] at hl hr
  have hpoint : infinity.map (IsLocalRing.closedPoint ℂ) =
      marking.map (IsLocalRing.closedPoint ℂ) := by
    calc
      infinity.map (IsLocalRing.closedPoint ℂ) =
          infinity.map (affineLineToC a) :=
        congrArg (fun p : ComplexBase => infinity.map p) (Subsingleton.elim _ _)
      _ = F.left (m.first a) := hl.symm
      _ = F.left (m.second b) := congrArg (fun p : F.source => F.left p) hab
      _ = marking.map (affineLineToC b) := hr
      _ = marking.map (IsLocalRing.closedPoint ℂ) :=
        congrArg (fun p : ComplexBase => marking.map p) (Subsingleton.elim _ _)
  exact zero_ne_infinity
    (AlgebraicGeometry.ext_of_apply_closedPoint_eq P.structureMap
      infinity.overC marking.overC hpoint).symm


/-- Base-change of the source along a parameter map. -/
abbrev SourceOver (F : StandardSource) {T : Scheme} (t : T ⟶ AffineLine) :=
  pullback F.parameter t

def sourceBaseChangeMap (F : StandardSource) {T H : Scheme}
    (t : T ⟶ AffineLine) (h : H ⟶ AffineLine)
    (a : T ⟶ H) (ha : a ≫ h = t) : SourceOver F t ⟶ SourceOver F h :=
  pullback.lift (pullback.fst F.parameter t) (pullback.snd F.parameter t ≫ a)
    (by simpa [Category.assoc, ha] using (pullback.condition (f := F.parameter) (g := t)))

/-- sm:relative-hom. The functor is represented on ALL schemes over A1.
No choice of a slice/subfamily of maps is admitted as a substitute. -/
structure RelativeHom {d : ℕ} (F : StandardSource) (X : SmoothProperComplexVariety d) where
  parameter : Scheme
  toBase : parameter ⟶ AffineLine
  evaluation : SourceOver F toBase ⟶ X.scheme
  overC : evaluation ≫ X.structureMap =
    pullback.snd F.parameter toBase ≫ toBase ≫ affineLineToC
  universal : ∀ (T : Scheme) (t : T ⟶ AffineLine),
    Function.Bijective (fun h : {h : T ⟶ parameter // h ≫ toBase = t} =>
      (⟨sourceBaseChangeMap F t toBase h.val h.property ≫ evaluation, by
        simp only [Category.assoc, overC, sourceBaseChangeMap, pullback.lift_snd_assoc]
        rw [← Category.assoc h.val toBase affineLineToC, h.property]⟩ :
        {f : SourceOver F t ⟶ X.scheme // f ≫ X.structureMap =
          pullback.snd F.parameter t ≫ t ≫ affineLineToC}))

namespace HomDeformationInput

/-- Base change in an arbitrary source family. The actual projection to
the source and the actual projection to the parameter are retained. -/
def familyChange {S Y T H : Scheme} (pi : Y ⟶ S)
    (t : T ⟶ S) (h : H ⟶ S) (a : T ⟶ H) (ha : a ≫ h = t) :
    pullback pi t ⟶ pullback pi h :=
  pullback.lift (pullback.fst pi t) (pullback.snd pi t ≫ a)
    (by simpa [Category.assoc, ha] using (pullback.condition (f := pi) (g := t)))

/-- The full relative morphism functor for an arbitrary source family.
Every test scheme occurs, including nilpotent thickenings. -/
structure Presentation {S Y : Scheme} (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    {d : ℕ} (X : SmoothProperComplexVariety d) where
  parameter : Scheme
  toBase : parameter ⟶ S
  evaluation : pullback pi toBase ⟶ X.scheme
  overC : evaluation ≫ X.structureMap = pullback.snd pi toBase ≫ toBase ≫ sS
  universal : ∀ (T : Scheme) (t : T ⟶ S),
    Function.Bijective (fun h : {h : T ⟶ parameter // h ≫ toBase = t} =>
      (⟨familyChange pi t toBase h.val h.property ≫ evaluation, by
        simp only [Category.assoc, overC, familyChange, pullback.lift_snd_assoc]
        rw [← Category.assoc h.val toBase sS, h.property]⟩ :
        {f : pullback pi t ⟶ X.scheme //
          f ≫ X.structureMap = pullback.snd pi t ≫ t ≫ sS}))

/-- No geometric information is added when viewing the specified conic
Hom presentation as a presentation for an arbitrary source family. -/
def ofRelativeHom {d : ℕ} {F : StandardSource} {X : SmoothProperComplexVariety d}
    (H : RelativeHom F X) : Presentation F.parameter affineLineToC X where
  parameter := H.parameter
  toBase := H.toBase
  evaluation := H.evaluation
  overC := H.overC
  universal := H.universal

abbrev projectiveProduct {S : Scheme} (sS : S ⟶ ComplexBase)
    (P Q : ProjectiveLineOverC) : Scheme :=
  pullback (pullback.fst sS P.structureMap ≫ sS) Q.structureMap

def projectiveProductToBase {S : Scheme} (sS : S ⟶ ComplexBase)
    (P Q : ProjectiveLineOverC) : projectiveProduct sS P Q ⟶ S :=
  pullback.fst _ _ ≫ pullback.fst sS P.structureMap

namespace FunctorComparison

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.RelativeMorphismsFunctor

/-- Base changing the target converts the actual maps over C into
maps over S, with both projections retained. -/
def targetChangeEquiv {S Y : Scheme} (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    {d : ℕ} (X : SmoothProperComplexVariety d) (T : Over S) :
    {f : pullback pi T.hom ⟶ X.scheme //
      f ≫ X.structureMap = pullback.snd pi T.hom ≫ T.hom ≫ sS} ≃
    (sourceOver pi T ⟶ Over.mk (pullback.snd X.structureMap sS)) where
  toFun f := Over.homMk
    (pullback.lift f.val (pullback.snd pi T.hom ≫ T.hom)
      (by simpa [Category.assoc] using f.property))
    (by simp [sourceOver])
  invFun g := ⟨g.left ≫ pullback.fst X.structureMap sS, by
    rw [Category.assoc, pullback.condition]
    change g.left ≫ (pullback.snd X.structureMap sS ≫ sS) = _
    rw [← Category.assoc]
    have hg : g.left ≫ pullback.snd X.structureMap sS =
        pullback.snd pi T.hom ≫ T.hom := g.w
    rw [hg, Category.assoc]⟩
  left_inv f := by
    apply Subtype.ext
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    simp
  right_inv g := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      simp
    · simpa using g.w.symm

def presentationRepresentation {S Y : Scheme} (pi : Y ⟶ S)
    (sS : S ⟶ ComplexBase) {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomDeformationInput.Presentation pi sS X) :
    (morphismFunctor pi (pullback.snd X.structureMap sS)).RepresentableBy
      (Over.mk H.toBase) where
  homEquiv {T} :=
    (SectionRepresentability.overHomEquiv (Over.mk H.toBase) T.left T.hom).symm.trans
      ((Equiv.ofBijective
        (fun a : {a : T.left ⟶ H.parameter // a ≫ H.toBase = T.hom} =>
          (⟨HomDeformationInput.familyChange pi T.hom H.toBase a.val a.property ≫
            H.evaluation, by
              simp only [Category.assoc, H.overC, HomDeformationInput.familyChange,
                pullback.lift_snd_assoc]
              rw [← Category.assoc a.val H.toBase sS, a.property]⟩ :
            {f : pullback pi T.hom ⟶ X.scheme //
              f ≫ X.structureMap = pullback.snd pi T.hom ≫ T.hom ≫ sS}))
        (H.universal T.left T.hom)).trans (targetChangeEquiv pi sS X T))
  homEquiv_comp a b := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change pullback.lift _ _ _ ≫ pullback.fst _ _ =
        (sourceMap pi a ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
      simp only [Category.assoc, pullback.lift_fst]
      change (HomDeformationInput.familyChange pi _ H.toBase (a ≫ b).left (a ≫ b).w ≫
        H.evaluation) = sourceMap pi a ≫
          (HomDeformationInput.familyChange pi _ H.toBase b.left b.w ≫ H.evaluation)
      change sourceMap pi (a ≫ b) ≫ H.evaluation =
        sourceMap pi a ≫ (sourceMap pi b ≫ H.evaluation)
      rw [sourceMap_comp, Category.assoc]
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ =
        (sourceMap pi a ≫ pullback.lift _ _ _) ≫ pullback.snd _ _
      simp only [Category.assoc, pullback.lift_snd]
      change pullback.snd pi _ ≫ _ =
        sourceMap pi a ≫ (pullback.snd pi _ ≫ _)
      rw [← Category.assoc, sourceMap_snd, Category.assoc, a.w]

/-- The proposed generic input is kept as an explicit parameter. No
project Hom theorem or original admission is used by this comparison. -/
theorem locallyOfFinitePresentation_of_generic_input
    (standardInput : ∀ {S Y Z : Scheme.{0}} (pi : Y ⟶ S) (q : Z ⟶ S),
      IsProper pi → Flat pi → LocallyOfFinitePresentation pi →
      QuasiCompact pi → QuasiSeparated pi →
      IsSeparated q → LocallyOfFinitePresentation q → QuasiCompact q → QuasiSeparated q →
      ∀ H : Over S, (morphismFunctor pi q).RepresentableBy H →
        LocallyOfFinitePresentation H.hom)
    {S Y : Scheme} (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    [IsProper pi] [Flat pi] [LocallyOfFinitePresentation pi]
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomDeformationInput.Presentation pi sS X) :
    LocallyOfFinitePresentation H.toBase := by
  exact standardInput pi (pullback.snd X.structureMap sS)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (Over.mk H.toBase) (presentationRepresentation pi sS X H)

end FunctorComparison

namespace StandardInputs

/-- Grothendieck, Bourbaki expose 221 (1961), section 4(c), pp.267--268:
the relative Hom scheme is an open subscheme of the Hilbert scheme.
The specified closed embedding into a product of two relative projective
lines supplies relative projectivity via Segre; flatness is explicit.
The full all-test-scheme universal property is also stated in
Araujo--Kollar, Rational Curves on Varieties, section 4 before Theorem 15.
No nodal or contact conclusion is included. -/
theorem presentation_exists_of_projectiveProduct {S Y : Scheme}
    [IsLocallyNoetherian S] (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    [Flat pi] [LocallyOfFinitePresentation pi]
    (P Q : ProjectiveLineOverC)
    (j : Y ⟶ projectiveProduct sS P Q) [IsClosedImmersion j]
    (hj : j ≫ projectiveProductToBase sS P Q = pi)
    {d : ℕ} (X : SmoothProperComplexVariety d) (hX : HasProjectiveEmbedding X) :
    Nonempty (Presentation pi sS X) := by
  sorry

/-- Published relative-morphism representability consequence: Stacks 0D1C,
Proposition 99.12.3, and 0DPN, Lemma 108.10.2. The supplied scheme already
represents the full functor; this statement asserts only its local finite
presentation and does not assert scheme representability from properness. -/
theorem locallyOfFinitePresentation {S Y : Scheme}
    (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    [IsProper pi] [Flat pi] [LocallyOfFinitePresentation pi]
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : Presentation pi sS X) : LocallyOfFinitePresentation H.toBase := by
  exact FunctorComparison.locallyOfFinitePresentation_of_generic_input
    @LeBrunSalamon.PublishedInputs.RelativeHom.locallyOfFinitePresentation pi sS X H

/-- Standard deformation-theory corollary of SGA 1, Expose III, Corollaries
5.4 and 5.6, with the pointwise infinitesimal criterion Stacks 02HX
(Lemma 37.12.1); compare Stacks 08U8 and 02H6. This is a corollary of those
published results, not a verbatim statement of one source. The obstruction
group is the actual fibre-map tangent pullback, with the original Yoneda
H1 predicate. No nodal, contact, or endpoint comparison is admitted here. -/
theorem smooth_of_firstCohomology_vanishes {S Y : Scheme}
    [IsLocallyNoetherian S] (pi : Y ⟶ S) (sS : S ⟶ ComplexBase)
    [IsProper pi] [Flat pi] [LocallyOfFinitePresentation pi]
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : Presentation pi sS X) [LocallyOfFinitePresentation H.toBase]
    (p : ComplexBase ⟶ H.parameter) (hp : p ≫ H.toBase ≫ sS = 𝟙 ComplexBase)
    (b : ComplexBase ⟶ S) (hb : p ≫ H.toBase = b)
    (hH1 : HasVanishingFirstCohomology
      (pullbackModule (familyChange pi b H.toBase p hb ≫ H.evaluation)
        (tangentSheaf X.structureMap))) :
    ∃ U : H.parameter.Opens, Set.range p ⊆ (U : Set H.parameter) ∧
      Smooth (U.ι ≫ H.toBase) := by
  sorry

end StandardInputs
end HomDeformationInput

/- Exact relativeHom_exists declaration is proved below after the actual
source closed immersion and finite-presentation theorems. -/

/- `relativeHom_lfp` follows the constructed source properness and finite
presentation, and applies the generic published relative-morphism result. -/

/-- The scheme over the punctured parameter line is ACTUALLY P1 x Gm.
The theorem uses the open nonvanishing locus of the global parameter.
The displayed inverse in the manuscript is [U0:U1] -> ([U0:U1],[U1:sU0]). -/
def puncturedParameter : AffineLine.Opens := AffineLine.basicOpen parameterFunction

/- The exact standardSource_puncturedTrivialization declaration is
proved below after the actual chosen-coordinate ratio charts. -/

def markedEvaluation {d : ℕ} {F : StandardSource} {X : SmoothProperComplexVariety d}
    (H : RelativeHom F X) (m : AffineLine ⟶ F.source)
    (hm : m ≫ F.parameter = 𝟙 AffineLine) : H.parameter ⟶ X.scheme :=
  pullback.lift (H.toBase ≫ m) (𝟙 H.parameter)
    (by simp [Category.assoc, hm]) ≫ H.evaluation

/-- A genuine affine chart around the nodal map in the full relative Hom scheme.
The endpoint chart maps are constrained by the actual evaluation morphisms.
Smoothness and surjectivity of differentials are NOT assumptions here. -/
structure Germ {n : ℕ} {X : ContactFanoManifold n} (D : SuitablePair X) where
  source : StandardSource
  marks : SourceMarks source
  hom : RelativeHom source X.variety
  chart : Charts.PointedAffine
  inclusion : chart.scheme ⟶ hom.parameter
  openImmersion : IsOpenImmersion inclusion
  chart_overC : inclusion ≫ hom.toBase ≫ affineLineToC = chart.toC
  centre_base : chart.point.val ≫ inclusion ≫ hom.toBase = scalarPoint 0
  firstTarget : Charts.PointedAffine
  firstOpen : firstTarget.scheme ⟶ X.variety.scheme
  firstOpen_immersion : IsOpenImmersion firstOpen
  firstOpen_over : firstOpen ≫ X.variety.structureMap = firstTarget.toC
  firstCentre : firstTarget.point.val ≫ firstOpen = infinity.map ≫ D.first.curve.map
  secondTarget : Charts.PointedAffine
  secondOpen : secondTarget.scheme ⟶ X.variety.scheme
  secondOpen_immersion : IsOpenImmersion secondOpen
  secondOpen_over : secondOpen ≫ X.variety.structureMap = secondTarget.toC
  secondCentre : secondTarget.point.val ≫ secondOpen = infinity.map ≫ D.second.curve.map
  firstEval : Charts.Hom chart firstTarget
  secondEval : Charts.Hom chart secondTarget
  firstEval_spec : firstEval.map ≫ firstOpen = inclusion ≫ markedEvaluation hom marks.first marks.first_base
  secondEval_spec : secondEval.map ≫ secondOpen = inclusion ≫ markedEvaluation hom marks.second marks.second_base
  leftCentral :
    pullback.lift marks.branchLeft (P.structureMap ≫ chart.point.val ≫ inclusion)
      (by rw [marks.left_base]; simp [Category.assoc, centre_base]) ≫ hom.evaluation = D.first.curve.map
  rightCentral :
    pullback.lift marks.branchRight (P.structureMap ≫ chart.point.val ≫ inclusion)
      (by rw [marks.right_base]; simp [Category.assoc, centre_base]) ≫ hom.evaluation = D.second.curve.map

namespace Germ
variable {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X} (G : Germ D)

/-- Derivative of the ACTUAL smoothing coordinate sigma. -/
def baseDifferential : G.chart.Tangent →ₗ[ℂ] ℂ :=
  Infinitesimal.evaluateFunction G.chart.Ring G.chart.evaluation
    ((G.inclusion ≫ G.hom.toBase).appTop parameterFunction)

def endpointDifferential : G.chart.Tangent →ₗ[ℂ]
    (G.firstTarget.Tangent × G.secondTarget.Tangent) :=
  G.firstEval.differential.prod G.secondEval.differential

def verticalEvaluation : LinearMap.ker G.baseDifferential →ₗ[ℂ]
    (G.firstTarget.Tangent × G.secondTarget.Tangent) :=
  G.endpointDifferential.comp (LinearMap.ker G.baseDifferential).subtype

/-- sm:fixed-ends, expressed using the actual differentiated maps. -/
def NoFixedEnds : Prop :=
  ¬ ∃ z : G.chart.Tangent, G.baseDifferential z = 1 ∧ G.endpointDifferential z = 0

def VerticalDefectOne : Prop :=
  Module.finrank ℂ ((G.firstTarget.Tangent × G.secondTarget.Tangent) ⧸
    LinearMap.range G.verticalEvaluation) = 1

end Germ

/- `germ_exists` is constructed after the central-fibre pushout API, using
the actual glued map and affine neighborhoods of its two endpoint values. -/

/- The smoothing-map smoothness theorem and its normalized differential
proof follow the actual central-bundle H1 vanishing in Normalization. -/

/- `germ_verticalDefectOne` is proved after the normalization comparison,
so that the original result uses that actual commuting diagram. -/

/- `germ_noFixedEnds` is proved from the actual global auxiliary
deformations, relative horizontality, and the common node tensor in
LSNodalFixedEnds, after the normalized tangent-fiber comparison. -/

/-! The exact linear-algebra deduction, independent of any geometry. -/
section EvaluationAlgebra
variable (V W : Type*) [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def verticalRange (b : V →ₗ[ℂ] ℂ) (e : V →ₗ[ℂ] W) : Submodule ℂ W :=
  LinearMap.range (e.comp (LinearMap.ker b).subtype)

theorem noFixedEnds_iff_kernel (b : V →ₗ[ℂ] ℂ) (e : V →ₗ[ℂ] W) :
    (¬ ∃ z, b z = 1 ∧ e z = 0) ↔ LinearMap.ker e ≤ LinearMap.ker b := by
  constructor
  · intro h z hz
    change e z = 0 at hz
    change b z = 0
    by_contra hb
    apply h
    refine ⟨(b z)⁻¹ • z, ?_, ?_⟩
    · simp [map_smul, smul_eq_mul, hb]
    · simp [map_smul, hz]
  · intro h ⟨z, hb, he⟩
    have hz : z ∈ LinearMap.ker e := he
    have hzero : b z = 0 := h hz
    exact one_ne_zero (hb.symm.trans hzero)

/-- If b is onto, the forbidden fixed-end smoothing says that a base
lift supplies a NONZERO element of the vertical evaluation cokernel. -/
theorem baseLift_not_vertical (b : V →ₗ[ℂ] ℂ) (e : V →ₗ[ℂ] W)
    (h : ¬ ∃ z, b z = 1 ∧ e z = 0) (z : V) (hz : b z = 1) :
    e z ∉ verticalRange V W b e := by
  rintro ⟨v, hv⟩
  have hv0 : b v.val = 0 := v.property
  have hev : e v.val = e z := hv
  apply h
  refine ⟨z - v.val, ?_, ?_⟩
  · simp [map_sub, hz, hv0]
  · simp [map_sub, hev]

/-- Codimension ONE is needed: this lemma is false with defect two.
No finite-dimensionality of V is required. -/
theorem endpoint_surjective_of_defect_one [FiniteDimensional ℂ W]
    (b : V →ₗ[ℂ] ℂ) (e : V →ₗ[ℂ] W)
    (hb : Function.Surjective b)
    (hdefect : Module.finrank ℂ (W ⧸ verticalRange V W b e) = 1)
    (hfixed : ¬ ∃ z, b z = 1 ∧ e z = 0) : Function.Surjective e := by
  obtain ⟨z, hz⟩ := hb 1
  have hne : (Submodule.Quotient.mk (e z) : W ⧸ verticalRange V W b e) ≠ 0 := by
    simpa only [ne_eq, Submodule.Quotient.mk_eq_zero] using
      baseLift_not_vertical V W b e hfixed z hz
  intro w
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdefect hne
    (Submodule.Quotient.mk w)
  have hmem : w - e (c • z) ∈ verticalRange V W b e := by
    apply (Submodule.Quotient.eq _).mp
    simpa only [map_smul, Submodule.Quotient.mk_smul] using hc.symm
  obtain ⟨v, hv⟩ := hmem
  refine ⟨v.val + c • z, ?_⟩
  change e v.val = w - e (c • z) at hv
  rw [map_add, hv]
  abel

/-- In a trivialized smooth-source family evaluation ignores the base
parameter. A spurious extra direction cannot establish very-freeness. -/
theorem productEvaluation_surjective_iff (e : V →ₗ[ℂ] W) :
    Function.Surjective (fun z : V × ℂ => e z.1) ↔ Function.Surjective e := by
  constructor
  · intro h w
    obtain ⟨z, hz⟩ := h w
    exact ⟨z.1, hz⟩
  · intro h w
    obtain ⟨v, hv⟩ := h w
    exact ⟨(v, 0), hv⟩

end EvaluationAlgebra

/-- The shared-constant contradiction in the local proof of sm:fixed-ends.
A is the coefficient derivative of alpha; A(a,b)-A(b,a)=d alpha(a,b). -/
theorem sharedConstant_horizontality_contradiction
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (theta : V →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] (V →ₗ[ℂ] ℂ)) (a b c : V)
    (hab : A a b - A b a ≠ 0)
    (h1 : A b a + theta c = 0) (h2 : A a b + theta c = 0) : False := by
  apply hab
  linear_combination h2 - h1

/-- Coordinate changes add the SAME Hessian correction on both branches. -/
theorem sharedConstant_coordinateChange
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (J : V →ₗ[ℂ] W) (H : V →ₗ[ℂ] (V →ₗ[ℂ] W))
    (hH : ∀ u v, H u v = H v u) (a b c : V) :
    J c + H a b = J c + H b a := by rw [hH a b]

/- `germ_extracts_veryFreeConic` is proved in LSNodalConic, after the
actual first-order family variation and both endpoint comparisons.
Its original header and diagnostic are preserved there. -/

/-- Five geometric slots replace PrimitiveSmoothing. Endpoint surjectivity
is a DERIVATION from the one-dimensional defect, not a stored conclusion. -/
structure Inputs : Prop where
  suitable : ∀ (n : ℕ) (X : ContactFanoManifold n), HasPrimitiveContactPicard X.contact →
    Nonempty (SuitablePair X)
  germ : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : SuitablePair X), Nonempty (Germ D)
  linearFacts : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : SuitablePair X) (G : Germ D),
    FiniteDimensional ℂ (G.firstTarget.Tangent × G.secondTarget.Tangent) ∧
      Function.Surjective G.baseDifferential ∧ G.VerticalDefectOne
  fixedEnds : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : SuitablePair X) (G : Germ D),
    G.NoFixedEnds
  extract : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : SuitablePair X) (G : Germ D),
    Function.Surjective G.baseDifferential → Function.Surjective G.endpointDifferential →
      Nonempty (VeryFreeContactConic P marking X)

/-- No call to primitiveContactFano_veryFreeConic_target occurs here.
The generic linear-algebra lemma is separately admitted until proved. -/
theorem Inputs.assemble (H : Inputs) : PrimitiveSmoothing P marking := by
  intro n X hp
  obtain ⟨D⟩ := H.suitable n X hp
  obtain ⟨G⟩ := H.germ n X D
  obtain ⟨hfinite, hb, hdefect⟩ := H.linearFacts n X D G
  letI := hfinite
  have he : Function.Surjective G.endpointDifferential :=
    endpoint_surjective_of_defect_one G.chart.Tangent
      (G.firstTarget.Tangent × G.secondTarget.Tangent)
      G.baseDifferential G.endpointDifferential hb hdefect (H.fixedEnds n X D G)
  exact H.extract n X D G hb he

end Smoothing

/-! ## Contact-value descent: finite image, all sheets, ramification, purity -/
namespace Descent

open LeBrunSalamon.Refinement
open Lines

abbrev Square {n : ℕ} (X : ContactFanoManifold n) := SelfProduct X.variety.structureMap
abbrev SquareLine {n : ℕ} (X : ContactFanoManifold n) :=
  externalSquareLine X.variety.structureMap X.contact.sequence.line

def IntegralScheme (S : Scheme) : Prop :=
  IrreducibleSpace S ∧ ∀ U : S.Opens, IsReduced (RingSections S U)

def NormalScheme (S : Scheme) : Prop :=
  ∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)

/-- Birationality for finite maps of integral schemes, specified by a
nonempty dense base open on which the ACTUAL morphism is an isomorphism. -/
def IsoOverDenseOpen {S T : Scheme} (q : S ⟶ T) : Prop :=
  ∃ U : T.Opens, Dense (U : Set T) ∧
    IsIso (pullback.snd q U.ι : pullback q U.ι ⟶ U.toScheme)

/-- The actual inverse over the dense open proves dominance of the original map. -/
theorem IsoOverDenseOpen.denseRange {S T : Scheme} (q : S ⟶ T)
    (h : IsoOverDenseOpen q) : DenseRange (fun x => q x) := by
  obtain ⟨U, hU, hi⟩ := h
  letI := hi
  apply hU.mono
  intro y hy
  let yu : U.toScheme := ⟨y, hy⟩
  obtain ⟨w, hw⟩ := (pullback.snd q U.ι).surjective yu
  refine ⟨pullback.fst q U.ι w, ?_⟩
  have he := congrArg (fun f : pullback q U.ι ⟶ T => f w)
    (pullback.condition (f := q) (g := U.ι))
  simpa only [Scheme.Hom.comp_apply, hw, Scheme.Opens.ι_apply, yu] using he

/-- Finite birational maps in the specified dense-open convention are surjective. -/
theorem IsoOverDenseOpen.surjective {S T : Scheme} (q : S ⟶ T)
    [IsFinite q] (h : IsoOverDenseOpen q) : Function.Surjective (fun x => q x) := by
  intro y
  change y ∈ Set.range q
  have hy := (IsoOverDenseOpen.denseRange q h) y
  simpa only [q.isClosedMap.isClosed_range.closure_eq] using hy

namespace FiniteCoverProof

/-- A connected scheme maps into a single component of a disjoint union.
The factor is an actual scheme morphism obtained from the open immersion. -/
theorem factors_through_sigma_component {T : Scheme} [ConnectedSpace T]
    {m : ℕ} (F : Fin m → Scheme) (j : T ⟶ ∐ F) :
    ∃ (i : Fin m) (a : T ⟶ F i), a ≫ Sigma.ι F i = j := by
  classical
  let g : T → (Σ i, F i) := fun x => (AlgebraicGeometry.sigmaMk F).symm (j x)
  have hg : Continuous g := (AlgebraicGeometry.sigmaMk F).symm.continuous.comp j.continuous
  let x₀ : T := Classical.choice inferInstance
  let w := g x₀
  have hr : Set.range g ⊆ Set.range (Sigma.mk w.1) :=
    (isPreconnected_range hg).subset_isClopen isClopen_range_sigmaMk
      ⟨w, ⟨x₀, rfl⟩, w.2, rfl⟩
  have hj : Set.range j ⊆ Set.range (Sigma.ι F w.1) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hr ⟨x, rfl⟩
    refine ⟨z, ?_⟩
    have he := congrArg (AlgebraicGeometry.sigmaMk F) hz
    simpa [g] using he
  exact ⟨w.1, IsOpenImmersion.lift (Sigma.ι F w.1) j hj,
    IsOpenImmersion.lift_fac (Sigma.ι F w.1) j hj⟩

/-- An integral closed subscheme dominating the base inside a split cover
is exactly one sheet. Reducedness of the base removes any closed thickening. -/
theorem closed_split_projection_isIso {T U : Scheme} [ConnectedSpace T]
    [AlgebraicGeometry.IsReduced U] {m : ℕ}
    (j : T ⟶ ∐ (fun _ : Fin m => U)) [IsClosedImmersion j]
    (f : T ⟶ U) [IsDominant f]
    (hf : j ≫ Sigma.desc (fun _ : Fin m => 𝟙 U) = f) : IsIso f := by
  obtain ⟨i, a, ha⟩ := factors_through_sigma_component (fun _ : Fin m => U) j
  have haf : a = f := by
    calc
      a = a ≫ Sigma.ι (fun _ : Fin m => U) i ≫
          Sigma.desc (fun _ : Fin m => 𝟙 U) := by simp
      _ = f := by rw [← Category.assoc, ha, hf]
  letI : IsClosedImmersion (a ≫ Sigma.ι (fun _ : Fin m => U) i) := by
    rw [ha]
    infer_instance
  letI : IsClosedImmersion a :=
    IsClosedImmersion.of_comp a (Sigma.ι (fun _ : Fin m => U) i)
  letI : IsClosedImmersion f := haf ▸ inferInstance
  letI : Surjective f := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  exact AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective f

/-- Dominance carries the actual generic point to the generic point. -/
theorem map_genericPoint {Y Z : Scheme} [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) [IsDominant f] : f (genericPoint Y) = genericPoint Z := by
  have h : IsGenericPoint (f (genericPoint Y)) (Set.univ : Set Z) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec Y).image f.continuous
  exact h.eq (genericPoint_spec Z)

/-- A finite dominant map between integral schemes has just the generic
source point over the generic target point. Discreteness of the actual
finite fibre rules out any further specialization in that fibre. -/
theorem eq_genericPoint_of_map_eq {Y Z : Scheme} [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) [IsFinite f] [IsDominant f] (y : Y)
    (hy : f y = genericPoint Z) : y = genericPoint Y := by
  let F : Set Y := f ⁻¹' {genericPoint Z}
  letI : DiscreteTopology F := isDiscrete_iff_discreteTopology.mp
    (f.isDiscrete_preimage_singleton (genericPoint Z))
  let a : F := ⟨genericPoint Y, by simpa only [F, Set.mem_preimage,
    Set.mem_singleton_iff] using map_genericPoint f⟩
  let b : F := ⟨y, by simpa only [F, Set.mem_preimage, Set.mem_singleton_iff] using hy⟩
  have hs : a ⤳ b := (subtype_specializes_iff a b).mpr (genericPoint_specializes y)
  exact (congrArg Subtype.val hs.eq).symm

/-- A dense source open under a finite dominant integral map contains the
whole inverse image of a dense base open. The base open is explicitly the
complement of the closed image of the source complement. -/
theorem shrink_dense_open {Y Z : Scheme} [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) [IsFinite f] [IsDominant f]
    (V : Y.Opens) (hV : Dense (V : Set Y)) :
    ∃ U : Z.Opens, Dense (U : Set Z) ∧ f ⁻¹ᵁ U ≤ V := by
  let U : Z.Opens := ⟨(f '' (V : Set Y)ᶜ)ᶜ,
    (f.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hηV : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV.nonempty)
  have hηU : genericPoint Z ∈ U := by
    rintro ⟨y, hy, he⟩
    exact hy ((eq_genericPoint_of_map_eq f y he).symm ▸ hηV)
  refine ⟨U, U.isOpen.dense ⟨genericPoint Z, hηU⟩, ?_⟩
  intro y hy
  by_contra h
  exact hy ⟨y, h, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Étaleness of the actual base change persists upon shrinking the base. -/
theorem etale_on_smaller_open {Y Z : Scheme} (f : Y ⟶ Z)
    (U W : Z.Opens) (hWU : W ≤ U)
    (hE : Etale (pullback.snd f U.ι)) : Etale (pullback.snd f W.ι) := by
  let k : W.toScheme ⟶ U.toScheme := Z.homOfLE hWU
  have hk : k ≫ U.ι = W.ι := Scheme.homOfLE_ι Z hWU
  let t : pullback f W.ι ⟶ pullback f U.ι :=
    pullback.lift (pullback.fst f W.ι) (pullback.snd f W.ι ≫ k) (by
      rw [Category.assoc, hk]
      exact pullback.condition)
  have hpb : IsPullback t (pullback.snd f W.ι) (pullback.snd f U.ι) k := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback f U.ι)
    · simpa only [t, pullback.lift_fst, hk] using IsPullback.of_hasPullback f W.ι
    · simp only [t, pullback.lift_snd]
  exact MorphismProperty.of_isPullback (P := @Etale) hpb hE

set_option backward.isDefEq.respectTransparency false in
theorem isIso_on_smaller_open {Y Z : Scheme} (f : Y ⟶ Z)
    (U W : Z.Opens) (hWU : W ≤ U)
    (hU : IsIso (pullback.snd f U.ι)) : IsIso (pullback.snd f W.ι) := by
  let k : W.toScheme ⟶ U.toScheme := Z.homOfLE hWU
  have hk : k ≫ U.ι = W.ι := Scheme.homOfLE_ι Z hWU
  let t : pullback f W.ι ⟶ pullback f U.ι :=
    pullback.lift (pullback.fst f W.ι) (pullback.snd f W.ι ≫ k) (by
      rw [Category.assoc, hk]
      exact pullback.condition)
  have hpb : IsPullback t (pullback.snd f W.ι) (pullback.snd f U.ι) k := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback f U.ι)
    · simpa only [t, pullback.lift_fst, hk] using IsPullback.of_hasPullback f W.ι
    · simp only [t, pullback.lift_snd]
  exact hpb.isIso_snd_of_isIso hU

set_option backward.isDefEq.respectTransparency false in
/-- Isomorphisms for both maps of a composite are transported through the
specified actual base changes, with the entire intermediate fibre in V. -/
theorem composite_restriction_isIso {S T Z : Scheme}
    (n : S ⟶ T) (e : T ⟶ Z) (q : S ⟶ Z) (he : n ≫ e = q)
    (V : T.Opens) (hV : IsIso (pullback.snd n V.ι))
    (U : Z.Opens) (hUV : e ⁻¹ᵁ U ≤ V)
    (hU : IsIso (pullback.snd e U.ι)) : IsIso (pullback.snd q U.ι) := by
  let r : pullback q U.ι ⟶ pullback e U.ι :=
    pullback.lift (pullback.fst q U.ι ≫ n) (pullback.snd q U.ι) (by
      simpa only [Category.assoc, he] using pullback.condition (f := q) (g := U.ι))
  have hrange : Set.range (pullback.fst e U.ι) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    apply hUV
    change e (pullback.fst e U.ι x) ∈ U
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact (pullback.snd e U.ι x).property
  let g : pullback e U.ι ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι (pullback.fst e U.ι) hrange
  have hg : g ≫ V.ι = pullback.fst e U.ι :=
    IsOpenImmersion.lift_fac V.ι (pullback.fst e U.ι) hrange
  have hpb : IsPullback (pullback.fst q U.ι) r n (pullback.fst e U.ι) := by
    apply IsPullback.of_bot (t := IsPullback.of_hasPullback e U.ι)
    · simpa only [r, pullback.lift_snd, he] using IsPullback.of_hasPullback q U.ι
    · simp only [r, pullback.lift_fst]
  let t : pullback q U.ι ⟶ pullback n V.ι :=
    pullback.lift (pullback.fst q U.ι) (r ≫ g) (by
      rw [Category.assoc, hg]
      exact hpb.w)
  have ht : IsPullback t r (pullback.snd n V.ι) g := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback n V.ι)
    · simpa only [t, pullback.lift_fst, hg] using hpb
    · simp only [t, pullback.lift_snd]
  letI : IsIso r := ht.isIso_snd_of_isIso hV
  letI := hU
  have hcomp : r ≫ pullback.snd e U.ι = pullback.snd q U.ι := pullback.lift_snd _ _ _
  rw [← hcomp]
  infer_instance

end FiniteCoverProof

namespace FiniteCoverStandardInputs

/-- Published generic étaleness for finite dominant maps of integral
schemes in characteristic zero. The actual map to Spec(C) supplies
characteristic zero; the finite extension of function fields is separable.
Sources: Stacks Project, Tag 09Z6, final paragraph of the proof, and
Tag 07ND (generic smoothness criterion for the corresponding domain map).
No normalization, contact structure, or selected test family occurs here. -/
theorem finite_dominant_genericEtale {Y Z : Scheme}
    [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z]
    (sZ : Z ⟶ ComplexBase) (f : Y ⟶ Z) [IsFinite f] [IsDominant f] :
    ∃ U : Z.Opens, Dense (U : Set Z) ∧ Etale (pullback.snd f U.ι) := by sorry

end FiniteCoverStandardInputs

/-- Etaleness on an actual neighborhood of a specified source point. -/
def EtaleAt {S T : Scheme} (q : S ⟶ T) (x : S) : Prop :=
  ∃ U : S.Opens, x ∈ U ∧ Etale (U.ι ≫ q)

/-- Codimension is the dimension of the local ring, not the dimension of
its closure. Generic points of divisors have one-dimensional local rings. -/
def EtaleInCodimensionOne {S T : Scheme} (q : S ⟶ T) : Prop :=
  ∀ x : S, ringKrullDim (S.presheaf.stalk x) = 1 → EtaleAt q x

/-- The total space of L represents sections of f*L on every test scheme.
This is the total space of L, not its dual: the tautological section fixes
that convention. The generic section-functor representation supplies these exact maps. -/
structure TotalLine {Z : Scheme} (L : LineBundle Z) where
  space : Scheme
  projection : space ⟶ Z
  tautological : AlgebraicSection (pullbackModule projection L.sheaf)
  universal : ∀ (T : Scheme) (f : T ⟶ Z),
    Function.Bijective (fun h : {h : T ⟶ space // h ≫ projection = f} =>
      pullSection h.val tautological ≫
        (compositionPullback h.val projection f h.property L.sheaf).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem totalLine_exists {Z : Scheme} (L : LineBundle Z) : Nonempty (TotalLine L) := by
  obtain ⟨V, p, τ, hV⟩ :=
    LeBrunSalamon.SectionRepresentability.represented_section_data L.locallyFree
  exact ⟨{ space := V, projection := p, tautological := τ, universal := hV }⟩

namespace TotalLine
variable {Z : Scheme} {L : LineBundle Z} (T : TotalLine L)

def mapOfSection {Y : Scheme} (f : Y ⟶ Z)
    (a : AlgebraicSection (pullbackModule f L.sheaf)) :
    {h : Y ⟶ T.space // h ≫ T.projection = f} :=
  Classical.choose ((T.universal Y f).surjective a)

theorem mapOfSection_value {Y : Scheme} (f : Y ⟶ Z)
    (a : AlgebraicSection (pullbackModule f L.sheaf)) :
    pullSection (T.mapOfSection f a).val T.tautological ≫
      (compositionPullback (T.mapOfSection f a).val T.projection f
        (T.mapOfSection f a).property L.sheaf).hom = a :=
  Classical.choose_spec ((T.universal Y f).surjective a)

/-- The section represented by an actual morphism to the total line. -/
def representedSection {Y : Scheme} (f : Y ⟶ Z) (h : Y ⟶ T.space)
    (hh : h ≫ T.projection = f) : AlgebraicSection (pullbackModule f L.sheaf) :=
  pullSection h T.tautological ≫
    (compositionPullback h T.projection f hh L.sheaf).hom

theorem representedSection_mapOfSection {Y : Scheme} (f : Y ⟶ Z)
    (a : AlgebraicSection (pullbackModule f L.sheaf)) :
    T.representedSection f (T.mapOfSection f a).val (T.mapOfSection f a).property = a :=
  T.mapOfSection_value f a

theorem mapOfSection_representedSection {Y : Scheme} (f : Y ⟶ Z)
    (h : Y ⟶ T.space) (hh : h ≫ T.projection = f) :
    (T.mapOfSection f (T.representedSection f h hh)).val = h := by
  have he : T.mapOfSection f (T.representedSection f h hh) = ⟨h, hh⟩ := by
    apply (T.universal Y f).injective
    exact T.mapOfSection_value f (T.representedSection f h hh)
  exact congrArg Subtype.val he

theorem mapOfSection_injective {Y : Scheme} (f : Y ⟶ Z)
    {a b : AlgebraicSection (pullbackModule f L.sheaf)}
    (h : (T.mapOfSection f a).val = (T.mapOfSection f b).val) : a = b := by
  let ev : {h : Y ⟶ T.space // h ≫ T.projection = f} →
      AlgebraicSection (pullbackModule f L.sheaf) :=
    fun h => T.representedSection f h.val h.property
  calc
    a = ev (T.mapOfSection f a) := (T.mapOfSection_value f a).symm
    _ = ev (T.mapOfSection f b) := congrArg ev (Subtype.ext h)
    _ = b := T.mapOfSection_value f b

set_option backward.isDefEq.respectTransparency false in
theorem pullbackComp_assoc {W V Y Z : Scheme}
    (f : W ⟶ V) (g : V ⟶ Y) (h : Y ⟶ Z) (E : OModule Z) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E =
      (Scheme.Modules.pullbackComp f g).hom.app (pullbackModule h E) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E ≫
          eqToHom (congrArg (fun k : W ⟶ Z => pullbackModule k E)
            (Category.assoc f g h)) := by
  have ha := congrArg (fun a => a.app E)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  have ha' :
      (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app E ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
          (Scheme.Modules.pullbackComp f g).hom.app (pullbackModule h E) ≫
            (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E =
      eqToHom (congrArg (fun k : W ⟶ Z => pullbackModule k E)
        (Category.assoc f g h).symm) := by
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
      eqToHom_app] using ha
  have hb := congrArg (fun a =>
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ a ≫
        eqToHom (congrArg (fun k : W ⟶ Z => pullbackModule k E)
          (Category.assoc f g h))) ha'
  simpa [Category.assoc, ← Functor.map_comp_assoc] using hb.symm

set_option backward.isDefEq.respectTransparency false in
theorem compositionPullback_assoc {W V Y Z : Scheme}
    (f : W ⟶ V) (g : V ⟶ Y) (h : Y ⟶ Z)
    (j : V ⟶ Z) (hj : g ≫ h = j)
    (k : W ⟶ Y) (hk : f ≫ g = k)
    (l : W ⟶ Z) (hl : f ≫ j = l) (hl' : k ≫ h = l) (E : OModule Z) :
    (Scheme.Modules.pullback f).map (compositionPullback g h j hj E).hom ≫
        (compositionPullback f j l hl E).hom =
      (compositionPullback f g k hk (pullbackModule h E)).hom ≫
        (compositionPullback k h l hl' E).hom := by
  subst j
  subst k
  subst l
  simpa only [compositionPullback, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id, pullbackModule, Functor.comp_obj]
    using pullbackComp_assoc f g h E

set_option backward.isDefEq.respectTransparency false in
/-- Naturality includes the canonical comparison for the specified composite. -/
theorem representedSection_naturality {W Y : Scheme}
    (f : Y ⟶ Z) (h : Y ⟶ T.space) (hh : h ≫ T.projection = f)
    (g : W ⟶ Y) (k : W ⟶ Z) (hk : g ≫ f = k) :
    pullSection g (T.representedSection f h hh) ≫
        (compositionPullback g f k hk L.sheaf).hom =
      T.representedSection k (g ≫ h) (by rw [Category.assoc, hh, hk]) := by
  unfold representedSection
  rw [pullSection_naturality, Category.assoc,
    compositionPullback_assoc g h T.projection f hh (g ≫ h) rfl k hk
      (by rw [Category.assoc, hh, hk]) L.sheaf,
    ← Category.assoc, compositionPullback_sections]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a represented section composes its actual total-space map. -/
theorem mapOfSection_naturality {W Y : Scheme}
    (f : Y ⟶ Z) (g : W ⟶ Y) (k : W ⟶ Z) (hk : g ≫ f = k)
    (a : AlgebraicSection (pullbackModule f L.sheaf)) :
    g ≫ (T.mapOfSection f a).val =
      (T.mapOfSection k (pullSection g a ≫
        (compositionPullback g f k hk L.sheaf).hom)).val := by
  let h : {h : W ⟶ T.space // h ≫ T.projection = k} :=
    ⟨g ≫ (T.mapOfSection f a).val,
      by rw [Category.assoc, (T.mapOfSection f a).property, hk]⟩
  have he : h = T.mapOfSection k (pullSection g a ≫
      (compositionPullback g f k hk L.sheaf).hom) := by
    apply (T.universal W k).injective
    change T.representedSection k h.val h.property =
      T.representedSection k _ _
    rw [representedSection_mapOfSection]
    change T.representedSection k (g ≫ (T.mapOfSection f a).val) _ = _
    rw [← T.representedSection_naturality f (T.mapOfSection f a).val
      (T.mapOfSection f a).property g k hk, T.representedSection_mapOfSection]
  exact congrArg Subtype.val he

/-- The actual represented total line is isomorphic over its base to the
generic affine representative; its map, tautological section and all-test
universal property are supplied explicitly to that proved transport. -/
theorem projection_affine : IsAffineHom T.projection := by
  exact LeBrunSalamon.SectionRepresentability.affine_of_data L.locallyFree
    T.projection T.tautological T.universal

/-- Published vector-bundle finite-presentation theorem. The represented functor
identifies this actual total line with `Spec Sym (L dual)`. Its coefficient
module is finite locally free of rank one, hence finitely presented.
Sources: Stacks Project, Tags 01M1 and 01ZR (second proof, item 2).
This statement concerns every line bundle over every scheme. -/
theorem projection_lfp : LocallyOfFinitePresentation T.projection := by sorry

theorem projection_separated : IsSeparated T.projection := by
  letI : IsAffineHom T.projection := T.projection_affine
  infer_instance


theorem graph_closed (a : AlgebraicSection L.sheaf) :
    IsClosedImmersion (T.mapOfSection (𝟙 Z) (pullSection (𝟙 Z) a)).val := by
  letI : IsSeparated T.projection := T.projection_separated
  let g := T.mapOfSection (𝟙 Z) (pullSection (𝟙 Z) a)
  haveI : IsClosedImmersion (g.val ≫ T.projection) := by
    rw [g.property]
    infer_instance
  exact IsClosedImmersion.of_comp g.val T.projection


end TotalLine

namespace FiniteImageProof

/-- A quasi-compact scheme-theoretic image of a reduced scheme is reduced.
The proof uses the injective maps on the actual affine-image coordinate rings. -/
theorem image_reduced {Y Z : Scheme} (f : Y ⟶ Z) [QuasiCompact f]
    [AlgebraicGeometry.IsReduced Y] : AlgebraicGeometry.IsReduced f.image := by
  refine ⟨fun U => ⟨fun a ha => ?_⟩⟩
  apply f.image.IsSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxV, hVU⟩ :=
    (Z.isBasis_affineOpens.of_isInducing
      f.imageι.isEmbedding.isInducing).exists_subset_of_mem_open hx U.isOpen
  obtain ⟨V, hV, rfl⟩ := hW
  refine ⟨f.imageι ⁻¹ᵁ V, hVU, hxV, ?_⟩
  apply f.toImage_app_injective ⟨V, hV⟩
  simp only [map_zero]
  exact ((ha.map (f.image.presheaf.map (homOfLE hVU).op).hom).map
    (f.toImage.app (f.imageι ⁻¹ᵁ V)).hom).eq_zero

end FiniteImageProof

/-- Reduced finite image of the common contact value in Tot(L boxtimes L).
The source map goes to the REDUCED IMAGE. No map to its normalization is a field.
Finite-ness is part of the OUTPUT to be constructed, not inferred by definition
from properness and dominance. -/
structure FiniteValueImage {n : ℕ} {X : ContactFanoManifold n} (D : ProperPair X) where
  total : TotalLine (SquareLine X)
  image : Scheme
  integral : IntegralScheme image
  inclusion : image ⟶ total.space
  closed : IsClosedImmersion inclusion
  projection : image ⟶ Square X
  overSquare : inclusion ≫ total.projection = projection
  finite : IsFinite projection
  surjective : Function.Surjective (fun z => projection z)
  fromSource : D.pair.data.source ⟶ image
  sourceProper : IsProper fromSource
  sourceSurjective : Function.Surjective (fun y => fromSource y)
  sourceOver : fromSource ≫ projection = D.pair.data.projection
  imageEquation : fromSource ≫ inclusion =
    (total.mapOfSection D.pair.data.projection D.value).val

/-- SOURCE des:descent, finite image. Uses proper+affine=>finite and
reduction of the image; it does not need source fibres to be connected. -/
theorem finiteValueImage_exists {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) : Nonempty (FiniteValueImage D) := by
  obtain ⟨T⟩ := totalLine_exists (SquareLine X)
  let a : D.pair.data.source ⟶ T.space :=
    (T.mapOfSection D.pair.data.projection D.value).val
  have ha : a ≫ T.projection = D.pair.data.projection :=
    (T.mapOfSection D.pair.data.projection D.value).property
  letI : IsProper D.pair.data.projection := D.pair.data.proper
  letI : IsDominant D.pair.data.projection := ⟨D.pair.data.dominant⟩
  letI : IrreducibleSpace D.pair.data.source := D.irreducible
  letI : AlgebraicGeometry.IsReduced D.pair.data.source := ⟨D.reduced⟩
  letI : IsAffineHom T.projection := T.projection_affine
  letI : LocallyOfFinitePresentation T.projection := T.projection_lfp
  letI : IsProper (a ≫ T.projection) := by rw [ha]; infer_instance
  letI : IsProper a := IsProper.of_comp a T.projection
  letI : IsProper (a.toImage ≫ a.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  letI : IsProper a.toImage := IsProper.of_comp a.toImage a.imageι
  letI : AlgebraicGeometry.IsReduced a.image := FiniteImageProof.image_reduced a
  letI : IrreducibleSpace a.image :=
    a.toImage.surjective.irreducibleSpace a.toImage.continuous
  let q : a.image ⟶ Square X := a.imageι ≫ T.projection
  have hq : a.toImage ≫ q = D.pair.data.projection := by
    simpa only [q, ← Category.assoc, Scheme.Hom.toImage_imageι] using ha
  letI : UniversallyClosed (a.toImage ≫ q) := by rw [hq]; infer_instance
  letI : UniversallyClosed q := UniversallyClosed.of_comp_surjective a.toImage q
  letI : IsProper q := ⟨⟩
  letI : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  refine ⟨{
    total := T
    image := a.image
    integral := ⟨inferInstance, fun U => inferInstance⟩
    inclusion := a.imageι
    closed := inferInstance
    projection := q
    overSquare := rfl
    finite := inferInstance
    surjective := ?_
    fromSource := a.toImage
    sourceProper := inferInstance
    sourceSurjective := a.toImage.surjective
    sourceOver := hq
    imageEquation := a.toImage_imageι }⟩
  intro z
  obtain ⟨y, hy⟩ := D.pair.data.projection.surjective z
  refine ⟨a.toImage y, ?_⟩
  simpa only [← Scheme.Hom.comp_apply, hq] using hy

/-- Finite, integral normal cover; this records actual schemes and maps.
The source is not yet assumed etale or isomorphic to the base. -/
structure FiniteNormalCover (Z : Scheme) where
  source : Scheme
  map : source ⟶ Z
  finite : IsFinite map
  integral : IntegralScheme source
  normal : NormalScheme source
  dominant : DenseRange (fun x => map x)

attribute [instance] FiniteNormalCover.finite

/-- The normalization is tied to the original finite value-image by a
FINITE BIRATIONAL map. A different unrelated finite cover is not acceptable. -/
structure NormalizedImage {n : ℕ} {X : ContactFanoManifold n}
    {D : ProperPair X} (I : FiniteValueImage D) where
  cover : FiniteNormalCover (Square X)
  normalization : cover.source ⟶ I.image
  finite : IsFinite normalization
  birational : IsoOverDenseOpen normalization
  overSquare : normalization ≫ I.projection = cover.map

theorem normalizedImage_exists {n : ℕ} {X : ContactFanoManifold n}
    {D : ProperPair X} (I : FiniteValueImage D) : Nonempty (NormalizedImage I) := by sorry

/-- Actual comparison of the two restricted finite covers. -/
def normalizedRestriction {n : ℕ} {X : ContactFanoManifold n}
    {D : ProperPair X} {I : FiniteValueImage D} (N : NormalizedImage I)
    (U : (Square X).Opens) : pullback N.cover.map U.ι ⟶ pullback I.projection U.ι :=
  pullback.lift (pullback.fst N.cover.map U.ι ≫ N.normalization)
    (pullback.snd N.cover.map U.ι)
    (by simpa [Category.assoc, N.overSquare] using (pullback.condition (f := N.cover.map) (g := U.ι)))

set_option backward.isDefEq.respectTransparency false in
/-- If the entire image over a base open lies in the normalization's
isomorphism open, the actual comparison of the two base changes is an
isomorphism. Both squares are obtained by pasting the specified pullbacks. -/
theorem normalizedRestriction_isIso_of_preimage_le {n : ℕ}
    {X : ContactFanoManifold n} {D : ProperPair X} {I : FiniteValueImage D}
    (N : NormalizedImage I) (V : I.image.Opens)
    (hV : IsIso (pullback.snd N.normalization V.ι))
    (U : (Square X).Opens) (hUV : I.projection ⁻¹ᵁ U ≤ V) :
    IsIso (normalizedRestriction N U) := by
  have hrange : Set.range (pullback.fst I.projection U.ι) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    apply hUV
    change I.projection (pullback.fst I.projection U.ι x) ∈ U
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact (pullback.snd I.projection U.ι x).property
  let g : pullback I.projection U.ι ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι (pullback.fst I.projection U.ι) hrange
  have hg : g ≫ V.ι = pullback.fst I.projection U.ι :=
    IsOpenImmersion.lift_fac V.ι (pullback.fst I.projection U.ι) hrange
  have hpb : IsPullback (pullback.fst N.cover.map U.ι)
      (normalizedRestriction N U) N.normalization (pullback.fst I.projection U.ι) := by
    apply IsPullback.of_bot (t := IsPullback.of_hasPullback I.projection U.ι)
    · simpa only [normalizedRestriction, pullback.lift_snd, N.overSquare] using
        IsPullback.of_hasPullback N.cover.map U.ι
    · simp only [normalizedRestriction, pullback.lift_fst]
  let t : pullback N.cover.map U.ι ⟶ pullback N.normalization V.ι :=
    pullback.lift (pullback.fst N.cover.map U.ι) (normalizedRestriction N U ≫ g) (by
      rw [Category.assoc, hg]
      exact hpb.w)
  have ht : IsPullback t (normalizedRestriction N U)
      (pullback.snd N.normalization V.ι) g := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback N.normalization V.ι)
    · simpa only [t, pullback.lift_fst, hg] using hpb
    · simp only [t, pullback.lift_snd]
  exact ht.isIso_snd_of_isIso hV

/-- The good open lives IN THE BASE. An open of the image is insufficient
for comparing all generic sheets of every later test-line pullback. -/
structure GoodOpen {n : ℕ} {X : ContactFanoManifold n}
    {D : ProperPair X} {I : FiniteValueImage D} (N : NormalizedImage I) where
  openSet : (Square X).Opens
  dense : Dense (openSet : Set (Square X))
  etale : Etale (pullback.snd N.cover.map openSet.ι)
  unchanged : IsIso (normalizedRestriction N openSet)

theorem goodOpen_exists {n : ℕ} {X : ContactFanoManifold n}
    {D : ProperPair X} {I : FiniteValueImage D} (N : NormalizedImage I) :
    Nonempty (GoodOpen N) := by
  letI : IrreducibleSpace I.image := I.integral.1
  letI : AlgebraicGeometry.IsReduced I.image := ⟨I.integral.2⟩
  letI : IsIntegral I.image := isIntegral_of_irreducibleSpace_of_isReduced I.image
  letI : IrreducibleSpace (Square X) :=
    I.surjective.irreducibleSpace I.projection.continuous
  let s : Square X ⟶ ComplexBase :=
    firstProjection X.variety.structureMap ≫ X.variety.structureMap
  letI : Smooth s := inferInstance
  letI : AlgebraicGeometry.IsReduced (Square X) :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced s
  letI : IsIntegral (Square X) := isIntegral_of_irreducibleSpace_of_isReduced (Square X)
  letI : IsLocallyNoetherian (Square X) := LocallyOfFiniteType.isLocallyNoetherian s
  letI : IsFinite I.projection := I.finite
  letI : Surjective I.projection := ⟨I.surjective⟩
  letI : IrreducibleSpace N.cover.source := N.cover.integral.1
  letI : AlgebraicGeometry.IsReduced N.cover.source := ⟨N.cover.integral.2⟩
  letI : IsIntegral N.cover.source :=
    isIntegral_of_irreducibleSpace_of_isReduced N.cover.source
  letI : IsDominant N.cover.map := ⟨N.cover.dominant⟩
  obtain ⟨V, hVdense, hVi⟩ := N.birational
  obtain ⟨U₀, hU₀, hpre⟩ := FiniteCoverProof.shrink_dense_open I.projection V hVdense
  obtain ⟨Ue, hUe, hEtale⟩ :=
    FiniteCoverStandardInputs.finite_dominant_genericEtale s N.cover.map
  let U : (Square X).Opens := U₀ ⊓ Ue
  have hη₀ : genericPoint (Square X) ∈ U₀ :=
    ((genericPoint_spec (Square X)).mem_open_set_iff U₀.isOpen).mpr
      (by simpa using hU₀.nonempty)
  have hηe : genericPoint (Square X) ∈ Ue :=
    ((genericPoint_spec (Square X)).mem_open_set_iff Ue.isOpen).mpr
      (by simpa using hUe.nonempty)
  refine ⟨{
    openSet := U
    dense := U.isOpen.dense ⟨genericPoint (Square X), hη₀, hηe⟩
    etale := FiniteCoverProof.etale_on_smaller_open N.cover.map Ue U inf_le_right hEtale
    unchanged := normalizedRestriction_isIso_of_preimage_le N V hVi U ?_ }⟩
  exact (I.projection.preimage_mono inf_le_left).trans hpre

set_option backward.isDefEq.respectTransparency false in
inductive Axis where
  | first | second
  deriving DecidableEq, Repr, Fintype

/-- Both directions of test curves are required: a divisor can be vertical
for one projection of X x X. -/
def testLine {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X)
    (y : ComplexPoint X.variety) : Axis → (ProjectiveLine ⟶ Square X)
  | .first => pullback.lift f.curve.map (P.structureMap ≫ y.map)
      (by simp [Category.assoc, f.curve.overC, y.overC])
  | .second => pullback.lift (P.structureMap ≫ y.map) f.curve.map
      (by simp [Category.assoc, f.curve.overC, y.overC])

def MeetsOpen {Z : Scheme} (c : ProjectiveLine ⟶ Z) (U : Z.Opens) : Prop :=
  ∃ t : ProjectiveLine, c t ∈ U

/-- The GENERIC splitting condition is an actual isomorphism over a
nonempty open of P1. The WHOLE restricted cover is a disjoint union of
copies of that open. One distinguished rational sheet is not enough. -/
structure SplitOnOpen {S Z : Scheme} (q : S ⟶ Z) (c : ProjectiveLine ⟶ Z) where
  openSet : ProjectiveLine.Opens
  nonempty : ∃ t : ProjectiveLine, t ∈ openSet
  sheets : ℕ
  positiveSheets : 0 < sheets
  identification : pullback q (openSet.ι ≫ c) ≅ ∐ (fun _ : Fin sheets => openSet.toScheme)
  overSource : identification.hom ≫
      (Sigma.desc (fun _ : Fin sheets => 𝟙 openSet.toScheme)) =
    pullback.snd q (openSet.ι ≫ c)

/-- Every test line meeting the common good open must split, not just a
single general line and not just a single component of its pullback. -/
def AllSheetsSplit {n : ℕ} {X : ContactFanoManifold n}
    {D : ProperPair X} {I : FiniteValueImage D} (N : NormalizedImage I)
    (U : GoodOpen N) (H : CoveringFamily X) : Prop :=
  ∀ (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) (axis : Axis),
    MeetsOpen (testLine (H.lineAt t) y axis) U.openSet →
      Nonempty (SplitOnOpen N.cover.map (testLine (H.lineAt t) y axis))



/-! ### Actual degrees and actual ramification on test-curve normalizations -/

structure FiniteCurveCover where
  curve : Scheme
  map : curve ⟶ ProjectiveLine
  finite : IsFinite map
  integral : IntegralScheme curve
  normal : NormalScheme curve
  smooth : SmoothOfRelativeDimension 1 (map ≫ P.structureMap)
  dominant : DenseRange (fun x => map x)

attribute [instance] FiniteCurveCover.finite FiniteCurveCover.smooth

/-- Generic degree is rank of the pushforward of O on a NONEMPTY base
open. The integer is constrained by a geometric sheaf, not supplied freely. -/
def GenericDegree (C : FiniteCurveCover) (d : ℕ) : Prop :=
  ∃ U : ProjectiveLine.Opens, (∃ t : ProjectiveLine, t ∈ U) ∧
    IsLocallyFreeOfRank
      ((Scheme.Modules.pushforward (pullback.snd C.map U.ι)).obj
        (structureModule (pullback C.map U.ι))) d

/-- Ramification is measured by the actual homomorphism of local rings.
The closed-point qualification excludes the generic point, where the
zero maximal ideal would make the equality meaningless as an order. -/
def RamificationIndex (C : FiniteCurveCover) (x : C.curve) (e : ℕ) : Prop :=
  IsClosed ({x} : Set C.curve) ∧ 0 < e ∧
    (IsLocalRing.maximalIdeal (ProjectiveLine.presheaf.stalk (C.map x))).map
        (C.map.stalkMap x).hom =
      (IsLocalRing.maximalIdeal (C.curve.presheaf.stalk x))^e

/-- SOURCE degree formula in des:pullback-germ. Residue extensions at
closed complex points have degree one; every ramification index is <= deg. -/
theorem ramification_le_degree (C : FiniteCurveCover) (x : C.curve) (e d : ℕ)
    (he : RamificationIndex C x e) (hd : GenericDegree C d) : e ≤ d := by sorry

/-- Normalization of an ACTUAL dominating irreducible component of a
finite line pullback. Nonreduced/vertical components elsewhere are allowed. -/
structure ComponentNormalization {S Z : Scheme} (q : S ⟶ Z)
    (c : ProjectiveLine ⟶ Z) where
  component : Scheme
  insertion : component ⟶ pullback q c
  closed : IsClosedImmersion insertion
  integral : IntegralScheme component
  maximalComponent : Set.range (fun x : component => insertion x) ∈ irreducibleComponents (pullback q c : Scheme)
  curveCover : FiniteCurveCover
  normalization : curveCover.curve ⟶ component
  finite : IsFinite normalization
  birational : IsoOverDenseOpen normalization
  overLine : normalization ≫ insertion ≫ pullback.snd q c = curveCover.map

set_option backward.isDefEq.respectTransparency false in
/-- Split generic fibre means EVERY dominating normalized component has
degree one. It does not assert the entire pullback is reduced or flat. -/
theorem split_component_degree_one {S Z : Scheme} (q : S ⟶ Z)
    (c : ProjectiveLine ⟶ Z) (split : SplitOnOpen q c)
    (C : ComponentNormalization q c) : GenericDegree C.curveCover 1 := by
  classical
  letI : IrreducibleSpace C.curveCover.curve := C.curveCover.integral.1
  letI : AlgebraicGeometry.IsReduced C.curveCover.curve := ⟨C.curveCover.integral.2⟩
  letI : IsIntegral C.curveCover.curve :=
    isIntegral_of_irreducibleSpace_of_isReduced C.curveCover.curve
  letI : IsDominant C.curveCover.map := ⟨C.curveCover.dominant⟩
  letI : Surjective C.curveCover.map :=
    surjective_of_isDominant_of_isClosed_range C.curveCover.map
      C.curveCover.map.isClosedMap.isClosed_range
  letI : IrreducibleSpace ProjectiveLine :=
    C.curveCover.map.surjective.irreducibleSpace C.curveCover.map.continuous
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  letI : AlgebraicGeometry.IsReduced ProjectiveLine :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced P.structureMap
  letI : IsIntegral ProjectiveLine :=
    isIntegral_of_irreducibleSpace_of_isReduced ProjectiveLine
  letI : IrreducibleSpace C.component := C.integral.1
  letI : AlgebraicGeometry.IsReduced C.component := ⟨C.integral.2⟩
  letI : IsIntegral C.component := isIntegral_of_irreducibleSpace_of_isReduced C.component
  letI : IsClosedImmersion C.insertion := C.closed
  letI : IsFinite C.normalization := C.finite
  let e : C.component ⟶ ProjectiveLine := C.insertion ≫ pullback.snd q c
  have he : C.normalization ≫ e = C.curveCover.map := C.overLine
  letI : Surjective e := ⟨by
    intro x
    obtain ⟨y, hy⟩ := C.curveCover.map.surjective x
    refine ⟨C.normalization y, ?_⟩
    simpa only [← Scheme.Hom.comp_apply, he] using hy⟩
  let U := split.openSet
  letI : Nonempty U.toScheme := by
    obtain ⟨x, hx⟩ := split.nonempty
    exact ⟨⟨x, hx⟩⟩
  letI : Nonempty (pullback e U.ι : Scheme) := by
    let x : U.toScheme := Classical.choice inferInstance
    obtain ⟨y, _⟩ := (pullback.snd e U.ι).surjective x
    exact ⟨y⟩
  letI : IsIntegral (pullback e U.ι : Scheme) :=
    isIntegral_of_isOpenImmersion (pullback.fst e U.ι)
  -- Restrict the actual closed component along the base open. The two
  -- pullback pasting squares identify its inclusion in the split cover.
  let k : pullback q (U.ι ≫ c) ⟶ pullback q c :=
    pullback.lift (pullback.fst q (U.ι ≫ c))
      (pullback.snd q (U.ι ≫ c) ≫ U.ι) (by
        simpa only [Category.assoc] using
          pullback.condition (f := q) (g := U.ι ≫ c))
  let b : pullback e U.ι ⟶ pullback q (U.ι ≫ c) :=
    pullback.lift (pullback.fst e U.ι ≫ C.insertion ≫ pullback.fst q c)
      (pullback.snd e U.ι) (by
        simp only [Category.assoc, pullback.condition]
        simpa only [e, Category.assoc] using
          congrArg (fun a => a ≫ c) (pullback.condition (f := e) (g := U.ι)))
  have hb : b ≫ k = pullback.fst e U.ι ≫ C.insertion := by
    apply pullback.hom_ext
    · simp [b, k, Category.assoc]
    · simp only [b, k, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      simpa only [e, Category.assoc] using
        (pullback.condition (f := e) (g := U.ι)).symm
  have hkpb : IsPullback k (pullback.snd q (U.ι ≫ c)) (pullback.snd q c) U.ι := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q c)
    · simpa only [k, pullback.lift_fst] using IsPullback.of_hasPullback q (U.ι ≫ c)
    · simp only [k, pullback.lift_snd]
  have hbpb : IsPullback b (pullback.fst e U.ι) k C.insertion := by
    apply IsPullback.of_right (t := hkpb.flip)
    · simpa only [b, pullback.lift_snd, e] using
        (IsPullback.of_hasPullback e U.ι).flip
    · exact hb
  letI : IsClosedImmersion b :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hbpb.flip C.closed
  have hi : IsIso (pullback.snd e U.ι) := by
    apply FiniteCoverProof.closed_split_projection_isIso
      (b ≫ split.identification.hom) (pullback.snd e U.ι)
    rw [Category.assoc, split.overSource]
    exact pullback.lift_snd _ _ _
  -- A further nonempty base open puts the entire component inside the
  -- dense locus on which its actual normalization map is an isomorphism.
  have hn : Function.Surjective C.normalization :=
    IsoOverDenseOpen.surjective C.normalization C.birational
  obtain ⟨V, hV, hVi⟩ := C.birational
  have hVpre : Dense (C.normalization ⁻¹ᵁ V : Set C.curveCover.curve) := by
    obtain ⟨z, hz⟩ := hV.nonempty
    obtain ⟨y, hy⟩ := hn z
    refine (C.normalization ⁻¹ᵁ V).isOpen.dense ⟨y, ?_⟩
    change C.normalization y ∈ (V : Set C.component)
    exact hy.symm ▸ hz
  obtain ⟨U₀, hU₀, hpre⟩ := FiniteCoverProof.shrink_dense_open
    C.curveCover.map (C.normalization ⁻¹ᵁ V) hVpre
  let W : ProjectiveLine.Opens := U₀ ⊓ U
  have hη₀ : genericPoint ProjectiveLine ∈ U₀ :=
    ((genericPoint_spec ProjectiveLine).mem_open_set_iff U₀.isOpen).mpr
      (by simpa using hU₀.nonempty)
  have hηU : genericPoint ProjectiveLine ∈ U :=
    ((genericPoint_spec ProjectiveLine).mem_open_set_iff U.isOpen).mpr
      (by
        obtain ⟨x, hx⟩ := split.nonempty
        refine ⟨x, ?_⟩
        refine ⟨Set.mem_univ x, ?_⟩
        change x ∈ split.openSet
        exact hx)
  have hW : ∃ x : ProjectiveLine, x ∈ W := ⟨genericPoint ProjectiveLine, hη₀, hηU⟩
  have hWV : e ⁻¹ᵁ W ≤ V := by
    intro z hz
    obtain ⟨y, rfl⟩ := hn z
    have hym : C.curveCover.map y ∈ U₀ := by
      have hy := hz.1
      change e (C.normalization y) ∈ U₀ at hy
      simpa only [← Scheme.Hom.comp_apply, he] using hy
    exact hpre hym
  have heW : IsIso (pullback.snd e W.ι) :=
    FiniteCoverProof.isIso_on_smaller_open e U W inf_le_right hi
  letI : IsIso (pullback.snd C.curveCover.map W.ι) :=
    FiniteCoverProof.composite_restriction_isIso C.normalization e C.curveCover.map
      he V hVi W hWV heW
  letI := P1Restriction.structurePushforwardMap_isIso (pullback.snd C.curveCover.map W.ι)
  exact ⟨W, hW, locallyFreeOfRank_iso
    (asIso (structurePushforwardMap (pullback.snd C.curveCover.map W.ι)))
    (structureModule_rank W.toScheme)⟩

theorem split_component_unramified {S Z : Scheme} (q : S ⟶ Z)
    (c : ProjectiveLine ⟶ Z) (split : SplitOnOpen q c)
    (C : ComponentNormalization q c) (x : C.curveCover.curve) (e : ℕ)
    (he : RamificationIndex C.curveCover x e) : e = 1 := by
  have hle := ramification_le_degree C.curveCover x e 1 he
    (split_component_degree_one q c split C)
  have hpos := he.2.1
  omega

/-- Output of the transversal test-curve argument. The index e refers to
the ACTUAL normalized curve local-ring map; it is not a numerical label. -/
structure RamifiedTest {n : ℕ} {X : ContactFanoManifold n}
    {D : ProperPair X} {I : FiniteValueImage D} (N : NormalizedImage I)
    (U : GoodOpen N) (H : CoveringFamily X) where
  member : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC
  otherPoint : ComplexPoint X.variety
  axis : Axis
  meets : MeetsOpen (testLine (H.lineAt member) otherPoint axis) U.openSet
  component : ComponentNormalization N.cover.map (testLine (H.lineAt member) otherPoint axis)
  ramifiedPoint : component.curveCover.curve
  index : ℕ
  ramification : RamificationIndex component.curveCover ramifiedPoint index
  ramified : 1 < index



/-- All sheets, rather than one sheet, are exactly what is needed for
this contradiction. The proof does not use simple connectedness yet. -/
theorem allSheets_exclude_ramifiedTest {n : ℕ} {X : ContactFanoManifold n}
    {D : ProperPair X} {I : FiniteValueImage D} {N : NormalizedImage I}
    {U : GoodOpen N} {H : CoveringFamily X} (hs : AllSheetsSplit N U H)
    (R : RamifiedTest N U H) : False := by
  obtain ⟨split⟩ := hs R.member R.otherPoint R.axis R.meets
  have h := split_component_unramified N.cover.map _ split R.component R.ramifiedPoint
    R.index R.ramification
  exact (Nat.ne_of_gt R.ramified) h

/-- SOURCE Stacks 0BMB, specialized to the smooth base X x X. Normality
of the finite source and equality of local dimensions must be established;
flatness is a CONCLUSION, not an assumption on the original cover. -/
theorem purity_over_contactSquare {n : ℕ} {X : ContactFanoManifold n}
    (N : FiniteNormalCover (Square X)) (h : EtaleInCodimensionOne N.map) :
    Etale N.map := by sorry

/-- Classical Fano simple connectedness + analytic covering comparison.
Integral/nonempty source is essential: a disjoint trivial cover need not
be an isomorphism. This lemma is independent of the primitive Picard case. -/
theorem finiteEtale_contactSquare_trivial {n : ℕ} (X : ContactFanoManifold n)
    (N : FiniteNormalCover (Square X)) (he : Etale N.map) : IsIso N.map := by sorry

/-- A trivial normalization cover forces the given reduced finite image itself
to have isomorphic projection. This uses the actual normalization map. -/
theorem NormalizedImage.projection_isIso_of_cover_isIso {n : ℕ}
    {X : ContactFanoManifold n} {D : ProperPair X} {I : FiniteValueImage D}
    (N : NormalizedImage I) (hi : IsIso N.cover.map) : IsIso I.projection := by
  letI : IsFinite I.projection := I.finite
  letI : IsFinite N.normalization := N.finite
  letI : IsIso N.cover.map := hi
  letI : IsIso (N.normalization ≫ I.projection) := by
    rw [N.overSquare]
    infer_instance
  letI : IsClosedImmersion N.normalization :=
    IsClosedImmersion.of_comp N.normalization I.projection
  letI : AlgebraicGeometry.IsReduced I.image := ⟨I.integral.2⟩
  letI : Surjective N.normalization :=
    ⟨IsoOverDenseOpen.surjective N.normalization N.birational⟩
  letI : IsIso N.normalization :=
    isIso_of_isClosedImmersion_of_surjective N.normalization
  exact IsIso.of_isIso_comp_left N.normalization I.projection

/-- The isomorphism of the NORMALIZATION implies the ORIGINAL finite
image is a graph, by finite birationality over a normal base (Stacks 0AB1).
There is still no hypothesized map from the original source to the normalization. -/
theorem finiteImage_graph_recovers_section {n : ℕ} {X : ContactFanoManifold n}
    (D : ProperPair X) (I : FiniteValueImage D) (N : NormalizedImage I)
    (hi : IsIso N.cover.map) :
    ∃ B : ExternalSquareSections X.variety X.contact.sequence.line, D.DescendsTo B := by
  letI : IsIso I.projection := N.projection_isIso_of_cover_isIso hi
  let u : Square X ⟶ I.total.space := inv I.projection ≫ I.inclusion
  have hu : u ≫ I.total.projection = 𝟙 (Square X) := by
    dsimp only [u]
    rw [Category.assoc, I.overSquare, IsIso.inv_hom_id]
  let a := I.total.representedSection (𝟙 (Square X)) u hu
  let B : ExternalSquareSections X.variety X.contact.sequence.line :=
    a ≫ (Scheme.Modules.pullbackId (Square X)).hom.app (SquareLine X).sheaf
  have ha : a = pullSection (𝟙 (Square X)) B := by
    apply (cancel_mono
      ((Scheme.Modules.pullbackId (Square X)).hom.app (SquareLine X).sheaf)).mp
    exact (LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof.pullSection_id B).symm
  have hB : (I.total.mapOfSection (𝟙 (Square X))
      (pullSection (𝟙 (Square X)) B)).val = u := by
    rw [← ha]
    exact I.total.mapOfSection_representedSection (𝟙 (Square X)) u hu
  have hsource : D.pair.data.projection ≫ u =
      (I.total.mapOfSection D.pair.data.projection D.value).val := by
    calc
      D.pair.data.projection ≫ u =
          (I.fromSource ≫ I.projection) ≫ u :=
        congrArg (fun p => p ≫ u) I.sourceOver.symm
      _ = I.fromSource ≫ I.inclusion := by
        simp only [u, Category.assoc, IsIso.hom_inv_id_assoc]
      _ = (I.total.mapOfSection D.pair.data.projection D.value).val :=
        I.imageEquation
  have hnatural := I.total.mapOfSection_naturality (𝟙 (Square X))
    D.pair.data.projection D.pair.data.projection (Category.comp_id _)
    (pullSection (𝟙 (Square X)) B)
  rw [hB, compositionPullback_sections] at hnatural
  refine ⟨B, ?_⟩
  change pullSection D.pair.data.projection B = D.value
  exact I.total.mapOfSection_injective D.pair.data.projection
    (hnatural.symm.trans hsource)

/-- Seven mathematical construction/comparison slots and one classical
rigidity slot replace a single admitted contact-value descent assertion. -/
structure Inputs : Prop where
  lines : ∀ (n : ℕ) (X : ContactFanoManifold n), HasPrimitiveContactPicard X.contact →
    Nonempty (CoveringFamily X)
  finiteImage : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : ProperPair X),
    Nonempty (FiniteValueImage D)
  normalize : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : ProperPair X)
    (I : FiniteValueImage D), ∃ N : NormalizedImage I, Nonempty (GoodOpen N)
  splitSheets : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : ProperPair X)
    (I : FiniteValueImage D) (N : NormalizedImage I) (U : GoodOpen N)
    (H : CoveringFamily X), AllSheetsSplit N U H
  detectBranch : ∀ (n : ℕ) (X : ContactFanoManifold n), HasPrimitiveContactPicard X.contact →
    ∀ (D : ProperPair X) (I : FiniteValueImage D) (N : NormalizedImage I)
      (U : GoodOpen N) (H : CoveringFamily X),
      ¬ EtaleInCodimensionOne N.cover.map → Nonempty (RamifiedTest N U H)
  purity : ∀ (n : ℕ) (X : ContactFanoManifold n) (N : FiniteNormalCover (Square X)),
    EtaleInCodimensionOne N.map → Etale N.map
  rigidity : ∀ (n : ℕ) (X : ContactFanoManifold n) (N : FiniteNormalCover (Square X)),
    Etale N.map → IsIso N.map
  graph : ∀ (n : ℕ) (X : ContactFanoManifold n) (D : ProperPair X)
    (I : FiniteValueImage D) (N : NormalizedImage I), IsIso N.cover.map →
      ∃ B : ExternalSquareSections X.variety X.contact.sequence.line, D.DescendsTo B

/-- Forward descent proof from the supplied smaller lemmas. The local
ramification/degree comparison and uniqueness are explicit foundations.
No contactValueDescent_obligation or whole-package admission is called. -/
theorem Inputs.assemble (H : Inputs) {n : ℕ} (X : ContactFanoManifold n)
    (hp : HasPrimitiveContactPicard X.contact) (D : ProperPair X) :
    ∃! B : ExternalSquareSections X.variety X.contact.sequence.line, D.DescendsTo B := by
  classical
  obtain ⟨L⟩ := H.lines n X hp
  obtain ⟨I⟩ := H.finiteImage n X D
  obtain ⟨N, hU⟩ := H.normalize n X D I
  obtain ⟨U⟩ := hU
  have hs := H.splitSheets n X D I N U L
  have hc : EtaleInCodimensionOne N.cover.map := by
    by_contra h
    obtain ⟨R⟩ := H.detectBranch n X hp D I N U L h
    exact allSheets_exclude_ramifiedTest hs R
  have hi := H.rigidity n X N.cover (H.purity n X N.cover hc)
  obtain ⟨B, hB⟩ := H.graph n X D I N hi
  refine ⟨B, hB, ?_⟩
  intro C hC
  exact D.descent_unique hC hB

end Descent

end LeBrunSalamon.Construction

namespace LeBrunSalamon.Refinement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction



end LeBrunSalamon.Refinement

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


/-! ## The conic source as a scheme of equality of two sections -/
namespace Smoothing

open Lines

namespace CoordinateCharts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace StandardInputs

/-- **Published input (exact).** Spectra turn a pullback of rings
into a pushout of affine schemes when one map to the common quotient is
surjective.  This is Stacks Project, Lemma 37.14.1 (Tag 0ET0). -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.spec_pullback_isPushout
    {A B C : CommRingCat} (f : A ⟶ C) (g : B ⟶ C)
    (hf : Function.Surjective f.hom) :
    IsPushout (Spec.map f) (Spec.map g)
      (Spec.map (pullback.fst f g)) (Spec.map (pullback.snd f g)) := by
  sorry

/-- Project API wrapper for the affine pushout theorem. -/
theorem spec_pullback_isPushout {A B C : CommRingCat}
    (f : A ⟶ C) (g : B ⟶ C) (hf : Function.Surjective f.hom) :
    IsPushout (Spec.map f) (Spec.map g)
      (Spec.map (pullback.fst f g)) (Spec.map (pullback.snd f g)) :=
  LeBrunSalamon.PublishedInputs.BaseChangeFibers.spec_pullback_isPushout f g hf

/-- The original generating tuple defines an actual nonvanishing-open cover.
The cover and its pullback unit criterion are proved in LSGeneratingUnitOpens;
this historical public name no longer carries a direct admission. -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.generating_sections_unitOpen
    {Y : Scheme} {N : ℕ}
    (L : LineBundle Y) (a : Fin (N+1) → AlgebraicSection L.sheaf)
    (ha : TupleGenerates L a) :
    ∃ U : Fin (N+1) → Y.Opens, iSup U = ⊤ ∧
      ∀ (i : Fin (N+1)) (T : Scheme) (f : T ⟶ Y),
        Set.range f ⊆ (U i : Set Y) ↔ IsIso (pullSection f (a i)) := by
  exact LeBrunSalamon.GeneratingUnitOpens.generating_sections_unitOpen L a ha

/-- Project API wrapper for the unit-locus open cover. -/
theorem generating_sections_unitOpen {Y : Scheme} {N : ℕ}
    (L : LineBundle Y) (a : Fin (N+1) → AlgebraicSection L.sheaf)
    (ha : TupleGenerates L a) :
    ∃ U : Fin (N+1) → Y.Opens, iSup U = ⊤ ∧
      ∀ (i : Fin (N+1)) (T : Scheme) (f : T ⟶ Y),
        Set.range f ⊆ (U i : Set Y) ↔ IsIso (pullSection f (a i)) :=
  LeBrunSalamon.PublishedInputs.BaseChangeFibers.generating_sections_unitOpen L a ha

end StandardInputs

/-- A regular function is retained as the corresponding actual
endomorphism of the structure sheaf. -/
def scalarSection {T : Scheme} (a : RingSections T ⊤) :
    AlgebraicSection (structureModule T) := sectionFromValue a

theorem scalarSection_one (T : Scheme) :
    scalarSection (T := T) 1 = 𝟙 (structureModule T) := by
  apply (sectionValue_bijective _).injective
  rw [scalarSection, sectionFromValue_spec]
  rfl

/-- Pullback of these scalar sections is normalized by the actual unit
pullback isomorphism. -/
theorem scalarSection_pullback {T Y : Scheme} (f : T ⟶ Y)
    (a : RingSections Y ⊤) :
    pullSection f (scalarSection a) ≫ (unitPullbackIso f).hom =
      scalarSection (f.appTop a) := by
  apply (sectionValue_bijective _).injective
  rw [sectionValue_comp]
  change (unitPullbackMap f).app ⊤ (sectionValue (pullSection f (scalarSection a))) =
    sectionValue (scalarSection (f.appTop a))
  exact (FrameEvaluation.unit_pullSection_value f (scalarSection a)).trans
    ((congrArg (fun z : RingSections Y ⊤ => f.appTop z)
      (sectionFromValue_spec (E := structureModule Y) a)).trans
      (sectionFromValue_spec (E := structureModule T) (f.appTop a)).symm)

/-- A map to the actual affine parameter line from a global function on
an arbitrary test scheme. No affine or reduced test restriction is used. -/
def fromFunction {T : Scheme} (sT : T ⟶ ComplexBase) (a : RingSections T ⊤) :
    T ⟶ AffineLine :=
  (ΓSpec.adjunction.homEquiv T (Opposite.op (CommRingCat.of (Polynomial ℂ))))
    (CommRingCat.ofHom (Polynomial.eval₂RingHom (complexConstants sT) a)).op

theorem fromFunction_apply {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) (p : Polynomial ℂ) :
    (fromFunction sT a).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv p) =
      Polynomial.eval₂ (complexConstants sT) a p := by
  exact congrArg (fun k : CommRingCat.of (Polynomial ℂ) ⟶
    T.presheaf.obj (Opposite.op ⊤) => k p)
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (CommRingCat.ofHom (Polynomial.eval₂RingHom (complexConstants sT) a)))

theorem fromFunction_parameter {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) : (fromFunction sT a).appTop parameterFunction = a := by
  rw [parameterFunction, fromFunction_apply, Polynomial.eval₂_X]

theorem affineLine_constant (c : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv (Polynomial.C c) =
      complexConstants affineLineToC c := by
  rw [complexConstants_apply_top]
  exact congrArg (fun k : CommRingCat.of ℂ ⟶ AffineLine.presheaf.obj (Opposite.op ⊤) => k c)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)))

theorem fromFunction_over {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) : fromFunction sT a ≫ affineLineToC = sT := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext c
  change (fromFunction sT a).appTop
      (affineLineToC.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
    sT.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  rw [← complexConstants_apply_top, ← affineLine_constant, fromFunction_apply,
    Polynomial.eval₂_C, complexConstants_apply_top]

theorem functionMap_ext {T : Scheme} (sT : T ⟶ ComplexBase)
    {f g : T ⟶ AffineLine} (hf : f ≫ affineLineToC = sT)
    (hg : g ≫ affineLineToC = sT)
    (h : f.appTop parameterFunction = g.appTop parameterFunction) : f = g := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv (Polynomial.C c)) =
      g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv (Polynomial.C c))
    rw [affineLine_constant, complexConstants_naturality f sT affineLineToC hf,
      complexConstants_naturality g sT affineLineToC hg]
  · exact h

theorem fromFunction_unique {T : Scheme} (sT : T ⟶ ComplexBase)
    (a : RingSections T ⊤) (f : T ⟶ AffineLine)
    (hf : f ≫ affineLineToC = sT) (ha : f.appTop parameterFunction = a) :
    f = fromFunction sT a :=
  functionMap_ext sT hf (fromFunction_over sT a)
    (ha.trans (fromFunction_parameter sT a).symm)

/-- Pullback preserves a generating tuple over every test scheme. -/
theorem pulled_tuple_generates {Y T : Scheme} {N : ℕ}
    (L : LineBundle Y) (a : Fin (N+1) → AlgebraicSection L.sheaf)
    (ha : TupleGenerates L a) (f : T ⟶ Y) :
    TupleGenerates (pullbackLine f L) (fun i => pullSection f (a i)) := by
  let F : SheafOfModules.{0} Y.ringCatSheaf ⥤ SheafOfModules.{0} T.ringCatSheaf :=
    Scheme.Modules.pullback f
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).isLeftAdjoint
  let q : SheafOfModules.free (R := Y.ringCatSheaf) (Fin (N+1)) ⟶ L.sheaf :=
    Sigma.desc a
  letI : Epi q := ha
  letI : Epi (F.map q) := inferInstance
  let c := SheafOfModules.mapFreeIso F (Fin (N+1)) (unitPullbackIso f).symm
  have h : Sigma.desc (fun i => pullSection f (a i)) = c.hom ≫ F.map q := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc]
    change pullSection f (a i) = SheafOfModules.ιFree i ≫ c.hom ≫ F.map q
    erw [SheafOfModules.ιFree_mapFreeIso_hom_assoc, ← Functor.map_comp]
    simp only [q, SheafOfModules.ιFree, Sigma.ι_comp_desc,
      pullSection, restrictSection, F, Iso.symm_hom]
  change Epi (Sigma.desc (fun i => pullSection f (a i)))
  rw [h]
  infer_instance

/-- Equality of maps follows from an isomorphism of their actual
quotient lines carrying every specified coordinate section. -/
theorem coordinate_ext {T : Scheme} {sT : T ⟶ ComplexBase} {N : ℕ}
    (C : ProjectiveCoordinates N)
    (f g : PointsOver T sT (ComplexProjectiveSpace N) (projectiveBaseMap N))
    (e : pullbackModule f.val C.hyperplane.sheaf ≅ pullbackModule g.val C.hyperplane.sheaf)
    (he : ∀ i, pullSection f.val (C.coordinate i) ≫ e.hom = pullSection g.val (C.coordinate i)) :
    f = g := by
  obtain ⟨h, _, hu⟩ := C.universal T sT (pullbackLine g.val C.hyperplane)
    (fun i => pullSection g.val (C.coordinate i))
    (pulled_tuple_generates C.hyperplane C.coordinate C.generates g.val)
  exact (hu f ⟨e, he⟩).trans (hu g ⟨Iso.refl _, by intro i; simp⟩).symm

theorem coordinate_ext_of_frames {T : Scheme} {sT : T ⟶ ComplexBase} {N : ℕ}
    (C : ProjectiveCoordinates N)
    (f g : PointsOver T sT (ComplexProjectiveSpace N) (projectiveBaseMap N))
    (e : pullbackModule f.val C.hyperplane.sheaf ≅ structureModule T)
    (d : pullbackModule g.val C.hyperplane.sheaf ≅ structureModule T)
    (h : ∀ i, pullSection f.val (C.coordinate i) ≫ e.hom =
      pullSection g.val (C.coordinate i) ≫ d.hom) : f = g := by
  apply coordinate_ext C f g (e ≪≫ d.symm)
  intro i
  change pullSection f.val (C.coordinate i) ≫ e.hom ≫ d.inv = _
  rw [← Category.assoc, h i, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The ratio charts are defined from the same chosen quotient as the
conic equation. They are not borrowed from independent homogeneous variables. -/
def ratioTuple (i : Fin 2) : Fin 2 → AlgebraicSection (structureModule AffineLine) :=
  fun j => if j = i then 𝟙 _ else scalarSection parameterFunction

theorem ratioTuple_generates (i : Fin 2) :
    TupleGenerates (trivialLine AffineLine) (ratioTuple i) := by
  have hi : ratioTuple i i = 𝟙 (structureModule AffineLine) := by simp [ratioTuple]
  letI : IsIso (ratioTuple i i) := by rw [hi]; infer_instance
  change Epi (Sigma.desc (ratioTuple i))
  exact epi_of_epi_fac (Sigma.ι_comp_desc (ratioTuple i) i)

def ratioPoint (i : Fin 2) : PointsOver AffineLine affineLineToC ProjectiveLine P.structureMap :=
  Classical.choose ((projectiveCoordinates 1).universal AffineLine affineLineToC
    (trivialLine AffineLine) (ratioTuple i) (ratioTuple_generates i))

def ratioFrame (i : Fin 2) :
    pullbackModule (ratioPoint i).val (projectiveCoordinates 1).hyperplane.sheaf ≅
      structureModule AffineLine :=
  Classical.choose (Classical.choose_spec ((projectiveCoordinates 1).universal
    AffineLine affineLineToC (trivialLine AffineLine) (ratioTuple i)
      (ratioTuple_generates i))).1

theorem ratioPoint_coordinate (i j : Fin 2) :
    pullSection (ratioPoint i).val ((projectiveCoordinates 1).coordinate j) ≫
        (ratioFrame i).hom = ratioTuple i j :=
  Classical.choose_spec (Classical.choose_spec ((projectiveCoordinates 1).universal
    AffineLine affineLineToC (trivialLine AffineLine) (ratioTuple i)
      (ratioTuple_generates i))).1 j

theorem ratioPoint_coordinate_self (i : Fin 2) :
    pullSection (ratioPoint i).val ((projectiveCoordinates 1).coordinate i) ≫
        (ratioFrame i).hom = 𝟙 (structureModule AffineLine) := by
  rw [ratioPoint_coordinate, ratioTuple, if_pos rfl]

theorem ratioPoint_coordinate_other (i j : Fin 2) (hji : j ≠ i) :
    pullSection (ratioPoint i).val ((projectiveCoordinates 1).coordinate j) ≫
        (ratioFrame i).hom = scalarSection parameterFunction := by
  rw [ratioPoint_coordinate, ratioTuple, if_neg hji]

/-- The ratio-chart frame after an arbitrary base map retains all
composition-pullback and unit maps explicitly. -/
def ratioPullFrame {T : Scheme} (g : T ⟶ AffineLine) (i : Fin 2) :
    pullbackModule (g ≫ (ratioPoint i).val) (projectiveCoordinates 1).hyperplane.sheaf ≅
      structureModule T :=
  (compositionPullback g (ratioPoint i).val (g ≫ (ratioPoint i).val) rfl
    (projectiveCoordinates 1).hyperplane.sheaf).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (ratioFrame i) ≪≫ unitPullbackIso g

theorem ratioPullFrame_coordinate {T : Scheme} (g : T ⟶ AffineLine) (i j : Fin 2) :
    pullSection (g ≫ (ratioPoint i).val) ((projectiveCoordinates 1).coordinate j) ≫
        (ratioPullFrame g i).hom =
      if j = i then 𝟙 (structureModule T) else scalarSection (g.appTop parameterFunction) := by
  rw [← compositionPullback_sections g (ratioPoint i).val (g ≫ (ratioPoint i).val) rfl]
  simp only [ratioPullFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← pullSection_naturality, ratioPoint_coordinate]
  by_cases hji : j = i
  · simp only [ratioTuple, if_pos hji]
    rw [← scalarSection_one AffineLine, scalarSection_pullback, map_one, scalarSection_one]
  · simp only [ratioTuple, if_neg hji, scalarSection_pullback]

def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem other_ne (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

theorem eq_other_of_ne {i j : Fin 2} (h : j ≠ i) : j = other i := by
  fin_cases i <;> fin_cases j <;> simp_all [other]

/-- A point whose specified coordinate is a unit has its other
coordinate as an actual regular ratio function. -/
def ratioFunction {T : Scheme} (f : T ⟶ ProjectiveLine) (i : Fin 2)
    [IsIso (pullSection f ((projectiveCoordinates 1).coordinate i))] : RingSections T ⊤ :=
  sectionValue (pullSection f ((projectiveCoordinates 1).coordinate (other i)) ≫
    (asIso (pullSection f ((projectiveCoordinates 1).coordinate i))).inv)

/-- Factor through the ratio chart on every test scheme on which the
selected quotient section is invertible. The factor uses its exact
regular ratio, including nilpotent coefficients. -/
theorem ratioPoint_factors {T : Scheme} (sT : T ⟶ ComplexBase)
    (f : PointsOver T sT ProjectiveLine P.structureMap) (i : Fin 2)
    [IsIso (pullSection f.val ((projectiveCoordinates 1).coordinate i))] :
    fromFunction sT (ratioFunction f.val i) ≫ (ratioPoint i).val = f.val := by
  let g := fromFunction sT (ratioFunction f.val i)
  let p : PointsOver T sT ProjectiveLine P.structureMap :=
    ⟨g ≫ (ratioPoint i).val, by rw [Category.assoc, (ratioPoint i).property,
      fromFunction_over]⟩
  let e := (asIso (pullSection f.val ((projectiveCoordinates 1).coordinate i))).symm
  have h : p = f := by
    apply coordinate_ext_of_frames (projectiveCoordinates 1) p f (ratioPullFrame g i) e
    intro j
    rw [ratioPullFrame_coordinate]
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      exact (Iso.hom_inv_id _).symm
    · rw [if_neg hji, eq_other_of_ne hji]
      change scalarSection (g.appTop parameterFunction) =
        pullSection f.val ((projectiveCoordinates 1).coordinate (other i)) ≫
          (asIso (pullSection f.val ((projectiveCoordinates 1).coordinate i))).inv
      rw [fromFunction_parameter]
      exact sectionFromValue_sectionValue _
  exact congrArg Subtype.val h

theorem ratioPull_self_isIso {T : Scheme} (g : T ⟶ AffineLine) (i : Fin 2) :
    IsIso (pullSection (g ≫ (ratioPoint i).val) ((projectiveCoordinates 1).coordinate i)) := by
  have h : pullSection (g ≫ (ratioPoint i).val) ((projectiveCoordinates 1).coordinate i) =
      (ratioPullFrame g i).inv := by
    apply (cancel_mono (ratioPullFrame g i).hom).mp
    rw [ratioPullFrame_coordinate, if_pos rfl, Iso.inv_hom_id]
  rw [h]
  infer_instance

theorem ratioFunction_comp {T : Scheme} (g : T ⟶ AffineLine) (i : Fin 2)
    [IsIso (pullSection (g ≫ (ratioPoint i).val) ((projectiveCoordinates 1).coordinate i))] :
    ratioFunction (g ≫ (ratioPoint i).val) i = g.appTop parameterFunction := by
  have he : (asIso (pullSection (g ≫ (ratioPoint i).val)
      ((projectiveCoordinates 1).coordinate i))).inv = (ratioPullFrame g i).hom := by
    apply Iso.inv_ext
    change pullSection (g ≫ (ratioPoint i).val)
      ((projectiveCoordinates 1).coordinate i) ≫ (ratioPullFrame g i).hom =
        𝟙 (structureModule T)
    exact (ratioPullFrame_coordinate g i i).trans (if_pos rfl)
  rw [ratioFunction, he, ratioPullFrame_coordinate, if_neg (other_ne i),
    scalarSection, sectionFromValue_spec]

/-- The ratio chart is a monomorphism on all test schemes: equality of
the quotient maps recovers equality of the exact regular ratio functions. -/
theorem ratioPoint_mono (i : Fin 2) : Mono (ratioPoint i).val := by
  refine ⟨?_⟩
  intro T g h hgh
  have hb : h ≫ affineLineToC = g ≫ affineLineToC := by
    have hz := congrArg (fun k => k ≫ P.structureMap) hgh
    simpa only [Category.assoc, (ratioPoint i).property] using hz.symm
  apply functionMap_ext (g ≫ affineLineToC) rfl hb
  letI := ratioPull_self_isIso g i
  letI := ratioPull_self_isIso h i
  have hg := ratioFunction_comp g i
  have hh := ratioFunction_comp h i
  let ratio : {f : T ⟶ ProjectiveLine //
      IsIso (pullSection f ((projectiveCoordinates 1).coordinate i))} → RingSections T ⊤ :=
    fun f => @ratioFunction T f.val i f.property
  have hr := congrArg ratio
    (Subtype.ext hgh :
      (⟨g ≫ (ratioPoint i).val, inferInstance⟩ : {f : T ⟶ ProjectiveLine //
        IsIso (pullSection f ((projectiveCoordinates 1).coordinate i))}) =
      ⟨h ≫ (ratioPoint i).val, inferInstance⟩)
  exact hg.symm.trans (hr.trans hh)

def ratioOpen (i : Fin 2) : ProjectiveLine.Opens :=
  Classical.choose (StandardInputs.generating_sections_unitOpen
    (projectiveCoordinates 1).hyperplane (projectiveCoordinates 1).coordinate
      (projectiveCoordinates 1).generates) i

theorem ratioOpen_cover : (⨆ i : Fin 2, ratioOpen i) = ⊤ :=
  (Classical.choose_spec (StandardInputs.generating_sections_unitOpen
    (projectiveCoordinates 1).hyperplane (projectiveCoordinates 1).coordinate
      (projectiveCoordinates 1).generates)).1

theorem ratioOpen_range_iff (i : Fin 2) {T : Scheme} (f : T ⟶ ProjectiveLine) :
    Set.range f ⊆ (ratioOpen i : Set ProjectiveLine) ↔
      IsIso (pullSection f ((projectiveCoordinates 1).coordinate i)) :=
  (Classical.choose_spec (StandardInputs.generating_sections_unitOpen
    (projectiveCoordinates 1).hyperplane (projectiveCoordinates 1).coordinate
      (projectiveCoordinates 1).generates)).2 i T f

theorem ratioPoint_self_isIso (i : Fin 2) :
    IsIso (pullSection (ratioPoint i).val ((projectiveCoordinates 1).coordinate i)) := by
  have h : pullSection (ratioPoint i).val ((projectiveCoordinates 1).coordinate i) =
      (ratioFrame i).inv := by
    apply (cancel_mono (ratioFrame i).hom).mp
    rw [ratioPoint_coordinate_self, Iso.inv_hom_id]
  rw [h]
  infer_instance

def ratioToOpen (i : Fin 2) : AffineLine ⟶ (ratioOpen i).toScheme :=
  IsOpenImmersion.lift (ratioOpen i).ι (ratioPoint i).val (by
    rw [Scheme.Opens.range_ι]
    exact (ratioOpen_range_iff i _).mpr (ratioPoint_self_isIso i))

theorem ratioToOpen_inclusion (i : Fin 2) :
    ratioToOpen i ≫ (ratioOpen i).ι = (ratioPoint i).val :=
  IsOpenImmersion.lift_fac _ _ _

theorem ratioOpen_coordinate_isIso (i : Fin 2) :
    IsIso (pullSection (ratioOpen i).ι ((projectiveCoordinates 1).coordinate i)) :=
  (ratioOpen_range_iff i _).mp (by rw [Scheme.Opens.range_ι])

def openToRatio (i : Fin 2) : (ratioOpen i).toScheme ⟶ AffineLine := by
  letI := ratioOpen_coordinate_isIso i
  exact fromFunction ((ratioOpen i).ι ≫ P.structureMap) (ratioFunction (ratioOpen i).ι i)

theorem openToRatio_point (i : Fin 2) :
    openToRatio i ≫ (ratioPoint i).val = (ratioOpen i).ι := by
  letI := ratioOpen_coordinate_isIso i
  exact ratioPoint_factors ((ratioOpen i).ι ≫ P.structureMap)
    ⟨(ratioOpen i).ι, rfl⟩ i

/-- The affine ratio chart is now identified with its actual unit open
by two explicit inverse morphisms, with the chosen quotient retained. -/
def ratioOpenIso (i : Fin 2) : (ratioOpen i).toScheme ≅ AffineLine where
  hom := openToRatio i
  inv := ratioToOpen i
  hom_inv_id := by
    apply (cancel_mono (ratioOpen i).ι).mp
    rw [Category.assoc, ratioToOpen_inclusion, openToRatio_point, Category.id_comp]
  inv_hom_id := by
    letI := ratioPoint_mono i
    apply (cancel_mono (ratioPoint i).val).mp
    rw [Category.assoc, openToRatio_point, ratioToOpen_inclusion, Category.id_comp]

theorem ratioPoint_openImmersion (i : Fin 2) : IsOpenImmersion (ratioPoint i).val := by
  rw [← ratioToOpen_inclusion i]
  change IsOpenImmersion ((ratioOpenIso i).inv ≫ (ratioOpen i).ι)
  infer_instance

theorem ratioPoint_range (i : Fin 2) :
    Set.range (ratioPoint i).val = (ratioOpen i : Set ProjectiveLine) := by
  rw [← ratioToOpen_inclusion i]
  change Set.range ((ratioOpenIso i).inv ≫ (ratioOpen i).ι) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso (ratioOpenIso i).inv.base).surjective.range_eq,
    Set.image_univ, Scheme.Opens.range_ι]

end CoordinateCharts

namespace StandardSourceProof

open LeBrunSalamon.Refinement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SectionEquality

variable {B : Scheme} {L : LineBundle B} (V : Descent.TotalLine L)

/-- The graph associated with a genuine global section of the line bundle. -/
def graph (a : AlgebraicSection L.sheaf) : B ⟶ V.space :=
  (V.mapOfSection (𝟙 B) (pullSection (𝟙 B) a)).val

theorem graph_over (a : AlgebraicSection L.sheaf) :
    graph V a ≫ V.projection = 𝟙 B :=
  (V.mapOfSection (𝟙 B) (pullSection (𝟙 B) a)).property

theorem graph_naturality {T : Scheme} (f : T ⟶ B)
    (a : AlgebraicSection L.sheaf) :
    f ≫ graph V a = (V.mapOfSection f (pullSection f a)).val := by
  simpa only [graph, compositionPullback_sections] using
    V.mapOfSection_naturality (𝟙 B) f f (Category.comp_id f)
      (pullSection (𝟙 B) a)

/-- A pullback of two graphs retains the scheme structure of their equality
locus, including its nilpotents on arbitrary test schemes. -/
abbrev locus (a b : AlgebraicSection L.sheaf) : Scheme :=
  pullback (graph V a) (graph V b)

def inclusion (a b : AlgebraicSection L.sheaf) : locus V a b ⟶ B :=
  pullback.fst (graph V a) (graph V b)

theorem first_eq_second (a b : AlgebraicSection L.sheaf) :
    inclusion V a b = pullback.snd (graph V a) (graph V b) := by
  have h := congrArg (fun k : locus V a b ⟶ V.space => k ≫ V.projection)
    (pullback.condition (f := graph V a) (g := graph V b))
  simpa only [Category.assoc, graph_over, Category.comp_id, inclusion] using h

theorem equation (a b : AlgebraicSection L.sheaf) :
    pullSection (inclusion V a b) a = pullSection (inclusion V a b) b := by
  have h := pullback.condition (f := graph V a) (g := graph V b)
  change inclusion V a b ≫ graph V a =
    pullback.snd (graph V a) (graph V b) ≫ graph V b at h
  rw [← first_eq_second V a b, graph_naturality, graph_naturality] at h
  exact V.mapOfSection_injective (inclusion V a b) h

theorem inclusion_closed (a b : AlgebraicSection L.sheaf) :
    IsClosedImmersion (inclusion V a b) := by
  letI : IsClosedImmersion (graph V b) := V.graph_closed b
  dsimp only [inclusion]
  infer_instance

def lift {T : Scheme} (a b : AlgebraicSection L.sheaf) (f : T ⟶ B)
    (h : pullSection f a = pullSection f b) : T ⟶ locus V a b :=
  pullback.lift f f (by rw [graph_naturality, graph_naturality, h])

theorem lift_inclusion {T : Scheme} (a b : AlgebraicSection L.sheaf) (f : T ⟶ B)
    (h : pullSection f a = pullSection f b) :
    lift V a b f h ≫ inclusion V a b = f := by
  simp only [lift, inclusion, pullback.lift_fst]

theorem hom_ext {T : Scheme} (a b : AlgebraicSection L.sheaf)
    {f g : T ⟶ locus V a b}
    (h : f ≫ inclusion V a b = g ≫ inclusion V a b) : f = g := by
  apply pullback.hom_ext
  · exact h
  · simpa only [← first_eq_second V a b] using h

end SectionEquality

/-- The ambient product over the specified complex structure maps. -/
abbrev ParameterLeft : Scheme := pullback affineLineToC P.structureMap

abbrev Ambient : Scheme :=
  pullback (pullback.fst affineLineToC P.structureMap ≫ affineLineToC) P.structureMap

def ambientParameter : Ambient ⟶ AffineLine :=
  pullback.fst _ _ ≫ pullback.fst affineLineToC P.structureMap

def ambientLeft : Ambient ⟶ ProjectiveLine :=
  pullback.fst _ _ ≫ pullback.snd affineLineToC P.structureMap

def ambientRight : Ambient ⟶ ProjectiveLine := pullback.snd _ _

theorem ambientLeft_over :
    ambientLeft ≫ P.structureMap = ambientParameter ≫ affineLineToC := by
  simp only [ambientLeft, ambientParameter, Category.assoc, pullback.condition]

theorem ambientRight_over :
    ambientRight ≫ P.structureMap = ambientParameter ≫ affineLineToC := by
  simpa only [ambientRight, ambientParameter, Category.assoc] using
    (pullback.condition
      (f := pullback.fst affineLineToC P.structureMap ≫ affineLineToC)
      (g := P.structureMap)).symm

def ambientLift {T : Scheme} (t : T ⟶ AffineLine)
    (u v : T ⟶ ProjectiveLine)
    (hu : u ≫ P.structureMap = t ≫ affineLineToC)
    (hv : v ≫ P.structureMap = t ≫ affineLineToC) : T ⟶ Ambient :=
  pullback.lift (pullback.lift t u hu.symm) v (by
    simpa only [pullback.lift_fst_assoc] using hv.symm)

theorem ambientLift_parameter {T : Scheme} (t : T ⟶ AffineLine)
    (u v : T ⟶ ProjectiveLine)
    (hu : u ≫ P.structureMap = t ≫ affineLineToC)
    (hv : v ≫ P.structureMap = t ≫ affineLineToC) :
    ambientLift t u v hu hv ≫ ambientParameter = t := by
  simp only [ambientLift, ambientParameter, pullback.lift_fst_assoc, pullback.lift_fst]

theorem ambientLift_left {T : Scheme} (t : T ⟶ AffineLine)
    (u v : T ⟶ ProjectiveLine)
    (hu : u ≫ P.structureMap = t ≫ affineLineToC)
    (hv : v ≫ P.structureMap = t ≫ affineLineToC) :
    ambientLift t u v hu hv ≫ ambientLeft = u := by
  simp only [ambientLift, ambientLeft, pullback.lift_fst_assoc, pullback.lift_snd]

theorem ambientLift_right {T : Scheme} (t : T ⟶ AffineLine)
    (u v : T ⟶ ProjectiveLine)
    (hu : u ≫ P.structureMap = t ≫ affineLineToC)
    (hv : v ≫ P.structureMap = t ≫ affineLineToC) :
    ambientLift t u v hu hv ≫ ambientRight = v := by
  simp only [ambientLift, ambientRight, pullback.lift_snd]

theorem ambient_hom_ext {T : Scheme} {f g : T ⟶ Ambient}
    (ht : f ≫ ambientParameter = g ≫ ambientParameter)
    (hu : f ≫ ambientLeft = g ≫ ambientLeft)
    (hv : f ≫ ambientRight = g ≫ ambientRight) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [ambientParameter, Category.assoc] using ht
    · simpa only [ambientLeft, Category.assoc] using hu
  · exact hv

def ambientLine : LineBundle Ambient :=
  tensorLine (pullbackLine ambientLeft (projectiveCoordinates 1).hyperplane)
    (pullbackLine ambientRight (projectiveCoordinates 1).hyperplane)

def ambientProduct (i : Fin 2) : AlgebraicSection ambientLine.sheaf :=
  tensorSection (pullSection ambientLeft ((projectiveCoordinates 1).coordinate i))
    (pullSection ambientRight ((projectiveCoordinates 1).coordinate i))

def equationLeft : AlgebraicSection ambientLine.sheaf := ambientProduct 1

def equationRight : AlgebraicSection ambientLine.sheaf :=
  sectionFromValue (ambientParameter.appTop parameterFunction •
    sectionValue (ambientProduct 0))

/-- The canonical comparison from the two pulled-back coordinate lines to
the pullback of their tensor product, with both composition maps fixed. -/
def equationComparison {T : Scheme} (f : T ⟶ Ambient) :
    tensorSheaf
        (pullbackModule (f ≫ ambientLeft) (projectiveCoordinates 1).hyperplane.sheaf)
        (pullbackModule (f ≫ ambientRight) (projectiveCoordinates 1).hyperplane.sheaf) ≅
      pullbackModule f ambientLine.sheaf := by
  letI := tensorPullbackComparison_isIso f
    (pullbackModule ambientLeft (projectiveCoordinates 1).hyperplane.sheaf)
    (pullbackModule ambientRight (projectiveCoordinates 1).hyperplane.sheaf)
  exact (tensorIso
    (compositionPullback f ambientLeft (f ≫ ambientLeft) rfl
      (projectiveCoordinates 1).hyperplane.sheaf)
    (compositionPullback f ambientRight (f ≫ ambientRight) rfl
      (projectiveCoordinates 1).hyperplane.sheaf)).symm ≪≫
    asIso (tensorPullbackComparison f
      (pullbackModule ambientLeft (projectiveCoordinates 1).hyperplane.sheaf)
      (pullbackModule ambientRight (projectiveCoordinates 1).hyperplane.sheaf))

theorem equationComparison_product {T : Scheme} (f : T ⟶ Ambient) (i : Fin 2) :
    tensorSection
        (pullSection (f ≫ ambientLeft) ((projectiveCoordinates 1).coordinate i))
        (pullSection (f ≫ ambientRight) ((projectiveCoordinates 1).coordinate i)) ≫
          (equationComparison f).hom = pullSection f (ambientProduct i) := by
  let e := tensorIso
    (compositionPullback f ambientLeft (f ≫ ambientLeft) rfl
      (projectiveCoordinates 1).hyperplane.sheaf)
    (compositionPullback f ambientRight (f ≫ ambientRight) rfl
      (projectiveCoordinates 1).hyperplane.sheaf)
  have h : tensorSection
        (pullSection f (pullSection ambientLeft ((projectiveCoordinates 1).coordinate i)))
        (pullSection f (pullSection ambientRight ((projectiveCoordinates 1).coordinate i))) ≫
        e.hom = tensorSection
          (pullSection (f ≫ ambientLeft) ((projectiveCoordinates 1).coordinate i))
          (pullSection (f ≫ ambientRight) ((projectiveCoordinates 1).coordinate i)) := by
    change tensorSection _ _ ≫ tensorMap _ _ = _
    rw [tensorSection_map, compositionPullback_sections, compositionPullback_sections]
  rw [← h]
  change (_ ≫ e.hom) ≫ (e.inv ≫ tensorPullbackComparison f _ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact tensorPullbackComparison_onSections f _ _

theorem scalarSection_comp {T : Scheme} {E F : OModule T}
    (a : AlgebraicSection E) (r : RingSections T ⊤) (h : E ⟶ F) :
    sectionFromValue (r • sectionValue a) ≫ h =
      sectionFromValue (r • sectionValue (a ≫ h)) := by
  apply (sectionValue_bijective F).injective
  rw [sectionValue_comp, sectionFromValue_spec, sectionFromValue_spec,
    sectionValue_comp]
  exact Scheme.Modules.Hom.app_smul h r (sectionValue a)

theorem pullSection_scalar {T B : Scheme} (f : T ⟶ B) {E : OModule B}
    (a : AlgebraicSection E) (r : RingSections B ⊤) :
    pullSection f (sectionFromValue (r • sectionValue a)) =
      sectionFromValue (f.appTop r • sectionValue (pullSection f a)) := by
  apply (sectionValue_bijective (pullbackModule f E)).injective
  rw [pullSectionValue_smul, sectionFromValue_spec, sectionFromValue_sectionValue]

/-- The displayed homogeneous conic equation is exactly the pullback of the
ambient section equation, not merely an equality on geometric points. -/
theorem conicEquation_iff {T : Scheme} (f : T ⟶ Ambient) :
    ConicEquation (f ≫ ambientParameter) (f ≫ ambientLeft) (f ≫ ambientRight) ↔
      pullSection f equationLeft = pullSection f equationRight := by
  change (_ = sectionFromValue (_ • sectionValue _)) ↔ _
  rw [← cancel_mono (equationComparison f).hom]
  rw [equationComparison_product, scalarSection_comp, equationComparison_product]
  change pullSection f (ambientProduct 1) =
      sectionFromValue ((f ≫ ambientParameter).appTop parameterFunction •
        sectionValue (pullSection f (ambientProduct 0))) ↔
    pullSection f (ambientProduct 1) =
      pullSection f (sectionFromValue (ambientParameter.appTop parameterFunction •
        sectionValue (ambientProduct 0)))
  rw [pullSection_scalar, Scheme.Hom.comp_appTop]
  rfl

def total : Descent.TotalLine ambientLine :=
  Classical.choice (Descent.totalLine_exists ambientLine)

abbrev source : Scheme := SectionEquality.locus total equationLeft equationRight

def inclusion : source ⟶ Ambient := SectionEquality.inclusion total equationLeft equationRight

def constructed : StandardSource where
  source := source
  parameter := inclusion ≫ ambientParameter
  left := inclusion ≫ ambientLeft
  right := inclusion ≫ ambientRight
  left_over := by rw [Category.assoc, ambientLeft_over, Category.assoc]
  right_over := by rw [Category.assoc, ambientRight_over, Category.assoc]
  equation := (conicEquation_iff inclusion).mpr
    (SectionEquality.equation total equationLeft equationRight)
  universal T sT t u v h := by
    let f := ambientLift t.val u.val v.val
      (u.property.trans t.property.symm) (v.property.trans t.property.symm)
    have ht : f ≫ ambientParameter = t.val := ambientLift_parameter _ _ _ _ _
    have hu : f ≫ ambientLeft = u.val := ambientLift_left _ _ _ _ _
    have hv : f ≫ ambientRight = v.val := ambientLift_right _ _ _ _ _
    have he : pullSection f equationLeft = pullSection f equationRight := by
      apply (conicEquation_iff f).mp
      simpa only [ht, hu, hv] using h
    let g := SectionEquality.lift total equationLeft equationRight f he
    have hg : g ≫ inclusion = f :=
      SectionEquality.lift_inclusion total equationLeft equationRight f he
    refine ⟨g, ?_, ?_⟩
    · exact ⟨by rw [← Category.assoc, hg, ht],
        by rw [← Category.assoc, hg, hu],
        by rw [← Category.assoc, hg, hv]⟩
    · intro k hk
      apply SectionEquality.hom_ext total equationLeft equationRight
      change k ≫ inclusion = g ≫ inclusion
      rw [hg]
      apply ambient_hom_ext
      · exact (Category.assoc _ _ _).trans (hk.1.trans ht.symm)
      · exact (Category.assoc _ _ _).trans (hk.2.1.trans hu.symm)
      · exact (Category.assoc _ _ _).trans (hk.2.2.trans hv.symm)

/-- Any two presentations of the specified functor have the actual unique
morphism preserving all three coordinates. -/
def mapTo (F G : StandardSource) : F.source ⟶ G.source :=
  Classical.choose (G.universal F.source (F.parameter ≫ affineLineToC)
    ⟨F.parameter, rfl⟩ ⟨F.left, F.left_over⟩ ⟨F.right, F.right_over⟩ F.equation)

theorem mapTo_spec (F G : StandardSource) :
    mapTo F G ≫ G.parameter = F.parameter ∧
      mapTo F G ≫ G.left = F.left ∧ mapTo F G ≫ G.right = F.right :=
  (Classical.choose_spec (G.universal F.source (F.parameter ≫ affineLineToC)
    ⟨F.parameter, rfl⟩ ⟨F.left, F.left_over⟩ ⟨F.right, F.right_over⟩ F.equation)).1

theorem mapTo_unique (F G : StandardSource) (h : F.source ⟶ G.source)
    (hh : h ≫ G.parameter = F.parameter ∧
      h ≫ G.left = F.left ∧ h ≫ G.right = F.right) : h = mapTo F G :=
  (Classical.choose_spec (G.universal F.source (F.parameter ≫ affineLineToC)
    ⟨F.parameter, rfl⟩ ⟨F.left, F.left_over⟩ ⟨F.right, F.right_over⟩ F.equation)).2 h hh

theorem mapTo_self (F : StandardSource) : mapTo F F = 𝟙 F.source := by
  symm
  exact mapTo_unique F F _ ⟨Category.id_comp _, Category.id_comp _, Category.id_comp _⟩

theorem mapTo_comp (F G H : StandardSource) : mapTo F G ≫ mapTo G H = mapTo F H := by
  apply mapTo_unique F H
  exact ⟨by rw [Category.assoc, (mapTo_spec G H).1, (mapTo_spec F G).1],
    by rw [Category.assoc, (mapTo_spec G H).2.1, (mapTo_spec F G).2.1],
    by rw [Category.assoc, (mapTo_spec G H).2.2, (mapTo_spec F G).2.2]⟩

def presentationIso (F G : StandardSource) : F.source ≅ G.source where
  hom := mapTo F G
  inv := mapTo G F
  hom_inv_id := by rw [mapTo_comp, mapTo_self]
  inv_hom_id := by rw [mapTo_comp, mapTo_self]

/-- The three specified coordinates determine a morphism into any
presentation of the conic, with no assumption on the test scheme. -/
theorem coordinates_ext (F : StandardSource) {T : Scheme} {f g : T ⟶ F.source}
    (ht : f ≫ F.parameter = g ≫ F.parameter)
    (hu : f ≫ F.left = g ≫ F.left)
    (hv : f ≫ F.right = g ≫ F.right) : f = g := by
  letI : IsIso (mapTo F constructed) := by
    change IsIso (presentationIso F constructed).hom
    infer_instance
  apply (cancel_mono (mapTo F constructed)).mp
  apply SectionEquality.hom_ext total equationLeft equationRight
  apply ambient_hom_ext
  · change ((f ≫ mapTo F constructed) ≫ inclusion) ≫ ambientParameter =
      ((g ≫ mapTo F constructed) ≫ inclusion) ≫ ambientParameter
    simp only [Category.assoc]
    change f ≫ (mapTo F constructed ≫ constructed.parameter) =
      g ≫ (mapTo F constructed ≫ constructed.parameter)
    rw [(mapTo_spec F constructed).1]
    exact ht
  · change ((f ≫ mapTo F constructed) ≫ inclusion) ≫ ambientLeft =
      ((g ≫ mapTo F constructed) ≫ inclusion) ≫ ambientLeft
    simp only [Category.assoc]
    change f ≫ (mapTo F constructed ≫ constructed.left) =
      g ≫ (mapTo F constructed ≫ constructed.left)
    rw [(mapTo_spec F constructed).2.1]
    exact hu
  · change ((f ≫ mapTo F constructed) ≫ inclusion) ≫ ambientRight =
      ((g ≫ mapTo F constructed) ≫ inclusion) ≫ ambientRight
    simp only [Category.assoc]
    change f ≫ (mapTo F constructed ≫ constructed.right) =
      g ≫ (mapTo F constructed ≫ constructed.right)
    rw [(mapTo_spec F constructed).2.2]
    exact hv

theorem ambientParameter_proper : IsProper ambientParameter := by
  letI : IsProper P.structureMap := ProjectiveLineProof.structureMap_proper P
  dsimp only [ambientParameter]
  infer_instance

theorem constructed_proper : IsProper constructed.parameter := by
  letI : IsClosedImmersion inclusion :=
    SectionEquality.inclusion_closed total equationLeft equationRight
  letI : IsProper ambientParameter := ambientParameter_proper
  change IsProper (inclusion ≫ ambientParameter)
  infer_instance

end StandardSourceProof

namespace SourceAffineCharts

open CoordinateCharts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem scalarSection_mul {T : Scheme} (a b : RingSections T ⊤) :
    scalarSection (a * b) = scalarSection a ≫ scalarSection b := by
  apply (sectionValue_bijective _).injective
  simp only [sectionValue_comp, scalarSection, sectionFromValue_spec]
  have h := Scheme.Modules.Hom.app_smul
    (sectionFromValue (E := structureModule T) b) a (1 : RingSections T ⊤)
  change Scheme.Modules.Hom.app (sectionFromValue (E := structureModule T) b) ⊤
      (a * (1 : RingSections T ⊤) : RingSections T ⊤) =
    a • sectionValue (sectionFromValue (E := structureModule T) b) at h
  have ha := congrArg (fun z : RingSections T ⊤ =>
    Scheme.Modules.Hom.app (sectionFromValue (E := structureModule T) b) ⊤ z) (mul_one a)
  exact (ha.symm.trans (h.trans
    (congrArg (fun z : GlobalSections (structureModule T) => a • z)
      (sectionFromValue_spec (E := structureModule T) b)))).symm

theorem scalarSection_isIso {T : Scheme} (a : RingSections T ⊤) (ha : IsUnit a) :
    IsIso (scalarSection a) := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  refine ⟨⟨scalarSection b, ?_, ?_⟩⟩
  · rw [← scalarSection_mul, hb, scalarSection_one]
  · rw [← scalarSection_mul, mul_comm, hb, scalarSection_one]

def coefficient {A : Type} [CommRing A] (i k : Fin 2) (z : A) : A :=
  if k = i then 1 else z

theorem ratioPullFrame_coefficient {T : Scheme} (g : T ⟶ AffineLine) (i k : Fin 2) :
    pullSection (g ≫ (ratioPoint i).val) ((projectiveCoordinates 1).coordinate k) ≫
        (ratioPullFrame g i).hom =
      scalarSection (coefficient i k (g.appTop parameterFunction)) := by
  rw [ratioPullFrame_coordinate]
  by_cases h : k = i <;> simp only [coefficient, h, if_true, if_false, scalarSection_one]

def productFrame {T : Scheme} (u v : T ⟶ AffineLine) (i j : Fin 2) :
    tensorSheaf
      (pullbackModule (u ≫ (ratioPoint i).val) (projectiveCoordinates 1).hyperplane.sheaf)
      (pullbackModule (v ≫ (ratioPoint j).val) (projectiveCoordinates 1).hyperplane.sheaf) ≅
        structureModule T :=
  tensorIso (ratioPullFrame u i) (ratioPullFrame v j) ≪≫
    TensorConstruction.leftUnitIso (structureModule T)

theorem tensorScalarSection {T : Scheme} (a b : RingSections T ⊤) :
    tensorSection (scalarSection a) (scalarSection b) ≫
      (TensorConstruction.leftUnitIso (structureModule T)).hom =
        scalarSection (a * b) := by
  apply (sectionValue_bijective _).injective
  simp only [sectionValue_comp, sectionValue_tensorSection,
    TensorConstruction.leftUnitHom_pair, scalarSection, sectionFromValue_spec]
  exact TensorConstruction.leftUnitHom_pair (structureModule T) ⊤ a b

theorem productFrame_product {T : Scheme} (u v : T ⟶ AffineLine) (i j k : Fin 2) :
    tensorSection
      (pullSection (u ≫ (ratioPoint i).val) ((projectiveCoordinates 1).coordinate k))
      (pullSection (v ≫ (ratioPoint j).val) ((projectiveCoordinates 1).coordinate k)) ≫
        (productFrame u v i j).hom =
      scalarSection (coefficient i k (u.appTop parameterFunction) *
        coefficient j k (v.appTop parameterFunction)) := by
  change tensorSection _ _ ≫
    (tensorMap (ratioPullFrame u i).hom (ratioPullFrame v j).hom ≫
      (TensorConstruction.leftUnitIso (structureModule T)).hom) = _
  rw [← Category.assoc, tensorSection_map, ratioPullFrame_coefficient,
    ratioPullFrame_coefficient, tensorScalarSection]

/-- This is an equality of actual regular functions on every test
scheme, obtained from the two specified quotient-line frames. -/
theorem conicEquation_ratios_iff {T : Scheme} (t u v : T ⟶ AffineLine)
    (i j : Fin 2) :
    ConicEquation t (u ≫ (ratioPoint i).val) (v ≫ (ratioPoint j).val) ↔
      coefficient i 1 (u.appTop parameterFunction) *
        coefficient j 1 (v.appTop parameterFunction) =
      t.appTop parameterFunction * (coefficient i 0 (u.appTop parameterFunction) *
        coefficient j 0 (v.appTop parameterFunction)) := by
  change (_ = sectionFromValue (_ • sectionValue _)) ↔ _
  rw [← cancel_mono (productFrame u v i j).hom,
    productFrame_product, StandardSourceProof.scalarSection_comp,
    productFrame_product]
  constructor
  · intro h
    have hh := congrArg sectionValue h
    simpa only [scalarSection, sectionFromValue_spec, smul_eq_mul] using hh
  · intro h
    apply (sectionValue_bijective _).injective
    simpa only [scalarSection, sectionFromValue_spec, smul_eq_mul] using h

/-- Restrict the actual section equation of the source, retaining the
canonical composition maps for its tensor line. -/
theorem sourceEquation_pullback (F : StandardSource) {T : Scheme} (f : T ⟶ F.source) :
    ConicEquation (f ≫ F.parameter) (f ≫ F.left) (f ≫ F.right) := by
  let a := StandardSourceProof.ambientLift F.parameter F.left F.right
    F.left_over F.right_over
  have ht : a ≫ StandardSourceProof.ambientParameter = F.parameter :=
    StandardSourceProof.ambientLift_parameter _ _ _ _ _
  have hu : a ≫ StandardSourceProof.ambientLeft = F.left :=
    StandardSourceProof.ambientLift_left _ _ _ _ _
  have hv : a ≫ StandardSourceProof.ambientRight = F.right :=
    StandardSourceProof.ambientLift_right _ _ _ _ _
  have he : pullSection a StandardSourceProof.equationLeft =
      pullSection a StandardSourceProof.equationRight := by
    apply (StandardSourceProof.conicEquation_iff a).mp
    simpa only [ht, hu, hv] using F.equation
  have hp := congrArg (fun s => pullSection f s ≫
    (compositionPullback f a (f ≫ a) rfl StandardSourceProof.ambientLine.sheaf).hom) he
  rw [compositionPullback_sections, compositionPullback_sections] at hp
  have h := (StandardSourceProof.conicEquation_iff (f ≫ a)).mpr hp
  simpa only [Category.assoc, ht, hu, hv] using h

def chartOpen (F : StandardSource) (i j : Fin 2) : F.source.Opens :=
  F.left ⁻¹ᵁ ratioOpen i ⊓ F.right ⁻¹ᵁ ratioOpen j

def chartBase (F : StandardSource) (i j : Fin 2) :
    (chartOpen F i j).toScheme ⟶ ComplexBase :=
  (chartOpen F i j).ι ≫ F.parameter ≫ affineLineToC

theorem chart_left_range (F : StandardSource) (i j : Fin 2) :
    Set.range ((chartOpen F i j).ι ≫ F.left) ⊆ (ratioOpen i : Set ProjectiveLine) := by
  rintro _ ⟨x, rfl⟩
  exact x.property.1

theorem chart_right_range (F : StandardSource) (i j : Fin 2) :
    Set.range ((chartOpen F i j).ι ≫ F.right) ⊆ (ratioOpen j : Set ProjectiveLine) := by
  rintro _ ⟨x, rfl⟩
  exact x.property.2

def chartLeftRatio (F : StandardSource) (i j : Fin 2) :
    (chartOpen F i j).toScheme ⟶ AffineLine := by
  letI := ratioPoint_openImmersion i
  exact IsOpenImmersion.lift (ratioPoint i).val ((chartOpen F i j).ι ≫ F.left)
    (by rw [ratioPoint_range]; exact chart_left_range F i j)

def chartRightRatio (F : StandardSource) (i j : Fin 2) :
    (chartOpen F i j).toScheme ⟶ AffineLine := by
  letI := ratioPoint_openImmersion j
  exact IsOpenImmersion.lift (ratioPoint j).val ((chartOpen F i j).ι ≫ F.right)
    (by rw [ratioPoint_range]; exact chart_right_range F i j)

theorem chartLeftRatio_spec (F : StandardSource) (i j : Fin 2) :
    chartLeftRatio F i j ≫ (ratioPoint i).val = (chartOpen F i j).ι ≫ F.left := by
  letI := ratioPoint_openImmersion i
  exact IsOpenImmersion.lift_fac _ _ _

theorem chartRightRatio_spec (F : StandardSource) (i j : Fin 2) :
    chartRightRatio F i j ≫ (ratioPoint j).val = (chartOpen F i j).ι ≫ F.right := by
  letI := ratioPoint_openImmersion j
  exact IsOpenImmersion.lift_fac _ _ _

theorem chartLeftRatio_over (F : StandardSource) (i j : Fin 2) :
    chartLeftRatio F i j ≫ affineLineToC = chartBase F i j := by
  rw [← (ratioPoint i).property, ← Category.assoc, chartLeftRatio_spec,
    Category.assoc, F.left_over]
  rfl

theorem chartRightRatio_over (F : StandardSource) (i j : Fin 2) :
    chartRightRatio F i j ≫ affineLineToC = chartBase F i j := by
  rw [← (ratioPoint j).property, ← Category.assoc, chartRightRatio_spec,
    Category.assoc, F.right_over]
  rfl

theorem chartEquation (F : StandardSource) (i j : Fin 2) :
    coefficient i 1 ((chartLeftRatio F i j).appTop parameterFunction) *
      coefficient j 1 ((chartRightRatio F i j).appTop parameterFunction) =
    ((chartOpen F i j).ι ≫ F.parameter).appTop parameterFunction *
      (coefficient i 0 ((chartLeftRatio F i j).appTop parameterFunction) *
        coefficient j 0 ((chartRightRatio F i j).appTop parameterFunction)) := by
  apply (conicEquation_ratios_iff _ _ _ i j).mp
  rw [chartLeftRatio_spec, chartRightRatio_spec]
  exact sourceEquation_pullback F _

theorem ratioPull_other_isIso {T : Scheme} (g : T ⟶ AffineLine) (i k : Fin 2)
    (hki : k ≠ i) (hg : IsUnit (g.appTop parameterFunction)) :
    IsIso (pullSection (g ≫ (ratioPoint i).val) ((projectiveCoordinates 1).coordinate k)) := by
  have h : pullSection (g ≫ (ratioPoint i).val) ((projectiveCoordinates 1).coordinate k) =
      scalarSection (g.appTop parameterFunction) ≫ (ratioPullFrame g i).inv := by
    apply (cancel_mono (ratioPullFrame g i).hom).mp
    rw [ratioPullFrame_coordinate, if_neg hki, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  letI := scalarSection_isIso _ hg
  rw [h]
  infer_instance

/-- On U1 V1 the actual equation is 1=sab. Thus both missing
coordinates are units; this fourth product chart already lies in U0 V0. -/
theorem chart11_le_chart00 (F : StandardSource) : chartOpen F 1 1 ≤ chartOpen F 0 0 := by
  let u := (chartLeftRatio F 1 1).appTop parameterFunction
  let v := (chartRightRatio F 1 1).appTop parameterFunction
  let t := ((chartOpen F 1 1).ι ≫ F.parameter).appTop parameterFunction
  have h : 1 = t * (u * v) := by simpa [coefficient, t, u, v] using chartEquation F 1 1
  have hu : IsUnit u := isUnit_iff_exists_inv.mpr ⟨t * v, by
    calc u * (t * v) = t * (u * v) := by ring
         _ = 1 := h.symm⟩
  have hv : IsUnit v := isUnit_iff_exists_inv.mpr ⟨t * u, by
    calc v * (t * u) = t * (u * v) := by ring
         _ = 1 := h.symm⟩
  have hl : IsIso (pullSection ((chartOpen F 1 1).ι ≫ F.left)
      ((projectiveCoordinates 1).coordinate 0)) := by
    rw [← chartLeftRatio_spec F 1 1]
    exact ratioPull_other_isIso _ 1 0 (by decide) hu
  have hr : IsIso (pullSection ((chartOpen F 1 1).ι ≫ F.right)
      ((projectiveCoordinates 1).coordinate 0)) := by
    rw [← chartRightRatio_spec F 1 1]
    exact ratioPull_other_isIso _ 1 0 (by decide) hv
  have hleft := (ratioOpen_range_iff 0 _).mpr hl
  have hright := (ratioOpen_range_iff 0 _).mpr hr
  intro x hx
  exact ⟨hleft ⟨⟨x, hx⟩, rfl⟩, hright ⟨⟨x, hx⟩, rfl⟩⟩

def leftIndex (k : Fin 3) : Fin 2 := if k = 1 then 1 else 0
def rightIndex (k : Fin 3) : Fin 2 := if k = 2 then 1 else 0

theorem threeCharts_cover (F : StandardSource) :
    (⨆ k : Fin 3, chartOpen F (leftIndex k) (rightIndex k)) = ⊤ := by
  apply top_unique
  intro x _
  have hu : F.left x ∈ (⨆ i : Fin 2, ratioOpen i) := by
    rw [ratioOpen_cover]
    trivial
  have hv : F.right x ∈ (⨆ i : Fin 2, ratioOpen i) := by
    rw [ratioOpen_cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hu
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hv
  apply TopologicalSpace.Opens.mem_iSup.mpr
  fin_cases i <;> fin_cases j
  · exact ⟨0, ⟨hi, hj⟩⟩
  · exact ⟨2, ⟨hi, hj⟩⟩
  · exact ⟨1, ⟨hi, hj⟩⟩
  · exact ⟨0, chart11_le_chart00 F ⟨hi, hj⟩⟩

abbrev PlaneRing := MvPolynomial (Fin 2) ℂ
abbrev Plane : Scheme := Spec (CommRingCat.of PlaneRing)

def planeBase : Plane ⟶ ComplexBase :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* PlaneRing))

def planeFunction (p : PlaneRing) : RingSections Plane ⊤ :=
  (Scheme.ΓSpecIso (CommRingCat.of PlaneRing)).inv p

def planeFromFunctions {T : Scheme} (sT : T ⟶ ComplexBase)
    (a b : RingSections T ⊤) : T ⟶ Plane :=
  (ΓSpec.adjunction.homEquiv T (Opposite.op (CommRingCat.of PlaneRing)))
    (CommRingCat.ofHom (MvPolynomial.eval₂Hom (complexConstants sT)
      (fun i : Fin 2 => if i = 0 then a else b))).op

theorem planeFromFunctions_apply {T : Scheme} (sT : T ⟶ ComplexBase)
    (a b : RingSections T ⊤) (p : PlaneRing) :
    (planeFromFunctions sT a b).appTop (planeFunction p) =
      MvPolynomial.eval₂ (complexConstants sT) (fun i : Fin 2 => if i = 0 then a else b) p := by
  exact congrArg (fun k : CommRingCat.of PlaneRing ⟶
    T.presheaf.obj (Opposite.op ⊤) => k p)
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (CommRingCat.ofHom (MvPolynomial.eval₂Hom (complexConstants sT)
        (fun i : Fin 2 => if i = 0 then a else b))))

theorem planeFunction_constant (c : ℂ) :
    planeFunction (MvPolynomial.C c) = complexConstants planeBase c := by
  rw [complexConstants_apply_top]
  exact congrArg (fun k : CommRingCat.of ℂ ⟶ Plane.presheaf.obj (Opposite.op ⊤) => k c)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* PlaneRing)))

theorem planeFromFunctions_over {T : Scheme} (sT : T ⟶ ComplexBase)
    (a b : RingSections T ⊤) : planeFromFunctions sT a b ≫ planeBase = sT := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext c
  change (planeFromFunctions sT a b).appTop
      (planeBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
    sT.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  rw [← complexConstants_apply_top, ← planeFunction_constant,
    planeFromFunctions_apply, MvPolynomial.eval₂_C, complexConstants_apply_top]

theorem plane_hom_ext {T : Scheme} (sT : T ⟶ ComplexBase)
    {f g : T ⟶ Plane} (hf : f ≫ planeBase = sT) (hg : g ≫ planeBase = sT)
    (h : ∀ i : Fin 2, f.appTop (planeFunction (MvPolynomial.X i)) =
      g.appTop (planeFunction (MvPolynomial.X i))) : f = g := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change f.appTop (planeFunction (MvPolynomial.C c)) =
      g.appTop (planeFunction (MvPolynomial.C c))
    rw [planeFunction_constant, complexConstants_naturality f sT planeBase hf,
      complexConstants_naturality g sT planeBase hg]
  · exact h

def polynomialLine (p : PlaneRing) : Plane ⟶ AffineLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom MvPolynomial.C p))

theorem polynomialLine_over (p : PlaneRing) : polynomialLine p ≫ affineLineToC = planeBase := by
  change Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom MvPolynomial.C p)) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext c
  simp

theorem polynomialLine_parameter (p : PlaneRing) :
    (polynomialLine p).appTop parameterFunction = planeFunction p := by
  have h := congrArg (fun k : CommRingCat.of (Polynomial ℂ) ⟶
    Plane.presheaf.obj (Opposite.op ⊤) => k Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Polynomial.eval₂RingHom MvPolynomial.C p)))
  change planeFunction ((Polynomial.eval₂RingHom MvPolynomial.C p) Polynomial.X) =
    (polynomialLine p).appTop parameterFunction at h
  simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using h.symm

/-- The node chart uses s=xy; the two outer charts use s=x.
The other projective ratio is then s times the free ratio. -/
def parameterPolynomial (k : Fin 3) : PlaneRing :=
  if k = 0 then MvPolynomial.X 0 * MvPolynomial.X 1 else MvPolynomial.X 0

def leftPolynomial (k : Fin 3) : PlaneRing :=
  if k = 0 then MvPolynomial.X 0 else
    if k = 1 then MvPolynomial.X 1 else MvPolynomial.X 0 * MvPolynomial.X 1

def rightPolynomial (k : Fin 3) : PlaneRing :=
  if k = 1 then MvPolynomial.X 0 * MvPolynomial.X 1 else MvPolynomial.X 1

theorem modelEquation (k : Fin 3) :
    ConicEquation (polynomialLine (parameterPolynomial k))
      (polynomialLine (leftPolynomial k) ≫ (ratioPoint (leftIndex k)).val)
      (polynomialLine (rightPolynomial k) ≫ (ratioPoint (rightIndex k)).val) := by
  apply (conicEquation_ratios_iff _ _ _ _ _).mpr
  rw [polynomialLine_parameter, polynomialLine_parameter, polynomialLine_parameter]
  fin_cases k <;> simp [coefficient, leftIndex, rightIndex, parameterPolynomial,
    leftPolynomial, rightPolynomial, planeFunction, map_mul]

def modelMap (F : StandardSource) (k : Fin 3) : Plane ⟶ F.source :=
  Classical.choose (F.universal Plane planeBase
    ⟨polynomialLine (parameterPolynomial k), polynomialLine_over _⟩
    ⟨polynomialLine (leftPolynomial k) ≫ (ratioPoint (leftIndex k)).val,
      by rw [Category.assoc, (ratioPoint _).property, polynomialLine_over]⟩
    ⟨polynomialLine (rightPolynomial k) ≫ (ratioPoint (rightIndex k)).val,
      by rw [Category.assoc, (ratioPoint _).property, polynomialLine_over]⟩
    (modelEquation k))

theorem modelMap_spec (F : StandardSource) (k : Fin 3) :
    modelMap F k ≫ F.parameter = polynomialLine (parameterPolynomial k) ∧
    modelMap F k ≫ F.left =
      polynomialLine (leftPolynomial k) ≫ (ratioPoint (leftIndex k)).val ∧
    modelMap F k ≫ F.right =
      polynomialLine (rightPolynomial k) ≫ (ratioPoint (rightIndex k)).val :=
  (Classical.choose_spec (F.universal Plane planeBase
    ⟨polynomialLine (parameterPolynomial k), polynomialLine_over _⟩
    ⟨polynomialLine (leftPolynomial k) ≫ (ratioPoint (leftIndex k)).val,
      by rw [Category.assoc, (ratioPoint _).property, polynomialLine_over]⟩
    ⟨polynomialLine (rightPolynomial k) ≫ (ratioPoint (rightIndex k)).val,
      by rw [Category.assoc, (ratioPoint _).property, polynomialLine_over]⟩
    (modelEquation k))).1

theorem modelMap_range (F : StandardSource) (k : Fin 3) :
    Set.range (modelMap F k) ⊆
      (chartOpen F (leftIndex k) (rightIndex k) : Set F.source) := by
  have hl : Set.range (modelMap F k ≫ F.left) ⊆
      (ratioOpen (leftIndex k) : Set ProjectiveLine) := by
    rw [(modelMap_spec F k).2.1, ← ratioPoint_range]
    rintro _ ⟨x, rfl⟩
    exact ⟨polynomialLine (leftPolynomial k) x, rfl⟩
  have hr : Set.range (modelMap F k ≫ F.right) ⊆
      (ratioOpen (rightIndex k) : Set ProjectiveLine) := by
    rw [(modelMap_spec F k).2.2, ← ratioPoint_range]
    rintro _ ⟨x, rfl⟩
    exact ⟨polynomialLine (rightPolynomial k) x, rfl⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨hl ⟨x, rfl⟩, hr ⟨x, rfl⟩⟩

def modelToChart (F : StandardSource) (k : Fin 3) :
    Plane ⟶ (chartOpen F (leftIndex k) (rightIndex k)).toScheme :=
  IsOpenImmersion.lift (chartOpen F (leftIndex k) (rightIndex k)).ι (modelMap F k)
    (by rw [Scheme.Opens.range_ι]; exact modelMap_range F k)

@[reassoc]
theorem modelToChart_inclusion (F : StandardSource) (k : Fin 3) :
    modelToChart F k ≫ (chartOpen F (leftIndex k) (rightIndex k)).ι = modelMap F k :=
  IsOpenImmersion.lift_fac _ _ _

def chartFirstFunction (F : StandardSource) (k : Fin 3) :
    RingSections (chartOpen F (leftIndex k) (rightIndex k)).toScheme ⊤ :=
  if k = 0 then (chartLeftRatio F (leftIndex k) (rightIndex k)).appTop parameterFunction
    else ((chartOpen F (leftIndex k) (rightIndex k)).ι ≫ F.parameter).appTop parameterFunction

def chartSecondFunction (F : StandardSource) (k : Fin 3) :
    RingSections (chartOpen F (leftIndex k) (rightIndex k)).toScheme ⊤ :=
  if k = 1 then (chartLeftRatio F (leftIndex k) (rightIndex k)).appTop parameterFunction
    else (chartRightRatio F (leftIndex k) (rightIndex k)).appTop parameterFunction

def chartToModel (F : StandardSource) (k : Fin 3) :
    (chartOpen F (leftIndex k) (rightIndex k)).toScheme ⟶ Plane :=
  planeFromFunctions (chartBase F (leftIndex k) (rightIndex k))
    (chartFirstFunction F k) (chartSecondFunction F k)

theorem chartToModel_over (F : StandardSource) (k : Fin 3) :
    chartToModel F k ≫ planeBase = chartBase F (leftIndex k) (rightIndex k) :=
  planeFromFunctions_over _ _ _

theorem chartToModel_parameter (F : StandardSource) (k : Fin 3) :
    chartToModel F k ≫ polynomialLine (parameterPolynomial k) =
      (chartOpen F (leftIndex k) (rightIndex k)).ι ≫ F.parameter := by
  apply functionMap_ext (chartBase F (leftIndex k) (rightIndex k))
  · rw [Category.assoc, polynomialLine_over, chartToModel_over]
  · rfl
  rw [Scheme.Hom.comp_appTop]
  change (chartToModel F k).appTop
    ((polynomialLine (parameterPolynomial k)).appTop parameterFunction) = _
  rw [polynomialLine_parameter]
  change (planeFromFunctions _ _ _).appTop (planeFunction _) = _
  rw [planeFromFunctions_apply]
  fin_cases k
  · simpa [parameterPolynomial, chartFirstFunction, chartSecondFunction,
      coefficient, leftIndex, rightIndex] using chartEquation F 0 0
  · simp [parameterPolynomial, chartFirstFunction, chartSecondFunction]
  · simp [parameterPolynomial, chartFirstFunction, chartSecondFunction]

theorem chartToModel_leftRatio (F : StandardSource) (k : Fin 3) :
    chartToModel F k ≫ polynomialLine (leftPolynomial k) =
      chartLeftRatio F (leftIndex k) (rightIndex k) := by
  apply functionMap_ext (chartBase F (leftIndex k) (rightIndex k))
  · rw [Category.assoc, polynomialLine_over, chartToModel_over]
  · exact chartLeftRatio_over _ _ _
  rw [Scheme.Hom.comp_appTop]
  change (chartToModel F k).appTop
    ((polynomialLine (leftPolynomial k)).appTop parameterFunction) = _
  rw [polynomialLine_parameter]
  change (planeFromFunctions _ _ _).appTop (planeFunction _) = _
  rw [planeFromFunctions_apply]
  fin_cases k
  · simp [leftPolynomial, chartFirstFunction, chartSecondFunction]
  · simp [leftPolynomial, chartFirstFunction, chartSecondFunction]
  · simpa [leftPolynomial, chartFirstFunction, chartSecondFunction,
      coefficient, leftIndex, rightIndex] using (chartEquation F 0 1).symm

theorem chartToModel_rightRatio (F : StandardSource) (k : Fin 3) :
    chartToModel F k ≫ polynomialLine (rightPolynomial k) =
      chartRightRatio F (leftIndex k) (rightIndex k) := by
  apply functionMap_ext (chartBase F (leftIndex k) (rightIndex k))
  · rw [Category.assoc, polynomialLine_over, chartToModel_over]
  · exact chartRightRatio_over _ _ _
  rw [Scheme.Hom.comp_appTop]
  change (chartToModel F k).appTop
    ((polynomialLine (rightPolynomial k)).appTop parameterFunction) = _
  rw [polynomialLine_parameter]
  change (planeFromFunctions _ _ _).appTop (planeFunction _) = _
  rw [planeFromFunctions_apply]
  fin_cases k
  · simp [rightPolynomial, chartFirstFunction, chartSecondFunction]
  · simpa [rightPolynomial, chartFirstFunction, chartSecondFunction,
      coefficient, leftIndex, rightIndex] using (chartEquation F 1 0).symm
  · simp [rightPolynomial, chartFirstFunction, chartSecondFunction]

theorem modelToChart_leftRatio (F : StandardSource) (k : Fin 3) :
    modelToChart F k ≫ chartLeftRatio F (leftIndex k) (rightIndex k) =
      polynomialLine (leftPolynomial k) := by
  letI := ratioPoint_mono (leftIndex k)
  apply (cancel_mono (ratioPoint (leftIndex k)).val).mp
  rw [Category.assoc, chartLeftRatio_spec, ← Category.assoc,
    modelToChart_inclusion]
  exact (modelMap_spec F k).2.1

theorem modelToChart_rightRatio (F : StandardSource) (k : Fin 3) :
    modelToChart F k ≫ chartRightRatio F (leftIndex k) (rightIndex k) =
      polynomialLine (rightPolynomial k) := by
  letI := ratioPoint_mono (rightIndex k)
  apply (cancel_mono (ratioPoint (rightIndex k)).val).mp
  rw [Category.assoc, chartRightRatio_spec, ← Category.assoc,
    modelToChart_inclusion]
  exact (modelMap_spec F k).2.2

theorem plane_hom_ext_model (k : Fin 3) {T : Scheme} {f g : T ⟶ Plane}
    (ht : f ≫ polynomialLine (parameterPolynomial k) =
      g ≫ polynomialLine (parameterPolynomial k))
    (hu : f ≫ polynomialLine (leftPolynomial k) =
      g ≫ polynomialLine (leftPolynomial k))
    (hv : f ≫ polynomialLine (rightPolynomial k) =
      g ≫ polynomialLine (rightPolynomial k)) : f = g := by
  have hb : g ≫ planeBase = f ≫ planeBase := by
    simpa only [Category.assoc, polynomialLine_over] using
      (congrArg (fun h => h ≫ affineLineToC) ht).symm
  apply plane_hom_ext (f ≫ planeBase) rfl hb
  have htp := congrArg (fun h => h.appTop parameterFunction) ht
  have hup := congrArg (fun h => h.appTop parameterFunction) hu
  have hvp := congrArg (fun h => h.appTop parameterFunction) hv
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    polynomialLine_parameter] at htp hup hvp
  intro i
  fin_cases k <;> fin_cases i
  · simpa [leftPolynomial] using hup
  · simpa [rightPolynomial] using hvp
  · simpa [parameterPolynomial] using htp
  · simpa [leftPolynomial] using hup
  · simpa [parameterPolynomial] using htp
  · simpa [rightPolynomial] using hvp

/-- An actual affine-plane isomorphism for each member of the three
open cover. Both inverse equations retain all three source coordinates. -/
def chartIso (F : StandardSource) (k : Fin 3) :
    (chartOpen F (leftIndex k) (rightIndex k)).toScheme ≅ Plane where
  hom := chartToModel F k
  inv := modelToChart F k
  hom_inv_id := by
    apply (cancel_mono (chartOpen F (leftIndex k) (rightIndex k)).ι).mp
    rw [Category.assoc, modelToChart_inclusion, Category.id_comp]
    apply StandardSourceProof.coordinates_ext F
    · rw [Category.assoc, (modelMap_spec F k).1, chartToModel_parameter]
    · rw [Category.assoc, (modelMap_spec F k).2.1, ← Category.assoc,
        chartToModel_leftRatio, chartLeftRatio_spec]
    · rw [Category.assoc, (modelMap_spec F k).2.2, ← Category.assoc,
        chartToModel_rightRatio, chartRightRatio_spec]
  inv_hom_id := by
    apply plane_hom_ext_model k
    · rw [Category.assoc, chartToModel_parameter, ← Category.assoc,
        modelToChart_inclusion, (modelMap_spec F k).1, Category.id_comp]
    · rw [Category.assoc, chartToModel_leftRatio, modelToChart_leftRatio,
        Category.id_comp]
    · rw [Category.assoc, chartToModel_rightRatio, modelToChart_rightRatio,
        Category.id_comp]

def parameterRetraction (k : Fin 3) : PlaneRing →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i : Fin 2 =>
    if k = 0 then (if i = 0 then 1 else Polynomial.X)
      else (if i = 0 then Polynomial.X else 0))

theorem parameterRetraction_comp (k : Fin 3) :
    (parameterRetraction k).comp
      (Polynomial.eval₂RingHom MvPolynomial.C (parameterPolynomial k)) =
        RingHom.id (Polynomial ℂ) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp [parameterRetraction]
  · fin_cases k <;> simp [parameterRetraction, parameterPolynomial]

/-- Flatness here is ordinary commutative algebra: the displayed
retraction makes C[s]→C[x,y] injective, hence the domain C[x,y] is
torsion-free over the PID C[s]. Mathlib supplies torsion-free flatness. -/
theorem polynomialParameter_flat (k : Fin 3) :
    Flat (polynomialLine (parameterPolynomial k)) := by
  rw [polynomialLine, Flat.SpecMap_iff]
  let q : Polynomial ℂ →+* PlaneRing :=
    Polynomial.eval₂RingHom MvPolynomial.C (parameterPolynomial k)
  have hq : Function.Injective q := by
    have hleft : Function.LeftInverse (parameterRetraction k) q := by
      intro p
      exact congrArg (fun f : Polynomial ℂ →+* Polynomial ℂ => f p)
        (parameterRetraction_comp k)
    exact hleft.injective
  letI : Algebra (Polynomial ℂ) PlaneRing := q.toAlgebra
  letI : Module.IsTorsionFree (Polynomial ℂ) PlaneRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hq
  change Module.Flat (Polynomial ℂ) PlaneRing
  infer_instance

theorem chart_flat (F : StandardSource) (k : Fin 3) :
    Flat ((chartOpen F (leftIndex k) (rightIndex k)).ι ≫ F.parameter) := by
  letI := polynomialParameter_flat k
  rw [← chartToModel_parameter F k]
  change Flat ((chartIso F k).hom ≫ polynomialLine (parameterPolynomial k))
  infer_instance

theorem parameter_flat (F : StandardSource) : Flat F.parameter :=
  IsZariskiLocalAtSource.of_iSup_eq_top
    (fun k : Fin 3 => chartOpen F (leftIndex k) (rightIndex k))
    (threeCharts_cover F) (chart_flat F)

theorem ratioPoint_zero_marking :
    scalarPoint 0 ≫ (ratioPoint 0).val = marking.map := by
  let v : Fin 2 → ℂ := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa [v] using h0
  let x := Classical.choose
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)
  let q : PointsOver ComplexBase (𝟙 ComplexBase) ProjectiveLine P.structureMap :=
    ⟨scalarPoint 0 ≫ (ratioPoint 0).val, by
      rw [Category.assoc, (ratioPoint 0).property, scalarPoint_overC]⟩
  have hq : (projectiveCoordinates 1).Represents q v := by
    refine ⟨hv, ratioPullFrame (scalarPoint 0) 0, ?_⟩
    intro i
    rw [ratioPullFrame_coordinate, SourceMarksProof.scalarPoint_zero_parameter]
    fin_cases i
    · simpa [v, scalarUnitSection, scalarSection] using
        (scalarSection_one ComplexBase).symm
    · simp [v, scalarUnitSection, scalarSection]
  change q.val = x.val
  exact congrArg Subtype.val ((Classical.choose_spec
    (projectiveCoordinates_pointOfVector (projectiveCoordinates 1) v hv)).2 q hq)

theorem projective_maps_ext {Z : Scheme} {f g : ProjectiveLine ⟶ Z}
    (h : ∀ i : Fin 2, (ratioPoint i).val ≫ f = (ratioPoint i).val ≫ g) : f = g := by
  apply Scheme.hom_ext_of_forall
  intro x
  have hx : x ∈ (⨆ i : Fin 2, ratioOpen i) := by rw [ratioOpen_cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨ratioOpen i, hi, ?_⟩
  apply (cancel_epi (ratioOpenIso i).inv).mp
  change ratioToOpen i ≫ ((ratioOpen i).ι ≫ f) =
    ratioToOpen i ≫ ((ratioOpen i).ι ≫ g)
  rw [← Category.assoc, ← Category.assoc, ratioToOpen_inclusion]
  exact h i

namespace AffineNode

open LeBrunSalamon.PhaseTwentyNine

abbrev NodeRing := NodeAlgebra ℂ 0
abbrev NodeScheme : Scheme := Spec (CommRingCat.of NodeRing)
abbrev EqualizerRing := BranchEqualizer ℂ

def zeroEvaluation : CommRingCat.of (Polynomial ℂ) ⟶ CommRingCat.of ℂ :=
  CommRingCat.ofHom (Polynomial.evalRingHom 0)

def equalizerFirst : CommRingCat.of EqualizerRing ⟶ CommRingCat.of (Polynomial ℂ) :=
  CommRingCat.ofHom ((RingHom.fst (Polynomial ℂ) (Polynomial ℂ)).comp
    (BranchEqualizer ℂ).val.toRingHom)

def equalizerSecond : CommRingCat.of EqualizerRing ⟶ CommRingCat.of (Polynomial ℂ) :=
  CommRingCat.ofHom ((RingHom.snd (Polynomial ℂ) (Polynomial ℂ)).comp
    (BranchEqualizer ℂ).val.toRingHom)

theorem equalizer_condition :
    equalizerFirst ≫ zeroEvaluation = equalizerSecond ≫ zeroEvaluation := by
  apply CommRingCat.hom_ext
  ext a
  exact a.property

def equalizerCone : PullbackCone zeroEvaluation zeroEvaluation :=
  PullbackCone.mk equalizerFirst equalizerSecond equalizer_condition

/-- The already constructed branch equalizer has the actual ring
pullback property. The two polynomial restrictions remain fixed. -/
def equalizerCone_isLimit : IsLimit equalizerCone := by
  refine PullbackCone.IsLimit.mk equalizer_condition (fun s => ?_) ?_ ?_ ?_
  · exact CommRingCat.ofHom ({
      toFun := fun a => ⟨(s.fst a, s.snd a), by
        exact congrArg (fun f : s.pt ⟶ CommRingCat.of ℂ => f a) s.condition⟩
      map_one' := by
        apply Subtype.ext
        exact Prod.ext (map_one s.fst.hom) (map_one s.snd.hom)
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact Prod.ext (map_mul s.fst.hom a b) (map_mul s.snd.hom a b)
      map_zero' := by
        apply Subtype.ext
        exact Prod.ext (map_zero s.fst.hom) (map_zero s.snd.hom)
      map_add' := by
        intro a b
        apply Subtype.ext
        exact Prod.ext (map_add s.fst.hom a b) (map_add s.snd.hom a b) } :
      s.pt →+* EqualizerRing)
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  · intro s m hm₁ hm₂
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply Subtype.ext
    exact Prod.ext
      (congrArg (fun f : s.pt ⟶ CommRingCat.of (Polynomial ℂ) => f a) hm₁)
      (congrArg (fun f : s.pt ⟶ CommRingCat.of (Polynomial ℂ) => f a) hm₂)

def equalizerPullbackIso :
    CommRingCat.of EqualizerRing ≅ pullback zeroEvaluation zeroEvaluation :=
  equalizerCone_isLimit.conePointUniqueUpToIso (pullback.isLimit _ _)

theorem equalizerPullbackIso_first :
    equalizerPullbackIso.hom ≫ pullback.fst zeroEvaluation zeroEvaluation =
      equalizerFirst :=
  IsLimit.conePointUniqueUpToIso_hom_comp equalizerCone_isLimit
    (pullback.isLimit _ _) WalkingCospan.left

theorem equalizerPullbackIso_second :
    equalizerPullbackIso.hom ≫ pullback.snd zeroEvaluation zeroEvaluation =
      equalizerSecond :=
  IsLimit.conePointUniqueUpToIso_hom_comp equalizerCone_isLimit
    (pullback.isLimit _ _) WalkingCospan.right

def normalizationRingIso : CommRingCat.of NodeRing ≅ CommRingCat.of EqualizerRing :=
  (NodeAlgebraProof.normalizationEquiv ℂ).toRingEquiv.toCommRingCatIso

def nodeFirst : CommRingCat.of NodeRing ⟶ CommRingCat.of (Polynomial ℂ) :=
  normalizationRingIso.hom ≫ equalizerFirst

def nodeSecond : CommRingCat.of NodeRing ⟶ CommRingCat.of (Polynomial ℂ) :=
  normalizationRingIso.hom ≫ equalizerSecond

theorem nodeFirst_u : nodeFirst (nodeU ℂ 0) = Polynomial.X := by
  change (NodeAlgebraProof.nodeToEqualizer ℂ (nodeU ℂ 0)).val.1 = _
  rw [NodeAlgebraProof.nodeToEqualizer_nodeU]
  rfl

theorem nodeFirst_v : nodeFirst (nodeV ℂ 0) = 0 := by
  change (NodeAlgebraProof.nodeToEqualizer ℂ (nodeV ℂ 0)).val.1 = _
  rw [NodeAlgebraProof.nodeToEqualizer_nodeV]
  rfl

theorem nodeSecond_u : nodeSecond (nodeU ℂ 0) = 0 := by
  change (NodeAlgebraProof.nodeToEqualizer ℂ (nodeU ℂ 0)).val.2 = _
  rw [NodeAlgebraProof.nodeToEqualizer_nodeU]
  rfl

theorem nodeSecond_v : nodeSecond (nodeV ℂ 0) = Polynomial.X := by
  change (NodeAlgebraProof.nodeToEqualizer ℂ (nodeV ℂ 0)).val.2 = _
  rw [NodeAlgebraProof.nodeToEqualizer_nodeV]
  rfl

theorem nodeFirst_constant (c : ℂ) : nodeFirst (algebraMap ℂ NodeRing c) = Polynomial.C c := by
  change (NodeAlgebraProof.nodeToEqualizer ℂ (algebraMap ℂ NodeRing c)).val.1 = _
  rw [AlgHom.commutes]
  rfl

theorem nodeSecond_constant (c : ℂ) : nodeSecond (algebraMap ℂ NodeRing c) = Polynomial.C c := by
  change (NodeAlgebraProof.nodeToEqualizer ℂ (algebraMap ℂ NodeRing c)).val.2 = _
  rw [AlgHom.commutes]
  rfl

def nodePullbackIso : CommRingCat.of NodeRing ≅ pullback zeroEvaluation zeroEvaluation :=
  normalizationRingIso ≪≫ equalizerPullbackIso

theorem nodePullbackIso_first :
    nodePullbackIso.hom ≫ pullback.fst zeroEvaluation zeroEvaluation = nodeFirst := by
  rw [nodePullbackIso, Iso.trans_hom, Category.assoc, equalizerPullbackIso_first]
  rfl

theorem nodePullbackIso_second :
    nodePullbackIso.hom ≫ pullback.snd zeroEvaluation zeroEvaluation = nodeSecond := by
  rw [nodePullbackIso, Iso.trans_hom, Category.assoc, equalizerPullbackIso_second]
  rfl

/-- Affine node gluing with the actual two branch restrictions, obtained
from the ordinary normalized algebra and the reviewed generic affine
pushout theorem. No central-projective-fibre identification is assumed. -/
theorem isPushout :
    IsPushout (scalarPoint 0) (scalarPoint 0)
      (Spec.map nodeFirst) (Spec.map nodeSecond) := by
  have hs : Function.Surjective zeroEvaluation.hom := by
    intro c
    exact ⟨Polynomial.C c, by simp [zeroEvaluation]⟩
  have h := CoordinateCharts.StandardInputs.spec_pullback_isPushout
    zeroEvaluation zeroEvaluation hs
  apply h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Scheme.Spec.mapIso nodePullbackIso.op)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · change Spec.map (pullback.fst zeroEvaluation zeroEvaluation) ≫
      Spec.map nodePullbackIso.hom = 𝟙 AffineLine ≫ Spec.map nodeFirst
    rw [← Spec.map_comp, nodePullbackIso_first, Category.id_comp]
  · change Spec.map (pullback.snd zeroEvaluation zeroEvaluation) ≫
      Spec.map nodePullbackIso.hom = 𝟙 AffineLine ≫ Spec.map nodeSecond
    rw [← Spec.map_comp, nodePullbackIso_second, Category.id_comp]

theorem glue {Z : Scheme} (f g : AffineLine ⟶ Z)
    (h : scalarPoint 0 ≫ f = scalarPoint 0 ≫ g) :
    ∃! k : NodeScheme ⟶ Z, Spec.map nodeFirst ≫ k = f ∧ Spec.map nodeSecond ≫ k = g := by
  refine ⟨isPushout.desc f g h, ⟨isPushout.inl_desc _ _ _, isPushout.inr_desc _ _ _⟩, ?_⟩
  intro k hk
  apply isPushout.hom_ext
  · exact hk.1.trans (isPushout.inl_desc _ _ _).symm
  · exact hk.2.trans (isPushout.inr_desc _ _ _).symm

def planeQuotient : CommRingCat.of PlaneRing ⟶ CommRingCat.of NodeRing :=
  CommRingCat.ofHom (Ideal.Quotient.mk (nodeIdeal ℂ 0))

def nodeConstants : CommRingCat.of ℂ ⟶ CommRingCat.of NodeRing :=
  CommRingCat.ofHom (algebraMap ℂ NodeRing)

def nodeParameter : CommRingCat.of (Polynomial ℂ) ⟶ CommRingCat.of PlaneRing :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom MvPolynomial.C
    (MvPolynomial.X 0 * MvPolynomial.X 1))

/-- Setting the actual parameter xy equal to zero produces precisely
the previously defined node quotient, with its actual quotient map. -/
theorem nodeFibre_ringPushout :
    IsPushout nodeParameter zeroEvaluation planeQuotient nodeConstants := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro c
      change Ideal.Quotient.mk (nodeIdeal ℂ 0)
          (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 * MvPolynomial.X 1)
            (Polynomial.C c)) =
        algebraMap ℂ NodeRing (Polynomial.eval 0 (Polynomial.C c))
      rw [Polynomial.eval₂_C, Polynomial.eval_C]
      exact Ideal.Quotient.mk_algebraMap ℂ (nodeIdeal ℂ 0) c
    · change Ideal.Quotient.mk (nodeIdeal ℂ 0)
          (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 * MvPolynomial.X 1)
            Polynomial.X) =
        algebraMap ℂ NodeRing (Polynomial.eval 0 Polynomial.X)
      rw [Polynomial.eval₂_X, Polynomial.eval_X, map_mul]
      exact NodeAlgebraProof.node_relation ℂ 0
  · intro T f g h _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun h : CommRingCat.of PlaneRing ⟶ T => h p) h
  · intro T a b h
    have hxy : a (MvPolynomial.X 0 * MvPolynomial.X 1) = 0 := by
      have hx := congrArg (fun h : CommRingCat.of (Polynomial ℂ) ⟶ T => h Polynomial.X) h
      simpa [nodeParameter, zeroEvaluation] using hx
    have hC (c : ℂ) : a (MvPolynomial.C c) = b c := by
      have hc := congrArg (fun h : CommRingCat.of (Polynomial ℂ) ⟶ T => h (Polynomial.C c)) h
      simpa [nodeParameter, zeroEvaluation] using hc
    have hk : nodeIdeal ℂ 0 ≤ RingHom.ker a.hom := by
      apply Ideal.span_le.mpr
      intro p hp
      have hp' : p = nodeEquation ℂ 0 := Set.mem_singleton_iff.mp hp
      subst p
      apply RingHom.mem_ker.mpr
      simpa [nodeEquation] using hxy
    let l : CommRingCat.of NodeRing ⟶ T :=
      CommRingCat.ofHom (Ideal.Quotient.lift (nodeIdeal ℂ 0) a.hom hk)
    refine ⟨l, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro p
      rfl
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro c
      exact hC c

theorem nodeFibre_isPullback :
    IsPullback (Spec.map planeQuotient) (Spec.map nodeConstants)
      (polynomialLine (parameterPolynomial 0)) (scalarPoint 0) := by
  exact isPullback_SpecMap_of_isPushout nodeParameter zeroEvaluation
    planeQuotient nodeConstants nodeFibre_ringPushout

def nodeFibreIso :
    NodeScheme ≅ pullback (polynomialLine (parameterPolynomial 0)) (scalarPoint 0) :=
  nodeFibre_isPullback.isoPullback

@[reassoc]
theorem nodeFibreIso_first :
    nodeFibreIso.hom ≫ pullback.fst (polynomialLine (parameterPolynomial 0)) (scalarPoint 0) =
      Spec.map planeQuotient := nodeFibre_isPullback.isoPullback_hom_fst

@[reassoc]
theorem nodeFibreIso_second :
    nodeFibreIso.hom ≫ pullback.snd (polynomialLine (parameterPolynomial 0)) (scalarPoint 0) =
      Spec.map nodeConstants := nodeFibre_isPullback.isoPullback_hom_snd

def coordinateParameter : CommRingCat.of (Polynomial ℂ) ⟶ CommRingCat.of PlaneRing :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))

def outerQuotient : CommRingCat.of PlaneRing ⟶ CommRingCat.of (Polynomial ℂ) :=
  CommRingCat.ofHom (MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => if i = 0 then 0 else Polynomial.X))

def polynomialConstants : CommRingCat.of ℂ ⟶ CommRingCat.of (Polynomial ℂ) :=
  CommRingCat.ofHom Polynomial.C

/-- The two outer charts have parameter x, so their zero fibres are
the actual affine line with coordinate y. -/
theorem outerFibre_ringPushout :
    IsPushout coordinateParameter zeroEvaluation outerQuotient polynomialConstants := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro c
      simp [coordinateParameter, zeroEvaluation, outerQuotient, polynomialConstants]
    · simp [coordinateParameter, zeroEvaluation, outerQuotient, polynomialConstants]
  · intro T f g hq hc
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro c
      exact congrArg (fun h : CommRingCat.of ℂ ⟶ T => h c) hc
    · have h := congrArg (fun h : CommRingCat.of PlaneRing ⟶ T => h (MvPolynomial.X 1)) hq
      simpa [outerQuotient] using h
  · intro T a b h
    have h0 : a (MvPolynomial.X 0) = 0 := by
      have hx := congrArg (fun h : CommRingCat.of (Polynomial ℂ) ⟶ T => h Polynomial.X) h
      simpa [coordinateParameter, zeroEvaluation] using hx
    have hC (c : ℂ) : a (MvPolynomial.C c) = b c := by
      have hc := congrArg (fun h : CommRingCat.of (Polynomial ℂ) ⟶ T => h (Polynomial.C c)) h
      simpa [coordinateParameter, zeroEvaluation] using hc
    let l : CommRingCat.of (Polynomial ℂ) ⟶ T :=
      CommRingCat.ofHom (Polynomial.eval₂RingHom b.hom (a (MvPolynomial.X 1)))
    refine ⟨l, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply MvPolynomial.ringHom_ext
      · intro c
        simpa [outerQuotient, l] using (hC c).symm
      · intro i
        fin_cases i
        · simpa [outerQuotient, l] using h0.symm
        · simp [outerQuotient, l]
    · apply CommRingCat.hom_ext
      ext c
      simp [polynomialConstants, l]

theorem outerFibre_isPullback :
    IsPullback (Spec.map outerQuotient) affineLineToC
      (polynomialLine (MvPolynomial.X 0)) (scalarPoint 0) :=
  isPullback_SpecMap_of_isPushout coordinateParameter zeroEvaluation
    outerQuotient polynomialConstants outerFibre_ringPushout

def outerFibreIso :
    AffineLine ≅ pullback (polynomialLine (MvPolynomial.X 0)) (scalarPoint 0) :=
  outerFibre_isPullback.isoPullback

@[reassoc]
theorem outerFibreIso_first :
    outerFibreIso.hom ≫ pullback.fst (polynomialLine (MvPolynomial.X 0)) (scalarPoint 0) =
      Spec.map outerQuotient := outerFibre_isPullback.isoPullback_hom_fst

@[reassoc]
theorem outerFibreIso_second :
    outerFibreIso.hom ≫ pullback.snd (polynomialLine (MvPolynomial.X 0)) (scalarPoint 0) =
      affineLineToC := outerFibre_isPullback.isoPullback_hom_snd

theorem first_base : Spec.map nodeFirst ≫ Spec.map nodeConstants = affineLineToC := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact nodeFirst_constant c

theorem second_base : Spec.map nodeSecond ≫ Spec.map nodeConstants = affineLineToC := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact nodeSecond_constant c

theorem first_plane_x :
    Spec.map nodeFirst ≫ Spec.map planeQuotient ≫ polynomialLine (MvPolynomial.X 0) =
      𝟙 AffineLine := by
  rw [polynomialLine, ← Spec.map_comp, ← Spec.map_comp]
  rw [← Spec.map_id (CommRingCat.of (Polynomial ℂ))]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change nodeFirst (Ideal.Quotient.mk (nodeIdeal ℂ 0)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (Polynomial.C c))) =
      Polynomial.C c
    rw [Polynomial.eval₂_C]
    exact (congrArg (fun z : NodeRing => nodeFirst z)
      (Ideal.Quotient.mk_algebraMap ℂ (nodeIdeal ℂ 0) c)).trans (nodeFirst_constant c)
  · change nodeFirst (Ideal.Quotient.mk (nodeIdeal ℂ 0)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) Polynomial.X)) =
      Polynomial.X
    rw [Polynomial.eval₂_X]
    exact nodeFirst_u

theorem first_plane_y :
    Spec.map nodeFirst ≫ Spec.map planeQuotient ≫ polynomialLine (MvPolynomial.X 1) =
      affineLineToC ≫ scalarPoint 0 := by
  rw [polynomialLine, affineLineToC, scalarPoint, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change nodeFirst (Ideal.Quotient.mk (nodeIdeal ℂ 0)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 1) (Polynomial.C c))) =
      Polynomial.C (Polynomial.eval 0 (Polynomial.C c))
    rw [Polynomial.eval₂_C, Polynomial.eval_C]
    exact (congrArg (fun z : NodeRing => nodeFirst z)
      (Ideal.Quotient.mk_algebraMap ℂ (nodeIdeal ℂ 0) c)).trans (nodeFirst_constant c)
  · change nodeFirst (Ideal.Quotient.mk (nodeIdeal ℂ 0)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 1) Polynomial.X)) =
      Polynomial.C (Polynomial.eval 0 Polynomial.X)
    rw [Polynomial.eval₂_X, Polynomial.eval_X, map_zero]
    exact nodeFirst_v

theorem second_plane_x :
    Spec.map nodeSecond ≫ Spec.map planeQuotient ≫ polynomialLine (MvPolynomial.X 0) =
      affineLineToC ≫ scalarPoint 0 := by
  rw [polynomialLine, affineLineToC, scalarPoint, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change nodeSecond (Ideal.Quotient.mk (nodeIdeal ℂ 0)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (Polynomial.C c))) =
      Polynomial.C (Polynomial.eval 0 (Polynomial.C c))
    rw [Polynomial.eval₂_C, Polynomial.eval_C]
    exact (congrArg (fun z : NodeRing => nodeSecond z)
      (Ideal.Quotient.mk_algebraMap ℂ (nodeIdeal ℂ 0) c)).trans (nodeSecond_constant c)
  · change nodeSecond (Ideal.Quotient.mk (nodeIdeal ℂ 0)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) Polynomial.X)) =
      Polynomial.C (Polynomial.eval 0 Polynomial.X)
    rw [Polynomial.eval₂_X, Polynomial.eval_X, map_zero]
    exact nodeSecond_u

theorem second_plane_y :
    Spec.map nodeSecond ≫ Spec.map planeQuotient ≫ polynomialLine (MvPolynomial.X 1) =
      𝟙 AffineLine := by
  rw [polynomialLine, ← Spec.map_comp, ← Spec.map_comp]
  rw [← Spec.map_id (CommRingCat.of (Polynomial ℂ))]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change nodeSecond (Ideal.Quotient.mk (nodeIdeal ℂ 0)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 1) (Polynomial.C c))) =
      Polynomial.C c
    rw [Polynomial.eval₂_C]
    exact (congrArg (fun z : NodeRing => nodeSecond z)
      (Ideal.Quotient.mk_algebraMap ℂ (nodeIdeal ℂ 0) c)).trans (nodeSecond_constant c)
  · change nodeSecond (Ideal.Quotient.mk (nodeIdeal ℂ 0)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 1) Polynomial.X)) =
      Polynomial.X
    rw [Polynomial.eval₂_X]
    exact nodeSecond_v

theorem outer_plane_y :
    Spec.map outerQuotient ≫ polynomialLine (MvPolynomial.X 1) = 𝟙 AffineLine := by
  rw [polynomialLine, ← Spec.map_comp, ← Spec.map_id (CommRingCat.of (Polynomial ℂ))]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp [outerQuotient]
  · simp [outerQuotient]

theorem outer_plane_xy :
    Spec.map outerQuotient ≫ polynomialLine (MvPolynomial.X 0 * MvPolynomial.X 1) =
      affineLineToC ≫ scalarPoint 0 := by
  rw [polynomialLine, affineLineToC, scalarPoint, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp [outerQuotient]
  · simp [outerQuotient]

end AffineNode

end SourceAffineCharts

namespace PuncturedSourceProof

open CoordinateCharts SourceAffineCharts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The usual reciprocal change of ratio is proved for the specified
quotient coordinates, on arbitrary test schemes. -/
theorem reciprocal_ratios {T : Scheme} (sT : T ⟶ ComplexBase)
    (a b : T ⟶ AffineLine) (ha : a ≫ affineLineToC = sT)
    (hb : b ≫ affineLineToC = sT)
    (hab : a.appTop parameterFunction * b.appTop parameterFunction = 1) :
    a ≫ (ratioPoint 1).val = b ≫ (ratioPoint 0).val := by
  let av := a.appTop parameterFunction
  letI := scalarSection_isIso av (isUnit_iff_exists_inv.mpr ⟨b.appTop parameterFunction, hab⟩)
  let p : PointsOver T sT ProjectiveLine P.structureMap :=
    ⟨a ≫ (ratioPoint 1).val, by rw [Category.assoc, (ratioPoint 1).property, ha]⟩
  let q : PointsOver T sT ProjectiveLine P.structureMap :=
    ⟨b ≫ (ratioPoint 0).val, by rw [Category.assoc, (ratioPoint 0).property, hb]⟩
  have h : p = q := by
    apply coordinate_ext_of_frames (projectiveCoordinates 1) p q (ratioPullFrame a 1)
      (ratioPullFrame b 0 ≪≫ asIso (scalarSection av))
    intro i
    change pullSection (a ≫ (ratioPoint 1).val) ((projectiveCoordinates 1).coordinate i) ≫
      (ratioPullFrame a 1).hom =
      (pullSection (b ≫ (ratioPoint 0).val) ((projectiveCoordinates 1).coordinate i) ≫
        (ratioPullFrame b 0).hom) ≫ scalarSection av
    rw [ratioPullFrame_coordinate, ratioPullFrame_coordinate]
    fin_cases i
    · simp [av]
    · have hscalar : (𝟙 (structureModule T)) =
          scalarSection (b.appTop parameterFunction) ≫
            scalarSection (a.appTop parameterFunction) := by
        rw [← scalarSection_mul, mul_comm, hab, scalarSection_one]
      simpa [av] using hscalar
  exact congrArg Subtype.val h

def solutionFunction {T : Scheme} (t u : T ⟶ AffineLine)
    (z : RingSections T ⊤) (i : Fin 2) : RingSections T ⊤ :=
  if i = 0 then u.appTop parameterFunction * z
    else t.appTop parameterFunction * u.appTop parameterFunction

def solutionRatio {T : Scheme} (sT : T ⟶ ComplexBase) (t u : T ⟶ AffineLine)
    (z : RingSections T ⊤) (i : Fin 2) : T ⟶ AffineLine :=
  fromFunction sT (solutionFunction t u z i)

theorem solution_equation {T : Scheme} (sT : T ⟶ ComplexBase)
    (t u : T ⟶ AffineLine) (z : RingSections T ⊤)
    (hz : t.appTop parameterFunction * z = 1) (i : Fin 2) :
    ConicEquation t (u ≫ (ratioPoint i).val)
      (solutionRatio sT t u z i ≫ (ratioPoint (other i)).val) := by
  apply (conicEquation_ratios_iff _ _ _ _ _).mpr
  rw [solutionRatio, fromFunction_parameter]
  fin_cases i
  · have hzero : u.appTop parameterFunction =
        t.appTop parameterFunction * (u.appTop parameterFunction * z) := by
      calc
        u.appTop parameterFunction = u.appTop parameterFunction *
            (t.appTop parameterFunction * z) := by rw [hz, mul_one]
        _ = t.appTop parameterFunction * (u.appTop parameterFunction * z) := by ring
    simpa [coefficient, other, solutionFunction] using hzero
  · simp [coefficient, other, solutionFunction]

/-- Every solution in a pair of ratio charts has the displayed inverse
formula. The four cases are regular-function identities, including
nilpotent coefficients. -/
theorem solution_unique {T : Scheme} (sT : T ⟶ ComplexBase)
    (t u v : T ⟶ AffineLine) (hv : v ≫ affineLineToC = sT)
    (z : RingSections T ⊤) (hz : t.appTop parameterFunction * z = 1)
    (i j : Fin 2)
    (he : ConicEquation t (u ≫ (ratioPoint i).val) (v ≫ (ratioPoint j).val)) :
    v ≫ (ratioPoint j).val =
      solutionRatio sT t u z i ≫ (ratioPoint (other i)).val := by
  have h := (conicEquation_ratios_iff t u v i j).mp he
  have hs (k : Fin 2) : solutionRatio sT t u z k ≫ affineLineToC = sT :=
    fromFunction_over _ _
  have hp (k : Fin 2) : (solutionRatio sT t u z k).appTop parameterFunction =
      solutionFunction t u z k := fromFunction_parameter _ _
  fin_cases i <;> fin_cases j
  · have huv : u.appTop parameterFunction * v.appTop parameterFunction =
        t.appTop parameterFunction := by simpa [coefficient] using h
    apply (reciprocal_ratios sT (solutionRatio sT t u z 0) v (hs 0) hv ?_).symm
    rw [hp]
    simp only [solutionFunction, if_pos rfl]
    calc
      (u.appTop parameterFunction * z) * v.appTop parameterFunction =
          (u.appTop parameterFunction * v.appTop parameterFunction) * z := by ring
      _ = 1 := by rw [huv, hz]
  · have huv : u.appTop parameterFunction =
        t.appTop parameterFunction * v.appTop parameterFunction := by
      simpa [coefficient] using h
    have hvs : v = solutionRatio sT t u z 0 := by
      apply functionMap_ext sT hv (hs 0)
      rw [hp]
      simp only [solutionFunction, if_pos rfl]
      calc
        v.appTop parameterFunction = v.appTop parameterFunction *
            (t.appTop parameterFunction * z) := by rw [hz, mul_one]
        _ = (t.appTop parameterFunction * v.appTop parameterFunction) * z := by ring
        _ = u.appTop parameterFunction * z := by rw [← huv]
    simpa [other] using congrArg (fun a => a ≫ (ratioPoint 1).val) hvs
  · have huv : v.appTop parameterFunction =
        t.appTop parameterFunction * u.appTop parameterFunction := by
      simpa [coefficient] using h
    have hvs : v = solutionRatio sT t u z 1 := by
      apply functionMap_ext sT hv (hs 1)
      rw [hp]
      simpa [solutionFunction] using huv
    simpa [other] using congrArg (fun a => a ≫ (ratioPoint 0).val) hvs
  · have huv : 1 = t.appTop parameterFunction *
        (u.appTop parameterFunction * v.appTop parameterFunction) := by
      simpa [coefficient] using h
    apply reciprocal_ratios sT v (solutionRatio sT t u z 1) hv (hs 1)
    rw [hp]
    simp only [solutionFunction, show (1 : Fin 2) ≠ 0 by decide, if_neg]
    calc
      v.appTop parameterFunction *
          (t.appTop parameterFunction * u.appTop parameterFunction) =
        t.appTop parameterFunction *
          (u.appTop parameterFunction * v.appTop parameterFunction) := by ring
      _ = 1 := huv.symm

def liftRatio {T : Scheme} (f : T ⟶ ProjectiveLine) (i : Fin 2)
    (hf : Set.range f ⊆ (ratioOpen i : Set ProjectiveLine)) : T ⟶ AffineLine := by
  letI := ratioPoint_openImmersion i
  exact IsOpenImmersion.lift (ratioPoint i).val f (by rw [ratioPoint_range]; exact hf)

theorem liftRatio_spec {T : Scheme} (f : T ⟶ ProjectiveLine) (i : Fin 2)
    (hf : Set.range f ⊆ (ratioOpen i : Set ProjectiveLine)) :
    liftRatio f i hf ≫ (ratioPoint i).val = f := by
  letI := ratioPoint_openImmersion i
  exact IsOpenImmersion.lift_fac _ _ _

theorem liftRatio_over {T : Scheme} (sT : T ⟶ ComplexBase)
    (f : T ⟶ ProjectiveLine) (hC : f ≫ P.structureMap = sT)
    (i : Fin 2) (hf : Set.range f ⊆ (ratioOpen i : Set ProjectiveLine)) :
    liftRatio f i hf ≫ affineLineToC = sT := by
  rw [← (ratioPoint i).property, ← Category.assoc, liftRatio_spec, hC]

/-- Over a unit parameter, the actual parameter and first projective
coordinate determine the entire conic map on every test scheme. -/
theorem parameter_left_ext (F : StandardSource) {T : Scheme} {f g : T ⟶ F.source}
    (ht : f ≫ F.parameter = g ≫ F.parameter)
    (hu : f ≫ F.left = g ≫ F.left)
    (hz : IsUnit ((f ≫ F.parameter).appTop parameterFunction)) : f = g := by
  apply StandardSourceProof.coordinates_ext F ht hu
  apply Scheme.hom_ext_of_forall
  intro x
  have cover (p : ProjectiveLine) : ∃ i : Fin 2, p ∈ ratioOpen i := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [ratioOpen_cover]
    trivial
  obtain ⟨i, hi⟩ := cover ((f ≫ F.left) x)
  obtain ⟨j, hj⟩ := cover ((f ≫ F.right) x)
  obtain ⟨k, hk⟩ := cover ((g ≫ F.right) x)
  let W : T.Opens := (f ≫ F.left) ⁻¹ᵁ ratioOpen i ⊓
    (f ≫ F.right) ⁻¹ᵁ ratioOpen j ⊓ (g ≫ F.right) ⁻¹ᵁ ratioOpen k
  refine ⟨W, ⟨⟨hi, hj⟩, hk⟩, ?_⟩
  let t : W.toScheme ⟶ AffineLine := W.ι ≫ f ≫ F.parameter
  let s : W.toScheme ⟶ ComplexBase := t ≫ affineLineToC
  have hleft : Set.range (W.ι ≫ f ≫ F.left) ⊆ (ratioOpen i : Set ProjectiveLine) := by
    rintro _ ⟨y, rfl⟩
    exact y.property.1.1
  have hright : Set.range (W.ι ≫ f ≫ F.right) ⊆ (ratioOpen j : Set ProjectiveLine) := by
    rintro _ ⟨y, rfl⟩
    exact y.property.1.2
  have hright' : Set.range (W.ι ≫ g ≫ F.right) ⊆ (ratioOpen k : Set ProjectiveLine) := by
    rintro _ ⟨y, rfl⟩
    exact y.property.2
  let a := liftRatio (W.ι ≫ f ≫ F.left) i hleft
  let b := liftRatio (W.ι ≫ f ≫ F.right) j hright
  let c := liftRatio (W.ι ≫ g ≫ F.right) k hright'
  have ha := liftRatio_spec (W.ι ≫ f ≫ F.left) i hleft
  have hb := liftRatio_spec (W.ι ≫ f ≫ F.right) j hright
  have hc := liftRatio_spec (W.ι ≫ g ≫ F.right) k hright'
  have hbC : b ≫ affineLineToC = s := by
    apply liftRatio_over
    simp only [Category.assoc, F.right_over]
    rfl
  have hcC : c ≫ affineLineToC = s := by
    apply liftRatio_over
    calc
      (W.ι ≫ g ≫ F.right) ≫ P.structureMap =
          W.ι ≫ (g ≫ F.parameter) ≫ affineLineToC := by
            simp only [Category.assoc, F.right_over]
      _ = W.ι ≫ (f ≫ F.parameter) ≫ affineLineToC := by rw [← ht]
      _ = s := rfl
  have htz : IsUnit (t.appTop parameterFunction) := by
    simpa only [t, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hz.map W.ι.appTop.hom
  obtain ⟨z, hzz⟩ := isUnit_iff_exists_inv.mp htz
  have he : ConicEquation t (a ≫ (ratioPoint i).val) (b ≫ (ratioPoint j).val) := by
    rw [ha, hb]
    simpa only [t, Category.assoc] using sourceEquation_pullback F (W.ι ≫ f)
  have he' : ConicEquation t (a ≫ (ratioPoint i).val) (c ≫ (ratioPoint k).val) := by
    rw [ha, hc]
    simpa only [t, Category.assoc, ← ht, ← hu] using sourceEquation_pullback F (W.ι ≫ g)
  have h₁ := solution_unique s t a b hbC z hzz i j he
  have h₂ := solution_unique s t a c hcC z hzz i k he'
  rw [hb] at h₁
  rw [hc] at h₂
  exact h₁.trans h₂.symm

abbrev Base : Scheme := puncturedParameter.toScheme
def baseMap : Base ⟶ ComplexBase := puncturedParameter.ι ≫ affineLineToC
abbrev Product : Scheme := RationalSourceOver P Base baseMap

def productLeft : Product ⟶ ProjectiveLine := pullback.fst P.structureMap baseMap
def productBase : Product ⟶ Base := pullback.snd P.structureMap baseMap

theorem productLeft_over : productLeft ≫ P.structureMap = productBase ≫ baseMap :=
  pullback.condition

theorem parameter_isUnit : IsUnit (puncturedParameter.ι.appTop parameterFunction) := by
  rw [← LeBrunSalamon.ScalarSections.topIso_inv_restrict puncturedParameter parameterFunction]
  exact (AffineLine.toRingedSpace.isUnit_res_basicOpen parameterFunction).map
    puncturedParameter.topIso.inv.hom

def inverseParameter : RingSections Base ⊤ :=
  Classical.choose (isUnit_iff_exists_inv.mp parameter_isUnit)

theorem inverseParameter_spec :
    puncturedParameter.ι.appTop parameterFunction * inverseParameter = 1 :=
  Classical.choose_spec (isUnit_iff_exists_inv.mp parameter_isUnit)

abbrev Star (F : StandardSource) := pullback F.parameter puncturedParameter.ι

def starSource (F : StandardSource) : Star F ⟶ F.source :=
  pullback.fst F.parameter puncturedParameter.ι

def starBase (F : StandardSource) : Star F ⟶ Base :=
  pullback.snd F.parameter puncturedParameter.ι

def projection (F : StandardSource) : Star F ⟶ Product :=
  pullback.lift (starSource F ≫ F.left) (starBase F) (by
    rw [Category.assoc, F.left_over, ← Category.assoc]
    change (pullback.fst F.parameter puncturedParameter.ι ≫ F.parameter) ≫ affineLineToC = _
    rw [pullback.condition, Category.assoc]
    rfl)

@[reassoc]
theorem projection_left (F : StandardSource) :
    projection F ≫ productLeft = starSource F ≫ F.left := by
  simp only [projection, productLeft, pullback.lift_fst]

@[reassoc]
theorem projection_base (F : StandardSource) : projection F ≫ productBase = starBase F := by
  simp only [projection, productBase, pullback.lift_snd]

theorem projection_mono (F : StandardSource) : Mono (projection F) := by
  constructor
  intro T f g h
  have hl : f ≫ starSource F ≫ F.left = g ≫ starSource F ≫ F.left := by
    simpa only [Category.assoc, projection_left] using
      congrArg (fun h => h ≫ productLeft) h
  have hb : f ≫ starBase F = g ≫ starBase F := by
    simpa only [Category.assoc, projection_base] using
      congrArg (fun h => h ≫ productBase) h
  apply pullback.hom_ext
  · apply parameter_left_ext F
    · change (f ≫ starSource F) ≫ F.parameter = (g ≫ starSource F) ≫ F.parameter
      simp only [starSource, Category.assoc, pullback.condition]
      simpa only [starBase, Category.assoc] using congrArg (fun h => h ≫ puncturedParameter.ι) hb
    · simpa only [starSource, Category.assoc] using hl
    · have hu := parameter_isUnit.map (f ≫ starBase F).appTop.hom
      simpa only [starSource, starBase, Category.assoc, pullback.condition,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hu
  · exact hb

def productOpen (i : Fin 2) : Product.Opens := productLeft ⁻¹ᵁ ratioOpen i

theorem productOpen_cover : (⨆ i : Fin 2, productOpen i) = ⊤ := by
  apply top_unique
  intro x _
  have h : productLeft x ∈ (⨆ i : Fin 2, ratioOpen i) := by rw [ratioOpen_cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

def localBase (i : Fin 2) : (productOpen i).toScheme ⟶ Base :=
  (productOpen i).ι ≫ productBase

def localParameter (i : Fin 2) : (productOpen i).toScheme ⟶ AffineLine :=
  localBase i ≫ puncturedParameter.ι

def localStructure (i : Fin 2) : (productOpen i).toScheme ⟶ ComplexBase :=
  localParameter i ≫ affineLineToC

def localRatio (i : Fin 2) : (productOpen i).toScheme ⟶ AffineLine :=
  liftRatio ((productOpen i).ι ≫ productLeft) i (by
    rintro _ ⟨x, rfl⟩
    exact x.property)

theorem localRatio_spec (i : Fin 2) :
    localRatio i ≫ (ratioPoint i).val = (productOpen i).ι ≫ productLeft :=
  liftRatio_spec _ _ _

theorem localRatio_over (i : Fin 2) : localRatio i ≫ affineLineToC = localStructure i := by
  apply liftRatio_over
  rw [Category.assoc, productLeft_over]
  rfl

def localInverseParameter (i : Fin 2) : RingSections (productOpen i).toScheme ⊤ :=
  (localBase i).appTop inverseParameter

theorem localInverseParameter_spec (i : Fin 2) :
    (localParameter i).appTop parameterFunction * localInverseParameter i = 1 := by
  have h := congrArg (fun a => (localBase i).appTop a) inverseParameter_spec
  simpa only [localParameter, localInverseParameter, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, map_mul, map_one] using h

/-- On U0 the inverse right coordinate is [r/s:1]; on U1 it is
[1:sr]. Both come from the literal formula [U1:sU0]. -/
def localSourceMap (F : StandardSource) (i : Fin 2) : (productOpen i).toScheme ⟶ F.source :=
  Classical.choose (F.universal (productOpen i).toScheme (localStructure i)
    ⟨localParameter i, rfl⟩
    ⟨localRatio i ≫ (ratioPoint i).val, by
      rw [Category.assoc, (ratioPoint i).property, localRatio_over]⟩
    ⟨solutionRatio (localStructure i) (localParameter i) (localRatio i)
        (localInverseParameter i) i ≫ (ratioPoint (other i)).val, by
      rw [Category.assoc, (ratioPoint _).property, solutionRatio, fromFunction_over]⟩
    (solution_equation _ _ _ _ (localInverseParameter_spec i) i))

theorem localSourceMap_spec (F : StandardSource) (i : Fin 2) :
    localSourceMap F i ≫ F.parameter = localParameter i ∧
    localSourceMap F i ≫ F.left = localRatio i ≫ (ratioPoint i).val ∧
    localSourceMap F i ≫ F.right =
      solutionRatio (localStructure i) (localParameter i) (localRatio i)
        (localInverseParameter i) i ≫ (ratioPoint (other i)).val :=
  (Classical.choose_spec (F.universal (productOpen i).toScheme (localStructure i)
    ⟨localParameter i, rfl⟩
    ⟨localRatio i ≫ (ratioPoint i).val, by
      rw [Category.assoc, (ratioPoint i).property, localRatio_over]⟩
    ⟨solutionRatio (localStructure i) (localParameter i) (localRatio i)
        (localInverseParameter i) i ≫ (ratioPoint (other i)).val, by
      rw [Category.assoc, (ratioPoint _).property, solutionRatio, fromFunction_over]⟩
    (solution_equation _ _ _ _ (localInverseParameter_spec i) i))).1

def localInverse (F : StandardSource) (i : Fin 2) : (productOpen i).toScheme ⟶ Star F :=
  pullback.lift (localSourceMap F i) (localBase i) (localSourceMap_spec F i).1

theorem localInverse_projection (F : StandardSource) (i : Fin 2) :
    localInverse F i ≫ projection F = (productOpen i).ι := by
  apply pullback.hom_ext
  · change (localInverse F i ≫ projection F) ≫ productLeft =
      (productOpen i).ι ≫ productLeft
    rw [Category.assoc, projection_left]
    change localInverse F i ≫ pullback.fst F.parameter puncturedParameter.ι ≫ F.left = _
    rw [localInverse, pullback.lift_fst_assoc, (localSourceMap_spec F i).2.1, localRatio_spec]
  · change (localInverse F i ≫ projection F) ≫ productBase =
      (productOpen i).ι ≫ productBase
    rw [Category.assoc, projection_base]
    change localInverse F i ≫ pullback.snd F.parameter puncturedParameter.ι = _
    rw [localInverse, pullback.lift_snd]
    rfl

def productCover : Product.OpenCover where
  I₀ := Fin 2
  X i := (productOpen i).toScheme
  f i := (productOpen i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x ∈ (⨆ i : Fin 2, productOpen i) := by rw [productOpen_cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩

theorem localInverse_compatible (F : StandardSource) (i j : Fin 2) :
    pullback.fst (productOpen i).ι (productOpen j).ι ≫ localInverse F i =
      pullback.snd (productOpen i).ι (productOpen j).ι ≫ localInverse F j := by
  letI := projection_mono F
  apply (cancel_mono (projection F)).mp
  rw [Category.assoc, Category.assoc, localInverse_projection, localInverse_projection]
  exact pullback.condition

def inverse (F : StandardSource) : Product ⟶ Star F :=
  productCover.glueMorphisms (localInverse F) (localInverse_compatible F)

@[reassoc]
theorem productOpen_inverse (F : StandardSource) (i : Fin 2) :
    (productOpen i).ι ≫ inverse F = localInverse F i :=
  productCover.ι_glueMorphisms _ _ i

theorem inverse_projection (F : StandardSource) : inverse F ≫ projection F = 𝟙 Product := by
  apply productCover.hom_ext
  intro i
  change (productOpen i).ι ≫ (inverse F ≫ projection F) = (productOpen i).ι ≫ 𝟙 Product
  rw [← Category.assoc, productOpen_inverse, localInverse_projection, Category.comp_id]

theorem projection_inverse (F : StandardSource) : projection F ≫ inverse F = 𝟙 (Star F) := by
  letI := projection_mono F
  apply (cancel_mono (projection F)).mp
  rw [Category.assoc, inverse_projection, Category.comp_id, Category.id_comp]

def trivialization (F : StandardSource) : Star F ≅ Product where
  hom := projection F
  inv := inverse F
  hom_inv_id := projection_inverse F
  inv_hom_id := inverse_projection F

end PuncturedSourceProof

theorem standardSource_puncturedTrivialization (F : StandardSource) :
    ∃ e : pullback F.parameter puncturedParameter.ι ≅
      RationalSourceOver P puncturedParameter.toScheme (puncturedParameter.ι ≫ affineLineToC),
      e.hom ≫ pullback.snd P.structureMap (puncturedParameter.ι ≫ affineLineToC) =
        pullback.snd F.parameter puncturedParameter.ι := by
  exact ⟨PuncturedSourceProof.trivialization F, PuncturedSourceProof.projection_base F⟩

/-- Geometry of the fixed source; these are theorems, not fields defining it.
Existence and properness are constructed after the total-line-space API. -/
theorem standardSource_flat (F : StandardSource) : Flat F.parameter := by
  exact SourceAffineCharts.parameter_flat F

/-- Geometry of the fixed source; these are theorems, not fields defining it. -/
theorem standardSource_exists : Nonempty StandardSource := ⟨StandardSourceProof.constructed⟩

theorem standardSource_proper (F : StandardSource) : IsProper F.parameter := by
  letI : IsProper StandardSourceProof.constructed.parameter :=
    StandardSourceProof.constructed_proper
  letI : IsIso (StandardSourceProof.mapTo F StandardSourceProof.constructed) := by
    change IsIso (StandardSourceProof.presentationIso F StandardSourceProof.constructed).hom
    infer_instance
  rw [← (StandardSourceProof.mapTo_spec F StandardSourceProof.constructed).1]
  infer_instance

theorem standardSource_lfp (F : StandardSource) : LocallyOfFinitePresentation F.parameter := by
  letI : IsProper F.parameter := standardSource_proper F
  letI : IsLocallyNoetherian AffineLine := by
    dsimp [AffineLine]
    infer_instance
  infer_instance

theorem relativeHom_exists {d : ℕ} (F : StandardSource)
    (X : SmoothProperComplexVariety d) (hX : HasProjectiveEmbedding X) :
    Nonempty (RelativeHom F X) := by
  letI : IsLocallyNoetherian AffineLine := by
    dsimp [AffineLine]
    infer_instance
  letI : Flat F.parameter := standardSource_flat F
  letI : LocallyOfFinitePresentation F.parameter := standardSource_lfp F
  let e : F.source ≅ StandardSourceProof.source :=
    StandardSourceProof.presentationIso F StandardSourceProof.constructed
  letI : IsClosedImmersion StandardSourceProof.inclusion :=
    StandardSourceProof.SectionEquality.inclusion_closed
      StandardSourceProof.total StandardSourceProof.equationLeft StandardSourceProof.equationRight
  let j : F.source ⟶ HomDeformationInput.projectiveProduct affineLineToC P P :=
    e.hom ≫ StandardSourceProof.inclusion
  letI : IsClosedImmersion j := by
    exact IsClosedImmersion.comp e.hom StandardSourceProof.inclusion
  have hj : j ≫ HomDeformationInput.projectiveProductToBase affineLineToC P P =
      F.parameter := by
    change (e.hom ≫ StandardSourceProof.inclusion) ≫
      StandardSourceProof.ambientParameter = F.parameter
    rw [Category.assoc]
    exact (StandardSourceProof.mapTo_spec F StandardSourceProof.constructed).1
  obtain ⟨H⟩ := HomDeformationInput.StandardInputs.presentation_exists_of_projectiveProduct
    F.parameter affineLineToC P P j hj X hX
  exact ⟨{ parameter := H.parameter
           toBase := H.toBase
           evaluation := H.evaluation
           overC := H.overC
           universal := H.universal }⟩

theorem relativeHom_lfp {d : ℕ} (F : StandardSource)
    (X : SmoothProperComplexVariety d) (hX : HasProjectiveEmbedding X)
    (H : RelativeHom F X) : LocallyOfFinitePresentation H.toBase := by
  letI : IsProper F.parameter := standardSource_proper F
  letI : Flat F.parameter := standardSource_flat F
  letI : LocallyOfFinitePresentation F.parameter := standardSource_lfp F
  exact HomDeformationInput.StandardInputs.locallyOfFinitePresentation
    F.parameter affineLineToC X (HomDeformationInput.ofRelativeHom H)

end Smoothing

/-! ## Algebra behind the all-sheet argument and transverse branch tests -/
namespace SheetAlgebra

section FiniteAlgebra
variable (K B : Type*) [Field K] [CommRing B] [Algebra K B]

/-- Every point of Spec B has K as its residue algebra (B is finite over K
when the splitting theorem is applied). Geometric points over Kbar are NOT
a substitute for this condition over the actual function field K. -/
def RationalPrimeResidues : Prop :=
  ∀ p : Ideal B, p.IsPrime → Nonempty ((B ⧸ p) ≃ₐ[K] K)

/-- A literal product decomposition, allowing no nilpotent thickening. -/
def SplitFiniteAlgebra : Prop := ∃ m : ℕ, Nonempty (B ≃ₐ[K] (Fin m → K))

/-- Reducedness is essential: K[epsilon]/epsilon² has rational residue
fields but is not a product of fields. -/
theorem finite_reduced_rational_isSplit [FiniteDimensional K B] [IsReduced B]
    (h : RationalPrimeResidues K B) : SplitFiniteAlgebra K B := by
  classical
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let r (p : MaximalSpectrum B) : (B ⧸ p.asIdeal) ≃ₐ[K] K :=
    Classical.choice (h p.asIdeal inferInstance)
  refine ⟨Fintype.card (MaximalSpectrum B), ⟨?_⟩⟩
  exact ((IsArtinianRing.equivPi B).restrictScalars K).trans
    ((AlgEquiv.piCongrRight r).trans
      (AlgEquiv.piCongrLeft K
        (fun _ : Fin (Fintype.card (MaximalSpectrum B)) => K)
        (Fintype.equivFin (MaximalSpectrum B))))


theorem split_implies_reduced (h : SplitFiniteAlgebra K B) : IsReduced B := by
  obtain ⟨m, ⟨e⟩⟩ := h
  exact isReduced_of_injective e.toRingHom e.injective


theorem split_implies_rationalResidues (h : SplitFiniteAlgebra K B) :
    RationalPrimeResidues K B := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := h
  intro p hp
  let q : PrimeSpectrum (Fin m → K) :=
    PrimeSpectrum.comap e.symm.toRingHom ⟨p, hp⟩
  obtain ⟨i, r, hr⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq q
  have hbot : r.asIdeal = ⊥ := Ideal.eq_bot_of_prime r.asIdeal
  let f : B →ₐ[K] K := (Pi.evalAlgHom K (fun _ : Fin m => K) i).comp e.toAlgHom
  have hker : RingHom.ker f.toRingHom = p := by
    ext b
    have H := congrArg (fun t : PrimeSpectrum (Fin m → K) => e b ∈ t.asIdeal) hr
    have H' : (e b i ∈ r.asIdeal) = (b ∈ p) := by
      simpa [q] using H
    change e b i = 0 ↔ b ∈ p
    simpa only [hbot, Ideal.mem_bot] using Iff.of_eq H'
  have hf : Function.Surjective f := by
    intro a
    refine ⟨e.symm (fun _ => a), ?_⟩
    simp [f]
  exact ⟨(Ideal.quotientEquivAlgOfEq K hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)⟩


theorem split_nontrivial_positive [Nontrivial B] (m : ℕ)
    (e : B ≃ₐ[K] (Fin m → K)) : 0 < m := by
  by_contra h
  have hm : m = 0 := Nat.eq_zero_of_not_pos h
  subst m
  have he : e (0 : B) = e 1 := funext fun i => Fin.elim0 i
  exact zero_ne_one (e.injective he)


theorem split_dimension [FiniteDimensional K B] (m : ℕ)
    (e : B ≃ₐ[K] (Fin m → K)) : Module.finrank K B = m := by
  calc
    Module.finrank K B = Module.finrank K (Fin m → K) := e.toLinearEquiv.finrank_eq
    _ = m := by simp only [Module.finrank_pi, Fintype.card_fin]


/-- The finite image is a closed subscheme of A1_K. Its coordinate
algebra is generated by its SINGLE tautological coordinate. -/
def GeneratedByCoordinate (z : B) : Prop := Algebra.adjoin K {z} = ⊤

/-- An injective map into a larger algebra sending the coordinate to a
scalar forces B=K. No K-rational point of the larger algebra is assumed. -/
theorem coordinate_scalar_forces_base
    (A : Type*) [CommRing A] [Nontrivial A] [Algebra K A]
    (z : B) (hz : GeneratedByCoordinate K B z)
    (f : B →ₐ[K] A) (hf : Function.Injective f) (a : K)
    (ha : f z = algebraMap K A a) :
    ∃ e : B ≃ₐ[K] K, e z = a := by
  change Algebra.adjoin K {z} = ⊤ at hz
  letI : Nontrivial B := f.toRingHom.domain_nontrivial
  have hzscalar : z = algebraMap K B a := by
    apply hf
    simpa only [f.commutes] using ha
  have hadjoin : Algebra.adjoin K {z} ≤ (⊥ : Subalgebra K B) := by
    apply Algebra.adjoin_le
    intro b hb
    have hbz : b = z := Set.mem_singleton_iff.mp hb
    rw [hbz, hzscalar]
    exact Subalgebra.algebraMap_mem _ a
  have htopbot : (⊤ : Subalgebra K B) = ⊥ :=
    le_antisymm (hz ▸ hadjoin) bot_le
  let e : K ≃ₐ[K] B := AlgEquiv.ofBijective (Algebra.ofId K B)
    ((Algebra.bijective_algebraMap_iff).mpr htopbot)
  refine ⟨e.symm, ?_⟩
  rw [hzscalar]
  exact e.symm_apply_apply a


/-- Generic component image test used in des:all-sheets. The kernel
identifies the particular prime image; it need not be zero in B itself. -/
theorem prime_image_of_scalar_coordinate
    (A : Type*) [CommRing A] [IsDomain A] [Algebra K A]
    (z : B) (hz : GeneratedByCoordinate K B z) (f : B →ₐ[K] A)
    (a : K) (ha : f z = algebraMap K A a) :
    Nonempty ((B ⧸ RingHom.ker f.toRingHom) ≃ₐ[K] K) := by
  change Algebra.adjoin K {z} = ⊤ at hz
  let q := Ideal.Quotient.mkₐ K (RingHom.ker f.toRingHom)
  have hzq : GeneratedByCoordinate K (B ⧸ RingHom.ker f.toRingHom) (q z) := by
    change Algebra.adjoin K {q z} = ⊤
    rw [← AlgHom.map_adjoin_singleton, hz, Algebra.map_top]
    exact (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective K _)
  obtain ⟨e, _⟩ := coordinate_scalar_forces_base K
    (B ⧸ RingHom.ker f.toRingHom) A (q z) hzq (Ideal.kerLiftAlg f)
    (Ideal.kerLiftAlg_injective f) a (by
      change f z = algebraMap K A a
      exact ha)
  exact ⟨e⟩


/-- Every prime is covered by some dominating source component whose
coordinate is scalar. Omitting the universal quantifier would leave
uncontrolled sheets. The family of source domains need not have K-points. -/
theorem all_prime_images_scalar_implies_split
    [FiniteDimensional K B] [IsReduced B]
    (z : B) (hz : GeneratedByCoordinate K B z)
    (h : ∀ p : Ideal B, p.IsPrime →
      ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra K A)
        (f : B →ₐ[K] A) (a : K),
        RingHom.ker f.toRingHom = p ∧ f z = algebraMap K A a) :
    SplitFiniteAlgebra K B := by
  apply finite_reduced_rational_isSplit K B
  intro p hp
  obtain ⟨A, hR, hD, hA, f, a, hker, ha⟩ := h p hp
  letI := hR
  letI := hD
  letI := hA
  obtain ⟨e⟩ := prime_image_of_scalar_coordinate K B A z hz f a ha
  exact ⟨(Ideal.quotientEquivAlgOfEq K hker.symm).trans e⟩


/-- If an integral finite cover splits generically, there is one sheet.
This is applied to a normalized dominating curve COMPONENT, not to the
whole pullback (which can have several components). -/
theorem split_domain_has_one_sheet [IsDomain B] (m : ℕ)
    (e : B ≃ₐ[K] (Fin m → K)) : m = 1 := by
  classical
  have hpos := split_nontrivial_positive K B m e
  by_contra hm
  have hm1 : 1 < m := by omega
  letI : IsDomain (Fin m → K) :=
    Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  let d : Fin m → K := fun i => if i.val = 0 then 1 else 0
  have hd : IsIdempotentElem d := by
    change d * d = d
    funext i
    simp only [Pi.mul_apply, d]
    split_ifs <;> simp
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hd with h0 | h1
  · have : (1 : K) = 0 := by simpa [d] using congrFun h0 ⟨0, hpos⟩
    exact one_ne_zero this
  · have : (0 : K) = 1 := by simpa [d] using congrFun h1 ⟨1, hm1⟩
    exact zero_ne_one this


end FiniteAlgebra

/-- Concrete warning against deleting reducedness from the splitting lemma. -/
theorem dualNumbers_not_reduced : ¬ IsReduced Infinitesimal.Dual := by
  intro h
  letI := h
  exact Infinitesimal.epsilon_ne_zero
    (show IsNilpotent Infinitesimal.epsilon from ⟨2, Infinitesimal.epsilon_square⟩).eq_zero


theorem dualNumbers_rationalResidues : RationalPrimeResidues ℂ Infinitesimal.Dual := by
  intro p hp
  letI : p.IsPrime := hp
  let q := Ideal.Quotient.mkₐ ℂ p
  have he : q Infinitesimal.epsilon = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [← map_pow, Infinitesimal.epsilon_square, map_zero]
  have hs : Function.Surjective (algebraMap ℂ (Infinitesimal.Dual ⧸ p)) := by
    intro x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ p x
    obtain ⟨ab, hz, _⟩ := Infinitesimal.dual_normalForm z
    refine ⟨ab.1, ?_⟩
    change algebraMap ℂ (Infinitesimal.Dual ⧸ p) ab.1 = q z
    rw [hz, map_add, map_mul, he, zero_mul, add_zero]
    exact (q.commutes ab.1).symm
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId ℂ (Infinitesimal.Dual ⧸ p))
    ⟨(algebraMap ℂ (Infinitesimal.Dual ⧸ p)).injective, hs⟩).symm⟩


theorem dualNumbers_not_split : ¬ SplitFiniteAlgebra ℂ Infinitesimal.Dual := by
  intro h
  exact dualNumbers_not_reduced (split_implies_reduced ℂ Infinitesimal.Dual h)

/-! Formal local calculation underlying des:pullback-germ. -/
namespace TransverseBranch

abbrev TwoSeries := MvPowerSeries (Fin 2) ℂ

/-- Embed a(t) as a two-variable series, independent of z. The coefficients
are specified directly; there is no unspecified substitution operator. -/
def inSecondVariable (a : PowerSeries ℂ) : TwoSeries :=
  fun d => if d 0 = 0 then PowerSeries.coeff (d 1) a else 0

def relationIdeal (e : ℕ) (a : PowerSeries ℂ) : Ideal TwoSeries :=
  Ideal.span {MvPowerSeries.X 0 ^ e - inSecondVariable a}

abbrev PullbackRing (e : ℕ) (a : PowerSeries ℂ) := TwoSeries ⧸ relationIdeal e a

def z (e : ℕ) (a : PowerSeries ℂ) : PullbackRing e a :=
  Ideal.Quotient.mk (relationIdeal e a) (MvPowerSeries.X 0)

def t (e : ℕ) (a : PowerSeries ℂ) : PullbackRing e a :=
  Ideal.Quotient.mk (relationIdeal e a) (MvPowerSeries.X 1)

/-- a(0)=0 and a'(0)!=0 express transversality of the test curve. -/
def IsTransverse (a : PowerSeries ℂ) : Prop :=
  PowerSeries.coeff 0 a = 0 ∧ PowerSeries.coeff 1 a ≠ 0

namespace FormalBranchProofCandidate

local notation "Z" => (MvPowerSeries.X (0 : Fin 2) : TwoSeries)
local notation "T" => (MvPowerSeries.X (1 : Fin 2) : TwoSeries)

/-- The original coefficientwise embedding is the actual substitution embedding. -/
theorem inSecondVariable_eq_toMvPowerSeries (a : PowerSeries ℂ) :
    inSecondVariable a = a.toMvPowerSeries (1 : Fin 2) := by
  apply MvPowerSeries.ext
  intro d
  rw [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.coeff_subst_single]
  change (if d 0 = 0 then PowerSeries.coeff (d 1) a else 0) =
    if d = Finsupp.single 1 (d 1) then PowerSeries.coeff (d 1) a else 0
  have hd : d = Finsupp.single 1 (d 1) ↔ d 0 = 0 := by
    constructor
    · intro h
      simpa using congrArg (fun v : Fin 2 →₀ ℕ => v 0) h
    · intro h
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [h]
  simp only [hd]

/-- Mixed uni/multivariable substitution is composition on every series. -/
theorem subst_univariate (v : Fin 2 → TwoSeries) (hv : MvPowerSeries.HasSubst v)
    (w : TwoSeries) (hw : PowerSeries.HasSubst w) (f : PowerSeries ℂ) :
    MvPowerSeries.subst v (f.subst w) = f.subst (MvPowerSeries.subst v w) := by
  exact MvPowerSeries.subst_comp_subst_apply hw.const hv f

def firstCoordinate : Unit ↪ Fin 2 where
  toFun _ := 0
  inj' := by intro i j _; cases i; cases j; rfl

/-- The actual map retaining z and killing t. -/
def firstProjection : TwoSeries →ₐ[ℂ] PowerSeries ℂ :=
  MvPowerSeries.killCompl firstCoordinate

theorem firstProjection_Z : firstProjection Z = PowerSeries.X := by
  exact MvPowerSeries.killCompl_X (e := firstCoordinate) ()

theorem firstProjection_T : firstProjection T = 0 := by
  apply MvPowerSeries.killCompl_X_eq_zero
  rintro ⟨i, hi⟩
  have h : (0 : Fin 2) = 1 := hi
  exact (by decide : (0 : Fin 2) ≠ 1) h

theorem firstProjection_surjective : Function.Surjective firstProjection := by
  intro f
  refine ⟨MvPowerSeries.rename firstCoordinate f, ?_⟩
  exact MvPowerSeries.killCompl_rename_app f

/-- Exact kernel, before taking any quotient or radical. -/
theorem firstProjection_eq_zero_iff (f : TwoSeries) :
    firstProjection f = 0 ↔ T ∣ f := by
  constructor
  · intro h
    apply MvPowerSeries.X_dvd_iff.mpr
    intro d hd
    have hd' : Finsupp.embDomain firstCoordinate (Finsupp.single () (d 0)) = d := by
      rw [Finsupp.embDomain_single]
      change Finsupp.single (0 : Fin 2) (d 0) = d
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [hd]
    have hc := congrArg (MvPowerSeries.coeff (Finsupp.single () (d 0))) h
    simpa only [firstProjection, MvPowerSeries.coeff_killCompl, hd', map_zero] using hc
  · rintro ⟨g, rfl⟩
    rw [map_mul, firstProjection_T, zero_mul]

def shiftedVariable (e : ℕ) : TwoSeries := T + Z ^ e

theorem shiftedVariable_hasSubst (e : ℕ) (he : 0 < e) :
    PowerSeries.HasSubst (shiftedVariable e) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  simp [shiftedVariable, Nat.ne_of_gt he]

def forwardVariables (e : ℕ) (b : PowerSeries ℂ) : Fin 2 → TwoSeries :=
  ![Z, b.subst (shiftedVariable e)]

def backwardVariables (e : ℕ) (a : PowerSeries ℂ) : Fin 2 → TwoSeries :=
  ![Z, a.subst T - Z ^ e]

theorem forwardVariables_hasSubst (e : ℕ) (he : 0 < e)
    (b : PowerSeries ℂ) (hb : b.constantCoeff = 0) :
    MvPowerSeries.HasSubst (forwardVariables e b) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i
  · simp [forwardVariables]
  · change MvPowerSeries.constantCoeff (b.subst (shiftedVariable e)) = 0
    exact PowerSeries.constantCoeff_subst_eq_zero
      (by simp [shiftedVariable, Nat.ne_of_gt he]) b hb

theorem backwardVariables_hasSubst (e : ℕ) (he : 0 < e)
    (a : PowerSeries ℂ) (ha : a.constantCoeff = 0) :
    MvPowerSeries.HasSubst (backwardVariables e a) := by
  have h : MvPowerSeries.constantCoeff (a.subst T) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) a ha
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [backwardVariables, h, Nat.ne_of_gt he]

/-- Phi(Psi(X_i)) = X_i; these equations feed the all-series composition theorem. -/
theorem forward_after_backward (e : ℕ) (he : 0 < e)
    (a b : PowerSeries ℂ) (hb : b.constantCoeff = 0)
    (hab : a.subst b = PowerSeries.X) (i : Fin 2) :
    MvPowerSeries.subst (forwardVariables e b) (backwardVariables e a i) =
      MvPowerSeries.X i := by
  let hf := forwardVariables_hasSubst e he b hb
  have hZ : MvPowerSeries.subst (forwardVariables e b) Z = Z := by
    exact MvPowerSeries.subst_X hf 0
  have hT : MvPowerSeries.subst (forwardVariables e b) T =
      b.subst (shiftedVariable e) := by
    exact MvPowerSeries.subst_X hf 1
  fin_cases i
  · exact hZ
  · change MvPowerSeries.subst (forwardVariables e b) (a.subst T - Z ^ e) = T
    rw [MvPowerSeries.subst_sub hf,
      subst_univariate _ hf T (PowerSeries.HasSubst.X 1) a,
      hT, MvPowerSeries.subst_pow hf, hZ,
      ← PowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' hb) (shiftedVariable_hasSubst e he) a,
      hab, PowerSeries.subst_X (shiftedVariable_hasSubst e he)]
    simp [shiftedVariable]

/-- Psi(Phi(X_i)) = X_i, with the inverse identity in the other order. -/
theorem backward_after_forward (e : ℕ) (he : 0 < e)
    (a b : PowerSeries ℂ) (ha : a.constantCoeff = 0)
    (hba : b.subst a = PowerSeries.X) (i : Fin 2) :
    MvPowerSeries.subst (backwardVariables e a) (forwardVariables e b i) =
      MvPowerSeries.X i := by
  let hg := backwardVariables_hasSubst e he a ha
  have hZ : MvPowerSeries.subst (backwardVariables e a) Z = Z := by
    exact MvPowerSeries.subst_X hg 0
  have hT : MvPowerSeries.subst (backwardVariables e a) T = a.subst T - Z ^ e := by
    exact MvPowerSeries.subst_X hg 1
  have hW : MvPowerSeries.subst (backwardVariables e a) (shiftedVariable e) =
      a.subst T := by
    rw [shiftedVariable, MvPowerSeries.subst_add hg, hT,
      MvPowerSeries.subst_pow hg, hZ, sub_add_cancel]
  fin_cases i
  · exact hZ
  · change MvPowerSeries.subst (backwardVariables e a) (b.subst (shiftedVariable e)) = T
    rw [subst_univariate _ hg _ (shiftedVariable_hasSubst e he) b, hW,
      ← PowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.of_constantCoeff_zero' ha) (PowerSeries.HasSubst.X 1) b,
      hba, PowerSeries.subst_X (PowerSeries.HasSubst.X 1)]

/-- Actual automorphism of the whole ring, proved using composition on arbitrary series. -/
def coordinateEquiv (e : ℕ) (he : 0 < e)
    (a b : PowerSeries ℂ) (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0)
    (hab : a.subst b = PowerSeries.X) (hba : b.subst a = PowerSeries.X) :
    TwoSeries ≃ₐ[ℂ] TwoSeries :=
  AlgEquiv.ofAlgHom
    (MvPowerSeries.substAlgHom (forwardVariables_hasSubst e he b hb))
    (MvPowerSeries.substAlgHom (backwardVariables_hasSubst e he a ha))
    (by
      apply AlgHom.ext
      intro f
      simp only [AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply, AlgHom.id_apply]
      rw [MvPowerSeries.subst_comp_subst_apply
        (backwardVariables_hasSubst e he a ha) (forwardVariables_hasSubst e he b hb),
        funext (forward_after_backward e he a b hb hab), MvPowerSeries.subst_self]
      rfl)
    (by
      apply AlgHom.ext
      intro f
      simp only [AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply, AlgHom.id_apply]
      rw [MvPowerSeries.subst_comp_subst_apply
        (forwardVariables_hasSubst e he b hb) (backwardVariables_hasSubst e he a ha),
        funext (backward_after_forward e he a b ha hba), MvPowerSeries.subst_self]
      rfl)

theorem coordinateEquiv_apply (e : ℕ) (he : 0 < e)
    (a b : PowerSeries ℂ) (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0)
    (hab : a.subst b = PowerSeries.X) (hba : b.subst a = PowerSeries.X) (f : TwoSeries) :
    coordinateEquiv e he a b ha hb hab hba f =
      MvPowerSeries.subst (forwardVariables e b) f := by
  change MvPowerSeries.substAlgHom (forwardVariables_hasSubst e he b hb) f = _
  exact MvPowerSeries.substAlgHom_apply _ _

/-- The exact original relation is carried to minus the second coordinate. -/
theorem coordinateEquiv_relation (e : ℕ) (he : 0 < e)
    (a b : PowerSeries ℂ) (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0)
    (hab : a.subst b = PowerSeries.X) (hba : b.subst a = PowerSeries.X) :
    coordinateEquiv e he a b ha hb hab hba (Z ^ e - inSecondVariable a) = -T := by
  let hf := forwardVariables_hasSubst e he b hb
  rw [coordinateEquiv_apply, inSecondVariable_eq_toMvPowerSeries,
    MvPowerSeries.subst_sub hf, MvPowerSeries.subst_pow hf,
    MvPowerSeries.subst_X hf, PowerSeries.subst_toMvPowerSeries hf]
  change Z ^ e - a.subst (b.subst (shiftedVariable e)) = -T
  rw [← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hb) (shiftedVariable_hasSubst e he) a,
    hab, PowerSeries.subst_X (shiftedVariable_hasSubst e he)]
  dsimp only [shiftedVariable]
  ring

/-- A simple zero is X times a unit, without a choice of component. -/
theorem simple_zero_unit_factor (b : PowerSeries ℂ) (hb : b.constantCoeff = 0)
    (hb1 : IsUnit (PowerSeries.coeff 1 b)) :
    ∃ u : (PowerSeries ℂ)ˣ, b = PowerSeries.X * u.val := by
  obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.mpr hb
  have hc0 : PowerSeries.coeff 1 b = PowerSeries.constantCoeff c := by
    rw [hc, PowerSeries.coeff_one_mul]
    simp
  have hu : IsUnit c := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [← hc0]
    exact hb1)
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, hc⟩

theorem transversePullback_isPowerSeries (e : ℕ) (he : 0 < e)
    (a : PowerSeries ℂ) (ha : IsTransverse a) :
    ∃ q : PullbackRing e a ≃ₐ[ℂ] PowerSeries ℂ,
      q (z e a) = PowerSeries.X ∧
      ∃ u : (PowerSeries ℂ)ˣ, q (t e a) = PowerSeries.X^e * u.val := by
  classical
  have ha0 : a.constantCoeff = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using ha.1
  have ha1 : IsUnit (PowerSeries.coeff 1 a) := isUnit_iff_ne_zero.mpr ha.2
  let b : PowerSeries ℂ := a.substInvOfIsUnit ha1
  have hb0 : b.constantCoeff = 0 := PowerSeries.constantCoeff_substInvOfIsUnit a ha1
  have hb1 : IsUnit (PowerSeries.coeff 1 b) := by
    dsimp only [b]
    rw [PowerSeries.coeff_one_substInvOfIsUnit]
    exact (ha1.unit⁻¹).isUnit
  have hab : a.subst b = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right a ha0 ha1
  have hba : b.subst a = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_left a ha0 ha1
  let φ : TwoSeries ≃ₐ[ℂ] TwoSeries := coordinateEquiv e he a b ha0 hb0 hab hba
  let F : TwoSeries →ₐ[ℂ] PowerSeries ℂ := firstProjection.comp φ.toAlgHom
  have hrel : φ (Z ^ e - inSecondVariable a) = -T :=
    coordinateEquiv_relation e he a b ha0 hb0 hab hba
  have hsurj : Function.Surjective F := firstProjection_surjective.comp φ.surjective
  have hker : RingHom.ker F.toRingHom = relationIdeal e a := by
    ext f
    change firstProjection (φ f) = 0 ↔ f ∈ relationIdeal e a
    rw [firstProjection_eq_zero_iff, relationIdeal, Ideal.mem_span_singleton]
    calc
      T ∣ φ f ↔ φ (Z ^ e - inSecondVariable a) ∣ φ f := by rw [hrel, neg_dvd]
      _ ↔ Z ^ e - inSecondVariable a ∣ f := map_dvd_iff φ
  let q : PullbackRing e a ≃ₐ[ℂ] PowerSeries ℂ :=
    (Ideal.quotientEquivAlgOfEq ℂ hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have hq (s : TwoSeries) : q (Ideal.Quotient.mk (relationIdeal e a) s) = F s := by
    rfl
  have hφz : φ Z = Z := by
    rw [coordinateEquiv_apply]
    exact MvPowerSeries.subst_X (forwardVariables_hasSubst e he b hb0) 0
  have hφt : φ T = b.subst (shiftedVariable e) := by
    rw [coordinateEquiv_apply]
    exact MvPowerSeries.subst_X (forwardVariables_hasSubst e he b hb0) 1
  obtain ⟨u0, hu0⟩ := simple_zero_unit_factor b hb0 hb1
  have hunit : IsUnit (firstProjection (u0.val.subst (shiftedVariable e))) := by
    simpa only [PowerSeries.coe_substAlgHom] using
      (u0.isUnit.map (PowerSeries.substAlgHom (R := ℂ) (shiftedVariable_hasSubst e he))).map
        firstProjection
  obtain ⟨u, hu⟩ := hunit
  refine ⟨q, ?_, u, ?_⟩
  · rw [z, hq]
    change firstProjection (φ Z) = PowerSeries.X
    rw [hφz, firstProjection_Z]
  · rw [t, hq]
    change firstProjection (φ T) = PowerSeries.X ^ e * u.val
    rw [hφt, hu0, PowerSeries.subst_mul (shiftedVariable_hasSubst e he),
      PowerSeries.subst_X (shiftedVariable_hasSubst e he), map_mul]
    have hW : firstProjection (shiftedVariable e) = PowerSeries.X ^ e := by
      rw [shiftedVariable, map_add, map_pow, firstProjection_T, firstProjection_Z, zero_add]
    rw [hW, hu]

theorem transversePullback_domain (e : ℕ) (he : 0 < e)
    (a : PowerSeries ℂ) (ha : IsTransverse a) : IsDomain (PullbackRing e a) := by
  obtain ⟨q, _, _⟩ := transversePullback_isPowerSeries e he a ha
  exact Function.Injective.isDomain q.toRingHom q.injective

theorem transversePullback_noEmbeddedNilpotents (e : ℕ) (he : 0 < e)
    (a : PowerSeries ℂ) (ha : IsTransverse a) : IsReduced (PullbackRing e a) := by
  obtain ⟨q, _, _⟩ := transversePullback_isPowerSeries e he a ha
  exact isReduced_of_injective q.toRingHom q.injective

end FormalBranchProofCandidate

/-- The formal implicit-function theorem: the entire local pullback is
regular, not just its reduction or one component. The isomorphism fixes
z; t becomes z^e times a unit. This does not assert convergence of the
formal inverse, which is a separate analytic theorem when needed. -/
theorem transversePullback_isPowerSeries (e : ℕ) (he : 0 < e)
    (a : PowerSeries ℂ) (ha : IsTransverse a) :
    ∃ q : PullbackRing e a ≃ₐ[ℂ] PowerSeries ℂ,
      q (z e a) = PowerSeries.X ∧
      ∃ u : (PowerSeries ℂ)ˣ, q (t e a) = PowerSeries.X^e * u.val := by
  exact FormalBranchProofCandidate.transversePullback_isPowerSeries e he a ha


theorem transversePullback_domain (e : ℕ) (he : 0 < e)
    (a : PowerSeries ℂ) (ha : IsTransverse a) : IsDomain (PullbackRing e a) := by
  exact FormalBranchProofCandidate.transversePullback_domain e he a ha


theorem transversePullback_noEmbeddedNilpotents (e : ℕ) (he : 0 < e)
    (a : PowerSeries ℂ) (ha : IsTransverse a) : IsReduced (PullbackRing e a) := by
  exact FormalBranchProofCandidate.transversePullback_noEmbeddedNilpotents e he a ha


namespace UniformizerLengthProof

/-- The first e coefficients, with their actual complex-linear structure. -/
def coefficientVector (e : ℕ) : PowerSeries ℂ →ₗ[ℂ] (Fin e → ℂ) :=
  LinearMap.pi fun i => PowerSeries.coeff i.val

theorem coefficientVector_surjective (e : ℕ) :
    Function.Surjective (coefficientVector e) := by
  intro v
  refine ⟨PowerSeries.mk (fun n => if h : n < e then v ⟨n, h⟩ else 0), ?_⟩
  funext i
  change PowerSeries.coeff i.val
    (PowerSeries.mk (fun n => if h : n < e then v ⟨n, h⟩ else 0)) = v i
  simp only [PowerSeries.coeff_mk, dif_pos i.isLt]

/-- Vanishing of precisely these coefficients is divisibility by X^e. -/
theorem coefficientVector_ker (e : ℕ) :
    LinearMap.ker (coefficientVector e) =
      (Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ e}).restrictScalars ℂ := by
  ext f
  change coefficientVector e f = 0 ↔
    f ∈ Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ e}
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h m hm
    exact congrFun h ⟨m, hm⟩
  · intro h
    funext i
    exact h i.val i.isLt

/-- The quotient is the actual ideal quotient, with scalar restriction explicit. -/
def quotientCoefficientEquiv (e : ℕ) :
    ((PowerSeries ℂ) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ e}) ≃ₗ[ℂ]
      (Fin e → ℂ) :=
  (Submodule.Quotient.restrictScalarsEquiv ℂ
      (Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ e})).symm.trans
    ((Submodule.quotEquivOfEq _ _ (coefficientVector_ker e).symm).trans
      ((coefficientVector e).quotKerEquivOfSurjective (coefficientVector_surjective e)))

theorem quotientCoefficientEquiv_mk (e : ℕ) (f : PowerSeries ℂ) :
    quotientCoefficientEquiv e
        (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ e}) f) =
      fun i : Fin e => PowerSeries.coeff i.val f := rfl

end UniformizerLengthProof

/-- The ideal generated by t has length e, agreeing with ramification.
Use module length after the normalized power-series identification; here
the quotient C[[z]]/(z^e) is concretely finite-dimensional. -/
theorem powerSeries_uniformizerPower_length (e : ℕ) :
    Module.finrank ℂ ((PowerSeries ℂ) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ℂ)^e}) = e := by
  calc
    _ = Module.finrank ℂ (Fin e → ℂ) := (UniformizerLengthProof.quotientCoefficientEquiv e).finrank_eq
    _ = e := by simp only [Module.finrank_pi, Fintype.card_fin]


/-- Dropping transversality can produce a reducible pullback. This exact
factorization records the simplest failure, not a general normality claim. -/
theorem tangent_pullback_factorization :
    (MvPowerSeries.X 0 : TwoSeries)^2 - (MvPowerSeries.X 1)^2 =
      (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
        (MvPowerSeries.X 0 + MvPowerSeries.X 1) := by ring

end TransverseBranch
end SheetAlgebra

/-! ## Normal extension of actual bundle-valued sections -/
namespace NormalExtension

open Descent

/-- Locally Noetherian expressed on affine neighborhoods, not the weaker
assertion that all stalks happen to be Noetherian. -/
def NoetherianOnAffines (X : Scheme) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → IsNoetherianRing (RingSections X U)

/-- A rational section represented on a dense open. No quotient by
representatives is needed for the extension statements below. -/
structure RationalSection {X : Scheme} (E : OModule X) where
  domain : X.Opens
  dense : Dense (domain : Set X)
  value : SectionsOn E domain

/-- Equality on an actual overlap, with restriction maps fully annotated.
Pointwise equality on closed points is not used as a substitute. -/
def CompatibleOnOverlap {X : Scheme} {E : OModule X} (s : RationalSection E)
    (V : X.Opens) (t : SectionsOn E V) : Prop :=
  E.presheaf.map (homOfLE (inf_le_left : s.domain ⊓ V ≤ s.domain)).op s.value =
    E.presheaf.map (homOfLE (inf_le_right : s.domain ⊓ V ≤ V)).op t

def RegularAt {X : Scheme} {E : OModule X} (s : RationalSection E) (x : X) : Prop :=
  ∃ V : X.Opens, x ∈ V ∧ ∃ t : SectionsOn E V, CompatibleOnOverlap s V t

def Extends {X : Scheme} {E : OModule X} (s : RationalSection E)
    (t : GlobalSections E) : Prop :=
  E.presheaf.map (homOfLE (le_top : s.domain ≤ ⊤)).op t = s.value

set_option backward.isDefEq.respectTransparency false in
/-- Dense restriction is injective for a locally free sheaf on a reduced
scheme. It is not asserted for arbitrary coherent torsion sheaves. -/
theorem denseRestriction_injective {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (hX : IntegralScheme X)
    (U : X.Opens) (hU : Dense (U : Set X)) :
    Function.Injective
      (fun s : GlobalSections E.sheaf =>
        E.sheaf.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  intro s t hst
  let a : AlgebraicSection E.sheaf := sectionFromValue s
  let b : AlgebraicSection E.sheaf := sectionFromValue t
  have hone : Scheme.Modules.Hom.app a U (1 : RingSections X U) =
      Scheme.Modules.Hom.app b U (1 : RingSections X U) := by
    rw [LeBrunSalamon.ScalarSections.section_app_one,
      LeBrunSalamon.ScalarSections.section_app_one]
    simpa only [a, b, sectionFromValue_spec] using hst
  have hover : a.over U = b.over U := by
    apply (E.sheaf.over U).unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro V
    change Scheme.Modules.Hom.app a V.unop.left (1 : RingSections X V.unop.left) =
      Scheme.Modules.Hom.app b V.unop.left (1 : RingSections X V.unop.left)
    have ha := sheafHom_naturality a V.unop.hom (1 : RingSections X U)
    have hb := sheafHom_naturality b V.unop.hom (1 : RingSections X U)
    change E.sheaf.presheaf.map V.unop.hom.op
        (Scheme.Modules.Hom.app a U (1 : RingSections X U)) =
      Scheme.Modules.Hom.app a V.unop.left
        (X.presheaf.map V.unop.hom.op (1 : RingSections X U)) at ha
    change E.sheaf.presheaf.map V.unop.hom.op
        (Scheme.Modules.Hom.app b U (1 : RingSections X U)) =
      Scheme.Modules.Hom.app b V.unop.left
        (X.presheaf.map V.unop.hom.op (1 : RingSections X U)) at hb
    have hmapOne : X.presheaf.map V.unop.hom.op (1 : RingSections X U) =
        (1 : RingSections X V.unop.left) :=
      (X.presheaf.map V.unop.hom.op).hom.map_one
    rw [hmapOne] at ha hb
    exact ha.symm.trans
      ((congrArg (fun w : SectionsOn E.sheaf U =>
        E.sheaf.presheaf.map V.unop.hom.op w) hone).trans hb)
  let A := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U ≪≫
    Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hpull : (Scheme.Modules.pullback U.ι).map a =
      (Scheme.Modules.pullback U.ι).map b := by
    apply (cancel_epi (e.hom.app (structureModule X))).1
    rw [← e.hom.naturality a, ← e.hom.naturality b]
    change A.map (a.over U) ≫ e.hom.app E.sheaf =
      A.map (b.over U) ≫ e.hom.app E.sheaf
    rw [hover]
  have hd : DenseRange U.ι.base := by
    change Dense (Set.range U.ι)
    simpa only [Scheme.Opens.range_ι] using hU
  have hab : a = b := by
    apply LeBrunSalamon.PhaseTwentyEight.dominant_pullSection_injective
      U.ι hd hX.2 E
    change (unitPullbackIso U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map a =
      (unitPullbackIso U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map b
    rw [hpull]
  have hv := congrArg (fun q : AlgebraicSection E.sheaf => sectionValue q) hab
  simpa only [a, b, sectionFromValue_spec] using hv


theorem rationalSection_extension_unique {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) (hX : IntegralScheme X)
    (s : RationalSection E.sheaf) {a b : GlobalSections E.sheaf}
    (ha : Extends s a) (hb : Extends s b) : a = b :=
  denseRestriction_injective E hX s.domain s.dense (ha.trans hb.symm)

/-- ext:extended-vectors in sheaf form. The hypotheses must apply to the
ACTUAL normal source chart and the LOCALLY FREE TARGET bundle. -/
theorem extend_from_heightOne {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r)
    (hI : IntegralScheme X) (hN : NormalScheme X) (hNoeth : NoetherianOnAffines X)
    (s : RationalSection E.sheaf)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 → RegularAt s x) :
    ∃! t : GlobalSections E.sheaf, Extends s t := by sorry

/-- Agreement of the two contact values is checked on the dense
smooth-source open, then continues to the entire normal source. -/
theorem morphism_values_agree_from_dense {X : Scheme} {r s t : ℕ}
    (E : AlgebraicVectorBundle X r) (F : AlgebraicVectorBundle X s)
    (G : AlgebraicVectorBundle X t) (hX : IntegralScheme X)
    (a : GlobalSections E.sheaf) (b : GlobalSections F.sheaf)
    (f : E.sheaf ⟶ G.sheaf) (g : F.sheaf ⟶ G.sheaf)
    (U : X.Opens) (hU : Dense (U : Set X))
    (h : G.sheaf.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.app ⊤ a) =
      G.sheaf.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (g.app ⊤ b)) :
    f.app ⊤ a = g.app ⊤ b := denseRestriction_injective G hX U hU h

/-- Non-normal sources are deliberately excluded. A finite birational
normalization can have functions with no divisorial poles upstairs that
do not descend to the original source. -/
def requiredHypotheses : List String :=
  [ "integral source", "normal source", "Noetherian affine charts",
    "locally free target", "actual dense-open section", "all height-one points" ]

end NormalExtension

/-! ## The geometric normalization sequence behind the smoothing defect -/
namespace Normalization

open Lines Smoothing

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on sections over C, with the base equality recorded. -/
def pullCSections {Y Z : Scheme} (f : Y ⟶ Z)
    (sY : Y ⟶ ComplexBase) (sZ : Z ⟶ ComplexBase) (hf : f ≫ sZ = sY)
    (E : OModule Z) : CSections sZ E →ₗ[ℂ] CSections sY (pullbackModule f E) :=
  pullCSectionsAlong f sY sZ hf E

abbrev CentralFiber (F : StandardSource) := SourceOver F (scalarPoint 0)

def centralBase (F : StandardSource) : CentralFiber F ⟶ ComplexBase :=
  pullback.snd F.parameter (scalarPoint 0)

def leftBranch {F : StandardSource} (m : SourceMarks F) : ProjectiveLine ⟶ CentralFiber F :=
  pullback.lift m.branchLeft P.structureMap m.left_base

def rightBranch {F : StandardSource} (m : SourceMarks F) : ProjectiveLine ⟶ CentralFiber F :=
  pullback.lift m.branchRight P.structureMap m.right_base

theorem leftBranch_over {F : StandardSource} (m : SourceMarks F) :
    leftBranch m ≫ centralBase F = P.structureMap := by simp [leftBranch, centralBase]

theorem rightBranch_over {F : StandardSource} (m : SourceMarks F) :
    rightBranch m ≫ centralBase F = P.structureMap := by simp [rightBranch, centralBase]

def node {F : StandardSource} (m : SourceMarks F) : ComplexBase ⟶ CentralFiber F :=
  marking.map ≫ leftBranch m

theorem branches_meet {F : StandardSource} (m : SourceMarks F) :
    marking.map ≫ leftBranch m = marking.map ≫ rightBranch m := by
  apply pullback.hom_ext
  · simp [leftBranch, rightBranch, Category.assoc, m.node_agreement]
  · simp [leftBranch, rightBranch, Category.assoc]

namespace CentralCharts

open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def inclusion (F : StandardSource) : CentralFiber F ⟶ F.source :=
  pullback.fst F.parameter (scalarPoint 0)

def chartOpen (F : StandardSource) (k : Fin 3) : (CentralFiber F).Opens :=
  inclusion F ⁻¹ᵁ SourceAffineCharts.chartOpen F (leftIndex k) (rightIndex k)

theorem chartOpen_cover (F : StandardSource) : (⨆ k : Fin 3, chartOpen F k) = ⊤ := by
  apply top_unique
  intro x _
  have h : inclusion F x ∈
      (⨆ k : Fin 3, SourceAffineCharts.chartOpen F (leftIndex k) (rightIndex k)) := by
    rw [threeCharts_cover]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩

def toSourceChart (F : StandardSource) (k : Fin 3) :
    (chartOpen F k).toScheme ⟶
      (SourceAffineCharts.chartOpen F (leftIndex k) (rightIndex k)).toScheme :=
  inclusion F ∣_ SourceAffineCharts.chartOpen F (leftIndex k) (rightIndex k)

def toPlane (F : StandardSource) (k : Fin 3) : (chartOpen F k).toScheme ⟶ Plane :=
  toSourceChart F k ≫ (chartIso F k).hom

def toBase (F : StandardSource) (k : Fin 3) : (chartOpen F k).toScheme ⟶ ComplexBase :=
  (chartOpen F k).ι ≫ centralBase F

/-- The central open is the actual base change of its affine-plane
chart, rather than a scheme chosen merely to have the same points. -/
theorem isPullback (F : StandardSource) (k : Fin 3) :
    IsPullback (toPlane F k) (toBase F k)
      (polynomialLine (parameterPolynomial k)) (scalarPoint 0) := by
  have h := (AlgebraicGeometry.isPullback_morphismRestrict (inclusion F)
    (SourceAffineCharts.chartOpen F (leftIndex k) (rightIndex k))).paste_vert
      (IsPullback.of_hasPullback F.parameter (scalarPoint 0))
  apply h.of_iso (Iso.refl _) (chartIso F k) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (chartToModel_parameter F k).symm
  · simp

theorem toPlane_source (F : StandardSource) (k : Fin 3) :
    toPlane F k ≫ modelMap F k = (chartOpen F k).ι ≫ inclusion F := by
  have h : (chartIso F k).hom ≫ modelMap F k =
      (SourceAffineCharts.chartOpen F (leftIndex k) (rightIndex k)).ι := by
    rw [← modelToChart_inclusion F k, ← Category.assoc]
    change ((chartIso F k).hom ≫ (chartIso F k).inv) ≫ _ = _
    rw [Iso.hom_inv_id, Category.id_comp]
  rw [toPlane, Category.assoc, h]
  exact AlgebraicGeometry.morphismRestrict_ι _ _

def nodeOpenIso (F : StandardSource) : AffineNode.NodeScheme ≅ (chartOpen F 0).toScheme :=
  AffineNode.nodeFibre_isPullback.isoIsPullback _ _ (isPullback F 0)

@[reassoc]
theorem nodeOpenIso_plane (F : StandardSource) :
    (nodeOpenIso F).hom ≫ toPlane F 0 = Spec.map AffineNode.planeQuotient :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc]
theorem nodeOpenIso_base (F : StandardSource) :
    (nodeOpenIso F).hom ≫ toBase F 0 = Spec.map AffineNode.nodeConstants :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

def outerOpenIso (F : StandardSource) (k : Fin 3) (hk : k ≠ 0) :
    AffineLine ≅ (chartOpen F k).toScheme := by
  have h : IsPullback (Spec.map AffineNode.outerQuotient) affineLineToC
      (polynomialLine (parameterPolynomial k)) (scalarPoint 0) := by
    simpa only [parameterPolynomial, if_neg hk] using AffineNode.outerFibre_isPullback
  exact h.isoIsPullback _ _ (isPullback F k)

@[reassoc]
theorem outerOpenIso_plane (F : StandardSource) (k : Fin 3) (hk : k ≠ 0) :
    (outerOpenIso F k hk).hom ≫ toPlane F k = Spec.map AffineNode.outerQuotient :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc]
theorem outerOpenIso_base (F : StandardSource) (k : Fin 3) (hk : k ≠ 0) :
    (outerOpenIso F k hk).hom ≫ toBase F k = affineLineToC :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

def nodeMap (F : StandardSource) : AffineNode.NodeScheme ⟶ CentralFiber F :=
  (nodeOpenIso F).hom ≫ (chartOpen F 0).ι

def outerMap (F : StandardSource) (k : Fin 3) (hk : k ≠ 0) :
    AffineLine ⟶ CentralFiber F :=
  (outerOpenIso F k hk).hom ≫ (chartOpen F k).ι

@[reassoc]
theorem nodeMap_source (F : StandardSource) :
    nodeMap F ≫ inclusion F = Spec.map AffineNode.planeQuotient ≫ modelMap F 0 := by
  rw [nodeMap, Category.assoc, ← toPlane_source, ← Category.assoc, nodeOpenIso_plane]

@[reassoc]
theorem nodeMap_base (F : StandardSource) :
    nodeMap F ≫ centralBase F = Spec.map AffineNode.nodeConstants :=
  nodeOpenIso_base F

@[reassoc]
theorem outerMap_source (F : StandardSource) (k : Fin 3) (hk : k ≠ 0) :
    outerMap F k hk ≫ inclusion F = Spec.map AffineNode.outerQuotient ≫ modelMap F k := by
  rw [outerMap, Category.assoc, ← toPlane_source, ← Category.assoc, outerOpenIso_plane]

@[reassoc]
theorem outerMap_base (F : StandardSource) (k : Fin 3) (hk : k ≠ 0) :
    outerMap F k hk ≫ centralBase F = affineLineToC :=
  outerOpenIso_base F k hk

theorem nodeMap_openImmersion (F : StandardSource) : IsOpenImmersion (nodeMap F) := by
  dsimp only [nodeMap]
  infer_instance

theorem outerMap_openImmersion (F : StandardSource) (k : Fin 3) (hk : k ≠ 0) :
    IsOpenImmersion (outerMap F k hk) := by
  dsimp only [outerMap]
  infer_instance

def leftProjection (F : StandardSource) : CentralFiber F ⟶ ProjectiveLine :=
  inclusion F ≫ F.left

def rightProjection (F : StandardSource) : CentralFiber F ⟶ ProjectiveLine :=
  inclusion F ≫ F.right

@[reassoc]
theorem leftBranch_projection {F : StandardSource} (m : SourceMarks F) :
    leftBranch m ≫ leftProjection F = 𝟙 ProjectiveLine := by
  simp only [leftProjection, inclusion, leftBranch, pullback.lift_fst_assoc, m.left_left]

@[reassoc]
theorem rightBranch_projection {F : StandardSource} (m : SourceMarks F) :
    rightBranch m ≫ rightProjection F = 𝟙 ProjectiveLine := by
  simp only [rightProjection, inclusion, rightBranch, pullback.lift_fst_assoc, m.right_right]

theorem coordinates_ext (F : StandardSource) {T : Scheme} {f g : T ⟶ CentralFiber F}
    (hb : f ≫ centralBase F = g ≫ centralBase F)
    (hl : f ≫ leftProjection F = g ≫ leftProjection F)
    (hr : f ≫ rightProjection F = g ≫ rightProjection F) : f = g := by
  apply pullback.hom_ext
  · apply StandardSourceProof.coordinates_ext F
    · simpa only [inclusion, centralBase, Category.assoc, pullback.condition] using
        congrArg (fun k : T ⟶ ComplexBase => k ≫ scalarPoint 0) hb
    · simpa only [leftProjection, inclusion, Category.assoc] using hl
    · simpa only [rightProjection, inclusion, Category.assoc] using hr
  · exact hb

theorem nodeMap_left (F : StandardSource) :
    nodeMap F ≫ leftProjection F =
      Spec.map AffineNode.planeQuotient ≫ polynomialLine (MvPolynomial.X 0) ≫
        (ratioPoint 0).val := by
  rw [leftProjection, ← Category.assoc, nodeMap_source, Category.assoc,
    (modelMap_spec F 0).2.1]
  rfl

theorem nodeMap_right (F : StandardSource) :
    nodeMap F ≫ rightProjection F =
      Spec.map AffineNode.planeQuotient ≫ polynomialLine (MvPolynomial.X 1) ≫
        (ratioPoint 0).val := by
  rw [rightProjection, ← Category.assoc, nodeMap_source, Category.assoc,
    (modelMap_spec F 0).2.2]
  rfl

@[reassoc]
theorem first_branch {F : StandardSource} (m : SourceMarks F) :
    Spec.map AffineNode.nodeFirst ≫ nodeMap F = (ratioPoint 0).val ≫ leftBranch m := by
  apply coordinates_ext F
  · rw [Category.assoc, nodeMap_base, AffineNode.first_base,
      Category.assoc, leftBranch_over, (ratioPoint 0).property]
  · calc
      (Spec.map AffineNode.nodeFirst ≫ nodeMap F) ≫ leftProjection F =
          (Spec.map AffineNode.nodeFirst ≫ Spec.map AffineNode.planeQuotient ≫
            polynomialLine (MvPolynomial.X 0)) ≫ (ratioPoint 0).val := by
        simp only [Category.assoc, nodeMap_left]
      _ = (ratioPoint 0).val := by
        rw [AffineNode.first_plane_x, Category.id_comp]
      _ = ((ratioPoint 0).val ≫ leftBranch m) ≫ leftProjection F := by
        rw [Category.assoc, leftBranch_projection, Category.comp_id]
  · calc
      (Spec.map AffineNode.nodeFirst ≫ nodeMap F) ≫ rightProjection F =
          (Spec.map AffineNode.nodeFirst ≫ Spec.map AffineNode.planeQuotient ≫
            polynomialLine (MvPolynomial.X 1)) ≫ (ratioPoint 0).val := by
        simp only [Category.assoc, nodeMap_right]
      _ = affineLineToC ≫ marking.map := by
        rw [AffineNode.first_plane_y, Category.assoc, ratioPoint_zero_marking]
      _ = ((ratioPoint 0).val ≫ leftBranch m) ≫ rightProjection F := by
        simp only [rightProjection, inclusion, leftBranch, Category.assoc,
          pullback.lift_fst_assoc, m.left_right]
        rw [← Category.assoc, (ratioPoint 0).property]

@[reassoc]
theorem second_branch {F : StandardSource} (m : SourceMarks F) :
    Spec.map AffineNode.nodeSecond ≫ nodeMap F = (ratioPoint 0).val ≫ rightBranch m := by
  apply coordinates_ext F
  · rw [Category.assoc, nodeMap_base, AffineNode.second_base,
      Category.assoc, rightBranch_over, (ratioPoint 0).property]
  · calc
      (Spec.map AffineNode.nodeSecond ≫ nodeMap F) ≫ leftProjection F =
          (Spec.map AffineNode.nodeSecond ≫ Spec.map AffineNode.planeQuotient ≫
            polynomialLine (MvPolynomial.X 0)) ≫ (ratioPoint 0).val := by
        simp only [Category.assoc, nodeMap_left]
      _ = affineLineToC ≫ marking.map := by
        rw [AffineNode.second_plane_x, Category.assoc, ratioPoint_zero_marking]
      _ = ((ratioPoint 0).val ≫ rightBranch m) ≫ leftProjection F := by
        simp only [leftProjection, inclusion, rightBranch, Category.assoc,
          pullback.lift_fst_assoc, m.right_left]
        rw [← Category.assoc, (ratioPoint 0).property]
  · calc
      (Spec.map AffineNode.nodeSecond ≫ nodeMap F) ≫ rightProjection F =
          (Spec.map AffineNode.nodeSecond ≫ Spec.map AffineNode.planeQuotient ≫
            polynomialLine (MvPolynomial.X 1)) ≫ (ratioPoint 0).val := by
        simp only [Category.assoc, nodeMap_right]
      _ = (ratioPoint 0).val := by
        rw [AffineNode.second_plane_y, Category.id_comp]
      _ = ((ratioPoint 0).val ≫ rightBranch m) ≫ rightProjection F := by
        rw [Category.assoc, rightBranch_projection, Category.comp_id]

@[reassoc]
theorem outer_left_branch {F : StandardSource} (m : SourceMarks F) :
    outerMap F 1 (by decide) = (ratioPoint 1).val ≫ leftBranch m := by
  apply coordinates_ext F
  · rw [outerMap_base, Category.assoc, leftBranch_over, (ratioPoint 1).property]
  · rw [leftProjection, ← Category.assoc, outerMap_source, Category.assoc,
      (modelMap_spec F 1).2.1]
    change Spec.map AffineNode.outerQuotient ≫ polynomialLine (MvPolynomial.X 1) ≫
      (ratioPoint 1).val = _
    rw [← Category.assoc, AffineNode.outer_plane_y, Category.id_comp]
    simp only [inclusion, leftBranch, Category.assoc, pullback.lift_fst_assoc,
      m.left_left, Category.comp_id]
  · rw [rightProjection, ← Category.assoc, outerMap_source, Category.assoc,
      (modelMap_spec F 1).2.2]
    change Spec.map AffineNode.outerQuotient ≫
      polynomialLine (MvPolynomial.X 0 * MvPolynomial.X 1) ≫ (ratioPoint 0).val = _
    rw [← Category.assoc, AffineNode.outer_plane_xy, Category.assoc, ratioPoint_zero_marking]
    simp only [inclusion, leftBranch, Category.assoc, pullback.lift_fst_assoc,
      m.left_right]
    rw [← Category.assoc, (ratioPoint 1).property]

@[reassoc]
theorem outer_right_branch {F : StandardSource} (m : SourceMarks F) :
    outerMap F 2 (by decide) = (ratioPoint 1).val ≫ rightBranch m := by
  apply coordinates_ext F
  · rw [outerMap_base, Category.assoc, rightBranch_over, (ratioPoint 1).property]
  · rw [leftProjection, ← Category.assoc, outerMap_source, Category.assoc,
      (modelMap_spec F 2).2.1]
    change Spec.map AffineNode.outerQuotient ≫
      polynomialLine (MvPolynomial.X 0 * MvPolynomial.X 1) ≫ (ratioPoint 0).val = _
    rw [← Category.assoc, AffineNode.outer_plane_xy, Category.assoc, ratioPoint_zero_marking]
    simp only [inclusion, rightBranch, Category.assoc, pullback.lift_fst_assoc,
      m.right_left]
    rw [← Category.assoc, (ratioPoint 1).property]
  · rw [rightProjection, ← Category.assoc, outerMap_source, Category.assoc,
      (modelMap_spec F 2).2.2]
    change Spec.map AffineNode.outerQuotient ≫ polynomialLine (MvPolynomial.X 1) ≫
      (ratioPoint 1).val = _
    rw [← Category.assoc, AffineNode.outer_plane_y, Category.id_comp]
    simp only [inclusion, rightBranch, Category.assoc, pullback.lift_fst_assoc,
      m.right_right, Category.comp_id]

theorem outer_left_factors {F : StandardSource} (m : SourceMarks F) :
    (chartOpen F 1).ι = ((chartOpen F 1).ι ≫ leftProjection F) ≫ leftBranch m := by
  apply (cancel_epi (outerOpenIso F 1 (by decide)).hom).mp
  simp only [← Category.assoc]
  change outerMap F 1 (by decide) =
    (outerMap F 1 (by decide) ≫ leftProjection F) ≫ leftBranch m
  rw [outer_left_branch m]
  simp only [Category.assoc, leftBranch_projection, leftBranch_projection_assoc,
    Category.id_comp, Category.comp_id]

theorem outer_right_factors {F : StandardSource} (m : SourceMarks F) :
    (chartOpen F 2).ι = ((chartOpen F 2).ι ≫ rightProjection F) ≫ rightBranch m := by
  apply (cancel_epi (outerOpenIso F 2 (by decide)).hom).mp
  simp only [← Category.assoc]
  change outerMap F 2 (by decide) =
    (outerMap F 2 (by decide) ≫ rightProjection F) ≫ rightBranch m
  rw [outer_right_branch m]
  simp only [Category.assoc, rightBranch_projection, rightBranch_projection_assoc,
    Category.id_comp, Category.comp_id]

/-- Equality on the two projective branches is detected on the node
pushout and on the two genuine outer affine charts. -/
theorem maps_ext {F : StandardSource} (m : SourceMarks F) {Z : Scheme}
    {f g : CentralFiber F ⟶ Z}
    (hl : leftBranch m ≫ f = leftBranch m ≫ g)
    (hr : rightBranch m ≫ f = rightBranch m ≫ g) : f = g := by
  apply Scheme.hom_ext_of_forall
  intro x
  have hx : x ∈ (⨆ k : Fin 3, chartOpen F k) := by rw [chartOpen_cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨chartOpen F k, hk, ?_⟩
  fin_cases k
  · apply (cancel_epi (nodeOpenIso F).hom).mp
    change nodeMap F ≫ f = nodeMap F ≫ g
    apply AffineNode.isPushout.hom_ext
    · calc
        Spec.map AffineNode.nodeFirst ≫ (nodeMap F ≫ f) =
            (ratioPoint 0).val ≫ (leftBranch m ≫ f) := by
              rw [← Category.assoc, first_branch m, Category.assoc]
        _ = (ratioPoint 0).val ≫ (leftBranch m ≫ g) := congrArg (fun h => (ratioPoint 0).val ≫ h) hl
        _ = Spec.map AffineNode.nodeFirst ≫ (nodeMap F ≫ g) := by
              symm
              rw [← Category.assoc, first_branch m, Category.assoc]
    · calc
        Spec.map AffineNode.nodeSecond ≫ (nodeMap F ≫ f) =
            (ratioPoint 0).val ≫ (rightBranch m ≫ f) := by
              rw [← Category.assoc, second_branch m, Category.assoc]
        _ = (ratioPoint 0).val ≫ (rightBranch m ≫ g) := congrArg (fun h => (ratioPoint 0).val ≫ h) hr
        _ = Spec.map AffineNode.nodeSecond ≫ (nodeMap F ≫ g) := by
              symm
              rw [← Category.assoc, second_branch m, Category.assoc]
  · change (chartOpen F 1).ι ≫ f = (chartOpen F 1).ι ≫ g
    rw [outer_left_factors m]
    simp only [Category.assoc, hl]
  · change (chartOpen F 2).ι ≫ f = (chartOpen F 2).ι ≫ g
    rw [outer_right_factors m]
    simp only [Category.assoc, hr]

section Gluing

variable {F : StandardSource} (m : SourceMarks F) {Z : Scheme}
  (f g : ProjectiveLine ⟶ Z) (hn : marking.map ≫ f = marking.map ≫ g)

def nodeGlue : AffineNode.NodeScheme ⟶ Z :=
  AffineNode.isPushout.desc ((ratioPoint 0).val ≫ f) ((ratioPoint 0).val ≫ g) (by
    rw [← Category.assoc, ← Category.assoc, ratioPoint_zero_marking]
    exact hn)

@[reassoc]
theorem nodeGlue_first :
    Spec.map AffineNode.nodeFirst ≫ nodeGlue f g hn = (ratioPoint 0).val ≫ f :=
  AffineNode.isPushout.inl_desc _ _ _

@[reassoc]
theorem nodeGlue_second :
    Spec.map AffineNode.nodeSecond ≫ nodeGlue f g hn = (ratioPoint 0).val ≫ g :=
  AffineNode.isPushout.inr_desc _ _ _

def localMap (k : Fin 3) : (chartOpen F k).toScheme ⟶ Z := by
  exact Fin.cases
    (motive := fun i : Fin 3 => (chartOpen F i).toScheme ⟶ Z)
    ((nodeOpenIso F).inv ≫ nodeGlue f g hn)
    (Fin.cases
      (motive := fun i : Fin 2 => (chartOpen F i.succ).toScheme ⟶ Z)
      ((chartOpen F 1).ι ≫ leftProjection F ≫ f)
      (Fin.cases
        (motive := fun i : Fin 1 => (chartOpen F i.succ.succ).toScheme ⟶ Z)
        ((chartOpen F 2).ι ≫ rightProjection F ≫ g)
        (fun i => Fin.elim0 i))) k

theorem localMap_zero : localMap (F := F) f g hn 0 =
    (nodeOpenIso F).inv ≫ nodeGlue f g hn := rfl

theorem localMap_one : localMap (F := F) f g hn 1 =
    (chartOpen F 1).ι ≫ leftProjection F ≫ f := rfl

theorem localMap_two : localMap (F := F) f g hn 2 =
    (chartOpen F 2).ι ≫ rightProjection F ≫ g := rfl

theorem node_local_left {T : Scheme} (a : T ⟶ (chartOpen F 0).toScheme)
    (l : T ⟶ ProjectiveLine) (hl : a ≫ (chartOpen F 0).ι = l ≫ leftBranch m) :
    a ≫ localMap (F := F) f g hn 0 = l ≫ f := by
  have hp : a ≫ (chartOpen F 0).ι ≫ leftProjection F = l := by
    rw [← Category.assoc, hl, Category.assoc, leftBranch_projection, Category.comp_id]
  have hr : Set.range l ⊆ Set.range (ratioPoint 0).val := by
    rw [ratioPoint_range, ← hp]
    rintro _ ⟨x, rfl⟩
    exact (a x).property.1
  letI := ratioPoint_openImmersion 0
  let q := IsOpenImmersion.lift (ratioPoint 0).val l hr
  have hq : q ≫ (ratioPoint 0).val = l := IsOpenImmersion.lift_fac _ _ _
  have ha : q ≫ Spec.map AffineNode.nodeFirst ≫ (nodeOpenIso F).hom = a := by
    apply (cancel_mono (chartOpen F 0).ι).mp
    change q ≫ Spec.map AffineNode.nodeFirst ≫ nodeMap F = a ≫ (chartOpen F 0).ι
    rw [first_branch m, ← Category.assoc, hq, hl]
  rw [← ha, localMap_zero]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [nodeGlue_first, ← Category.assoc, hq]

theorem node_local_right {T : Scheme} (a : T ⟶ (chartOpen F 0).toScheme)
    (l : T ⟶ ProjectiveLine) (hl : a ≫ (chartOpen F 0).ι = l ≫ rightBranch m) :
    a ≫ localMap (F := F) f g hn 0 = l ≫ g := by
  have hp : a ≫ (chartOpen F 0).ι ≫ rightProjection F = l := by
    rw [← Category.assoc, hl, Category.assoc, rightBranch_projection, Category.comp_id]
  have hr : Set.range l ⊆ Set.range (ratioPoint 0).val := by
    rw [ratioPoint_range, ← hp]
    rintro _ ⟨x, rfl⟩
    exact (a x).property.2
  letI := ratioPoint_openImmersion 0
  let q := IsOpenImmersion.lift (ratioPoint 0).val l hr
  have hq : q ≫ (ratioPoint 0).val = l := IsOpenImmersion.lift_fac _ _ _
  have ha : q ≫ Spec.map AffineNode.nodeSecond ≫ (nodeOpenIso F).hom = a := by
    apply (cancel_mono (chartOpen F 0).ι).mp
    change q ≫ Spec.map AffineNode.nodeSecond ≫ nodeMap F = a ≫ (chartOpen F 0).ι
    rw [second_branch m, ← Category.assoc, hq, hl]
  rw [← ha, localMap_zero]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [nodeGlue_second, ← Category.assoc, hq]

include m in
theorem node_outer_left {T : Scheme} (a : T ⟶ (chartOpen F 0).toScheme)
    (b : T ⟶ (chartOpen F 1).toScheme)
    (h : a ≫ (chartOpen F 0).ι = b ≫ (chartOpen F 1).ι) :
    a ≫ localMap (F := F) f g hn 0 = b ≫ localMap (F := F) f g hn 1 := by
  have hl : a ≫ (chartOpen F 0).ι =
      (b ≫ (chartOpen F 1).ι ≫ leftProjection F) ≫ leftBranch m := by
    rw [h]
    exact (congrArg (fun h => b ≫ h) (outer_left_factors m)).trans (by simp only [Category.assoc])
  simpa only [localMap_one, Category.assoc] using
    node_local_left m f g hn a (b ≫ (chartOpen F 1).ι ≫ leftProjection F) hl

include m in
theorem node_outer_right {T : Scheme} (a : T ⟶ (chartOpen F 0).toScheme)
    (b : T ⟶ (chartOpen F 2).toScheme)
    (h : a ≫ (chartOpen F 0).ι = b ≫ (chartOpen F 2).ι) :
    a ≫ localMap (F := F) f g hn 0 = b ≫ localMap (F := F) f g hn 2 := by
  have hl : a ≫ (chartOpen F 0).ι =
      (b ≫ (chartOpen F 2).ι ≫ rightProjection F) ≫ rightBranch m := by
    rw [h]
    exact (congrArg (fun h => b ≫ h) (outer_right_factors m)).trans (by simp only [Category.assoc])
  simpa only [localMap_two, Category.assoc] using
    node_local_right m f g hn a (b ≫ (chartOpen F 2).ι ≫ rightProjection F) hl

include m in
theorem outer_outer {T : Scheme} (a : T ⟶ (chartOpen F 1).toScheme)
    (b : T ⟶ (chartOpen F 2).toScheme)
    (h : a ≫ (chartOpen F 1).ι = b ≫ (chartOpen F 2).ι) :
    a ≫ localMap (F := F) f g hn 1 = b ≫ localMap (F := F) f g hn 2 := by
  have hr : Set.range (a ≫ (chartOpen F 1).ι) ⊆ Set.range (chartOpen F 0).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx := congrArg (fun h => h x) h
    simp only [Scheme.Hom.comp_apply] at hx
    change F.left (inclusion F ((chartOpen F 1).ι (a x))) ∈ ratioOpen 0 ∧
      F.right (inclusion F ((chartOpen F 1).ι (a x))) ∈ ratioOpen 0
    refine ⟨?_, (a x).property.2⟩
    rw [hx]
    exact (b x).property.1
  let z := IsOpenImmersion.lift (chartOpen F 0).ι (a ≫ (chartOpen F 1).ι) hr
  have hz : z ≫ (chartOpen F 0).ι = a ≫ (chartOpen F 1).ι :=
    IsOpenImmersion.lift_fac _ _ _
  exact (node_outer_left m f g hn z a hz).symm.trans
    (node_outer_right m f g hn z b (hz.trans h))

include m in
theorem localMap_compatible {T : Scheme} (i j : Fin 3)
    (a : T ⟶ (chartOpen F i).toScheme) (b : T ⟶ (chartOpen F j).toScheme)
    (h : a ≫ (chartOpen F i).ι = b ≫ (chartOpen F j).ι) :
    a ≫ localMap (F := F) f g hn i = b ≫ localMap (F := F) f g hn j := by
  fin_cases i <;> fin_cases j
  · rw [(cancel_mono (chartOpen F 0).ι).mp h]
  · exact node_outer_left m f g hn a b h
  · exact node_outer_right m f g hn a b h
  · exact (node_outer_left m f g hn b a h.symm).symm
  · rw [(cancel_mono (chartOpen F 1).ι).mp h]
  · exact outer_outer m f g hn a b h
  · exact (node_outer_right m f g hn b a h.symm).symm
  · exact (outer_outer m f g hn b a h.symm).symm
  · rw [(cancel_mono (chartOpen F 2).ι).mp h]

def cover (F : StandardSource) : (CentralFiber F).OpenCover where
  I₀ := Fin 3
  X k := (chartOpen F k).toScheme
  f k := (chartOpen F k).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x ∈ (⨆ k : Fin 3, chartOpen F k) := by rw [chartOpen_cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨k, ⟨⟨x, hk⟩, rfl⟩⟩

def glued : CentralFiber F ⟶ Z :=
  (cover F).glueMorphisms (localMap f g hn) (fun i j =>
    localMap_compatible m f g hn i j _ _ (pullback.condition))

@[reassoc]
theorem chart_glued (k : Fin 3) :
    (chartOpen F k).ι ≫ glued m f g hn = localMap (F := F) f g hn k :=
  (cover F).ι_glueMorphisms _ _ k

@[reassoc]
theorem nodeMap_glued : nodeMap F ≫ glued m f g hn = nodeGlue f g hn := by
  rw [nodeMap, Category.assoc, chart_glued, localMap_zero, Iso.hom_inv_id_assoc]

theorem glued_left : leftBranch m ≫ glued m f g hn = f := by
  apply projective_maps_ext
  intro i
  fin_cases i
  · change (ratioPoint 0).val ≫ (leftBranch m ≫ glued m f g hn) =
      (ratioPoint 0).val ≫ f
    rw [← Category.assoc, ← first_branch m, Category.assoc, nodeMap_glued, nodeGlue_first]
  · change (ratioPoint 1).val ≫ (leftBranch m ≫ glued m f g hn) =
      (ratioPoint 1).val ≫ f
    calc
      (ratioPoint 1).val ≫ (leftBranch m ≫ glued m f g hn) =
          outerMap F 1 (by decide) ≫ glued m f g hn := by
        rw [← Category.assoc, ← outer_left_branch m]
      _ = (outerMap F 1 (by decide) ≫ leftProjection F) ≫ f := by
        simp only [outerMap, Category.assoc, chart_glued, localMap_one]
      _ = (ratioPoint 1).val ≫ f := by
        rw [outer_left_branch m]
        simp only [Category.assoc, leftBranch_projection, leftBranch_projection_assoc,
          Category.id_comp, Category.comp_id]

theorem glued_right : rightBranch m ≫ glued m f g hn = g := by
  apply projective_maps_ext
  intro i
  fin_cases i
  · change (ratioPoint 0).val ≫ (rightBranch m ≫ glued m f g hn) =
      (ratioPoint 0).val ≫ g
    rw [← Category.assoc, ← second_branch m, Category.assoc, nodeMap_glued, nodeGlue_second]
  · change (ratioPoint 1).val ≫ (rightBranch m ≫ glued m f g hn) =
      (ratioPoint 1).val ≫ g
    calc
      (ratioPoint 1).val ≫ (rightBranch m ≫ glued m f g hn) =
          outerMap F 2 (by decide) ≫ glued m f g hn := by
        rw [← Category.assoc, ← outer_right_branch m]
      _ = (outerMap F 2 (by decide) ≫ rightProjection F) ≫ g := by
        simp only [outerMap, Category.assoc, chart_glued, localMap_two]
      _ = (ratioPoint 1).val ≫ g := by
        rw [outer_right_branch m]
        simp only [Category.assoc, rightBranch_projection, rightBranch_projection_assoc,
          Category.id_comp, Category.comp_id]

end Gluing

end CentralCharts

/-- Actual scheme-theoretic central fibre: it is the pushout along the
node, not simply the union of the two sets of closed points. -/
theorem centralFiber_pushout {F : StandardSource} (m : SourceMarks F) :
    ∀ (Z : Scheme) (f g : ProjectiveLine ⟶ Z), marking.map ≫ f = marking.map ≫ g →
      ∃! h : CentralFiber F ⟶ Z, leftBranch m ≫ h = f ∧ rightBranch m ≫ h = g := by
  intro Z f g hn
  refine ⟨CentralCharts.glued m f g hn,
    ⟨CentralCharts.glued_left m f g hn, CentralCharts.glued_right m f g hn⟩, ?_⟩
  intro h hh
  apply CentralCharts.maps_ext m
  · exact hh.1.trans (CentralCharts.glued_left m f g hn).symm
  · exact hh.2.trans (CentralCharts.glued_right m f g hn).symm

theorem centralFiber_hom_ext {F : StandardSource} (m : SourceMarks F)
    {Z : Scheme} {f g : CentralFiber F ⟶ Z}
    (hl : leftBranch m ≫ f = leftBranch m ≫ g)
    (hr : rightBranch m ≫ f = rightBranch m ≫ g) : f = g := by
  obtain ⟨u, _, hu⟩ := centralFiber_pushout m Z (leftBranch m ≫ f)
    (rightBranch m ≫ f) (by rw [← Category.assoc, branches_meet, Category.assoc])
  exact (hu f ⟨rfl, rfl⟩).trans (hu g ⟨hl.symm, hr.symm⟩).symm

theorem centralFiber_branches_closed {F : StandardSource} (m : SourceMarks F) :
    IsClosedImmersion (leftBranch m) ∧ IsClosedImmersion (rightBranch m) := by
  letI : IsProper F.parameter := standardSource_proper F
  letI : IsSeparated (centralBase F) := by
    dsimp [centralBase]
    infer_instance
  let l : CentralFiber F ⟶ ProjectiveLine :=
    pullback.fst F.parameter (scalarPoint 0) ≫ F.left
  let r : CentralFiber F ⟶ ProjectiveLine :=
    pullback.fst F.parameter (scalarPoint 0) ≫ F.right
  have hl : l ≫ P.structureMap = centralBase F := by
    dsimp [l, centralBase]
    rw [Category.assoc, F.left_over, ← Category.assoc,
      pullback.condition, Category.assoc, scalarPoint_overC, Category.comp_id]
  have hr : r ≫ P.structureMap = centralBase F := by
    dsimp [r, centralBase]
    rw [Category.assoc, F.right_over, ← Category.assoc,
      pullback.condition, Category.assoc, scalarPoint_overC, Category.comp_id]
  letI : IsSeparated (l ≫ P.structureMap) := by rw [hl]; infer_instance
  letI : IsSeparated (r ≫ P.structureMap) := by rw [hr]; infer_instance
  letI : IsSeparated l := IsSeparated.of_comp l P.structureMap
  letI : IsSeparated r := IsSeparated.of_comp r P.structureMap
  have hleft : leftBranch m ≫ l = 𝟙 ProjectiveLine := by
    simp only [l, leftBranch, pullback.lift_fst_assoc, m.left_left]
  have hright : rightBranch m ≫ r = 𝟙 ProjectiveLine := by
    simp only [r, rightBranch, pullback.lift_fst_assoc, m.right_right]
  letI : IsClosedImmersion (leftBranch m ≫ l) := by rw [hleft]; infer_instance
  letI : IsClosedImmersion (rightBranch m ≫ r) := by rw [hright]; infer_instance
  exact ⟨IsClosedImmersion.of_comp (leftBranch m) l,
    IsClosedImmersion.of_comp (rightBranch m) r⟩

/-- The total space of a finite locally free sheaf represents sections of
its pullbacks on every test scheme. It is Spec Sym(E.dual), so that the
tautological section has values in E itself. -/
structure TotalBundle {Z : Scheme} {r : ℕ} (E : AlgebraicVectorBundle Z r) where
  space : Scheme
  projection : space ⟶ Z
  tautological : AlgebraicSection (pullbackModule projection E.sheaf)
  universal : ∀ (T : Scheme) (f : T ⟶ Z),
    Function.Bijective (fun h : {h : T ⟶ space // h ≫ projection = f} =>
      pullSection h.val tautological ≫
        (compositionPullback h.val projection f h.property E.sheaf).hom)

/-- The exact tautological-section formula is proved from representability
of the actual section functor, EGA IV4 (18.5.1). The project-specific existential
and its composition-pullback normalization are supplied by the Yoneda proof
in LSSectionRepresentability, rather than admitted in this declaration. -/
theorem _root_.LeBrunSalamon.PublishedInputs.BaseChangeFibers.totalBundle_representation
    {Z : Scheme} {r : ℕ} (E : AlgebraicVectorBundle Z r) :
    ∃ (V : Scheme) (bundleProjection : V ⟶ Z)
      (τ : AlgebraicSection (pullbackModule bundleProjection E.sheaf)),
      ∀ (T : Scheme) (f : T ⟶ Z),
        Function.Bijective (fun h : {h : T ⟶ V // h ≫ bundleProjection = f} =>
          pullSection h.val τ ≫
            (compositionPullback h.val bundleProjection f h.property E.sheaf).hom) := by
  exact LeBrunSalamon.SectionRepresentability.represented_section_data E.locallyFree

/-- Project API wrapper for the total-space representation of a vector bundle. -/
theorem totalBundle_exists {Z : Scheme} {r : ℕ} (E : AlgebraicVectorBundle Z r) :
    Nonempty (TotalBundle E) := by
  obtain ⟨V, bundleProjection, τ, hV⟩ :=
    LeBrunSalamon.PublishedInputs.BaseChangeFibers.totalBundle_representation E
  exact ⟨{ space := V, projection := bundleProjection, tautological := τ, universal := hV }⟩

namespace TotalBundle

variable {Z : Scheme} {r : ℕ} {E : AlgebraicVectorBundle Z r} (V : TotalBundle E)

def mapOfSection {Y : Scheme} (f : Y ⟶ Z)
    (a : AlgebraicSection (pullbackModule f E.sheaf)) :
    {h : Y ⟶ V.space // h ≫ V.projection = f} :=
  Classical.choose ((V.universal Y f).surjective a)

theorem mapOfSection_value {Y : Scheme} (f : Y ⟶ Z)
    (a : AlgebraicSection (pullbackModule f E.sheaf)) :
    pullSection (V.mapOfSection f a).val V.tautological ≫
      (compositionPullback (V.mapOfSection f a).val V.projection f
        (V.mapOfSection f a).property E.sheaf).hom = a :=
  Classical.choose_spec ((V.universal Y f).surjective a)

def representedSection {Y : Scheme} (f : Y ⟶ Z) (h : Y ⟶ V.space)
    (hh : h ≫ V.projection = f) : AlgebraicSection (pullbackModule f E.sheaf) :=
  pullSection h V.tautological ≫
    (compositionPullback h V.projection f hh E.sheaf).hom

theorem representedSection_mapOfSection {Y : Scheme} (f : Y ⟶ Z)
    (a : AlgebraicSection (pullbackModule f E.sheaf)) :
    V.representedSection f (V.mapOfSection f a).val (V.mapOfSection f a).property = a :=
  V.mapOfSection_value f a

theorem mapOfSection_representedSection {Y : Scheme} (f : Y ⟶ Z)
    (h : Y ⟶ V.space) (hh : h ≫ V.projection = f) :
    (V.mapOfSection f (V.representedSection f h hh)).val = h := by
  have he : V.mapOfSection f (V.representedSection f h hh) = ⟨h, hh⟩ := by
    apply (V.universal Y f).injective
    exact V.mapOfSection_value f (V.representedSection f h hh)
  exact congrArg Subtype.val he

theorem mapOfSection_injective {Y : Scheme} (f : Y ⟶ Z)
    {a b : AlgebraicSection (pullbackModule f E.sheaf)}
    (h : (V.mapOfSection f a).val = (V.mapOfSection f b).val) : a = b := by
  let ev : {h : Y ⟶ V.space // h ≫ V.projection = f} →
      AlgebraicSection (pullbackModule f E.sheaf) :=
    fun h => V.representedSection f h.val h.property
  calc
    a = ev (V.mapOfSection f a) := (V.mapOfSection_value f a).symm
    _ = ev (V.mapOfSection f b) := congrArg ev (Subtype.ext h)
    _ = b := V.mapOfSection_value f b

set_option backward.isDefEq.respectTransparency false in
theorem representedSection_naturality {W Y : Scheme}
    (f : Y ⟶ Z) (h : Y ⟶ V.space) (hh : h ≫ V.projection = f)
    (g : W ⟶ Y) (k : W ⟶ Z) (hk : g ≫ f = k) :
    pullSection g (V.representedSection f h hh) ≫
        (compositionPullback g f k hk E.sheaf).hom =
      V.representedSection k (g ≫ h) (by rw [Category.assoc, hh, hk]) := by
  unfold representedSection
  rw [pullSection_naturality, Category.assoc,
    Descent.TotalLine.compositionPullback_assoc g h V.projection f hh (g ≫ h) rfl k hk
      (by rw [Category.assoc, hh, hk]) E.sheaf,
    ← Category.assoc, compositionPullback_sections]

set_option backward.isDefEq.respectTransparency false in
theorem mapOfSection_naturality {W Y : Scheme}
    (f : Y ⟶ Z) (g : W ⟶ Y) (k : W ⟶ Z) (hk : g ≫ f = k)
    (a : AlgebraicSection (pullbackModule f E.sheaf)) :
    g ≫ (V.mapOfSection f a).val =
      (V.mapOfSection k (pullSection g a ≫
        (compositionPullback g f k hk E.sheaf).hom)).val := by
  let h : {h : W ⟶ V.space // h ≫ V.projection = k} :=
    ⟨g ≫ (V.mapOfSection f a).val,
      by rw [Category.assoc, (V.mapOfSection f a).property, hk]⟩
  have he : h = V.mapOfSection k (pullSection g a ≫
      (compositionPullback g f k hk E.sheaf).hom) := by
    apply (V.universal W k).injective
    change V.representedSection k h.val h.property = V.representedSection k _ _
    rw [representedSection_mapOfSection]
    change V.representedSection k (g ≫ (V.mapOfSection f a).val) _ = _
    rw [← V.representedSection_naturality f (V.mapOfSection f a).val
      (V.mapOfSection f a).property g k hk, V.representedSection_mapOfSection]
  exact congrArg Subtype.val he

end TotalBundle

/-- The central nodal map is extracted from the relative-Hom evaluation,
not independently chosen. -/
def centralMap {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) : CentralFiber G.source ⟶ X.variety.scheme :=
  sourceBaseChangeMap G.source (scalarPoint 0) G.hom.toBase
    (G.chart.point.val ≫ G.inclusion) G.centre_base ≫ G.hom.evaluation

theorem centralMap_over {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) : centralMap G ≫ X.variety.structureMap = centralBase G.source := by
  have hc : G.chart.point.val ≫ G.inclusion ≫ G.hom.toBase ≫ affineLineToC =
      𝟙 ComplexBase := by
    simpa only [Category.assoc, scalarPoint_overC] using
      congrArg (fun k => k ≫ affineLineToC) G.centre_base
  simp [centralMap, Category.assoc, G.hom.overC, sourceBaseChangeMap, hc, centralBase]

theorem centralMap_left {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) : leftBranch G.marks ≫ centralMap G = D.first.curve.map := by
  rw [centralMap, ← Category.assoc]
  convert G.leftCentral using 1
  congr 1
  apply pullback.hom_ext
  · simp [leftBranch, sourceBaseChangeMap, Category.assoc]
  · simp [leftBranch, sourceBaseChangeMap, Category.assoc]

theorem centralMap_right {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) : rightBranch G.marks ≫ centralMap G = D.second.curve.map := by
  rw [centralMap, ← Category.assoc]
  convert G.rightCentral using 1
  congr 1
  apply pullback.hom_ext
  · simp [rightBranch, sourceBaseChangeMap, Category.assoc]
  · simp [rightBranch, sourceBaseChangeMap, Category.assoc]

def centralBundle {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) : AlgebraicVectorBundle (CentralFiber G.source) (2*n+1) :=
  pullbackBundle (centralMap G) (intrinsicTangentBundle X.variety)

abbrev ComponentSections {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :=
  CSections P.structureMap (pullbackModule f.curve.map (tangentSheaf X.variety.structureMap))

abbrev CentralSections {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) := CSections (centralBase G.source) (centralBundle G).sheaf

def restrictLeft {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) : CentralSections G →ₗ[ℂ] ComponentSections D.first :=
  (onCSections P.structureMap
    (compositionPullback (leftBranch G.marks) (centralMap G) D.first.curve.map
      (centralMap_left G) (tangentSheaf X.variety.structureMap)).hom).comp
    (pullCSections (leftBranch G.marks) P.structureMap (centralBase G.source)
      (leftBranch_over G.marks) (centralBundle G).sheaf)

def restrictRight {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
    (G : Germ D) : CentralSections G →ₗ[ℂ] ComponentSections D.second :=
  (onCSections P.structureMap
    (compositionPullback (rightBranch G.marks) (centralMap G) D.second.curve.map
      (centralMap_right G) (tangentSheaf X.variety.structureMap)).hom).comp
    (pullCSections (rightBranch G.marks) P.structureMap (centralBase G.source)
      (rightBranch_over G.marks) (centralBundle G).sheaf)

namespace CentralSectionMatchingProof

set_option backward.isDefEq.respectTransparency false

/-- Associativity of the genuine pullback comparisons, including the associativity transport. -/
theorem pullbackComp_assoc {T Y Z W : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (E : OModule W) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E =
      (Scheme.Modules.pullbackComp f g).hom.app (pullbackModule h E) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E ≫
          eqToHom (congrArg (fun k : T ⟶ W => pullbackModule k E)
            (Category.assoc f g h)) := by
  have ha := congrArg (fun a => a.app E)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  have ha' :
      (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app E ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
          (Scheme.Modules.pullbackComp f g).hom.app (pullbackModule h E) ≫
            (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E =
      eqToHom (congrArg (fun k : T ⟶ W => pullbackModule k E)
        (Category.assoc f g h).symm) := by
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
      eqToHom_app] using ha
  have hb := congrArg (fun a =>
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ a ≫
        eqToHom (congrArg (fun k : T ⟶ W => pullbackModule k E)
          (Category.assoc f g h))) ha'
  simpa [Category.assoc, ← Functor.map_comp_assoc] using hb.symm

/-- The same coherence with all three composite morphisms specified by their actual equations. -/
theorem compositionPullback_assoc {T Y Z W : Scheme}
    (f : T ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (j : Y ⟶ W) (hj : g ≫ h = j)
    (k : T ⟶ Z) (hk : f ≫ g = k)
    (l : T ⟶ W) (hl : f ≫ j = l) (hl' : k ≫ h = l) (E : OModule W) :
    (Scheme.Modules.pullback f).map (compositionPullback g h j hj E).hom ≫
        (compositionPullback f j l hl E).hom =
      (compositionPullback f g k hk (pullbackModule h E)).hom ≫
        (compositionPullback k h l hl' E).hom := by
  subst j
  subst k
  subst l
  simpa only [compositionPullback, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id, pullbackModule, Functor.comp_obj]
    using pullbackComp_assoc f g h E

/-- Evaluating after branch restriction follows the same canonical map as evaluating at the node. -/
theorem section_branch {Y Z W : Scheme}
    (p : ComplexBase ⟶ Y) (f : Y ⟶ Z) (g : Z ⟶ W)
    (h : Y ⟶ W) (hh : f ≫ g = h)
    (q : ComplexBase ⟶ Z) (hq : p ≫ f = q)
    (x : ComplexBase ⟶ W) (hx : p ≫ h = x) (hx' : q ≫ g = x)
    {E : OModule W} (s : AlgebraicSection (pullbackModule g E)) :
    pullSection p (pullSection f s ≫ (compositionPullback f g h hh E).hom) ≫
        (compositionPullback p h x hx E).hom =
      pullSection q s ≫ (compositionPullback q g x hx' E).hom := by
  rw [pullSection_naturality, Category.assoc,
    compositionPullback_assoc p f g h hh q hq x hx hx' E,
    ← Category.assoc, compositionPullback_sections]

end CentralSectionMatchingProof

set_option backward.isDefEq.respectTransparency false in
/-- Kernel equality on ACTUAL global sections is the first half of the
normalization exact sequence. It is not inferred just from expected dimensions. -/
theorem centralSections_matching {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) (s : CentralSections G) :
    nodeEvaluation D.first D.node D.firstAtNode (restrictLeft G s) =
      nodeEvaluation D.second D.node D.secondAtNode (restrictRight G s) := by
  let E := tangentSheaf X.variety.structureMap
  let v : AlgebraicSection (pullbackModule (centralMap G) E) := sectionFromValue s
  have hnode : node G.marks ≫ centralMap G = D.node.map := by
    change (marking.map ≫ leftBranch G.marks) ≫ centralMap G = D.node.map
    rw [Category.assoc, centralMap_left, D.firstAtNode]
  have hl := CentralSectionMatchingProof.section_branch
    marking.map (leftBranch G.marks) (centralMap G)
    D.first.curve.map (centralMap_left G)
    (node G.marks) rfl D.node.map D.firstAtNode hnode v
  have hr := CentralSectionMatchingProof.section_branch
    marking.map (rightBranch G.marks) (centralMap G)
    D.second.curve.map (centralMap_right G)
    (node G.marks) (branches_meet G.marks).symm
    D.node.map D.secondAtNode hnode v
  have hv := congrArg (fun a : AlgebraicSection (pullbackModule D.node.map E) =>
    sectionValue a) (hl.trans hr.symm)
  have hleftValue : restrictLeft G s =
      sectionValue (pullSection (leftBranch G.marks) v ≫
        (compositionPullback (leftBranch G.marks) (centralMap G) D.first.curve.map
          (centralMap_left G) E).hom) := by
    change Scheme.Modules.Hom.app
        (compositionPullback (leftBranch G.marks) (centralMap G) D.first.curve.map
          (centralMap_left G) E).hom ⊤
        (sectionValue (pullSection (leftBranch G.marks) v)) = _
    exact (sectionValue_comp _ _).symm
  have hrightValue : restrictRight G s =
      sectionValue (pullSection (rightBranch G.marks) v ≫
        (compositionPullback (rightBranch G.marks) (centralMap G) D.second.curve.map
          (centralMap_right G) E).hom) := by
    change Scheme.Modules.Hom.app
        (compositionPullback (rightBranch G.marks) (centralMap G) D.second.curve.map
          (centralMap_right G) E).hom ⊤
        (sectionValue (pullSection (rightBranch G.marks) v)) = _
    exact (sectionValue_comp _ _).symm
  change Scheme.Modules.Hom.app
      (compositionPullback marking.map D.first.curve.map D.node.map D.firstAtNode E).hom ⊤
      (sectionValue (pullSection marking.map (sectionFromValue (restrictLeft G s)))) =
    Scheme.Modules.Hom.app
      (compositionPullback marking.map D.second.curve.map D.node.map D.secondAtNode E).hom ⊤
      (sectionValue (pullSection marking.map (sectionFromValue (restrictRight G s))))
  rw [hleftValue, hrightValue]
  simp only [sectionFromValue_sectionValue]
  simpa only [sectionValue_comp] using hv


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
def normalizationRestriction {n : ℕ} {X : ContactFanoManifold n}
    {D : Lines.SuitablePair X} (G : Smoothing.Germ D) : Normalization.CentralSections G →ₗ[ℂ]
      matchingSections (Lines.nodeEvaluation D.first D.node D.firstAtNode)
        (Lines.nodeEvaluation D.second D.node D.secondAtNode) where
  toFun s := ⟨(Normalization.restrictLeft G s, Normalization.restrictRight G s),
    Normalization.centralSections_matching G s⟩
  map_add' := by intro a b; apply Subtype.ext; simp
  map_smul' := by intro c a; apply Subtype.ext; simp

namespace RestrictionProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem left_section {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) (s : CentralSections G) :
    pullSection (leftBranch G.marks) (sectionFromValue s) ≫
        (compositionPullback (leftBranch G.marks) (centralMap G) D.first.curve.map
          (centralMap_left G) (tangentSheaf X.variety.structureMap)).hom =
      sectionFromValue (restrictLeft G s) := by
  apply (sectionValue_bijective _).injective
  rw [sectionValue_comp, sectionFromValue_spec]
  rfl

theorem right_section {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) (s : CentralSections G) :
    pullSection (rightBranch G.marks) (sectionFromValue s) ≫
        (compositionPullback (rightBranch G.marks) (centralMap G) D.second.curve.map
          (centralMap_right G) (tangentSheaf X.variety.structureMap)).hom =
      sectionFromValue (restrictRight G s) := by
  apply (sectionValue_bijective _).injective
  rw [sectionValue_comp, sectionFromValue_spec]
  rfl

/-- Equality of the two node evaluations is equality of the actual
pulled-back bundle sections after the prescribed composition comparisons. -/
theorem node_sections {n : ℕ} {X : ContactFanoManifold n}
    (D : SuitablePair X)
    (v : matchingSections (nodeEvaluation D.first D.node D.firstAtNode)
      (nodeEvaluation D.second D.node D.secondAtNode)) :
    pullSection marking.map (sectionFromValue v.val.1) ≫
        (compositionPullback marking.map D.first.curve.map D.node.map
          D.firstAtNode (tangentSheaf X.variety.structureMap)).hom =
      pullSection marking.map (sectionFromValue v.val.2) ≫
        (compositionPullback marking.map D.second.curve.map D.node.map
          D.secondAtNode (tangentSheaf X.variety.structureMap)).hom := by
  apply (sectionValue_bijective _).injective
  change nodeEvaluation D.first D.node D.firstAtNode v.val.1 =
    nodeEvaluation D.second D.node D.secondAtNode v.val.2
  exact v.property

end RestrictionProof

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- SOURCE sm:normalization. The prescribed map is restriction to both
branches; an arbitrary isomorphism of equal-dimensional spaces is excluded. -/
theorem normalizationRestriction_bijective {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) :
    Function.Bijective (normalizationRestriction G) := by
  obtain ⟨V⟩ := totalBundle_exists (intrinsicTangentBundle X.variety)
  constructor
  · intro a b hab
    have hl : restrictLeft G a = restrictLeft G b :=
      congrArg (fun v => v.val.1) hab
    have hr : restrictRight G a = restrictRight G b :=
      congrArg (fun v => v.val.2) hab
    have hm : (V.mapOfSection (centralMap G) (sectionFromValue a)).val =
        (V.mapOfSection (centralMap G) (sectionFromValue b)).val := by
      apply centralFiber_hom_ext G.marks
      · exact (V.mapOfSection_naturality (centralMap G) (leftBranch G.marks)
          D.first.curve.map (centralMap_left G) (sectionFromValue a)).trans
          ((congrArg (fun t : AlgebraicSection (pullbackModule D.first.curve.map
              (tangentSheaf X.variety.structureMap)) =>
            (V.mapOfSection D.first.curve.map t).val)
            ((RestrictionProof.left_section G a).trans
              ((congrArg (fun z : ComponentSections D.first =>
                sectionFromValue (E := pullbackModule D.first.curve.map
                  (tangentSheaf X.variety.structureMap)) z) hl).trans
                (RestrictionProof.left_section G b).symm))).trans
            (V.mapOfSection_naturality (centralMap G) (leftBranch G.marks)
              D.first.curve.map (centralMap_left G) (sectionFromValue b)).symm)
      · exact (V.mapOfSection_naturality (centralMap G) (rightBranch G.marks)
          D.second.curve.map (centralMap_right G) (sectionFromValue a)).trans
          ((congrArg (fun t : AlgebraicSection (pullbackModule D.second.curve.map
              (tangentSheaf X.variety.structureMap)) =>
            (V.mapOfSection D.second.curve.map t).val)
            ((RestrictionProof.right_section G a).trans
              ((congrArg (fun z : ComponentSections D.second =>
                sectionFromValue (E := pullbackModule D.second.curve.map
                  (tangentSheaf X.variety.structureMap)) z) hr).trans
                (RestrictionProof.right_section G b).symm))).trans
            (V.mapOfSection_naturality (centralMap G) (rightBranch G.marks)
              D.second.curve.map (centralMap_right G) (sectionFromValue b)).symm)
    have hs := V.mapOfSection_injective (centralMap G) hm
    simpa only [sectionFromValue_spec] using
      congrArg (fun s : AlgebraicSection (centralBundle G).sheaf => sectionValue s) hs
  · intro v
    let l := V.mapOfSection D.first.curve.map (sectionFromValue v.val.1)
    let r := V.mapOfSection D.second.curve.map (sectionFromValue v.val.2)
    have hnode : marking.map ≫ l.val = marking.map ≫ r.val := by
      change marking.map ≫
          (V.mapOfSection D.first.curve.map (sectionFromValue v.val.1)).val =
        marking.map ≫
          (V.mapOfSection D.second.curve.map (sectionFromValue v.val.2)).val
      exact (V.mapOfSection_naturality D.first.curve.map marking.map D.node.map
        D.firstAtNode (sectionFromValue v.val.1)).trans
        ((congrArg (fun t : AlgebraicSection (pullbackModule D.node.map
            (tangentSheaf X.variety.structureMap)) =>
          (V.mapOfSection D.node.map t).val) (RestrictionProof.node_sections D v)).trans
          (V.mapOfSection_naturality D.second.curve.map marking.map D.node.map
            D.secondAtNode (sectionFromValue v.val.2)).symm)
    obtain ⟨g, hg, _⟩ := centralFiber_pushout G.marks V.space l.val r.val hnode
    have ho : g ≫ V.projection = centralMap G := by
      apply centralFiber_hom_ext G.marks
      · rw [← Category.assoc, hg.1, l.property, centralMap_left]
      · rw [← Category.assoc, hg.2, r.property, centralMap_right]
    let a := V.representedSection (centralMap G) g ho
    have ha : (V.mapOfSection (centralMap G) a).val = g :=
      V.mapOfSection_representedSection (centralMap G) g ho
    have hleft : restrictLeft G (sectionValue a) = v.val.1 := by
      have hnatural := V.mapOfSection_naturality (centralMap G) (leftBranch G.marks)
        D.first.curve.map (centralMap_left G) a
      rw [ha, hg.1] at hnatural
      have hs : pullSection (leftBranch G.marks) a ≫
          (compositionPullback (leftBranch G.marks) (centralMap G) D.first.curve.map
            (centralMap_left G) (tangentSheaf X.variety.structureMap)).hom =
          sectionFromValue v.val.1 :=
        V.mapOfSection_injective D.first.curve.map hnatural.symm
      have hvalues := congrArg sectionValue
        (RestrictionProof.left_section G (sectionValue a))
      rw [sectionFromValue_sectionValue, hs, sectionFromValue_spec,
        sectionFromValue_spec] at hvalues
      exact hvalues.symm
    have hright : restrictRight G (sectionValue a) = v.val.2 := by
      have hnatural := V.mapOfSection_naturality (centralMap G) (rightBranch G.marks)
        D.second.curve.map (centralMap_right G) a
      rw [ha, hg.2] at hnatural
      have hs : pullSection (rightBranch G.marks) a ≫
          (compositionPullback (rightBranch G.marks) (centralMap G) D.second.curve.map
            (centralMap_right G) (tangentSheaf X.variety.structureMap)).hom =
          sectionFromValue v.val.2 :=
        V.mapOfSection_injective D.second.curve.map hnatural.symm
      have hvalues := congrArg sectionValue
        (RestrictionProof.right_section G (sectionValue a))
      rw [sectionFromValue_sectionValue, hs, sectionFromValue_spec,
        sectionFromValue_spec] at hvalues
      exact hvalues.symm
    refine ⟨sectionValue a, ?_⟩
    apply Subtype.ext
    exact Prod.ext hleft hright

end Normalization
end LeBrunSalamon.Construction
end
