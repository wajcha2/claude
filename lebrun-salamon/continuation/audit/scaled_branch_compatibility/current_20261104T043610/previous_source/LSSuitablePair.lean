import LSScaledVelocityDifferential

/-!
## The original suitable pair from actual Hom geometry

The construction uses the published general-point direction geometry,
the ordinary cone-addition theorem, actual bounded Hom families, and
generic smoothness. Its two positive spaces and its Levi test are the
original ones in SuitablePair.

Source preparation only; compilation remains deferred to the final check.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.SuitablePairProof

open DirectionCones VelocityCoordinates IntrinsicVelocityRange
open ContactVelocityFactorization

variable {n : ℕ} (X : ContactFanoManifold n)
variable (H : HomSpacePresentation P X.variety)
variable (D : HomDegree.Open P marking X.variety H X.contact.sequence.line 1)
variable (x : ComplexPoint X.variety) (C : GlobalVelocity.TargetChart X.variety x)
variable (A : Charts.PointedAffine)

def homOfScaled
    (k : PointsOver A.scheme A.toC (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x)) :
    PointsOver A.scheme A.toC (FixedNodeHom.parameter P marking H x) (FixedNodeHom.toC P marking H x) :=
  ⟨k.val ≫ (ScaledVelocities.asFixedHom X H D x).val, by
    rw [Category.assoc, (ScaledVelocities.asFixedHom X H D x).property, k.property]⟩

/-- Pullback of the constructed global scaled coordinate is its literal
scalar function times the actual universal velocity comorphism. -/
theorem pull_scaledCoordinate
    (k : PointsOver A.scheme A.toC (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x))
    (i : Fin (dimension (n := n) + 1)) :
    k.val.appTop (ScaledVelocities.coordinates X H D x C i) =
      k.val.appTop (ScaledVelocities.scalar X H D x) *
        ScaledVelocityDifferential.coordinate H x C A (homOfScaled X H D x A k) i := by
  rw [ScaledVelocities.coordinates, map_mul]
  congr 1
  simp only [ScaledVelocities.unscaledFunctions, AlgHom.comp_apply,
    GlobalCoordinates.comorphism_apply, ScaledVelocities.velocity,
    ScaledVelocityDifferential.coordinate, velocityFunctions, schemeComorphism_apply,
    chartVelocity, homOfScaled, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

theorem scaled_point_is_freeLine
    (k : PointsOver A.scheme A.toC (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x)) :
    ∃ (f : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map),
      A.point.val ≫ (homOfScaled X H D x A k).val =
        (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val := by
  let t : PointsOver ComplexBase (𝟙 ComplexBase)
      (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x) :=
    ⟨A.point.val ≫ k.val, by rw [Category.assoc, k.property, A.point.property]⟩
  obtain ⟨f, hf, ht⟩ := ScaledVelocities.point_is_freeLine X H D x t
  exact ⟨f, hf, by simpa only [t, homOfScaled, Category.assoc] using ht⟩

variable (j : PointsOver A.scheme A.toC
  (VelocityAdditionFamily.parameter X H D x C) (VelocityAdditionFamily.toC X H D x C))

def firstParameter : PointsOver A.scheme A.toC
    (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x) :=
  ⟨j.val ≫ VelocityAdditionFamily.firstScaled X H D x C, by
    rw [Category.assoc, VelocityAdditionFamily.firstScaled_overC, j.property]⟩

def secondParameter : PointsOver A.scheme A.toC
    (ScaledVelocities.parameter X H D x) (ScaledVelocities.toC X H D x) :=
  ⟨j.val ≫ VelocityAdditionFamily.secondScaled X H D x C, by
    rw [Category.assoc, VelocityAdditionFamily.secondScaled_overC, j.property]⟩

def firstHom := homOfScaled X H D x A (firstParameter X H D x C A j)
def secondHom := homOfScaled X H D x A (secondParameter X H D x C A j)

def firstScalar : A.Ring :=
  (firstParameter X H D x C A j).val.appTop (ScaledVelocities.scalar X H D x)

def secondScalar : A.Ring :=
  (secondParameter X H D x C A j).val.appTop (ScaledVelocities.scalar X H D x)

def sumComorphism : MvPolynomial (Fin (dimension (n := n) + 1)) ℂ →ₐ[ℂ] A.Ring :=
  schemeComorphism A (j.val ≫ VelocityAdditionFamily.morphism X H D x C)
    (by rw [Category.assoc, VelocityAdditionFamily.morphism_overC, j.property])

theorem sumComorphism_X (i : Fin (dimension (n := n) + 1)) :
    sumComorphism X H D x C A j (MvPolynomial.X i) =
      firstScalar X H D x C A j *
        ScaledVelocityDifferential.coordinate H x C A (firstHom X H D x C A j) i +
      secondScalar X H D x C A j *
        ScaledVelocityDifferential.coordinate H x C A (secondHom X H D x C A j) i := by
  change (j.val ≫ VelocityAdditionFamily.morphism X H D x C).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (dimension (n := n) + 1)) ℂ))).inv
        (MvPolynomial.X i)) = _
  have h : (j.val ≫ VelocityAdditionFamily.morphism X H D x C).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (dimension (n := n) + 1)) ℂ))).inv
        (MvPolynomial.X i)) =
      (firstParameter X H D x C A j).val.appTop (ScaledVelocities.coordinates X H D x C i) +
      (secondParameter X H D x C A j).val.appTop (ScaledVelocities.coordinates X H D x C i) := by
    simp only [VelocityAdditionFamily.morphism, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      GlobalCoordinates.map_X, VelocityAdditionFamily.sumCoordinates, map_add,
      VelocityAdditionFamily.firstCoordinates, VelocityAdditionFamily.secondCoordinates,
      SectionAlgebra.onFunctionsTop_apply, firstParameter, secondParameter,
      VelocityAdditionFamily.firstScaled, VelocityAdditionFamily.secondScaled]
  rw [h, pull_scaledCoordinate, pull_scaledCoordinate]
  rfl

variable (f g : FreeLine X)
variable (hf : marking.map ≫ f.curve.map = x.map)
variable (hg : marking.map ≫ g.curve.map = x.map)
variable (hatf : A.point.val ≫ (firstHom X H D x C A j).val =
  (HomDeformation.fixedCenter P H marking x f.curve.map f.curve.overC hf).val)
variable (hatg : A.point.val ≫ (secondHom X H D x C A j).val =
  (HomDeformation.fixedCenter P H marking x g.curve.map g.curve.overC hg).val)

include hatf hatg in
/-- The point was selected inside the actual nonorthogonality open;
its nonzero value is the original Levi pairing on the original scaled
source-tangent vectors. -/
theorem center_nonorthogonal :
    NonzeroLeviPair X x
      (nodeDifferential f x hf
        (A.evaluation (firstScalar X H D x C A j) • SourceTangent.sourceVector marking))
      (nodeDifferential g x hg
        (A.evaluation (secondScalar X H D x C A j) • SourceTangent.sourceVector marking)) := by
  let U := VelocityAdditionFamily.nonorthogonalOpen X H D x C
  let p : PointsOver ComplexBase (𝟙 ComplexBase) (VelocityAdditionFamily.pairParameter X H D x)
      (VelocityAdditionFamily.pairToC X H D x) :=
    ⟨A.point.val ≫ j.val ≫ U.ι, by
      simp only [Category.assoc]
      change A.point.val ≫ (j.val ≫ VelocityAdditionFamily.toC X H D x C) = 𝟙 ComplexBase
      rw [j.property, A.point.property]⟩
  have hp : p.val (IsLocalRing.closedPoint ℂ) ∈ U :=
    (j.val (A.point.val (IsLocalRing.closedPoint ℂ))).property
  have hne : GlobalCoordinates.evaluation p (VelocityAdditionFamily.pairingFunction X H D x C) ≠ 0 :=
    (GlobalCoordinates.point_mem_basicOpen p (VelocityAdditionFamily.pairingFunction X H D x C)).mp hp
  have hfirst (i : Fin (dimension (n := n) + 1)) :
      GlobalCoordinates.evaluation p (VelocityAdditionFamily.firstCoordinates X H D x C i) =
        A.evaluation (firstScalar X H D x C A j *
          ScaledVelocityDifferential.coordinate H x C A (firstHom X H D x C A j) i) := by
    have he := pull_scaledCoordinate X H D x C A (firstParameter X H D x C A j) i
    apply Eq.trans _ (congrArg A.evaluation he)
    simp only [p, GlobalCoordinates.evaluation, VelocityAdditionFamily.firstCoordinates,
      SectionAlgebra.onFunctionsTop_apply, firstParameter, VelocityAdditionFamily.firstScaled,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Charts.PointedAffine.evaluation]
  have hsecond (i : Fin (dimension (n := n) + 1)) :
      GlobalCoordinates.evaluation p (VelocityAdditionFamily.secondCoordinates X H D x C i) =
        A.evaluation (secondScalar X H D x C A j *
          ScaledVelocityDifferential.coordinate H x C A (secondHom X H D x C A j) i) := by
    have he := pull_scaledCoordinate X H D x C A (secondParameter X H D x C A j) i
    apply Eq.trans _ (congrArg A.evaluation he)
    simp only [p, GlobalCoordinates.evaluation, VelocityAdditionFamily.secondCoordinates,
      SectionAlgebra.onFunctionsTop_apply, secondParameter, VelocityAdditionFamily.secondScaled,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Charts.PointedAffine.evaluation]
  have hpair : ConePairing.pairing (omega X x C)
      (contactFrame X x C (A.evaluation (firstScalar X H D x C A j) • ScaledVelocities.nodeVector X x f hf))
      (contactFrame X x C (A.evaluation (secondScalar X H D x C A j) • ScaledVelocities.nodeVector X x g hg)) ≠ 0 := by
    unfold VelocityAdditionFamily.pairingFunction at hne
    rw [ConePairing.pairing_map] at hne
    simpa only [hfirst, hsecond, map_mul,
      ScaledVelocityDifferential.coordinate_value H x C A (firstHom X H D x C A j) f hf hatf,
      ScaledVelocityDifferential.coordinate_value H x C A (secondHom X H D x C A j) g hg hatg,
      map_smul, Pi.smul_apply, smul_eq_mul] using hne
  rw [pairing_omega] at hpair
  have hlevi := (LeviFiberGeometry.scalarLevi_ne_zero_iff X x
    (LeviFiberGeometry.lineFiberFrame X x)
    (A.evaluation (firstScalar X H D x C A j) • ScaledVelocities.nodeVector X x f hf)
    (A.evaluation (secondScalar X H D x C A j) • ScaledVelocities.nodeVector X x g hg)).mp hpair
  simpa only [map_smul] using hlevi

/-- Smoothness of the actual sum supplies all contact directions. Each
of its two differentiated summands lands in the original positive space. -/
def from_smooth_chart (hs : Smooth (j.val ≫ VelocityAdditionFamily.morphism X H D x C)) :
    SuitablePair X := by
  obtain ⟨f, hf, hatf⟩ := scaled_point_is_freeLine X H D x A (firstParameter X H D x C A j)
  obtain ⟨g, hg, hatg⟩ := scaled_point_is_freeLine X H D x A (secondParameter X H D x C A j)
  let d₁ := ScaledVelocityDifferential.differential H x C A (firstHom X H D x C A j) f hf hatf
    (firstScalar X H D x C A j)
  let d₂ := ScaledVelocityDifferential.differential H x C A (secondHom X H D x C A j) g hg hatg
    (secondScalar X H D x C A j)
  have hsurj : Function.Surjective (Infinitesimal.tangentMap (sumComorphism X H D x C A j) A.evaluation) :=
    SuitableAffineSource.tangentMap_surjective A (j.val ≫ VelocityAdditionFamily.morphism X H D x C)
      (by rw [Category.assoc, VelocityAdditionFamily.morphism_overC, j.property]) hs
  have hsum : Function.Surjective (d₁.coprod d₂) := by
    intro v
    obtain ⟨E, hE⟩ := GlobalCoordinates.polynomialTangent_coordinates
      (A.evaluation.comp (sumComorphism X H D x C A j)) (contactFrame X x C v)
    obtain ⟨t, ht⟩ := hsurj E
    refine ⟨(t, t), ?_⟩
    apply (contactFrame X x C).injective
    funext i
    change contactFrame X x C (d₁ t + d₂ t) i = contactFrame X x C v i
    rw [map_add, Pi.add_apply,
      ScaledVelocityDifferential.differential_coordinate,
      ScaledVelocityDifferential.differential_coordinate, ← map_add]
    rw [← sumComorphism_X]
    exact (congrArg (fun z : Infinitesimal.Tangent _ _ => z.val (MvPolynomial.X i)) ht).trans (hE i)
  exact SuitablePairAlgebra.suitablePair_of_surjective_variation x f g hf hg
    (A.evaluation (firstScalar X H D x C A j) • SourceTangent.sourceVector marking)
    (A.evaluation (secondScalar X H D x C A j) • SourceTangent.sourceVector marking)
    (center_nonorthogonal X H D x C A j f g hf hg hatf hatg) d₁ d₂
    (ScaledVelocityDifferential.differential_positive H x C A (firstHom X H D x C A j) f hf hatf
      (firstScalar X H D x C A j))
    (ScaledVelocityDifferential.differential_positive H x C A (secondHom X H D x C A j) g hg hatg
      (secondScalar X H D x C A j)) hsum

/-- A nonzero actual selected vector belongs to one of the genuine
projective components. No component is assumed to span the contact plane. -/
theorem vector_component (V : PublishedDirections.LegendrianDirections X x C)
    (a : contactPlane X x) (ha0 : a ≠ 0)
    (ha : a ∈ projectiveCone (selectedDirections (fun _ : FreeLine X => True) x)) :
    ∃ K : V.directions.Component,
      contactFrame X x C a ∈ V.directions.componentConePoints (contactFrame X x C) K := by
  have hd : Projectivization.mk ℂ a ha0 ∈ selectedDirections (fun _ : FreeLine X => True) x :=
    (mem_projectiveCone_of_ne_zero _ a ha0).mp ha
  rw [← V.realizes] at hd
  obtain ⟨z, hz⟩ := hd
  obtain ⟨K, hK⟩ := V.directions.direction_in_component (contactFrame X x C) z (IsLocalRing.closedPoint ℂ)
  refine ⟨K, a, Or.inr ⟨ha0, ?_⟩, rfl⟩
  exact hz ▸ hK

/-- All the geometric hypotheses here are exactly the published
general-point direction geometry. Dominance, Hom coverage, smoothness,
and the original suitable pair are constructed ordinarily. -/
theorem of_spanning_legendrian
    (V : PublishedDirections.LegendrianDirections X x C)
    (hspan : Submodule.span ℂ
      (projectiveCone (selectedDirections (fun _ : FreeLine X => True) x)) = ⊤) :
    Nonempty (SuitablePair X) := by
  have hlevi : SuitablePairAlgebra.contactLevi X x ≠ 0 :=
    LeviFiberGeometry.contactLevi_ne_zero_of_homFiberEvaluation_injective X x
      (StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree
        X.contact.sequence.distribution X.contact.sequence.line.sheaf x.map)
  obtain ⟨a, ha, b, hb, hab⟩ := SuitablePairAlgebra.exists_nonorthogonal_generators
    (SuitablePairAlgebra.contactLevi X x) hlevi
    (projectiveCone (selectedDirections (fun _ : FreeLine X => True) x))
    (projectiveCone (selectedDirections (fun _ : FreeLine X => True) x)) hspan hspan
  have ha0 := SuitablePairAlgebra.nonorthogonal_left_ne_zero (SuitablePairAlgebra.contactLevi X x) hab
  have hb0 := SuitablePairAlgebra.nonorthogonal_right_ne_zero (SuitablePairAlgebra.contactLevi X x) hab
  obtain ⟨K, hK⟩ := vector_component X x C V a ha0 ha
  obtain ⟨E, hE⟩ := vector_component X x C V b hb0 hb
  have hpair : ConePairing.pairing (omega X x C) (contactFrame X x C a) (contactFrame X x C b) ≠ 0 := by
    rw [pairing_omega]
    exact fun he => hab ((LeviFiberGeometry.scalarLevi_eq_zero_iff X x
      (LeviFiberGeometry.lineFiberFrame X x) a b).mp he)
  obtain ⟨H⟩ := homSpacePresentation_exists P X.variety (contactFano_hasProjectiveEmbedding X)
  obtain ⟨D⟩ := HomDegree.StandardInputs.degree_open P marking X.variety
    (contactFano_hasProjectiveEmbedding X) H X.contact.sequence.line (contactFano_contactLine_ample X) 1
  have hdom := VelocityAdditionFamily.morphism_denseRange X H D x C V K E
    (contactFrame X x C a) (contactFrame X x C b) hK hE hpair
  obtain ⟨A, j, hj⟩ := SuitableAffineSource.exists_smooth_chart
    (VelocityAdditionFamily.toC X H D x C) (VelocityAdditionFamily.morphism X H D x C)
    (VelocityAdditionFamily.morphism_overC X H D x C) hdom
  exact ⟨from_smooth_chart X H D x C A j hj⟩

/-- The n=1 branch uses the original two-dimensional symplectic argument
and union spanning, with no higher-dimensional Legendrian theorem. -/
theorem dimensionThree_of_spanning (X : ContactFanoManifold 1) (x : ComplexPoint X.variety)
    (hspan : Submodule.span ℂ
      (projectiveCone (selectedDirections (fun _ : FreeLine X => True) x)) = ⊤) :
    Nonempty (SuitablePair X) := by
  have hlevi := LeviFiberGeometry.contactLevi_ne_zero_of_homFiberEvaluation_injective X x
    (StandardInputs.BundleGeometry.homFiberEvaluation_injective_of_locallyFree
      X.contact.sequence.distribution X.contact.sequence.line.sheaf x.map)
  obtain ⟨D⟩ := SelectedPair.nonorthogonalPair_exists_of_selected_spanning X
    (fun _ : FreeLine X => True) x hlevi hspan
  exact ⟨ContactPositive.dimensionThree_suitablePair_of_tangents X x D.first D.second
    D.first_at D.second_at D.first_parameter D.second_parameter D.nonorthogonal⟩

/-- This final assembly discharges the n>=2 and n=1 cases separately
from the corrected published leaves. -/
theorem exists_from_published_geometry (X : ContactFanoManifold n)
    (hPic : HasPrimitiveContactPicard X.contact) : Nonempty (SuitablePair X) := by
  obtain ⟨U, hU, hspan⟩ := PublishedDirections.StandardInputs.general_selectedDirections_span X hPic
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨q, hq, hqU⟩ := RelativeGenericSmoothness.exists_point_in_nonempty_open
      X.variety.structureMap U hU.nonempty
    let x : ComplexPoint X.variety := ⟨q, hq⟩
    exact dimensionThree_of_spanning X x (hspan x hqU)
  · have hn : 2 ≤ n := by have hn := X.positiveContactDimension; omega
    obtain ⟨V, hV, hlegendrian⟩ := PublishedDirections.StandardInputs.general_legendrianDirections X hn hPic
    have hUV : ((U ⊓ V : X.variety.scheme.Opens) : Set X.variety.scheme).Nonempty := by
      obtain ⟨z, hzV, hzU⟩ := hU.inter_open_nonempty (V : Set X.variety.scheme) V.isOpen hV.nonempty
      exact ⟨z, hzU, hzV⟩
    obtain ⟨q, hq, hqUV⟩ := RelativeGenericSmoothness.exists_point_in_nonempty_open
      X.variety.structureMap (U ⊓ V) hUV
    let x : ComplexPoint X.variety := ⟨q, hq⟩
    obtain ⟨C⟩ := GlobalVelocity.targetChart_exists X.variety x
    obtain ⟨E⟩ := hlegendrian x hqUV.2 C
    exact of_spanning_legendrian X x C E (hspan x hqUV.1)

end LeBrunSalamon.Construction.Lines.SuitablePairProof

end

namespace LeBrunSalamon.Construction.Lines

/-- Manuscript claim; prove via the covering line family, corrected
Legendrian direction theorem, and lines:cone-addition, including n=1. -/
theorem suitablePair_exists {n : ℕ} (X : ContactFanoManifold n)
    (hPic : HasPrimitiveContactPicard X.contact) : Nonempty (SuitablePair X) := by
  exact SuitablePairProof.exists_from_published_geometry X hPic

end LeBrunSalamon.Construction.Lines

#print axioms LeBrunSalamon.Construction.Lines.suitablePair_exists
