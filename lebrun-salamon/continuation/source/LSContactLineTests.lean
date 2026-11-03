import LSGenericSheets

/-!
The actual two-axis contact-line family used in the branch test.  Its
evaluation maps are smooth and dominant because they are the prescribed
line evaluation after base change.  The source is proved to be the actual
P1 family over H times X; no unproved family or transversality predicate
is included in these definitions.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction.Lines
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.StandardInputs

/-- Generic smooth-connected integrality over the actual algebraically
closed base. Stacks 0363 (33.7.6), 056T (33.25.4), and 033N
(28.7.7), applied after each field extension. No contact data. -/
theorem smooth_connected_complex_geometricallyIntegral {Y : Scheme}
    (sY : Y ⟶ ComplexBase) [Smooth sY] [ConnectedSpace Y] :
    GeometricallyIntegral sY := by sorry

/-- **Published input (exact specialization).** In a connected family of
line bundles on the trivial projective-line family, the fiber degree is
constant.  This is the projective-line specialization of constancy of Euler
characteristic in a proper flat finitely presented family (Stacks Project,
Lemma 36.32.2, Tag 0B9T), together with `χ(O(d)) = d + 1` on `P¹` and the
Picard classification of `P¹`. -/
theorem _root_.LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.familyDegreeConstant
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {S : Scheme} (sS : S ⟶ ComplexBase)
    [LocallyOfFiniteType sS] [ConnectedSpace S]
    (L : LineBundle (RationalSourceOver P S sS))
    (a b : PointsOver ComplexBase (𝟙 ComplexBase) S sS) :
    projectiveLineDegree P p
      (pullbackLine
        (pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ a.val)
          (by simp only [Category.id_comp, Category.assoc, a.property,
            Category.comp_id])) L) =
    projectiveLineDegree P p
      (pullbackLine
        (pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ b.val)
          (by simp only [Category.id_comp, Category.assoc, b.property,
            Category.comp_id])) L) := by
  sorry

/-- Project wrapper for fiber-degree constancy. -/
theorem projectiveLineFamily_degree_constant
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {S : Scheme} (sS : S ⟶ ComplexBase)
    [LocallyOfFiniteType sS] [ConnectedSpace S]
    (L : LineBundle (RationalSourceOver P S sS))
    (a b : PointsOver ComplexBase (𝟙 ComplexBase) S sS) :
    projectiveLineDegree P p
      (pullbackLine
        (pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ a.val)
          (by simp only [Category.id_comp, Category.assoc, a.property,
            Category.comp_id])) L) =
    projectiveLineDegree P p
      (pullbackLine
        (pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ b.val)
          (by simp only [Category.id_comp, Category.assoc, b.property,
            Category.comp_id])) L) :=
  LeBrunSalamon.PublishedInputs.ProjectiveLineGeometry.familyDegreeConstant
    P p sS L a b

end LeBrunSalamon.StandardInputs

namespace LeBrunSalamon.Construction.Descent.LineTests

variable {n : ℕ} {X : ContactFanoManifold n} (H : CoveringFamily X)

local instance : Smooth P.structureMap :=
  smoothProperComplexVariety_smooth (projectiveLineVariety P)

local instance : IsProper P.structureMap := (projectiveLine_smoothProper P).2.1

abbrev Parameter : Scheme := pullback H.toC X.variety.structureMap

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.Parameter :=
  @LeBrunSalamon.Construction.Descent.LineTests.Parameter

def parameterToC : H.Parameter ⟶ ComplexBase :=
  pullback.fst H.toC X.variety.structureMap ≫ H.toC

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.parameterToC :=
  @LeBrunSalamon.Construction.Descent.LineTests.parameterToC

/-- This presentation makes the first evaluation an actual base change. -/
abbrev Source : Scheme := pullback H.evaluation (firstProjection X.variety.structureMap)

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.Source :=
  @LeBrunSalamon.Construction.Descent.LineTests.Source

def toFamily : H.Source ⟶ RationalSourceOver P H.parameter H.toC :=
  pullback.fst H.evaluation (firstProjection X.variety.structureMap)

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.toFamily :=
  @LeBrunSalamon.Construction.Descent.LineTests.toFamily

def firstEvaluation : H.Source ⟶ Square X :=
  pullback.snd H.evaluation (firstProjection X.variety.structureMap)

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.firstEvaluation :=
  @LeBrunSalamon.Construction.Descent.LineTests.firstEvaluation

def sourcePoint : H.Source ⟶ ProjectiveLine :=
  H.toFamily ≫ pullback.fst P.structureMap H.toC

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.sourcePoint :=
  @LeBrunSalamon.Construction.Descent.LineTests.sourcePoint

def otherPoint : H.Source ⟶ X.variety.scheme :=
  H.firstEvaluation ≫ secondProjection X.variety.structureMap

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.otherPoint :=
  @LeBrunSalamon.Construction.Descent.LineTests.otherPoint

theorem parameter_commutes :
    (H.toFamily ≫ pullback.snd P.structureMap H.toC) ≫ H.toC =
      H.otherPoint ≫ X.variety.structureMap := by
  calc
    _ = H.toFamily ≫ pullback.fst P.structureMap H.toC ≫ P.structureMap := by
      rw [Category.assoc, ← pullback.condition]
    _ = H.toFamily ≫ H.evaluation ≫ X.variety.structureMap := by
      rw [H.overC]
    _ = H.firstEvaluation ≫ firstProjection X.variety.structureMap ≫
        X.variety.structureMap := by
      change pullback.fst H.evaluation (firstProjection X.variety.structureMap) ≫
          H.evaluation ≫ X.variety.structureMap =
        pullback.snd H.evaluation (firstProjection X.variety.structureMap) ≫
          firstProjection X.variety.structureMap ≫ X.variety.structureMap
      simpa only [Category.assoc] using
        congrArg (fun k : H.Source ⟶ X.variety.scheme => k ≫ X.variety.structureMap)
          (pullback.condition (f := H.evaluation)
            (g := firstProjection X.variety.structureMap))
    _ = H.otherPoint ≫ X.variety.structureMap := by
      change H.firstEvaluation ≫ pullback.fst X.variety.structureMap
          X.variety.structureMap ≫ X.variety.structureMap =
        (H.firstEvaluation ≫ pullback.snd X.variety.structureMap
          X.variety.structureMap) ≫ X.variety.structureMap
      simpa only [Category.assoc] using
        congrArg (fun k : Square X ⟶ ComplexBase => H.firstEvaluation ≫ k)
          (pullback.condition (f := X.variety.structureMap)
            (g := X.variety.structureMap))

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.parameter_commutes :=
  @LeBrunSalamon.Construction.Descent.LineTests.parameter_commutes

def projection : H.Source ⟶ H.Parameter :=
  pullback.lift (H.toFamily ≫ pullback.snd P.structureMap H.toC)
    H.otherPoint H.parameter_commutes

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.projection :=
  @LeBrunSalamon.Construction.Descent.LineTests.projection

@[reassoc (attr := simp)]
theorem projection_fst :
    H.projection ≫ pullback.fst H.toC X.variety.structureMap =
      H.toFamily ≫ pullback.snd P.structureMap H.toC :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem projection_snd :
    H.projection ≫ pullback.snd H.toC X.variety.structureMap = H.otherPoint :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem source_overC : H.sourcePoint ≫ P.structureMap =
    H.projection ≫ H.parameterToC := by
  change (H.toFamily ≫ pullback.fst P.structureMap H.toC) ≫ P.structureMap =
    H.projection ≫ (pullback.fst H.toC X.variety.structureMap ≫ H.toC)
  calc
    _ = H.toFamily ≫ pullback.snd P.structureMap H.toC ≫ H.toC := by
      simpa only [Category.assoc] using
        congrArg
          (fun k : RationalSourceOver P H.parameter H.toC ⟶ ComplexBase =>
            H.toFamily ≫ k)
          (pullback.condition (f := P.structureMap) (g := H.toC))
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k : H.Source ⟶ H.parameter => k ≫ H.toC)
          (projection_fst H).symm

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.source_overC :=
  @LeBrunSalamon.Construction.Descent.LineTests.source_overC

/-- The source is the entire P1 product over the parameter scheme. -/
theorem source_isPullback :
    IsPullback H.sourcePoint H.projection P.structureMap H.parameterToC := by
  apply IsPullback.mk' H.source_overC
  · intro T a b h₁ h₂
    have hfamily : a ≫ H.toFamily = b ≫ H.toFamily := by
      apply pullback.hom_ext
      · simpa only [sourcePoint, Category.assoc] using h₁
      · simpa only [Category.assoc, projection_fst] using
          congrArg (fun k => k ≫ pullback.fst H.toC X.variety.structureMap) h₂
    apply pullback.hom_ext
    · exact hfamily
    · apply pullback.hom_ext
      · simpa only [toFamily, firstEvaluation, Category.assoc, pullback.condition] using
          congrArg (fun k => k ≫ H.evaluation) hfamily
      · simpa only [Category.assoc, projection_snd, otherPoint,
          firstEvaluation, secondProjection] using
          congrArg
            (fun k : T ⟶ H.Parameter => k ≫ pullback.snd H.toC X.variety.structureMap) h₂
  · intro T a b hab
    let u : T ⟶ RationalSourceOver P H.parameter H.toC :=
      pullback.lift a (b ≫ pullback.fst H.toC X.variety.structureMap)
        (by simpa only [parameterToC, Category.assoc] using hab)
    let v : T ⟶ Square X :=
      pullback.lift (u ≫ H.evaluation)
        (b ≫ pullback.snd H.toC X.variety.structureMap) (by
          rw [Category.assoc, H.overC, ← Category.assoc, pullback.lift_fst]
          calc
            a ≫ P.structureMap = b ≫ H.parameterToC := hab
            _ = _ := by simp only [parameterToC, Category.assoc, pullback.condition])
    let w : T ⟶ H.Source := pullback.lift u v (by simp only [v, pullback.lift_fst])
    refine ⟨w, ?_, ?_⟩
    · simp only [w, sourcePoint, toFamily, Category.assoc, pullback.lift_fst_assoc,
        u, pullback.lift_fst]
    · apply pullback.hom_ext
      · simp only [Category.assoc, projection_fst, w, toFamily,
          pullback.lift_fst_assoc, u, pullback.lift_snd]
      · simp only [Category.assoc, projection_snd, otherPoint, firstEvaluation, w,
          pullback.lift_snd_assoc, v, secondProjection, pullback.lift_snd]

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.source_isPullback :=
  @LeBrunSalamon.Construction.Descent.LineTests.source_isPullback

instance parameter_smooth : Smooth H.parameterToC := by
  letI : Smooth H.toC := H.smooth
  change Smooth (pullback.fst H.toC X.variety.structureMap ≫ H.toC)
  infer_instance

instance projection_proper : IsProper H.projection :=
  MorphismProperty.of_isPullback H.source_isPullback inferInstance

instance projection_smooth : Smooth H.projection :=
  MorphismProperty.of_isPullback H.source_isPullback inferInstance

instance firstEvaluation_smooth : Smooth H.firstEvaluation := by
  letI : Smooth H.evaluation := H.smoothEvaluation
  change Smooth (pullback.snd H.evaluation (firstProjection X.variety.structureMap))
  infer_instance

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.firstEvaluation_smooth :=
  @LeBrunSalamon.Construction.Descent.LineTests.firstEvaluation_smooth

theorem firstEvaluation_dominant : DenseRange H.firstEvaluation := by
  change Dense (Set.range (pullback.snd H.evaluation
    (firstProjection X.variety.structureMap)))
  rw [Scheme.Pullback.range_snd]
  exact H.dominantEvaluation.preimage (firstProjection X.variety.structureMap).isOpenMap

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.firstEvaluation_dominant :=
  @LeBrunSalamon.Construction.Descent.LineTests.firstEvaluation_dominant

def axisEvaluation : Axis → (H.Source ⟶ Square X)
  | .first => H.firstEvaluation
  | .second => H.firstEvaluation ≫ swapSelfProduct X.variety.structureMap

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.axisEvaluation :=
  @LeBrunSalamon.Construction.Descent.LineTests.axisEvaluation

instance axisEvaluation_smooth (axis : Axis) : Smooth (H.axisEvaluation axis) := by
  cases axis
  · exact H.firstEvaluation_smooth
  · let e : Square X ≅ Square X :=
      ⟨swapSelfProduct X.variety.structureMap, swapSelfProduct X.variety.structureMap,
        swap_square _, swap_square _⟩
    letI : Smooth H.firstEvaluation := H.firstEvaluation_smooth
    letI : IsIso e.hom := e.isIso_hom
    change Smooth (H.firstEvaluation ≫ e.hom)
    infer_instance

theorem axisEvaluation_dominant (axis : Axis) : DenseRange (H.axisEvaluation axis) := by
  cases axis
  · exact H.firstEvaluation_dominant
  · have hs : Function.Surjective (swapSelfProduct X.variety.structureMap) := by
      intro x
      refine ⟨swapSelfProduct X.variety.structureMap x, ?_⟩
      rw [← Scheme.Hom.comp_apply, swap_square]
      rfl
    exact hs.denseRange.comp H.firstEvaluation_dominant
      (swapSelfProduct X.variety.structureMap).continuous

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.axisEvaluation_dominant :=
  @LeBrunSalamon.Construction.Descent.LineTests.axisEvaluation_dominant

def parameterPoint (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) :
    PointsOver ComplexBase (𝟙 ComplexBase) H.Parameter H.parameterToC :=
  ⟨pullback.lift t.val y.map (by rw [t.property, y.overC]), by
    simp only [parameterToC, Category.assoc, pullback.lift_fst_assoc, t.property]⟩

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.parameterPoint :=
  @LeBrunSalamon.Construction.Descent.LineTests.parameterPoint

def fiberInclusion (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) : ProjectiveLine ⟶ H.Source :=
  pullback.lift
    (pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val)
      (by simp only [Category.id_comp, Category.assoc, t.property, Category.comp_id]))
    (testLine (H.lineAt t) y .first) (by
      rw [← H.lineAt_spec]
      simp only [testLine, firstProjection, pullback.lift_fst])

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.fiberInclusion :=
  @LeBrunSalamon.Construction.Descent.LineTests.fiberInclusion

@[reassoc (attr := simp)]
theorem fiberInclusion_sourcePoint
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) : H.fiberInclusion t y ≫ H.sourcePoint = 𝟙 _ := by
  simp only [fiberInclusion, sourcePoint, toFamily, Category.assoc,
    pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem fiberInclusion_projection
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) :
    H.fiberInclusion t y ≫ H.projection = P.structureMap ≫ (H.parameterPoint t y).val := by
  apply pullback.hom_ext
  · simp only [Category.assoc, projection_fst, fiberInclusion, toFamily,
      pullback.lift_fst_assoc, pullback.lift_snd, parameterPoint, pullback.lift_fst]
  · simp only [Category.assoc, projection_snd, otherPoint, firstEvaluation,
      fiberInclusion, pullback.lift_snd_assoc, testLine, secondProjection,
      pullback.lift_snd, parameterPoint]

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.fiberInclusion_projection :=
  @LeBrunSalamon.Construction.Descent.LineTests.fiberInclusion_projection

@[reassoc (attr := simp)]
theorem fiberInclusion_evaluation
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) (axis : Axis) :
    H.fiberInclusion t y ≫ H.axisEvaluation axis = testLine (H.lineAt t) y axis := by
  cases axis
  · exact pullback.lift_snd _ _ _
  · change H.fiberInclusion t y ≫ H.firstEvaluation ≫
        swapSelfProduct X.variety.structureMap = _
    rw [← Category.assoc]
    rw [show H.fiberInclusion t y ≫ H.firstEvaluation =
      testLine (H.lineAt t) y .first from pullback.lift_snd _ _ _]
    apply pullback.hom_ext <;>
      simp only [Category.assoc, firstProjection, secondProjection,
        testLine, swapSelfProduct, pullback.lift_fst, pullback.lift_snd]

/-- Meeting a given open is an actual open condition on the parameter
scheme, because the entire source projection is smooth and hence open. -/
def meetingOpen (axis : Axis) (U : (Square X).Opens) : H.Parameter.Opens :=
  ⟨H.projection '' ((H.axisEvaluation axis) ⁻¹' (U : Set (Square X))),
    H.projection.isOpenMap _ (U.isOpen.preimage (H.axisEvaluation axis).continuous)⟩

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.meetingOpen :=
  @LeBrunSalamon.Construction.Descent.LineTests.meetingOpen

theorem meetingOpen_nonempty (axis : Axis) (U : (Square X).Opens)
    (hU : (U : Set (Square X)).Nonempty) :
    (H.meetingOpen axis U : Set H.Parameter).Nonempty := by
  obtain ⟨z, hz⟩ := (H.axisEvaluation_dominant axis).inter_open_nonempty _ U.isOpen hU
  obtain ⟨a, rfl⟩ := hz.2
  exact ⟨H.projection a, a, hz.1, rfl⟩

theorem meets_of_meetsOpen
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) (axis : Axis) (U : (Square X).Opens)
    (h : MeetsOpen (testLine (H.lineAt t) y axis) U) :
    (H.parameterPoint t y).val (IsLocalRing.closedPoint ℂ) ∈ H.meetingOpen axis U := by
  obtain ⟨a, ha⟩ := h
  refine ⟨H.fiberInclusion t y a, ?_, ?_⟩
  · change H.axisEvaluation axis (H.fiberInclusion t y a) ∈ U
    rw [← Scheme.Hom.comp_apply, fiberInclusion_evaluation]
    exact ha
  · rw [← Scheme.Hom.comp_apply, fiberInclusion_projection, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _

theorem variety_integral : IsIntegral X.variety.scheme := by
  letI : GeometricallyIntegral X.variety.structureMap :=
    LeBrunSalamon.StandardInputs.smooth_connected_complex_geometricallyIntegral
      X.variety.structureMap
  exact GeometricallyIntegral.isIntegral_of_subsingleton X.variety.structureMap

theorem square_integral : IsIntegral (Square X) := by
  letI : IsIntegral X.variety.scheme := variety_integral (X := X)
  letI : IsLocallyNoetherian X.variety.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian X.variety.structureMap
  letI : GeometricallyIntegral X.variety.structureMap :=
    LeBrunSalamon.StandardInputs.smooth_connected_complex_geometricallyIntegral
      X.variety.structureMap
  dsimp [Square, SelfProduct]
  infer_instance

instance parameter_irreducible : IrreducibleSpace H.Parameter := by
  letI : IrreducibleSpace H.parameter := H.irreducible
  letI : GeometricallyIntegral X.variety.structureMap :=
    LeBrunSalamon.StandardInputs.smooth_connected_complex_geometricallyIntegral
      X.variety.structureMap
  change IrreducibleSpace (pullback H.toC X.variety.structureMap : Scheme)
  infer_instance

def sourceProductIso : H.Source ≅ RationalSourceOver P H.Parameter H.parameterToC :=
  H.source_isPullback.isoPullback

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.sourceProductIso :=
  @LeBrunSalamon.Construction.Descent.LineTests.sourceProductIso

def productFiber
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) :
    ProjectiveLine ⟶ RationalSourceOver P H.Parameter H.parameterToC :=
  pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ (H.parameterPoint t y).val)
    (by simp only [Category.id_comp, Category.assoc,
      (H.parameterPoint t y).property, Category.comp_id])

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.productFiber :=
  @LeBrunSalamon.Construction.Descent.LineTests.productFiber

@[reassoc]
theorem productFiber_inclusion
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) :
    H.productFiber t y ≫ H.sourceProductIso.inv = H.fiberInclusion t y := by
  apply H.source_isPullback.hom_ext
  · simp only [sourceProductIso, Category.assoc, IsPullback.isoPullback_inv_fst,
      productFiber, pullback.lift_fst, fiberInclusion_sourcePoint]
  · simp only [sourceProductIso, Category.assoc, IsPullback.isoPullback_inv_snd,
      productFiber, pullback.lift_snd, fiberInclusion_projection]

/-- The degree belongs to the actual test-line pullback, and is constant
over all complex parameters of the same axis. -/
theorem testLine_degree_constant (M : LineBundle (Square X)) (axis : Axis)
    (t₁ t₂ : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y₁ y₂ : ComplexPoint X.variety) :
    projectiveLineDegree P marking (pullbackLine (testLine (H.lineAt t₁) y₁ axis) M) =
      projectiveLineDegree P marking (pullbackLine (testLine (H.lineAt t₂) y₂ axis) M) := by
  let f := H.sourceProductIso.inv ≫ H.axisEvaluation axis
  let L := pullbackLine f M
  have h (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
      (y : ComplexPoint X.variety) :
      H.productFiber t y ≫ f = testLine (H.lineAt t) y axis := by
    dsimp [f]
    rw [← Category.assoc, productFiber_inclusion, fiberInclusion_evaluation]
  have d (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
      (y : ComplexPoint X.variety) :
      projectiveLineDegree P marking (pullbackLine (H.productFiber t y) L) =
        projectiveLineDegree P marking (pullbackLine (testLine (H.lineAt t) y axis) M) :=
    projectiveLineDegree_iso P marking _ _
      (compositionPullback (H.productFiber t y) f
        (testLine (H.lineAt t) y axis) (h t y) M.sheaf)
  exact (d t₁ y₁).symm.trans
    ((LeBrunSalamon.StandardInputs.projectiveLineFamily_degree_constant P marking
      H.parameterToC L (H.parameterPoint t₁ y₁) (H.parameterPoint t₂ y₂)).trans
      (d t₂ y₂))

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.testLine_degree_constant :=
  @LeBrunSalamon.Construction.Descent.LineTests.testLine_degree_constant

def familyFiber (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) :
    ProjectiveLine ⟶ RationalSourceOver P H.parameter H.toC :=
  pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ t.val)
    (by simp only [Category.id_comp, Category.assoc, t.property, Category.comp_id])

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.familyFiber :=
  @LeBrunSalamon.Construction.Descent.LineTests.familyFiber

@[reassoc (attr := simp)]
theorem familyFiber_evaluation
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC) :
    H.familyFiber t ≫ H.evaluation = (H.lineAt t).curve.map :=
  (H.lineAt_spec t).symm

/-- Actual members of the covering line family detect a line-bundle
section. The proof uses all complex points of its smooth source. -/
theorem section_zero_of_lines (M : LineBundle X.variety.scheme)
    (a : AlgebraicSection M.sheaf)
    (ha : ∀ t, pullSection (H.lineAt t).curve.map a = 0) : a = 0 := by
  let s : RationalSourceOver P H.parameter H.toC ⟶ ComplexBase :=
    pullback.fst P.structureMap H.toC ≫ P.structureMap
  letI : Smooth H.toC := H.smooth
  letI : Smooth s := by dsimp [s]; infer_instance
  letI : AlgebraicGeometry.IsReduced (RationalSourceOver P H.parameter H.toC) :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced s
  have hzero : pullSection H.evaluation a = 0 := by
    apply ComplexPointSectionDetection.section_eq s (pullbackBundle H.evaluation M)
    intro q
    rw [FullFamilyDiagonalProof.pullSection_zero]
    let t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC :=
      ⟨q.val ≫ pullback.snd P.structureMap H.toC, by
        simpa only [s, Category.assoc, ← pullback.condition] using q.property⟩
    let p := q.val ≫ pullback.fst P.structureMap H.toC
    have hp : p ≫ P.structureMap = 𝟙 ComplexBase := by
      simpa only [p, s, Category.assoc] using q.property
    have hq : q.val = p ≫ H.familyFiber t := by
      apply pullback.hom_ext
      · simp only [familyFiber, Category.assoc, pullback.lift_fst, Category.comp_id, p]
      · symm
        calc
          (p ≫ H.familyFiber t) ≫ pullback.snd P.structureMap H.toC =
              (p ≫ P.structureMap) ≫ t.val := by
            simp only [familyFiber, Category.assoc, pullback.lift_snd]
          _ = t.val := by rw [hp, Category.id_comp]
          _ = _ := rfl
    apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff q.val H.evaluation a).2
    rw [hq, Category.assoc, familyFiber_evaluation]
    apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff p (H.lineAt t).curve.map a).1
    rw [ha, FullFamilyDiagonalProof.pullSection_zero]
  letI : AlgebraicGeometry.IsReduced X.variety.scheme :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced X.variety.structureMap
  apply dominant_pullSection_injective H.evaluation H.dominantEvaluation
    (fun U => inferInstance) M
  simpa only [FullFamilyDiagonalProof.pullSection_zero] using hzero

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.section_zero_of_lines :=
  @LeBrunSalamon.Construction.Descent.LineTests.section_zero_of_lines

theorem negative_degree_section_zero (L : LineBundle ProjectiveLine)
    (hL : projectiveLineDegree P marking L < 0) (a : AlgebraicSection L.sheaf) : a = 0 := by
  obtain ⟨e⟩ := projectiveLineDegree_spec P marking L
  have hz := negativeTwist_noSections P marking (projectiveLineDegree P marking L)
    hL (a ≫ e.hom)
  apply (cancel_mono e.hom).mp
  simpa only [zero_comp] using hz

theorem linePowerInt_curve_degree (f : FreeLine X) (L : LineBundle X.variety.scheme)
    (k : ℤ) :
    degreeOnCurve P marking f.curve.toParametrizedCurve (linePowerInt L k) =
      k * degreeOnCurve P marking f.curve.toParametrizedCurve L := by
  cases k with
  | ofNat k =>
      obtain ⟨e⟩ := linePower_pullback f.curve.map L k
      exact (projectiveLineDegree_iso P marking _ _ e).trans
        (projectiveLineDegree_power P marking (pullbackLine f.curve.map L) k)
  | negSucc k =>
      obtain ⟨e⟩ := linePower_pullback f.curve.map (dualLine L) (k + 1)
      obtain ⟨ed⟩ := dualSheaf_pullback f.curve.map L.locallyFree
      change projectiveLineDegree P marking
        (pullbackLine f.curve.map (linePower (dualLine L) (k + 1))) = _
      rw [projectiveLineDegree_iso P marking _ _ e, projectiveLineDegree_power,
        projectiveLineDegree_iso P marking (pullbackLine f.curve.map (dualLine L))
          (dualLine (pullbackLine f.curve.map L)) ed,
        projectiveLineDegree_dual]
      simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one, mul_neg, neg_mul] <;> rfl

theorem degree_of_picard_power (M : LineBundle X.variety.scheme) (k : ℤ)
    (e : M.sheaf ≅ (linePowerInt X.contact.sequence.line k).sheaf) (f : FreeLine X) :
    degreeOnCurve P marking f.curve.toParametrizedCurve M = k := by
  rw [show degreeOnCurve P marking f.curve.toParametrizedCurve M =
      degreeOnCurve P marking f.curve.toParametrizedCurve
        (linePowerInt X.contact.sequence.line k) from
    projectiveLineDegree_iso P marking _ _ ((Scheme.Modules.pullback f.curve.map).mapIso e),
    linePowerInt_curve_degree, f.degreeOne, mul_one]

include H in
/-- Nonnegative exponent is forced by the actual line family, with no
intersection number supplied as an additional premise. -/
theorem picard_exponent_nonnegative (M : LineBundle X.variety.scheme) (k : ℤ)
    (e : M.sheaf ≅ (linePowerInt X.contact.sequence.line k).sheaf)
    (a : AlgebraicSection M.sheaf) (ha : a ≠ 0) : 0 ≤ k := by
  by_contra hk
  have hnegative : k < 0 := lt_of_not_ge hk
  apply ha
  apply H.section_zero_of_lines M a
  intro t
  refine negative_degree_section_zero (pullbackLine (H.lineAt t).curve.map M)
    ?_ (pullSection (H.lineAt t).curve.map a)
  change degreeOnCurve P marking (H.lineAt t).curve.toParametrizedCurve M < 0
  rw [degree_of_picard_power M k e (H.lineAt t)]
  exact hnegative

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.picard_exponent_nonnegative :=
  @LeBrunSalamon.Construction.Descent.LineTests.picard_exponent_nonnegative

/-- A scalar section on the proper integral target is determined by its
value at one actual complex point. -/
theorem unit_section_zero_of_point (a : AlgebraicSection (structureModule X.variety.scheme))
    (x : ComplexPoint X.variety) (hx : pullSection x.map a = 0) : a = 0 := by
  letI : IsIntegral X.variety.scheme := variety_integral (X := X)
  obtain ⟨c, hc⟩ := (ProperSections.constants_bijective X.variety.structureMap).surjective
    (sectionValue a)
  have hvalue : x.map.appTop (sectionValue a) = 0 := by
    rw [← FrameEvaluation.unit_pullSection_value, hx]
    simp [sectionValue]
  rw [← hc, complexConstants_naturality x.map (𝟙 ComplexBase)
    X.variety.structureMap x.overC] at hvalue
  have hc0 : c = 0 := by
    rw [complexConstants_apply_top] at hvalue
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c = 0 at hvalue
    have h := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom z) hvalue
    simpa only [Iso.inv_hom_id_apply, map_zero] using h
  apply (sectionValue_bijective _).injective
  rw [← hc, hc0, map_zero]
  simp [sectionValue]

include H in
/-- An actual nonzero section with an actual zero has strictly positive
Picard exponent; the zero-exponent case uses properness, not a label. -/
theorem picard_exponent_positive (M : LineBundle X.variety.scheme) (k : ℤ)
    (e : M.sheaf ≅ (linePowerInt X.contact.sequence.line k).sheaf)
    (a : AlgebraicSection M.sheaf) (ha : a ≠ 0)
    (x : ComplexPoint X.variety) (hx : pullSection x.map a = 0) : 0 < k := by
  have hk := H.picard_exponent_nonnegative M k e a ha
  have hk0 : k ≠ 0 := by
    intro hk0
    subst k
    let b : AlgebraicSection (structureModule X.variety.scheme) := a ≫ e.hom
    have hb : pullSection x.map b = 0 := by
      dsimp [b]
      rw [pullSection_map, hx, zero_comp]
    have hz := unit_section_zero_of_point b x hb
    apply ha
    apply (cancel_mono e.hom).mp
    simpa only [b, zero_comp] using hz
  omega

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.picard_exponent_positive :=
  @LeBrunSalamon.Construction.Descent.LineTests.picard_exponent_positive

/-- Restriction to either whole factor through an actual complex point. -/
def axisFiber (y : ComplexPoint X.variety) : Axis → (X.variety.scheme ⟶ Square X)
  | .first => pullback.lift (𝟙 _) (X.variety.structureMap ≫ y.map)
      (by simp only [Category.id_comp, Category.assoc, y.overC, Category.comp_id])
  | .second => pullback.lift (X.variety.structureMap ≫ y.map) (𝟙 _)
      (by simp only [Category.id_comp, Category.assoc, y.overC, Category.comp_id])

theorem testLine_factor (f : FreeLine X) (y : ComplexPoint X.variety) (axis : Axis) :
    f.curve.map ≫ axisFiber y axis = testLine f y axis := by
  have hbase : f.curve.map ≫ X.variety.structureMap ≫ y.map =
      P.structureMap ≫ y.map :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k : ProjectiveLine ⟶ ComplexBase => k ≫ y.map) f.curve.overC)
  cases axis <;> apply pullback.hom_ext <;>
    simp only [Category.assoc, axisFiber, testLine, firstProjection, secondProjection,
      pullback.lift_fst, pullback.lift_snd, Category.comp_id, hbase]

theorem axisFiber_points (x y : ComplexPoint X.variety) :
    x.map ≫ axisFiber y .first = y.map ≫ axisFiber x .second := by
  have hxbase : x.map ≫ X.variety.structureMap ≫ y.map = y.map :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : ComplexBase ⟶ ComplexBase => k ≫ y.map) x.overC).trans
        (Category.id_comp y.map))
  have hybase : y.map ≫ X.variety.structureMap ≫ x.map = x.map :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : ComplexBase ⟶ ComplexBase => k ≫ x.map) y.overC).trans
        (Category.id_comp x.map))
  apply pullback.hom_ext <;>
    simp only [Category.assoc, axisFiber, firstProjection, secondProjection,
      pullback.lift_fst, pullback.lift_snd, Category.comp_id, hxbase, hybase]

/-- Every nonzero square section has a nonzero value at an actual ordered
pair of complex points. Both projections are those of the given square. -/
theorem square_section_nonzero_pair (M : LineBundle (Square X))
    (a : AlgebraicSection M.sheaf) (ha : a ≠ 0) :
    ∃ x y : ComplexPoint X.variety,
      pullSection x.map (pullSection (axisFiber y .first) a) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply ha
  let s : Square X ⟶ ComplexBase :=
    firstProjection X.variety.structureMap ≫ X.variety.structureMap
  letI : Smooth s := by dsimp [s]; infer_instance
  letI : AlgebraicGeometry.IsReduced (Square X) :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced s
  apply ComplexPointSectionDetection.section_eq s M a 0
  intro q
  rw [FullFamilyDiagonalProof.pullSection_zero]
  let x : ComplexPoint X.variety :=
    ⟨q.val ≫ firstProjection X.variety.structureMap,
      by simpa only [s, Category.assoc] using q.property⟩
  let y : ComplexPoint X.variety :=
    ⟨q.val ≫ secondProjection X.variety.structureMap, by
      simpa only [s, Category.assoc, firstProjection, secondProjection,
        ← pullback.condition] using q.property⟩
  have hq : q.val = x.map ≫ axisFiber y .first := by
    apply pullback.hom_ext
    · simp only [axisFiber, firstProjection, Category.assoc, pullback.lift_fst,
        Category.comp_id, x]
    · calc
        q.val ≫ pullback.snd X.variety.structureMap X.variety.structureMap = y.map := rfl
        _ = (x.map ≫ X.variety.structureMap) ≫ y.map :=
          (Category.id_comp y.map).symm.trans
            (congrArg (fun k : ComplexBase ⟶ ComplexBase => k ≫ y.map) x.overC.symm)
        _ = (x.map ≫ axisFiber y .first) ≫
            pullback.snd X.variety.structureMap X.variety.structureMap := by
          simp only [axisFiber, Category.assoc, pullback.lift_snd]
  rw [hq]
  exact (FullFamilyDiagonalProof.pullSection_comp_zero_iff x.map
    (axisFiber y .first) a).1 (h x y)

/-- The two-axis choice is an actual restriction argument. If the first
factor through a zero is identically zero, a nonzero value elsewhere
forces a nontrivial section with a zero on the opposite factor. -/
theorem twoAxis_nonzero_with_zero (M : LineBundle (Square X))
    (a : AlgebraicSection M.sheaf) (ha : a ≠ 0)
    (x₀ y₀ : ComplexPoint X.variety)
    (hz : pullSection x₀.map (pullSection (axisFiber y₀ .first) a) = 0) :
    ∃ (axis : Axis) (y : ComplexPoint X.variety),
      pullSection (axisFiber y axis) a ≠ 0 ∧
        ∃ x : ComplexPoint X.variety,
          pullSection x.map (pullSection (axisFiber y axis) a) = 0 := by
  classical
  by_cases hfirst : pullSection (axisFiber y₀ .first) a = 0
  · obtain ⟨x₁, y₁, hnonzero⟩ := square_section_nonzero_pair M a ha
    refine ⟨.second, x₁, ?_, y₀, ?_⟩
    · intro hsecond
      apply hnonzero
      apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff x₁.map
        (axisFiber y₁ .first) a).2
      rw [axisFiber_points]
      apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff y₁.map
        (axisFiber x₁ .second) a).1
      rw [hsecond, FullFamilyDiagonalProof.pullSection_zero]
    · apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff y₀.map
        (axisFiber x₁ .second) a).2
      rw [← axisFiber_points]
      apply (FullFamilyDiagonalProof.pullSection_comp_zero_iff x₁.map
        (axisFiber y₀ .first) a).1
      rw [hfirst, FullFamilyDiagonalProof.pullSection_zero]
  · exact ⟨.first, y₀, hfirst, x₀, hz⟩

/-- One of the two actual test-line axes has positive degree against a
nonzero square section with a zero. The same axis works for every member
and every constant point, by the actual family degree comparison. -/
theorem twoAxis_positive_degree (hPic : HasPrimitiveContactPicard X.contact)
    (M : LineBundle (Square X)) (a : AlgebraicSection M.sheaf) (ha : a ≠ 0)
    (x₀ y₀ : ComplexPoint X.variety)
    (hz : pullSection x₀.map (pullSection (axisFiber y₀ .first) a) = 0) :
    ∃ axis : Axis,
      ∀ (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
        (y : ComplexPoint X.variety),
        0 < projectiveLineDegree P marking
          (pullbackLine (testLine (H.lineAt t) y axis) M) := by
  obtain ⟨axis, y, hnonzero, x, hzero⟩ := twoAxis_nonzero_with_zero M a ha x₀ y₀ hz
  let L := pullbackLine (axisFiber y axis) M
  obtain ⟨k, ⟨e⟩, _⟩ := hPic L
  have hk : 0 < k := H.picard_exponent_positive L k e
    (pullSection (axisFiber y axis) a) hnonzero x hzero
  refine ⟨axis, ?_⟩
  intro t z
  rw [H.testLine_degree_constant M axis t t z y]
  have hdegree := degree_of_picard_power L k e (H.lineAt t)
  have hcomparison := projectiveLineDegree_iso P marking
    (pullbackLine (H.lineAt t).curve.map L)
    (pullbackLine (testLine (H.lineAt t) y axis) M)
    (compositionPullback (H.lineAt t).curve.map (axisFiber y axis)
      (testLine (H.lineAt t) y axis) (testLine_factor (H.lineAt t) y axis) M.sheaf)
  change projectiveLineDegree P marking (pullbackLine (H.lineAt t).curve.map L) = k
    at hdegree
  rw [hcomparison] at hdegree
  rw [hdegree]
  exact hk

/-- A nonzero value in an actual rank-one complex fiber is invertible.
The scalar is obtained from the actual unit-sheaf endomorphism. -/
theorem point_pullSection_isIso_of_ne_zero {Y : Scheme}
    (L : LineBundle Y) (a : AlgebraicSection L.sheaf)
    (x : ComplexBase ⟶ Y) (hx : pullSection x a ≠ 0) :
    IsIso (pullSection x a) := by
  obtain ⟨e⟩ := ProjectiveCoordinateProof.line_at_complex_point_trivial L x
  obtain ⟨c, hc⟩ := ProjectiveCoordinateProof.scalarUnitSection_surjective
    (pullSection x a ≫ e.hom)
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hx
    apply (cancel_mono e.hom).mp
    rw [← hc, hc0, ProjectiveCoordinateProof.scalarUnitSection_eq_scalarEnd,
      map_zero, GlobalScalars.scalarEnd_zero, zero_comp]
  letI : IsIso (pullSection x a ≫ e.hom) := by
    rw [← hc]
    exact ProjectiveCoordinateProof.scalarUnitSection_isIso c hc0
  exact IsIso.of_isIso_comp_right (pullSection x a) e.hom

/-- The maximal invertibility open has its expected meaning at the
actual complex-valued points. -/
theorem point_mem_nonvanishing_iff {Y : Scheme}
    (L : LineBundle Y) (a : AlgebraicSection L.sheaf)
    (x : ComplexBase ⟶ Y) :
    x (IsLocalRing.closedPoint ℂ) ∈ nonvanishingOpen L a ↔
      pullSection x a ≠ 0 := by
  constructor
  · intro hx hz
    have hx' : IsLocalRing.closedPoint ℂ ∈
        nonvanishingOpen (pullbackLine x L) (pullSection x a) := by
      rw [← nonvanishingOpen_pullback]
      exact hx
    rw [hz, nonvanishingOpen_zero] at hx'
    exact hx'
  · intro hx
    have htop := (nonvanishingOpen_eq_top_iff
      (pullbackLine x L) (pullSection x a)).mpr
        (point_pullSection_isIso_of_ne_zero L a x hx)
    have hp : IsLocalRing.closedPoint ℂ ∈
        nonvanishingOpen (pullbackLine x L) (pullSection x a) := by
      rw [htop]
      trivial
    rw [← nonvanishingOpen_pullback] at hp
    exact hp

theorem nonvanishing_nonempty {Y : Scheme} (sY : Y ⟶ ComplexBase)
    [LocallyOfFiniteType sY] [AlgebraicGeometry.IsReduced Y]
    (L : LineBundle Y) (a : AlgebraicSection L.sheaf) (ha : a ≠ 0) :
    (nonvanishingOpen L a : Set Y).Nonempty := by
  by_contra h
  apply ha
  apply ComplexPointSectionDetection.section_eq sY L a 0
  intro q
  rw [FullFamilyDiagonalProof.pullSection_zero]
  by_contra hq
  exact h ⟨q.val (IsLocalRing.closedPoint ℂ),
    (point_mem_nonvanishing_iff L a q.val).mpr hq⟩

/-- Positive actual degree forces a zero of every section at an actual
complex point of P1. A section with no zeros would trivialize the line. -/
theorem positive_degree_exists_zero (L : LineBundle ProjectiveLine)
    (hL : 0 < projectiveLineDegree P marking L)
    (a : AlgebraicSection L.sheaf) :
    ∃ p : ProjectiveLinePoint P, pullSection p.map a = 0 := by
  classical
  by_contra h
  push_neg at h
  have htop : nonvanishingOpen L a = ⊤ := by
    apply LeBrunSalamon.PhaseNine.ClosedPointGenerationProof.open_eq_top_of_complexPoints
      (projectiveLineVariety P)
    intro x
    exact (point_mem_nonvanishing_iff L a x.map).mpr (h ⟨x.map, x.overC⟩)
  letI : IsIso a := (nonvanishingOpen_eq_top_iff L a).mp htop
  have hd := projectiveLineDegree_iso P marking L (projectiveTwist P marking 0)
    (asIso a).symm
  rw [projectiveTwist_degree] at hd
  omega

/-- The specified line inclusion is the entire scheme-theoretic fiber
of the actual source projection. -/
theorem fiberInclusion_isPullback
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) :
    IsPullback (H.fiberInclusion t y) P.structureMap H.projection
      (H.parameterPoint t y).val := by
  apply IsPullback.mk' (H.fiberInclusion_projection t y)
  · intro T a b h₁ h₂
    have hh := congrArg (fun k => k ≫ H.sourcePoint) h₁
    simpa only [Category.assoc, fiberInclusion_sourcePoint, Category.comp_id] using hh
  · intro T a b hab
    have hbase : (a ≫ H.sourcePoint) ≫ P.structureMap = b := by
      calc
        _ = a ≫ H.projection ≫ H.parameterToC := by
          rw [Category.assoc, H.source_overC]
        _ = b ≫ (H.parameterPoint t y).val ≫ H.parameterToC := by
          rw [← Category.assoc, hab, Category.assoc]
        _ = b := by rw [(H.parameterPoint t y).property, Category.comp_id]
    refine ⟨a ≫ H.sourcePoint, ?_, hbase⟩
    apply H.source_isPullback.hom_ext
    · simp only [Category.assoc, fiberInclusion_sourcePoint, Category.comp_id]
    · calc
        _ = ((a ≫ H.sourcePoint) ≫ P.structureMap) ≫
            (H.parameterPoint t y).val := by
          simp only [Category.assoc, fiberInclusion_projection]
        _ = b ≫ (H.parameterPoint t y).val := by rw [hbase]
        _ = a ≫ H.projection := hab.symm

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.fiberInclusion_isPullback :=
  @LeBrunSalamon.Construction.Descent.LineTests.fiberInclusion_isPullback

/-- A complex parameter in the incidence open gives a point on the
actual test line in the specified target open. -/
theorem meets_of_mem_meetingOpen
    (t : PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC)
    (y : ComplexPoint X.variety) (axis : Axis) (U : (Square X).Opens)
    (h : (H.parameterPoint t y).val (IsLocalRing.closedPoint ℂ) ∈
      H.meetingOpen axis U) :
    MeetsOpen (testLine (H.lineAt t) y axis) U := by
  obtain ⟨z, hz, hproj⟩ := h
  obtain ⟨p, hp, _⟩ := AlgebraicGeometry.Scheme.exists_preimage_of_isPullback
    (H.fiberInclusion_isPullback t y) z (IsLocalRing.closedPoint ℂ) hproj
  refine ⟨p, ?_⟩
  change H.axisEvaluation axis z ∈ U at hz
  have hh : H.axisEvaluation axis (H.fiberInclusion t y p) ∈ U := by
    rw [hp]
    exact hz
  simpa only [← Scheme.Hom.comp_apply, fiberInclusion_evaluation] using hh

def memberOfParameter
    (w : PointsOver ComplexBase (𝟙 ComplexBase) H.Parameter H.parameterToC) :
    PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC :=
  ⟨w.val ≫ pullback.fst H.toC X.variety.structureMap, by
    simpa only [parameterToC, Category.assoc] using w.property⟩

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.memberOfParameter :=
  @LeBrunSalamon.Construction.Descent.LineTests.memberOfParameter

def otherOfParameter
    (w : PointsOver ComplexBase (𝟙 ComplexBase) H.Parameter H.parameterToC) :
    ComplexPoint X.variety :=
  ⟨w.val ≫ pullback.snd H.toC X.variety.structureMap, by
    rw [Category.assoc, ← pullback.condition]
    exact w.property⟩

abbrev _root_.LeBrunSalamon.Construction.Lines.CoveringFamily.otherOfParameter :=
  @LeBrunSalamon.Construction.Descent.LineTests.otherOfParameter

theorem parameterPoint_decompose
    (w : PointsOver ComplexBase (𝟙 ComplexBase) H.Parameter H.parameterToC) :
    H.parameterPoint (H.memberOfParameter w) (H.otherOfParameter w) = w := by
  apply Subtype.ext
  apply pullback.hom_ext <;>
    simp only [parameterPoint, memberOfParameter, otherOfParameter,
      pullback.lift_fst, pullback.lift_snd]

instance parameter_integral : IsIntegral H.Parameter := by
  letI : AlgebraicGeometry.IsReduced H.Parameter :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced H.parameterToC
  exact isIntegral_of_irreducibleSpace_of_isReduced H.Parameter

instance parameter_compact : CompactSpace H.Parameter := by
  letI : CompactSpace H.parameter := H.quasiCompact
  change CompactSpace (pullback H.toC X.variety.structureMap : Scheme)
  infer_instance

/-- Finite-type complex schemes have an actual complex point in every
nonempty open. This uses Mathlib's closed-point construction. -/
theorem complexPoint_in_nonempty_open {Y : Scheme} (sY : Y ⟶ ComplexBase)
    [LocallyOfFiniteType sY] (V : Y.Opens) (hV : (V : Set Y).Nonempty) :
    ∃ p : PointsOver ComplexBase (𝟙 ComplexBase) Y sY,
      p.val (IsLocalRing.closedPoint ℂ) ∈ V := by
  letI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨x, hxV, hxclosed⟩ :=
    nonempty_inter_closedPoints hV V.isOpen.isLocallyClosed
  refine ⟨⟨pointOfClosedPoint sY x hxclosed,
    pointOfClosedPoint_comp sY x hxclosed⟩, ?_⟩
  change pointOfClosedPoint sY x hxclosed (IsLocalRing.closedPoint ℂ) ∈ V
  rw [pointOfClosedPoint_apply]
  exact hxV

end LeBrunSalamon.Construction.Descent.LineTests

end
